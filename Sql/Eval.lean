/-
  Expression evaluation and queries.

  Row order. Where SQL leaves the order of rows unspecified, this executable
  semantics produces the order SQLite's plan produces in the simple cases:
  a table scan in rowid order, GROUP BY groups in key order, DISTINCT in
  first-occurrence order, UNION/INTERSECT/EXCEPT in sorted order. The
  relational semantics (`Sql.Derives`, Phase 2.5) states these orders as
  unspecified; the differential tests then compare per statement as
  multisets where the order is unspecified.

  This file uses `partial` definitions; making them total (fuel for recursive
  CTEs, SQLite's own depth limits) is Phase 2.5 (PHASES.md).
-/
import Sql.Db
import Sql.Json.Funcs

namespace Sql

/-- One source of a FROM clause, as seen by name resolution. -/
structure Src where
  /-- the name it is referred to by (alias or table name) -/
  alias : Name
  cols : Array (Name × Option Aff × Coll)
  /-- has a rowid (`rowid`, `oid`, `_rowid_` resolve to it) -/
  hasRowid : Bool := false
  /-- the INTEGER PRIMARY KEY column, which is also the rowid -/
  rowidCol : Option Nat := none
  /-- columns hidden from `*` (USING/NATURAL duplicates) -/
  hidden : List Nat := []
  /-- HIDDEN columns: resolvable by name, not part of `*` -/
  hiddenStar : List Nat := []
  /-- only reachable by qualified names (`excluded.` of an UPSERT) -/
  qualOnly : Bool := false
  deriving Inhabited

/-- A source's current row: rowid and values; `none` is the NULL row of an outer join. -/
abbrev Cur := Option Row

/-- A scope of name resolution: the sources of one SELECT and their current rows. -/
structure Scope where
  srcs : Array Src
  cur : Array Cur
  /-- result-column aliases usable in WHERE/ORDER BY (SQLite allows them) -/
  aliases : List (Name × Expr) := []
  deriving Inhabited

/-- Aggregate context: the rows of the current group (each a full set of frames). -/
structure Env where
  frames : List Scope := []
  /-- when evaluating over a group: the group's rows (innermost frame's `cur`) -/
  group : Option (Array (Array Cur)) := none
  /-- values of window functions for the current row, by position -/
  windowVals : List (Expr × Value) := []
  /-- the trigger's NEW and OLD rows -/
  newRow : Option (Src × Row) := none
  oldRow : Option (Src × Row) := none
  /-- bound parameters (unbound are NULL) -/
  params : List (Nat × Value) := []
  deriving Inhabited

/-- The choices SQL leaves to the implementation (PHASES.md, "Unspecified
    choices"). The executable semantics takes the defaults; `Sql.Derives`
    quantifies over all of them. -/
structure Choices where
  /-- the `n`-th unspecified order (`chooseOrder`), as a Lehmer code: 0 keeps
      the executable's order, and every permutation of a list of length `m`
      has a code below `m!` -/
  order : Nat → Nat := fun _ => 0
  /-- the `n`-th draw of SQLite's PRNG: `random()` takes word 0 modulo 2^64
      (two's complement), `randomblob(N)` bytes 1..N modulo 256 -/
  random : Nat → Nat → Nat := fun seed i =>
    if i == 0 then (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    else (seed * 31 + (i - 1) * 17) % 256
  /-- the `n`-th candidate of the random rowid SQLite picks after rowid
      2^63−1 (taken modulo 2^62, plus 1) -/
  rowid : Nat → Nat := fun k => (k * 2862933555777941757 + 3037000493) % 2 ^ 63
  /-- the time 'now' reads, in milliseconds since the Unix epoch (the
      external model's clock, `Run.World.clock`, is a parameter likewise) -/
  clockMs : Int := 0
  deriving Inhabited

structure Ctx where
  db : Db
  /-- the implementation's choices, and how many orders were chosen so far -/
  choices : Choices := {}
  orderPos : Nat := 0
  /-- some fuel ran out (the run is not a derivation, `Sql.Derives`) -/
  exhausted : Bool := false
  /-- json.c's cache of parsed JSON texts, per statement (`Sql.Json`) -/
  jsonCache : Json.Cache := {}
  deriving Inhabited

abbrev M := ExceptT Err (StateM Ctx)

def err {α} (msg : String) (code : Nat := SQLITE_ERROR) : M α := throw { code, msg }

/-- The fuel `runStmt` gives the evaluator: a bound on the depth of its
    recursion (nested expressions, subqueries, triggers) and on the rounds of a
    recursive CTE. SQLite bounds the first by SQLITE_MAX_EXPR_DEPTH and
    SQLITE_MAX_TRIGGER_DEPTH (1000); a recursive CTE that would run longer is
    reported as out of fuel by the executable (SQLite would run on). -/
def evalFuel : Nat := 1000000000

/-- The total evaluator ran out of fuel (Phase 2.5): never with the fuel `sql_run`
    passes, which exceeds every depth SQLite itself allows. -/
def fuelErr : Err := { code := SQLITE_ERROR, msg := "out of fuel" }

/-- Fuel exhausted: recorded in the state (which survives errors and
    rollbacks), then thrown. -/
def outOfFuel {α} : M α := do
  modify fun c => { c with exhausted := true }
  throw fuelErr

/-- The permutation with Lehmer code `code` (digit `code % n` picks among the
    `n` elements left). Code 0 is the identity. -/
def permute {α} (code : Nat) (xs : Array α) : Array α :=
  if code == 0 then xs else
  let rec go (k : Nat) (c : Nat) (l : List α) : List α :=
    match k with
    | 0 => l
    | k + 1 =>
      match l with
      | [] => []
      | _ =>
        let i := c % l.length
        match l[i]? with
        | some x => x :: go k (c / l.length) (l.eraseIdx i)
        | none => l
  (go xs.size code xs.toList).toArray

/-- An order SQL leaves unspecified: the next code of `Choices.order`. -/
def chooseOrder {α} (xs : Array α) : M (Array α) := do
  let c ← get
  set { c with orderPos := c.orderPos + 1 }
  return permute (c.choices.order c.orderPos) xs

/-! ## Values as SQL booleans -/

/-- Truth of a value: NULL is unknown; numbers by being nonzero; text by its numeric prefix. -/
def truth : Value → Option Bool
  | .null => none
  | .int i => some (i != 0)
  | .real r => some (r != 0.0)
  | v => some (v.toReal != 0.0)

def boolV : Option Bool → Value
  | none => .null
  | some b => .int (if b then 1 else 0)

/-! ## LIKE and GLOB (patternCompare) -/

/-- The characters of a byte string as SQLite steps over them
    (`SQLITE_SKIP_UTF8`): a byte ≥ 0xC0 takes the continuation bytes after it;
    any other byte is one character. -/
def utf8Chars (b : ByteArray) : List (List UInt8) :=
  let rec go : List UInt8 → List (List UInt8)
    | [] => []
    | c :: rest =>
      if c ≥ 0xC0 then
        let cont := rest.takeWhile (· &&& 0xC0 == 0x80)
        (c :: cont) :: go (rest.drop cont.length)
      else [c] :: go rest
  termination_by l => l.length
  decreasing_by all_goals simp_wf; all_goals (try simp [List.length_drop]); all_goals omega
  go b.toList

def charLower (c : List UInt8) : List UInt8 := c.map lowerB

/-- LIKE matching (patternCompare). Every recursive call consumes at least
    one pattern element, so `k = pat.length + 1` is never exhausted. -/
def likeGo (k : Nat) (pat str : List (List UInt8)) (esc : Option (List UInt8)) (nocase : Bool) : Bool :=
  match k with
  | 0 => false
  | k + 1 =>
  let eqc (a b : List UInt8) := if nocase then charLower a == charLower b else a == b
  match pat with
  | [] => str.isEmpty
  | p :: ps =>
    if some p == esc then
      match ps, str with
      | q :: qs, s :: ss => eqc q s && likeGo k qs ss esc nocase
      | _, _ => false
    else if p == [37] then -- %
      (List.range (str.length + 1)).any fun i => likeGo k ps (str.drop i) esc nocase
    else if p == [95] then -- _
      match str with
      | _ :: ss => likeGo k ps ss esc nocase
      | [] => false
    else
      match str with
      | s :: ss => eqc p s && likeGo k ps ss esc nocase
      | [] => false

def likeMatch (pat str : List (List UInt8)) (esc : Option (List UInt8)) (nocase : Bool) : Bool :=
  likeGo (pat.length + 1) pat str esc nocase

/-- The members of a GLOB character class `[...]` (after `[` or `[^`): whether
    `s` is in it, and the pattern after the closing `]`. -/
def globClass (s : List UInt8) : List (List UInt8) → Bool → Bool → Option (Bool × List (List UInt8))
  | [], _, _ => none
  | [93] :: r, first, acc => if first then globClass s r false (acc || s == [93]) else some (acc, r)
  | a :: [45] :: b :: r, _, acc =>
    if b == [93] then globClass s ([45] :: b :: r) false (acc || s == a)
    else globClass s r false (acc || (decide (a ≤ s) && decide (s ≤ b)))
  | a :: r, _, acc => globClass s r false (acc || s == a)

/-- GLOB: `*`, `?`, `[...]` (with `^` and ranges), case-sensitive. Every
    recursive call consumes at least one pattern element. -/
def globGo (k : Nat) (pat str : List (List UInt8)) : Bool :=
  match k with
  | 0 => false
  | k + 1 =>
  match pat with
  | [] => str.isEmpty
  | p :: ps =>
    if p == [42] then
      (List.range (str.length + 1)).any fun i => globGo k ps (str.drop i)
    else if p == [63] then
      match str with
      | _ :: ss => globGo k ps ss
      | [] => false
    else if p == [91] then
      match str with
      | [] => false
      | s :: ss =>
        let (neg, body) := match ps with
          | [94] :: r => (true, r) | r => (false, r)
        match globClass s body true false with
        | some (hit, rest) => (hit != neg) && globGo k rest ss
        | none => false
    else
      match str with
      | s :: ss => p == s && globGo k ps ss
      | [] => false

def globMatch (pat str : List (List UInt8)) : Bool := globGo (pat.length + 1) pat str

end Sql
