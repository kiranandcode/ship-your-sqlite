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

structure Ctx where
  db : Db
  /-- json.c's cache of parsed JSON texts, per statement (`Sql.Json`) -/
  jsonCache : Json.Cache := {}
  deriving Inhabited

abbrev M := ExceptT Err (StateM Ctx)

def err {α} (msg : String) (code : Nat := SQLITE_ERROR) : M α := throw { code, msg }

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

partial def likeMatch (pat str : List (List UInt8)) (esc : Option (List UInt8)) (nocase : Bool) : Bool :=
  let eqc (a b : List UInt8) := if nocase then charLower a == charLower b else a == b
  match pat with
  | [] => str.isEmpty
  | p :: ps =>
    if some p == esc then
      match ps, str with
      | q :: qs, s :: ss => eqc q s && likeMatch qs ss esc nocase
      | _, _ => false
    else if p == [37] then -- %
      let rec tryAll : List (List UInt8) → Bool
        | [] => likeMatch ps [] esc nocase
        | s :: ss => likeMatch ps (s :: ss) esc nocase || tryAll ss
      tryAll str
    else if p == [95] then -- _
      match str with
      | _ :: ss => likeMatch ps ss esc nocase
      | [] => false
    else
      match str with
      | s :: ss => eqc p s && likeMatch ps ss esc nocase
      | [] => false

/-- GLOB: `*`, `?`, `[...]` (with `^` and ranges), case-sensitive. -/
partial def globMatch (pat str : List (List UInt8)) : Bool :=
  match pat with
  | [] => str.isEmpty
  | p :: ps =>
    if p == [42] then
      let rec tryAll : List (List UInt8) → Bool
        | [] => globMatch ps []
        | s :: ss => globMatch ps (s :: ss) || tryAll ss
      tryAll str
    else if p == [63] then
      match str with
      | _ :: ss => globMatch ps ss
      | [] => false
    else if p == [91] then
      match str with
      | [] => false
      | s :: ss =>
        let (neg, body) := match ps with
          | [94] :: r => (true, r) | r => (false, r)
        -- a ']' right after '[' (or '[^') is a member
        let rec cls (l : List (List UInt8)) (first : Bool) (acc : Bool) : Option (Bool × List (List UInt8)) :=
          match l with
          | [] => none
          | [93] :: r => if first then cls r false (acc || s == [93]) else some (acc, r)
          | a :: [45] :: b :: r =>
            if b == [93] then cls ([45] :: b :: r) false (acc || s == a)
            else cls r false (acc || (decide (a ≤ s) && decide (s ≤ b)))
          | a :: r => cls r false (acc || s == a)
        match cls body true false with
        | some (hit, rest) => (hit != neg) && globMatch rest ss
        | none => false
    else
      match str with
      | s :: ss => p == s && globMatch ps ss
      | [] => false

end Sql
