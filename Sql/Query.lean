/-
  Expressions and SELECT. See `Sql.Eval` for the row-order convention.
-/
import Sql.Func

namespace Sql

/-! ## Static information about expressions -/

/-- Metadata of a result column: name, affinity, collation. -/
structure ColMeta where
  name : Name
  aff : Option Aff
  coll : Coll
  deriving Inhabited

/-- The rows a CTE stands for, or its definition. -/
inductive CteVal where
  | defn (cols : List Name) (q : Select) (recursive : Bool)
  | rows (cols : Array ColMeta) (rows : Array (Array Value))
  deriving Inhabited

structure QEnv where
  env : Env := {}
  ctes : List (Name × CteVal) := []
  deriving Inhabited

def aggNames : List String :=
  ["count", "sum", "total", "avg", "min", "max", "group_concat", "string_agg",
   "json_group_array", "json_group_object", "jsonb_group_array", "jsonb_group_object"]

def windowOnlyNames : List String :=
  ["row_number", "rank", "dense_rank", "percent_rank", "cume_dist", "ntile", "lag", "lead",
   "first_value", "last_value", "nth_value"]

/-- Is a call an aggregate here? `min`/`max` are aggregates with one argument. -/
def isAggCall (name : Name) (nargs : Nat) (star : Bool) (over : Bool) : Bool :=
  if over then false else
  let n := name.toLower
  if n == "min" || n == "max" then nargs == 1
  else if n == "count" then star || nargs ≤ 1
  else aggNames.contains n

mutual
/-- Does an expression contain an aggregate call (not inside a subquery)? -/
def hasAgg.go (k : Nat)  (x : Expr) : Bool :=
  match k with
  | 0 => false
  | k + 1 =>
  match x with
  | .call n _ args star _ _ over => isAggCall n args.length star over.isSome || args.any (hasAgg.go k)
  | .unop _ e | .collate e _ | .cast e _ | .isNull _ e => (hasAgg.go k) e
  | .binop _ a b => (hasAgg.go k) a || (hasAgg.go k) b
  | .between _ a b c => (hasAgg.go k) a || (hasAgg.go k) b || (hasAgg.go k) c
  | .inList _ e l => (hasAgg.go k) e || l.any (hasAgg.go k)
  | .inSelect _ e _ | .inTable _ e _ _ _ => (hasAgg.go k) e
  | .like _ _ a b c => (hasAgg.go k) a || (hasAgg.go k) b || (c.map (hasAgg.go k)).getD false
  | .case_ b ws e => (b.map (hasAgg.go k)).getD false || ws.any (fun (x, y) => (hasAgg.go k) x || (hasAgg.go k) y) || (e.map (hasAgg.go k)).getD false
  | .row l => l.any (hasAgg.go k)
  | _ => false

def hasWindow.go (k : Nat)  (x : Expr) : Bool :=
  match k with
  | 0 => false
  | k + 1 =>
  match x with
  | .call _ _ args _ _ _ over => over.isSome || args.any (hasWindow.go k)
  | .unop _ e | .collate e _ | .cast e _ | .isNull _ e => (hasWindow.go k) e
  | .binop _ a b => (hasWindow.go k) a || (hasWindow.go k) b
  | .between _ a b c => (hasWindow.go k) a || (hasWindow.go k) b || (hasWindow.go k) c
  | .inList _ e l => (hasWindow.go k) e || l.any (hasWindow.go k)
  | .case_ b ws e => (b.map (hasWindow.go k)).getD false || ws.any (fun (x, y) => (hasWindow.go k) x || (hasWindow.go k) y) || (e.map (hasWindow.go k)).getD false
  | .like _ _ a b c => (hasWindow.go k) a || (hasWindow.go k) b || (c.map (hasWindow.go k)).getD false
  | _ => false
end

def hasWindow (x : Expr) : Bool := hasWindow.go syntaxFuel x

def hasAgg (x : Expr) : Bool := hasAgg.go syntaxFuel x

/-! ## Name resolution -/

inductive Resolved where
  | col (frame : Nat) (src : Nat) (col : Nat)
  | rowid (frame : Nat) (src : Nat)
  | new (col : Nat) | newRowid
  | old (col : Nat) | oldRowid
  | alias (e : Expr)
  deriving Inhabited

def isRowidName (n : Name) : Bool := nameEq n "rowid" || nameEq n "oid" || nameEq n "_rowid_"

/-- Resolve a column reference in the scopes of `env` (innermost first). -/
def resolveCol (env : Env) (tbl : Option Name) (col : Name) : Except String Resolved := do
  -- NEW. and OLD. in triggers
  if let some t := tbl then
    if nameEq t "new" then
      if let some (src, _) := env.newRow then
        match (src.cols.toList.findIdx? fun (n, _, _) => nameEq n col) with
        | some i => return .new i
        | none => if isRowidName col then return .newRowid else throw s!"no such column: new.{col}"
    if nameEq t "old" then
      if let some (src, _) := env.oldRow then
        match (src.cols.toList.findIdx? fun (n, _, _) => nameEq n col) with
        | some i => return .old i
        | none => if isRowidName col then return .oldRowid else throw s!"no such column: old.{col}"
  let rec go (fs : List Scope) (fi : Nat) : Except String Resolved := do
    match fs with
    | [] =>
      match tbl with
      | some t => throw s!"no such column: {t}.{col}"
      | none => throw s!"no such column: {col}"
    | f :: rest =>
      let mut hits : Array Resolved := #[]
      for h : si in [0:f.srcs.size] do
        let s := f.srcs[si]
        if (tbl.isNone && !s.qualOnly) || (tbl.isSome && nameEq s.alias tbl.get!) then
          match (s.cols.toList.findIdx? fun (n, _, _) => nameEq n col) with
          | some ci =>
            -- a USING/NATURAL duplicate is not a second match
            if !(tbl.isNone && s.hidden.contains ci) then hits := hits.push (.col fi si ci)
          | none => pure ()
      if hits.size > 1 then
        throw (match tbl with
          | some t => s!"ambiguous column name: {t}.{col}"
          | none => s!"ambiguous column name: {col}")
      if hits.size == 1 then return hits[0]!
      -- rowid
      if isRowidName col then
        let cands := (List.range f.srcs.size).filter fun si =>
          let s := f.srcs[si]!
          s.hasRowid && (tbl.isNone || nameEq s.alias tbl.get!)
        match cands with
        | [si] => return .rowid fi si
        | _ :: _ :: _ => throw s!"ambiguous column name: {col}"
        | [] => pure ()
      -- result-column aliases (only unqualified)
      if tbl.isNone then
        if let some (_, e) := f.aliases.find? (fun (n, _) => nameEq n col) then return .alias e
      go rest (fi + 1)
  go env.frames 0

/-- Metadata of a resolved column. -/
def colMetaOf (env : Env) : Resolved → Option (Option Aff × Coll)
  | .col fi si ci => do
    let f ← env.frames[fi]?
    let s ← f.srcs[si]?
    let (_, a, c) ← s.cols[ci]?
    return (a, c)
  | .rowid .. | .newRowid | .oldRowid => some (some .integer, .binary)
  | .new ci => env.newRow.bind fun (s, _) => s.cols[ci]?.map fun (_, a, c) => (a, c)
  | .old ci => env.oldRow.bind fun (s, _) => s.cols[ci]?.map fun (_, a, c) => (a, c)
  | .alias _ => none

/-- Expression affinity (`sqlite3ExprAffinity`): `none` is "no affinity". -/
def exprAff.go (k : Nat) (env : Env) (x : Expr) : Option Aff :=
  match k with
  | 0 => none
  | k + 1 =>
  match x with
  | .col _ t c => match resolveCol env t c with
    | .ok r => match colMetaOf env r with
      | some (a, _) => a
      | none => match r with | .alias e => (exprAff.go k) env e | _ => none
    | .error _ => none
  | .dqcol c => (exprAff.go k) env (.col none none c)
  | .cast _ ty => some (affinityOfType ty)
  | .collate e _ => (exprAff.go k) env e
  | .unop .pos e => (exprAff.go k) env e
  | _ => none

def exprAff (env : Env) (x : Expr) : Option Aff := exprAff.go syntaxFuel env x

/-- Collation of an expression: explicit (`COLLATE`) or from a column. -/
def exprColl.go (k : Nat) (env : Env) (x : Expr) : Option (Coll × Bool) :=
  match k with
  | 0 => none
  | k + 1 =>
  match x with
  | .collate _ c => some ((collOfName c).getD .binary, true)
  | .col _ t c => match resolveCol env t c with
    | .ok r => match colMetaOf env r with
      | some (_, coll) => some (coll, false)
      | none => match r with | .alias e => (exprColl.go k) env e | _ => none
    | .error _ => none
  | .dqcol c => (exprColl.go k) env (.col none none c)
  | .unop .pos e | .cast e _ => (exprColl.go k) env e
  | .binop _ a b =>
    match (exprColl.go k) env a with
    | some (c, true) => some (c, true)
    | x => match (exprColl.go k) env b with
      | some (c, true) => some (c, true)
      | _ => x
  | _ => none

def exprColl (env : Env) (x : Expr) : Option (Coll × Bool) := exprColl.go syntaxFuel env x

/-- The collation of a binary comparison (`sqlite3BinaryCompareCollSeq`). -/
def cmpColl (env : Env) (a b : Expr) : Coll :=
  match exprColl env a, exprColl env b with
  | some (c, true), _ => c
  | _, some (c, true) => c
  | some (c, false), _ => c
  | _, some (c, false) => c
  | _, _ => .binary

/-- The affinity of a comparison (`sqlite3CompareAffinity`). -/
def cmpAff (a1 a2 : Option Aff) : Option Aff :=
  match a1, a2 with
  | some x, some y =>
    if x == .numeric || x == .integer || x == .real || y == .numeric || y == .integer || y == .real
    then some .numeric else none
  | some x, none => some x
  | none, some y => some y
  | none, none => none

/-- Apply a comparison affinity to an operand (OP_Lt … with p5). -/
def cmpConvert (aff : Option Aff) (v : Value) : Value :=
  match aff, v with
  | some .numeric, .text s | some .integer, .text s | some .real, .text s =>
    (numericOfText s false).getD v
  | some .text, .int _ | some .text, .real _ => .text (textOf v)
  | _, _ => v

/-- `a op b` for a comparison operator, three-valued. -/
def compareOp (op : BinOp) (aff : Option Aff) (coll : Coll) (a b : Value) : Value :=
  if a.isNull || b.isNull then .null else
  let o := compareValues coll (cmpConvert aff a) (cmpConvert aff b)
  boolV <| some <| match op with
    | .lt => o == .lt | .le => o != .gt | .gt => o == .gt | .ge => o != .lt
    | .eq => o == .eq | .ne => o != .eq | _ => false

/-! ## Casts -/

def castValue (v : Value) (ty : String) : Value :=
  match affinityOfType ty, v with
  | _, .null => .null
  | .text, _ => .text (textOf v)
  | .blob, .text s => .blob s
  | .blob, .blob b => .blob b
  | .blob, _ => .blob (textOf v)
  | .integer, .text s | .integer, .blob s => .int (atoiPrefix s)
  | .integer, .real r => .int (realToInt r)
  | .integer, w => w
  | .real, .int i => .real (intToReal i)
  | .real, .text s | .real, .blob s => .real (atof s).value
  | .real, w => w
  | .numeric, .text s | .numeric, .blob s =>
    -- CAST(x AS NUMERIC): the numeric prefix, an integer if it is one
    let a := atof s
    if !a.digit then .int 0
    else match (Value.text s).numeric with
      | .real r => match realAsInt r with
        | some i => if a.frac then .int i else .real r
        | none => .real r
      | w => w
  | .numeric, .real r => .real r   -- sqlite3VdbeMemNumerify keeps a REAL
  | .numeric, w => w

/-! ## Bit operations -/

def bitOp (op : BinOp) (a b : Value) : Value :=
  if a.isNull || b.isNull then .null else
  -- sqlite3VdbeIntValue: a text gives its integer prefix
  let x := a.toInt
  let y := b.toInt
  let wrap (i : Int) : Int := let m := i % 2 ^ 64; if m ≥ 2 ^ 63 then m - 2 ^ 64 else m
  let toU (i : Int) : Nat := (i % 2 ^ 64).toNat
  match op with
  | .bitand => .int (wrap ((toU x &&& toU y : Nat) : Int))
  | .bitor => .int (wrap ((toU x ||| toU y : Nat) : Int))
  | .shl | .shr =>
    -- a negative count shifts the other way
    let left : Bool := (op == .shl) == (y ≥ 0)
    let n := y.natAbs
    if left then
      if n ≥ 64 then .int 0 else .int (wrap ((toU x <<< n : Nat) : Int))
    else
      if n ≥ 64 then .int (if x < 0 then -1 else 0) else .int (x >>> n)
  | _ => .null

end Sql
