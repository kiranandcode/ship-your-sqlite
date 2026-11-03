/-
  The evaluator: expressions, subqueries and SELECT (mutually recursive).
-/
import Std.Data.HashMap
import Std.Data.HashSet
import Sql.Query
import Sql.Printf
import Sql.DateTime
import Sql.Json

namespace Sql

def getDb : M Db := return (← get).db

def tableSrc (alias : Name) (t : Table) : Src :=
  { alias, cols := t.cols.map fun c => (c.name, some c.aff, c.coll),
    hasRowid := !t.withoutRowid, rowidCol := t.rowidCol }

def metaSrc (alias : Name) (cols : Array ColMeta) : Src :=
  { alias, cols := cols.map fun c => (c.name, c.aff, c.coll) }

/-- Sort with a comparison, stably (merge sort). -/
partial def stableSort {α} [Inhabited α] (cmp : α → α → Ordering) (xs : Array α) : Array α :=
  if xs.size ≤ 1 then xs else
  let mid := xs.size / 2
  let l := stableSort cmp (xs.extract 0 mid)
  let r := stableSort cmp (xs.extract mid xs.size)
  Id.run do
    let mut out := Array.emptyWithCapacity xs.size
    let mut i := 0
    let mut j := 0
    while i < l.size || j < r.size do
      if j ≥ r.size || (i < l.size && cmp l[i]! r[j]! != .gt) then
        out := out.push l[i]!; i := i + 1
      else out := out.push r[j]!; j := j + 1
    return out

def lexCompare (colls : List Coll) (dirs : List (SortDir × NullsOrder)) (a b : Array Value) : Ordering := Id.run do
  for h : i in [0:a.size] do
    let c := colls[i]?.getD .binary
    let (d, n) := dirs[i]?.getD (.asc, .default)
    let x := a[i]
    let y := b[i]!
    let o : Ordering :=
      match x.isNull, y.isNull with
      | true, true => .eq
      | true, false => if n == .last || (n == .default && d == .desc) then .gt else .lt
      | false, true => if n == .last || (n == .default && d == .desc) then .lt else .gt
      | false, false => let o := compareValues c x y; if d == .desc then o.swap else o
    if o != .eq then return o
  return .eq

/-- Rows equal for DISTINCT/UNION (NULLs equal). -/
def rowsEq (colls : List Coll) (a b : Array Value) : Bool :=
  lexCompare colls [] a b == .eq

/-- A key equal for two rows exactly when `rowsEq` holds: numbers by value (an
    integral REAL as the integer), text folded by its collation. -/
def canonKey (colls : List Coll) (r : Array Value) : String := Id.run do
  let mut out := ""
  for h : i in [0:r.size] do
    let c := colls[i]?.getD .binary
    let piece := match r[i] with
      | .null => "N"
      | .int n => s!"I{n}"
      | .real x => match realAsInt x with
        | some n => if intToReal n == x then s!"I{n}" else s!"R{Real.bits x}"
        | none => s!"R{Real.bits (if x == 0.0 then 0.0 else x)}"
      | .text t =>
        let bs := match c with
          | .binary => t.toList
          | .nocase => t.toList.map lowerB
          | .rtrim => (t.toList.reverse.dropWhile (· == 32)).reverse
        "T" ++ hexOf ⟨bs.toArray⟩
      | .blob b => "B" ++ hexOf b
    out := out ++ piece ++ ","
  return out

def dedupe (colls : List Coll) (rows : Array (Array Value)) : Array (Array Value) := Id.run do
  let mut out := #[]
  let mut seen : Std.HashSet String := {}
  for r in rows do
    let k := canonKey colls r
    if !seen.contains k then
      seen := seen.insert k
      out := out.push r
  return out

/-- The integer value of a LIMIT/OFFSET expression. -/
def limitValue (v : Value) : M Int := do
  match v with
  | .int i => return i
  | .real r => match realAsInt r with
    | some i => return i
    | none => err "datatype mismatch" SQLITE_MISMATCH
  | .text s => match numericOfText s true with
    | some (.int i) => return i
    | _ => err "datatype mismatch" SQLITE_MISMATCH
  | .null => err "datatype mismatch" SQLITE_MISMATCH
  | .blob _ => err "datatype mismatch" SQLITE_MISMATCH

/-- Aggregate state over a group. -/
structure AggArg where
  vals : List Value
  deriving Inhabited

/-- The inner-join chain of a FROM item: leaves joined by INNER/CROSS joins
    without USING/NATURAL, and the ON conditions of those joins. Any other join
    is a single leaf. -/
partial def innerChain : FromItem → List FromItem × List Expr
  | .join l k false r on [] =>
    if k == .inner || k == .cross then
      let (ls, lc) := innerChain l
      let (rs, rc) := innerChain r
      (ls ++ rs, lc ++ rc ++ on.toList)
    else ([.join l k false r on []], [])
  | f => ([f], [])

/-- The conjuncts of a WHERE clause. -/
partial def conjuncts : Expr → List Expr
  | .binop .and a b => conjuncts a ++ conjuncts b
  | e => [e]

mutual
/-- Column names referred to anywhere in an expression, subqueries included
    (qualifier, name). Conservative: used only to delay a conjunct. -/
partial def exprRefs : Expr → List (Option Name × Name)
  | .col _ t c => [(t, c)]
  | .dqcol c => [(none, c)]
  | .unop _ e | .collate e _ | .cast e _ | .isNull _ e => exprRefs e
  | .binop _ a b => exprRefs a ++ exprRefs b
  | .between _ a b c => exprRefs a ++ exprRefs b ++ exprRefs c
  | .inList _ e l => exprRefs e ++ l.flatMap exprRefs
  | .inSelect _ e q => exprRefs e ++ selectRefs q
  | .inTable _ e _ _ a => exprRefs e ++ a.flatMap exprRefs
  | .like _ _ a b c => exprRefs a ++ exprRefs b ++ (c.map exprRefs).getD []
  | .case_ b ws e => (b.map exprRefs).getD [] ++ ws.flatMap (fun (x, y) => exprRefs x ++ exprRefs y) ++ (e.map exprRefs).getD []
  | .exists_ q | .subquery q => selectRefs q
  | .row l => l.flatMap exprRefs
  | .call _ _ args _ ob f _ => args.flatMap exprRefs ++ ob.flatMap (fun (.mk e _ _) => exprRefs e) ++ (f.map exprRefs).getD []
  | .raise _ m => (m.map exprRefs).getD []
  | _ => []

partial def selectRefs : Select → List (Option Name × Name)
  | .mk ctes _ first rest ob lim off =>
    ctes.flatMap (fun (.mk _ _ _ q) => selectRefs q) ++ coreRefs first ++ rest.flatMap (fun (_, c) => coreRefs c) ++
    ob.flatMap (fun (.mk e _ _) => exprRefs e) ++ (lim.map exprRefs).getD [] ++ (off.map exprRefs).getD []

partial def coreRefs : SelectCore → List (Option Name × Name)
  | .values rows => rows.flatten.flatMap exprRefs
  | .select _ cols f w g h _ =>
    cols.flatMap (fun | .expr e _ _ => exprRefs e | _ => []) ++ (f.map fromRefs).getD [] ++
    (w.map exprRefs).getD [] ++ g.flatMap exprRefs ++ (h.map exprRefs).getD []

partial def fromRefs : FromItem → List (Option Name × Name)
  | .tableFn _ _ args _ => args.flatMap exprRefs
  | .subquery q _ => selectRefs q
  | .join l _ _ r on _ => fromRefs l ++ fromRefs r ++ (on.map exprRefs).getD []
  | _ => []
end

/-! ### sum(), total(), avg(): SQLite's SumCtx (integer sum until a REAL or an
overflow, then Kahan-Babuska-Neumaier compensated summation; sqlite3.c sumStep) -/

structure SumCtx where
  rSum : Float := 0.0
  rErr : Float := 0.0
  iSum : Int := 0
  cnt : Int := 0
  approx : Bool := false
  ovrfl : Bool := false

def SumCtx.kbn (p : SumCtx) (r : Float) : SumCtx :=
  let s := p.rSum
  let t := s + r
  let e := if s.abs > r.abs then p.rErr + ((s - t) + r) else p.rErr + ((r - t) + s)
  { p with rSum := t, rErr := e }

def big52 : Int := 4503599627370496

def SumCtx.kbnInt (p : SumCtx) (i : Int) : SumCtx :=
  if i ≤ -big52 || i ≥ big52 then
    let sm := i.tmod 16384
    (p.kbn (intToReal (i - sm))).kbn (intToReal sm)
  else p.kbn (intToReal i)

def SumCtx.init (p : SumCtx) (i : Int) : SumCtx :=
  if i ≤ -big52 || i ≥ big52 then
    let sm := i.tmod 16384
    { p with rSum := intToReal (i - sm), rErr := intToReal sm }
  else { p with rSum := intToReal i, rErr := 0.0 }

/-- sqlite3_value_numeric_type: a text is an integer only if all of it reads as one. -/
def numericForSum (v : Value) : Value :=
  match v with
  | .text t | .blob t => match numericOfText t false with
    | some (.int i) => .int i
    | _ => .real v.toReal
  | w => w

def SumCtx.step (p : SumCtx) (v : Value) : SumCtx :=
  match numericForSum v with
  | .null => p
  | nv =>
    let p := { p with cnt := p.cnt + 1 }
    if !p.approx then
      match nv with
      | .int i =>
        if inI64 (p.iSum + i) then { p with iSum := p.iSum + i }
        else ({ (p.init p.iSum) with ovrfl := true, approx := true }).kbnInt i
      | w => ({ (p.init p.iSum) with approx := true }).kbn w.toReal
    else
      match nv with
      | .int i => p.kbnInt i
      | w => ({ p with ovrfl := false }).kbn w.toReal

/-- `sumInverse`: a row leaves a window frame. -/
def SumCtx.inverse (p : SumCtx) (v : Value) : SumCtx :=
  match numericForSum v with
  | .null => p
  | nv =>
    let p := { p with cnt := p.cnt - 1 }
    let (p, done) := if !p.approx then
        match nv with
        | .int i => if inI64 (p.iSum - i) then ({ p with iSum := p.iSum - i }, true)
                    else ({ (p.init p.iSum) with ovrfl := true, approx := true }, false)
        | _ => ({ (p.init p.iSum) with ovrfl := true, approx := true }, false)
      else (p, false)
    if done then p else
    match nv with
    | .int i => if i != minI64 then p.kbnInt (-i) else (p.kbnInt maxI64).kbnInt 1
    | w => p.kbn (-w.toReal)

def isOverflow (x : Float) : Bool := x.isInf || x.isNaN

/-- The REAL result (sum with approx, total, avg's numerator). -/
def SumCtx.real (p : SumCtx) : Float := if isOverflow p.rErr then p.rSum else p.rSum + p.rErr

def SumCtx.finish (p : SumCtx) : Float := if p.approx then p.real else intToReal p.iSum

/-- SQLITE_LIMIT_LENGTH (SQLITE_MAX_LENGTH of the default build) -/
def maxLength : Int := 1000000000

/-- A TEXT read through `sqlite3_value_text` as a C string: up to its first NUL. -/
def cstrOf (b : ByteArray) : ByteArray := ⟨(b.data.toList.takeWhile (· != 0)).toArray⟩

/-- quote() of a text: single quotes doubled. -/
def quoteText (b : ByteArray) : ByteArray :=
  ByteArray.mk (#[39] ++ (b.data.foldl (fun acc c => if c == 39 then (acc.push 39).push 39 else acc.push c) #[]) ++ #[39])

def windowParamBase : Nat := 1000000000

/-- The arity rules of `pragma function_list` for the lazy built-ins. -/
def checkArity (n : Name) (k : Nat) : M Unit := do
  let low := n.toLower
  let ok := if low == "ifnull" then k == 2 else k ≥ 2
  if !ok then err s!"wrong number of arguments to function {n}()"

/-- Replace each window-function call (outside subqueries) by a numbered
    parameter; returns the rewritten expressions and the calls in order. -/
partial def replaceWindows (es : List Expr) : List Expr × List Expr :=
  let rec go (e : Expr) : StateM (Array Expr) Expr := do
    match e with
    | .call n d args st ob f (some w) =>
      let k := (← get).size
      modify (·.push (.call n d args st ob f (some w)))
      return .param "__window" (windowParamBase + k)
    | .call n d args st ob f none => return .call n d (← args.mapM go) st ob f none
    | .unop o a => return .unop o (← go a)
    | .binop o a b => return .binop o (← go a) (← go b)
    | .collate a c => return .collate (← go a) c
    | .cast a t => return .cast (← go a) t
    | .isNull ng a => return .isNull ng (← go a)
    | .between ng a b c => return .between ng (← go a) (← go b) (← go c)
    | .inList ng a l => return .inList ng (← go a) (← l.mapM go)
    | .like o ng a b c => return .like o ng (← go a) (← go b) (← c.mapM go)
    | .case_ b ws el => return .case_ (← b.mapM go) (← ws.mapM fun (x, y) => do pure (← go x, ← go y)) (← el.mapM go)
    | .row l => return .row (← l.mapM go)
    | x => return x
  let (es', calls) := (es.mapM go).run #[]
  (es', calls.toList)

/-- The index of the argument iif(c1, v1, c2, v2, …, else) returns. -/
def iifIndex (vs : List Value) : Option Nat :=
  let rec go (i : Nat) : List Value → Option Nat
    | c :: _ :: rest => if truth c == some true then some (i + 1) else go (i + 2) rest
    | [_] => some i
    | [] => none
  go 0 vs

def iifPick : List Value → Value
  | c :: v :: rest => if truth c == some true then v else iifPick rest
  | [e] => e
  | [] => .null

def QEnv.noGroup (q : QEnv) : QEnv := { q with env := { q.env with group := none } }

mutual

partial def evalExpr (q : QEnv) (e : Expr) : M Value := do
  let env := q.env
  match e with
  | .lit v => return v
  | .param _ i => return ((env.params.find? (·.1 == i)).map (·.2)).getD .null
  | .col sch t c =>
    let _ := sch
    match resolveCol env t c with
    | .ok r => valueOf q r
    | .error m =>
      if t.isNone && (nameEq c "true" || nameEq c "false") then
        return .int (if nameEq c "true" then 1 else 0)
      err m
  | .dqcol c =>
    match resolveCol env none c with
    | .ok r => valueOf q r
    | .error _ => return .ofString c
  | .unop op a =>
    let v ← evalExpr q a
    match op with
    | .not => return boolV ((truth v).map (!·))
    | .pos => return v
    | .neg =>
      match v.numeric with
      | .null => return .null
      | .int i => return if i == minI64 then .real (- intToReal i) else .int (-i)
      | .real r => return .real (-r)
      | w => return w
    | .bitnot =>
      if v.isNull then return .null
      let x := v.numeric.toInt
      return .int (-x - 1)
  | .binop op a b =>
    match op with
    | .and =>
      let x ← evalExpr q a
      if truth x == some false then return .int 0
      let y ← evalExpr q b
      return match truth x, truth y with
        | _, some false => .int 0
        | some true, some true => .int 1
        | _, _ => .null
    | .or =>
      let x ← evalExpr q a
      if truth x == some true then return .int 1
      let y ← evalExpr q b
      return match truth x, truth y with
        | _, some true => .int 1
        | some false, some false => .int 0
        | _, _ => .null
    | .lt | .le | .gt | .ge | .eq | .ne =>
      match a, b with
      | .row xs, .row ys => compareRows q op xs ys
      | _, _ =>
        let x ← evalExpr q a
        let y ← evalExpr q b
        return compareOp op (cmpAff (exprAff env a) (exprAff env b)) (cmpColl env a b) x y
    | .is | .isNot =>
      let x ← evalExpr q a
      let y ← evalExpr q b
      let same := match x.isNull, y.isNull with
        | true, true => true
        | true, false | false, true => false
        | false, false =>
          let aff := cmpAff (exprAff env a) (exprAff env b)
          compareValues (cmpColl env a b) (cmpConvert aff x) (cmpConvert aff y) == .eq
      return .int (if same == (op == .is) then 1 else 0)
    | .add | .sub | .mul | .div | .rem =>
      let x ← evalExpr q a
      let y ← evalExpr q b
      let aop := match op with
        | .add => ArithOp.add | .sub => .sub | .mul => .mul | .div => .div | _ => .rem
      return arith aop x y
    | .concat =>
      let x ← evalExpr q a
      let y ← evalExpr q b
      if x.isNull || y.isNull then return .null
      let r := textOf x ++ textOf y
      if r.size > maxLength then err "string or blob too big" SQLITE_TOOBIG
      return .text r
    | .bitand | .bitor | .shl | .shr =>
      return bitOp op (← evalExpr q a) (← evalExpr q b)
    | .ptr | .ptr2 => callFn q (if op == .ptr then "->" else "->>") [a, b] false
  | .collate a _ => evalExpr q a
  | .cast a ty => return castValue (← evalExpr q a) ty
  | .isNull neg a =>
    let v ← evalExpr q a
    return .int (if v.isNull != neg then 1 else 0)
  | .between neg x lo hi =>
    let v ← evalExpr q x
    let l ← evalExpr q lo
    let h ← evalExpr q hi
    let c1 := compareOp .ge (cmpAff (exprAff env x) (exprAff env lo)) (cmpColl env x lo) v l
    let c2 := compareOp .le (cmpAff (exprAff env x) (exprAff env hi)) (cmpColl env x hi) v h
    let r := match truth c1, truth c2 with
      | some false, _ | _, some false => some false
      | some true, some true => some true
      | _, _ => none
    return boolV (if neg then r.map (!·) else r)
  | .inList neg x items =>
    let v ← evalExpr q x
    if items.isEmpty then return .int (if neg then 1 else 0)
    let mut sawNull := false
    let mut found := false
    for it in items do
      let w ← evalExpr q it
      -- comparisonAffinity: an IN list compares with the left side's affinity only
      let c := compareOp .eq (exprAff env x) (cmpColl env x it) v w
      if truth c == some true then found := true; break
      if c.isNull then sawNull := true
    if v.isNull then return .null
    let r := if found then some true else if sawNull then none else some false
    return boolV (if neg then r.map (!·) else r)
  | .inSelect neg x sub =>
    let v ← evalExpr q x
    let (cols, rows) ← runSelect q sub
    if cols.size != 1 then err s!"sub-select returns {cols.size} columns - expected 1"
    if rows.isEmpty then return .int (if neg then 1 else 0)
    if v.isNull then return .null
    let aff := cmpAff (exprAff env x) (cols[0]!.aff)
    let coll := match exprColl env x with
      | some (c, _) => c
      | none => cols[0]!.coll
    let mut sawNull := false
    let mut found := false
    for r in rows do
      let c := compareOp .eq aff coll v r[0]!
      if truth c == some true then found := true; break
      if c.isNull then sawNull := true
    let res := if found then some true else if sawNull then none else some false
    return boolV (if neg then res.map (!·) else res)
  | .inTable neg x sch t args =>
    evalExpr q (.inSelect neg x (.mk [] false (.select false [.star]
      (some (if args.isEmpty then .table sch t none none else .tableFn sch t args none))
      none [] none []) [] [] none none))
  | .like op neg x pat esc =>
    let s ← evalExpr q x
    let p ← evalExpr q pat
    let es ← match esc with
      | some ee => some <$> evalExpr q ee
      | none => pure none
    if s.isNull || p.isNull then return .null
    if let some ev := es then if ev.isNull then return .null
    -- patternCompare reads NUL-terminated strings
    let cstr (b : ByteArray) : ByteArray := ⟨(b.data.toList.takeWhile (· != 0)).toArray⟩
    let ptxt := cstr (textOf p)
    let stxt := cstr (textOf s)
    let r ← match op with
      | .glob => pure (globMatch (utf8Chars ptxt) (utf8Chars stxt))
      | .like =>
        let escC ← match es with
          | some ev =>
            let c := utf8Chars (textOf ev)
            if c.length != 1 then err "ESCAPE expression must be a single character"
            pure c.head?
          | none => pure none
        pure (likeMatch (utf8Chars ptxt) (utf8Chars stxt) escC
          (!(← getDb).pragmas.caseSensitiveLike))
      | .regexp => err "no such function: regexp"
      | .match_ => err "unable to use function MATCH in the requested context"
    return .int (if r != neg then 1 else 0)
  | .case_ .. => return (← evalExprST q e).1
  | .exists_ sub =>
    let (_, rows) ← runSelect q sub
    return .int (if rows.isEmpty then 0 else 1)
  | .subquery sub =>
    let (cols, rows) ← runSelect q sub
    if cols.size != 1 then err s!"sub-select returns {cols.size} columns - expected 1"
    return (rows[0]?.bind (·[0]?)).getD .null
  | .row _ => err "row value misused"
  | .call n distinct args star ob filter over =>
    if over.isSome then
      err s!"misuse of window function {n}()"
    else if isAggCall n args.length star false then
      evalAgg q n distinct args star ob filter
    else
      if filter.isSome then err s!"FILTER clause may only be used with aggregate window functions"
      if star then err s!"wrong number of arguments to function {n}()"
      callFn q n args distinct
  | .raise kind msg =>
    let m ← match msg with
      | some x => pure (String.fromUTF8! (textOf (← evalExpr q x)))
      | none => pure ""
    match kind with
    | .ignore => throw { code := 0, msg := "RAISE(IGNORE)" }
    | _ => throw { code := SQLITE_CONSTRAINT_TRIGGER, msg := m }

partial def compareRows (q : QEnv) (op : BinOp) (xs ys : List Expr) : M Value := do
  if xs.length != ys.length then err "row value misused"
  -- lexicographic, three-valued
  let pairs := xs.zip ys
  let mut result : Option Bool := some (op == .eq || op == .le || op == .ge)
  let mut unknown := false
  for (a, b) in pairs do
    let x ← evalExpr q a
    let y ← evalExpr q b
    if x.isNull || y.isNull then
      unknown := true
      if op == .eq || op == .ne then continue
      break
    let o := compareValues (cmpColl q.env a b) (cmpConvert (cmpAff (exprAff q.env a) (exprAff q.env b)) x)
      (cmpConvert (cmpAff (exprAff q.env a) (exprAff q.env b)) y)
    if o != .eq then
      result := some (match op with
        | .eq => false | .ne => true | .lt | .le => o == .lt | _ => o == .gt)
      unknown := false
      return boolV result
  if unknown then return .null
  return boolV (if op == .ne then some false else result)

partial def valueOf (q : QEnv) : Resolved → M Value
  | .col fi si ci => do
    let some f := q.env.frames[fi]? | err "internal: frame"
    match f.cur[si]? with
    | some (some r) => return r.vals[ci]?.getD .null
    | _ => return .null
  | .rowid fi si => do
    let some f := q.env.frames[fi]? | err "internal: frame"
    match f.cur[si]? with
    | some (some r) => return .int r.rowid
    | _ => return .null
  | .new ci => return (q.env.newRow.bind fun (_, r) => r.vals[ci]?).getD .null
  | .newRowid => return (q.env.newRow.map fun (_, r) => Value.int r.rowid).getD .null
  | .old ci => return (q.env.oldRow.bind fun (_, r) => r.vals[ci]?).getD .null
  | .oldRowid => return (q.env.oldRow.map fun (_, r) => Value.int r.rowid).getD .null
  | .alias e => evalExpr q e

/-- An aggregate call over the current group. -/
partial def evalAgg (q : QEnv) (n : Name) (distinct : Bool) (args : List Expr) (star : Bool)
    (ob : List OrderTerm) (filter : Option Expr) : M Value := do
  if distinct && args.length != 1 then err "DISTINCT aggregates must have exactly one argument"
  let some grp := q.env.group | err s!"misuse of aggregate function {n}()"
  let name := n.toLower
  -- evaluate arguments per row of the group, in the context of that row
  let mut rows : Array (List Value × Array Value) := #[]
  let mut jflags : Array (List Bool) := #[]
  for cur in grp do
    let q' := setCur q cur
    if let some fl := filter then
      if truth (← evalExpr q'.noGroup fl) != some true then continue
    let vs ← args.mapM (evalExpr q'.noGroup)
    jflags := jflags.push (← args.mapM (argIsJson q'.noGroup))
    let keys ← ob.toArray.mapM fun (.mk e _ _) => evalExpr q'.noGroup e
    rows := rows.push (vs, keys)
  if !ob.isEmpty then
    let dirs := ob.map fun (.mk _ d nl) => (d, nl)
    let colls := ob.map fun (.mk e _ _) => ((exprColl q.env e).map (·.1)).getD .binary
    rows := stableSort (fun a b => lexCompare colls dirs a.2 b.2) rows
  if distinct then
    let coll := ((args.head?.bind (exprColl q.env)).map (·.1)).getD .binary
    let mut seen : Array (List Value) := #[]
    for (vs, _) in rows do
      if !(seen.any fun s => rowsEq [coll] s.toArray vs.toArray) then seen := seen.push vs
    rows := seen.map (·, #[])
  let coll := ((args.head?.bind (exprColl q.env)).map (·.1)).getD .binary
  aggFinish q n star args coll (rows.map (·.1)) (if ob.isEmpty && !distinct then some jflags else none)

/-- An aggregate over the argument lists of its rows (after FILTER, ORDER BY, DISTINCT). -/
partial def aggFinish (q : QEnv) (n : Name) (star : Bool) (args : List Expr) (coll : Coll)
    (vals : Array (List Value)) (jflags : Option (Array (List Bool)) := none) : M Value := do
  let name := n.toLower
  let arg1 := vals.map fun vs => vs.head?.getD .null
  match name with
  | "count" =>
    if star || args.isEmpty then return .int vals.size
    return .int (arg1.filter (!·.isNull)).size
  | "sum" | "total" | "avg" =>
    if args.length != 1 then err s!"wrong number of arguments to function {n}()"
    let st := arg1.foldl SumCtx.step {}
    if name == "sum" then
      if st.cnt == 0 then return .null
      if st.approx then
        if st.ovrfl then err "integer overflow"
        return .real st.real
      return .int st.iSum
    if name == "total" then return .real st.finish
    if st.cnt == 0 then return .null
    return .real (st.finish / intToReal st.cnt)
  | "min" | "max" =>
    let nn := arg1.filter (!·.isNull)
    if nn.isEmpty then return .null
    let better (a b : Value) : Bool :=
      let o := compareValues coll a b
      if name == "min" then o == .lt else o == .gt
    return nn.foldl (fun acc v => if better v acc then v else acc) nn[0]!
  | "group_concat" | "string_agg" =>
    if name == "string_agg" && args.length != 2 then err s!"wrong number of arguments to function {n}()"
    if args.length > 2 || args.isEmpty then err s!"wrong number of arguments to function {n}()"
    let mut out : Option ByteArray := none
    for vs in vals do
      let v := vs.head?.getD .null
      if v.isNull then continue
      let sep := match vs[1]? with
        | some s => if s.isNull then ByteArray.empty else textOf s
        | none => ",".toUTF8
      out := some (match out with
        | none => textOf v
        | some acc => acc ++ sep ++ textOf v)
    return match out with | some b => .text b | none => .null
  | _ => callAgg q name vals (args.map Json.exprIsJson) jflags

/-- Aggregates implemented elsewhere (JSON). -/
partial def callAgg (_q : QEnv) (name : String) (vals : Array (List Value)) (flags : List Bool)
    (rowFlags : Option (Array (List Bool)) := none) : M Value :=
  let rows := match rowFlags with
    | some fs => (vals.zip fs).toList.map fun (vs, f) => vs.zip (f.zipWith (· || ·) flags)
    | none => vals.toList.map fun vs => vs.zip flags
  match Json.aggregate? name rows with
  | some (.ok v) => pure v
  | some (.error e) => throw e
  | none => err s!"no such function: {name}"

/-- Does an argument carry the JSON subtype: a JSON-valued expression, or a
    column whose current value has it (`json_each.value`)? -/
partial def argIsJson (q : QEnv) (a : Expr) : M Bool := do
  if Json.exprIsJson a then return true
  match a with
  | .col _ t c =>
    match resolveCol q.env t c with
    | .ok (.col fi si ci) =>
      match q.env.frames[fi]? with
      | some f => match f.cur[si]? with
        | some (some r) => return r.jsonCols.contains ci
        | _ => return false
      | none => return false
    | _ => return false
  | _ => return false

partial def callFn (q : QEnv) (n : Name) (args : List Expr) (distinct : Bool) : M Value :=
  return (← callFnST q n args distinct).1

/-- A scalar call, with whether its result carries the JSON subtype: a JSON
    function says so; coalesce/ifnull/iif/nullif/likely/unlikely/likelihood and
    two-or-more-argument min/max pass on the subtype of the argument they
    return (checked against SQLite by the JSON lane, tests/sem/json_subtype.sql). -/
partial def callFnST (q : QEnv) (n : Name) (args : List Expr) (_distinct : Bool) : M (Value × Bool) := do
  -- coalesce/ifnull/iif are compiled to jumps: later arguments are evaluated
  -- only if needed
  let low := n.toLower
  if low == "coalesce" || low == "ifnull" then
    checkArity n args.length
    for a in args do
      let (v, f) ← evalExprST q a
      if !v.isNull then return (v, f)
    return (.null, false)
  if low == "iif" || low == "if" then
    checkArity n args.length
    let rec goIif : List Expr → M (Value × Bool)
      | c :: v :: rest => do
        if truth (← evalExpr q c) == some true then evalExprST q v else goIif rest
      | [e] => evalExprST q e
      | [] => pure (.null, false)
    return ← goIif args
  let evs ← args.mapM (evalExprST q)
  let vs := evs.map (·.1)
  let flags := evs.map (·.2)
  -- an arity error names the function as written
  let fixName (e : Err) : Err :=
    let low := s!"wrong number of arguments to function {n.toLower}()"
    if e.msg == low then { e with msg := s!"wrong number of arguments to function {n}()" } else e
  let lift (r : Except Err Value) : M (Value × Bool) := match r with
    | .ok v => pure (v, false)
    | .error e => throw (fixName e)
  match Json.scalarCached (← get).jsonCache n.toLower evs with
  | some (.ok (vf, cache')) =>
    modify fun c => { c with jsonCache := cache' }
    return vf
  | some (.error e) => throw (fixName e)
  | none =>
  match Printf.scalar? n.toLower vs with
  | some r => lift r
  | none =>
  match DateTime.scalar? {} n.toLower vs with
  | some r => lift r
  | none =>
    let v ← (try scalarFn n vs (args.map fun a => exprColl q.env a) catch e => throw (fixName e))
    -- the argument whose value is returned passes its subtype on
    let pick : Option Nat := match n.toLower with
      | "coalesce" | "ifnull" => vs.findIdx? (!·.isNull)
      | "nullif" | "likely" | "unlikely" | "likelihood" => if v.isNull then none else some 0
      | "iif" | "if" => iifIndex vs
      | "min" | "max" => if vs.length ≥ 2 then vs.findIdx? (fun x => compareValues .binary x v == .eq && x.rank == v.rank) else none
      | _ => none
    return (v, (pick.bind (flags[·]?)).getD false)

/-- An expression's value and whether it carries the JSON subtype. -/
partial def evalExprST (q : QEnv) (e : Expr) : M (Value × Bool) := do
  match e with
  | .call n distinct args star ob filter none =>
    if isAggCall n args.length star false then
      return (← evalExpr q e, Json.jsonProducers.contains n.toLower)
    if filter.isSome || star || !ob.isEmpty then return (← evalExpr q e, false)
    callFnST q n args distinct
  | .binop .ptr a b => callFnST q "->" [a, b] false
  | .unop .pos a => evalExprST q a
  | .collate a _ => evalExprST q a
  | .cast a ty =>
    let (v, f) ← evalExprST q a
    return (castValue v ty, f && affinityOfType ty == .text)
  | .case_ base whens els =>
    match base with
    | some b =>
      let bv ← evalExpr q b
      for (w, t) in whens do
        let wv ← evalExpr q w
        let c := compareOp .eq (cmpAff (exprAff q.env b) (exprAff q.env w)) (cmpColl q.env b w) bv wv
        if truth c == some true then return ← evalExprST q t
      match els with
      | some x => evalExprST q x
      | none => return (.null, false)
    | none =>
      for (w, t) in whens do
        if truth (← evalExpr q w) == some true then return ← evalExprST q t
      match els with
      | some x => evalExprST q x
      | none => return (.null, false)
  | .col _ _ _ => return (← evalExpr q e, ← argIsJson q e)
  | _ => return (← evalExpr q e, false)

/-- Scalar functions. -/
partial def scalarFn (n : Name) (vs : List Value) (colls : List (Option (Coll × Bool))) : M Value := do
  let name := n.toLower
  let wrong {α} : M α := err s!"wrong number of arguments to function {n}()"
  let a0 := vs[0]?.getD .null
  let a1 := vs[1]?.getD .null
  let nargs := vs.length
  match name with
  | "abs" =>
    if nargs != 1 then wrong
    -- an integer stays an integer; anything else is read as a double
    match a0 with
    | .null => return .null
    | .int i => if i == minI64 then err "integer overflow" else return .int i.natAbs
    | v => return .real v.toReal.abs
  | "length" =>
    if nargs != 1 then wrong
    match a0 with
    | .null => return .null
    | .blob b => return .int b.size
    -- a TEXT is read as a C string (up to its first NUL)
    | .text s => return .int (utf8Len (cstrOf s))
    | v => return .int (utf8Len (textOf v))
  | "octet_length" =>
    if nargs != 1 then wrong
    if a0.isNull then return .null
    return .int (textOf a0).size
  | "lower" | "upper" =>
    if nargs != 1 then wrong
    if a0.isNull then return .null
    let f := if name == "lower" then lowerB else fun c => if 97 ≤ c && c ≤ 122 then c - 32 else c
    return .text (ByteArray.mk ((textOf a0).data.map f))
  | "typeof" =>
    if nargs != 1 then wrong
    return .ofString (match a0 with
      | .null => "null" | .int _ => "integer" | .real _ => "real" | .text _ => "text" | .blob _ => "blob")
  | "coalesce" | "ifnull" =>
    if name == "ifnull" && nargs != 2 then wrong
    if nargs < 2 then wrong
    return (vs.find? (!·.isNull)).getD .null
  | "nullif" =>
    if nargs != 2 then wrong
    let coll := match colls[0]?.join, colls[1]?.join with
      | some (c, _), _ => c | _, some (c, _) => c | _, _ => .binary
    if !a0.isNull && !a1.isNull && compareValues coll a0 a1 == .eq then return .null
    return a0
  | "iif" | "if" =>
    if nargs < 2 then wrong
    -- iif(c1, v1, c2, v2, …, else)
    return iifPick vs
  | "quote" =>
    if nargs != 1 then wrong
    match a0 with
    | .real r => return .ofString ((Printf.quoteReal? r).getD (quoteValue a0))
    | .text t => return .text (quoteText (cstrOf t))
    | _ => return .ofString (quoteValue a0)
  | "hex" =>
    if nargs != 1 then wrong
    return .ofString (hexOf (textOf a0))
  | "unhex" =>
    if nargs < 1 || nargs > 2 then wrong
    if a0.isNull then return .null
    let ign := if nargs == 2 then textOf a1 else .empty
    let hv (c : UInt8) : Option Nat :=
      if 48 ≤ c && c ≤ 57 then some (c - 48).toNat
      else if 65 ≤ c && c ≤ 70 then some (c - 55).toNat
      else if 97 ≤ c && c ≤ 102 then some (c - 87).toNat else none
    let rec goHex : List UInt8 → Option (List UInt8)
      | [] => some []
      | c :: rest =>
        if ign.toList.contains c && (hv c).isNone then goHex rest else
        match rest with
        | d :: rest' => match hv c, hv d with
          | some x, some y => (goHex rest').map ((x * 16 + y).toUInt8 :: ·)
          | _, _ => none
        | [] => none
    match goHex (textOf a0).toList with
    | some l => return .blob ⟨l.toArray⟩
    | none => return .null
  | "char" =>
    let cs := vs.map fun v => Char.ofNat v.numeric.toInt.toNat
    return .text (String.ofList cs).toUTF8
  | "unicode" =>
    if nargs != 1 then wrong
    -- the first code point of the text (read up to its first NUL), as sqlite3Utf8Read
    let bs := (textOf a0).toList.takeWhile (· != 0)
    if a0.isNull || bs.isEmpty then return .null
    return .int (utf8Read bs).1
  | "instr" =>
    if nargs != 2 then wrong
    if a0.isNull || a1.isNull then return .null
    match a0, a1 with
    | .blob h, _ | _, .blob h =>
      let hay := (textOf a0).toList
      let nee := (textOf a1).toList
      let _ := h
      let idx := (List.range (hay.length + 1)).find? fun i => (hay.drop i).take nee.length == nee
      return .int (match idx with | some i => i + 1 | none => 0)
    | _, _ =>
      let hay := utf8Chars (textOf a0)
      let nee := utf8Chars (textOf a1)
      let idx := (List.range (hay.length + 1)).find? fun i => (hay.drop i).take nee.length == nee
      return .int (match idx with | some i => i + 1 | none => 0)
  | "substr" | "substring" =>
    if nargs < 2 || nargs > 3 then wrong
    if a0.isNull || a1.isNull then return .null
    if nargs == 3 && vs[2]!.isNull then return .null
    let z : Option Int := if nargs == 3 then some vs[2]!.numeric.toInt else none
    let y := a1.numeric.toInt
    match a0 with
    | .blob b =>
      let units := b.toList.map ([·])
      return .blob ⟨((substrOf units y z).flatten).toArray⟩
    | _ =>
      let units := utf8Chars (cstrOf (textOf a0))
      return .text ⟨((substrOf units y z).flatten).toArray⟩
  | "trim" | "ltrim" | "rtrim" =>
    if nargs < 1 || nargs > 2 then wrong
    if a0.isNull then return .null
    if nargs == 2 && a1.isNull then return .null
    let set := if nargs == 2 then utf8Chars (textOf a1) else [[32]]
    let s := utf8Chars (textOf a0)
    return .text ⟨(trimBy s set (name != "rtrim") (name != "ltrim")).flatten.toArray⟩
  | "replace" =>
    if nargs != 3 then wrong
    if vs.any (·.isNull) then return .null
    let s := (textOf a0).toList
    let pat := (textOf a1).toList
    let rep := (textOf vs[2]!).toList
    if pat.isEmpty then return .text (textOf a0)
    let rec goRep (s : List UInt8) (fuel : Nat) : List UInt8 :=
      match fuel with
      | 0 => s
      | f + 1 =>
        match s with
        | [] => []
        | c :: rest => if s.take pat.length == pat then rep ++ goRep (s.drop pat.length) f else c :: goRep rest f
    return .text ⟨(goRep s s.length).toArray⟩
  | "round" =>
    if nargs < 1 || nargs > 2 then wrong
    if a0.isNull then return .null
    if nargs == 2 && a1.isNull then return .null
    let digits : Int := if nargs == 2 then a1.numeric.toInt else 0
    let digits := if digits > 30 then 30 else if digits < 0 then 0 else digits
    return .real ((Printf.round? a0.toReal digits).getD (roundTo a0.toReal digits))
  | "sign" =>
    if nargs != 1 then wrong
    match mathArg a0 with
    | none => return .null
    | some r => return .int (if r > 0 then 1 else if r < 0 then -1 else 0)
  | "min" | "max" =>
    if nargs < 2 then wrong
    if vs.any (·.isNull) then return .null
    let coll := (colls.findSome? id).map (·.1) |>.getD .binary
    let better (a b : Value) : Bool :=
      let o := compareValues coll a b
      if name == "min" then o == .lt else o == .gt
    return vs.foldl (fun acc v => if better v acc then v else acc) a0
  | "zeroblob" =>
    if nargs != 1 then wrong
    let n := max 0 a0.numeric.toInt
    if n > maxLength then err "string or blob too big" SQLITE_TOOBIG
    return .blob ⟨Array.replicate n.toNat 0⟩
  | "likelihood" | "likely" | "unlikely" => return a0
  | "sqlite_version" => return .ofString "3.54.1"
  | "sqlite_source_id" => return .ofString "2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76"
  -- random(), randomblob(N): SQLite's PRNG; the semantics allows any value
  -- (Phase 2.5 states this as a choice); this executable draws from a counter
  | "random" =>
    if nargs != 0 then wrong
    let c ← get
    let seed := c.db.prng
    set { c with db := { c.db with prng := seed + 1 } }
    let x : Nat := (seed * 6364136223846793005 + 1442695040888963407) % 2 ^ 64
    return .int (if x ≥ 2 ^ 63 then (x : Int) - 2 ^ 64 else x)
  | "randomblob" =>
    if nargs != 1 then wrong
    let n := max 1 a0.numeric.toInt
    if n > maxLength then err "string or blob too big" SQLITE_TOOBIG
    let c ← get
    let seed := c.db.prng
    set { c with db := { c.db with prng := seed + 1 } }
    return .blob ⟨(Array.range n.toNat).map fun i => ((seed * 31 + i * 17) % 256).toUInt8⟩
  | "changes" => return .int (← getDb).changes
  | "total_changes" => return .int (← getDb).totalChanges
  | "last_insert_rowid" => return .int (← getDb).lastRowid
  | "concat" =>
    if nargs < 1 then wrong
    return .text (vs.foldl (fun acc v => acc ++ textOf v) .empty)
  | "concat_ws" =>
    if nargs < 2 then wrong
    if a0.isNull then return .null
    let parts := (vs.drop 1).filter (!·.isNull) |>.map textOf
    return .text (match parts with
      | [] => .empty
      | p :: ps => ps.foldl (fun acc x => acc ++ textOf a0 ++ x) p)
  | "glob" | "like" =>
    if nargs < 2 || nargs > 3 then wrong
    if a0.isNull || a1.isNull then return .null
    let cstr (b : ByteArray) : ByteArray := ⟨(b.data.toList.takeWhile (· != 0)).toArray⟩
    let r := if name == "glob" then globMatch (utf8Chars (cstr (textOf a0))) (utf8Chars (cstr (textOf a1)))
      else likeMatch (utf8Chars (cstr (textOf a0))) (utf8Chars (cstr (textOf a1)))
        (if nargs == 3 then (utf8Chars (textOf vs[2]!)).head? else none) true
    return .int (if r then 1 else 0)
  | "pi" => if nargs != 0 then wrong else return .real 3.141592653589793
  | "log" =>
    if nargs < 1 || nargs > 2 then wrong
    if nargs == 1 then
      match mathArg a0 with
      | some x => return mathResult (Float.log10 x)
      | none => return .null
    match mathArg a0, mathArg a1 with
    | some b, some x => return mathResult (Float.log x / Float.log b)
    | _, _ => return .null
  | "pow" | "power" | "atan2" | "mod" =>
    if nargs != 2 then wrong
    match mathArg a0, mathArg a1 with
    | some x, some y =>
      return mathResult (match name with
        | "atan2" => Float.atan2 x y
        | "mod" => x - y * (let t := x / y; if t < 0 then t.ceil else t.floor)
        | _ => Float.pow x y)
    | _, _ => return .null
  | "ceil" | "ceiling" | "floor" | "trunc" =>
    if nargs != 1 then wrong
    match a0 with
    | .int i => return .int i
    | .null => return .null
    | _ =>
      match mathArg a0 with
      | some x => return mathResult (match name with
          | "floor" => x.floor | "trunc" => (if x < 0 then x.ceil else x.floor) | _ => x.ceil)
      | none => return .null
  | _ =>
    match mathUnary name with
    | some f =>
      if nargs != 1 then wrong
      match mathArg a0 with
      | some x => return mathResult (f x)
      | none => return .null
    | none => err s!"no such function: {n}"

/-- The group-free view of an environment (arguments of aggregates). -/
partial def setCur (q : QEnv) (cur : Array Cur) : QEnv :=
  match q.env.frames with
  | f :: rest => { q with env := { q.env with frames := { f with cur } :: rest } }
  | [] => q

/-- A window definition with its base window (named in the WINDOW clause) merged in. -/
partial def resolveWindow (windows : List (Name × Window)) (w : Window) : M Window := do
  let .mk base part ord frame := w
  match base with
  | none => return w
  | some b =>
    match windows.find? (fun (n, _) => nameEq n b) with
    | none => err s!"no such window: {b}"
    | some (_, bw) =>
      let .mk _ bpart bord bframe ← resolveWindow windows bw
      if !part.isEmpty then err s!"cannot override PARTITION clause of window: {b}"
      if !ord.isEmpty && !bord.isEmpty then err s!"cannot override ORDER BY clause of window: {b}"
      return .mk none bpart (if ord.isEmpty then bord else ord) (frame.orElse fun _ => bframe)

/-- Values of one window function call for each row context, and the sorted order of the rows. -/
partial def computeWindow (ctxs : Array QEnv) (windows : List (Name × Window)) (call : Expr) :
    M (Array Value × Array Nat) := do
  let .call n _ args star _ filter (some w0) := call | err "internal: window"
  let .mk _ part ord frame ← resolveWindow windows w0
  let name := n.toLower
  let nrows := ctxs.size
  let pkeys ← ctxs.mapM fun c => part.toArray.mapM (evalExpr c)
  let okeys ← ctxs.mapM fun c => ord.toArray.mapM fun (.mk e _ _) => evalExpr c e
  let pcolls := part.map fun e => ((ctxs[0]?.bind (fun c => exprColl c.env e)).map (·.1)).getD .binary
  let ocolls := ord.map fun (.mk e _ _) => ((ctxs[0]?.bind (fun c => exprColl c.env e)).map (·.1)).getD .binary
  let odirs := ord.map fun (.mk _ d nl) => (d, nl)
  let order := stableSort (fun i j =>
      match lexCompare pcolls [] pkeys[i]! pkeys[j]! with
      | .eq => lexCompare ocolls odirs okeys[i]! okeys[j]!
      | o => o) (Array.range nrows)
  -- partitions: runs of equal partition keys in sorted order
  let mut parts : Array (Array Nat) := #[]
  for i in order do
    match parts.back? with
    | some p => if lexCompare pcolls [] pkeys[p[0]!]! pkeys[i]! == .eq then parts := parts.pop.push (p.push i) else parts := parts.push #[i]
    | none => parts := parts.push #[i]
  -- per-row argument values
  let argv ← ctxs.mapM fun c => args.mapM (evalExpr c)
  let pass ← ctxs.mapM fun c => match filter with
    | some f => do pure (truth (← evalExpr c f) == some true)
    | none => pure true
  let constArg (k : Nat) (dflt : Int) : M Int := do
    match args[k]? with
    | none => return dflt
    | some e => match ← evalExpr (ctxs[0]?.getD {}) e with
      | .int i => return i
      | v => match realAsInt v.numeric.toReal with
        | some i => return i
        | none => return (if v.isNull then dflt else v.numeric.toInt)
  let mut result := Array.replicate nrows Value.null
  let isPeer (a b : Nat) : Bool := lexCompare ocolls odirs okeys[a]! okeys[b]! == .eq
  for p in parts do
    let m := p.size
    let mut firstPeer := Array.replicate m 0
    let mut lastPeer := Array.replicate m 0
    let mut groupIdx := Array.replicate m 0
    let mut g : Nat := 0
    for j in [0:m] do
      if j > 0 && isPeer p[j - 1]! p[j]! then
        firstPeer := firstPeer.set! j firstPeer[j - 1]!
        groupIdx := groupIdx.set! j groupIdx[j - 1]!
      else
        firstPeer := firstPeer.set! j j
        if j > 0 then g := g + 1
        groupIdx := groupIdx.set! j g
    for j' in [0:m] do
      let j := m - 1 - j'
      if j + 1 < m && isPeer p[j]! p[j + 1]! then lastPeer := lastPeer.set! j lastPeer[j + 1]!
      else lastPeer := lastPeer.set! j j
    let ngroups : Nat := g + 1
    let gIdx := groupIdx
    let groupStart (k : Nat) : Nat := ((List.range m).find? (fun x => gIdx[x]! == k)).getD m
    let groupEnd (k : Nat) : Nat := ((List.range m).reverse.find? (fun x => gIdx[x]! == k)).getD 0
    let fP := firstPeer
    let lP := lastPeer
    let frameOf (j : Nat) : M (List Nat) := do
      let fr := frame.getD (if ord.isEmpty then .mk .rows .unboundedPreceding .unboundedFollowing .noOthers
                            else .mk .range .unboundedPreceding .currentRow .noOthers)
      let .mk unit st en excl := fr
      let offset (e : Expr) (start : Bool) : M Value := do
        let v ← evalExpr (ctxs[p[j]!]!) e
        let bad : Bool := match v with
          | .int i => decide (i < 0) | .real r => r < 0.0 | _ => true
        if bad then
          err (if start then "frame starting offset must be a non-negative number" else "frame ending offset must be a non-negative number")
        return v
      let bound (b : FrameBound) (isStart : Bool) : M Int := do
        match b with
        | .unboundedPreceding => return 0
        | .unboundedFollowing => return (m : Int) - 1
        | .currentRow =>
          match unit with
          | .rows => return j
          | _ => return (if isStart then fP[j]! else lP[j]!)
        | .preceding e | .following e =>
          let v ← offset e isStart
          let prec := match b with | .preceding _ => true | _ => false
          match unit with
          | .rows =>
            let k := v.numeric.toInt
            return (if prec then (j : Int) - k else j + k)
          | .groups =>
            let k := v.numeric.toInt
            let tg : Int := if prec then (gIdx[j]! : Int) - k else gIdx[j]! + k
            if tg < 0 then return (if isStart then 0 else -1)
            if tg ≥ ngroups then return (if isStart then m else (m : Int) - 1)
            return (if isStart then groupStart tg.toNat else groupEnd tg.toNat)
          | .range =>
            let key := okeys[p[j]!]![0]?.getD .null
            if key.isNull then return (if isStart then fP[j]! else lP[j]!)
            let desc := match ord.head? with | some (.mk _ d _) => d == .desc | none => false
            let x := key.toReal
            let d := v.toReal
            let target := if prec != desc then x - d else x + d
            let inside (k : Nat) : Bool :=
              let kv := okeys[p[k]!]![0]?.getD .null
              if kv.isNull then false else
              let y := kv.toReal
              if isStart then (if desc then y ≤ target else y ≥ target)
              else (if desc then y ≥ target else y ≤ target)
            if isStart then return (((List.range m).find? inside).getD m : Nat)
            else return (match (List.range m).reverse.find? inside with | some k => (k : Int) | none => -1)
      let lo ← bound st true
      let hi ← bound en false
      let mut out := []
      let mut k := lo
      while k ≤ hi do
        if k ≥ 0 && k < m then
          let kk := k.toNat
          let excluded := match excl with
            | .noOthers => false
            | .currentRow => kk == j
            | .group => isPeer p[kk]! p[j]!
            | .ties => kk != j && isPeer p[kk]! p[j]!
          if !excluded then out := kk :: out
        k := k + 1
      return out.reverse
    for j in [0:m] do
      let row := p[j]!
      let v ← match name with
        | "row_number" => pure (Value.int (j + 1))
        | "rank" => pure (.int (fP[j]! + 1))
        | "dense_rank" => pure (.int (gIdx[j]! + 1))
        | "percent_rank" => pure (.real (if m ≤ 1 then 0.0 else intToReal fP[j]! / intToReal ((m : Int) - 1)))
        | "cume_dist" => pure (.real (intToReal (lP[j]! + 1) / intToReal m))
        | "ntile" =>
          let nt ← constArg 0 1
          if nt ≤ 0 then err "argument of ntile must be a positive integer"
          let nt := nt.toNat
          let base := m / nt
          let extra := m % nt
          let bucket := if j < extra * (base + 1) then j / (base + 1) else extra + (j - extra * (base + 1)) / (max base 1)
          pure (.int (bucket + 1))
        | "lag" | "lead" =>
          let off ← constArg 1 1
          let k : Int := if name == "lag" then (j : Int) - off else j + off
          if k ≥ 0 && k < m then pure ((argv[p[k.toNat]!]!)[0]?.getD .null)
          else match args[2]? with
            | some e => evalExpr ctxs[row]! e
            | none => pure .null
        | "first_value" | "last_value" | "nth_value" =>
          let fr ← frameOf j
          let nth ← constArg 1 1
          if name == "nth_value" && nth ≤ 0 then err "second argument to nth_value must be a positive integer"
          let pick := if name == "first_value" then fr.head?
            else if name == "last_value" then fr.getLast?
            else fr[(nth - 1).toNat]?
          pure ((pick.bind fun k => (argv[p[k]!]!)[0]?).getD .null)
        | _ =>
          if !(isAggCall n args.length star false) then err s!"no such window function: {n}"
          let fr ← frameOf j
          let vals := (fr.filter fun k => pass[p[k]!]!).toArray.map fun k => argv[p[k]!]!
          let coll := ((args.head?.bind fun e => (ctxs[0]?.bind fun c => exprColl c.env e)).map (·.1)).getD .binary
          aggFinish ctxs[row]! n star args coll vals
      result := result.set! row v
  return (result, order)

/-- FROM with WHERE: a chain of inner joins is evaluated as nested loops, each
    conjunct of WHERE and of the ON clauses applied as soon as every source it
    may refer to is bound. Equal to evaluating the joins and then filtering. -/
partial def evalFromWhere (q : QEnv) (f : FromItem) (where_ : Option Expr) (aliases : List (Name × Expr)) :
    M (Array Src × Array (Array Cur)) := do
  let (leavesL, onConds) := innerChain f
  let leaves := leavesL.toArray
  -- leaves whose rows do not depend on earlier leaves are evaluated once;
  -- table-valued functions are evaluated per partial row (their arguments may
  -- refer to earlier sources)
  let mut leafSrcs : Array (Array Src) := #[]
  let mut leafRows : Array (Option (Array (Array Cur))) := #[]
  for lf in leaves do
    match lf with
    | .tableFn _ n _ alias =>
      leafSrcs := leafSrcs.push #[← tableFnSrc n alias]
      leafRows := leafRows.push none
    | _ =>
      let (ss, rs) ← evalFrom q lf
      leafSrcs := leafSrcs.push ss
      leafRows := leafRows.push (some rs)
  let srcs := leafSrcs.foldl (· ++ ·) #[]
  -- the leaf of each source position
  let leafOf : Array Nat := (leafSrcs.mapIdx fun i ss => Array.replicate ss.size i).foldl (· ++ ·) #[]
  let conds := onConds ++ (where_.map conjuncts).getD []
  -- the last leaf a conjunct may refer to
  let level (e : Expr) : Nat := Id.run do
    let mut lv := 0
    for (t, c) in exprRefs e do
      for h : si in [0:srcs.size] do
        let s := srcs[si]
        let hit := match t with
          | some tn => nameEq s.alias tn
          | none => s.cols.any (fun (n, _, _) => nameEq n c) || (s.hasRowid && isRowidName c)
        if hit then lv := max lv leafOf[si]!
    return lv
  let byLevel := conds.map fun e => (level e, e)
  let check (cur : Array Cur) (lv : Nat) : M Bool := do
    let qr := { q with env := { q.env with frames := { srcs := srcs.extract 0 cur.size, cur, aliases } :: q.env.frames, group := none } }
    for (l, e) in byLevel do
      if l == lv then
        if hasAgg e then err "misuse of aggregate function"
        if truth (← evalExpr qr e) != some true then return false
    return true
  let mut partial_ : Array (Array Cur) := #[#[]]
  for h : k in [0:leaves.size] do
    let mut next := #[]
    for pre in partial_ do
      let rows ← match leafRows[k]! with
        | some rs => pure rs
        | none =>
          match leaves[k]! with
          | .tableFn _ n args alias =>
            let qp := { q with env := { q.env with frames := { srcs := srcs.extract 0 pre.size, cur := pre } :: q.env.frames } }
            let vs ← args.mapM (evalExpr qp)
            let rs ← tableFunction n (vs.zip (← args.mapM (argIsJson qp)))
            let _ := alias
            pure (rs.map fun r => #[some r])
          | _ => pure #[]
      for r in rows do
        let cur := pre ++ r
        if ← check cur k then next := next.push cur
    partial_ := next
  return (srcs, partial_)

-- FROM

/-- The rows of a named table, view or CTE, with its source description. -/
partial def namedSource (q : QEnv) (sch : Option Name) (n : Name) (alias : Name) : M (Src × Array Row) := do
  if sch.isNone then
    if let some (_, cv) := q.ctes.find? (fun (m, _) => nameEq m n) then
      let (cols, rows) ← cteRows q n cv
      return (metaSrc alias cols, rows.mapIdx fun i r => ({ rowid := i + 1, vals := r } : Row))
  let db ← getDb
  let tbl ← match sch with
    | none => pure (db.main.findTable n db.attached)
    | some s =>
      if nameEq s "main" || nameEq s "temp" || db.attached.any (nameEq · s) then pure (db.main.findTableDb s n)
      else err s!"no such table: {s}.{n}"
  if let some t := tbl then
    return (tableSrc alias t, t.rows)
  if let some v := db.main.findView n then
    let (cols, rows) ← runSelect { q with ctes := [] } v.q
    let cols := if v.cols.isEmpty then cols else
      (cols.zip v.cols.toArray).map fun (c, nm) => { c with name := nm }
    return (metaSrc alias cols, rows.mapIdx fun i r => ({ rowid := i + 1, vals := r } : Row))
  if nameEq n "sqlite_schema" || nameEq n "sqlite_master" || nameEq n "sqlite_temp_schema" || nameEq n "sqlite_temp_master" then
    let which : Name := if nameEq n "sqlite_temp_schema" || nameEq n "sqlite_temp_master" then "temp" else (sch.getD "main")
    let rows := schemaRows db which
    let cols : Array ColMeta := #["type", "name", "tbl_name", "rootpage", "sql"].map fun c => ⟨c, none, .binary⟩
    return (metaSrc alias cols, rows.mapIdx fun i r => ({ rowid := i + 1, vals := r } : Row))
  err s!"no such table: {n}"

/-- Rows of `sqlite_schema` (or `sqlite_temp_schema`): tables and indexes take
    root pages 2, 3, … in creation order; views and triggers have 0. -/
partial def schemaRows (db : Db) (which : Name := "main") : Array (Array Value) := Id.run do
  let mut out := #[]
  let mut page : Int := 1
  for o in db.main.objs do
    let dbn : Name := match o with
      | .table t => t.dbName
      | .view v => v.attachedTo.getD (if v.temp then "temp" else "main")
      | .index ix => ((db.main.findTable ix.table db.attached).map (·.dbName)).getD "main"
      | .trigger tr => ((db.main.findTable tr.table db.attached).map (·.dbName)).getD "main"
    if !nameEq dbn which then continue
    match o with
    | .table t =>
      page := page + 1
      out := out.push #[.ofString "table", .ofString t.name, .ofString t.name, .int page, .ofString t.sql]
    | .index ix =>
      page := page + 1
      out := out.push #[.ofString "index", .ofString ix.name, .ofString ix.table, .int page,
        match ix.sql with | some s => .ofString s | none => .null]
    | .view v => out := out.push #[.ofString "view", .ofString v.name, .ofString v.name, .int 0, .ofString v.sql]
    | .trigger tr => out := out.push #[.ofString "trigger", .ofString tr.name, .ofString tr.table, .int 0, .ofString tr.sql]
  return out

partial def cteRows (q : QEnv) (n : Name) : CteVal → M (Array ColMeta × Array (Array Value))
  | .rows cols rows => return (cols, rows)
  | .defn names sel rec_ => do
    -- the CTE is not visible in its own body unless recursive
    let others := q.ctes.filter fun (m, _) => !nameEq m n
    let rename (cols : Array ColMeta) : M (Array ColMeta) := do
      if names.isEmpty then return cols
      if names.length != cols.size then
        err s!"table {n} has {cols.size} values for {names.length} columns"
      return (cols.zip names.toArray).map fun (c, nm) => { c with name := nm }
    let .mk with_ wrec first rest ob lim off := sel
    let isRec := rec_ && !rest.isEmpty && (rest.any fun (_, c) => coreRefers n c)
    if !isRec then
      let (cols, rows) ← runSelect { q with ctes := others } sel
      return (← rename cols, rows)
    -- recursive: the cores that do not refer to n are the initial part; the
    -- rest run on each row taken from the queue
    let allCores := (CompoundOp.unionAll, first) :: rest
    let initial := allCores.filter fun (_, c) => !coreRefers n c
    let recursive := allCores.filter fun (_, c) => coreRefers n c
    let distinctMode := recursive.any fun (o, _) => o == .union
    let limit ← match lim with
      | some l => some <$> (limitValue (← evalExpr q l))
      | none => pure none
    let offset ← match off with
      | some o => limitValue (← evalExpr q o)
      | none => pure 0
    let mut cols : Array ColMeta := #[]
    let mut queue : Array (Array Value) := #[]
    let mut seen : Array (Array Value) := #[]
    for (_, c) in initial do
      let (cs, rows) ← runSelect { q with ctes := others } (.mk with_ wrec c [] [] none none)
      if cols.isEmpty then cols ← rename cs
      for r in rows do
        if distinctMode then
          if seen.any (rowsEq [] r) then continue
          seen := seen.push r
        queue := queue.push r
    let mut out : Array (Array Value) := #[]
    let mut skipped : Int := 0
    let mut steps := 0
    while !queue.isEmpty do
      -- ORDER BY on a recursive CTE makes the queue a priority queue
      let (row, rest') ← if ob.isEmpty then pure (queue[0]!, queue.extract 1 queue.size)
        else do
          let keys ← queue.mapM fun r => ob.toArray.mapM fun (.mk e _ _) =>
            evalExpr { q with env := { q.env with frames := { srcs := #[metaSrc n cols], cur := #[some { rowid := 0, vals := r }] } :: q.env.frames } } e
          let dirs := ob.map fun (.mk _ d nl) => (d, nl)
          let mut best := 0
          for i in [1:queue.size] do
            if lexCompare [] dirs keys[i]! keys[best]! == .lt then best := i
          pure (queue[best]!, (queue.extract 0 best) ++ (queue.extract (best + 1) queue.size))
      queue := rest'
      if skipped < offset then skipped := skipped + 1
      else
        if let some l := limit then
          if l ≥ 0 && out.size ≥ l.toNat then break
        out := out.push row
      steps := steps + 1
      let ctesRow := (n, CteVal.rows cols #[row]) :: others
      for (_, c) in recursive do
        let (_, rows) ← runSelect { q with ctes := ctesRow } (.mk with_ wrec c [] [] none none)
        for r in rows do
          if distinctMode then
            if seen.any (rowsEq [] r) then continue
            seen := seen.push r
          queue := queue.push r
    return (cols, out)

/-- Does a select core refer to table name `n` in its FROM (directly)? -/
partial def coreRefers (n : Name) : SelectCore → Bool
  | .select _ _ (some f) _ _ _ _ => fromRefers n f
  | _ => false

partial def fromRefers (n : Name) : FromItem → Bool
  | .table none m _ _ => nameEq m n
  | .join l _ _ r _ _ => fromRefers n l || fromRefers n r
  | .subquery (.mk _ _ c rest _ _ _) _ => coreRefers n c || rest.any (fun (_, x) => coreRefers n x)
  | _ => false

/-- Evaluate a FROM clause: its sources and joined rows (one `Cur` per source). -/
partial def evalFrom (q : QEnv) : FromItem → M (Array Src × Array (Array Cur))
  | .table sch n alias _ => do
    let (src, rows) ← namedSource q sch n (alias.getD n)
    return (#[src], rows.map fun r => #[some r])
  | .subquery sel alias => do
    let (cols, rows) ← runSelect q sel
    return (#[metaSrc (alias.getD "") cols], rows.mapIdx fun i r => #[some ({ rowid := i + 1, vals := r } : Row)])
  | .tableFn sch n args alias => do
    let _ := sch
    let vs ← args.mapM (evalExpr q)
    let rows ← tableFunction n (vs.zip (← args.mapM (argIsJson q)))
    return (#[← tableFnSrc n alias], rows.map fun r => #[some r])
  | .join l kind natural r on usingCols => do
    let (ls, lrows) ← evalFrom q l
    -- a table-valued function on the right may refer to the left sources: its
    -- rows are computed per left row
    let (rs, rrows0) ← match r with
      | .tableFn _ n _ alias => do
        pure (#[← tableFnSrc n alias], #[])
      | _ => evalFrom q r
    let rowsFor (lr : Array Cur) : M (Array (Array Cur)) := do
      match r with
      | .tableFn _ n args _ =>
        let qp := { q with env := { q.env with frames := { srcs := ls, cur := lr } :: q.env.frames } }
        let vs ← args.mapM (evalExpr qp)
        let rows ← tableFunction n (vs.zip (← args.mapM (argIsJson qp)))
        pure (rows.map fun row => #[some row])
      | _ => pure rrows0
    let srcs := ls ++ rs
    -- USING / NATURAL columns: equality on each, right copy hidden from *
    let common : List Name :=
      if natural then
        let lnames := ls.toList.flatMap fun s => s.cols.toList.map (·.1)
        (rs.toList.flatMap fun s => s.cols.toList.map (·.1)).filter fun c => lnames.any (nameEq · c)
      else usingCols
    for c in common do
      if !(ls.any fun s => s.cols.any fun (m, _, _) => nameEq m c) || !(rs.any fun s => s.cols.any fun (m, _, _) => nameEq m c) then
        err s!"cannot join using column {c} - column not present in both tables"
    let rsHidden := rs.map fun s => { s with hidden := s.hidden ++ (List.range s.cols.size).filter fun i => common.any (nameEq · s.cols[i]!.1) }
    let srcs' := ls ++ rsHidden
    let nl := ls.size
    let joinCond (cur : Array Cur) : M Bool := do
      let q' := { q with env := { q.env with frames := { srcs := srcs, cur } :: q.env.frames } }
      for c in common do
        let lv ← evalExpr { q' with env := { q'.env with frames := { srcs := ls, cur := cur.extract 0 nl } :: q.env.frames } } (.col none none c)
        let rv ← evalExpr { q' with env := { q'.env with frames := { srcs := rs, cur := cur.extract nl cur.size } :: q.env.frames } } (.col none none c)
        if truth (compareOp .eq none .binary lv rv) != some true then return false
      match on with
      | some e => return truth (← evalExpr q' e) == some true
      | none => return true
    let mut out := #[]
    let rrows := rrows0
    let mut rmatched := Array.replicate rrows.size false
    for lr in lrows do
      let rrows ← rowsFor lr
      let mut any := false
      for h : j in [0:rrows.size] do
        let cur := lr ++ rrows[j]
        if ← joinCond cur then
          out := out.push cur; any := true
          if j < rmatched.size then rmatched := rmatched.set! j true
      if !any && (kind == .left || kind == .full) then
        out := out.push (lr ++ Array.replicate rs.size none)
    if kind == .right || kind == .full then
      for h : j in [0:rrows.size] do
        if !rmatched[j]! then out := out.push (Array.replicate nl none ++ rrows[j])
    -- in a RIGHT/FULL join the USING column comes from whichever side is non-NULL;
    -- modelled by not hiding the right copy for such joins
    let srcs'' := if kind == .right || kind == .full then srcs else srcs'
    return (srcs'', out)

/-- The source of a table-valued function (its columns; `json` and `root` of
    json_each/json_tree are hidden). -/
partial def tableFnSrc (n : Name) (alias : Option Name) : M Src := do
  if Json.tableFns.contains n.toLower then
    let cols : Array ColMeta := Json.eachColumns.toArray.map fun c => ⟨c, none, .binary⟩
    return { metaSrc (alias.getD n) cols with hiddenStar := [8, 9] }
  err s!"no such table: {n}"

/-- The rows of a table-valued function. -/
partial def tableFunction (n : Name) (argsJ : List (Value × Bool)) : M (Array Row) := do
  match Json.tableFnST? n.toLower argsJ with
  | some (.ok (_, rows)) =>
    return rows.toArray.mapIdx fun i (vs, j) => { rowid := i + 1, vals := vs.toArray, jsonCols := if j then [1] else [] }
  | some (.error e) => throw e
  | none => err s!"no such table: {n}"

-- SELECT

partial def resultName (q : QEnv) (srcs : Array Src) : ResultCol → Name
  | .expr _ (some a) _ => a
  | .expr (.col _ _ c) none _ =>
    -- the declared name of the column
    match srcs.toList.findSome? fun s => s.cols.toList.find? fun (m, _, _) => nameEq m c with
    | some (m, _, _) => m
    | none => if isRowidName c then c else c
  | .expr _ none txt => txt
  | _ => let _ := q; ""

/-- Expand `*` and `t.*` into column references. -/
partial def expandCols (srcs : Array Src) (cols : List ResultCol) : M (List ResultCol) := do
  let mut out := #[]
  for c in cols do
    match c with
    | .star =>
      if srcs.isEmpty then err "no tables specified"
      for s in srcs do
        for h : i in [0:s.cols.size] do
          if !s.hidden.contains i && !s.hiddenStar.contains i then
            let (nm, _, _) := s.cols[i]
            out := out.push (.expr (.col none (some s.alias) nm) (some nm) nm)
    | .tableStar t =>
      match srcs.toList.find? (fun s => nameEq s.alias t) with
      | some s =>
        for h : i in [0:s.cols.size] do
          if !s.hiddenStar.contains i then
            let (nm, _, _) := s.cols[i]
            out := out.push (.expr (.col none (some s.alias) nm) (some nm) nm)
      | none => err s!"no such table: {t}"
    | c => out := out.push c
  return out.toList

/-- One SELECT core: result metadata and rows, plus the sort keys of
    `orderBy` evaluated per row (for a simple, non-compound select). -/
partial def runCore (q : QEnv) (core : SelectCore) (orderBy : List OrderTerm) :
    M (Array ColMeta × Array (Array Value × Array Value)) := do
  match core with
  | .values rows =>
    let mut out := #[]
    let mut width : Option Nat := none
    for r in rows do
      if let some w := width then
        if w != r.length then err "all VALUES must have the same number of terms"
      width := some r.length
      out := out.push ((← r.toArray.mapM (evalExpr q)), #[])
    let cols : Array ColMeta := (List.range (width.getD 0)).toArray.map fun i => ⟨s!"column{i + 1}", none, .binary⟩
    return (cols, out)
  | .select distinct cols from_ where_ groupBy having windows =>
    let _ := windows
    -- result-column aliases usable in WHERE (`*` columns resolve as columns anyway)
    let aliases0 := cols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
    let (srcs, rows) ← match from_ with
      | some f => evalFromWhere q f where_ aliases0
      | none => pure (#[], #[#[]])
    let rcols ← expandCols srcs cols
    let frameOf (cur : Array Cur) : Scope := { srcs, cur }
    let withFrame (cur : Array Cur) (aliases : List (Name × Expr) := []) : QEnv :=
      { q with env := { q.env with frames := { frameOf cur with aliases } :: q.env.frames, group := none } }
    let exprs := rcols.filterMap fun | .expr e _ _ => some e | _ => none
    let aliases := rcols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
    -- WHERE (with a FROM clause it was applied while joining)
    let mut kept := #[]
    for cur in rows do
      match where_, from_ with
      | some w, none =>
        if hasAgg w then err "misuse of aggregate function"
        if truth (← evalExpr (withFrame cur aliases) w) == some true then kept := kept.push cur
      | _, _ => kept := kept.push cur
    let qm := withFrame (Array.replicate srcs.size none)
    let cmeta : Array ColMeta := rcols.toArray.map fun rc =>
      match rc with
      | .expr e _ _ => ⟨resultName q srcs rc, exprAff qm.env e, ((exprColl qm.env e).map (·.1)).getD .binary⟩
      | _ => ⟨"", none, .binary⟩
    -- ORDER BY terms: a result column number, a result alias, or an expression
    let obExpr (t : OrderTerm) : M Expr := do
      let .mk e _ _ := t
      match e with
      | .lit (.int i) =>
        if i < 1 || i > exprs.length then
          err s!"ORDER BY term out of range - should be between 1 and {exprs.length}"
        return exprs[(i - 1).toNat]!
      | .col none none c =>
        match aliases.find? (fun (a, _) => nameEq a c) with
        | some (_, x) => return x
        | none => return e
      | _ => return e
    let obExprs ← orderBy.mapM obExpr
    let isAgg := !groupBy.isEmpty || exprs.any hasAgg || (having.map hasAgg).getD false || obExprs.any hasAgg
    -- window calls become numbered placeholders, computed over the row contexts
    let (wexprs, wcalls) := replaceWindows (exprs ++ obExprs)
    let exprs := wexprs.take exprs.length
    let obExprs := wexprs.drop exprs.length
    let mut ctxs : Array QEnv := #[]
    let mut out : Array (Array Value × Array Value) := #[]
    if isAgg then
      -- groups, in order of their key
      let mut groups : Array (Array Value × Array (Array Cur)) := #[]
      let mut gindex : Std.HashMap String Nat := {}
      for cur in kept do
        let key ← groupBy.toArray.mapM fun g => do
          let g' := match g with
            | .lit (.int i) => (exprs[(i - 1).toNat]?).getD g
            | _ => g
          if hasAgg g' then err "aggregate functions are not allowed in the GROUP BY clause"
          evalExpr (withFrame cur aliases) g'
        let gcolls := groupBy.map fun g => ((exprColl qm.env g).map (·.1)).getD .binary
        let ck := canonKey gcolls key
        match gindex.get? ck with
        | some i => groups := groups.modify i fun (k, rs) => (k, rs.push cur)
        | none =>
          gindex := gindex.insert ck groups.size
          groups := groups.push (key, #[cur])
      if groupBy.isEmpty && groups.isEmpty then groups := #[(#[], #[])]
      let gcolls := groupBy.map fun g => ((exprColl qm.env g).map (·.1)).getD .binary
      if !groupBy.isEmpty then groups := stableSort (fun a b => lexCompare gcolls [] a.1 b.1) groups
      -- the row bare columns are read from: the min/max row if there is exactly one
      -- min()/max() aggregate, else the last row of the group
      let minmax := exprs.filterMap fun e => match e with
        | .call n false [a] false [] none none =>
          if nameEq n "min" || nameEq n "max" then some (nameEq n "min", a) else none
        | _ => none
      for (_, grp) in groups do
        let mut rep : Array Cur := grp.back?.getD (Array.replicate srcs.size none)
        if minmax.length == 1 && !grp.isEmpty then
          let (isMin, a) := minmax[0]!
          let coll := ((exprColl qm.env a).map (·.1)).getD .binary
          let mut best : Option (Value × Array Cur) := none
          for cur in grp do
            let v ← evalExpr (withFrame cur) a
            if v.isNull then continue
            match best with
            | none => best := some (v, cur)
            | some (bv, _) =>
              let o := compareValues coll v bv
              if (isMin && o == .lt) || (!isMin && o == .gt) then best := some (v, cur)
          if let some (_, cur) := best then rep := cur
        let qg := { withFrame rep aliases with env := { (withFrame rep aliases).env with group := some grp } }
        if let some h := having then
          if truth (← evalExpr qg h) != some true then continue
        ctxs := ctxs.push qg
    else
      if having.isSome then err "HAVING clause on a non-aggregate query"
      for cur in kept do
        ctxs := ctxs.push (withFrame cur aliases)
    -- window functions: each call's values; rows come out in the windows' sort order
    let mut order := Array.range ctxs.size
    let mut wvals : Array (Array Value) := #[]
    for c in wcalls do
      let (vs, ord) ← computeWindow ctxs windows c
      wvals := wvals.push vs
      if !(match c with | .call _ _ _ _ _ _ (some (.mk none [] [] _)) => true | _ => false) then order := ord
    for i in order do
      let base := ctxs[i]!
      let qi := { base with env := { base.env with params := (wvals.toList.zipIdx.map fun (vs, k) => (windowParamBase + k, vs[i]!)) ++ base.env.params } }
      let vals ← exprs.toArray.mapM (evalExpr qi)
      let keys ← obExprs.toArray.mapM (evalExpr qi)
      out := out.push (vals, keys)
    if distinct then
      let colls := cmeta.toList.map (·.coll)
      let mut d := #[]
      let mut seen : Std.HashSet String := {}
      for r in out do
        let k := canonKey colls r.1
        if !seen.contains k then
          seen := seen.insert k
          d := d.push r
      out := d
    return (cmeta, out)

partial def runSelect (q : QEnv) (sel : Select) : M (Array ColMeta × Array (Array Value)) := do
  let .mk with_ rec_ first rest orderBy limit offset := sel
  let q := { q with ctes := (with_.map fun (.mk n cols _ s) => (n, CteVal.defn cols s rec_)) ++ q.ctes }
  let limitN ← match limit with
    | some l => some <$> limitValue (← evalExpr q l)
    | none => pure none
  let offsetN ← match offset with
    | some o => limitValue (← evalExpr q o)
    | none => pure 0
  let dirs := orderBy.map fun (.mk _ d nl) => (d, nl)
  let (cols, rows) ← if rest.isEmpty then do
      let (cols, rows) ← runCore q first orderBy
      let colls := orderBy.map fun (.mk e _ _) =>
        match e with
        | .collate _ c => (collOfName c).getD .binary
        | .lit (.int i) => (cols[(i - 1).toNat]?.map (·.coll)).getD .binary
        | _ => ((exprColl { q.env with frames := q.env.frames } e).map (·.1)).getD
            ((cols.toList.find? fun c => match e with | .col _ _ n => nameEq c.name n | _ => false).map (·.coll) |>.getD .binary)
      let rows := if orderBy.isEmpty then rows else stableSort (fun a b => lexCompare colls dirs a.2 b.2) rows
      pure (cols, rows.map (·.1))
    else do
      let (cols, rows0) ← runCore q first []
      -- multiSelectCollSeq: each column's collation is that of the leftmost
      -- SELECT that has one for it
      let mutable_cores ← rest.mapM fun (op, core) => do
        let (cs, rs) ← runCore q core []
        pure (op, cs, rs)
      let colls := (List.range cols.size).map fun i =>
        let all := (cols :: mutable_cores.map (·.2.1)).filterMap fun cs => cs[i]?.map (·.coll)
        (all.find? (· != .binary)).getD .binary
      let cols := cols.mapIdx fun i c => { c with coll := colls[i]! }
      let mut acc := rows0.map (·.1)
      for (op, cs, rs) in mutable_cores do
        if cs.size != cols.size then
          err s!"SELECTs to the left and right of {match op with | .union => "UNION" | .unionAll => "UNION ALL" | .intersect => "INTERSECT" | .except => "EXCEPT"} do not have the same number of result columns"
        let rs := rs.map (·.1)
        match op with
        | .unionAll => acc := acc ++ rs
        | .union =>
          -- SQLite's union index: the left side's duplicates keep the first row;
          -- a row of the right side replaces an equal row already there
          let mut idx : Std.HashMap String Nat := {}
          let mut out : Array (Array Value) := #[]
          for r in acc do
            let k := canonKey colls r
            if !idx.contains k then
              idx := idx.insert k out.size
              out := out.push r
          for r in rs do
            let k := canonKey colls r
            match idx.get? k with
            | some i => out := out.set! i r
            | none =>
              idx := idx.insert k out.size
              out := out.push r
          acc := stableSort (lexCompare colls []) out
        | .intersect =>
          let rk : Std.HashSet String := rs.foldl (fun st r => st.insert (canonKey colls r)) {}
          acc := stableSort (lexCompare colls []) (dedupe colls (acc.filter fun r => rk.contains (canonKey colls r)))
        | .except =>
          let rk : Std.HashSet String := rs.foldl (fun st r => st.insert (canonKey colls r)) {}
          acc := stableSort (lexCompare colls []) (dedupe colls (acc.filter fun r => !rk.contains (canonKey colls r)))
      -- ORDER BY of a compound refers to result columns
      if orderBy.isEmpty then pure (cols, acc) else
      let mut idx := #[]
      for h : k in [0:orderBy.length] do
        let .mk e _ _ := orderBy[k]
        let i ← match e with
          | .lit (.int i) =>
            if i < 1 || i > cols.size then err s!"ORDER BY term out of range - should be between 1 and {cols.size}"
            pure (i - 1).toNat
          | .col none none c | .collate (.col none none c) _ =>
            match cols.toList.findIdx? (fun m => nameEq m.name c) with
            | some i => pure i
            | none => err s!"{ordinal (k + 1)} ORDER BY term does not match any column in the result set"
          | _ => err s!"{ordinal (k + 1)} ORDER BY term does not match any column in the result set"
        idx := idx.push i
      let ocolls := (List.range orderBy.length).map fun k =>
        match orderBy[k]! with
        | .mk (.collate _ c) _ _ => (collOfName c).getD .binary
        | _ => (cols[idx[k]!]?.map (·.coll)).getD .binary
      let keyed := acc.map fun r => (r, idx.map fun i => r[i]!)
      pure (cols, (stableSort (fun a b => lexCompare ocolls dirs a.2 b.2) keyed).map (·.1))
  let rows := rows.extract offsetN.toNat rows.size
  let rows := match limitN with
    | some l => if l < 0 then rows else rows.extract 0 l.toNat
    | none => rows
  return (cols, rows)

partial def ordinal (k : Nat) : String :=
  match k with
  | 1 => "1st" | 2 => "2nd" | 3 => "3rd" | n => s!"{n}th"

end

end Sql
