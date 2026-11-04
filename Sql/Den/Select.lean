/-
  The denotation of Sql/Select.lean (Phase 2.6): derived by scripts/dev/denize.py, then
  edited where the interpreter has fuel, a choice oracle or a strategy.
-/
import Sql.Den.Join

namespace Sql.Den

open Sql Lean.Order

def getDb : D Db := return (← get).db


/-- The integer value of a LIMIT/OFFSET expression. -/
def limitValue (v : Value) : D Int := do
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


/-- The arity rules of `pragma function_list` for the lazy built-ins. -/
def checkArity (n : Name) (k : Nat) : D Unit := do
  let low := n.toLower
  let ok := if low == "ifnull" then k == 2 else k ≥ 2
  if !ok then err s!"wrong number of arguments to function {n}()"


/-- Expression affinity, with scalar subqueries resolved against the schema. -/
def affOf (env : Env) (e : Expr) : D (Option Aff) := do
  return exprAff env e (subqueryAffK (← getDb) syntaxFuel)


mutual

def evalExpr (q : QEnv) (e : Expr) : D Value :=
    do
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
          let x := v.toInt
          return .int (-x - 1)
      | .binop op a b =>
        match op with
        | .and | .or =>
          -- exprCodeTargetAndOr: both operands are computed, except that a
          -- subquery operand is skipped when the other decides the result
          let isAnd := match op with | .and => true | _ => false
          let decides (v : Value) : Bool := truth v == some !isAnd
          match andOrAlt env e with
          | some alt =>
            let v ← evalExpr q alt
            return andOrValue true v v
          | none =>
            if hasSubquery a && !hasSubquery b then
              let y ← evalExpr q b
              if decides y then return andOrValue true y y
              let x ← evalExpr q a
              return andOrValue isAnd x y
            else
              let x ← evalExpr q a
              if hasSubquery b && decides x then return andOrValue true x x
              let y ← evalExpr q b
              return andOrValue isAnd x y
        | .lt | .le | .gt | .ge | .eq | .ne =>
          match a, b with
          | .row xs, .row ys => compareRows q op xs ys
          | _, _ =>
            let x ← evalExpr q a
            let y ← evalExpr q b
            return compareOp op (cmpAff ((← affOf env a)) ((← affOf env b))) (cmpColl env a b) x y
        | .is | .isNot =>
          -- `x IS [NOT] TRUE/FALSE` (true/false not a column) is a truth test (TK_TRUTH)
          if let some tv := truthConstOf env b then
            let x ← evalExpr q a
            let holds := truth x == some tv
            return .int (if holds == (op == .is) then 1 else 0)
          let x ← evalExpr q a
          let y ← evalExpr q b
          let aff := cmpAff (← affOf env a) (← affOf env b)
          let same := match x.isNull, y.isNull with
            | true, true => true
            | true, false | false, true => false
            | false, false =>
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
        let c1 := compareOp .ge (cmpAff ((← affOf env x)) ((← affOf env lo))) (cmpColl env x lo) v l
        let c2 := compareOp .le (cmpAff ((← affOf env x)) ((← affOf env hi))) (cmpColl env x hi) v h
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
          let c := compareOp .eq ((← affOf env x)) (cmpColl env x it) v w
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
        let aff := cmpAff ((← affOf env x)) (cols[0]!.aff)
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
        let (_, rows) ← runSelect q sub (cap := true)
        return .int (if rows.isEmpty then 0 else 1)
      | .subquery sub =>
        let (cols, rows) ← runSelect q sub (cap := true)
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
        -- ROLLBACK rolls the transaction back; FAIL keeps the statement's
        -- changes so far; ABORT undoes the statement
        | .rollback => throw { code := SQLITE_CONSTRAINT_TRIGGER, msg := m, rollback := true }
        | .fail => throw { code := SQLITE_CONSTRAINT_TRIGGER, msg := m, keep := true }
        | _ => throw { code := SQLITE_CONSTRAINT_TRIGGER, msg := m }
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def compareRows (q : QEnv) (op : BinOp) (xs ys : List Expr) : D Value :=
    do
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
        let o := compareValues (cmpColl q.env a b) (cmpConvert (cmpAff ((← affOf q.env a)) ((← affOf q.env b))) x)
          (cmpConvert (cmpAff ((← affOf q.env a)) ((← affOf q.env b))) y)
        if o != .eq then
          result := some (match op with
            | .eq => false | .ne => true | .lt | .le => o == .lt | _ => o == .gt)
          unknown := false
          return boolV result
      if unknown then return .null
      return boolV (if op == .ne then some false else result)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def valueOf (q : QEnv) (r0 : Resolved) : D Value :=
    match r0 with
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- An aggregate call over the current group. -/
def evalAgg (q : QEnv) (n : Name) (distinct : Bool) (args : List Expr) (star : Bool)
    (ob : List OrderTerm) (filter : Option Expr) : D Value :=
    do
      if distinct && args.length != 1 then err "DISTINCT aggregates must have exactly one argument"
      let some grp := q.env.group | err s!"misuse of aggregate function {n}()"
      let name := n.toLower
      -- evaluate arguments per row of the group, in the context of that row
      let mut rows : Array (List Value × Array Value) := #[]
      let mut jflags : Array (List Bool) := #[]
      for cur in grp do
        let q' := setCur q cur
        if let some fl := filter then
          if !(← condHolds q'.noGroup fl) then continue
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- An aggregate over the argument lists of its rows (after FILTER, ORDER BY, DISTINCT). -/
def aggFinish (q : QEnv) (n : Name) (star : Bool) (args : List Expr) (coll : Coll)
    (vals : Array (List Value)) (jflags : Option (Array (List Bool)) := none) : D Value :=
    do
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- Aggregates implemented elsewhere (JSON). -/
def callAgg (_q : QEnv) (name : String) (vals : Array (List Value)) (flags : List Bool)
    (rowFlags : Option (Array (List Bool)) := none) : D Value :=
      let rows := match rowFlags with
        | some fs => (vals.zip fs).toList.map fun (vs, f) => vs.zip (f.zipWith (· || ·) flags)
        | none => vals.toList.map fun vs => vs.zip flags
      match Json.aggregate? name rows with
      | some (.ok v) => pure v
      | some (.error e) => throw e
      | none => err s!"no such function: {name}"
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- Does an argument carry the JSON subtype: a JSON-valued expression, or a
    column whose current value has it (`json_each.value`)? -/
def argIsJson (q : QEnv) (a : Expr) : D Bool :=
    do
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def callFn (q : QEnv) (n : Name) (args : List Expr) (distinct : Bool) : D Value :=
      return (← callFnST q n args distinct).1
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- A scalar call, with whether its result carries the JSON subtype: a JSON
    function says so; coalesce/ifnull/iif/nullif/likely/unlikely/likelihood and
    two-or-more-argument min/max pass on the subtype of the argument they
    return (checked against SQLite by the JSON lane, tests/sem/json_subtype.sql). -/
def callFnST (q : QEnv) (n : Name) (args : List Expr) (_distinct : Bool) : D (Value × Bool) :=
    do
      -- coalesce/ifnull/iif are compiled to jumps: later arguments are evaluated
      -- only if needed
      let low := n.toLower
      -- subtype(X): 74 ('J') for a value with the JSON subtype, else 0
      if low == "subtype" then
        let [x] := args | err s!"wrong number of arguments to function {n}()"
        let (_, j) ← evalExprST q x
        return (.int (if j then 74 else 0), false)
      if low == "coalesce" || low == "ifnull" then
        checkArity n args.length
        for a in args do
          let (v, f) ← evalExprST q a
          if !v.isNull then return (v, f)
        return (.null, false)
      if low == "iif" || low == "if" then
        checkArity n args.length
        -- iif(c1, v1, c2, v2, …, else): the first true condition's value
        let arr := args.toArray
        let mut i := 0
        for _ in [0:arr.size] do
          if i + 1 < arr.size then
            if ← condHolds q arr[i]! then return ← evalExprST q arr[i + 1]!
            i := i + 2
        if i < arr.size then return ← evalExprST q arr[i]!
        return (.null, false)
      let evs ← args.mapM (evalExprST q)
      let vs := evs.map (·.1)
      let flags := evs.map (·.2)
      -- an arity error names the function as written
      let fixName (e : Err) : Err :=
        let low := s!"wrong number of arguments to function {n.toLower}()"
        if e.msg == low then { e with msg := s!"wrong number of arguments to function {n}()" } else e
      let lift (r : Except Err Value) : D (Value × Bool) := match r with
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
      match DateTime.scalar? { unixMs := (← get).clockMs } n.toLower vs with
      | some r => lift r
      | none =>
        let v ← (try scalarFn n vs (args.map fun a => exprColl q.env a) catch e => throw (fixName e))
        -- the argument whose value is returned passes its subtype on
        let pick : Option Nat := match n.toLower with
          | "coalesce" | "ifnull" => vs.findIdx? (!·.isNull)
          | "nullif" | "likely" | "unlikely" | "likelihood" => if v.isNull then none else some 0
          | "iif" | "if" => iifIndex vs
          | "min" | "max" =>
            if vs.length < 2 then none else
            let same := fun x => compareValues .binary x v == .eq && x.rank == v.rank
            -- the argument min()/max() returned (min: the last of equal ones)
            if n.toLower == "min" then (vs.reverse.findIdx? same).map (vs.length - 1 - ·) else vs.findIdx? same
          | _ => none
        return (v, (pick.bind (flags[·]?)).getD false)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- A condition coded as a jump (`sqlite3ExprIfTrue` when `sense`,
    `sqlite3ExprIfFalse` otherwise; `jn`: SQLITE_JUMPIFNULL): whether the
    jump is taken. AND/OR evaluate their second operand only when the first
    does not decide the jump. -/
def condJump (q : QEnv) (e : Expr) (sense jn : Bool) : D Bool :=
  do
    let env := q.env
    match e with
    | .binop .and a b | .binop .or a b =>
      let isAnd := match e with | .binop .and .. => true | _ => false
      match andOrAlt env e with
      | some alt => condJump q alt sense jn
      | none =>
        -- the right side first when only the left has a subquery
        let swap := hasSubquery a && !hasSubquery b
        let f1 := if swap then b else a
        let f2 := if swap then a else b
        let ((s1, j1), short, (s2, j2)) := jumpPlan isAnd sense jn
        if ← condJump q f1 s1 j1 then return short
        condJump q f2 s2 j2
    | .binop .is a b | .binop .isNot a b =>
      let isNot := match e with | .binop .isNot .. => true | _ => false
      match truthConstOf env b with
      | some tv =>
        -- TK_TRUTH
        if sense then condJump q a (tv != isNot) isNot
        else condJump q a (tv == isNot) (!isNot)
      | none => return jumpOf (← evalExpr q e) sense jn
    | .unop .not a => condJump q a (!sense) jn
    | .between true x lo hi => condJump q (.between false x lo hi) (!sense) jn
    | .between false x lo hi =>
      -- exprCodeBetween: x once, then (x >= lo) AND (x <= hi) as jumps
      let xv ← evalExpr q x
      let ((s1, j1), short, (s2, j2)) := jumpPlan true sense jn
      let l ← evalExpr q lo
      if jumpOf (compareOp .ge (cmpAff (← affOf env x) (← affOf env lo)) (cmpColl env x lo) xv l) s1 j1 then
        return short
      let h ← evalExpr q hi
      return jumpOf (compareOp .le (cmpAff (← affOf env x) (← affOf env hi)) (cmpColl env x hi) xv h) s2 j2
    | _ => return jumpOf (← evalExpr q e) sense jn
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- A WHERE, ON, HAVING, FILTER, CASE WHEN or trigger WHEN condition holds
    (`sqlite3ExprIfFalse(e, skip, SQLITE_JUMPIFNULL)` not taken). -/
def condHolds (q : QEnv) (e : Expr) : D Bool := do
  return !(← condJump q e false true)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- An expression's value and whether it carries the JSON subtype. -/
def evalExprST (q : QEnv) (e : Expr) : D (Value × Bool) :=
    do
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
            let c := compareOp .eq (cmpAff ((← affOf q.env b)) ((← affOf q.env w))) (cmpColl q.env b w) bv wv
            if truth c == some true then return ← evalExprST q t
          match els with
          | some x => evalExprST q x
          | none => return (.null, false)
        | none =>
          for (w, t) in whens do
            if ← condHolds q w then return ← evalExprST q t
          match els with
          | some x => evalExprST q x
          | none => return (.null, false)
      | .col _ _ _ => return (← evalExpr q e, ← argIsJson q e)
      | _ => return (← evalExpr q e, false)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- Scalar functions. -/
def scalarFn (n : Name) (vs : List Value) (colls : List (Option (Coll × Bool))) : D Value :=
    do
      let name := n.toLower
      let wrong {α} : D α := err s!"wrong number of arguments to function {n}()"
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
      -- extension loading is off by default (SQLITE_LoadExtFunc)
      | "load_extension" =>
        if nargs < 1 || nargs > 2 then wrong
        err "not authorized"
      -- the MATCH operator's function form: only virtual tables provide it
      | "match" =>
        if nargs != 2 then wrong
        err "unable to use function MATCH in the requested context"
      -- sqlite_log(code, msg) writes to the error log and returns NULL
      | "sqlite_log" =>
        if nargs != 2 then wrong
        return .null
      | "unistr" =>
        if nargs != 1 then wrong
        if a0.isNull then return .null
        match unistrBytes (textOf a0) with
        | some b => return .text b
        | none => err "invalid Unicode escape"
      | "unistr_quote" =>
        if nargs != 1 then wrong
        -- quote(), with %#Q for text: control characters through unistr()
        match a0 with
        | .text _ => match Printf.scalar? "printf" [.ofString "%#Q", a0] with
          | some (.ok v) => return v
          | some (.error e) => throw e
          | none => return .ofString (quoteValue a0)
        | .real r => return .ofString ((Printf.quoteReal? r).getD (quoteValue a0))
        | _ => return .ofString (quoteValue a0)
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
        let cs := vs.map fun v => Char.ofNat v.toInt.toNat
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
        let z : Option Int := if nargs == 3 then some vs[2]!.toInt else none
        let y := a1.toInt
        match a0 with
        | .blob b =>
          -- sqlite3_value_blob of an empty blob is a null pointer: no result
          if b.size == 0 then return .null
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
        let rec goRep (s : List UInt8) (k : Nat) : List UInt8 :=
          match k with
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
        -- sqlite3_value_numeric_type: only an INTEGER or REAL (a TEXT after numeric affinity)
        let nv := match a0 with
          | .text t => (numericOfText t false).getD a0
          | v => v
        match nv with
        | .int _ | .real _ => pure ()
        | _ => return .null
        match mathArg nv with
        | none => return .null
        | some r => return .int (if r > 0 then 1 else if r < 0 then -1 else 0)
      | "min" | "max" =>
        if nargs < 2 then wrong
        if vs.any (·.isNull) then return .null
        let coll := (colls.findSome? id).map (·.1) |>.getD .binary
        -- minmaxFunc: min() moves to a later argument on a tie, max() does not
        let better (a b : Value) : Bool :=
          let o := compareValues coll a b
          if name == "min" then o != .gt else o == .gt
        return vs.foldl (fun acc v => if better v acc then v else acc) a0
      | "zeroblob" =>
        if nargs != 1 then wrong
        let n := max 0 a0.toInt
        if n > maxLength then err "string or blob too big" SQLITE_TOOBIG
        return .blob ⟨Array.replicate n.toNat 0⟩
      | "likelihood" | "likely" | "unlikely" => return a0
      | "sqlite_version" => return .ofString "3.54.1"
      -- the options of the ccomp build, which the Clight export is (Sql.PragmaData)
      | "sqlite_compileoption_used" =>
        if nargs != 1 then wrong
        match a0.toText? with
        | some b => return .int (if Pragma.compileOptionUsed b.toList then 1 else 0)
        | none => return .null
      | "sqlite_compileoption_get" =>
        if nargs != 1 then wrong
        match Pragma.compileOptionGet a0.toInt with
        | some o => return .ofString o
        | none => return .null
      | "sqlite_source_id" => return .ofString "2026-10-16 14:45:20 555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76"
      -- random(), randomblob(N): SQLite's PRNG, any value
      | "random" =>
        if nargs != 0 then wrong
        let x ← anyOf fun (x : Int) => -2 ^ 63 ≤ x ∧ x < 2 ^ 63
        return .int x
      | "randomblob" =>
        if nargs != 1 then wrong
        let n := max 1 a0.toInt
        if n > maxLength then err "string or blob too big" SQLITE_TOOBIG
        let b ← anyOf fun (b : ByteArray) => b.size = n.toNat
        return .blob b
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- A window definition with its base window (named in the WINDOW clause) merged in. -/
def resolveWindow (windows : List (Name × Window)) (w : Window) : D Window :=
    do
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- Values of one window function call for each row context, and the sorted order of the rows. -/
def computeWindow (ctxs : Array QEnv) (windows : List (Name × Window)) (call : Expr) :
    D (Array Value × Array Nat) :=
    do
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
        | some f => condHolds c f
        | none => pure true
      let constArg (k : Nat) (dflt : Int) : D Int := do
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
        let frameOf (j : Nat) : D (List Nat) := do
          let fr := frame.getD (if ord.isEmpty then .mk .rows .unboundedPreceding .unboundedFollowing .noOthers
                                else .mk .range .unboundedPreceding .currentRow .noOthers)
          let .mk unit st en excl := fr
          let offset (e : Expr) (start : Bool) : D Value := do
            let v ← evalExpr (ctxs[p[j]!]!) e
            let bad : Bool := match v with
              | .int i => decide (i < 0) | .real r => r < 0.0 | _ => true
            if bad then
              err (if start then "frame starting offset must be a non-negative number" else "frame ending offset must be a non-negative number")
            return v
          let bound (b : FrameBound) (isStart : Bool) : D Int := do
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
          for _ in [0:(hi - lo + 1).toNat] do
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- A join prepared for the loops: the leaves of the chain of inner joins
    with their sources and (for tables) rows in scan order, the nesting order,
    each conjunct with its depth, and where each leaf's columns start. -/
def joinPrepare (q : QEnv) (f : FromItem) (where_ : Option Expr) (aliases : List (Name × Expr)) :
    D JoinPlan := do
  let (leavesL, onConds) := innerChain f
  let leaves := leavesL.toArray
  -- a table-valued function's rows depend on earlier leaves (its arguments)
  let mut leafSrcs : Array (Array Src) := #[]
  let mut leafRows : Array (Option (Array (Array Cur))) := #[]
  for lf in leaves do
    match lf with
    | .tableFn _ n _ «alias» =>
      leafSrcs := leafSrcs.push #[← tableFnSrc n «alias»]
      leafRows := leafRows.push none
    | _ =>
      let (ss, rs) ← evalFrom q lf
      leafSrcs := leafSrcs.push ss
      -- the order the plan scans the leaf in
      leafRows := leafRows.push (some (← permA rs))
  let nL := leaves.size
  -- the order of the loops: any, as the plan picks; FROM's with a
  -- table-valued function (its arguments name earlier leaves)
  let nest ← if leafRows.any (·.isNone) then pure (Array.range nL) else permA (Array.range nL)
  return JoinPlan.make leaves leafSrcs leafRows nest (onConds ++ (where_.map conjuncts).getD []) aliases
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The rows of leaf `k` after the partial row `pre`. -/
def joinRowsAt (q : QEnv) (p : JoinPlan) (k : Nat) (pre : Array Cur) : D (Array (Array Cur)) := do
  match p.leafRows[k]! with
  | some rs => return rs
  | none =>
    match p.leaves[k]! with
    | .tableFn _ n args _ =>
      let qp := { q with env := { q.env with frames := { srcs := p.srcs, cur := pre } :: q.env.frames } }
      let vs ← args.mapM (evalExpr qp)
      let rs ← tableFunction n (vs.zip (← args.mapM (argIsJson qp)))
      return rs.map fun r => #[some r]
    | _ => return #[]
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The conjuncts of depth `d` on a row, in an order the plan picks; the
    first that does not hold rejects the row. -/
def joinCheck (q : QEnv) (p : JoinPlan) (cur : Array Cur) (d : Nat) : D Bool := do
  let qr := { q with env := { q.env with frames := { srcs := p.srcs, cur, aliases := p.aliases } :: q.env.frames, group := none } }
  let order ← perm ((p.byDepth.filter (·.1 == d)).map (·.2))
  for e in order do
    if hasAgg e then err "misuse of aggregate function"
    if !(← condHolds qr e) then return false
  return true
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- A FROM clause joined and filtered by WHERE: its sources and rows. -/
def evalFromWhere (q : QEnv) (f : FromItem) (where_ : Option Expr) (aliases : List (Name × Expr)) :
    D (Array Src × Array (Array Cur)) := do
  let p ← joinPrepare q f where_ aliases
  let (rows, _, failure) ← joinLoops p.leaves.size p.nest (joinRowsAt q p) p.place (joinCheck q p)
    (fun acc cur => pure (acc.push cur, true)) 0 p.empty (#[] : Array (Array Cur))
  if let some e := failure then throw e
  return (p.srcs, rows)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The rows of a named table, view or CTE, with its source description. -/
def namedSource (q : QEnv) (sch : Option Name) (n : Name) («alias» : Name) : D (Src × Array Row) :=
    do
      if sch.isNone then
        if let some (_, cv) := q.ctes.find? (fun (m, _) => nameEq m n) then
          let (cols, rows) ← cteRows q n cv
          return (metaSrc «alias» cols, rows.mapIdx fun i r => ({ rowid := i + 1, vals := r } : Row))
      let db ← getDb
      let tbl ← match sch with
        | none => pure (db.main.findTable n db.attached)
        | some s =>
          if nameEq s "main" || nameEq s "temp" || db.attached.any (nameEq · s) then pure (db.main.findTableDb s n)
          else err s!"no such table: {s}.{n}"
      if let some t := tbl then
        return (tableSrc «alias» t, t.rows)
      if let some v := db.main.findView n then
        let (cols, rows) ← runSelect { q with ctes := [] } v.q
        let cols := if v.cols.isEmpty then cols else
          (cols.zip v.cols.toArray).map fun (c, nm) => { c with name := nm }
        return (metaSrc «alias» cols, rows.mapIdx fun i r => ({ rowid := i + 1, vals := r } : Row))
      if nameEq n "sqlite_schema" || nameEq n "sqlite_master" || nameEq n "sqlite_temp_schema" || nameEq n "sqlite_temp_master" then
        let which : Name := if nameEq n "sqlite_temp_schema" || nameEq n "sqlite_temp_master" then "temp" else (sch.getD "main")
        let rows := schemaRows db which
        let cols : Array ColMeta := #["type", "name", "tbl_name", "rootpage", "sql"].map fun c => ⟨c, none, .binary⟩
        return (metaSrc «alias» cols, rows.mapIdx fun i r => ({ rowid := i + 1, vals := r } : Row))
      if n.toLower.startsWith "pragma_" then
        return (← tableFnSrc n (some «alias»), ← tableFunction n [])
      err s!"no such table: {n}"
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def cteRows (q : QEnv) (n : Name) (cv0 : CteVal) : D (Array ColMeta × Array (Array Value)) :=
    match cv0 with
      | .rows cols rows => return (cols, rows)
      | .defn names sel rec_ => do
        -- the CTE is not visible in its own body unless recursive
        let others := q.ctes.filter fun (m, _) => !nameEq m n
        let rename (cols : Array ColMeta) : D (Array ColMeta) := do
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
        -- the queue, run to empty: a least fixed point (a recursive CTE that
        -- never empties its queue has no outcome)
        let out ← cteLoop q n cols others with_ wrec (recursive.map (·.2)) ob distinctMode limit offset
          queue seen #[] 0
        return (cols, out)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The rows of a recursive CTE `n` from the queue on (setupQueue/the loop of
    multiSelect's recursive case): take the first row (or, with ORDER BY,
    the least), hand it out unless OFFSET skips it or LIMIT is reached, and
    queue the rows the recursive SELECTs give on it (UNION: unless seen). -/
def cteLoop (q : QEnv) (n : Name) (cols : Array ColMeta) (others : List (Name × CteVal))
    (with_ : List Cte) (wrec : Bool) (recursive : List SelectCore) (ob : List OrderTerm)
    (distinctMode : Bool) (limit : Option Int) (offset : Int)
    (queue seen out : Array (Array Value)) (skipped : Int) : D (Array (Array Value)) := do
  if queue.isEmpty then return out
  -- ORDER BY on a recursive CTE makes the queue a priority queue
  let (row, rest') ← if ob.isEmpty then pure (queue[0]!, queue.extract 1 queue.size)
    else do
      let keys ← queue.mapM fun r => ob.toArray.mapM fun (.mk e _ _) =>
        evalExpr { q with env := { q.env with frames := { srcs := #[metaSrc n cols], cur := #[some { rowid := 0, vals := r }] } :: q.env.frames } } e
      let dirs := ob.map fun (.mk _ d nl) => (d, nl)
      let mut best := 0
      for i in List.range queue.size do
        if i > 0 && lexCompare [] dirs keys[i]! keys[best]! == .lt then best := i
      pure (queue[best]!, (queue.extract 0 best) ++ (queue.extract (best + 1) queue.size))
  let mut queue := rest'
  let mut skipped := skipped
  let mut out := out
  if skipped < offset then skipped := skipped + 1
  else
    if let some l := limit then
      if l ≥ 0 && out.size ≥ l.toNat then return out
    out := out.push row
  let ctesRow := (n, CteVal.rows cols #[row]) :: others
  let mut seen := seen
  for c in recursive do
    let (_, rows) ← runSelect { q with ctes := ctesRow } (.mk with_ wrec c [] [] none none)
    for r in rows do
      if distinctMode then
        if seen.any (rowsEq [] r) then continue
        seen := seen.push r
      queue := queue.push r
  cteLoop q n cols others with_ wrec recursive ob distinctMode limit offset queue seen out skipped
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- Evaluate a FROM clause: its sources and joined rows (one `Cur` per source). -/
def evalFrom (q : QEnv) (f0 : FromItem) : D (Array Src × Array (Array Cur)) :=
    match f0 with
      | .table sch n «alias» _ => do
        let (src, rows) ← namedSource q sch n («alias».getD n)
        return (#[src], rows.map fun r => #[some r])
      | .subquery sel «alias» => do
        let (cols, rows) ← runSelect q sel
        return (#[metaSrc («alias».getD "") cols], rows.mapIdx fun i r => #[some ({ rowid := i + 1, vals := r } : Row)])
      | .tableFn sch n args «alias» => do
        let _ := sch
        let vs ← args.mapM (evalExpr q)
        let rows ← tableFunction n (vs.zip (← args.mapM (argIsJson q)))
        return (#[← tableFnSrc n «alias»], rows.map fun r => #[some r])
      | .join l kind natural r on usingCols => do
        let (ls, lrows) ← evalFrom q l
        -- a table-valued function on the right may refer to the left sources: its
        -- rows are computed per left row
        let (rs, rrows0) ← match r with
          | .tableFn _ n _ «alias» => do
            pure (#[← tableFnSrc n «alias»], #[])
          | _ => evalFrom q r
        let rowsFor (lr : Array Cur) : D (Array (Array Cur)) := do
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
        let joinCond (cur : Array Cur) : D Bool := do
          let q' := { q with env := { q.env with frames := { srcs := srcs, cur } :: q.env.frames } }
          for c in common do
            let lv ← evalExpr { q' with env := { q'.env with frames := { srcs := ls, cur := cur.extract 0 nl } :: q.env.frames } } (.col none none c)
            let rv ← evalExpr { q' with env := { q'.env with frames := { srcs := rs, cur := cur.extract nl cur.size } :: q.env.frames } } (.col none none c)
            if truth (compareOp .eq none .binary lv rv) != some true then return false
          match on with
          | some e => condHolds q' e
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The columns of views for `Sql.Pragma`: the interpreter's (deterministic)
    computation on the corresponding state. Debt (PHASES 2.6): it runs the
    view's SELECT with the interpreter's fuel; to be replaced by the static
    column analysis. -/
def viewCols : D Pragma.ViewCols := do
  let c ← get
  let ctx : Ctx := { db := c.db, jsonCache := c.jsonCache }
  return ((Sql.viewCols evalFuel).run.run ctx).1.toOption.getD (fun _ => .error { code := SQLITE_ERROR, msg := "internal: view columns" })

/-- The source of a table-valued function (its columns; `json` and `root` of
    json_each/json_tree are hidden, as are `arg` and `schema` of the
    pragma_<name> tables). -/
def tableFnSrc (n : Name) («alias» : Option Name) : D Src :=
    do
      if Json.tableFns.contains n.toLower then
        modify fun c => { c with db := Pragma.registerModule c.db n }
        let cols : Array ColMeta := Json.eachColumns.toArray.map fun c => ⟨c, none, .binary⟩
        return { metaSrc («alias».getD n) cols with hiddenStar := [8, 9] }
      if let some (cols, nVisible) := Pragma.vtabColumns n then
        modify fun c => { c with db := Pragma.registerModule c.db n }
        let cols : Array ColMeta := cols.toArray.map fun c => ⟨c, none, .binary⟩
        return { metaSrc («alias».getD n) cols with hiddenStar := (List.range cols.size).drop nVisible }
      err s!"no such table: {n}"
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The rows of a table-valued function. -/
def tableFunction (n : Name) (argsJ : List (Value × Bool)) : D (Array Row) :=
    do
      -- pragma_<name>(arg, schema): the eponymous virtual tables of pragma.c
      match Pragma.tableValued (← viewCols) (← getDb) n (argsJ.map (·.1)) with
      | some (.ok (db', rows)) =>
        modify fun c => { c with db := db' }
        return rows.mapIdx fun i vs => { rowid := i + 1, vals := vs }
      | some (.error e) => throw e
      | none =>
      match Json.tableFnST? n.toLower argsJ with
      | some (.ok (_, rows)) =>
        modify fun c => { c with db := Pragma.registerModule c.db n }
        return rows.toArray.mapIdx fun i (vs, j) => { rowid := i + 1, vals := vs.toArray, jsonCols := if j then [1] else [] }
      | some (.error e) => throw e
      | none => err s!"no such table: {n}"

    -- SELECT
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- Expand `*` and `t.*` into column references. -/
def expandCols (srcs : Array Src) (cols : List ResultCol) : D (List ResultCol) :=
    do
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
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- One SELECT core: result metadata and rows, plus the sort keys of
    `orderBy` evaluated per row (for a simple, non-compound select). -/
def runCore (q : QEnv) (core : SelectCore) (orderBy : List OrderTerm) (noRows : Bool := false)
    (lim : Option Nat := none) (off : Nat := 0) (stream : Bool := false) :
    D (Array ColMeta × Array (Array Value × Array Value)) :=
    do
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
        -- `noRows` (LIMIT 0): SQLite jumps past the loop before computing a
        -- row (computeLimitRegisters); only the sources are opened
        let where_ := if noRows then some (.lit (.int 0)) else where_
        -- result-column aliases usable in WHERE (`*` columns resolve as columns anyway)
        let aliases0 := cols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
        -- the column metadata of the result
        let metaOf (srcs : Array Src) (rcols : List ResultCol) : Array ColMeta :=
          let qm : QEnv := { q with env := { q.env with frames := { srcs, cur := Array.replicate srcs.size none } :: q.env.frames, group := none } }
          rcols.toArray.map fun rc =>
            match rc with
            | .expr e _ _ => ⟨resultName q srcs rc, exprAff qm.env e, ((exprColl qm.env e).map (·.1)).getD .binary⟩
            | _ => ⟨"", none, .binary⟩
        -- a SELECT without aggregates, windows or ORDER BY computes and hands
        -- out each row inside the join loop (selectInnerLoop): OFFSET skips a
        -- row before its result columns are computed (after DISTINCT's check
        -- with DISTINCT), LIMIT ends the loop, and an error leaves the rows
        -- already out (a top-level SELECT has printed them)
        let streamable := !noRows && groupBy.isEmpty && having.isNone && orderBy.isEmpty &&
          !(cols.any fun | .expr e _ _ => hasAgg e || hasWindow e | _ => false)
        if let (true, some f) := (streamable, from_) then
          let step (a : StreamAcc) (srcs : Array Src) (cur : Array Cur) : D (StreamAcc × Bool) := do
            if !distinct && a.skipped < off then return ({ a with skipped := a.skipped + 1 }, true)
            let (rcols, colls) ← match a.rcols with
              | some rc => pure rc
              | none => do
                let rcols ← expandCols srcs cols
                pure (rcols, (metaOf srcs rcols).toList.map (·.coll))
            let a := { a with rcols := some (rcols, colls) }
            let exprs := rcols.filterMap fun | .expr e _ _ => some e | _ => none
            let aliases := rcols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
            let qr := { q with env := { q.env with frames := { srcs, cur, aliases } :: q.env.frames, group := none } }
            let vals ← exprs.toArray.mapM (evalExpr qr)
            let a ← if distinct then do
                let k := canonKey colls vals
                if a.seen.contains k then return (a, true)
                let a := { a with seen := a.seen.insert k }
                if a.skipped < off then return ({ a with skipped := a.skipped + 1 }, true)
                pure a
              else pure a
            let a := { a with rows := a.rows.push vals }
            return (a, lim.all (a.rows.size < ·))
          let p ← joinPrepare q f where_ aliases0
          let srcs := p.srcs
          let (a, _, failure) ← joinLoops p.leaves.size p.nest (joinRowsAt q p) p.place (joinCheck q p)
            (step · srcs ·) 0 p.empty ({} : StreamAcc)
          if let some e := failure then throw (if stream then { e with printed := a.rows } else e)
          let rcols ← match a.rcols with
            | some (rc, _) => pure rc
            | none => expandCols srcs cols
          return (metaOf srcs rcols, a.rows.map (·, #[]))
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
            if ← condHolds (withFrame cur aliases) w then kept := kept.push cur
          | _, _ => kept := kept.push cur
        -- the order the plan visits the joined rows: it decides group and
        -- DISTINCT representatives and the input order of aggregates
        kept ← permA kept
        let qm := withFrame (Array.replicate srcs.size none)
        let cmeta : Array ColMeta := rcols.toArray.map fun rc =>
          match rc with
          | .expr e _ _ => ⟨resultName q srcs rc, exprAff qm.env e, ((exprColl qm.env e).map (·.1)).getD .binary⟩
          | _ => ⟨"", none, .binary⟩
        if noRows then return (cmeta, #[])
        -- ORDER BY terms: a result column number, a result «alias», or an expression
        let obExpr (t : OrderTerm) : D Expr := do
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
          -- min()/max() aggregate, else the first row of the group (SQLite 3.54)
          let minmax := exprs.filterMap fun e => match e with
            | .call n d [a] false [] none none =>
              if nameEq n "min" || nameEq n "max" then some (nameEq n "min", d, a) else none
            | _ => none
          for (_, grp) in groups do
            let mut rep : Array Cur := grp[0]?.getD (Array.replicate srcs.size none)
            -- with one min()/max(), minmaxStep tells the accumulator when not to
            -- load the bare columns: they come from each row until the first
            -- non-NULL value, then only from rows that strictly improve it; a
            -- DISTINCT duplicate skips the step itself, so its row is loaded
            if minmax.length == 1 && !grp.isEmpty then
              let (isMin, dist, a) := minmax[0]!
              let coll := ((exprColl qm.env a).map (·.1)).getD .binary
              let mut best : Option Value := none
              let mut seen : Std.HashSet String := {}
              for cur in grp do
                let v ← evalExpr (withFrame cur) a
                if dist && !v.isNull then
                  let k := canonKey [coll] #[v]
                  if seen.contains k then rep := cur; continue
                  seen := seen.insert k
                if v.isNull then
                  if best.isNone then rep := cur
                  continue
                match best with
                | none => best := some v; rep := cur
                | some bv =>
                  let o := compareValues coll v bv
                  if (isMin && o == .lt) || (!isMin && o == .gt) then best := some v; rep := cur
            let qg := { withFrame rep aliases with env := { (withFrame rep aliases).env with group := some grp } }
            if let some h := having then
              if !(← condHolds qg h) then continue
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
        -- the order of a SELECT's rows is the plan's (ORDER BY, applied
        -- after, keeps this order among ties)
        out ← permA out
        out := out.extract off out.size
        if let some l := lim then out := out.extract 0 l
        return (cmeta, out)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def runSelect (q : QEnv) (sel : Select) (cap : Bool := false) (stream : Bool := false) :
    D (Array ColMeta × Array (Array Value)) :=
    do
      let .mk with_ rec_ first rest orderBy limit offset := sel
      let q := { q with ctes := (with_.map fun (.mk n cols _ s) => (n, CteVal.defn cols s rec_)) ++ q.ctes }
      let limitN ← match limit with
        | some l => some <$> limitValue (← evalExpr q l)
        | none => pure none
      -- a scalar subquery or EXISTS has LIMIT 1, or LIMIT (X<>0) for its own
      -- LIMIT X (sqlite3CodeSubselect)
      let limitN := if cap then (if limitN == some 0 then some 0 else some 1) else limitN
      -- LIMIT 0 jumps past the loop before OFFSET is computed (computeLimitRegisters)
      let offsetN ← match offset, limitN with
        | _, some 0 => pure 0
        | some o, _ => limitValue (← evalExpr q o)
        | none, _ => pure 0
      let dirs := orderBy.map fun (.mk _ d nl) => (d, nl)
      let (cols, rows, applied) ← if rest.isEmpty then do
          -- without ORDER BY, LIMIT and OFFSET act inside the loop
          let direct := orderBy.isEmpty
          let limNat : Option Nat := limitN.bind fun l => if l < 0 then none else some l.toNat
          let (cols, rows) ← if direct then runCore q first [] (limitN == some 0) limNat offsetN.toNat stream
            else runCore q first orderBy (limitN == some 0)
          let colls := orderBy.map fun (.mk e _ _) =>
            match e with
            | .collate _ c => (collOfName c).getD .binary
            | .lit (.int i) => (cols[(i - 1).toNat]?.map (·.coll)).getD .binary
            | _ => ((exprColl { q.env with frames := q.env.frames } e).map (·.1)).getD
                ((cols.toList.find? fun c => match e with | .col _ _ n => nameEq c.name n | _ => false).map (·.coll) |>.getD .binary)
          if direct then pure (cols, rows.map (·.1), true) else
          let rows := stableSort (fun a b => lexCompare colls dirs a.2 b.2) rows
          pure (cols, rows.map (·.1), false)
        else if orderBy.isEmpty && rest.all (fun (op, _) => match op with | .unionAll => true | _ => false) then do
          -- UNION ALL without ORDER BY: the SELECTs run one after the other into
          -- the output, sharing LIMIT (multiSelect), so an error in one leaves
          -- the rows of those before it out
          let limNat : Option Nat := limitN.bind fun l => if l < 0 then none else some l.toNat
          let off := offsetN.toNat
          let total := limNat.map (· + off)
          let mut acc : Array (Array Value) := #[]
          let mut metas : List (Array ColMeta) := []
          for core in first :: rest.map (·.2) do
            if total.any (acc.size ≥ ·) then break
            let remaining := total.map (· - acc.size)
            let r ← tryCatch (do
                let (cs, rs) ← runCore q core [] (limitN == some 0) remaining 0 stream
                pure (Except.ok (cs, rs)))
              (fun e => pure (Except.error e))
            match r with
            | .ok (cs, rs) =>
              metas := metas ++ [cs]
              acc := acc ++ rs.map (·.1)
            | .error e =>
              throw (if stream then { e with printed := (acc ++ e.printed).extract off (acc.size + e.printed.size) } else e)
          let cols := metas.head?.getD #[]
          -- multiSelectCollSeq: the leftmost SELECT with a collation for a column
          let colls := (List.range cols.size).map fun i =>
            ((metas.filterMap fun cs => cs[i]?.map (·.coll)).find? (· != .binary)).getD .binary
          let cols := cols.mapIdx fun i c => { c with coll := colls[i]! }
          let rows := acc.extract off acc.size
          let rows := match limNat with | some l => rows.extract 0 l | none => rows
          pure (cols, rows, true)
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
              -- within this SELECT the first of equal rows wins; it replaces an
              -- equal row from an earlier SELECT of the compound
              let mut mine : Std.HashSet String := {}
              for r in rs do
                let k := canonKey colls r
                if mine.contains k then continue
                mine := mine.insert k
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
          if orderBy.isEmpty then pure (cols, acc, false) else
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
          pure (cols, (stableSort (fun a b => lexCompare ocolls dirs a.2 b.2) keyed).map (·.1), false)
      if applied then return (cols, rows)
      let rows := rows.extract offsetN.toNat rows.size
      let rows := match limitN with
        | some l => if l < 0 then rows else rows.extract 0 l.toNat
        | none => rows
      return (cols, rows)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity
end



end Sql.Den
