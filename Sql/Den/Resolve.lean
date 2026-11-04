/-
  The denotation of Sql/Resolve.lean (Phase 2.6): derived by scripts/dev/denize.py, then
  edited where the interpreter has fuel, a choice oracle or a strategy.
-/
import Sql.Den.Select

namespace Sql.Den

open Sql Lean.Order

/-- Check a call's name and argument count against the built-in functions. -/
def checkCall (n : Name) (nargs : Nat) : D Unit := do
  let entries := builtinFunctions.filter fun (m, _, _) => m == n.toLower
  if entries.isEmpty then err s!"no such function: {n}"
  let ok := entries.any fun (_, a, _) => a == nargs || (a < 0 && (nargs : Int) ≥ -a - 2)
  if !ok then err s!"wrong number of arguments to function {n}()"


mutual

def staticExpr (q : QEnv) (e : Expr) : D Unit :=
    do
      match e with
      | .col _ t c =>
        match resolveCol q.env t c with
        | .ok _ => pure ()
        | .error m =>
          if t.isNone && (nameEq c "true" || nameEq c "false") then pure () else err m
      | .dqcol _ | .lit _ | .param .. => pure ()
      | .unop _ a | .collate a _ | .cast a _ | .isNull _ a => staticExpr q a
      | .binop _ a b => staticExpr q a; staticExpr q b
      | .between _ a b c => staticExpr q a; staticExpr q b; staticExpr q c
      | .inList _ a l => staticExpr q a; l.forM (staticExpr q)
      | .inSelect _ a s => staticExpr q a; staticSelect q s
      | .inTable _ a _ _ args => staticExpr q a; args.forM (staticExpr q)
      | .like _ _ a b c => staticExpr q a; staticExpr q b; c.forM (staticExpr q)
      | .case_ b ws el =>
        b.forM (staticExpr q)
        ws.forM fun (x, y) => do staticExpr q x; staticExpr q y
        el.forM (staticExpr q)
      | .exists_ s | .subquery s => staticSelect q s
      | .row l => l.forM (staticExpr q)
      | .call n _ args star ob f _ =>
        checkCall n (if star then 0 else args.length)
        args.forM (staticExpr q)
        ob.forM fun (.mk x _ _) => staticExpr q x
        f.forM (staticExpr q)
      | .raise _ m => m.forM (staticExpr q)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The sources of a FROM clause, metadata only. -/
def staticFrom (q : QEnv) (f0 : FromItem) : D (Array Src) :=
    match f0 with
      | .table sch n «alias» _ => do
        if sch.isNone then
          if let some (_, cv) := q.ctes.find? (fun (m, _) => nameEq m n) then
            let cols ← match cv with
              | .rows cs _ => pure cs
              | .defn names sel _ => do
                let cs ← staticSelectMeta { q with ctes := q.ctes.filter fun (m, _) => !nameEq m n } sel
                pure (if names.isEmpty then cs else (cs.zip names.toArray).map fun (c, nm) => { c with name := nm })
            return #[metaSrc («alias».getD n) cols]
        let db ← getDb
        let tbl ← match sch with
          | none => pure (db.main.findTable n db.attached)
          | some s =>
            if nameEq s "main" || nameEq s "temp" || db.attached.any (nameEq · s) then pure (db.main.findTableDb s n)
            else err s!"no such table: {s}.{n}"
        if let some t := tbl then return #[tableSrc («alias».getD n) t]
        if let some v := db.main.findView n then
          let cs ← staticSelectMeta { q with ctes := [] } v.q
          let cs := if v.cols.isEmpty then cs else (cs.zip v.cols.toArray).map fun (c, nm) => { c with name := nm }
          return #[metaSrc («alias».getD n) cs]
        if nameEq n "sqlite_schema" || nameEq n "sqlite_master" || nameEq n "sqlite_temp_schema" || nameEq n "sqlite_temp_master" then
          return #[metaSrc («alias».getD n) (#["type", "name", "tbl_name", "rootpage", "sql"].map fun c => ⟨c, none, .binary⟩)]
        if n.toLower.startsWith "pragma_" then return #[← tableFnSrc n «alias»]
        match sch with
        | some s => err s!"no such table: {s}.{n}"
        | none => err s!"no such table: {n}"
      | .subquery sel «alias» => do
        staticSelect q sel
        return #[metaSrc («alias».getD "") (← staticSelectMeta q sel)]
      | .tableFn _ n args «alias» => do
        args.forM (staticExpr q)
        return #[← tableFnSrc n «alias»]
      | .join l _ natural r on usingCols => do
        let ls ← staticFrom q l
        -- a table-valued function on the right may refer to the sources on its left
        let rs ← match r with
          | .tableFn _ n args «alias» => do
            args.forM (staticExpr { q with env := { q.env with frames := metaScope ls :: q.env.frames } })
            pure #[← tableFnSrc n «alias»]
          | _ => staticFrom q r
        let srcs := ls ++ rs
        let common : List Name :=
          if natural then
            let lnames := ls.toList.flatMap fun s => s.cols.toList.map (·.1)
            (rs.toList.flatMap fun s => s.cols.toList.map (·.1)).filter fun c => lnames.any (nameEq · c)
          else usingCols
        for c in common do
          if !(ls.any fun s => s.cols.any fun (m, _, _) => nameEq m c) || !(rs.any fun s => s.cols.any fun (m, _, _) => nameEq m c) then
            err s!"cannot join using column {c} - column not present in both tables"
        if let some o := on then
          staticExpr { q with env := { q.env with frames := metaScope srcs :: q.env.frames } } o
        return srcs
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The result columns of a SELECT, metadata only. -/
def staticSelectMeta (q : QEnv) (sel : Select) : D (Array ColMeta) :=
    do
      let .mk with_ rec_ first _ _ _ _ := sel
      let q := { q with ctes := (with_.map fun (.mk n cols _ s) => (n, CteVal.defn cols s rec_)) ++ q.ctes }
      match first with
      | .values rows =>
        return (List.range ((rows.head?.map (·.length)).getD 0)).toArray.map fun i => ⟨s!"column{i + 1}", none, .binary⟩
      | .select _ cols from_ _ _ _ _ =>
        let srcs ← match from_ with
          | some f => staticFrom q f
          | none => pure #[]
        let rcols ← expandCols srcs cols
        let qm := { q with env := { q.env with frames := metaScope srcs :: q.env.frames } }
        return rcols.toArray.filterMap fun rc => match rc with
          | .expr e _ _ => some ⟨resultName q srcs rc, exprAff qm.env e, ((exprColl qm.env e).map (·.1)).getD .binary⟩
          | _ => none
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def staticCore (q : QEnv) (core : SelectCore) (orderBy : List OrderTerm) : D Unit :=
    do
      match core with
      | .values rows => rows.forM fun r => r.forM (staticExpr q)
      | .select _ cols from_ where_ groupBy having _ =>
        let srcs ← match from_ with
          | some f => staticFrom q f
          | none => pure #[]
        let rcols ← expandCols srcs cols
        let exprs := rcols.filterMap fun | .expr e _ _ => some e | _ => none
        let aliases := rcols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
        let qa := { q with env := { q.env with frames := metaScope srcs aliases :: q.env.frames } }
        let q0 := { q with env := { q.env with frames := metaScope srcs :: q.env.frames } }
        exprs.forM (staticExpr q0)
        where_.forM (staticExpr qa)
        groupBy.forM fun g => match g with
          | .lit (.int _) => pure ()
          | _ => staticExpr qa g
        having.forM (staticExpr qa)
        orderBy.forM fun (.mk e _ _) => match e with
          | .lit (.int _) => pure ()
          | .col none none c => if aliases.any (fun (a, _) => nameEq a c) then pure () else staticExpr qa e
          | _ => staticExpr qa e
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def staticSelect (q : QEnv) (sel : Select) : D Unit :=
    do
      let .mk with_ rec_ first rest orderBy limit offset := sel
      let q := { q with ctes := (with_.map fun (.mk n cols _ s) => (n, CteVal.defn cols s rec_)) ++ q.ctes }
      -- the bodies of the CTEs (a recursive one sees itself)
      for (.mk n _ _ s) in with_ do
        let qc := if rec_ then q else { q with ctes := q.ctes.filter fun (m, _) => !nameEq m n }
        let _ := qc
        pure ()
      staticCore q first (if rest.isEmpty then orderBy else [])
      rest.forM fun (_, c) => staticCore q c []
      limit.forM (staticExpr q)
      offset.forM (staticExpr q)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity
end



/-- Prepare-time checks of a statement. -/
def staticStmt (s : Stmt) : D Unit := do
  let q : QEnv := {}
  match s with
  | .select sel => staticSelect q sel
  | .insert _ _ _ tname _ _ src _ ret =>
    match src with
    | .values rows => rows.forM fun r => r.forM (staticExpr q)
    | .select sel => staticSelect q sel
    | .defaults => pure ()
    if !ret.isEmpty then
      if let some t := (← getDb).main.findTable tname (← getDb).attached then
        let srcs := #[tableSrc tname t]
        let rcols ← expandCols srcs ret
        rcols.forM fun rc => match rc with
          | .expr e _ _ => staticExpr { q with env := { frames := [metaScope srcs] } } e
          | _ => pure ()
  | .update _ _ _ tname «alias» sets from_ wh ret _ _ _ =>
    let some t := (← getDb).main.findTable tname (← getDb).attached | pure ()
    let fsrcs ← match from_ with
      | some f => staticFrom q f
      | none => pure #[]
    let srcs := #[tableSrc («alias».getD tname) t] ++ fsrcs
    let qs := { q with env := { frames := [metaScope srcs] } }
    sets.forM fun (_, e) => staticExpr qs e
    wh.forM (staticExpr qs)
    let _ := ret
  | .delete _ _ tname «alias» wh _ _ _ _ =>
    let some t := (← getDb).main.findTable tname (← getDb).attached | pure ()
    let qs := { q with env := { frames := [metaScope #[tableSrc («alias».getD tname) t]] } }
    wh.forM (staticExpr qs)
  | _ => pure ()


end Sql.Den
