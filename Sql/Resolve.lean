/-
  Name resolution at prepare time. SQLite resolves every column reference and
  function call of a statement when it prepares it, before any row is read:
  `select nosuch from t` fails on an empty table, and so does a bad call in a
  subquery that is never evaluated. This pass walks a statement with the
  sources' metadata only (no rows), in SQLite's resolver order (FROM, result
  columns, WHERE, GROUP BY, HAVING, ORDER BY), and raises the first error.
-/
import Sql.Select
import Sql.FuncTable

namespace Sql

/-- Check a call's name and argument count against the built-in functions. -/
def checkCall (n : Name) (nargs : Nat) : M Unit := do
  let entries := builtinFunctions.filter fun (m, _, _) => m == n.toLower
  if entries.isEmpty then err s!"no such function: {n}"
  let ok := entries.any fun (_, a, _) => a == nargs || (a < 0 && (nargs : Int) ≥ -a - 2)
  if !ok then err s!"wrong number of arguments to function {n}()"

/-- A scope of metadata only: sources, every current row the NULL row. -/
def metaScope (srcs : Array Src) (aliases : List (Name × Expr) := []) : Scope :=
  { srcs, cur := Array.replicate srcs.size none, aliases }

mutual

def staticExpr (fuel : Nat) (q : QEnv) (e : Expr) : M Unit :=
  match fuel with
  | 0 => outOfFuel
  | fuel + 1 =>
    do
      match e with
      | .col _ t c =>
        match resolveCol q.env t c with
        | .ok _ => pure ()
        | .error m =>
          if t.isNone && (nameEq c "true" || nameEq c "false") then pure () else err m
      | .dqcol _ | .lit _ | .param .. => pure ()
      | .unop _ a | .collate a _ | .cast a _ | .isNull _ a => staticExpr fuel q a
      | .binop _ a b => staticExpr fuel q a; staticExpr fuel q b
      | .between _ a b c => staticExpr fuel q a; staticExpr fuel q b; staticExpr fuel q c
      | .inList _ a l => staticExpr fuel q a; l.forM (staticExpr fuel q)
      | .inSelect _ a s => staticExpr fuel q a; staticSelect fuel q s
      | .inTable _ a _ _ args => staticExpr fuel q a; args.forM (staticExpr fuel q)
      | .like _ _ a b c => staticExpr fuel q a; staticExpr fuel q b; c.forM (staticExpr fuel q)
      | .case_ b ws el =>
        b.forM (staticExpr fuel q)
        ws.forM fun (x, y) => do staticExpr fuel q x; staticExpr fuel q y
        el.forM (staticExpr fuel q)
      | .exists_ s | .subquery s => staticSelect fuel q s
      | .row l => l.forM (staticExpr fuel q)
      | .call n _ args star ob f _ =>
        checkCall n (if star then 0 else args.length)
        args.forM (staticExpr fuel q)
        ob.forM fun (.mk x _ _) => staticExpr fuel q x
        f.forM (staticExpr fuel q)
      | .raise _ m => m.forM (staticExpr fuel q)

/-- The sources of a FROM clause, metadata only. -/
def staticFrom (fuel : Nat) (q : QEnv) (f0 : FromItem) : M (Array Src) :=
  match fuel with
  | 0 => outOfFuel
  | fuel + 1 =>
    match f0 with
      | .table sch n alias _ => do
        if sch.isNone then
          if let some (_, cv) := q.ctes.find? (fun (m, _) => nameEq m n) then
            let cols ← match cv with
              | .rows cs _ => pure cs
              | .defn names sel _ => do
                let cs ← staticSelectMeta fuel { q with ctes := q.ctes.filter fun (m, _) => !nameEq m n } sel
                pure (if names.isEmpty then cs else (cs.zip names.toArray).map fun (c, nm) => { c with name := nm })
            return #[metaSrc (alias.getD n) cols]
        let db ← getDb
        let tbl ← match sch with
          | none => pure (db.main.findTable n db.attached)
          | some s =>
            if nameEq s "main" || nameEq s "temp" || db.attached.any (nameEq · s) then pure (db.main.findTableDb s n)
            else err s!"no such table: {s}.{n}"
        if let some t := tbl then return #[tableSrc (alias.getD n) t]
        if let some v := db.main.findView n then
          let cs ← staticSelectMeta fuel { q with ctes := [] } v.q
          let cs := if v.cols.isEmpty then cs else (cs.zip v.cols.toArray).map fun (c, nm) => { c with name := nm }
          return #[metaSrc (alias.getD n) cs]
        if nameEq n "sqlite_schema" || nameEq n "sqlite_master" || nameEq n "sqlite_temp_schema" || nameEq n "sqlite_temp_master" then
          return #[metaSrc (alias.getD n) (#["type", "name", "tbl_name", "rootpage", "sql"].map fun c => ⟨c, none, .binary⟩)]
        if n.toLower.startsWith "pragma_" then return #[← tableFnSrc fuel n alias]
        match sch with
        | some s => err s!"no such table: {s}.{n}"
        | none => err s!"no such table: {n}"
      | .subquery sel alias => do
        staticSelect fuel q sel
        return #[metaSrc (alias.getD "") (← staticSelectMeta fuel q sel)]
      | .tableFn _ n args alias => do
        args.forM (staticExpr fuel q)
        return #[← tableFnSrc fuel n alias]
      | .join l _ natural r on usingCols => do
        let ls ← staticFrom fuel q l
        -- a table-valued function on the right may refer to the sources on its left
        let rs ← match r with
          | .tableFn _ n args alias => do
            args.forM (staticExpr fuel { q with env := { q.env with frames := metaScope ls :: q.env.frames } })
            pure #[← tableFnSrc fuel n alias]
          | _ => staticFrom fuel q r
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
          staticExpr fuel { q with env := { q.env with frames := metaScope srcs :: q.env.frames } } o
        return srcs

/-- The result columns of a SELECT, metadata only. -/
def staticSelectMeta (fuel : Nat) (q : QEnv) (sel : Select) : M (Array ColMeta) :=
  match fuel with
  | 0 => outOfFuel
  | fuel + 1 =>
    do
      let .mk with_ rec_ first _ _ _ _ := sel
      let q := { q with ctes := (with_.map fun (.mk n cols _ s) => (n, CteVal.defn cols s rec_)) ++ q.ctes }
      match first with
      | .values rows =>
        return (List.range ((rows.head?.map (·.length)).getD 0)).toArray.map fun i => ⟨s!"column{i + 1}", none, .binary⟩
      | .select _ cols from_ _ _ _ _ =>
        let srcs ← match from_ with
          | some f => staticFrom fuel q f
          | none => pure #[]
        let rcols ← expandCols fuel srcs cols
        let qm := { q with env := { q.env with frames := metaScope srcs :: q.env.frames } }
        return rcols.toArray.filterMap fun rc => match rc with
          | .expr e _ _ => some ⟨resultName q srcs rc, exprAff qm.env e, ((exprColl qm.env e).map (·.1)).getD .binary⟩
          | _ => none

def staticCore (fuel : Nat) (q : QEnv) (core : SelectCore) (orderBy : List OrderTerm) : M Unit :=
  match fuel with
  | 0 => outOfFuel
  | fuel + 1 =>
    do
      match core with
      | .values rows => rows.forM fun r => r.forM (staticExpr fuel q)
      | .select _ cols from_ where_ groupBy having _ =>
        let srcs ← match from_ with
          | some f => staticFrom fuel q f
          | none => pure #[]
        let rcols ← expandCols fuel srcs cols
        let exprs := rcols.filterMap fun | .expr e _ _ => some e | _ => none
        let aliases := rcols.filterMap fun | .expr e (some a) _ => some (a, e) | _ => none
        let qa := { q with env := { q.env with frames := metaScope srcs aliases :: q.env.frames } }
        let q0 := { q with env := { q.env with frames := metaScope srcs :: q.env.frames } }
        exprs.forM (staticExpr fuel q0)
        where_.forM (staticExpr fuel qa)
        groupBy.forM fun g => match g with
          | .lit (.int _) => pure ()
          | _ => staticExpr fuel qa g
        having.forM (staticExpr fuel qa)
        orderBy.forM fun (.mk e _ _) => match e with
          | .lit (.int _) => pure ()
          | .col none none c => if aliases.any (fun (a, _) => nameEq a c) then pure () else staticExpr fuel qa e
          | _ => staticExpr fuel qa e

def staticSelect (fuel : Nat) (q : QEnv) (sel : Select) : M Unit :=
  match fuel with
  | 0 => outOfFuel
  | fuel + 1 =>
    do
      let .mk with_ rec_ first rest orderBy limit offset := sel
      let q := { q with ctes := (with_.map fun (.mk n cols _ s) => (n, CteVal.defn cols s rec_)) ++ q.ctes }
      -- the bodies of the CTEs (a recursive one sees itself)
      for (.mk n _ _ s) in with_ do
        let qc := if rec_ then q else { q with ctes := q.ctes.filter fun (m, _) => !nameEq m n }
        let _ := qc
        pure ()
      staticCore fuel q first (if rest.isEmpty then orderBy else [])
      rest.forM fun (_, c) => staticCore fuel q c []
      limit.forM (staticExpr fuel q)
      offset.forM (staticExpr fuel q)
end

/-- Prepare-time checks of a statement. -/
def staticStmt (fuel : Nat) (s : Stmt) : M Unit := do
  let q : QEnv := {}
  match s with
  | .select sel => staticSelect fuel q sel
  | .insert _ _ _ tname _ _ src _ ret =>
    match src with
    | .values rows => rows.forM fun r => r.forM (staticExpr fuel q)
    | .select sel => staticSelect fuel q sel
    | .defaults => pure ()
    if !ret.isEmpty then
      if let some t := (← getDb).main.findTable tname (← getDb).attached then
        let srcs := #[tableSrc tname t]
        let rcols ← expandCols fuel srcs ret
        rcols.forM fun rc => match rc with
          | .expr e _ _ => staticExpr fuel { q with env := { frames := [metaScope srcs] } } e
          | _ => pure ()
  | .update _ _ _ tname alias sets from_ wh ret _ _ _ =>
    let some t := (← getDb).main.findTable tname (← getDb).attached | pure ()
    let fsrcs ← match from_ with
      | some f => staticFrom fuel q f
      | none => pure #[]
    let srcs := #[tableSrc (alias.getD tname) t] ++ fsrcs
    let qs := { q with env := { frames := [metaScope srcs] } }
    sets.forM fun (_, e) => staticExpr fuel qs e
    wh.forM (staticExpr fuel qs)
    let _ := ret
  | .delete _ _ tname alias wh _ _ _ _ =>
    let some t := (← getDb).main.findTable tname (← getDb).attached | pure ()
    let qs := { q with env := { frames := [metaScope #[tableSrc (alias.getD tname) t]] } }
    wh.forM (staticExpr fuel qs)
  | _ => pure ()

end Sql
