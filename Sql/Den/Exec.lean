/-
  The denotation of Sql/Exec.lean (Phase 2.6): derived by scripts/dev/denize.py, then
  edited where the interpreter has fuel, a choice oracle or a strategy.
-/
import Sql.Den.Resolve

namespace Sql.Den

open Sql Lean.Order

def mkTable (name : Name) (cols : List ColumnDef) (cons : List (Option Name × TableConstraint))
    (withoutRowid strict : Bool) (sql : String) : D Table := do
  let mut cs : Array Column := #[]
  for cd in cols do
    if cs.any (nameEq ·.name cd.name) then err s!"duplicate column name: {cd.name}"
    if strict && !(strictTypes.contains cd.type.trimAscii.toString.toUpper) then
      if cd.type.trimAscii.toString.isEmpty then err s!"missing datatype for {name}.{cd.name}"
      err s!"unknown datatype for {name}.{cd.name}: \"{cd.type}\""
    let ty := stripGeneratedAlways cd.type.trimAscii.toString
    let ty := if strictTypes.contains ty.toUpper then ty.toUpper else P.unquote ty
    let mut c : Column := { name := cd.name, type := ty, aff := affinityOfType ty }
    for (_, k) in cd.constraints do
      match k with
      | .notNull oc => c := { c with notNull := true, notNullConflict := oc }
      | .default_ e _ => c := { c with dflt := some e }
      | .collate n =>
        match collOfName n with
        | some co => c := { c with coll := co }
        | none => err s!"no such collation sequence: {n}"
      | .generated e st => c := { c with generated := some (e, st) }
      | _ => pure ()
    cs := cs.push c
  let colIdx (n : Name) : D Nat := do
    match cs.toList.findIdx? (nameEq ·.name n) with
    | some i => return i
    | none => err s!"no such column: {n}"
  let mut t : Table := { name, cols := cs, withoutRowid, strict, sql }
  -- a constraint's index with the columns and collations of an earlier one is
  -- that one (sqlite3CreateIndex): its ON CONFLICT is the one given, and a
  -- PRIMARY KEY makes it the primary key index
  let addKey (keys : List UniqueKey) (k : UniqueKey) : D (List UniqueKey) := do
    let same (o : UniqueKey) := o.cols.length == k.cols.length &&
      (o.cols.zip k.cols).all fun ((i, c), (j, d)) => i == j && c == d
    match keys.findIdx? same with
    | none => return keys ++ [k]
    | some n =>
      let o := keys[n]!
      if o.onConflict.isSome && k.onConflict.isSome && o.onConflict != k.onConflict then
        err "conflicting ON CONFLICT clauses specified"
      return keys.set n { o with onConflict := o.onConflict.orElse fun _ => k.onConflict, isPk := o.isPk || k.isPk }
  let mut pkSet := false
  -- column constraints
  for h : i in [0:cols.length] do
    let cd := cols[i]
    for (cname, k) in cd.constraints do
      match k with
      | .primaryKey dir oc ai =>
        if pkSet then err s!"table \"{name}\" has more than one primary key"
        pkSet := true
        t := { t with pk := [i] }
        if isIntegerType cd.type && dir != some .desc && !withoutRowid then
          t := { t with rowidCol := some i, autoinc := ai, rowidConflict := oc }
        else
          if ai then err "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
          t := { t with uniques := ← addKey t.uniques { cols := [(i, cs[i]!.coll)], onConflict := oc, isPk := true } }
      | .unique oc => t := { t with uniques := ← addKey t.uniques { cols := [(i, cs[i]!.coll)], onConflict := oc } }
      | .check e txt => t := { t with checks := t.checks ++ [(cname.orElse (fun _ => some txt), e)] }
      | .references p pc acts =>
        let del := (acts.find? (·.startsWith "DELETE ")).map (·.drop 7 |>.toString) |>.getD "NO ACTION"
        let upd := (acts.find? (·.startsWith "UPDATE ")).map (·.drop 7 |>.toString) |>.getD "NO ACTION"
        t := { t with fks := t.fks ++ [{ cols := [i], parent := p, parentCols := pc, onDelete := del, onUpdate := upd }] }
      | _ => pure ()
  -- table constraints
  for (cname, k) in cons do
    match k with
    | .primaryKey kcols oc ai =>
      if pkSet then err s!"table \"{name}\" has more than one primary key"
      pkSet := true
      let idxs ← kcols.mapM fun (n, _, _) => colIdx n
      t := { t with pk := idxs }
      if idxs.length == 1 && isIntegerType cs[idxs[0]!]!.type && !withoutRowid &&
         (kcols[0]!.2.2 != .desc) then
        t := { t with rowidCol := some idxs[0]!, autoinc := ai, rowidConflict := oc }
      else
        let kc ← kcols.mapM (fun (n, c, _) => do
          let i ← colIdx n; pure (i, (c.bind collOfName).getD cs[i]!.coll))
        t := { t with uniques := ← addKey t.uniques { cols := kc, onConflict := oc, isPk := true } }
    | .unique kcols oc =>
      let kc ← kcols.mapM (fun (n, c, _) => do
          let i ← colIdx n; pure (i, (c.bind collOfName).getD cs[i]!.coll))
      t := { t with uniques := ← addKey t.uniques { cols := kc, onConflict := oc } }
    | .check e txt => t := { t with checks := t.checks ++ [(cname.orElse (fun _ => some txt), e)] }
    | .foreignKey fc p pc acts =>
      let del := (acts.find? (·.startsWith "DELETE ")).map (·.drop 7 |>.toString) |>.getD "NO ACTION"
      let upd := (acts.find? (·.startsWith "UPDATE ")).map (·.drop 7 |>.toString) |>.getD "NO ACTION"
      t := { t with fks := t.fks ++ [{ cols := ← fc.mapM colIdx, parent := p, parentCols := pc, onDelete := del, onUpdate := upd }] }
  if withoutRowid && !pkSet then err s!"PRIMARY KEY missing on table {name}"
  -- the columns of a PRIMARY KEY of a WITHOUT ROWID table are NOT NULL
  if withoutRowid then
    t := { t with cols := t.cols.mapIdx fun i c => if t.pk.contains i then { c with notNull := true } else c }
  return t


def setDb (db : Db) : D Unit := modify fun c => { c with db := db }


/-- Count `n` changed rows: always in total_changes(); in changes() only for a
    top-level statement (not inside a trigger program). -/
def countChanges (q : QEnv) (n : Int) : D Unit :=
  let inTrigger := q.env.newRow.isSome || q.env.oldRow.isSome
  modify fun c => { c with db := { c.db with
    changes := if inTrigger then c.db.changes else n,
    totalChanges := c.db.totalChanges + n } }


def modifyMain (f : Schema → Schema) : D Unit :=
  modify fun c => { c with db := { c.db with main := f c.db.main } }


/-- The value stored in a column: affinity, and STRICT type checks. -/
def storeValue (t : Table) (i : Nat) (v : Value) : D Value := do
  let c := t.cols[i]!
  let v' := applyAffinity c.aff v
  if t.strict then
    let ty := c.type.trimAscii.toString.toUpper
    let ok := match ty, v' with
      | _, .null => true
      | "ANY", _ => true
      | "INT", .int _ | "INTEGER", .int _ => true
      | "REAL", .real _ => true
      | "REAL", .int _ => true
      | "TEXT", .text _ => true
      | "BLOB", .blob _ => true
      | _, _ => false
    if !ok then
      let tn := match v' with
        | .int _ => "INTEGER" | .real _ => "REAL" | .text _ => "TEXT" | .blob _ => "BLOB" | .null => "NULL"
      err s!"cannot store {tn} value in {ty} column {t.name}.{c.name}" SQLITE_CONSTRAINT_DATATYPE
    -- a REAL column of a STRICT table stores an integer as a REAL
    if ty == "REAL" then
      if let .int i := v' then return .real (intToReal i)
  return v'


/-- Compute generated columns of a row. -/
def withGenerated (t : Table) (r : Row) : D Row := do
  let mut r := r
  for h : i in [0:t.cols.size] do
    if let some (e, _) := t.cols[i].generated then
      let v ← evalExpr (qOfRow t r) e
      r := { r with vals := r.vals.set! i (applyAffinity t.cols[i].aff v) }
  return r


/-- A constraint error under resolution `r` (other than IGNORE and REPLACE,
    which the caller handles): FAIL keeps the statement's earlier changes,
    ROLLBACK rolls the transaction back. -/
def throwConflict {α} (r : ConflictRes) (msg : String) (code : Nat) : D α :=
  throw { code, msg, keep := r == .fail, rollback := r == .rollback }


/-- NOT NULL and CHECK constraints; false: the row is ignored (a CHECK
    failing under OR IGNORE). REPLACE is ABORT for CHECK. -/
def checkRow (t : Table) (r : Row) (ovr : Option ConflictRes := none) : D Bool := do
  for h : i in [0:t.cols.size] do
    let c := t.cols[i]
    if c.notNull && (r.vals[i]?.getD .null).isNull then
      err s!"NOT NULL constraint failed: {t.name}.{c.name}" SQLITE_CONSTRAINT_NOTNULL
  for (nm, e) in (if Pragma.flag (← getDb) "ignore_check_constraints" then [] else t.checks) do
    -- sqlite3ExprIfTrue(check, ok, SQLITE_JUMPIFNULL): true or NULL passes
    if !(← condJump (qOfRow t r) e true true) then
      match ovr.getD .abort with
      | .ignore => return false
      | .replace | .abort => err s!"CHECK constraint failed: {nm.getD ""}" SQLITE_CONSTRAINT_CHECK
      | res => throwConflict res s!"CHECK constraint failed: {nm.getD ""}" SQLITE_CONSTRAINT_CHECK
  return true


def currentTable (n : Name) : D Table := do
  match (← getDb).main.findTable n (← getDb).attached with
  | some t => return t
  | none =>
    if (← getDb).main.findView n |>.isSome then err s!"cannot modify {n} because it is a view"
    err s!"no such table: {n}"


/-- The `sqlite_stat1` rows of one table (`analyzeOneTable`), as (idx, stat):
    for each index in `pTab->pIndex` order (only `only` if given), "nRow
    avg1 … avgN" with avgᵢ the rows per distinct prefix of i+1 key columns
    (rounded up; 1 when it would be 2 with nRow·10 ≤ distinct·11), NULLs
    equal; an empty index has no row unless partial. Then, when the table
    has no non-partial index, (NULL, row count) if it has rows. -/
def analyzeRows (t : Table) (only : Option Name) : D (List (Option String × Value)) := do
  let db ← getDb
  let mut out : List (Option String × Value) := []
  let mut needTableCnt := true
  for ix in (Pragma.indexList db t).toList do
    if let some o := only then
      if !nameEq ix.name o then continue
    if !ix.partial_ then needTableCnt := false
    let decl := db.main.indexes.find? (nameEq ·.name ix.name)
    -- the index's entries: the rows its WHERE admits, keyed by its key columns
    let mut keys : Array (Array Value) := #[]
    for r in t.rows do
      let q := qOfRow t r
      if let some w := decl.bind (·.where_) then
        if !(← condHolds q w) then continue
      let mut k := #[]
      for h : j in [0:ix.keys.size] do
        let c := ix.keys[j]
        let v ← if c.cid == -1 then pure (Value.int r.rowid)
          else if c.cid ≥ 0 then pure (r.vals[c.cid.toNat]?.getD .null)
          else match decl.bind (·.cols[j]?) with
            | some (.mk e _ _) => evalExpr q (match e with | .collate x _ => x | x => x)
            | none => pure .null
        k := k.push v
      keys := keys.push k
    let nRow := keys.size
    if nRow == 0 && !ix.partial_ then continue
    let colls := ix.keys.toList.map fun c => (collOfName c.coll).getD .binary
    let mut stat := toString nRow
    for i in [0:ix.keys.size] do
      let distinct := (keys.foldl (fun (st : Std.HashSet String) k => st.insert (canonKey colls (k.extract 0 (i + 1)))) {}).size
      let nD := max distinct 1
      let v := (nRow + nD - 1) / nD
      let v := if v == 2 && nRow * 10 ≤ nD * 11 then 1 else v
      stat := stat ++ s!" {v}"
    -- a WITHOUT ROWID table's primary key is listed under the table's name
    let name := if t.withoutRowid && ix.origin == "pk" then t.name else ix.name
    out := out ++ [(some name, .ofString stat)]
  if only.isNone && needTableCnt && !t.rows.isEmpty then
    -- the record has TEXT affinity ("BBB"): the count is stored as text
    out := out ++ [(none, .ofString (toString t.rows.size))]
  return out


/-- Insert one row (values for every column, rowid value or none), applying
    conflict resolution. Returns the inserted row, or none if ignored. -/
def insertRow (tname : Name) (vals : Array Value) (rowidV : Option Value) (ovr : Option ConflictRes) :
    D (Option Row) := do
  let t ← currentTable tname
  let db ← getDb
  let mut vals := vals
  for h : i in [0:t.cols.size] do
    vals := vals.set! i (← storeValue t i (vals[i]?.getD .null))
  -- rowid
  -- OP_NewRowid: one more than the largest rowid (which may be negative); 1 for an empty table
  let maxRowid : Int := match t.rows.toList.map (·.rowid) with
    | [] => 0
    | r :: rs => rs.foldl max r
  let rid ← match rowidV with
    | some v =>
      let v' := applyAffinity .integer v
      match v' with
      | .int i => pure i
      | .null => pure (maxRowid + 1)
      | _ => err "datatype mismatch" SQLITE_MISMATCH
    | none => pure (maxRowid + 1)
  let seqOf (s : Schema) : Int :=
    match s.findTable "sqlite_sequence" with
    | some st => (st.rows.findSome? fun r => match r.vals[0]?, r.vals[1]? with
        | some (Value.text n), some v => if nameEq (String.fromUTF8! n) t.name then some v.numeric.toInt else none
        | _, _ => none).getD 0
    | none => 0
  let auto := rowidV.all (·.isNull)
  let rid := if t.autoinc && auto then max (maxRowid + 1) (seqOf db.main + 1) else rid
  -- the next rowid does not fit: AUTOINCREMENT fails; otherwise SQLite picks a
  -- random unused rowid (an unspecified choice; the executable takes one)
  let rid ← if auto && rid > maxI64 then do
      if t.autoinc then err "database or disk is full" 13
      -- OP_NewRowid: up to 100 random candidates in [1, 2^62] (any); none
      -- unused is SQLITE_FULL
      let cands ← anyOf fun (l : List Int) => l.length = 100 ∧ ∀ c ∈ l, 1 ≤ c ∧ c ≤ 2 ^ 62
      match cands.find? (fun cand => !(t.rows.any (·.rowid == cand))) with
      | some cand => pure cand
      | none => err "database or disk is full" 13
    else pure rid
  if let some ci := t.rowidCol then vals := vals.set! ci (.int rid)
  let mut row ← withGenerated t { rowid := rid, vals }
  -- NOT NULL with conflict resolution
  for h : i in [0:t.cols.size] do
    let c := t.cols[i]
    if c.notNull && (row.vals[i]?.getD .null).isNull then
      match resolveConflict ovr c.notNullConflict with
      | .ignore => return none
      | .replace =>
        match c.dflt with
        | some d => row := { row with vals := row.vals.set! i (← storeValue t i (← evalExpr {} d)) }
        | none => err s!"NOT NULL constraint failed: {t.name}.{c.name}" SQLITE_CONSTRAINT_NOTNULL
      | res => throwConflict res s!"NOT NULL constraint failed: {t.name}.{c.name}" SQLITE_CONSTRAINT_NOTNULL
  if !(← checkRow t row ovr) then return none
  -- uniqueness: the rowid, then the unique keys
  let mut rows := t.rows
  if !t.withoutRowid then
    if rows.any (·.rowid == rid) then
      match resolveConflict ovr t.rowidConflict with
      | .ignore => return none
      | .replace => rows := rows.filter (·.rowid != rid)
      | res =>
        let cname := match t.rowidCol with | some ci => t.cols[ci]!.name | none => "rowid"
        throwConflict res s!"UNIQUE constraint failed: {t.name}.{cname}" SQLITE_CONSTRAINT_PRIMARYKEY
  for (k, _) in allUniques db t do
    let key := keyOf row k
    if rows.any (fun r => keyEq k (keyOf r k) key) then
      match resolveConflict ovr k.onConflict with
      | .ignore => return none
      | .replace => rows := rows.filter (fun r => !keyEq k (keyOf r k) key)
      | res => throwConflict res (uniqueMsg t k) (if k.isPk then SQLITE_CONSTRAINT_PRIMARYKEY else SQLITE_CONSTRAINT_UNIQUE)
  let t' := { t with rows := sortRows t (rows.push row) }
  modifyMain fun s => s.setTable t'
  if t.autoinc then
    modifyMain fun s =>
      match s.findTable "sqlite_sequence" with
      | none => s
      | some st =>
        let cur := seqOf s
        let mine (r : Row) : Bool := match r.vals[0]? with
          | some (Value.text n) => nameEq (String.fromUTF8! n) t.name | _ => false
        let rows := if st.rows.any mine then
            st.rows.map fun r => if mine r then { r with vals := r.vals.set! 1 (.int (max cur rid)) } else r
          else st.rows.push { rowid := (st.rows.foldl (fun m r => max m r.rowid) 0) + 1, vals := #[.ofString t.name, .int (max cur rid)] }
        s.setTable { st with rows }
  return some row


def resultRows (q : QEnv) (t : Table) («alias» : Name) (rows : Array Row) (ret : List ResultCol) :
    D (Array (Array Value)) := do
  if ret.isEmpty then return #[]
  let src := tableSrc «alias» t
  let cols ← expandCols #[src] ret
  rows.mapM fun r => do
    let q' := { q with env := { q.env with frames := { srcs := #[src], cur := #[some r] } :: q.env.frames } }
    cols.toArray.filterMapM fun c => match c with
      | .expr e _ _ => some <$> evalExpr q' e
      | _ => pure none


mutual

/-- Execute a statement; returns its output rows. -/
def execStmt (q : QEnv) (s : Stmt) : D (Array (Array Value)) :=
    do
      match s with
      | .select sel =>
        let (_, rows) ← runSelect q sel (stream := true)
        return rows
      | .explain _ _ => err "EXPLAIN is not modelled"
      | .createTable temp ine sch name cols cons wr strict asSel sql tailStart =>
        let temp := temp || sch.any (nameEq · "temp")
        let db ← getDb
        let att : Option Name := sch.bind fun s => if db.attached.any (nameEq · s) then some s else none
        if let some s := sch then
          if !(nameEq s "main" || nameEq s "temp" || att.isSome) then err s!"unknown database {s}"
        let errAt {α} (m : String) (t : Nat) : D α := throw { code := SQLITE_ERROR, msg := m, tail := some t }
        if objExists db name temp att then
          if ine then return #[]
          if (db.main.findTable name).isSome || (db.main.findView name).isSome then errAt s!"table {name} already exists" tailStart
          errAt s!"there is already an index named {name}" tailStart
        -- errors in a column definition stop prepare after that definition
        let mut seen : List Name := []
        for cd in cols do
          if seen.any (nameEq · cd.name) then errAt s!"duplicate column name: {cd.name}" cd.tailAt
          seen := cd.name :: seen
        if name.toLower.startsWith "sqlite_" then err s!"object name reserved for internal use: {name}"
        let t ← match asSel with
          | some sel =>
            let (cmeta, rows) ← runSelect q sel
            let cds := cmeta.toList.map fun c => ({ name := c.name, type := match c.aff with
              | some .integer => "INT" | some .real => "REAL" | some .text => "TEXT" | some .numeric => "NUM" | _ => "", constraints := [] } : ColumnDef)
            let t ← mkTable name cds [] false false ""
            let sqlText := "CREATE TABLE " ++ name ++ "(" ++ ",".intercalate (cds.map fun c => c.name ++ (if c.type.isEmpty then "" else " " ++ c.type)) ++ ")"
            pure { t with sql := sqlText, rows := rows.mapIdx fun i r => ({ rowid := i + 1, vals := r } : Row) }
          | none => mkTable name cols cons wr strict sql
        let t := { t with temp, attachedTo := att }
        -- automatic indexes for UNIQUE and non-rowid PRIMARY KEY constraints
        let nAuto := t.uniques.length
        modifyMain fun s => { s with objs := s.objs.push (.table t) ++
          ((List.range nAuto).toArray.map fun i => .index
            { name := s!"sqlite_autoindex_{name}_{i + 1}", table := name, cols := [], unique := false,
              where_ := none, sql := none }) }
        if t.autoinc && ((← getDb).main.findTable "sqlite_sequence").isNone then
          let st ← mkTable "sqlite_sequence" [{ name := "name", type := "", constraints := [] },
            { name := "seq", type := "", constraints := [] }] [] false false "CREATE TABLE sqlite_sequence(name,seq)"
          modifyMain fun s => { s with objs := s.objs.push (.table st) }
        return #[]
      | .createIndex unique ine _ name tname cols w sql =>
        let db ← getDb
        if objExists db name then
          if ine then return #[]
          err s!"index {name} already exists"
        let some t := db.main.findTable tname | err s!"no such table: main.{tname}"
        for (.mk e _ _) in cols do
          let _ ← t.rows.mapM fun r => evalExpr (qOfRow t r) e
        let ix : Index := { name, table := tname, cols, unique, where_ := w, sql := some sql }
        modifyMain fun s => { s with objs := s.objs.push (.index ix) }
        if unique then
          -- existing rows must already be unique
          for (k, _) in allUniques (← getDb) t do
            let keys := t.rows.map (keyOf · k)
            for h : i in [0:keys.size] do
              for j in [0:i] do
                if keyEq k keys[i] keys[j]! then err (uniqueMsg t k) SQLITE_CONSTRAINT_UNIQUE
        return #[]
      | .createView temp ine _ name cols sel sql =>
        let db ← getDb
        if objExists db name temp then
          if ine then return #[]
          err s!"view {name} already exists"
        let _ ← runSelect q sel
        modifyMain fun s => { s with objs := s.objs.push (.view { name, cols, q := sel, sql, temp }) }
        return #[]
      | .createTrigger temp ine _ name time ev tname _ w body sql tailBegin =>
        let db ← getDb
        let errAt {α} (m : String) : D α := throw { code := SQLITE_ERROR, msg := m, tail := some tailBegin }
        if objExists db name then
          if ine then return #[]
          errAt s!"trigger {name} already exists"
        if (db.main.findTable tname).isNone && (db.main.findView tname).isNone then
          errAt s!"no such table: main.{tname}"
        modifyMain fun s => { s with objs := s.objs.push (.trigger { name, table := tname, time, event := ev, when_ := w, body, sql, temp }) }
        return #[]
      | .drop kind ie _ name =>
        let db ← getDb
        let hit := db.main.objs.toList.find? fun o =>
          nameEq (Schema.objName o) name && match o, kind with
            | .table _, "table" | .index _, "index" | .view _, "view" | .trigger _, "trigger" => true
            | _, _ => false
        match hit with
        | none => if ie then return #[] else err s!"no such {kind}: {name}"
        | some _ =>
          modifyMain fun s => { s with objs := s.objs.filter fun o =>
            !(nameEq (Schema.objName o) name) &&
            -- dropping a table drops its indexes and triggers
            !(kind == "table" && match o with
              | .index ix => nameEq ix.table name
              | .trigger tr => nameEq tr.table name
              | _ => false) }
          return #[]
      | .insert _ orC _ tname _ cols src upserts ret =>
        if ← viewWithTriggers tname then
          return ← insertView q tname cols src
        let t ← currentTable tname
        let oc := orC.getD .abort
        let colIdx ← if cols.isEmpty then pure (List.range t.cols.size)
          else cols.mapM fun c => do
            match t.cols.toList.findIdx? (nameEq ·.name c) with
            | some i => pure i
            | none => if isRowidName c && !t.withoutRowid then pure t.cols.size else err s!"table {t.name} has no column named {c}"
        let ncols := if cols.isEmpty then (t.cols.toList.filter fun c => c.generated.isNone).length else cols.length
        -- the rows to insert, each computed when the loop reaches it (a VALUES
        -- list is a co-routine: a row is evaluated, then inserted, then the
        -- next; its arity is checked at prepare)
        let srcRows : Array (D (Array Value)) ← match src with
          | .values rows => do
              -- the parser's check (sqlite3MultiValues) comes first
              if let r0 :: _ := rows then
                if rows.any (·.length != r0.length) then err "all VALUES must have the same number of terms"
              for r in rows do
                if r.length != ncols then
                  if cols.isEmpty then err s!"table {t.name} has {ncols} columns but {r.length} values were supplied"
                  err s!"{r.length} values for {ncols} columns"
              pure (rows.toArray.map fun r => r.toArray.mapM (evalExpr q))
          | .select sel => do
              let (cm, rows) ← runSelect q sel
              if cm.size != ncols then
                if cols.isEmpty then err s!"table {t.name} has {ncols} columns but {cm.size} values were supplied"
                err s!"{cm.size} values for {ncols} columns"
              pure (rows.map pure)
          | .defaults => pure #[pure #[]]
        let colIdx := match src with
          | .defaults => []
          | _ => if cols.isEmpty then (List.range t.cols.size).filter fun (i : Nat) => (t.cols[i]!).generated.isNone else colIdx
        let mut inserted := #[]
        let mut n : Int := 0
        for rM in srcRows do
          let r ← rM
          -- defaults for the other columns
          let mut vals := Array.replicate t.cols.size Value.null
          let mut given := Array.replicate t.cols.size false
          let mut rowidV : Option Value := none
          for (ci, k) in colIdx.zipIdx do
            if ci == t.cols.size then rowidV := some r[k]!
            else vals := vals.set! ci r[k]!; given := given.set! ci true
          for h : i in [0:t.cols.size] do
            if !given[i]! then
              if let some d := t.cols[i].dflt then vals := vals.set! i (← evalExpr {} d)
          if let some ci := t.rowidCol then
            if given[ci]! then rowidV := some vals[ci]!
          -- BEFORE INSERT triggers see NEW with the defaults (rowid -1 when it is not given)
          let hasBefore := (← getDb).main.triggers.any fun tr => nameEq tr.table tname && tr.time == .before &&
            match tr.event with | .insert => true | _ => false
          if hasBefore then
            let mut nvals := vals
            for h : i in [0:t.cols.size] do nvals := nvals.set! i (← storeValue t i (vals[i]?.getD .null))
            let rid := match rowidV.map (applyAffinity .integer) with | some (.int i) => i | _ => -1
            -- RAISE(FAIL) keeps the rows inserted so far, and counts them
            tryCatch (runTriggers q .before .insert tname none (some { rowid := rid, vals := nvals }))
              fun e => do
                if e.keep then modify fun c => { c with db := { c.db with changes := n, totalChanges := c.db.totalChanges + n } }
                throw e
          -- UPSERT: a conflict on the target runs the DO clause instead
          let r? : Option Row ← try (insertRow tname vals rowidV (if upserts.isEmpty then orC else some .abort))
            catch e => do
              -- FAIL keeps the earlier rows on a constraint conflict (insertRow
              -- marks it); any other error rolls the statement back
              if e.keep && upserts.isEmpty then
                modify fun c => { c with db := { c.db with changes := n, totalChanges := c.db.totalChanges + n } }
                throw e
              if upserts.isEmpty || !(e.code == SQLITE_CONSTRAINT_UNIQUE || e.code == SQLITE_CONSTRAINT_PRIMARYKEY) then throw e
              let some up := upserts.head? | throw e
              match up.action with
              | .nothing => pure none
              | .update sets wh =>
                -- the conflicting row
                let t ← currentTable tname
                let mut vals' := vals
                for h : i in [0:t.cols.size] do
                  vals' := vals'.set! i (← storeValue t i vals[i]!)
                let probe : Row := { rowid := (rowidV.map (·.toInt)).getD 0, vals := vals' }
                let uq := allUniques (← getDb) t
                let conflict := t.rows.find? fun old =>
                  (t.rowidCol.isSome && rowidV.isSome && old.rowid == probe.rowid) ||
                  uq.any fun (k, _) => keyEq k (keyOf old k) (keyOf probe k)
                match conflict with
                | none => throw e
                | some old =>
                  let exSrc := { tableSrc "excluded" t with hasRowid := false, qualOnly := true }
                  let qx := { q with env := { q.env with frames := { srcs := #[tableSrc t.name t, exSrc], cur := #[some old, some probe] } :: q.env.frames } }
                  let pass ← match wh with
                    | some wexp => condHolds qx wexp
                    | none => pure true
                  if !pass then pure none else
                  let mut nv := old.vals
                  for (names, ex) in sets do
                    let v ← evalExpr qx ex
                    for nm in names do
                      match t.cols.toList.findIdx? (nameEq ·.name nm) with
                      | some i => nv := nv.set! i (← storeValue t i v)
                      | none => err s!"no such column: {nm}"
                  let newRow ← withGenerated t { old with vals := nv }
                  let _ ← checkRow t newRow
                  let others := t.rows.filter (·.rowid != old.rowid)
                  for (k, _) in allUniques (← getDb) t do
                    if others.any (fun r => keyEq k (keyOf r k) (keyOf newRow k)) then
                      err (uniqueMsg t k) (if k.isPk then SQLITE_CONSTRAINT_PRIMARYKEY else SQLITE_CONSTRAINT_UNIQUE)
                  modifyMain fun s => s.setTable { t with rows := sortRows t (others.push newRow) }
                  pure (some newRow)
          match r? with
          | some row =>
            n := n + 1
            inserted := inserted.push row
            modify fun c => { c with db := { c.db with lastRowid := row.rowid } }
            tryCatch (runTriggers q .after (.insert) tname none (some row))
              fun e => do
                if e.keep then modify fun c => { c with db := { c.db with changes := n, totalChanges := c.db.totalChanges + n } }
                throw e
          | _ => pure ()
        countChanges q n
        resultRows q (← currentTable tname) tname inserted ret
      | .update _ orC _ tname «alias» sets from_ wh ret _ _ _ =>
        if ← viewWithTriggers tname then
          return ← updateView q tname sets wh
        let t ← currentTable tname
        let «alias» := «alias».getD tname
        let src := tableSrc «alias» t
        -- with FROM: each target row is joined with the FROM rows; the first match is used
        let (fsrcs, frows) ← match from_ with
          | some f => evalFrom q f
          | none => pure (#[], #[#[]])
        let mut targets : Array (Row × Array Cur) := #[]
        for r in t.rows do
          -- which matching FROM row is used is the plan's choice
          for fr in ← permA frows do
            let qr := { q with env := { q.env with frames := { srcs := #[src] ++ fsrcs, cur := #[some r] ++ fr } :: q.env.frames } }
            let ok ← match wh with
              | some w => condHolds qr w
              | none => pure true
            if ok then targets := targets.push (r, fr); break
        -- the order the rows are updated in is the plan's
        targets ← permA targets
        let mut updated := #[]
        for (old, fr) in targets do
          let t ← currentTable tname
          -- the row as it is now (an earlier trigger may have changed it)
          let some old := t.rows.find? (·.rowid == old.rowid) | continue
          let qr := { q with env := { q.env with frames := { srcs := #[src] ++ fsrcs, cur := #[some old] ++ fr } :: q.env.frames } }
          let mut nv := old.vals
          let mut newRowid := old.rowid
          for (names, ex) in sets do
            let v ← evalExpr qr ex
            for nm in names do
              match t.cols.toList.findIdx? (nameEq ·.name nm) with
              | some i =>
                nv := nv.set! i (← storeValue t i v)
                if t.rowidCol == some i then
                  match applyAffinity .integer v with
                  | .int ri => newRowid := ri
                  | _ => err "datatype mismatch" SQLITE_MISMATCH
              | none =>
                if isRowidName nm && !t.withoutRowid then
                  match applyAffinity .integer v with
                  | .int ri => newRowid := ri
                  | _ => err "datatype mismatch" SQLITE_MISMATCH
                else err s!"no such column: {nm}"
          let newRow ← withGenerated t { rowid := newRowid, vals := nv }
          runTriggers q .before (.update (sets.flatMap (·.1))) tname (some old) (some newRow)
          let t ← currentTable tname
          -- a constraint error under resolution `r` (FAIL keeps the rows
          -- updated so far, ROLLBACK rolls the transaction back)
          let conflictErr (r : ConflictRes) (m : String) (code : Nat) : D Unit := do
            if r == .fail then countChanges q updated.size
            throwConflict r m code
          -- NOT NULL, resolved by UPDATE OR <oc> (else the column's ON CONFLICT)
          let mut newRow := newRow
          let mut skipNN := false
          for h : i in [0:t.cols.size] do
            let c := t.cols[i]
            if c.notNull && (newRow.vals[i]?.getD .null).isNull then
              match resolveConflict orC c.notNullConflict with
              | .ignore => skipNN := true
              | .replace =>
                match c.dflt with
                | some d => newRow := { newRow with vals := newRow.vals.set! i (← storeValue t i (← evalExpr {} d)) }
                | none => err s!"NOT NULL constraint failed: {t.name}.{c.name}" SQLITE_CONSTRAINT_NOTNULL
              | r => conflictErr r s!"NOT NULL constraint failed: {t.name}.{c.name}" SQLITE_CONSTRAINT_NOTNULL
          if skipNN then continue
          if !(← checkRow t newRow orC) then continue
          -- conflicts, resolved by UPDATE OR <oc> (else the constraint's own ON CONFLICT)
          let mut others := t.rows.filter (·.rowid != old.rowid)
          let mut skip := false
          if others.any (·.rowid == newRowid) && !t.withoutRowid then
            let cname := match t.rowidCol with | some ci => t.cols[ci]!.name | none => "rowid"
            match resolveConflict orC t.rowidConflict with
            | .replace => others := others.filter (·.rowid != newRowid)
            | .ignore => skip := true
            | r => conflictErr r s!"UNIQUE constraint failed: {t.name}.{cname}" SQLITE_CONSTRAINT_PRIMARYKEY
          if !skip then
            for (k, _) in allUniques (← getDb) t do
              if others.any (fun r => keyEq k (keyOf r k) (keyOf newRow k)) then
                match resolveConflict orC k.onConflict with
                | .replace => others := others.filter (fun r => !keyEq k (keyOf r k) (keyOf newRow k))
                | .ignore => skip := true
                | r => conflictErr r (uniqueMsg t k) (if k.isPk then SQLITE_CONSTRAINT_PRIMARYKEY else SQLITE_CONSTRAINT_UNIQUE)
          if skip then continue
          modifyMain fun s => s.setTable { t with rows := sortRows t (others.push newRow) }
          fkOnParentUpdate tname old newRow
          updated := updated.push newRow
          let changedCols := sets.flatMap (·.1)
          runTriggers q .after (.update changedCols) tname (some old) (some newRow)
        countChanges q updated.size
        resultRows q (← currentTable tname) «alias» updated ret
      | .delete _ _ tname «alias» wh ret _ _ _ =>
        if ← viewWithTriggers tname then
          return ← deleteView q tname wh
        let t ← currentTable tname
        let «alias» := «alias».getD tname
        let src := tableSrc «alias» t
        let mut gone := #[]
        for r in t.rows do
          let qr := { q with env := { q.env with frames := { srcs := #[src], cur := #[some r] } :: q.env.frames } }
          match wh with
          | some w => if ← condHolds qr w then gone := gone.push r
          | none => gone := gone.push r
        -- the order the rows are deleted in is the plan's
        gone ← permA gone
        let out ← resultRows q t «alias» gone ret
        for r in gone do
          runTriggers q .before .delete tname (some r) none
          let t ← currentTable tname
          modifyMain fun s => s.setTable { t with rows := t.rows.filter (·.rowid != r.rowid) }
          fkOnParentDelete tname r
          runTriggers q .after .delete tname (some r) none
        countChanges q gone.size
        return out
      | .begin_ _ =>
        let db ← getDb
        if db.inTxn then err "cannot start a transaction within a transaction"
        setDb { db with inTxn := true, savepoints := [("", db.main)] }
        return #[]
      | .commit =>
        let db ← getDb
        if !db.inTxn then err "cannot commit - no transaction is active"
        setDb { db with inTxn := false, savepoints := [] }
        return #[]
      | .rollback none =>
        let db ← getDb
        if !db.inTxn then err "cannot rollback - no transaction is active"
        let base := (db.savepoints.getLast?.map (·.2)).getD db.main
        setDb { db with inTxn := false, savepoints := [], main := base }
        return #[]
      | .rollback (some sp) =>
        let db ← getDb
        match db.savepoints.findIdx? (nameEq ·.1 sp) with
        | none => err s!"no such savepoint: {sp}"
        | some i =>
          let (_, snap) := db.savepoints[i]!
          setDb { db with main := snap, savepoints := db.savepoints.drop i }
          return #[]
      | .savepoint sp =>
        let db ← getDb
        if db.inTxn then setDb { db with savepoints := (sp, db.main) :: db.savepoints }
        else setDb { db with inTxn := true, savepoints := [(sp, db.main)] }
        return #[]
      | .release sp =>
        let db ← getDb
        match db.savepoints.findIdx? (nameEq ·.1 sp) with
        | none => err s!"no such savepoint: {sp}"
        | some i =>
          let rest := db.savepoints.drop (i + 1)
          -- releasing the outermost savepoint (when it started the transaction) commits
          if rest.isEmpty || (rest.all (·.1 == "") && false) then
            setDb { db with savepoints := [], inTxn := false }
          else setDb { db with savepoints := rest }
          return #[]
      | .pragma sch name arg _ =>
        let argV ← match arg with
          | some (.lit v) => pure (some v)
          | some e => some <$> evalExpr q e
          | none => pure none
        match Pragma.runWith (← viewCols) (← getDb) sch name argV with
        | .ok (db', rows) => setDb db'; return rows
        | .error e => throw e
      | .alterAddColumn _ tname cd txt =>
        let t ← currentTable tname
        if t.cols.any (nameEq ·.name cd.name) then err s!"duplicate column name: {cd.name}"
        for (_, k) in cd.constraints do
          match k with
          | .primaryKey .. => err "Cannot add a PRIMARY KEY column"
          | .unique .. => err "Cannot add a UNIQUE column"
          | .generated _ true => err "cannot add a STORED column"
          | _ => pure ()
        let t1 ← mkTable t.name [cd] [] false false ""
        let c := t1.cols[0]!
        if c.notNull && c.dflt.isNone && c.generated.isNone && !t.rows.isEmpty then
          err "Cannot add a NOT NULL column with default value NULL"
        let dv ← match c.dflt with
          | some d => storeValue { t with cols := t.cols.push c } t.cols.size (← evalExpr {} d)
          | none => pure .null
        let newFks := t1.fks.map (fun (fk : ForeignKey) => { fk with cols := [t.cols.size] })
        let newRows := t.rows.map (fun (r : Row) => { r with vals := r.vals.push dv })
        let t' := { t with cols := t.cols.push c, checks := t.checks ++ t1.checks, fks := t.fks ++ newFks,
                           sql := addColumnText t.sql txt, rows := newRows }
        let t' := { t' with rows := ← t'.rows.mapM (withGenerated t') }
        modifyMain fun s => s.setTable t'
        return #[]
      | .alterRenameColumn _ tname old new =>
        let t ← currentTable tname
        let some ci := t.cols.toList.findIdx? (nameEq ·.name old) | err s!"no such column: \"{old}\""
        if t.cols.any (nameEq ·.name new) then err s!"duplicate column name: {new}"
        let t' := { t with cols := t.cols.modify ci (fun c => { c with name := new }), sql := renameIdent t.sql old new }
        modifyMain fun s => { (s.setTable t') with objs := (s.setTable t').objs.map (renameColInIndex tname old new) }
        return #[]
      | .alterRename _ tname new =>
        let t ← currentTable tname
        let db ← getDb
        if objExists db new then err s!"there is already another table or index with this name: {new}"
        let q' := "\"" ++ new ++ "\""
        let t' := { t with name := new, sql := renameIdent t.sql tname q' }
        modifyMain fun s => { s with objs := s.objs.map (renameTableObj tname new q' t') }
        return #[]
      | .alterDropColumn _ tname col =>
        let t ← currentTable tname
        let some ci := t.cols.toList.findIdx? (nameEq ·.name col) | err s!"no such column: \"{col}\""
        if t.pk.contains ci then err s!"cannot drop PRIMARY KEY column: \"{col}\""
        if t.uniques.any (·.cols.any (·.1 == ci)) then err s!"cannot drop UNIQUE column: \"{col}\""
        if t.cols.size == 1 then err s!"cannot drop column \"{col}\": no other columns exist"
        let shift (i : Nat) : Nat := if i > ci then i - 1 else i
        let t' := { t with cols := t.cols.eraseIdx! ci, rowidCol := t.rowidCol.map shift, pk := t.pk.map shift,
                           sql := dropColumnText t.sql col,
                           rows := t.rows.map fun r => { r with vals := r.vals.eraseIdx! ci } }
        modifyMain fun s => s.setTable t'
        return #[]
      | .attach file schema =>
        let f ← evalExpr q file
        let nm ← match schema with
          | .col none none n => pure n
          | e => do pure (String.fromUTF8! (textOf (← evalExpr q e)))
        let db ← getDb
        if nameEq nm "main" || nameEq nm "temp" || db.attached.any (nameEq · nm) then
          err s!"database {nm} is already in use"
        if db.attached.length ≥ 10 then err "too many attached databases - max 10"
        let fname := String.fromUTF8! (textOf f)
        if !(fname == ":memory:" || fname == "") then
          err "ATTACH of a database file is not modelled (the semantics has no file system yet)"
        setDb { db with attached := db.attached ++ [nm] }
        return #[]
      | .detach nm =>
        let db ← getDb
        if nameEq nm "main" || nameEq nm "temp" then err s!"cannot detach database {nm}"
        if !(db.attached.any (nameEq · nm)) then err s!"no such database: {nm}"
        let gone (o : SchemaObj) : Bool := match o with
          | .table t => t.attachedTo.any (nameEq · nm)
          | .view v => v.attachedTo.any (nameEq · nm)
          | .index ix => ((db.main.findTable ix.table db.attached).bind (·.attachedTo)).any (nameEq · nm)
          | .trigger tr => ((db.main.findTable tr.table db.attached).bind (·.attachedTo)).any (nameEq · nm)
        setDb { db with attached := db.attached.filter (!nameEq · nm), main := { db.main with objs := db.main.objs.filter (!gone ·) } }
        return #[]
      | .reindex none => return #[]
      | .reindex (some n) =>
        let db ← getDb
        if (collOfName n).isSome || (db.main.findTable n).isSome || db.main.indexes.any (nameEq ·.name n) then return #[]
        err "unable to identify the object to be reindexed"
      | .analyze target =>
        let db ← getDb
        -- what to analyze: everything, a database, an index or a table
        -- (sqlite3Analyze); the stat rows deleted first (openStatTable)
        let isDb (n : Name) := nameEq n "main" || db.attached.any (nameEq · n)
        let inHashOrder : List Table :=
          let ts := Pragma.tablesIn db "main"
          let keys := (Pragma.hashOf db "main").keys
          keys.filterMap fun k => ts.find? (nameEq ·.name k)
        let (targets, del) : List (Table × Option Name) × (Row → Bool) ← match target with
          | none => pure (inHashOrder.map (·, none), fun _ => true)
          | some n =>
            if isDb n then pure (inHashOrder.map (·, none), fun _ => true)
            else match db.main.indexes.find? (nameEq ·.name n) with
              | some ix => match db.main.findTable ix.table with
                | some t => pure ([(t, some ix.name)], fun (r : Row) => match r.vals[1]? with
                    | some (Value.text b) => nameEq (String.fromUTF8! b) ix.name | _ => false)
                | none => err s!"no such table: {ix.table}"
              | none => match db.main.findTable n with
                | some t => pure ([(t, none)], fun (r : Row) => match r.vals[0]? with
                    | some (Value.text b) => nameEq (String.fromUTF8! b) t.name | _ => false)
                | none =>
                  if (db.main.findView n).isSome then pure ([], fun _ => false)
                  else err s!"no such table: {n}"
        if (db.main.findTable "sqlite_stat1").isNone then
          let st ← mkTable "sqlite_stat1" [{ name := "tbl", type := "", constraints := [] },
            { name := "idx", type := "", constraints := [] }, { name := "stat", type := "", constraints := [] }]
            [] false false "CREATE TABLE sqlite_stat1(tbl,idx,stat)"
          modifyMain fun s => { s with objs := s.objs.push (.table st) }
        let some st := (← getDb).main.findTable "sqlite_stat1" | err "internal: sqlite_stat1"
        let mut rows := st.rows.filter (!del ·)
        for (t, only) in targets do
          if t.name.toLower.startsWith "sqlite_" then continue
          for (idx, stat) in ← analyzeRows t only do
            let rid := rows.foldl (fun m r => max m r.rowid) 0 + 1
            rows := rows.push { rowid := rid, vals := #[.ofString t.name, (idx.map Value.ofString).getD .null, stat] }
        modifyMain fun s => s.setTable { st with rows }
        return #[]
      | .vacuum _ none => return #[]
      | .createVirtualTable ine _ name m _ tailAt =>
        -- this build registers no module that CREATE VIRTUAL TABLE can use
        -- (json_each and the pragma tables are eponymous only); the name is
        -- checked first (sqlite3StartTable)
        let db ← getDb
        if objExists db name || (db.main.findView name).isSome then
          if ine then return #[]
          -- an error of the parser (sqlite3StartTable): prepare stops there
          throw { code := SQLITE_ERROR, msg := s!"table {name} already exists", tail := some tailAt }
        err s!"no such module: {m}"
      | _ => err "statement not modelled yet"
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- ON DELETE actions for the children of a deleted parent row. -/
def fkOnParentDelete (pname : Name) (pr : Row) : D Unit :=
    do
      let db ← getDb
      if !db.pragmas.foreignKeys then return
      for (t, fk, cr) in fkChildren db pname pr do
        match fk.onDelete with
        | "CASCADE" =>
          let t ← currentTable t.name
          modifyMain fun s => s.setTable { t with rows := t.rows.filter (·.rowid != cr.rowid) }
          -- foreign key actions are trigger programs: counted in total_changes()
          modify fun c => { c with db := { c.db with totalChanges := c.db.totalChanges + 1 } }
          fkOnParentDelete t.name cr
        | "SET NULL" | "SET DEFAULT" =>
          let t ← currentTable t.name
          let mut nv := cr.vals
          for i in fk.cols do
            let v ← if fk.onDelete == "SET NULL" then pure Value.null else
              match t.cols[i]!.dflt with
              | some d => evalExpr {} d
              | none => pure .null
            nv := nv.set! i v
          modifyMain fun s => s.setTable { t with rows := t.rows.map fun r => if r.rowid == cr.rowid then { r with vals := nv } else r }
          modify fun c => { c with db := { c.db with totalChanges := c.db.totalChanges + 1 } }
        | "RESTRICT" => err "FOREIGN KEY constraint failed" SQLITE_CONSTRAINT_FOREIGNKEY
        | _ => pure ()
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- ON UPDATE actions for the children of a parent row whose key changed. -/
def fkOnParentUpdate (pname : Name) (old new : Row) : D Unit :=
    do
      let db ← getDb
      if !db.pragmas.foreignKeys then return
      let some parent := db.main.findTable pname | return
      for (t, fk, cr) in fkChildren db pname old do
        let pcols := fkParentCols parent fk
        let changed := pcols.any fun pc => compareValues .binary (parentVal parent old pc) (parentVal parent new pc) != .eq
        if !changed then continue
        match fk.onUpdate with
        | "CASCADE" | "SET NULL" | "SET DEFAULT" =>
          let t ← currentTable t.name
          let mut nv := cr.vals
          for (i, pc) in fk.cols.zip pcols do
            let v ← match fk.onUpdate with
              | "CASCADE" => pure (parentVal parent new pc)
              | "SET NULL" => pure Value.null
              | _ => match t.cols[i]!.dflt with
                | some d => evalExpr {} d
                | none => pure .null
            nv := nv.set! i v
          modifyMain fun s => s.setTable { t with rows := t.rows.map fun r => if r.rowid == cr.rowid then { r with vals := nv } else r }
          modify fun c => { c with db := { c.db with totalChanges := c.db.totalChanges + 1 } }
        | "RESTRICT" => err "FOREIGN KEY constraint failed" SQLITE_CONSTRAINT_FOREIGNKEY
        | _ => pure ()
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- Is `n` a view (DML on it runs its INSTEAD OF triggers)? -/
def viewWithTriggers (n : Name) : D Bool :=
    do
      let db ← getDb
      return (db.main.findTable n).isNone && (db.main.findView n).isSome
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def viewRows (q : QEnv) (n : Name) : D (Src × Array Row) :=
    namedSource q none n n
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def insertView (q : QEnv) (vname : Name) (cols : List Name) (src : InsertSource) : D (Array (Array Value)) :=
    do
      let (vsrc, _) ← viewRows q vname
      let rows ← match src with
        | .values rs => rs.toArray.mapM fun r => r.toArray.mapM (evalExpr q)
        | .select sel => do let (_, rs) ← runSelect q sel; pure rs
        | .defaults => pure #[#[]]
      let hasIO := (← getDb).main.triggers.any fun tr => nameEq tr.table vname && tr.time == .insteadOf &&
        match tr.event with | .insert => true | _ => false
      if !hasIO then err s!"cannot modify {vname} because it is a view"
      let n := vsrc.cols.size
      let idx := if cols.isEmpty then List.range n else cols.filterMap fun c => vsrc.cols.toList.findIdx? fun (m, _, _) => nameEq m c
      for r in rows do
        let mut vals := Array.replicate n Value.null
        for (ci, k) in idx.zipIdx do vals := vals.set! ci (r[k]?.getD .null)
        runViewTriggers q vname .insert none (some { rowid := -1, vals }) vsrc
      return #[]
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def updateView (q : QEnv) (vname : Name) (sets : List (List Name × Expr)) (wh : Option Expr) : D (Array (Array Value)) :=
    do
      let (vsrc, rows) ← viewRows q vname
      let hasIO := (← getDb).main.triggers.any fun tr => nameEq tr.table vname && tr.time == .insteadOf &&
        match tr.event with | .update _ => true | _ => false
      if !hasIO then err s!"cannot modify {vname} because it is a view"
      for r in rows do
        let qr := { q with env := { q.env with frames := { srcs := #[vsrc], cur := #[some r] } :: q.env.frames } }
        if let some w := wh then
          if !(← condHolds qr w) then continue
        let mut nv := r.vals
        for (names, ex) in sets do
          let v ← evalExpr qr ex
          for nm in names do
            match vsrc.cols.toList.findIdx? (fun (m, _, _) => nameEq m nm) with
            | some i => nv := nv.set! i v
            | none => err s!"no such column: {nm}"
        runViewTriggers q vname (.update (sets.flatMap (·.1))) (some r) (some { r with vals := nv }) vsrc
      return #[]
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

def deleteView (q : QEnv) (vname : Name) (wh : Option Expr) : D (Array (Array Value)) :=
    do
      let (vsrc, rows) ← viewRows q vname
      let hasIO := (← getDb).main.triggers.any fun tr => nameEq tr.table vname && tr.time == .insteadOf &&
        match tr.event with | .delete => true | _ => false
      if !hasIO then err s!"cannot modify {vname} because it is a view"
      for r in rows do
        let qr := { q with env := { q.env with frames := { srcs := #[vsrc], cur := #[some r] } :: q.env.frames } }
        if let some w := wh then
          if !(← condHolds qr w) then continue
        runViewTriggers q vname .delete (some r) none vsrc
      return #[]
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- INSTEAD OF triggers of a view. -/
def runViewTriggers (q : QEnv) (vname : Name) (ev : TriggerEvent) (old new : Option Row) (src : Src) : D Unit :=
    do
      for tr in (← getDb).main.triggers do
        if !nameEq tr.table vname || tr.time != .insteadOf then continue
        let fires := match tr.event, ev with
          | .insert, .insert | .delete, .delete => true
          | .update cols, .update changed => cols.isEmpty || cols.any fun c => changed.any (nameEq · c)
          | _, _ => false
        if !fires then continue
        let qt := { q with env := { q.env with newRow := new.map (src, ·), oldRow := old.map (src, ·) } }
        if let some w := tr.when_ then
          if !(← condHolds qt w) then continue
        for st in tr.body do
          let r ← try (some <$> execStmt qt st) catch e => if e.code == 0 then pure none else throw e
          if r.isNone then break
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- Run the triggers of `table` for an event at a time. -/
def runTriggers (q : QEnv) (time : TriggerTime) (ev : TriggerEvent) (table : Name)
    (old new : Option Row) : D Unit :=
    do
      let db ← getDb
      let t ← currentTable table
      let src := tableSrc table t
      for tr in db.main.triggers do
        if !nameEq tr.table table || tr.time != time then continue
        let fires := match tr.event, ev with
          | .insert, .insert => true
          | .delete, .delete => true
          | .update cols, .update changed => cols.isEmpty || cols.any fun c => changed.any (nameEq · c)
          | _, _ => false
        if !fires then continue
        let qt := { q with env := { q.env with newRow := new.map (src, ·), oldRow := old.map (src, ·) } }
        if let some w := tr.when_ then
          if !(← condHolds qt w) then continue
        for st in tr.body do
          let r ← try (some <$> execStmt qt st) catch e => if e.code == 0 then pure none else throw e
          if r.isNone then break
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity
end



/-- Execute a statement atomically: on error the database is as before
    (except for what SQLite keeps: `OR FAIL` rows, and the counters). The
    error is returned, not thrown, so that the state after it is kept. -/
def runStmt (s : Stmt) : D (Except Err (Array (Array Value))) := do
  -- json.c's parse cache lives for one statement; 'now' is fixed for it
  let clockMs ← anyOf fun (_ : Int) => True
  modify fun c => { c with jsonCache := {}, clockMs }
  let saved ← get
  try
    let before := fkOrphans saved.db
    -- prepare: names and functions are resolved before anything runs
    staticStmt s
    let rows ← execStmt {} s
    let db ← getDb
    -- PRAGMA query_only: a statement that opens a write transaction fails
    -- (after the errors of prepare, which the executor finds while running)
    if Pragma.flag saved.db "query_only" && Pragma.writes saved.db db s then
      throw { code := Pragma.SQLITE_READONLY, msg := "attempt to write a readonly database" }
    -- immediate foreign keys: the violation counter at the end of the statement
    if db.pragmas.foreignKeys then
      let isDml := match s with | .insert .. | .update .. | .delete .. => true | _ => false
      if isDml && fkOrphans db > before then
        -- a DELETE's rows were deleted (and counted) before the check failed
        let counted := match s with | .delete .. => db.changes | _ => 0
        restoreTo saved { saved.db with changes := 0, totalChanges := saved.db.totalChanges + counted }
        return .error { code := SQLITE_CONSTRAINT_FOREIGNKEY, msg := "FOREIGN KEY constraint failed" }
    -- schema cookie, pages, table hash order (Sql.Pragma)
    setDb (Pragma.afterStmt saved.db (← getDb) s)
    -- PRAGMA count_changes: DML without RETURNING returns the number of changes
    if Pragma.flag db "count_changes" && Pragma.countsChanges s then return .ok #[#[.int db.changes]]
    return .ok rows
  catch e =>
    if !e.keep then
      -- a failed statement changes nothing
      -- (the eponymous virtual tables it named stay registered)
      let failed ← get
      -- a failed INSERT/UPDATE/DELETE sets changes() to 0; other statements
      -- leave it (vdbeHalt: sqlite3VdbeSetChanges only when changeCntOn)
      let isDml := match s with | .insert .. | .update .. | .delete .. => true | _ => false
      let changes := if isDml then 0 else saved.db.changes
      -- ON CONFLICT ROLLBACK: back to the transaction's start, which ends it
      let base := if e.rollback then
          { saved.db with main := (saved.db.savepoints.getLast?.map (·.2)).getD saved.db.main,
                          inTxn := false, savepoints := [] }
        else saved.db
      -- the choices made and the spent are not rolled back
      restoreTo saved (Pragma.keepModules failed.db { base with changes })
    return .error e


/-- ⟦src⟧: the outputs of a script, run as the driver runs it (statement by
    statement, printing rows and errors), each statement's meaning applied to
    the state. The loop is bounded by the script's length (every round but the
    last moves past at least one byte); were the bound reached, the run would
    have no outcome. -/
def runScript (src : ByteArray) : Nd ByteArray := do
  let mut out := ByteArray.empty
  let mut ctx : DCtx := { db := {} }
  let mut finished := false
  let mut pos := 0
  -- the script is tokenized once; a statement starts at the first token at or
  -- after its byte offset, unless the offset falls inside a token (after the
  -- driver's skip to the next ';'), when the rest is tokenized again from there
  let mut toks := tokenize src 0
  let mut ti := 0
  for _ in [0:src.size + 1] do
    for _ in [ti:toks.size] do
      if toks[ti]!.start < pos then ti := ti + 1 else break
    if ti > 0 && toks[ti - 1]!.stop > pos then
      toks := toks.extract 0 (ti - 1) ++ tokenize src pos
      ti := ti - 1
    match parseNextTok src toks ti with
    | .empty => finished := true; break
    | .error msg tail =>
      out := out ++ renderErr { code := SQLITE_ERROR, msg }
      if tail ≤ pos then
        -- no progress: skip to after the next ';'
        let mut i := pos
        for _ in [pos:src.size] do
          if src[i]! != 59 then i := i + 1 else break
        pos := if i < src.size then i + 1 else src.size
      else pos := tail
    | .ok stmt tail =>
      pos := tail
      match ← (runStmt stmt).run.run ctx with
      | (.ok (.ok rows), ctx') =>
        ctx := ctx'
        for r in rows do out := out ++ renderRow r
      | (.ok (.error e), ctx') | (.error e, ctx') =>
        ctx := ctx'
        for r in e.printed do out := out ++ renderRow r
        out := out ++ renderErr e
        if let some t := e.tail then pos := t
  if !finished then Nd.any fun _ => False else return out

/-- `out` is an output of the script `src` (the denotation). -/
def Derives (src out : ByteArray) : Prop := out ∈ runScript src

end Sql.Den
