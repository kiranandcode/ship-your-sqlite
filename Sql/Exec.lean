/-
  Statements and scripts: what the driver (`c/driver.c`) prints for a script.
-/
import Sql.Select
import Sql.ParseStmt

namespace Sql

/-! ## Output in the driver's format -/

def quoteText (b : ByteArray) : ByteArray :=
  let q : UInt8 := 39
  ByteArray.mk (#[q] ++ (b.data.foldl (fun acc c => if c == q then acc.push q |>.push q else acc.push c) #[]) ++ #[q])

def renderValue : Value → ByteArray
  | .null => "NULL".toUTF8
  | .int i => intText i
  | .real r => realText r
  | .text s => quoteText s
  | .blob b => ("X'" ++ hexOf b ++ "'").toUTF8

def renderRow (r : Array Value) : ByteArray :=
  let parts := r.toList.map renderValue
  (match parts with
    | [] => ByteArray.empty
    | p :: ps => ps.foldl (fun acc x => acc ++ "|".toUTF8 ++ x) p) ++ "\n".toUTF8

def renderErr (e : Err) : ByteArray := s!"error: {e.code}: {e.msg}\n".toUTF8

/-! ## Schema construction -/

def isIntegerType (t : String) : Bool := t.trimAscii.toString.toUpper == "INTEGER"

def strictTypes : List String := ["INT", "INTEGER", "REAL", "TEXT", "BLOB", "ANY"]

def mkTable (name : Name) (cols : List ColumnDef) (cons : List (Option Name × TableConstraint))
    (withoutRowid strict : Bool) (sql : String) : M Table := do
  let mut cs : Array Column := #[]
  for cd in cols do
    if cs.any (nameEq ·.name cd.name) then err s!"duplicate column name: {cd.name}"
    if strict && !(strictTypes.contains cd.type.trimAscii.toString.toUpper) then
      if cd.type.trimAscii.toString.isEmpty then err s!"missing datatype for {name}.{cd.name}"
      err s!"unknown datatype for {name}.{cd.name}: \"{cd.type}\""
    let mut c : Column := { name := cd.name, type := cd.type, aff := affinityOfType cd.type }
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
  let colIdx (n : Name) : M Nat := do
    match cs.toList.findIdx? (nameEq ·.name n) with
    | some i => return i
    | none => err s!"no such column: {n}"
  let mut t : Table := { name, cols := cs, withoutRowid, strict, sql }
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
          t := { t with rowidCol := some i, autoinc := ai }
        else
          if ai then err "AUTOINCREMENT is only allowed on an INTEGER PRIMARY KEY"
          t := { t with uniques := t.uniques ++ [{ cols := [(i, cs[i]!.coll)], onConflict := oc, isPk := true }] }
      | .unique oc => t := { t with uniques := t.uniques ++ [{ cols := [(i, cs[i]!.coll)], onConflict := oc }] }
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
        t := { t with rowidCol := some idxs[0]!, autoinc := ai }
      else
        t := { t with uniques := t.uniques ++ [{ cols := ← kcols.mapM (fun (n, c, _) => do
          let i ← colIdx n; pure (i, (c.bind collOfName).getD cs[i]!.coll)), onConflict := oc, isPk := true }] }
    | .unique kcols oc =>
      t := { t with uniques := t.uniques ++ [{ cols := ← kcols.mapM (fun (n, c, _) => do
          let i ← colIdx n; pure (i, (c.bind collOfName).getD cs[i]!.coll)), onConflict := oc }] }
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

/-! ## Statement execution -/

/-- The result of a statement: output rows, then possibly an error. -/
structure StmtOut where
  rows : Array (Array Value) := #[]

def setDb (db : Db) : M Unit := modify fun c => { c with db := db }

def modifyMain (f : Schema → Schema) : M Unit :=
  modify fun c => { c with db := { c.db with main := f c.db.main } }

def objExists (db : Db) (n : Name) : Bool :=
  db.main.objs.any fun o => nameEq (Schema.objName o) n

/-- The sources of a single table, for evaluating its constraints and defaults. -/
def rowScope (t : Table) (alias : Name) (r : Row) : Scope :=
  { srcs := #[tableSrc alias t], cur := #[some r] }

def qOfRow (t : Table) (r : Row) : QEnv :=
  { env := { frames := [rowScope t t.name r] } }

/-- The value stored in a column: affinity, and STRICT type checks. -/
def storeValue (t : Table) (i : Nat) (v : Value) : M Value := do
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
def withGenerated (t : Table) (r : Row) : M Row := do
  let mut r := r
  for h : i in [0:t.cols.size] do
    if let some (e, _) := t.cols[i].generated then
      let v ← evalExpr (qOfRow t r) e
      r := { r with vals := r.vals.set! i (applyAffinity t.cols[i].aff v) }
  return r

/-- NOT NULL and CHECK constraints. -/
def checkRow (t : Table) (r : Row) : M Unit := do
  for h : i in [0:t.cols.size] do
    let c := t.cols[i]
    if c.notNull && (r.vals[i]?.getD .null).isNull then
      err s!"NOT NULL constraint failed: {t.name}.{c.name}" SQLITE_CONSTRAINT_NOTNULL
  for (nm, e) in t.checks do
    let v ← evalExpr (qOfRow t r) e
    if truth v == some false then
      err s!"CHECK constraint failed: {nm.getD ""}" SQLITE_CONSTRAINT_CHECK

/-- Unique keys of the table, including UNIQUE indexes. -/
def allUniques (db : Db) (t : Table) : List (UniqueKey × Option Name) :=
  let fromIdx := db.main.indexes.filterMap fun ix =>
    if ix.unique && nameEq ix.table t.name then
      let cols := ix.cols.filterMap fun (.mk e _ _) =>
        let (inner, coll) := match e with
          | .collate x c => (x, collOfName c)
          | x => (x, none)
        match inner with
        | .col _ _ n => (t.cols.toList.findIdx? (nameEq ·.name n)).map fun i => (i, coll.getD t.cols[i]!.coll)
        | _ => none
      if cols.length == ix.cols.length then some ({ cols, onConflict := none }, some ix.name) else none
    else none
  (t.uniques.map (·, none)) ++ fromIdx

def keyOf (r : Row) (k : UniqueKey) : Array Value := k.cols.toArray.map fun (i, _) => r.vals[i]?.getD .null

def keyEq (k : UniqueKey) (a b : Array Value) : Bool :=
  !(a.any (·.isNull)) && !(b.any (·.isNull)) &&
  (a.zip b |>.zip k.cols.toArray).all fun ((x, y), (_, c)) => compareValues c x y == .eq

def uniqueMsg (t : Table) (k : UniqueKey) : String :=
  "UNIQUE constraint failed: " ++ ", ".intercalate (k.cols.map fun (i, _) => s!"{t.name}.{t.cols[i]!.name}")

/-- Sort the rows of a table into storage order (rowid, or PRIMARY KEY for WITHOUT ROWID). -/
def sortRows (t : Table) (rows : Array Row) : Array Row :=
  if t.withoutRowid then
    let colls := t.pk.map fun i => t.cols[i]!.coll
    stableSort (fun a b => lexCompare colls [] (t.pk.toArray.map fun i => a.vals[i]!) (t.pk.toArray.map fun i => b.vals[i]!)) rows
  else stableSort (fun a b => compare a.rowid b.rowid) rows

def currentTable (n : Name) : M Table := do
  match (← getDb).main.findTable n with
  | some t => return t
  | none =>
    if (← getDb).main.findView n |>.isSome then err s!"cannot modify {n} because it is a view"
    err s!"no such table: {n}"

/-- Insert one row (values for every column, rowid value or none), applying
    conflict resolution. Returns the inserted row, or none if ignored. -/
def insertRow (tname : Name) (vals : Array Value) (rowidV : Option Value) (oc : ConflictRes) :
    M (Option Row) := do
  let t ← currentTable tname
  let db ← getDb
  let mut vals := vals
  for h : i in [0:t.cols.size] do
    vals := vals.set! i (← storeValue t i (vals[i]?.getD .null))
  -- rowid
  let maxRowid : Int := t.rows.foldl (fun m r => max m r.rowid) 0
  let rid ← match rowidV with
    | some v =>
      let v' := applyAffinity .integer v
      match v' with
      | .int i => pure i
      | .null => pure (maxRowid + 1)
      | _ => err "datatype mismatch" SQLITE_MISMATCH
    | none => pure (maxRowid + 1)
  let rid := if t.autoinc && rowidV.all (·.isNull) then
      max (maxRowid + 1) (((db.main.seq.find? (nameEq ·.1 t.name)).map (·.2)).getD 0 + 1)
    else rid
  if let some ci := t.rowidCol then vals := vals.set! ci (.int rid)
  let mut row ← withGenerated t ⟨rid, vals⟩
  -- NOT NULL with conflict resolution
  for h : i in [0:t.cols.size] do
    let c := t.cols[i]
    if c.notNull && (row.vals[i]?.getD .null).isNull then
      match c.notNullConflict.getD oc with
      | .ignore => return none
      | .replace =>
        match c.dflt with
        | some d => row := { row with vals := row.vals.set! i (← storeValue t i (← evalExpr {} d)) }
        | none => err s!"NOT NULL constraint failed: {t.name}.{c.name}" SQLITE_CONSTRAINT_NOTNULL
      | _ => err s!"NOT NULL constraint failed: {t.name}.{c.name}" SQLITE_CONSTRAINT_NOTNULL
  checkRow t row
  -- uniqueness: the rowid, then the unique keys
  let mut rows := t.rows
  if !t.withoutRowid then
    if rows.any (·.rowid == rid) then
      match oc with
      | .ignore => return none
      | .replace => rows := rows.filter (·.rowid != rid)
      | _ =>
        let cname := match t.rowidCol with | some ci => t.cols[ci]!.name | none => "rowid"
        err s!"UNIQUE constraint failed: {t.name}.{cname}" SQLITE_CONSTRAINT_PRIMARYKEY
  for (k, _) in allUniques db t do
    let key := keyOf row k
    if rows.any (fun r => keyEq k (keyOf r k) key) then
      match k.onConflict.getD oc with
      | .ignore => return none
      | .replace => rows := rows.filter (fun r => !keyEq k (keyOf r k) key)
      | _ => err (uniqueMsg t k) (if k.isPk then SQLITE_CONSTRAINT_PRIMARYKEY else SQLITE_CONSTRAINT_UNIQUE)
  let t' := { t with rows := sortRows t (rows.push row) }
  modifyMain fun s => s.setTable t'
  if t.autoinc then
    modifyMain fun s =>
      let cur := ((s.seq.find? (nameEq ·.1 t.name)).map (·.2)).getD 0
      { s with seq := (t.name, max cur rid) :: s.seq.filter (!nameEq ·.1 t.name) }
  return some row

def resultRows (q : QEnv) (t : Table) (alias : Name) (rows : Array Row) (ret : List ResultCol) :
    M (Array (Array Value)) := do
  if ret.isEmpty then return #[]
  let src := tableSrc alias t
  let cols ← expandCols #[src] ret
  rows.mapM fun r => do
    let q' := { q with env := { q.env with frames := { srcs := #[src], cur := #[some r] } :: q.env.frames } }
    cols.toArray.filterMapM fun c => match c with
      | .expr e _ _ => some <$> evalExpr q' e
      | _ => pure none

mutual

/-- Execute a statement; returns its output rows. -/
partial def execStmt (q : QEnv) (s : Stmt) : M (Array (Array Value)) := do
  match s with
  | .select sel =>
    let (_, rows) ← runSelect q sel
    return rows
  | .explain _ _ => err "EXPLAIN is not modelled"
  | .createTable temp ine sch name cols cons wr strict asSel sql =>
    let _ := sch
    if temp then err "TEMP tables are not modelled yet"
    let db ← getDb
    if objExists db name then
      if ine then return #[]
      if (db.main.findTable name).isSome then err s!"table {name} already exists"
      err s!"there is already an index named {name}"
    if name.toLower.startsWith "sqlite_" then err s!"object name reserved for internal use: {name}"
    let t ← match asSel with
      | some sel =>
        let (cmeta, rows) ← runSelect q sel
        let cds := cmeta.toList.map fun c => ({ name := c.name, type := match c.aff with
          | some .integer => "INT" | some .real => "REAL" | some .text => "TEXT" | some .numeric => "NUM" | _ => "", constraints := [] } : ColumnDef)
        let t ← mkTable name cds [] false false ""
        let sqlText := "CREATE TABLE " ++ name ++ "(" ++ ",".intercalate (cds.map fun c => c.name ++ (if c.type.isEmpty then "" else " " ++ c.type)) ++ ")"
        pure { t with sql := sqlText, rows := rows.mapIdx fun i r => ⟨i + 1, r⟩ }
      | none => mkTable name cols cons wr strict sql
    -- automatic indexes for UNIQUE and non-rowid PRIMARY KEY constraints
    let nAuto := t.uniques.length
    modifyMain fun s => { s with objs := s.objs.push (.table t) ++
      ((List.range nAuto).toArray.map fun i => .index
        { name := s!"sqlite_autoindex_{name}_{i + 1}", table := name, cols := [], unique := false,
          where_ := none, sql := none }) }
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
    if temp then err "TEMP views are not modelled yet"
    let db ← getDb
    if objExists db name then
      if ine then return #[]
      err s!"view {name} already exists"
    let _ ← runSelect q sel
    modifyMain fun s => { s with objs := s.objs.push (.view { name, cols, q := sel, sql }) }
    return #[]
  | .createTrigger _ ine _ name time ev tname _ w body sql =>
    let db ← getDb
    if objExists db name then
      if ine then return #[]
      err s!"trigger {name} already exists"
    if (db.main.findTable tname).isNone && (db.main.findView tname).isNone then
      err s!"no such table: main.{tname}"
    modifyMain fun s => { s with objs := s.objs.push (.trigger { name, table := tname, time, event := ev, when_ := w, body, sql }) }
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
    let t ← currentTable tname
    let oc := orC.getD .abort
    let colIdx ← if cols.isEmpty then pure (List.range t.cols.size)
      else cols.mapM fun c => do
        match t.cols.toList.findIdx? (nameEq ·.name c) with
        | some i => pure i
        | none => if isRowidName c && !t.withoutRowid then pure t.cols.size else err s!"table {t.name} has no column named {c}"
    let ncols := if cols.isEmpty then (t.cols.toList.filter fun c => c.generated.isNone).length else cols.length
    let srcRows ← match src with
      | .values rows => rows.toArray.mapM fun r => do
          if r.length != ncols then
            if cols.isEmpty then err s!"table {t.name} has {ncols} columns but {r.length} values were supplied"
            err s!"{r.length} values for {ncols} columns"
          r.toArray.mapM (evalExpr q)
      | .select sel => do
          let (cm, rows) ← runSelect q sel
          if cm.size != ncols then
            if cols.isEmpty then err s!"table {t.name} has {ncols} columns but {cm.size} values were supplied"
            err s!"{cm.size} values for {ncols} columns"
          pure rows
      | .defaults => pure #[#[]]
    let colIdx := if cols.isEmpty then (List.range t.cols.size).filter fun i => t.cols[i]!.generated.isNone else colIdx
    let mut inserted := #[]
    let mut n : Int := 0
    for r in srcRows do
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
      -- UPSERT: a conflict on the target runs the DO clause instead
      let r? : Option Row ← try (insertRow tname vals rowidV (if upserts.isEmpty then oc else .abort))
        catch e => do
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
            let probe : Row := ⟨(rowidV.map (·.toInt)).getD 0, vals'⟩
            let uq := allUniques (← getDb) t
            let conflict := t.rows.find? fun old =>
              (t.rowidCol.isSome && rowidV.isSome && old.rowid == probe.rowid) ||
              uq.any fun (k, _) => keyEq k (keyOf old k) (keyOf probe k)
            match conflict with
            | none => throw e
            | some old =>
              let exSrc := { tableSrc "excluded" t with hasRowid := false }
              let qx := { q with env := { q.env with frames := { srcs := #[tableSrc t.name t, exSrc], cur := #[some old, some probe] } :: q.env.frames } }
              let pass ← match wh with
                | some wexp => do pure (truth (← evalExpr qx wexp) == some true)
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
              checkRow t newRow
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
        runTriggers q .after (.insert) tname none (some row)
      | _ => pure ()
    modify fun c => { c with db := { c.db with changes := n, totalChanges := c.db.totalChanges + n } }
    resultRows q (← currentTable tname) tname inserted ret
  | .update _ orC _ tname alias sets from_ wh ret _ _ _ =>
    let _ := from_
    let _ := orC
    let t ← currentTable tname
    let alias := alias.getD tname
    let src := tableSrc alias t
    let mut targets : Array Row := #[]
    for r in t.rows do
      let qr := { q with env := { q.env with frames := { srcs := #[src], cur := #[some r] } :: q.env.frames } }
      match wh with
      | some w => if truth (← evalExpr qr w) == some true then targets := targets.push r
      | none => targets := targets.push r
    let mut updated := #[]
    for old in targets do
      let t ← currentTable tname
      let qr := { q with env := { q.env with frames := { srcs := #[src], cur := #[some old] } :: q.env.frames } }
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
      let newRow ← withGenerated t ⟨newRowid, nv⟩
      checkRow t newRow
      let others := t.rows.filter (·.rowid != old.rowid)
      if others.any (·.rowid == newRowid) && !t.withoutRowid then
        let cname := match t.rowidCol with | some ci => t.cols[ci]!.name | none => "rowid"
        err s!"UNIQUE constraint failed: {t.name}.{cname}" SQLITE_CONSTRAINT_PRIMARYKEY
      for (k, _) in allUniques (← getDb) t do
        if others.any (fun r => keyEq k (keyOf r k) (keyOf newRow k)) then
          err (uniqueMsg t k) (if k.isPk then SQLITE_CONSTRAINT_PRIMARYKEY else SQLITE_CONSTRAINT_UNIQUE)
      modifyMain fun s => s.setTable { t with rows := sortRows t (others.push newRow) }
      updated := updated.push newRow
      let changedCols := sets.flatMap (·.1)
      runTriggers q .after (.update changedCols) tname (some old) (some newRow)
    modify fun c => { c with db := { c.db with changes := updated.size, totalChanges := c.db.totalChanges + updated.size } }
    resultRows q (← currentTable tname) alias updated ret
  | .delete _ _ tname alias wh ret _ _ _ =>
    let t ← currentTable tname
    let alias := alias.getD tname
    let src := tableSrc alias t
    let mut gone := #[]
    for r in t.rows do
      let qr := { q with env := { q.env with frames := { srcs := #[src], cur := #[some r] } :: q.env.frames } }
      match wh with
      | some w => if truth (← evalExpr qr w) == some true then gone := gone.push r
      | none => gone := gone.push r
    let out ← resultRows q t alias gone ret
    for r in gone do
      runTriggers q .before .delete tname (some r) none
      let t ← currentTable tname
      modifyMain fun s => s.setTable { t with rows := t.rows.filter (·.rowid != r.rowid) }
      runTriggers q .after .delete tname (some r) none
    modify fun c => { c with db := { c.db with changes := gone.size, totalChanges := c.db.totalChanges + gone.size } }
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
  | .pragma _ name arg _ => execPragma q name arg
  | _ => err "statement not modelled yet"

partial def execPragma (q : QEnv) (name : Name) (arg : Option Expr) : M (Array (Array Value)) := do
  let db ← getDb
  let argV ← match arg with
    | some e => some <$> evalExpr q (match e with | .col none none n => .lit (.ofString n) | x => x)
    | none => pure none
  let boolArg (v : Value) : Bool :=
    match v with
    | .text s => let u := (String.fromUTF8! s).toLower; u == "on" || u == "yes" || u == "true" || u == "1"
    | w => truth w == some true
  match name.toLower with
  | "user_version" =>
    match argV with
    | some v => modifyMain (fun s => { s with userVersion := v.numeric.toInt }); return #[]
    | none => return #[#[.int db.main.userVersion]]
  | "foreign_keys" =>
    match argV with
    | some v => setDb { db with pragmas := { db.pragmas with foreignKeys := boolArg v } }; return #[]
    | none => return #[#[.int (if db.pragmas.foreignKeys then 1 else 0)]]
  | "case_sensitive_like" =>
    if let some v := argV then setDb { db with pragmas := { db.pragmas with caseSensitiveLike := boolArg v } }
    return #[]
  | "recursive_triggers" =>
    match argV with
    | some v => setDb { db with pragmas := { db.pragmas with recursiveTriggers := boolArg v } }; return #[]
    | none => return #[#[.int (if db.pragmas.recursiveTriggers then 1 else 0)]]
  | "integrity_check" | "quick_check" => return #[#[.ofString "ok"]]
  | "table_info" | "table_xinfo" =>
    let some v := argV | return #[]
    let tn := String.fromUTF8! (textOf v)
    match db.main.findTable tn with
    | none => return #[]
    | some t =>
      return t.cols.mapIdx fun i c =>
        #[.int i, .ofString c.name, .ofString c.type, .int (if c.notNull then 1 else 0),
          (match c.dflt with | some _ => .ofString "?" | none => .null),
          .int (match t.pk.findIdx? (· == i) with | some k => k + 1 | none => 0)]
  | _ => return #[]

/-- Run the triggers of `table` for an event at a time. -/
partial def runTriggers (q : QEnv) (time : TriggerTime) (ev : TriggerEvent) (table : Name)
    (old new : Option Row) : M Unit := do
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
      if truth (← evalExpr qt w) != some true then continue
    for st in tr.body do
      let r ← try (some <$> execStmt qt st) catch e => if e.code == 0 then pure none else throw e
      if r.isNone then break
end

/-- Execute a statement atomically: on error the database is as before. -/
def runStmt (s : Stmt) : M (Array (Array Value)) := do
  let saved ← get
  try
    let rows ← execStmt {} s
    return rows
  catch e =>
    -- keep the counters, restore the data
    set { saved with db := { saved.db with changes := saved.db.changes } }
    throw e

/-- Run a script as the driver does: statement by statement, printing rows and errors. -/
partial def runScript (src : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut ctx : Ctx := { db := {} }
  let mut pos := 0
  let mut fuel := src.size + 1
  while fuel > 0 do
    fuel := fuel - 1
    match parseNext src pos with
    | .empty => break
    | .error msg tail =>
      out := out ++ renderErr ⟨SQLITE_ERROR, msg⟩
      if tail ≤ pos then
        -- no progress: skip to after the next ';'
        let mut i := pos
        while i < src.size && src[i]! != 59 do i := i + 1
        pos := if i < src.size then i + 1 else src.size
      else pos := tail
    | .ok stmt tail =>
      pos := tail
      match (runStmt stmt).run ctx with
      | .ok (rows, ctx') =>
        ctx := ctx'
        for r in rows do out := out ++ renderRow r
      | .error e => out := out ++ renderErr e
  return out

end Sql
