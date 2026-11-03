/-
  PRAGMA statements (https://sqlite.org/pragma.html) as SQLite 3.54.1's
  pragma.c implements them, for the D7 build on an in-memory database
  (`:memory:` main, attached `:memory:` databases, and the `temp` database).

  * Arguments are parsed as pragma.c parses `zRight`: `sqlite3GetInt32`,
    `sqlite3Atoi`, `sqlite3DecOrHexToI64`, `getSafetyLevel`/`sqlite3GetBoolean`,
    `getTempStore`, `getAutoVacuum`, the journal-mode prefix match.
  * Connection settings live in `Db.pragmaVals` (keys below), header cookies
    and page counts in `Schema.cookies` (so ROLLBACK restores them), the
    order of each schema's table hash in `Db.tblHash`; `Db.pragmas` holds
    the three flags the evaluator reads (foreign_keys, recursive_triggers,
    case_sensitive_like).
  * `afterStmt` is the executor's hook: after every successful statement it
    bumps the schema cookie of each database whose schema changed (one bump
    per statement, as `sqlite3ChangeCookie` does), allocates and frees pages,
    and keeps the table hash order. Checked against the oracle
    (tests/sem/pragma-ddl.sql, pragma-cookies.sql): CREATE/DROP of a table,
    index, view or trigger and every ALTER TABLE bump the cookie of the
    database the object is in (temp objects: `temp.schema_version`), once per
    statement (CREATE TABLE … AS SELECT, AUTOINCREMENT with its
    sqlite_sequence, DROP TABLE with its indexes and triggers: one bump);
    `IF [NOT] EXISTS` no-ops, DML, REINDEX, ATTACH/DETACH and pragmas other
    than `schema_version=N` do not; VACUUM bumps by one; ROLLBACK (TO)
    restores the cookie with the schema. ANALYZE bumps when it creates
    sqlite_stat1, which the executor does not model.
  * Pages: an in-memory database has 0 pages until its first write
    transaction, then page 1; each b-tree (rowid table, index, WITHOUT ROWID
    table) has a root page, freed b-trees go to the freelist and are reused
    first, auto-vacuum databases have a pointer-map page 2. This is exact
    under the premise that every b-tree fits in its root page (small tables);
    with more data `page_count` is not derivable from the abstract state.
-/
import Sql.Db
import Sql.ParseStmt
import Sql.PragmaData

namespace Sql.Pragma

open PragmaData

/-! ## Bytes and the parsers of util.c -/

abbrev Bytes := List UInt8

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isXDigit (c : UInt8) : Bool := isDigit c || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)
def hexVal (c : UInt8) : Nat := if isDigit c then (c - 48).toNat else ((c &&& 7) + 9).toNat
/-- `sqlite3Isspace`: space, \t, \n, \v, \f, \r -/
def isSpace (c : UInt8) : Bool := c == 32 || (9 ≤ c && c ≤ 13)
def lower (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c
/-- `sqlite3StrICmp(a, b) == 0` on ASCII. -/
def iEq (a b : Bytes) : Bool := a.map lower == b.map lower
def bs (s : String) : Bytes := s.toUTF8.toList
def str (b : Bytes) : String := String.fromUTF8! (ByteArray.mk b.toArray)

/-- `sqlite3GetInt32`: the 32-bit integer at the start of `z`, if it is one. -/
def getInt32 (z : Bytes) : Option Int :=
  let (neg, z, hexOk) := match z with
    | 45 :: r => (true, r, false)
    | 43 :: r => (false, r, false)
    | _ => (false, z, true)
  match z with
  | 48 :: x :: c :: _ =>
    if hexOk && (x == 120 || x == 88) && isXDigit c then
      let r := (z.drop 2).dropWhile (· == 48)
      let ds := (r.take 8).takeWhile isXDigit
      let u := ds.foldl (fun a c => a * 16 + hexVal c) 0
      if u < 2 ^ 31 && !((r.drop ds.length).head?.map isXDigit |>.getD false) then some u else none
    else dec neg z
  | _ => dec neg z
where
  dec (neg : Bool) (z : Bytes) : Option Int :=
    if !(z.head?.map isDigit |>.getD false) then none else
    let r := z.dropWhile (· == 48)
    let ds := (r.take 11).takeWhile isDigit
    if ds.length > 10 then none else
    let v : Int := ds.foldl (fun a c => a * 10 + (c - 48).toNat) 0
    if v - (if neg then 1 else 0) > 2147483647 then none
    else some (if neg then -v else v)

/-- `sqlite3Atoi` -/
def atoi (z : Bytes) : Int := (getInt32 z).getD 0

def largest : Int := 2 ^ 63 - 1
def smallest : Int := -(2 ^ 63)

/-- `sqlite3Atoi64` on UTF-8: (return code, value). Code 0: an integer;
    1: extra text after it; 2: overflow; 3: exactly 2^63; -1: no digits. -/
def atoi64 (z : Bytes) : Int × Int := Id.run do
  let z := z.dropWhile isSpace
  let (neg, z) := match z with
    | 45 :: r => (true, r) | 43 :: r => (false, r) | _ => (false, z)
  let zeros := (z.takeWhile (· == 48)).length
  let r := z.drop zeros
  let ds := r.takeWhile isDigit
  let i := ds.length
  let u : Nat := ds.foldl (fun a c => a * 10 + (c - 48).toNat) 0
  let clamp := if neg then smallest else largest
  let val : Int := if u > largest.toNat then clamp else if neg then -(u : Int) else u
  let rest := r.drop i
  let rc : Int := if i == 0 && zeros == 0 then -1 else if rest.any (!isSpace ·) then 1 else 0
  if i < 19 then return (rc, val)
  if i > 19 then return (2, clamp)
  if u < 2 ^ 63 then return (rc, val)
  if u > 2 ^ 63 then return (2, clamp)
  return (if neg then rc else 3, clamp)

/-- `sqlite3DecOrHexToI64`: (return code, value written). -/
def decOrHex (z : Bytes) : Int × Int :=
  match z with
  | 48 :: x :: r =>
    if x == 120 || x == 88 then
      let r := r.dropWhile (· == 48)
      let ds := r.takeWhile isXDigit
      let u : Nat := (ds.foldl (fun a c => a * 16 + hexVal c) 0) % 2 ^ 64
      let v : Int := if u ≥ 2 ^ 63 then (u : Int) - 2 ^ 64 else u
      (if ds.length > 16 then 2 else if r.length > ds.length then 1 else 0, v)
    else dec
  | _ => dec
where
  dec : Int × Int :=
    let ok (c : UInt8) := c == 43 || c == 45 || c == 32 || c == 10 || c == 9 || isDigit c
    let n := (z.takeWhile ok).length
    atoi64 (z.take (if n < z.length then n + 1 else n))

/-- `getSafetyLevel(z, omitFull, dflt)` -/
def getSafetyLevel (z : Bytes) (omitFull : Bool) (dflt : Nat) : Nat :=
  if z.head?.map isDigit |>.getD false then (if atoi z != 0 then 1 else 0) else
  let tbl : List (String × Nat) :=
    [("on", 1), ("no", 0), ("off", 0), ("false", 0), ("yes", 1), ("true", 1), ("extra", 3), ("full", 2)]
  match tbl.find? fun (w, v) => iEq (bs w) z && (!omitFull || v ≤ 1) with
  | some (_, v) => v
  | none => dflt

/-- `sqlite3GetBoolean` -/
def getBoolean (z : Bytes) (dflt : Bool) : Bool := getSafetyLevel z true (if dflt then 1 else 0) != 0

/-! ## Compile-time options (the ccomp build, `PragmaData.compileOptions`) -/

/-- `sqlite3IsIdChar` -/
def isIdChar (c : UInt8) : Bool :=
  isDigit c || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122) || c == 95 || c == 36 || c ≥ 0x80

/-- `sqlite3_compileoption_used`: an option, without its `SQLITE_` prefix, that
    the name matches up to a non-identifier character (`=` or the end). -/
def compileOptionUsed (z : Bytes) : Bool :=
  let z := if z.length ≥ 7 && iEq (z.take 7) (bs "sqlite_") then z.drop 7 else z
  compileOptions.any fun o =>
    let o := bs o
    o.length ≥ z.length && iEq (o.take z.length) z && !((o.drop z.length).head?.map isIdChar |>.getD false)

/-- `sqlite3_compileoption_get(N)` of the 32-bit integer value of the argument. -/
def compileOptionGet (n : Int) : Option String :=
  let n := n % 2 ^ 32
  let n := if n ≥ 2 ^ 31 then n - 2 ^ 32 else n
  if n < 0 then none else compileOptions[n.toNat]?

/-! ## State -/

def pv (db : Db) (k : String) : Option Value := (db.pragmaVals.find? (·.1 == k)).map (·.2)
def pvInt (db : Db) (k : String) (dflt : Int) : Int :=
  match pv db k with | some (.int i) => i | _ => dflt
def pvStr (db : Db) (k : String) (dflt : String) : String :=
  match pv db k with | some (.text s) => String.fromUTF8! s | _ => dflt
def setPv (db : Db) (k : String) (v : Value) : Db :=
  { db with pragmaVals := (k, v) :: db.pragmaVals.filter (·.1 != k) }
def setPvInt (db : Db) (k : String) (i : Int) : Db := setPv db k (.int i)

def setCookie (db : Db) (dbk key : String) (v : Int) : Db :=
  let k := dbk ++ "." ++ key
  { db with main := { db.main with cookies := (k, v) :: db.main.cookies.filter (·.1 != k) } }

/-- Forget everything kept about a database (closed `temp`, detached). -/
def forgetDb (db : Db) (dbk : String) : Db :=
  let p := dbk ++ "."
  { db with
    pragmaVals := db.pragmaVals.filter (!·.1.startsWith p)
    main := { db.main with cookies := db.main.cookies.filter (!·.1.startsWith p) }
    tblHash := db.tblHash.filter (·.1 != dbk) }

/-- The value of a boolean flag of `db->flags` (`PragTyp_FLAG`), by pragma name. -/
def flagDefault : String → Bool
  | "automatic_index" | "short_column_names" | "trusted_schema" | "cache_spill" => true
  | _ => false

def flag (db : Db) (name : String) : Bool :=
  match name with
  | "foreign_keys" => db.pragmas.foreignKeys
  | "recursive_triggers" => db.pragmas.recursiveTriggers
  | _ => pvInt db ("flag." ++ name) (if flagDefault name then 1 else 0) != 0

def setFlag (db : Db) (name : String) (b : Bool) : Db :=
  match name with
  | "foreign_keys" => { db with pragmas := { db.pragmas with foreignKeys := b } }
  | "recursive_triggers" => { db with pragmas := { db.pragmas with recursiveTriggers := b } }
  | _ => setPvInt db ("flag." ++ name) (if b then 1 else 0)

def flagPragmas : List String :=
  ["automatic_index", "cell_size_check", "checkpoint_fullfsync", "count_changes",
   "defer_foreign_keys", "empty_result_callbacks", "foreign_keys", "full_column_names",
   "fullfsync", "ignore_check_constraints", "legacy_alter_table", "query_only",
   "read_uncommitted", "recursive_triggers", "reverse_unordered_selects",
   "short_column_names", "trusted_schema", "writable_schema"]

/-! ## Databases and their objects -/

/-- The databases in `db->aDb` order: main, temp, attached (lower-case key, name). -/
def databases (db : Db) : List (String × String) :=
  [("main", "main"), ("temp", "temp")] ++ db.attached.map fun a => (a.toLower, a)

/-- Each object with the database it belongs to (lower case). An index or
    trigger names its table only; it belongs to the table it was created on:
    an automatic index to the table it follows, a CREATE INDEX or trigger to
    the table that name found (temp, main, attached) among the tables created
    before it. -/
def objsWithDb (db : Db) : List (SchemaObj × String) := Id.run do
  let order : List String := ["temp", "main"] ++ db.attached.map fun (a : String) => a.toLower
  let mut seen : List (String × String) := []   -- (table name, db), latest first
  let mut out := #[]
  for o in db.main.objs do
    let d : String := match o with
      | .table t => t.dbName.toLower
      | .view v => (v.attachedTo.getD (if v.temp then "temp" else "main")).toLower
      | .index ix =>
        if ix.sql.isNone then ((seen.find? (nameEq ·.1 ix.table)).map (·.2)).getD "main"
        else byOrder order seen ix.table
      | .trigger tr => byOrder order seen tr.table
    if let .table t := o then seen := (t.name, d) :: seen
    out := out.push (o, d)
  return out.toList
where
  byOrder (order : List String) (seen : List (String × String)) (n : String) : String :=
    (order.find? fun d => seen.any fun (m, e) => nameEq m n && e == d).getD "main"

def tempOpen (db : Db) : Bool :=
  pvInt db "temp_open" 0 != 0 || (objsWithDb db).any (·.2 == "temp")

def tablesIn (db : Db) (dbk : String) : List Table := db.main.tables.filter (·.dbName.toLower == dbk)
def viewsIn (db : Db) (dbk : String) : List View :=
  db.main.objs.toList.filterMap fun o => match o with
    | .view v => if (v.attachedTo.getD (if v.temp then "temp" else "main")).toLower == dbk then some v else none
    | _ => none

/-- `sqlite3_strnicmp(zName, "sqlite_", 7)` names of the schema tables. -/
def masterName (dbk : String) : String := if dbk == "temp" then "sqlite_temp_master" else "sqlite_master"

/-- A table, a view, or a schema table, as `sqlite3LocateTable` finds it. -/
inductive Obj where
  | table (t : Table)
  | view (v : View)
  | master (dbk : String)
  /-- an eponymous virtual table: its module, columns, how many are visible -/
  | vtab (name : String) (cols : List String) (nVisible : Nat)

def findIn (db : Db) (dbk : String) (n : String) : Option Obj :=
  match (tablesIn db dbk).find? (nameEq ·.name n) with
  | some t => some (.table t)
  | none => match (viewsIn db dbk).find? (nameEq ·.name n) with
    | some v => some (.view v)
    | none => if nameEq n (masterName dbk) then some (.master dbk) else none

/-- The eponymous virtual tables of json.c (columns; `json` and `root` hidden). -/
def jsonVtab (n : String) : Option Obj :=
  if ["json_each", "json_tree", "jsonb_each", "jsonb_tree"].contains n.toLower then
    some (.vtab n.toLower ["key", "value", "type", "atom", "id", "parent", "fullkey", "path", "json", "root"] 8)
  else none

/-- `sqlite3LocateTable`: temp before main, then the attached databases; the
    names `sqlite_schema`/`sqlite_temp_schema` are the legacy ones. Eponymous
    virtual tables are found by `locateAny`. -/
def locate (db : Db) (n : String) (zDb : Option String) : Option Obj :=
  let n := if nameEq n "sqlite_schema" then "sqlite_master"
    else if nameEq n "sqlite_temp_schema" then "sqlite_temp_master" else n
  let order := match zDb with
    | some d => [d.toLower]
    | none => ["temp", "main"] ++ db.attached.map fun (a : String) => a.toLower
  order.findSome? fun d => findIn db d n

/-! ## Indexes as SQLite builds them -/

/-- One column of an index: column number (-1 rowid, -2 expression),
    DESC, collation name as written. -/
structure IdxCol where
  cid : Int
  desc : Bool
  coll : String
  deriving Inhabited

structure IdxInfo where
  name : String
  keys : Array IdxCol
  /-- the columns after the key (`index_xinfo` rows with key = 0) -/
  rest : Array IdxCol
  unique : Bool
  /-- "c", "u" or "pk" -/
  origin : String
  partial_ : Bool
  replace : Bool
  deriving Inhabited

/-- The CREATE TABLE statement of a table, parsed again (default texts,
    collation names and DESC as written). -/
def reparse (t : Table) : Option (List ColumnDef × List (Option Name × TableConstraint)) :=
  match parseNext t.sql.toUTF8 0 with
  | .ok (.createTable _ _ _ _ cols cons _ _ _ _ _) _ => some (cols, cons)
  | _ => none

def collName : Coll → String
  | .binary => "BINARY" | .nocase => "NOCASE" | .rtrim => "RTRIM"

/-- The declared collation of each column, as written. -/
def colColls (t : Table) (cds : Option (List ColumnDef)) : Array String :=
  t.cols.map fun c =>
    let written := cds.bind fun l => (l.find? (nameEq ·.name c.name)).bind fun cd =>
      cd.constraints.findSome? fun | (_, .collate n) => some n | _ => none
    match written with
    | some n => n
    | none => if c.coll == .binary then "BINARY" else collName c.coll

def isIntegerType (t : String) : Bool := t.trimAscii.toString.toUpper == "INTEGER"

/-- The automatic indexes of a table, in creation order (`sqlite3CreateIndex`
    called by the PRIMARY KEY and UNIQUE constraints, with equivalent ones
    merged; an INTEGER PRIMARY KEY of a WITHOUT ROWID table is indexed last). -/
def autoIndexes (t : Table) : Array IdxInfo := Id.run do
  let parsed := reparse t
  let colls := colColls t (parsed.map (·.1))
  let colIdx (n : Name) : Option Nat := t.cols.toList.findIdx? (nameEq ·.name n)
  -- candidates: (columns, isPk, onConflict replace)
  let mut cands : Array (Array IdxCol × Bool × Bool) := #[]
  let mut deferredPk : Option (Array IdxCol × Bool × Bool) := none
  match parsed with
  | some (cds, cons) =>
    for cd in cds do
      let some i := colIdx cd.name | continue
      for (_, k) in cd.constraints do
        match k with
        | .primaryKey dir oc _ =>
          let c : IdxCol := ⟨i, dir == some .desc, colls[i]!⟩
          if isIntegerType cd.type && dir != some .desc then
            if t.withoutRowid then deferredPk := some (#[c], true, oc == some .replace)
          else cands := cands.push (#[c], true, oc == some .replace)
        | .unique oc => cands := cands.push (#[⟨i, false, colls[i]!⟩], false, oc == some .replace)
        | _ => pure ()
    for (_, k) in cons do
      let mk (l : List (Name × Option Name × SortDir)) : Array IdxCol :=
        (l.filterMap fun (n, c, d) => (colIdx n).map fun (i : Nat) => (⟨(i : Int), d == .desc, c.getD colls[i]!⟩ : IdxCol)).toArray
      match k with
      | .primaryKey l oc _ =>
        let cs := mk l
        let ipk := cs.size == 1 && !cs[0]!.desc && isIntegerType (t.cols[cs[0]!.cid.toNat]!).type
        if ipk then
          if t.withoutRowid then deferredPk := some (cs, true, oc == some .replace)
        else cands := cands.push (cs, true, oc == some .replace)
      | .unique l oc => cands := cands.push (mk l, false, oc == some .replace)
      | _ => pure ()
  | none =>
    for u in t.uniques do
      cands := cands.push ((u.cols.map fun (i, c) => (⟨i, false, collName c⟩ : IdxCol)).toArray, u.isPk,
        u.onConflict == some .replace)
  if let some d := deferredPk then cands := cands.push d
  -- merge equivalent constraints; number the survivors
  let mut out : Array (Array IdxCol × Bool × Bool) := #[]
  for (cs, pk, rep) in cands do
    match out.findIdx? fun (o, _, _) => o.size == cs.size &&
        (o.zip cs).all fun (a, b) => a.cid == b.cid && iEq (bs a.coll) (bs b.coll) with
    | some j =>
      let (o, opk, orep) := out[j]!
      out := out.set! j (o, opk || pk, orep || rep)
    | none => out := out.push (cs, pk, rep)
  let pkCols : Array IdxCol := match out.find? (·.2.1) with | some (cs, _, _) => cs | none => #[]
  return out.mapIdx fun i (cs, pk, rep) =>
    let rest : Array IdxCol :=
      if !t.withoutRowid then #[⟨-1, false, "BINARY"⟩]
      else if pk then
        ((List.range t.cols.size).filter fun (j : Nat) => !cs.any (·.cid == (j : Int)) &&
          !(match t.cols[j]!.generated with | some (_, stored) => !stored | none => false)).toArray.map
          fun (j : Nat) => (⟨(j : Int), false, "BINARY"⟩ : IdxCol)
      else pkCols.filter fun p => !cs.any fun c => c.cid == p.cid && iEq (bs c.coll) (bs p.coll)
    { name := s!"sqlite_autoindex_{t.name}_{i + 1}", keys := cs, rest, unique := true,
      origin := if pk then "pk" else "u", partial_ := false, replace := rep }

/-- The explicit indexes (CREATE INDEX) on a table, in creation order. -/
def explicitIndexes (db : Db) (t : Table) : Array IdxInfo := Id.run do
  let colls := colColls t ((reparse t).map (·.1))
  let pkCols : Array IdxCol := match (autoIndexes t).find? (·.origin == "pk") with
    | some i => i.keys | none => #[]
  let mut out := #[]
  for (o, d) in objsWithDb db do
    let .index ix := o | continue
    if ix.sql.isNone || !nameEq ix.table t.name || d != t.dbName.toLower then continue
    let keys : Array IdxCol := (ix.cols.map fun (.mk e dir _) =>
      let (e, coll) := match e with | .collate e c => (e, some c) | e => (e, none)
      let cid : Option Nat := match e with
        | .col _ _ c | .dqcol c => t.cols.toList.findIdx? (nameEq ·.name c)
        | _ => none
      let coll := coll.getD (match cid with | some i => colls[i]! | none => "BINARY")
      (⟨(cid.map Int.ofNat).getD (-2), dir == .desc, coll⟩ : IdxCol)).toArray
    let rest := if !t.withoutRowid then #[(⟨-1, false, "BINARY"⟩ : IdxCol)]
      else pkCols.filter fun p => !keys.any fun c => c.cid == p.cid && iEq (bs c.coll) (bs p.coll)
    out := out.push { name := ix.name, keys, rest, unique := ix.unique, origin := "c",
                      partial_ := ix.where_.isSome, replace := false }
  return out

/-- `pTab->pIndex`: each new index is put first, then REPLACE indexes are
    moved after all the others. -/
def indexList (db : Db) (t : Table) : Array IdxInfo :=
  let all := (autoIndexes t ++ explicitIndexes db t).reverse
  all.filter (!·.replace) ++ all.filter (·.replace)

/-- The number of b-trees of a database. -/
def btrees (db : Db) (dbk : String) : Nat :=
  (tablesIn db dbk).foldl (fun n t =>
    let autos := t.uniques.foldl (fun (l : List (List (Nat × Coll))) u =>
      if l.any (· == u.cols) then l else l ++ [u.cols]) []
    let wrPk := if t.withoutRowid && !t.uniques.any (·.isPk) then 1 else 0
    n + (if t.withoutRowid then 0 else 1) + autos.length + wrPk) 0
  + ((objsWithDb db).filter fun (o, d) => match o with
      | .index ix => ix.sql.isSome && d == dbk
      | _ => false).length

/-! ## The table hash (hash.c) -/

def strHash (s : String) : UInt32 :=
  s.toUTF8.foldl (fun h c => (h + (0xdf &&& c).toUInt32) * 0x9e3779b1) 0

def bucket (h : TblHash) (k : String) : Nat := (strHash k).toNat % h.htsize

/-- `insertElement`: before the first element of its bucket, else first. -/
def insertElem (h : TblHash) (k : String) : TblHash :=
  if h.htsize == 0 then { h with keys := k :: h.keys } else
  let b := bucket h k
  match h.keys.findIdx? (bucket h · == b) with
  | some j => { h with keys := h.keys.take j ++ [k] ++ h.keys.drop j }
  | none => { h with keys := k :: h.keys }

/-- `sqlite3HashInsert` of a new key (`rehash` to `count*3` buckets, at most
    `SQLITE_MALLOC_SOFT_LIMIT/sizeof(struct _ht)` = 64). -/
def hashInsert (h : TblHash) (k : String) : TblHash :=
  let count := h.keys.length + 1
  let h :=
    if count ≥ 5 && count > 2 * h.htsize then
      let n := min (count * 3) 64
      if n == h.htsize then h else h.keys.foldl insertElem { keys := [], htsize := n }
    else h
  insertElem h k

def hashRemove (h : TblHash) (k : String) : TblHash :=
  let keys := h.keys.filter (!nameEq · k)
  if keys.isEmpty then {} else { h with keys }

/-- The table and view names of a database, in `sqlite_schema` order. -/
def tableNames (db : Db) (dbk : String) : List String :=
  db.main.objs.toList.filterMap fun o => match o with
    | .table t => if t.dbName.toLower == dbk then some t.name else none
    | .view v => if (v.attachedTo.getD (if v.temp then "temp" else "main")).toLower == dbk then some v.name else none
    | _ => none

/-- The hash as a fresh schema load builds it. -/
def freshHash (db : Db) (dbk : String) : TblHash :=
  (tableNames db dbk).foldl hashInsert (hashInsert {} (masterName dbk))

def hashOf (db : Db) (dbk : String) : TblHash :=
  ((db.tblHash.find? (·.1 == dbk)).map (·.2)).getD (freshHash db dbk)

def setHash (db : Db) (dbk : String) (h : Option TblHash) : Db :=
  { db with tblHash := (match h with | some h => [(dbk, h)] | none => []) ++ db.tblHash.filter (·.1 != dbk) }

/-! ## Pages -/

def pages (db : Db) (dbk : String) : Int := db.cookie dbk "$pages"
def freePages (db : Db) (dbk : String) : Int := db.cookie dbk "$free"
def autoVacuum (db : Db) (dbk : String) : Int := pvInt db (dbk ++ ".auto_vacuum") 0

/-- A write transaction on the database: page 1 exists. -/
def markWritten (db : Db) (dbk : String) : Db :=
  if pages db dbk ≥ 1 then db else setCookie db dbk "$pages" 1

/-- Allocate (`k > 0`) or free (`k < 0`) b-tree root pages. -/
def adjustPages (db : Db) (dbk : String) (k : Int) : Db := Id.run do
  let mut db := markWritten db dbk
  let av := autoVacuum db dbk
  let mut p := pages db dbk
  let mut f := freePages db dbk
  if k > 0 then
    if av != 0 && p == 1 then p := 2   -- the pointer-map page
    let reuse := min f k
    f := f - reuse; p := p + (k - reuse)
  else if k < 0 then
    if av == 1 then p := p + k else f := f - k
  db := setCookie db dbk "$pages" p
  return setCookie db dbk "$free" f

def pageSizes : List Int := [512, 1024, 2048, 4096, 8192, 16384, 32768, 65536]

/-- Open the temp database (`sqlite3OpenTempDatabase`), whose page size is
    the last one requested by `PRAGMA page_size` (`db->nextPagesize`). -/
def openTemp (db : Db) : Db :=
  if pvInt db "temp_open" 0 != 0 then db else
  let db := setPvInt db "temp_open" 1
  let n := pvInt db "next_page_size" 0
  if pageSizes.contains n then setPvInt db "temp.page_size" n else db

/-! ## Statement hook (schema cookie, pages, table hash) -/

/-- What identifies a database's schema (not its contents). -/
def signature (db : Db) (dbk : String) : List String :=
  (objsWithDb db).filterMap fun (o, d) =>
    if d != dbk then none else some (match o with
      | .table t => "t" ++ t.name ++ "\x00" ++ t.sql ++ "\x00" ++ toString t.cols.size
      | .index i => "i" ++ i.name ++ "\x00" ++ (i.sql.getD "")
      | .view v => "v" ++ v.name ++ "\x00" ++ v.sql
      | .trigger t => "g" ++ t.name ++ "\x00" ++ t.sql)

def schemaCookies (db : Db) : List (String × Int) :=
  db.main.cookies.filter (·.1.endsWith ".schema_version")

/-- The executor's hook, after statement `s` ran successfully and turned
    `before` into `after`. A statement that changes the schema of a database
    bumps its schema cookie once, allocates or frees root pages, and updates
    the table hash (ALTER TABLE and VACUUM reload the schema, which rebuilds
    the hash). ROLLBACK of a transaction that changed the schema reloads all
    schemas. DETACH forgets the database. -/
def afterStmt (before after : Db) (s : Stmt) : Db := Id.run do
  let mut db := after
  -- the text encoding is fixed once a schema row has been read (`sqlite3InitCallback`)
  if !after.main.objs.isEmpty then db := setPvInt db "enc_fixed" 1
  -- detached databases
  for (k, _) in databases before do
    if !(databases after).any (·.1 == k) then db := forgetDb db k
  match s with
  | .pragma .. | .attach .. | .detach .. => return db
  | .rollback _ =>
    if schemaCookies before != schemaCookies after then db := { db with tblHash := [] }
    return db
  | .vacuum sch none =>
    let dbk := (sch.getD "main").toLower
    db := setCookie db dbk "schema_version" (db.cookie dbk "schema_version" + 1)
    let av := pvInt db "next_auto_vacuum" (-1)
    if av ≥ 0 then db := setPvInt db (dbk ++ ".auto_vacuum") av
    let n := btrees db dbk
    db := setCookie db dbk "$pages" (1 + n + (if autoVacuum db dbk != 0 && n > 0 then 1 else 0))
    db := setCookie db dbk "$free" 0
    return setHash db dbk none
  | _ => pure ()
  let reload := match s with
    | .alterRename .. | .alterRenameColumn .. | .alterAddColumn .. | .alterDropColumn .. => true
    | _ => false
  for (dbk, _) in databases after do
    if signature before dbk == signature after dbk then continue
    db := setCookie db dbk "schema_version" (db.cookie dbk "schema_version" + 1)
    db := adjustPages db dbk ((btrees after dbk : Int) - btrees before dbk)
    if dbk == "temp" then db := openTemp db
    if reload then db := setHash db dbk none
    else
      let old := tableNames before dbk
      let new := tableNames after dbk
      let h0 := hashOf before dbk
      let h1 := old.foldl (fun h n => if new.any (nameEq · n) then h else hashRemove h n) h0
      -- sqlite_sequence is parsed (nested) before the AUTOINCREMENT table that creates it
      let added := new.filter fun n => !old.any (nameEq · n)
      let added := added.filter (nameEq · "sqlite_sequence") ++ added.filter (!nameEq · "sqlite_sequence")
      let h2 := added.foldl hashInsert h1
      db := setHash db dbk (some h2)
  return db

/-! ## Flags the executor consults -/

def SQLITE_READONLY : Nat := 8

/-- Statements that open a write transaction (refused under `query_only`):
    DML always, DDL when it changes the schema (not `IF [NOT] EXISTS` no-ops). -/
def writes (before after : Db) : Stmt → Bool
  | .insert .. | .update .. | .delete .. => true
  | .createTable .. | .createIndex .. | .createView .. | .createTrigger .. | .drop ..
  | .alterRename .. | .alterRenameColumn .. | .alterAddColumn .. | .alterDropColumn ..
  | .createVirtualTable .. => (databases after).any fun (k, _) => signature before k != signature after k
  | _ => false

/-- DML whose result under `count_changes` is the number of changed rows. -/
def countsChanges : Stmt → Bool
  | .insert _ _ _ _ _ _ _ _ ret => ret.isEmpty
  | .update _ _ _ _ _ _ _ _ ret _ _ _ => ret.isEmpty
  | .delete _ _ _ _ _ ret _ _ _ => ret.isEmpty
  | _ => false

/-! ## Result helpers -/

abbrev Rows := Array (Array Value)
abbrev Res := Except Err (Db × Rows)

def txt (s : String) : Value := .ofString s
def int (i : Int) : Value := .int i
def one (v : Value) : Rows := #[#[v]]
def fail {α} (msg : String) : Except Err α := throw { code := SQLITE_ERROR, msg }
def readonly {α} : Except Err α := throw { code := SQLITE_READONLY, msg := "attempt to write a readonly database" }

/-- The text of an argument as `zRight` (NULL: no argument). -/
def argBytes : Value → Option Bytes
  | .null => none
  | .blob b => some b.toList
  | v => (v.toText?).map (·.toList)

/-! ## Per-database settings -/

def cacheSize (db : Db) (dbk : String) : Int := pvInt db (dbk ++ ".cache_size") (-2000)
def pageSize (db : Db) (dbk : String) : Int := pvInt db (dbk ++ ".page_size") 4096

/-- `numberOfCachePages`: `szPage + szExtra` is the page size plus 136 bytes
    (`sizeof(MemPage)` on x86-64, the same in both builds). -/
def cachePages (db : Db) (dbk : String) : Int :=
  let c := cacheSize db dbk
  if c ≥ 0 then c else (-1024 * c) / (pageSize db dbk + 136)

def journalDefault (db : Db) (dbk : String) : String :=
  if dbk == "temp" then (if pvInt db "temp_store" 0 == 2 then "memory" else "delete") else "memory"

def journalMode (db : Db) (dbk : String) : String := pvStr db (dbk ++ ".journal_mode") (journalDefault db dbk)

def valEq : Value → Value → Bool
  | .null, .null => true
  | .int a, .int b => a == b
  | .real a, .real b => a.toBits == b.toBits
  | .text a, .text b | .blob a, .blob b => a.data == b.data
  | _, _ => false

/-- The database has been written in the open transaction (its pager is past
    the reader state): its contents, schema or header differ from the state at
    BEGIN. -/
def dirty (db : Db) (dbk : String) : Bool :=
  db.inTxn && match db.savepoints.getLast? with
    | none => false
    | some (_, snap) =>
      let old : Db := { db with main := snap }
      let p := dbk ++ "."
      old.main.cookies.filter (·.1.startsWith p) != db.main.cookies.filter (·.1.startsWith p) ||
      signature old dbk != signature db dbk ||
      (tablesIn db dbk).any fun t => match (tablesIn old dbk).find? (nameEq ·.name t.name) with
        | none => true
        | some u => u.rows.size != t.rows.size || (u.rows.zip t.rows).any fun (a, b) =>
            a.rowid != b.rowid || a.vals.size != b.vals.size || (a.vals.zip b.vals).any fun (x, y) => !valEq x y

/-- `sqlite3PagerSetJournalMode` and `OP_JournalMode` for in-memory databases
    (only MEMORY and OFF) and the temp database (not WAL); no change once the
    database has been written in the open transaction
    (`sqlite3PagerOkToChangeJournalMode`). -/
def setJournal (db : Db) (dbk : String) (mode : String) : Db :=
  let memdb := journalDefault db dbk == "memory"
  let ok := if memdb then mode == "memory" || mode == "off" else mode != "wal"
  if ok && !dirty db dbk then setPv db (dbk ++ ".journal_mode") (txt mode) else db

/-! ## View columns -/

/-- Name and affinity of each result column of a view (`none`: the view's
    SELECT fails), supplied by the evaluator. -/
abbrev ViewCols := View → Except Err (Array (Name × Option Aff))

def stdType : Aff → String
  | .numeric => "NUM" | .blob => "BLOB" | .integer => "INT" | .real => "REAL" | .text => "TEXT"

/-- The declared types of a view's columns (`sqlite3SubqueryColumnTypes`): the
    declared type of a column the expression names, when its affinity is the
    column's; otherwise the standard type of the affinity. -/
partial def viewColumns (db : Db) (vc : ViewCols) (v : View) : Except Err (Array (Name × String)) :=
  match vc v with
  | .error e => .error e
  | .ok cols => .ok <|
    let srcCols : Array (Option String) := match v.q with
      | .mk _ _ (.select _ rcs from_ ..) _ _ _ _ =>
        let tabs : List (Name × Table) := match from_ with
          | some f => tablesOfFrom f
          | none => []
        (rcs.flatMap fun rc => match rc with
          | .star => tabs.flatMap fun (_, t) => (t.cols.toList.filter (·.generated.isNone)).map fun c => some c.type
          | .tableStar a => (tabs.filter (nameEq ·.1 a)).flatMap fun (_, t) => t.cols.toList.map fun c => some c.type
          | .expr e _ _ => [declOf tabs e]).toArray
      | _ => #[]
    -- the later arms of a compound SELECT: the possible datatypes of each column
    let arms : List (List Expr × List (Name × Table)) := match v.q with
      | .mk _ _ first rest _ _ _ =>
        let later := match first with
          | .values (_ :: rows) => rows.map fun r => (r, [])
          | _ => []
        later ++ rest.flatMap fun (_, core) => match core with
          | .select _ rcs from_ .. =>
            [(rcs.filterMap fun | .expr e _ _ => some e | _ => none, match from_ with
                | some f => tablesOfFrom f | none => [])]
          | .values rows => rows.map fun r => (r, [])
    let firstCast : Array Bool := match v.q with
      | .mk _ _ (.select _ rcs ..) _ _ _ _ =>
        (rcs.map fun | .expr (.cast ..) _ _ => true | _ => false).toArray
      | _ => #[]
    let names := if v.cols.isEmpty then cols.map (·.1) else v.cols.toArray
    (cols.zip names).mapIdx fun i ((_, aff), nm) =>
      let compound := !arms.isEmpty
      let m := arms.foldl (fun m (es, tabs) => m ||| (match es[i]? with | some e => dataType tabs e | none => 0)) 0
      let aff := match aff with
        | some .text => if compound && m &&& 1 != 0 then some .blob else aff
        | some .blob => aff
        | some a => if compound && m &&& 2 != 0 then some .blob else some a
        | none => none
      let flex := compound && firstCast[i]?.getD false &&
        (match aff with | some .numeric | some .integer | some .real => true | _ => false)
      let ty := match aff with
        | none => ""
        | some a => if flex then "NUM" else match srcCols[i]?.getD none with
          | some d => if !d.isEmpty && affinityOfType d == a then d else stdType a
          | none => stdType a
      (nm, ty)
where
  /-- `sqlite3ExprDataType`: 1 numeric, 2 text, 4 blob. -/
  dataType (tabs : List (Name × Table)) : Expr → Nat
    | .collate e _ | .unop .pos e => dataType tabs e
    | .lit .null => 0
    | .lit (.text _) => 2
    | .lit (.blob _) => 4
    | .binop .concat .. => 6
    | .param .. | .call .. => 7
    | e@(.col ..) | e@(.subquery _) | e@(.cast ..) =>
      let aff := match e with
        | .cast _ ty => some (affinityOfType ty)
        | .col .. => (declOf tabs e).map affinityOfType
        | _ => none
      match aff with
      | some .text => 6
      | some .blob | none => 7
      | _ => 5
    | .case_ _ whens els =>
      whens.foldl (fun m (_, r) => m ||| dataType tabs r) (match els with | some e => dataType tabs e | none => 0)
    | _ => 1
  tablesOfFrom : FromItem → List (Name × Table)
    | .table sch n alias _ =>
      let t := match sch with
        | some s => db.main.findTableDb s n
        | none => db.main.findTable n db.attached
      match t with | some t => [(alias.getD n, t)] | none => []
    | .join l _ _ r _ _ => tablesOfFrom l ++ tablesOfFrom r
    | _ => []
  declOf (tabs : List (Name × Table)) : Expr → Option String
    | .col _ (some a) c => (tabs.find? (nameEq ·.1 a)).bind fun (_, t) => (t.cols.find? (nameEq ·.name c)).map (·.type)
    | .col _ none c => tabs.findSome? fun (_, t) => (t.cols.find? (nameEq ·.name c)).map (·.type)
    | _ => none

def masterCols : Array (Name × String) :=
  #[("type", "TEXT"), ("name", "TEXT"), ("tbl_name", "TEXT"), ("rootpage", "INT"), ("sql", "TEXT")]

/-! ## Result-set pragmas -/

/-- The default value's text (`sqlite3AddDefaultValue`: the span after
    DEFAULT, without the parentheses of `DEFAULT (expr)`). -/
def dfltText (cd : ColumnDef) : Option String :=
  cd.constraints.findSome? fun
    | (_, .default_ _ s) =>
      let s := s.trimAscii.toString
      some (if s.startsWith "(" && s.endsWith ")" then ((s.drop 1).dropEnd 1).trimAscii.toString else s)
    | _ => none

def tableInfo (db : Db) (vc : ViewCols) (o : Obj) (xinfo : Bool) : Except Err Rows := do
  match o with
  | .master _ =>
    return masterCols.mapIdx fun i (n, ty) =>
      #[int i, txt n, txt ty, int 0, .null, int 0] ++ (if xinfo then #[int 0] else #[])
  | .view v =>
    return (← viewColumns db vc v).mapIdx fun i (n, ty) =>
      #[int i, txt n, txt ty, int 0, .null, int 0] ++ (if xinfo then #[int 0] else #[])
  | .vtab _ cols nVisible =>
    let cols := if xinfo then cols else cols.take nVisible
    return cols.toArray.mapIdx fun i n =>
      #[int i, txt n, txt "", int 0, .null, int 0] ++ (if xinfo then #[int (if i < nVisible then 0 else 1)] else #[])
  | .table t =>
    let cds := (reparse t).map (·.1)
    let mut out := #[]
    let mut nHidden := 0
    for h : i in [0:t.cols.size] do
      let c := t.cols[i]
      let hidden : Nat := match c.generated with
        | some (_, stored) => if stored then 3 else 2
        | none => 0
      if hidden != 0 && !xinfo then nHidden := nHidden + 1; continue
      let pk : Int := match t.pk.findIdx? (· == i) with | some k => k + 1 | none => 0
      let dflt : Value := if hidden ≥ 2 then .null else
        match (cds.bind fun l => l.find? (nameEq ·.name c.name)).bind dfltText with
        | some s => txt s
        | none => .null
      out := out.push (#[int (i - nHidden), txt c.name, txt c.type, int (if c.notNull then 1 else 0), dflt, int pk]
        ++ (if xinfo then #[int hidden] else #[]))
    return out

def indexRows (t : Table) (ix : IdxInfo) (xinfo : Bool) : Rows :=
  let cname (c : IdxCol) : Value := if c.cid < 0 then .null else txt (t.cols[c.cid.toNat]!).name
  let keys := ix.keys.mapIdx fun i c =>
    #[int i, int c.cid, cname c] ++ (if xinfo then #[int (if c.desc then 1 else 0), txt c.coll, int 1] else #[])
  if !xinfo then keys else
  keys ++ ix.rest.mapIdx fun i c =>
    #[int (ix.keys.size + i), int c.cid, cname c, int (if c.desc then 1 else 0), txt c.coll, int 0]

/-- `sqlite3FindIndex`: temp first, then main and the attached databases. -/
def findIndex (db : Db) (n : String) (zDb : Option String) : Option (Table × IdxInfo) :=
  let order := match zDb with
    | some d => [d.toLower]
    | none => ["temp", "main"] ++ db.attached.map fun (a : String) => a.toLower
  order.findSome? fun d =>
    (tablesIn db d).findSome? fun t => ((indexList db t).find? (nameEq ·.name n)).map (t, ·)

def actionName (s : String) : String :=
  match s.toUpper with
  | "SET NULL" => "SET NULL" | "SET DEFAULT" => "SET DEFAULT" | "CASCADE" => "CASCADE"
  | "RESTRICT" => "RESTRICT" | _ => "NO ACTION"

def fkList (t : Table) : Rows := Id.run do
  let mut out := #[]
  for (fk, id) in t.fks.reverse.zipIdx do
    for (c, j) in fk.cols.zipIdx do
      out := out.push #[int id, int j, txt fk.parent, txt (t.cols[c]!).name,
        (match fk.parentCols[j]? with | some p => txt p | none => .null),
        txt (actionName fk.onUpdate), txt (actionName fk.onDelete), txt "NONE"]
  return out

/-- How a foreign key finds its parent row (`sqlite3FkLocateIndex`): by rowid,
    or through a UNIQUE index, with the child column for each index column. -/
inductive FkLookup where
  | rowid (childCol : Nat)
  | index (ix : IdxInfo) (childCols : Array Nat)

def fkLocate (db : Db) (child parent : Table) (fk : ForeignKey) : Except Err FkLookup := do
  let mismatch : Except Err FkLookup :=
    fail s!"foreign key mismatch - \"{child.name}\" referencing \"{parent.name}\""
  let nCol := fk.cols.length
  let zKey := fk.parentCols.head?
  if nCol == 1 then
    if let some ipk := parent.rowidCol then
      match zKey with
      | none => return .rowid fk.cols[0]!
      | some k => if nameEq (parent.cols[ipk]!).name k then return .rowid fk.cols[0]!
  let colls := colColls parent ((reparse parent).map (·.1))
  for ix in indexList db parent do
    if ix.keys.size != nCol || !ix.unique || ix.partial_ then continue
    match zKey with
    | none => if ix.origin == "pk" then return .index ix fk.cols.toArray
    | some _ =>
      let mut aiCol : Array Nat := #[]
      let mut ok := true
      for c in ix.keys do
        if c.cid < 0 then ok := false; break
        let pc := parent.cols[c.cid.toNat]!
        if !iEq (bs c.coll) (bs colls[c.cid.toNat]!) then ok := false; break
        match fk.parentCols.findIdx? (nameEq · pc.name) with
        | some j => aiCol := aiCol.push fk.cols[j]!
        | none => ok := false; break
      if ok then return .index ix aiCol
  mismatch

/-- Rows in the order of the table's b-tree: rowid, or the PRIMARY KEY of a
    WITHOUT ROWID table. -/
def btreeOrder (t : Table) : Array Row :=
  if !t.withoutRowid then t.rows.qsort (·.rowid < ·.rowid) else
  let pk := (autoIndexes t).find? (·.origin == "pk")
  match pk with
  | none => t.rows
  | some ix => t.rows.qsort fun a b =>
    let rec go : List IdxCol → Bool
      | [] => false
      | c :: cs =>
        let i := c.cid.toNat
        let coll := (collOfName c.coll).getD .binary
        match compareValues coll (a.vals[i]?.getD .null) (b.vals[i]?.getD .null) with
        | .lt => !c.desc | .gt => c.desc | .eq => go cs
    go ix.keys.toList

def fkCheckTable (db : Db) (t : Table) : Except Err Rows := do
  let dbk := t.dbName.toLower
  let fks := t.fks.reverse
  -- locate every parent key first (errors stop the whole pragma)
  let mut lookups : Array (ForeignKey × Option (Table × FkLookup)) := #[]
  for fk in fks do
    match (tablesIn db dbk).find? (nameEq ·.name fk.parent) with
    | none => lookups := lookups.push (fk, none)
    | some p => lookups := lookups.push (fk, some (p, ← fkLocate db t p fk))
  let mut out := #[]
  for r in btreeOrder t do
    for ((fk, lk), i) in lookups.zipIdx do
      let cols : List Nat := match lk with
        | some (_, .index _ cc) => cc.toList
        | _ => fk.cols
      let vals := cols.map fun c => r.vals[c]?.getD .null
      if vals.any (·.isNull) then continue
      let found := match lk with
        | none => false
        | some (p, .rowid _) =>
          match applyAffinity .numeric vals[0]! with
          | .int k => p.rows.any (·.rowid == k)
          | _ => false
        | some (p, .index ix _) =>
          let key := (ix.keys.toList.zip vals).map fun (c, v) =>
            (applyAffinity (p.cols[c.cid.toNat]!).aff v, c)
          p.rows.any fun pr => key.all fun (v, c) =>
            compareValues ((collOfName c.coll).getD .binary) (pr.vals[c.cid.toNat]?.getD .null) v == .eq
      if !found then
        out := out.push #[txt t.name, (if t.withoutRowid then .null else int r.rowid), txt fk.parent, int i]
  return out

/-! ## The pragmas -/

def journalModes : List String := ["delete", "persist", "off", "truncate", "memory", "wal"]

/-- Close the temp database (`invalidateTempStorage`): its objects go, all
    schemas are reloaded. -/
def closeTemp (db : Db) : Db :=
  let keep := ((objsWithDb db).filter (·.2 != "temp")).map (·.1)
  let db := { db with main := { db.main with objs := keep.toArray } }
  { forgetDb (setPvInt db "temp_open" 0) "temp" with tblHash := [] }

/-- PRAGMA statements whose output does not depend on a database argument. -/
def pragmaNames : List String := pragmaList.toList

/-- The flags of the pragmas that are eponymous virtual tables: (has an
    argument column, has a schema column, result column names). -/
def vtabShape (name : String) : Option (Bool × Bool × List String) :=
  let r1 := ["foreign_key_check", "foreign_key_list", "index_info", "index_list", "index_xinfo",
    "integrity_check", "optimize", "quick_check", "table_info", "table_list", "table_xinfo"]
  let schemaOpt := ["foreign_key_check", "foreign_key_list", "index_info", "index_list", "index_xinfo",
    "integrity_check", "quick_check", "table_info", "table_xinfo"]
  let schemaReq := ["auto_vacuum", "cache_size", "cache_spill", "default_cache_size", "journal_mode",
    "journal_size_limit", "locking_mode", "max_page_count", "page_count", "page_size", "synchronous"]
  let noResult0 := ["case_sensitive_like", "incremental_vacuum", "lock_proxy_file", "mmap_size",
    "shrink_memory", "temp_store_directory", "wal_autocheckpoint", "wal_checkpoint", "optimize"]
  let cols : List String := match name with
    | "foreign_key_list" => ["id", "seq", "table", "from", "to", "on_update", "on_delete", "match"]
    | "table_info" => ["cid", "name", "type", "notnull", "dflt_value", "pk"]
    | "table_xinfo" => ["cid", "name", "type", "notnull", "dflt_value", "pk", "hidden"]
    | "function_list" => ["name", "builtin", "type", "enc", "narg", "flags"]
    | "table_list" => ["schema", "name", "type", "ncol", "wr", "strict"]
    | "index_xinfo" => ["seqno", "cid", "name", "desc", "coll", "key"]
    | "index_info" => ["seqno", "cid", "name"]
    | "index_list" => ["seq", "name", "unique", "origin", "partial"]
    | "foreign_key_check" => ["table", "rowid", "parent", "fkid"]
    | "database_list" => ["seq", "name", "file"]
    | "collation_list" => ["seq", "name"]
    | "default_cache_size" => ["cache_size"]
    | "busy_timeout" => ["timeout"]
    | "module_list" | "pragma_list" => ["name"]
    | "wal_checkpoint" => ["busy", "log", "checkpointed"]
    | n => [n]
  if !pragmaNames.contains name then none
  else if noResult0.contains name && !r1.contains name then none
  else some (r1.contains name, schemaOpt.contains name || schemaReq.contains name, cols)

/-- Register an eponymous virtual table module (`pragma module_list`). -/
def registerModule (db : Db) (m : String) : Db :=
  let mods := (pvStr db "modules" "").splitOn "\x00" |>.filter (!·.isEmpty)
  if mods.any (nameEq · m) then db else setPv db "modules" (txt ("\x00".intercalate (mods ++ [m.toLower])))

/-- `PRAGMA [schema.]name [= arg | (arg)]` on database state `db`. `arg` is
    the argument as `sqlite3Pragma` sees it: the token's text (with its sign
    for a negative number; a bare identifier or keyword is its name), except
    that a string literal arrives as a BLOB of its dequoted bytes (the raw
    token is what `integrity_check` reads). `vc` gives the columns of views.
    Returns the new state and the result rows, or an error. -/
def runWith (vc : ViewCols) (db0 : Db) (schema : Option String) (name : String) (arg : Option Value) :
    Except Err (Db × Rows) := do
  let name := name.toLower
  let z : Option Bytes := arg.bind argBytes
  let quoted := match arg with | some (.blob _) => true | _ => false
  -- the schema: `sqlite3TwoPartName`
  let (dbk, _) ← match schema with
    | none => pure ("main", "main")
    | some s => match (databases db0).find? (nameEq ·.2 s) with
      | some d => pure d
      | none => fail s!"unknown database {s}"
  let explicit := schema.isSome
  -- naming temp opens it
  let db := if dbk == "temp" then openTemp db0 else db0
  let some _ := pragmaNames.find? (· == name) | return (db, #[])
  let zDb : Option String := if explicit then some dbk else none
  let zStr := z.map str
  if flagPragmas.contains name then
    match z with
    | none => return (db, one (int (if flag db name then 1 else 0)))
    | some z =>
      if name == "foreign_keys" && db.inTxn then return (db, #[])
      let b := getBoolean z false
      let db := setFlag db name b
      if name == "writable_schema" && !b && iEq z (bs "reset") then return ({ db with tblHash := [] }, #[])
      return (db, #[])
  match name with
  -- header cookies
  | "application_id" | "user_version" | "schema_version" =>
    match z with
    | none => return (db, one (int (db.cookie dbk name)))
    | some z =>
      if flag db "query_only" then readonly
      let db := markWritten (setCookie db dbk name (atoi z)) dbk
      return (if name == "schema_version" then setHash db dbk none else db, #[])
  | "data_version" => return (db, one (int 1))
  | "freelist_count" => return (db, one (int (freePages db dbk)))
  | "page_count" => return (db, one (int (pages db dbk)))
  | "max_page_count" =>
    let cur := pvInt db (dbk ++ ".max_page_count") 0xfffffffe
    let x : Int := match z with
      | some z => match decOrHex z with
        | (0, x) => if x < 0 then 0 else if x > 0xfffffffe then 0xfffffffe else x
        | _ => 0
      | none => 0
    if x == 0 then return (db, one (int cur))
    let m := max (pages db dbk) x
    return (setPvInt db (dbk ++ ".max_page_count") m, one (int m))
  | "auto_vacuum" =>
    match z with
    | none => return (db, one (int (autoVacuum db dbk)))
    | some z =>
      let e : Int :=
        if iEq z (bs "none") then 0 else if iEq z (bs "full") then 1
        else if iEq z (bs "incremental") then 2
        else let i := atoi z; if 0 ≤ i && i ≤ 2 then i else 0
      let db := setPvInt db "next_auto_vacuum" e
      let cur := autoVacuum db dbk
      let fixed := pages db dbk ≥ 1
      let db := if fixed && (e != 0) != (cur != 0) then db else setPvInt db (dbk ++ ".auto_vacuum") e
      return (if e == 1 || e == 2 then markWritten db dbk else db, #[])
  | "incremental_vacuum" =>
    let n : Int := match z.bind getInt32 with | some n => if n ≤ 0 then 0x7fffffff else n | none => 0x7fffffff
    let db := markWritten db dbk
    if autoVacuum db dbk != 2 then return (db, #[])
    let k := min n (freePages db dbk)
    let db := setCookie (setCookie db dbk "$pages" (pages db dbk - k)) dbk "$free" (freePages db dbk - k)
    return (db, Array.replicate k.toNat #[])
  | "busy_timeout" =>
    let db := match z.bind getInt32 with
      | some n => setPvInt db "busy_timeout" (if n > 0 then n else 0)
      | none => db
    return (db, one (int (pvInt db "busy_timeout" 0)))
  | "cache_size" =>
    match z with
    | none => return (db, one (int (cacheSize db dbk)))
    | some z => return (setPvInt db (dbk ++ ".cache_size") (atoi z), #[])
  | "default_cache_size" =>
    match z with
    | none =>
      let c := db.cookie dbk "default_cache_size"
      return (db, one (int (if c > 0 then c else if c < 0 then -c else -2000)))
    | some z =>
      if flag db "query_only" then readonly
      let size := (atoi z).natAbs
      let db := markWritten (setCookie db dbk "default_cache_size" size) dbk
      return (setPvInt db (dbk ++ ".cache_size") size, #[])
  | "cache_spill" =>
    match z with
    | none =>
      let v := if flag db "cache_spill" then max (cachePages db dbk) (pvInt db (dbk ++ ".spill") 1) else 0
      return (db, one (int v))
    | some z =>
      let size := (getInt32 z).getD 1
      let db := match getInt32 z with
        | some n => if n == 0 then db else
            setPvInt db (dbk ++ ".spill") (if n < 0 then (-1024 * n) / (pageSize db dbk + 136) else n)
        | none => db
      return (setFlag db "cache_spill" (getBoolean z (size != 0)), #[])
  | "case_sensitive_like" =>
    match z with
    | none => return (db, #[])
    | some z =>
      let db := { db with pragmas := { db.pragmas with caseSensitiveLike := getBoolean z false } }
      return (setPvInt db "like_registered" 1, #[])
  | "collation_list" => return (db, collationList.map fun (i, n) => #[int i, txt n])
  | "compile_options" => return (db, compileOptions.map fun o => #[txt o])
  | "pragma_list" => return (db, pragmaList.map fun n => #[txt n])
  | "function_list" =>
    let rows := if pvInt db "like_registered" 0 != 0 then functionListLike else functionList
    return (db, rows.map fun r => #[txt r.name, int r.builtin, txt r.type, txt r.enc, int r.narg, int r.flags])
  | "module_list" =>
    let mods := (pvStr db "modules" "").splitOn "\x00" |>.filter (!·.isEmpty)
    let h := mods.foldl hashInsert {}
    return (db, h.keys.toArray.map fun m => #[txt m])
  | "database_list" =>
    let rows := (databases db).toArray.zipIdx.filterMap fun ((k, n), i) =>
      if k == "temp" && !tempOpen db then none else some #[int i, txt n, txt ""]
    return (db, rows)
  | "encoding" =>
    match zStr with
    | none => return (db, one (txt (pvStr db "encoding" "UTF-8")))
    | some s =>
      let fixed := pvInt db "enc_fixed" 0 != 0 || !db.main.objs.isEmpty
      if fixed then return (db, #[])
      let names : List (String × String) :=
        [("UTF8", "UTF-8"), ("UTF-8", "UTF-8"), ("UTF-16le", "UTF-16le"), ("UTF-16be", "UTF-16be"),
         ("UTF16le", "UTF-16le"), ("UTF16be", "UTF-16be"), ("UTF-16", "UTF-16le"), ("UTF16", "UTF-16le")]
      match names.find? fun (n, _) => iEq (bs n) (bs s) with
      | some (_, e) => return (setPv db "encoding" (txt e), #[])
      | none => fail s!"unsupported encoding: {s}"
  | "hard_heap_limit" =>
    let db := match z.map decOrHex with
      | some (0, n) =>
        let prior := pvInt db "hard_heap_limit" 0
        if n > 0 && (prior == 0 || prior > n) then
          let soft := pvInt db "soft_heap_limit" 0
          let db := setPvInt db "hard_heap_limit" n
          if n < soft || soft == 0 then setPvInt db "soft_heap_limit" n else db
        else db
      | _ => db
    return (db, one (int (pvInt db "hard_heap_limit" 0)))
  | "soft_heap_limit" =>
    let db := match z.map decOrHex with
      | some (0, n) =>
        if n < 0 then db else
        let hard := pvInt db "hard_heap_limit" 0
        let n := if hard > 0 && (n > hard || n == 0) then hard else n
        setPvInt db "soft_heap_limit" n
      | _ => db
    return (db, one (int (pvInt db "soft_heap_limit" 0)))
  | "threads" =>
    let db := match z.map decOrHex with
      | some (0, n) => if n ≥ 0 then setPvInt db "threads" (min (n % 2 ^ 31) 8) else db
      | _ => db
    return (db, one (int (pvInt db "threads" 0)))
  | "analysis_limit" =>
    let db := match z.map decOrHex with
      | some (0, n) => if n ≥ 0 then setPvInt db "analysis_limit" (n % 2 ^ 31) else db
      | _ => db
    return (db, one (int (pvInt db "analysis_limit" 0)))
  | "wal_autocheckpoint" =>
    let db := match z with
      | some z => setPvInt db "wal_autocheckpoint" (let n := atoi z; if n > 0 then n else 0)
      | none => db
    return (db, one (int (pvInt db "wal_autocheckpoint" 1000)))
  | "wal_checkpoint" => return (db, #[#[int 0, int (-1), int (-1)]])
  | "journal_size_limit" =>
    let db := match z.map decOrHex with
      | some (_, n) => setPvInt db (dbk ++ ".journal_size_limit") (if n < -1 then -1 else n)
      | none => db
    return (db, one (int (pvInt db (dbk ++ ".journal_size_limit") (-1))))
  | "journal_mode" =>
    let mode : Option String := zStr.bind fun s =>
      journalModes.find? fun m => (bs m).length ≥ (bs s).length && iEq ((bs m).take (bs s).length) (bs s)
    match mode with
    | none =>
      let k := if explicit then dbk else "main"
      return (db, one (txt (journalMode db k)))
    | some m =>
      let targets := (databases db).filter fun (k, _) =>
        (k != "temp" || tempOpen db) && (k == dbk || !explicit)
      let db := targets.foldl (fun db (k, _) => setJournal db k m) db
      return (db, one (txt (journalMode db dbk)))
  | "locking_mode" =>
    let mode : Option String := zStr.bind fun s =>
      if iEq (bs s) (bs "exclusive") then some "exclusive" else if iEq (bs s) (bs "normal") then some "normal" else none
    match mode, explicit with
    | none, false => return (db, one (txt (pvStr db "locking_mode" "normal")))
    | some m, false => return (setPv db "locking_mode" (txt m), one (txt "exclusive"))
    -- in-memory and temporary databases are always in exclusive mode
    | _, true => return (db, one (txt "exclusive"))
  | "mmap_size" | "shrink_memory" | "optimize" | "temp_store_directory" =>
    if name == "temp_store_directory" then
      if let some s := zStr then
        if !s.isEmpty then fail "not a writable directory"
        if tempOpen db && pvInt db "temp_store" 0 ≤ 1 then
          if db.inTxn then fail "temporary storage cannot be changed from within a transaction"
          return (closeTemp db, #[])
    return (db, #[])
  | "page_size" =>
    match z with
    | none => return (db, one (int (pageSize db dbk)))
    | some z =>
      let n := atoi z
      let db := setPvInt db "next_page_size" n
      if pages db dbk ≥ 1 || !pageSizes.contains n then return (db, #[])
      return (setPvInt db (dbk ++ ".page_size") n, #[])
  | "secure_delete" =>
    let b : Option Int := z.map fun z => if iEq z (bs "fast") then 2 else if getBoolean z false then 1 else 0
    let db := match b with
      | some b =>
        let db := if explicit then db else
          (databases db).foldl (fun db (k, _) =>
            if k == "temp" && !tempOpen db then db else setPvInt db (k ++ ".secure_delete") b) db
        setPvInt db (dbk ++ ".secure_delete") b
      | none => db
    return (db, one (int (pvInt db (dbk ++ ".secure_delete") 0)))
  | "synchronous" =>
    match z with
    | none => return (db, one (int (pvInt db (dbk ++ ".synchronous") (if dbk == "temp" then 0 else 2))))
    | some z =>
      if db.inTxn then fail "Safety level may not be changed inside a transaction"
      if dbk == "temp" then return (db, #[])
      let lvl : Int := if z.head?.map isDigit |>.getD false then atoi z else getSafetyLevel z false 1
      let lvl := (lvl + 1) % 8
      let lvl := if lvl == 0 then 1 else lvl
      return (setPvInt db (dbk ++ ".synchronous") (lvl - 1), #[])
  | "temp_store" =>
    match z with
    | none => return (db, one (int (pvInt db "temp_store" 0)))
    | some z =>
      let ts : Int := match z with
        | c :: _ => if 48 ≤ c && c ≤ 50 then (c - 48).toNat
            else if iEq z (bs "file") then 1 else if iEq z (bs "memory") then 2 else 0
        | [] => 0
      if ts == pvInt db "temp_store" 0 then return (db, #[])
      let db ← if tempOpen db then do
          if db.inTxn then fail "temporary storage cannot be changed from within a transaction"
          pure (closeTemp db)
        else pure db
      return (setPvInt db "temp_store" ts, #[])
  | "integrity_check" | "quick_check" =>
    if let some z := z then
      let isNum := !quoted && (getInt32 z).isSome
      if !isNum then
        if (locate db (str z) zDb).isNone then
          fail s!"no such table: {match zDb with | some d => d ++ "." | none => ""}{str z}"
    return (db, one (txt "ok"))
  | "table_info" | "table_xinfo" =>
    match zStr with
    | none => return (db, #[])
    | some s => match locate db s zDb with
      | some o => return (db, ← tableInfo db vc o (name == "table_xinfo"))
      | none =>
        -- an eponymous virtual table (`sqlite3LocateTable` registers its module)
        let ep : Option Obj := (jsonVtab s).orElse fun _ =>
          if s.toLower.startsWith "pragma_" then
            (vtabShape (s.toLower.drop 7).toString).map fun (hasArg, hasSchema, cols) =>
              .vtab s.toLower (cols ++ (if hasArg then ["arg"] else []) ++ (if hasSchema then ["schema"] else [])) cols.length
          else none
        match ep with
        | some o@(.vtab m _ _) => return (registerModule db m, ← tableInfo db vc o (name == "table_xinfo"))
        | _ => return (db, #[])
  | "table_list" =>
    let mut out := #[]
    for (k, n) in databases db do
      if explicit && k != dbk then continue
      for key in (hashOf db k).keys do
        if let some s := zStr then
          if !iEq (bs s) (bs key) then continue
        match findIn db k key with
        | some (.master _) =>
          out := out.push #[txt n, txt (if k == "temp" then "sqlite_temp_schema" else "sqlite_schema"),
            txt "table", int 5, int 0, int 0]
        | some (.table t) =>
          out := out.push #[txt n, txt t.name, txt "table", int t.cols.size,
            int (if t.withoutRowid then 1 else 0), int (if t.strict then 1 else 0)]
        | some (.view v) =>
          out := out.push #[txt n, txt v.name, txt "view", int (match viewColumns db vc v with | .ok c => c.size | .error _ => 0), int 0, int 0]
        | _ => pure ()
    return (db, out)
  | "index_list" =>
    match zStr.bind fun s => (match locate db s zDb with | some (.table t) => some t | _ => none) with
    | none => return (db, #[])
    | some t =>
      return (db, (indexList db t).mapIdx fun i ix =>
        #[int i, txt ix.name, int (if ix.unique then 1 else 0), txt ix.origin, int (if ix.partial_ then 1 else 0)])
  | "index_info" | "index_xinfo" =>
    match zStr with
    | none => return (db, #[])
    | some s =>
      let hit := match findIndex db s zDb with
        | some p => some p
        | none => match locate db s zDb with
          | some (.table t) => if t.withoutRowid then ((indexList db t).find? (·.origin == "pk")).map (t, ·) else none
          | _ => none
      match hit with
      | some (t, ix) => return (db, indexRows t ix (name == "index_xinfo"))
      | none => return (db, #[])
  | "foreign_key_list" =>
    match zStr.bind fun s => (match locate db s zDb with | some (.table t) => some t | _ => none) with
    | some t => return (db, fkList t)
    | none => return (db, #[])
  | "foreign_key_check" =>
    let tabs : List Table ← match zStr with
      | some s => match locate db s zDb with
        | some (.table t) => pure [t]
        | some _ => pure []
        | none => fail s!"no such table: {match zDb with | some d => d ++ "." | none => ""}{s}"
      | none => pure ((hashOf db dbk).keys.filterMap fun k => (tablesIn db dbk).find? (nameEq ·.name k))
    let mut out := #[]
    for t in tabs do
      if t.fks.isEmpty then continue
      out := out ++ (← fkCheckTable db t)
    return (db, out)
  | _ => return (db, #[])

/-- `PRAGMA [schema.]name [= arg | (arg)]` (see `runWith`); views have no
    known columns. -/
def run (db : Db) (schema : Option String) (name : String) (arg : Option Value) (_call : Bool) :
    Option (Except Err (Db × Array (Array Value))) :=
  some (runWith (fun _ => .ok #[]) db schema name arg)

/-! ## Table-valued functions `pragma_<name>(arg, schema)` (pragmaVtab*) -/

/-- The columns of `pragma_<name>` (`pragmaVtabConnect`): the result columns,
    then the hidden `arg` and `schema`; and how many are visible. -/
def vtabColumns (fname : String) : Option (List String × Nat) := do
  let lname := fname.toLower
  if !lname.startsWith "pragma_" then none
  let (hasArg, hasSchema, cols) ← vtabShape (lname.drop 7).toString
  some (cols ++ (if hasArg then ["arg"] else []) ++ (if hasSchema then ["schema"] else []), cols.length)

/-- The modules registered by a statement that failed stay registered (they
    belong to the connection, not to the transaction). -/
def keepModules (failed restored : Db) : Db :=
  match pv failed "modules" with
  | some v => setPv restored "modules" v
  | none => restored

/-- `SELECT … FROM pragma_<name>(args)`: the module is registered, the
    arguments are the pragma's argument and schema (as text), and the rows
    are those of `PRAGMA 'schema'.name='arg'`, followed by the hidden `arg`
    and `schema` columns. `none` if there is no such eponymous table. -/
def tableValued (vc : ViewCols) (db : Db) (fname : String) (args : List Value) :
    Option (Except Err (Db × Rows)) := do
  let lname := fname.toLower
  if !lname.startsWith "pragma_" then none
  let name := (lname.drop 7).toString
  let (hasArg, hasSchema, _) ← vtabShape name
  let db := registerModule db lname
  let nHidden := (if hasArg then 1 else 0) + (if hasSchema then 1 else 0)
  some do
    if args.length > nHidden then
      throw ({ code := SQLITE_ERROR,
               msg := s!"too many arguments on {fname}() - max {nHidden}" } : Err)
    let texts : List (Option String) := args.map fun v => (v.toText?).map fun b => String.fromUTF8! b
    let (argT, schT) : Option String × Option String :=
      if hasArg then (texts[0]?.getD none, texts[1]?.getD none) else (none, texts[0]?.getD none)
    if let some s := schT then
      if !(databases db).any (nameEq ·.2 s) then
        throw ({ code := SQLITE_ERROR, msg := s!"unknown database '{s}'" } : Err)
    let (db, rows) ← runWith vc db schT name (argT.map fun a => .blob a.toUTF8)
    let opt (o : Option String) : Value := match o with | some s => txt s | none => .null
    let hidden : Array Value := (if hasArg then #[opt argT] else #[]) ++ (if hasSchema then #[opt schT] else #[])
    return (db, rows.map (· ++ hidden))

end Sql.Pragma
