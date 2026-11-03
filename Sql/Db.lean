/-
  The database state: schema and contents of the `main` database
  (`temp` and attached databases are separate `Schema`s), and the
  connection's state.
-/
import Sql.Ast

namespace Sql

/-- Bound on the depth of walks over syntax: SQLite parses no deeper than
    SQLITE_MAX_EXPR_DEPTH (1000) per expression, and its parser stack bounds
    the nesting of queries; this bound is far above both. -/
def syntaxFuel : Nat := 1000000

structure Column where
  name : Name
  /-- declared type, as written -/
  type : String
  aff : Aff
  notNull : Bool := false
  notNullConflict : Option ConflictRes := none
  dflt : Option Expr := none
  coll : Coll := .binary
  /-- `GENERATED ALWAYS AS (e)`, and whether STORED -/
  generated : Option (Expr × Bool) := none
  deriving Inhabited

/-- A UNIQUE or PRIMARY KEY constraint (or a UNIQUE index): column positions and collations. -/
structure UniqueKey where
  cols : List (Nat × Coll)
  onConflict : Option ConflictRes
  /-- name for error messages: `UNIQUE constraint failed: t.a, t.b` -/
  isPk : Bool := false
  deriving Inhabited

structure ForeignKey where
  cols : List Nat
  parent : Name
  parentCols : List Name
  onDelete : String := "NO ACTION"
  onUpdate : String := "NO ACTION"
  deriving Inhabited

/-- A row: its rowid (for WITHOUT ROWID tables an internal counter) and values. -/
structure Row where
  rowid : Int
  vals : Array Value
  /-- columns whose value carries the JSON subtype (`json_each.value`) -/
  jsonCols : List Nat := []
  deriving Inhabited

structure Table where
  name : Name
  cols : Array Column
  /-- the INTEGER PRIMARY KEY column, which is the rowid -/
  rowidCol : Option Nat := none
  withoutRowid : Bool := false
  strict : Bool := false
  autoinc : Bool := false
  pk : List Nat := []
  uniques : List UniqueKey := []
  checks : List (Option Name × Expr) := []
  fks : List ForeignKey := []
  rows : Array Row := #[]
  sql : String
  /-- in the `temp` database -/
  temp : Bool := false
  /-- in an attached database of that name -/
  attachedTo : Option Name := none
  deriving Inhabited

/-- The database a table belongs to. -/
def Table.dbName (t : Table) : Name := t.attachedTo.getD (if t.temp then "temp" else "main")

structure Index where
  name : Name
  table : Name
  /-- indexed expressions with collation and order -/
  cols : List OrderTerm
  unique : Bool
  where_ : Option Expr
  sql : Option String
  deriving Inhabited

structure View where
  name : Name
  cols : List Name
  q : Select
  sql : String
  temp : Bool := false
  attachedTo : Option Name := none
  deriving Inhabited

structure Trigger where
  name : Name
  table : Name
  time : TriggerTime
  event : TriggerEvent
  when_ : Option Expr
  body : List Stmt
  sql : String
  deriving Inhabited

/-- An object of the schema, in creation order (`sqlite_schema` rows). -/
inductive SchemaObj where
  | table (t : Table)
  | index (i : Index)
  | view (v : View)
  | trigger (t : Trigger)
  deriving Inhabited

structure Schema where
  objs : Array SchemaObj := #[]
  /-- `sqlite_sequence`: largest rowid used by each AUTOINCREMENT table -/
  seq : List (Name × Int) := []
  /-- The database headers and pager sizes of every database (`Sql.Pragma`),
      keyed `<db>.<name>` with `<db>` the lower-case database name:
      `schema_version`, `user_version`, `application_id`, `default_cache_size`
      (header cookies) and `$pages`, `$free` (page and freelist counts).
      Absent means 0. Part of the schema so that ROLLBACK restores them, as it
      restores SQLite's database header. -/
  cookies : List (String × Int) := []
  deriving Inhabited

/-- The iteration order of a schema's table hash (`Schema.tblHash` of
    SQLite's hash.c: tables and views by name), which `PRAGMA table_list`,
    `foreign_key_check` and `integrity_check` expose: the keys in list order
    and the number of buckets. Maintained by `Sql.Pragma`. -/
structure TblHash where
  keys : List String := []
  htsize : Nat := 0
  deriving Inhabited

structure Pragmas where
  foreignKeys : Bool := false
  recursiveTriggers : Bool := false
  caseSensitiveLike : Bool := false
  deriving Inhabited

/-- The connection: databases, transaction state, counters. -/
structure Db where
  main : Schema := {}
  pragmas : Pragmas := {}
  /-- open savepoints, innermost first, with the state to roll back to;
      the outermost of a BEGIN is named "" -/
  savepoints : List (Name × Schema) := []
  inTxn : Bool := false
  changes : Int := 0
  totalChanges : Int := 0
  lastRowid : Int := 0
  /-- PRAGMA settings that are not modelled elsewhere, by name (`Sql.Pragma`) -/
  pragmaVals : List (String × Value) := []
  /-- attached databases, in ATTACH order -/
  attached : List Name := []
  /-- state of the executable's stand-in for SQLite's PRNG (`random()`) -/
  prng : Nat := 0
  /-- the table hash of each loaded schema, by lower-case database name;
      absent: the schema is (re)loaded from `sqlite_schema` when next needed -/
  tblHash : List (String × TblHash) := []
  deriving Inhabited

/-- A header cookie of a database (see `Schema.cookies`). -/
def Db.cookie (db : Db) (dbName key : String) : Int :=
  ((db.main.cookies.find? (·.1 == dbName.toLower ++ "." ++ key)).map (·.2)).getD 0

/-- The schema cookie of `main` (`PRAGMA schema_version`). -/
def Db.schemaVersion (db : Db) : Int := db.cookie "main" "schema_version"

namespace Schema

def tables (s : Schema) : List Table :=
  s.objs.toList.filterMap fun | .table t => some t | _ => none

/-- A table by name, searching `temp`, then `main`, then the attached databases
    (in the order of `attachOrder`). -/
def findTable (s : Schema) (n : Name) (attachOrder : List Name := []) : Option Table :=
  let ts := s.tables.filter (nameEq ·.name n)
  (ts.find? (·.temp)).orElse fun _ => (ts.find? fun t => !t.temp && t.attachedTo.isNone).orElse fun _ =>
    attachOrder.findSome? fun a => ts.find? fun t => t.attachedTo.any (nameEq · a)

/-- A table of one database: `temp` (true) or `main` (false). -/
def findTableIn (s : Schema) (temp : Bool) (n : Name) : Option Table :=
  s.tables.find? fun t => t.temp == temp && t.attachedTo.isNone && nameEq t.name n

/-- A table of a named database (`main`, `temp` or attached). -/
def findTableDb (s : Schema) (db : Name) (n : Name) : Option Table :=
  s.tables.find? fun t => nameEq t.dbName db && nameEq t.name n

def findView (s : Schema) (n : Name) : Option View :=
  let vs := s.objs.toList.filterMap fun | .view v => if nameEq v.name n then some v else none | _ => none
  (vs.find? (·.temp)).orElse fun _ => vs.head?

def indexes (s : Schema) : List Index :=
  s.objs.toList.filterMap fun | .index i => some i | _ => none

def triggers (s : Schema) : List Trigger :=
  s.objs.toList.filterMap fun | .trigger t => some t | _ => none

def objName : SchemaObj → Name
  | .table t => t.name | .index i => i.name | .view v => v.name | .trigger t => t.name

def setTable (s : Schema) (t : Table) : Schema :=
  { s with objs := s.objs.map fun o => match o with
      | .table u => if nameEq u.name t.name && nameEq u.dbName t.dbName then .table t else o
      | _ => o }

end Schema

/-- Errors: SQLite's extended result code and message. -/
structure Err where
  code : Nat
  msg : String
  /-- where `sqlite3_prepare` stops for an error found while parsing (the end
      of the lookahead token of the failing reduction); `none`: the end of the
      statement -/
  tail : Option Nat := none
  /-- the statement's changes so far stay (ON CONFLICT FAIL) -/
  keep : Bool := false
  /-- the rows a SELECT handed out before the error (the driver has printed them) -/
  printed : Array (Array Value) := #[]
  deriving Inhabited

def SQLITE_ERROR : Nat := 1
def SQLITE_CONSTRAINT_CHECK : Nat := 275
def SQLITE_CONSTRAINT_NOTNULL : Nat := 1299
def SQLITE_CONSTRAINT_PRIMARYKEY : Nat := 1555
def SQLITE_CONSTRAINT_UNIQUE : Nat := 2067
def SQLITE_CONSTRAINT_FOREIGNKEY : Nat := 787
def SQLITE_CONSTRAINT_TRIGGER : Nat := 1811
def SQLITE_CONSTRAINT_DATATYPE : Nat := 3091
def SQLITE_TOOBIG : Nat := 18
def SQLITE_MISMATCH : Nat := 20
def SQLITE_RANGE : Nat := 25

end Sql
