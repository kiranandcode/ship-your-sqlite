/-
  The database state: schema and contents of the `main` database
  (`temp` and attached databases are separate `Schema`s), and the
  connection's state.
-/
import Sql.Ast

namespace Sql

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
  deriving Inhabited

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
  userVersion : Int := 0
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
  deriving Inhabited

namespace Schema

def tables (s : Schema) : List Table :=
  s.objs.toList.filterMap fun | .table t => some t | _ => none

def findTable (s : Schema) (n : Name) : Option Table :=
  s.tables.find? (nameEq ·.name n)

def findView (s : Schema) (n : Name) : Option View :=
  s.objs.toList.findSome? fun | .view v => if nameEq v.name n then some v else none | _ => none

def indexes (s : Schema) : List Index :=
  s.objs.toList.filterMap fun | .index i => some i | _ => none

def triggers (s : Schema) : List Trigger :=
  s.objs.toList.filterMap fun | .trigger t => some t | _ => none

def objName : SchemaObj → Name
  | .table t => t.name | .index i => i.name | .view v => v.name | .trigger t => t.name

def setTable (s : Schema) (t : Table) : Schema :=
  { s with objs := s.objs.map fun o => match o with
      | .table u => if nameEq u.name t.name then .table t else o
      | _ => o }

end Schema

/-- Errors: SQLite's extended result code and message. -/
structure Err where
  code : Nat
  msg : String
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
