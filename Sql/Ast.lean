/-
  Abstract syntax of SQLite's SQL dialect (https://sqlite.org/lang.html).
  Names are kept as written (after unquoting); comparisons of names are
  ASCII case-insensitive, as in SQLite.
-/
import Sql.Value

namespace Sql

/-- A name as written, unquoted. -/
abbrev Name := String

def nameEq (a b : Name) : Bool := a.toLower == b.toLower

inductive UnOp where
  | neg | pos | bitnot | not
  deriving BEq, Repr, Inhabited

inductive BinOp where
  | add | sub | mul | div | rem | concat
  | bitand | bitor | shl | shr
  | lt | le | gt | ge | eq | ne
  | and | or
  | is | isNot             -- IS / IS NOT (also IS [NOT] DISTINCT FROM, negated)
  | ptr | ptr2             -- -> and ->>
  deriving BEq, Repr, Inhabited

inductive LikeOp where
  | like | glob | regexp | match_
  deriving BEq, Repr, Inhabited

inductive RaiseKind where
  | ignore | rollback | abort | fail
  deriving BEq, Repr, Inhabited

inductive SortDir where
  | asc | desc
  deriving BEq, Repr, Inhabited

inductive NullsOrder where
  | default | first | last
  deriving BEq, Repr, Inhabited

inductive JoinKind where
  | inner | left | right | full | cross
  deriving BEq, Repr, Inhabited

inductive CompoundOp where
  | union | unionAll | intersect | except
  deriving BEq, Repr, Inhabited

inductive FrameUnit where
  | rows | range | groups
  deriving BEq, Repr, Inhabited

inductive FrameExclude where
  | noOthers | currentRow | group | ties
  deriving BEq, Repr, Inhabited

inductive ConflictRes where
  | rollback | abort | fail | ignore | replace
  deriving BEq, Repr, Inhabited

mutual
inductive Expr where
  | lit (v : Value)
  /-- `[schema.][table.]column` -/
  | col (schema : Option Name) (table : Option Name) (column : Name)
  /-- a bare double-quoted identifier: a column if one has that name, else a
      string literal (SQLite's "double-quoted string literal" rule) -/
  | dqcol (name : Name)
  | param (name : String) (index : Nat)
  | unop (op : UnOp) (e : Expr)
  | binop (op : BinOp) (a b : Expr)
  | collate (e : Expr) (coll : Name)
  | cast (e : Expr) (type : String)
  | between (neg : Bool) (e lo hi : Expr)
  | inList (neg : Bool) (e : Expr) (items : List Expr)
  | inSelect (neg : Bool) (e : Expr) (q : Select)
  | inTable (neg : Bool) (e : Expr) (schema : Option Name) (table : Name) (args : List Expr)
  | like (op : LikeOp) (neg : Bool) (e pat : Expr) (escape : Option Expr)
  | isNull (neg : Bool) (e : Expr)
  | case_ (base : Option Expr) (whens : List (Expr × Expr)) (else_ : Option Expr)
  | exists_ (q : Select)
  | subquery (q : Select)
  | row (items : List Expr)
  /-- function call: name, DISTINCT, arguments (`*` is `star`), ORDER BY inside
      the call, FILTER, OVER -/
  | call (name : Name) (distinct : Bool) (args : List Expr) (star : Bool)
      (orderBy : List OrderTerm) (filter : Option Expr) (over : Option Window)
  | raise (kind : RaiseKind) (msg : Option Expr)

inductive OrderTerm where
  | mk (e : Expr) (dir : SortDir) (nulls : NullsOrder)

/-- a window: base window name, PARTITION BY, ORDER BY, frame -/
inductive Window where
  | mk (base : Option Name) (partition : List Expr) (orderBy : List OrderTerm) (frame : Option Frame)

inductive FrameBound where
  | unboundedPreceding | preceding (e : Expr) | currentRow | following (e : Expr) | unboundedFollowing

inductive Frame where
  | mk (unit : FrameUnit) (start stop : FrameBound) (exclude : FrameExclude)

inductive ResultCol where
  | star
  | tableStar (table : Name)
  | expr (e : Expr) (alias : Option Name) (text : String)  -- text: the expression as written

inductive FromItem where
  | table (schema : Option Name) (name : Name) (alias : Option Name) (indexed : Option (Option Name))
  | tableFn (schema : Option Name) (name : Name) (args : List Expr) (alias : Option Name)
  | subquery (q : Select) (alias : Option Name)
  | join (left : FromItem) (kind : JoinKind) (natural : Bool) (right : FromItem)
      (on : Option Expr) (usingCols : List Name)

inductive SelectCore where
  | select (distinct : Bool) (cols : List ResultCol) (from_ : Option FromItem)
      (where_ : Option Expr) (groupBy : List Expr) (having : Option Expr)
      (windows : List (Name × Window))
  | values (rows : List (List Expr))

inductive Cte where
  | mk (name : Name) (columns : List Name) (materialized : Option Bool) (q : Select)

inductive Select where
  | mk (with_ : List Cte) (recursive : Bool) (first : SelectCore)
      (rest : List (CompoundOp × SelectCore))
      (orderBy : List OrderTerm) (limit : Option Expr) (offset : Option Expr)
end

instance : Inhabited Expr := ⟨.lit .null⟩
instance : Inhabited OrderTerm := ⟨.mk default .asc .default⟩
instance : Inhabited Window := ⟨.mk none [] [] none⟩
instance : Inhabited FrameBound := ⟨.currentRow⟩
instance : Inhabited Frame := ⟨.mk .rows .currentRow .currentRow .noOthers⟩
instance : Inhabited ResultCol := ⟨.star⟩
instance : Inhabited FromItem := ⟨.table none "" none none⟩
instance : Inhabited SelectCore := ⟨.values []⟩

instance : Inhabited Select := ⟨.mk [] false (.values []) [] [] none none⟩
instance : Inhabited Cte := ⟨.mk "" [] none default⟩

/-! ## Statements -/

inductive ColConstraint where
  | primaryKey (dir : Option SortDir) (onConflict : Option ConflictRes) (autoinc : Bool)
  | notNull (onConflict : Option ConflictRes)
  | null_
  | unique (onConflict : Option ConflictRes)
  | check (e : Expr) (text : String)
  | default_ (e : Expr) (text : String)
  | collate (name : Name)
  | references (table : Name) (cols : List Name) (actions : List String)
  | generated (e : Expr) (stored : Bool)

structure ColumnDef where
  name : Name
  type : String
  constraints : List (Option Name × ColConstraint)
  /-- prepare's tail for an error in this definition (end of the next token) -/
  tailAt : Nat := 0

inductive TableConstraint where
  | primaryKey (cols : List (Name × Option Name × SortDir)) (onConflict : Option ConflictRes) (autoinc : Bool)
  | unique (cols : List (Name × Option Name × SortDir)) (onConflict : Option ConflictRes)
  | check (e : Expr) (text : String)
  | foreignKey (cols : List Name) (table : Name) (refCols : List Name) (actions : List String)

inductive UpsertAction where
  | nothing
  | update (sets : List (List Name × Expr)) (where_ : Option Expr)

structure Upsert where
  target : Option (List Expr × Option Expr)
  action : UpsertAction

inductive InsertSource where
  | values (rows : List (List Expr))
  | select (q : Select)
  | defaults

inductive TriggerTime where
  | before | after | insteadOf
  deriving BEq, Repr, Inhabited

inductive TriggerEvent where
  | delete | insert | update (cols : List Name)

inductive Stmt where
  | select (q : Select)
  | createTable (temp : Bool) (ifNotExists : Bool) (schema : Option Name) (name : Name)
      (cols : List ColumnDef) (constraints : List (Option Name × TableConstraint))
      (withoutRowid strict : Bool) (asSelect : Option Select) (text : String)
      -- tailAtStart: prepare's tail for "already exists" (the end of `(` or `AS`)
      (tailAtStart : Nat)
  | insert (with_ : List Cte) (orConflict : Option ConflictRes) (schema : Option Name) (table : Name)
      (alias : Option Name) (cols : List Name) (source : InsertSource) (upserts : List Upsert)
      (returning : List ResultCol)
  | update (with_ : List Cte) (orConflict : Option ConflictRes) (schema : Option Name) (table : Name)
      (alias : Option Name) (sets : List (List Name × Expr)) (from_ : Option FromItem)
      (where_ : Option Expr) (returning : List ResultCol) (orderBy : List OrderTerm)
      (limit offset : Option Expr)
  | delete (with_ : List Cte) (schema : Option Name) (table : Name) (alias : Option Name)
      (where_ : Option Expr) (returning : List ResultCol) (orderBy : List OrderTerm)
      (limit offset : Option Expr)
  | createIndex (unique ifNotExists : Bool) (schema : Option Name) (name : Name) (table : Name)
      (cols : List OrderTerm) (where_ : Option Expr) (text : String)
  | createView (temp ifNotExists : Bool) (schema : Option Name) (name : Name) (cols : List Name)
      (q : Select) (text : String)
  | createTrigger (temp ifNotExists : Bool) (schema : Option Name) (name : Name) (time : TriggerTime)
      (event : TriggerEvent) (table : Name) (forEachRow : Bool) (when_ : Option Expr)
      (body : List Stmt) (text : String)
      -- tailAtBegin: prepare's tail for an error in the header (the end of `BEGIN`)
      (tailAtBegin : Nat)
  | drop (kind : String) (ifExists : Bool) (schema : Option Name) (name : Name)
  | begin_ (mode : String)
  | commit
  | rollback (savepoint : Option Name)
  | savepoint (name : Name)
  | release (name : Name)
  | pragma (schema : Option Name) (name : Name) (arg : Option Expr) (call : Bool)
  | alterRename (schema : Option Name) (table : Name) (newName : Name)
  | alterRenameColumn (schema : Option Name) (table : Name) (old new : Name)
  | alterAddColumn (schema : Option Name) (table : Name) (col : ColumnDef) (text : String)
  | alterDropColumn (schema : Option Name) (table : Name) (col : Name)
  | attach (file : Expr) (schema : Expr)
  | detach (schema : Name)
  | vacuum (schema : Option Name) (into : Option Expr)
  | reindex (name : Option Name)
  | analyze (name : Option Name)
  | explain (queryPlan : Bool) (s : Stmt)
  | createVirtualTable (ifNotExists : Bool) (schema : Option Name) (name : Name) (module : Name)
      (args : List String)

instance : Inhabited Stmt := ⟨.commit⟩
instance : Inhabited TriggerEvent := ⟨.delete⟩

end Sql
