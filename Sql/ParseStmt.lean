/-
  Statements (https://sqlite.org/lang.html) and the per-statement entry point
  `parseNext`, which mirrors `sqlite3_prepare_v2`: it reads one statement
  from a byte offset of the script and reports where the next one starts.
-/
import Sql.Parse

namespace Sql
open P

def conflictClause : P (Option ConflictRes) := do
  if ← eatKw "ON" then
    kw "CONFLICT"
    resolution
  else return none
where
  resolution : P (Option ConflictRes) := do
    if ← eatKw "ROLLBACK" then return some .rollback
    if ← eatKw "ABORT" then return some .abort
    if ← eatKw "FAIL" then return some .fail
    if ← eatKw "IGNORE" then return some .ignore
    if ← eatKw "REPLACE" then return some .replace
    failHere

def orConflict : P (Option ConflictRes) := do
  if ← eatKw "OR" then conflictClause.resolution else return none

def nameList : P (List Name) := do
  op "LP"
  let mut l := #[← name]
  while ← eatOp "COMMA" do l := l.push (← name)
  op "RP"
  return l.toList

def qualifiedName : P (Option Name × Name) := do
  let n1 ← name
  if ← eatOp "DOT" then return (some n1, ← name) else return (none, n1)

/-- `REFERENCES t(cols) [ON DELETE|UPDATE action | MATCH n]* [[NOT] DEFERRABLE …]` -/
def foreignKeyClause : P (Name × List Name × List String) := do
  kw "REFERENCES"
  let t ← name
  let cols ← if ← isOp "LP" then nameList else pure []
  let mut acts := #[]
  repeat
    if ← eatKw "ON" then
      let ev ← if ← eatKw "DELETE" then pure "DELETE" else do kw "UPDATE"; pure "UPDATE"
      let act ← if ← eatKw "SET" then do
          if ← eatKw "NULL" then pure "SET NULL" else do kw "DEFAULT"; pure "SET DEFAULT"
        else if ← eatKw "CASCADE" then pure "CASCADE"
        else if ← eatKw "RESTRICT" then pure "RESTRICT"
        else do kw "NO"; kw "ACTION"; pure "NO ACTION"
      acts := acts.push s!"{ev} {act}"
    else if ← eatKw "MATCH" then let _ ← name
    else if (← isKw "DEFERRABLE") || ((← isKw "NOT") && (← isKwAt 1 "DEFERRABLE")) then
      let neg ← eatKw "NOT"
      kw "DEFERRABLE"
      if ← eatKw "INITIALLY" then
        if ← eatKw "DEFERRED" then
          if !neg then acts := acts.push "DEFERRED"
        else kw "IMMEDIATE"
    else break
  return (t, cols, acts.toList)

def columnDef : P ColumnDef := do
  let n ← name
  let ty ← parseTypeName
  let mut cs := #[]
  repeat
    let cname ← if ← eatKw "CONSTRAINT" then some <$> name else pure none
    if ← eatKw "PRIMARY" then
      kw "KEY"
      let dir ← if ← eatKw "ASC" then pure (some SortDir.asc) else if ← eatKw "DESC" then pure (some .desc) else pure none
      let oc ← conflictClause
      let ai ← eatKw "AUTOINCR"
      cs := cs.push (cname, .primaryKey dir oc ai)
    else if (← isKw "NOT") && (← isKwAt 1 "NULL") then
      advance; advance; cs := cs.push (cname, .notNull (← conflictClause))
    else if ← eatKw "NULL" then cs := cs.push (cname, .null_)
    else if ← eatKw "UNIQUE" then cs := cs.push (cname, .unique (← conflictClause))
    else if ← eatKw "CHECK" then
      op "LP"
      let c0 := (← get).pos
      let e ← parseExpr
      let txt ← spanText c0 (← get).pos
      op "RP"; cs := cs.push (cname, .check e txt)
    else if ← eatKw "DEFAULT" then
      let s0 := (← get).pos
      let e ← if ← eatOp "LP" then do let e ← parseExpr; op "RP"; pure e
        else if ← eatOp "MINUS" then do let e ← parsePrimary; pure (Expr.unop .neg e)
        else if ← eatOp "PLUS" then parsePrimary
        else parsePrimary
      cs := cs.push (cname, .default_ e (← spanText s0 (← get).pos))
    else if ← eatKw "COLLATE" then cs := cs.push (cname, .collate (← name))
    else if ← isKw "REFERENCES" then
      let (t, cols, acts) ← foreignKeyClause
      cs := cs.push (cname, .references t cols acts)
    else if (← isKw "GENERATED") || (← isKw "AS") then
      if ← eatKw "GENERATED" then kw "ALWAYS"
      kw "AS"; op "LP"; let e ← parseExpr; op "RP"
      let word ← match ← peek with
        | some t => pure (← text t).toLower
        | none => pure ""
      let stored := word == "stored"
      if word == "stored" || word == "virtual" then advance
      cs := cs.push (cname, .generated e stored)
    else
      if cname.isSome then failHere
      break
  return { name := n, type := ty, constraints := cs.toList }

def indexedColumns : P (List (Name × Option Name × SortDir)) := do
  op "LP"
  let one : P (Name × Option Name × SortDir) := do
    let n ← name
    let c ← if ← eatKw "COLLATE" then some <$> name else pure none
    let d ← if ← eatKw "DESC" then pure SortDir.desc else do let _ ← eatKw "ASC"; pure .asc
    return (n, c, d)
  let mut l := #[← one]
  while ← eatOp "COMMA" do l := l.push (← one)
  op "RP"
  return l.toList

def tableConstraint : P (Option (Option Name × TableConstraint)) := do
  let cname ← if ← eatKw "CONSTRAINT" then some <$> name else pure none
  if ← eatKw "PRIMARY" then
    kw "KEY"
    let cols ← indexedColumns
    let ai := false
    return some (cname, .primaryKey cols (← conflictClause) ai)
  if ← eatKw "UNIQUE" then
    let cols ← indexedColumns
    return some (cname, .unique cols (← conflictClause))
  if ← eatKw "CHECK" then
    op "LP"
    let c0 := (← get).pos
    let e ← parseExpr
    let txt ← spanText c0 (← get).pos
    op "RP"
    return some (cname, .check e txt)
  if ← eatKw "FOREIGN" then
    kw "KEY"
    let cols ← nameList
    let (t, rc, acts) ← foreignKeyClause
    return some (cname, .foreignKey cols t rc acts)
  if cname.isSome then failHere
  return none

def returningClause : P (List ResultCol) := do
  if ← eatKw "RETURNING" then parseResultCols else return []

def setList : P (List (List Name × Expr)) := do
  let one : P (List Name × Expr) := do
    let cols ← if ← isOp "LP" then nameList else do pure [← name]
    op "EQ"
    return (cols, ← parseExpr)
  let mut l := #[← one]
  while ← eatOp "COMMA" do l := l.push (← one)
  return l.toList

def upsertClauses : P (List Upsert) := do
  let mut l := #[]
  while (← isKw "ON") && (← isKwAt 1 "CONFLICT") do
    advance; advance
    let target ← if ← eatOp "LP" then do
        let mut cols := #[]
        repeat
          let e ← parseExpr
          let e ← if ← eatKw "COLLATE" then do pure (Expr.collate e (← name)) else pure e
          let _ ← eatKw "ASC" <||> eatKw "DESC"
          cols := cols.push e
          if !(← eatOp "COMMA") then break
        op "RP"
        let w ← if ← eatKw "WHERE" then some <$> parseExpr else pure none
        pure (some (cols.toList, w))
      else pure none
    kw "DO"
    let act ← if ← eatKw "NOTHING" then pure UpsertAction.nothing
      else do
        kw "UPDATE"; kw "SET"
        let sets ← setList
        let w ← if ← eatKw "WHERE" then some <$> parseExpr else pure none
        pure (.update sets w)
    l := l.push { target, action := act }
  return l.toList

def orderLimit : P (List OrderTerm × Option Expr × Option Expr) := do
  let ob ← if ← eatKw "ORDER" then do kw "BY"; parseOrderList else pure []
  if ← eatKw "LIMIT" then
    let a ← parseExpr
    if ← eatKw "OFFSET" then return (ob, some a, some (← parseExpr))
    if ← eatOp "COMMA" then do let b ← parseExpr; return (ob, some b, some a)
    return (ob, some a, none)
  return (ob, none, none)

mutual
partial def parseStmt : P Stmt := do
  let s0 := (← get).pos
  if ← eatKw "EXPLAIN" then
    let qp ← if ← eatKw "QUERY" then do kw "PLAN"; pure true else pure false
    return .explain qp (← parseStmt)
  if (← isKw "SELECT") || (← isKw "VALUES") then return .select (← parseSelect)
  if ← isKw "WITH" then
    let st := (← get).pos
    let (ctes, rec_) ← parseWith
    if (← isKw "SELECT") || (← isKw "VALUES") then
      modify fun s => { s with pos := st }
      return .select (← parseSelect)
    if (← isKw "INSERT") || (← isKw "REPLACE") then return ← parseInsert ctes
    if ← isKw "UPDATE" then return ← parseUpdate ctes
    if ← isKw "DELETE" then return ← parseDelete ctes
    let _ := rec_
    failHere
  if (← isKw "INSERT") || (← isKw "REPLACE") then return ← parseInsert []
  if ← isKw "UPDATE" then return ← parseUpdate []
  if ← isKw "DELETE" then return ← parseDelete []
  if ← eatKw "CREATE" then return ← parseCreate s0
  if ← eatKw "DROP" then
    let kind ← if ← eatKw "TABLE" then pure "table" else if ← eatKw "INDEX" then pure "index"
      else if ← eatKw "VIEW" then pure "view" else do kw "TRIGGER"; pure "trigger"
    let ie ← if ← eatKw "IF" then do kw "EXISTS"; pure true else pure false
    let (sch, n) ← qualifiedName
    return .drop kind ie sch n
  if ← eatKw "BEGIN" then
    let mode ← if ← eatKw "DEFERRED" then pure "DEFERRED" else if ← eatKw "IMMEDIATE" then pure "IMMEDIATE"
      else if ← eatKw "EXCLUSIVE" then pure "EXCLUSIVE" else pure ""
    let _ ← eatKw "TRANSACTION"
    return .begin_ mode
  if (← eatKw "COMMIT") || (← eatKw "END") then
    let _ ← eatKw "TRANSACTION"; return .commit
  if ← eatKw "ROLLBACK" then
    let _ ← eatKw "TRANSACTION"
    if ← eatKw "TO" then
      let _ ← eatKw "SAVEPOINT"
      return .rollback (some (← name))
    return .rollback none
  if ← eatKw "SAVEPOINT" then return .savepoint (← name)
  if ← eatKw "RELEASE" then
    let _ ← eatKw "SAVEPOINT"; return .release (← name)
  if ← eatKw "PRAGMA" then
    let (sch, n) ← qualifiedName
    if ← eatOp "EQ" then return .pragma sch n (some (← pragmaValue)) false
    if ← eatOp "LP" then
      let v ← pragmaValue
      op "RP"; return .pragma sch n (some v) true
    return .pragma sch n none false
  if ← eatKw "ALTER" then
    kw "TABLE"
    let (sch, t) ← qualifiedName
    if ← eatKw "RENAME" then
      if ← eatKw "TO" then return .alterRename sch t (← name)
      let _ ← eatKw "COLUMNKW"
      let old ← name
      kw "TO"
      return .alterRenameColumn sch t old (← name)
    if ← eatKw "ADD" then
      let _ ← eatKw "COLUMNKW"
      let c0 := (← get).pos
      let cd ← columnDef
      return .alterAddColumn sch t cd (← spanText c0 (← get).pos)
    kw "DROP"
    let _ ← eatKw "COLUMNKW"
    return .alterDropColumn sch t (← name)
  if ← eatKw "ATTACH" then
    let _ ← eatKw "DATABASE"
    let f ← parseExpr
    kw "AS"
    return .attach f (← parseExpr)
  if ← eatKw "DETACH" then
    let _ ← eatKw "DATABASE"; return .detach (← name)
  if ← eatKw "VACUUM" then
    let sch ← nameOpt
    let into ← if ← eatKw "INTO" then some <$> parseExpr else pure none
    return .vacuum sch into
  if ← eatKw "REINDEX" then return .reindex (← nameOpt)
  if ← eatKw "ANALYZE" then return .analyze (← nameOpt)
  failHere

/-- The value of a PRAGMA (`nmnum`, `plus_num`, `minus_num` of parse.y), as
    the text `sqlite3Pragma` sees: a number's token text (with its sign for
    `-`), an identifier's or keyword's name. A string literal is passed as a
    BLOB of its dequoted bytes, so that `integrity_check` can tell `'5'` from
    `5` (it reads the raw token). -/
partial def pragmaValue : P Expr := do
  let number : P (Option String) := do
    match ← peek with
    | some t => if t.tk == .integer || t.tk == .float then advance; return some (← text t) else return none
    | none => return none
  if ← eatOp "MINUS" then
    match ← number with | some s => return .lit (.ofString ("-" ++ s)) | none => failHere
  if ← eatOp "PLUS" then
    match ← number with | some s => return .lit (.ofString s) | none => failHere
  if let some s ← number then return .lit (.ofString s)
  match ← peek with
  | some t =>
    match t.tk with
    | .str => advance; return .lit (.blob (unquote (← text t)).toUTF8)
    | .kw c =>
      if c == "ON" || c == "DELETE" || c == "DEFAULT" then advance; return .lit (.ofString (← text t))
      return .lit (.ofString (← name))
    | _ => return .lit (.ofString (← name))
  | none => failHere

partial def parseInsert (ctes : List Cte) : P Stmt := do
  let oc ← if ← eatKw "REPLACE" then pure (some ConflictRes.replace) else do kw "INSERT"; orConflict
  kw "INTO"
  let (sch, t) ← qualifiedName
  let alias ← if ← eatKw "AS" then some <$> name else pure none
  let cols ← if ← isOp "LP" then nameList else pure []
  let isDefault ← eatKw "DEFAULT"
  if isDefault then kw "VALUES"
  let src ← if isDefault then pure InsertSource.defaults
    else if ← eatKw "VALUES" then do
      let row : P (List Expr) := do op "LP"; let l ← parseExprList; op "RP"; return l
      let mut rows := #[← row]
      while ← eatOp "COMMA" do rows := rows.push (← row)
      -- a VALUES followed by compound/order is a SELECT
      if (← isKw "UNION") || (← isKw "INTERSECT") || (← isKw "EXCEPT") || (← isKw "ORDER") || (← isKw "LIMIT") then
        failHere
      pure (.values rows.toList)
    else .select <$> parseSelect
  let ups ← upsertClauses
  return .insert ctes oc sch t alias cols src ups (← returningClause)

partial def parseUpdate (ctes : List Cte) : P Stmt := do
  kw "UPDATE"
  let oc ← orConflict
  let (sch, t) ← qualifiedName
  let alias ← if ← eatKw "AS" then some <$> name else pure none
  if ← eatKw "INDEXED" then do kw "BY"; let _ ← name
  else if (← isKw "NOT") && (← isKwAt 1 "INDEXED") then advance; advance
  kw "SET"
  let sets ← setList
  let from_ ← if ← eatKw "FROM" then some <$> parseFrom else pure none
  let w ← if ← eatKw "WHERE" then some <$> parseExpr else pure none
  let ret ← returningClause
  -- ORDER BY/LIMIT on UPDATE needs SQLITE_ENABLE_UPDATE_DELETE_LIMIT, off by default
  return .update ctes oc sch t alias sets from_ w ret [] none none

partial def parseDelete (ctes : List Cte) : P Stmt := do
  kw "DELETE"; kw "FROM"
  let (sch, t) ← qualifiedName
  let alias ← if ← eatKw "AS" then some <$> name else pure none
  if ← eatKw "INDEXED" then do kw "BY"; let _ ← name
  else if (← isKw "NOT") && (← isKwAt 1 "INDEXED") then advance; advance
  let w ← if ← eatKw "WHERE" then some <$> parseExpr else pure none
  let ret ← returningClause
  return .delete ctes sch t alias w ret [] none none

partial def parseCreate (_s0 : Nat) : P Stmt := do
  let temp ← eatKw "TEMP"
  let unique ← eatKw "UNIQUE"
  if !unique && (← eatKw "TABLE") then
    let ine ← if ← eatKw "IF" then do kw "NOT"; kw "EXISTS"; pure true else pure false
    let s0 := (← get).pos
    let (sch, n) ← qualifiedName
    let curStop : P Nat := do
      match ← peek with
      | some t => return t.stop
      | none => return (← get).src.size
    let tailStart ← curStop
    if ← eatKw "AS" then
      let q ← parseSelect
      return .createTable temp ine sch n [] [] false false (some q) ("CREATE TABLE " ++ (← spanText s0 (← get).pos)) tailStart
    op "LP"
    let colDefT : P ColumnDef := do
      let c ← columnDef
      return { c with tailAt := ← curStop }
    let mut cols := #[← colDefT]
    let mut cons := #[]
    while ← eatOp "COMMA" do
      match ← tableConstraint with
      | some c =>
        cons := cons.push c
        -- after the first table constraint, only constraints follow
        repeat
          let _ ← eatOp "COMMA"
          match ← tableConstraint with
          | some c => cons := cons.push c
          | none => break
        break
      | none => cols := cols.push (← colDefT)
    op "RP"
    let mut wr := false
    let mut strict := false
    repeat
      if ← eatKw "WITHOUT" then
        let w ← name
        if w.toLower != "rowid" then throw ⟨s!"unknown table option: {w}", (← get).toks[(← get).pos - 1]!.stop⟩
        wr := true
      else if ← isKw "STRICT" <||> (do match ← peek with
          | some t => pure ((← text t).toLower == "strict" && t.tk == .id)
          | none => pure false) then
        advance; strict := true
      else break
      if !(← eatOp "COMMA") then break
    return .createTable temp ine sch n cols.toList cons.toList wr strict none ("CREATE TABLE " ++ (← spanText s0 (← get).pos)) tailStart
  if ← eatKw "INDEX" then
    let ine ← if ← eatKw "IF" then do kw "NOT"; kw "EXISTS"; pure true else pure false
    let s0 := (← get).pos
    let (sch, n) ← qualifiedName
    kw "ON"
    let t ← name
    op "LP"
    let cols ← parseOrderList
    op "RP"
    let w ← if ← eatKw "WHERE" then some <$> parseExpr else pure none
    return .createIndex unique ine sch n t cols w ((if unique then "CREATE UNIQUE INDEX " else "CREATE INDEX ") ++ (← spanText s0 (← get).pos))
  if unique then failHere
  if ← eatKw "VIEW" then
    let ine ← if ← eatKw "IF" then do kw "NOT"; kw "EXISTS"; pure true else pure false
    let s0 := (← get).pos
    let (sch, n) ← qualifiedName
    let cols ← if ← isOp "LP" then nameList else pure []
    kw "AS"
    let q ← parseSelect
    return .createView temp ine sch n cols q ("CREATE VIEW " ++ (← spanText s0 (← get).pos))
  if ← eatKw "TRIGGER" then
    let ine ← if ← eatKw "IF" then do kw "NOT"; kw "EXISTS"; pure true else pure false
    let s0 := (← get).pos
    let (sch, n) ← qualifiedName
    let time ← if ← eatKw "BEFORE" then pure TriggerTime.before
      else if ← eatKw "AFTER" then pure .after
      else if ← eatKw "INSTEAD" then do kw "OF"; pure .insteadOf
      else pure .before
    let ev ← if ← eatKw "DELETE" then pure TriggerEvent.delete
      else if ← eatKw "INSERT" then pure .insert
      else do
        kw "UPDATE"
        if ← eatKw "OF" then do
          let mut l := #[← name]
          while ← eatOp "COMMA" do l := l.push (← name)
          pure (.update l.toList)
        else pure (.update [])
    kw "ON"
    let t ← name
    let fer ← if ← eatKw "FOR" then do kw "EACH"; kw "ROW"; pure true else pure false
    let w ← if ← eatKw "WHEN" then some <$> parseExpr else pure none
    let tailBegin ← match ← peek with
      | some t => pure t.stop
      | none => pure (← get).src.size
    kw "BEGIN"
    let mut body := #[]
    repeat
      body := body.push (← parseStmt)
      op "SEMI"
      if ← eatKw "END" then break
    return .createTrigger temp ine sch n time ev t fer w body.toList ("CREATE TRIGGER " ++ (← spanText s0 (← get).pos)) tailBegin
  if ← eatKw "VIRTUAL" then
    kw "TABLE"
    let ine ← if ← eatKw "IF" then do kw "NOT"; kw "EXISTS"; pure true else pure false
    let (sch, n) ← qualifiedName
    kw "USING"
    let m ← name
    let args ← if ← eatOp "LP" then do
        -- module arguments are kept as text
        let mut depth := 1
        let st := (← get).pos
        repeat
          if ← isOp "LP" then depth := depth + 1
          if ← isOp "RP" then depth := depth - 1
          if depth == 0 then break
          if (← peek).isNone then failHere
          advance
        let txt ← spanText st (← get).pos
        op "RP"
        pure ((txt.splitOn ",").map (·.trimAscii.toString))
      else pure []
    return .createVirtualTable ine sch n m args
  failHere
end

/-- The outcome of preparing one statement (`sqlite3_prepare_v2`). -/
inductive Prepared where
  /-- nothing but whitespace, comments or `;` up to the end -/
  | empty
  | ok (s : Stmt) (tail : Nat)
  | error (msg : String) (tail : Nat)

/-- Prepare the statement starting at byte `start` of `src`. -/
def parseNext (src : ByteArray) (start : Nat) : Prepared :=
  let toks := tokenize src start
  -- leading semicolons are empty statements
  let rec skipSemis (i : Nat) : Nat :=
    if h : i < toks.size then (if toks[i].tk == .op "SEMI" then skipSemis (i + 1) else i) else i
  termination_by toks.size - i
  let i := skipSemis 0
  if i ≥ toks.size then .empty else
  let st : PState := { src, toks, pos := i }
  match (do
      let s ← parseStmt
      -- the statement ends at ';' or at the end of the text
      match ← peek with
      | none => pure (s, src.size)
      | some t => if t.tk == .op "SEMI" then advance; pure (s, t.stop) else failHere : P (Stmt × Nat)).run st with
  | .ok ((s, tail), _) => .ok s tail
  | .error e => .error e.msg e.tail

end Sql
