/-
  The parser: SQL text → statements (https://sqlite.org/lang.html), one
  statement at a time, as `sqlite3_prepare` takes them.

  A syntax error is reported at the first token that cannot continue the
  statement, as SQLite's LALR parser does: `near "X": syntax error`, or
  `incomplete input` at the end of the text. `unrecognized token: "X"` for a
  token the lexer rejects.
-/
import Sql.Ast
import Sql.Lex

namespace Sql

/-- A parse error and where the next statement starts (`sqlite3_prepare`'s tail). -/
structure ParseError where
  msg : String
  tail : Nat

structure PState where
  src : ByteArray
  toks : Array Token
  pos : Nat
  /-- number of `?` parameters seen -/
  nparam : Nat := 0

abbrev P := StateT PState (Except ParseError)

namespace P

def text (t : Token) : P String := do
  let s ← get
  return String.fromUTF8! (s.src.extract t.start t.stop)

def peekAt (k : Nat) : P (Option Token) := do
  let s ← get
  return s.toks[s.pos + k]?

def peek : P (Option Token) := peekAt 0

def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }

/-- Fail at the current token. -/
def failHere {α} : P α := do
  match ← peek with
  | none =>
    let s ← get
    throw ⟨"incomplete input", s.src.size⟩
  | some t =>
    if t.tk == .illegal then
      throw ⟨s!"unrecognized token: \"{← text t}\"", t.start⟩
    else
      throw ⟨s!"near \"{← text t}\": syntax error", t.stop⟩

def isKw (cls : String) : P Bool := do
  match ← peek with
  | some { tk := .kw c, .. } => return c == cls
  | _ => return false

def isKwAt (k : Nat) (cls : String) : P Bool := do
  match ← peekAt k with
  | some { tk := .kw c, .. } => return c == cls
  | _ => return false

def isOp (o : String) : P Bool := do
  match ← peek with
  | some { tk := .op x, .. } => return x == o
  | _ => return false

def eatKw (cls : String) : P Bool := do
  if ← isKw cls then advance; return true else return false

def eatOp (o : String) : P Bool := do
  if ← isOp o then advance; return true else return false

def kw (cls : String) : P Unit := do
  unless ← eatKw cls do failHere

def op (o : String) : P Unit := do
  unless ← eatOp o do failHere

/-- the keyword word of the current token (for JOIN_KW, LIKE_KW, CTIME_KW) -/
def kwWord : P String := do
  match ← peek with
  | some t => return (← text t).toUpper
  | none => return ""

/-- Unquote an identifier or string token. -/
def unquote (s : String) : String :=
  let cs := s.toList
  match cs with
  | '[' :: rest => String.ofList (rest.dropLast)
  | q :: rest =>
    if q == '\'' || q == '"' || q == '`' then
      let body := rest.dropLast
      let rec go : List Char → List Char
        | [] => []
        | c :: d :: t => if c == q && d == q then q :: go t else c :: go (d :: t)
        | [c] => [c]
      String.ofList (go body)
    else s
  | [] => s

/-- An identifier (`nm`): an ID, a fallback keyword, or a string. -/
def nameOpt (allowString := true) : P (Option Name) := do
  match ← peek with
  | some t =>
    match t.tk with
    | .id => advance; return some (unquote (← text t))
    | .str => if allowString then advance; return some (unquote (← text t)) else return none
    | .kw c =>
      if fallbackToId.contains c || c == "JOIN_KW" then advance; return some (← text t)
      else return none
    | _ => return none
  | none => return none

def name : P Name := do
  match ← nameOpt with
  | some n => return n
  | none => failHere

/-- source text from the start of token `i` to the end of token `j - 1` -/
def spanText (i j : Nat) : P String := do
  let s ← get
  if j ≤ i then return "" else
  match s.toks[i]?, s.toks[j - 1]? with
  | some a, some b => return String.fromUTF8! (s.src.extract a.start b.stop)
  | _, _ => return ""

end P

open P

/-- Value of a numeric literal token. -/
def numLiteral (s : String) (isFloat : Bool) : Except String Value :=
  let b := s.toUTF8
  if !isFloat && s.length > 2 && (s.startsWith "0x" || s.startsWith "0X") then
    let hex := (s.toList.drop 2).filter (· != '_')
    if hex.length > 16 then .error s!"hex literal too big: {s}"
    else
      let v : Nat := hex.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else (c.toLower.toNat - 87))) 0
      .ok (.int (if v ≥ 2 ^ 63 then (v : Int) - 2 ^ 64 else v))
  else
    let b := ByteArray.mk (b.data.filter (· != 95))   -- digit separators
    if !isFloat then
      match atoi64 b with
      | some i => .ok (.int i)
      | none => .ok (.real (atof b).value)
    else .ok (.real (atof b).value)

def hexBlob (s : String) : ByteArray :=
  let h := (s.toList.drop 2).dropLast
  let hv (c : Char) : Nat := if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87
  let rec go : List Char → List UInt8
    | a :: b :: t => (hv a * 16 + hv b).toUInt8 :: go t
    | _ => []
  ⟨(go h).toArray⟩

mutual

partial def parseExpr : P Expr := parseOr

partial def parseOr : P Expr := do
  let mut e ← parseAnd
  while ← eatKw "OR" do
    e := .binop .or e (← parseAnd)
  return e

partial def parseAnd : P Expr := do
  let mut e ← parseNot
  while ← eatKw "AND" do
    let r ← parseNot
    -- sqlite3ExprAnd: an AND with an integer literal 0 on either side is FALSE
    -- at parse time (the other side is never resolved)
    let isZero (x : Expr) : Bool := match x with | .lit (.int 0) => true | _ => false
    e := if isZero e || isZero r then .lit (.int 0) else .binop .and e r
  return e

partial def parseNot : P Expr := do
  if ← eatKw "NOT" then return .unop .not (← parseNot)
  parseEquality

/-- IS, MATCH, LIKE, BETWEEN, IN, ISNULL, NOTNULL, NE, EQ (one level, left assoc) -/
partial def parseEquality : P Expr := do
  let mut e ← parseComparison
  repeat
    if ← eatOp "EQ" then e := .binop .eq e (← parseComparison)
    else if ← eatOp "NE" then e := .binop .ne e (← parseComparison)
    else if ← eatKw "ISNULL" then e := .isNull false e
    else if ← eatKw "NOTNULL" then e := .isNull true e
    else if ← isKw "IS" then
      advance
      let neg ← eatKw "NOT"
      if ← eatKw "DISTINCT" then
        kw "FROM"
        let r ← parseComparison
        e := .binop (if neg then .is else .isNot) e r
      else
        let r ← parseComparison
        e := .binop (if neg then .isNot else .is) e r
    else if (← isKw "NOT") && ((← isKwAt 1 "NULL")) then
      advance; advance; e := .isNull true e
    else
      let neg := (← isKw "NOT") && ((← isKwAt 1 "BETWEEN") || (← isKwAt 1 "IN") ||
                  (← isKwAt 1 "LIKE_KW") || (← isKwAt 1 "MATCH"))
      if neg then advance
      if ← eatKw "BETWEEN" then
        let lo ← parseComparison
        kw "AND"
        let hi ← parseComparison
        e := .between neg e lo hi
      else if ← eatKw "IN" then
        e ← parseInRhs neg e
      else if ← isKw "LIKE_KW" then
        let w ← kwWord
        advance
        let opk := if w == "GLOB" then LikeOp.glob else if w == "REGEXP" then .regexp else .like
        let pat ← parseComparison
        let esc ← if ← eatKw "ESCAPE" then some <$> parseComparison else pure none
        e := .like opk neg e pat esc
      else if ← eatKw "MATCH" then
        let pat ← parseComparison
        e := .like .match_ neg e pat none
      else if neg then failHere
      else break
  return e

partial def parseInRhs (neg : Bool) (e : Expr) : P Expr := do
  if ← eatOp "LP" then
    if ← eatOp "RP" then return .inList neg e []
    if (← isKw "SELECT") || (← isKw "VALUES") || (← isKw "WITH") then
      let q ← parseSelect
      op "RP"
      return .inSelect neg e q
    let items ← parseExprList
    op "RP"
    return .inList neg e items
  else
    let n1 ← name
    let (sch, t) ← if ← eatOp "DOT" then do pure (some n1, ← name) else pure (none, n1)
    let args ← if ← eatOp "LP" then do
        if ← eatOp "RP" then pure [] else do let a ← parseExprList; op "RP"; pure a
      else pure []
    return .inTable neg e sch t args

partial def parseComparison : P Expr := do
  let mut e ← parseEscape
  repeat
    if ← eatOp "LT" then e := .binop .lt e (← parseEscape)
    else if ← eatOp "LE" then e := .binop .le e (← parseEscape)
    else if ← eatOp "GT" then e := .binop .gt e (← parseEscape)
    else if ← eatOp "GE" then e := .binop .ge e (← parseEscape)
    else break
  return e

partial def parseEscape : P Expr := parseBits

partial def parseBits : P Expr := do
  let mut e ← parseAdd
  repeat
    if ← eatOp "BITAND" then e := .binop .bitand e (← parseAdd)
    else if ← eatOp "BITOR" then e := .binop .bitor e (← parseAdd)
    else if ← eatOp "LSHIFT" then e := .binop .shl e (← parseAdd)
    else if ← eatOp "RSHIFT" then e := .binop .shr e (← parseAdd)
    else break
  return e

partial def parseAdd : P Expr := do
  let mut e ← parseMul
  repeat
    if ← eatOp "PLUS" then e := .binop .add e (← parseMul)
    else if ← eatOp "MINUS" then e := .binop .sub e (← parseMul)
    else break
  return e

partial def parseMul : P Expr := do
  let mut e ← parseConcat
  repeat
    if ← eatOp "STAR" then e := .binop .mul e (← parseConcat)
    else if ← eatOp "SLASH" then e := .binop .div e (← parseConcat)
    else if ← eatOp "REM" then e := .binop .rem e (← parseConcat)
    else break
  return e

partial def parseConcat : P Expr := do
  let mut e ← parseCollate
  repeat
    if ← eatOp "CONCAT" then e := .binop .concat e (← parseCollate)
    else if ← isOp "PTR" then
      let s ← get
      let t := s.toks[s.pos]!
      advance
      let two := t.stop - t.start == 3
      e := .binop (if two then .ptr2 else .ptr) e (← parseCollate)
    else break
  return e

partial def parseCollate : P Expr := do
  let mut e ← parseUnary
  while ← eatKw "COLLATE" do
    e := .collate e (← name)
  return e

partial def parseUnary : P Expr := do
  if ← eatOp "MINUS" then
    -- -9223372036854775808 is an integer
    match ← peek with
    | some t =>
      if t.tk == .integer && (← text t) == "9223372036854775808" then
        advance; return .lit (.int minI64)
      return .unop .neg (← parseUnary)
    | none => return .unop .neg (← parseUnary)
  if ← eatOp "PLUS" then return .unop .pos (← parseUnary)
  if ← eatOp "BITNOT" then return .unop .bitnot (← parseUnary)
  parsePrimary

partial def parseExprList : P (List Expr) := do
  let mut l := #[← parseExpr]
  while ← eatOp "COMMA" do l := l.push (← parseExpr)
  return l.toList

partial def parsePrimary : P Expr := do
  let some t ← peek | failHere
  match t.tk with
  | .integer | .float | .qnumber =>
    advance
    match numLiteral (← text t) (t.tk == .float || (← text t).any (fun c => c == '.' || c == 'e' || c == 'E') && !(← text t).startsWith "0x") with
    | .ok v => return .lit v
    | .error m => throw ⟨m, t.stop⟩
  | .str => advance; return .lit (.ofString (unquote (← text t)))
  | .blob => advance; return .lit (.blob (hexBlob (← text t)))
  | .variable =>
    advance
    let s ← get
    let txt ← text t
    let idx := if txt == "?" then s.nparam + 1 else
      if txt.startsWith "?" then (txt.drop 1).toNat! else s.nparam + 1
    set { s with nparam := max s.nparam idx }
    return .param txt idx
  | .op "LP" =>
    advance
    if (← isKw "SELECT") || (← isKw "VALUES") || (← isKw "WITH") then
      let q ← parseSelect
      op "RP"
      return .subquery q
    let items ← parseExprList
    op "RP"
    match items with
    | [e] => return e
    | _ => return .row items
  | .kw "NULL" => advance; return .lit .null
  | .kw "CAST" =>
    advance; op "LP"
    let e ← parseExpr
    kw "AS"
    let ty ← parseTypeName
    op "RP"
    return .cast e ty
  | .kw "CASE" =>
    advance
    let base ← if ← isKw "WHEN" then pure none else some <$> parseExpr
    let mut whens := #[]
    while ← eatKw "WHEN" do
      let c ← parseExpr
      kw "THEN"
      whens := whens.push (c, ← parseExpr)
    if whens.isEmpty then failHere
    let els ← if ← eatKw "ELSE" then some <$> parseExpr else pure none
    kw "END"
    return .case_ base whens.toList els
  | .kw "EXISTS" =>
    advance; op "LP"
    let q ← parseSelect
    op "RP"
    return .exists_ q
  | .kw "NOT" =>
    -- NOT EXISTS reaches here only through parseNot; keep for safety
    failHere
  | .kw "RAISE" =>
    advance; op "LP"
    let w ← kwWord
    let k ← if ← eatKw "IGNORE" then pure RaiseKind.ignore
      else if ← eatKw "ROLLBACK" then pure .rollback
      else if ← eatKw "ABORT" then pure .abort
      else if ← eatKw "FAIL" then pure .fail else failHere
    let _ := w
    let msg ← if k == .ignore then pure none else do op "COMMA"; some <$> parseExpr
    op "RP"
    return .raise k msg
  | .kw "CTIME_KW" =>
    advance
    let w := (← text t).toUpper
    return .call (if w == "CURRENT_TIME" then "time" else if w == "CURRENT_DATE" then "date" else "datetime")
      false [] false [] none none
  | _ =>
    -- identifiers, qualified names, function calls
    match ← nameOpt (allowString := false) with
    | none => failHere
    | some n =>
      if ← isOp "LP" then
        advance
        parseCall n
      else if ← eatOp "DOT" then
        let n2 ← name
        if ← eatOp "DOT" then
          let n3 ← name
          return .col (some n) (some n2) n3
        return .col none (some n) n2
      else if t.tk == .id && (← text t).startsWith "\"" then return .dqcol n
      else return .col none none n

partial def parseCall (fname : Name) : P Expr := do
  let mut distinct := false
  let mut args := []
  let mut star := false
  let mut orderBy := []
  if ← eatOp "STAR" then star := true; op "RP"
  else if ← eatOp "RP" then pure ()
  else
    distinct ← eatKw "DISTINCT"
    if !distinct then let _ ← eatKw "ALL"
    args ← parseExprList
    if ← eatKw "ORDER" then
      kw "BY"
      orderBy ← parseOrderList
    op "RP"
  let filter ← if ← eatKw "FILTER" then do
      op "LP"; kw "WHERE"; let e ← parseExpr; op "RP"; pure (some e)
    else pure none
  let over ← if ← eatKw "OVER" then do
      if ← eatOp "LP" then do let w ← parseWindowBody; op "RP"; pure (some w)
      else do let n ← name; pure (some (Window.mk (some n) [] [] none))
    else pure none
  return .call fname distinct args star orderBy filter over

partial def parseWindowBody : P Window := do
  let base ← if (← isKw "PARTITION") || (← isKw "ORDER") || (← isKw "RANGE") || (← isKw "ROWS") || (← isKw "GROUPS") || (← isOp "RP") then pure none
    else nameOpt
  let part ← if ← eatKw "PARTITION" then do kw "BY"; parseExprList else pure []
  let ord ← if ← eatKw "ORDER" then do kw "BY"; parseOrderList else pure []
  let frame ← if (← isKw "RANGE") || (← isKw "ROWS") || (← isKw "GROUPS") then some <$> parseFrame else pure none
  return .mk base part ord frame

partial def parseFrame : P Frame := do
  let unit ← if ← eatKw "RANGE" then pure FrameUnit.range else if ← eatKw "ROWS" then pure .rows
    else do kw "GROUPS"; pure .groups
  let bound : P FrameBound := do
    if ← eatKw "UNBOUNDED" then
      if ← eatKw "PRECEDING" then return .unboundedPreceding
      kw "FOLLOWING"; return .unboundedFollowing
    if ← eatKw "CURRENT" then kw "ROW"; return .currentRow
    let e ← parseExpr
    if ← eatKw "PRECEDING" then return .preceding e
    kw "FOLLOWING"; return .following e
  let (start, stop) ← if ← eatKw "BETWEEN" then do
      let a ← bound; kw "AND"; let b ← bound; pure (a, b)
    else do let a ← bound; pure (a, FrameBound.currentRow)
  let excl ← if ← eatKw "EXCLUDE" then do
      if ← eatKw "NO" then do kw "OTHERS"; pure FrameExclude.noOthers
      else if ← eatKw "CURRENT" then do kw "ROW"; pure .currentRow
      else if ← eatKw "GROUP" then pure .group
      else do kw "TIES"; pure .ties
    else pure .noOthers
  return .mk unit start stop excl

partial def parseOrderList : P (List OrderTerm) := do
  let one : P OrderTerm := do
    let e ← parseExpr
    let dir ← if ← eatKw "DESC" then pure SortDir.desc else do let _ ← eatKw "ASC"; pure .asc
    let nulls ← if ← eatKw "NULLS" then do
        if ← eatKw "FIRST" then pure NullsOrder.first else do kw "LAST"; pure .last
      else pure .default
    return .mk e dir nulls
  let mut l := #[← one]
  while ← eatOp "COMMA" do l := l.push (← one)
  return l.toList

/-- A type name: words, optionally `(n)` or `(n, m)`; returned as written. -/
partial def parseTypeName : P String := do
  let s0 := (← get).pos
  let mut any := false
  repeat
    match ← nameOpt with
    | some _ => any := true
    | none => break
  if any && (← isOp "LP") then
    advance
    let signed : P Unit := do
      let _ ← eatOp "PLUS" <||> eatOp "MINUS"
      match ← peek with
      | some t => if t.tk == .integer || t.tk == .float || t.tk == .qnumber then advance else failHere
      | none => failHere
    signed
    if ← eatOp "COMMA" then signed
    op "RP"
  spanText s0 (← get).pos

partial def parseResultCols : P (List ResultCol) := do
  let one : P ResultCol := do
    if ← eatOp "STAR" then return .star
    -- table.*
    match ← peekAt 0, ← peekAt 1, ← peekAt 2 with
    | some _, some { tk := .op "DOT", .. }, some { tk := .op "STAR", .. } =>
      let n ← name; advance; advance; return .tableStar n
    | _, _, _ =>
      let s0 := (← get).pos
      let e ← parseExpr
      let txt ← spanText s0 (← get).pos
      if ← eatKw "AS" then return .expr e (some (← name)) txt
      match ← nameOpt with
      | some a => return .expr e (some a) txt
      | none => return .expr e none txt
  let mut l := #[← one]
  while ← eatOp "COMMA" do l := l.push (← one)
  return l.toList

partial def parseAlias : P (Option Name) := do
  if ← eatKw "AS" then return some (← name)
  -- an alias may not be a keyword that can start the rest of the clause
  if (← isKw "JOIN_KW") then return none
  nameOpt

partial def parseFromTerm : P FromItem := do
  if ← eatOp "LP" then
    if (← isKw "SELECT") || (← isKw "VALUES") || (← isKw "WITH") then
      let q ← parseSelect
      op "RP"
      return .subquery q (← parseAlias)
    let f ← parseFrom
    op "RP"
    match ← parseAlias with
    | some a => return .subquery (.mk [] false (.select false [.star] (some f) none [] none []) [] [] none none) (some a)
    | none => return f
  let n1 ← name
  let (sch, n) ← if ← eatOp "DOT" then do pure (some n1, ← name) else pure (none, n1)
  if ← eatOp "LP" then
    let args ← if ← eatOp "RP" then pure [] else do let a ← parseExprList; op "RP"; pure a
    return .tableFn sch n args (← parseAlias)
  let alias ← parseAlias
  let indexed ← if ← eatKw "INDEXED" then do kw "BY"; pure (some (some (← name)))
    else if (← isKw "NOT") && (← isKwAt 1 "INDEXED") then do advance; advance; pure (some none)
    else pure none
  return .table sch n alias indexed

partial def parseFrom : P FromItem := do
  let mut left ← parseFromTerm
  repeat
    let mut kind := JoinKind.inner
    let mut natural := false
    if ← eatOp "COMMA" then
      kind := .cross
    else if (← isKw "JOIN_KW") || (← isKw "JOIN") then
      -- [NATURAL] [LEFT|RIGHT|FULL] [OUTER] | INNER | CROSS  JOIN
      let mut words := #[]
      while ← isKw "JOIN_KW" do words := words.push (← kwWord); advance
      kw "JOIN"
      natural := words.contains "NATURAL"
      kind := if words.contains "LEFT" then .left else if words.contains "RIGHT" then .right
        else if words.contains "FULL" then .full else if words.contains "CROSS" then .cross else .inner
      if words.contains "CROSS" then kind := .inner
    else break
    let right ← parseFromTerm
    let on ← if ← eatKw "ON" then some <$> parseExpr else pure none
    let usingCols ← if ← eatKw "USING" then do
        op "LP"
        let mut l := #[← name]
        while ← eatOp "COMMA" do l := l.push (← name)
        op "RP"; pure l.toList
      else pure []
    left := .join left kind natural right on usingCols
  return left

partial def parseSelectCore : P SelectCore := do
  if ← eatKw "VALUES" then
    let row : P (List Expr) := do op "LP"; let l ← parseExprList; op "RP"; return l
    let mut rows := #[← row]
    while ← eatOp "COMMA" do rows := rows.push (← row)
    return .values rows.toList
  kw "SELECT"
  let distinct ← eatKw "DISTINCT"
  if !distinct then let _ ← eatKw "ALL"
  let cols ← parseResultCols
  let from_ ← if ← eatKw "FROM" then some <$> parseFrom else pure none
  let where_ ← if ← eatKw "WHERE" then some <$> parseExpr else pure none
  let (groupBy, having) ← if ← eatKw "GROUP" then do
      kw "BY"
      let g ← parseExprList
      let h ← if ← eatKw "HAVING" then some <$> parseExpr else pure none
      pure (g, h)
    else if ← eatKw "HAVING" then do pure ([], some (← parseExpr))
    else pure ([], none)
  let windows ← if ← eatKw "WINDOW" then do
      let one : P (Name × Window) := do
        let n ← name; kw "AS"; op "LP"; let w ← parseWindowBody; op "RP"; return (n, w)
      let mut l := #[← one]
      while ← eatOp "COMMA" do l := l.push (← one)
      pure l.toList
    else pure []
  return .select distinct cols from_ where_ groupBy having windows

partial def parseWith : P (List Cte × Bool) := do
  if !(← eatKw "WITH") then return ([], false)
  let rec_ ← eatKw "RECURSIVE"
  let one : P Cte := do
    let n ← name
    let cols ← if ← eatOp "LP" then do
        let mut l := #[← name]
        while ← eatOp "COMMA" do l := l.push (← name)
        op "RP"; pure l.toList
      else pure []
    kw "AS"
    let mat ← if ← eatKw "MATERIALIZED" then pure (some true)
      else if (← isKw "NOT") && (← isKwAt 1 "MATERIALIZED") then do advance; advance; pure (some false)
      else pure none
    op "LP"
    let q ← parseSelect
    op "RP"
    return .mk n cols mat q
  let mut l := #[← one]
  while ← eatOp "COMMA" do l := l.push (← one)
  return (l.toList, rec_)

partial def parseSelect : P Select := do
  let (ctes, rec_) ← parseWith
  let first ← parseSelectCore
  let mut rest := #[]
  repeat
    if ← eatKw "UNION" then
      let all ← eatKw "ALL"
      rest := rest.push (if all then CompoundOp.unionAll else .union, ← parseSelectCore)
    else if ← eatKw "INTERSECT" then rest := rest.push (.intersect, ← parseSelectCore)
    else if ← eatKw "EXCEPT" then rest := rest.push (.except, ← parseSelectCore)
    else break
  let orderBy ← if ← eatKw "ORDER" then do kw "BY"; parseOrderList else pure []
  let (limit, offset) ← if ← eatKw "LIMIT" then do
      let a ← parseExpr
      if ← eatKw "OFFSET" then pure (some a, some (← parseExpr))
      else if ← eatOp "COMMA" then do let b ← parseExpr; pure (some b, some a)
      else pure (some a, none)
    else pure (none, none)
  return .mk ctes rec_ first rest.toList orderBy limit offset

end

end Sql
