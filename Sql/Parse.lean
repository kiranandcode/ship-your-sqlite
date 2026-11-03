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

/-! ### Bounds

The parser is total: its mutually recursive functions take a `fuel` that
decreases on every call, and its loops are bounded by the tokens left. Both
bounds are chosen so that they are never reached (see `parseNextTok`); running
out is the internal error `exhausted`, distinct from every SQLite error. -/

/-- Running out of fuel or of loop iterations: never happens for the bounds
    the parser is started with (`parseNextTok`). -/
def exhausted {α} : P α := do
  throw ⟨"internal error: parser bound exhausted", (← get).src.size⟩

/-- The iterations of a parser loop (`for _ in steps do …`): at most one more
    than the tokens left when the loop starts. Every loop of the parser
    consumes at least one token in each iteration that does not leave it, so
    the bound is never reached. -/
structure Steps where
def steps : Steps := ⟨⟩

/-- `k` iterations at most of `f`. -/
def loopN {β} (k : Nat) (b : β) (f : Unit → β → P (ForInStep β)) : P β :=
  match k with
  | 0 => exhausted
  | k + 1 => do
    match ← f () b with
    | .done b => pure b
    | .yield b => loopN k b f

instance : ForIn P Steps Unit where
  forIn _ b f := do
    let s ← get
    loopN (s.toks.size - s.pos + 1) b f

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

/-- A type name: words, optionally `(n)` or `(n, m)`; returned as written. -/
def parseTypeName : P String := do
  let s0 := (← get).pos
  let mut any := false
  for _ in steps do
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

def parseAlias : P (Option Name) := do
  if ← eatKw "AS" then return some (← name)
  -- an alias may not be a keyword that can start the rest of the clause
  if (← isKw "JOIN_KW") then return none
  nameOpt

/-! The recursive descent. Each function takes the fuel first and passes one
less to every function of the block it calls (see `parseNextTok` for why the
initial fuel suffices). -/

mutual

def parseExpr : Nat → P Expr
  | 0 => exhausted
  | n + 1 => parseOr n

def parseOr : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseAnd n
  for _ in steps do
    if !(← eatKw "OR") then break
    e := .binop .or e (← parseAnd n)
  return e

def parseAnd : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseNot n
  for _ in steps do
    if !(← eatKw "AND") then break
    let r ← parseNot n
    -- sqlite3ExprAnd: an AND with an integer literal 0 on either side is FALSE
    -- at parse time (the other side is never resolved)
    let isZero (x : Expr) : Bool := match x with | .lit (.int 0) => true | _ => false
    e := if isZero e || isZero r then .lit (.int 0) else .binop .and e r
  return e

def parseNot : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  if ← eatKw "NOT" then return .unop .not (← parseNot n)
  parseEquality n

/-- IS, MATCH, LIKE, BETWEEN, IN, ISNULL, NOTNULL, NE, EQ (one level, left assoc) -/
def parseEquality : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseComparison n
  for _ in steps do
    if ← eatOp "EQ" then e := .binop .eq e (← parseComparison n)
    else if ← eatOp "NE" then e := .binop .ne e (← parseComparison n)
    else if ← eatKw "ISNULL" then e := .isNull false e
    else if ← eatKw "NOTNULL" then e := .isNull true e
    else if ← isKw "IS" then
      advance
      let neg ← eatKw "NOT"
      if ← eatKw "DISTINCT" then
        kw "FROM"
        let r ← parseComparison n
        e := .binop (if neg then .is else .isNot) e r
      else
        let r ← parseComparison n
        e := .binop (if neg then .isNot else .is) e r
    else if (← isKw "NOT") && ((← isKwAt 1 "NULL")) then
      advance; advance; e := .isNull true e
    else
      let neg := (← isKw "NOT") && ((← isKwAt 1 "BETWEEN") || (← isKwAt 1 "IN") ||
                  (← isKwAt 1 "LIKE_KW") || (← isKwAt 1 "MATCH"))
      if neg then advance
      if ← eatKw "BETWEEN" then
        let lo ← parseComparison n
        kw "AND"
        let hi ← parseComparison n
        e := .between neg e lo hi
      else if ← eatKw "IN" then
        e ← parseInRhs n neg e
      else if ← isKw "LIKE_KW" then
        let w ← kwWord
        advance
        let opk := if w == "GLOB" then LikeOp.glob else if w == "REGEXP" then .regexp else .like
        let pat ← parseComparison n
        let esc ← if ← eatKw "ESCAPE" then some <$> parseComparison n else pure none
        e := .like opk neg e pat esc
      else if ← eatKw "MATCH" then
        let pat ← parseComparison n
        e := .like .match_ neg e pat none
      else if neg then failHere
      else break
  return e

def parseInRhs : Nat → Bool → Expr → P Expr
  | 0, _, _ => exhausted
  | n + 1, neg, e => do
  if ← eatOp "LP" then
    if ← eatOp "RP" then return .inList neg e []
    if (← isKw "SELECT") || (← isKw "VALUES") || (← isKw "WITH") then
      let q ← parseSelect n
      op "RP"
      return .inSelect neg e q
    let items ← parseExprList n
    op "RP"
    return .inList neg e items
  else
    let n1 ← name
    let (sch, t) ← if ← eatOp "DOT" then do pure (some n1, ← name) else pure (none, n1)
    let args ← if ← eatOp "LP" then do
        if ← eatOp "RP" then pure [] else do let a ← parseExprList n; op "RP"; pure a
      else pure []
    return .inTable neg e sch t args

def parseComparison : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseEscape n
  for _ in steps do
    if ← eatOp "LT" then e := .binop .lt e (← parseEscape n)
    else if ← eatOp "LE" then e := .binop .le e (← parseEscape n)
    else if ← eatOp "GT" then e := .binop .gt e (← parseEscape n)
    else if ← eatOp "GE" then e := .binop .ge e (← parseEscape n)
    else break
  return e

def parseEscape : Nat → P Expr
  | 0 => exhausted
  | n + 1 => parseBits n

def parseBits : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseAdd n
  for _ in steps do
    if ← eatOp "BITAND" then e := .binop .bitand e (← parseAdd n)
    else if ← eatOp "BITOR" then e := .binop .bitor e (← parseAdd n)
    else if ← eatOp "LSHIFT" then e := .binop .shl e (← parseAdd n)
    else if ← eatOp "RSHIFT" then e := .binop .shr e (← parseAdd n)
    else break
  return e

def parseAdd : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseMul n
  for _ in steps do
    if ← eatOp "PLUS" then e := .binop .add e (← parseMul n)
    else if ← eatOp "MINUS" then e := .binop .sub e (← parseMul n)
    else break
  return e

def parseMul : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseConcat n
  for _ in steps do
    if ← eatOp "STAR" then e := .binop .mul e (← parseConcat n)
    else if ← eatOp "SLASH" then e := .binop .div e (← parseConcat n)
    else if ← eatOp "REM" then e := .binop .rem e (← parseConcat n)
    else break
  return e

def parseConcat : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseCollate n
  for _ in steps do
    if ← eatOp "CONCAT" then e := .binop .concat e (← parseCollate n)
    else if ← isOp "PTR" then
      let s ← get
      let t := s.toks[s.pos]!
      advance
      let two := t.stop - t.start == 3
      e := .binop (if two then .ptr2 else .ptr) e (← parseCollate n)
    else break
  return e

def parseCollate : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  let mut e ← parseUnary n
  for _ in steps do
    if !(← eatKw "COLLATE") then break
    e := .collate e (← name)
  return e

def parseUnary : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
  if ← eatOp "MINUS" then
    -- -9223372036854775808 is an integer
    match ← peek with
    | some t =>
      if t.tk == .integer && (← text t) == "9223372036854775808" then
        advance; return .lit (.int minI64)
      return .unop .neg (← parseUnary n)
    | none => return .unop .neg (← parseUnary n)
  if ← eatOp "PLUS" then return .unop .pos (← parseUnary n)
  if ← eatOp "BITNOT" then return .unop .bitnot (← parseUnary n)
  parsePrimary n

def parseExprList : Nat → P (List Expr)
  | 0 => exhausted
  | n + 1 => do
  let mut l := #[← parseExpr n]
  for _ in steps do
    if !(← eatOp "COMMA") then break
    l := l.push (← parseExpr n)
  return l.toList

def parsePrimary : Nat → P Expr
  | 0 => exhausted
  | n + 1 => do
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
      let q ← parseSelect n
      op "RP"
      return .subquery q
    let items ← parseExprList n
    op "RP"
    match items with
    | [e] => return e
    | _ => return .row items
  | .kw "NULL" => advance; return .lit .null
  | .kw "CAST" =>
    advance; op "LP"
    let e ← parseExpr n
    kw "AS"
    let ty ← parseTypeName
    op "RP"
    return .cast e ty
  | .kw "CASE" =>
    advance
    let base ← if ← isKw "WHEN" then pure none else some <$> parseExpr n
    let mut whens := #[]
    for _ in steps do
      if !(← eatKw "WHEN") then break
      let c ← parseExpr n
      kw "THEN"
      whens := whens.push (c, ← parseExpr n)
    if whens.isEmpty then failHere
    let els ← if ← eatKw "ELSE" then some <$> parseExpr n else pure none
    kw "END"
    return .case_ base whens.toList els
  | .kw "EXISTS" =>
    advance; op "LP"
    let q ← parseSelect n
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
    let msg ← if k == .ignore then pure none else do op "COMMA"; some <$> parseExpr n
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
    | some nm =>
      if ← isOp "LP" then
        advance
        parseCall n nm
      else if ← eatOp "DOT" then
        let n2 ← name
        if ← eatOp "DOT" then
          let n3 ← name
          return .col (some nm) (some n2) n3
        return .col none (some nm) n2
      else if t.tk == .id && (← text t).startsWith "\"" then return .dqcol nm
      else return .col none none nm

def parseCall : Nat → Name → P Expr
  | 0, _ => exhausted
  | n + 1, fname => do
  let mut distinct := false
  let mut args := []
  let mut star := false
  let mut orderBy := []
  if ← eatOp "STAR" then star := true; op "RP"
  else if ← eatOp "RP" then pure ()
  else
    distinct ← eatKw "DISTINCT"
    if !distinct then let _ ← eatKw "ALL"
    args ← parseExprList n
    if ← eatKw "ORDER" then
      kw "BY"
      orderBy ← parseOrderList n
    op "RP"
  let filter ← if ← eatKw "FILTER" then do
      op "LP"; kw "WHERE"; let e ← parseExpr n; op "RP"; pure (some e)
    else pure none
  let over ← if ← eatKw "OVER" then do
      if ← eatOp "LP" then do let w ← parseWindowBody n; op "RP"; pure (some w)
      else do let nm ← name; pure (some (Window.mk (some nm) [] [] none))
    else pure none
  return .call fname distinct args star orderBy filter over

def parseWindowBody : Nat → P Window
  | 0 => exhausted
  | n + 1 => do
  let base ← if (← isKw "PARTITION") || (← isKw "ORDER") || (← isKw "RANGE") || (← isKw "ROWS") || (← isKw "GROUPS") || (← isOp "RP") then pure none
    else nameOpt
  let part ← if ← eatKw "PARTITION" then do kw "BY"; parseExprList n else pure []
  let ord ← if ← eatKw "ORDER" then do kw "BY"; parseOrderList n else pure []
  let frame ← if (← isKw "RANGE") || (← isKw "ROWS") || (← isKw "GROUPS") then some <$> parseFrame n else pure none
  return .mk base part ord frame

def parseFrame : Nat → P Frame
  | 0 => exhausted
  | n + 1 => do
  let unit ← if ← eatKw "RANGE" then pure FrameUnit.range else if ← eatKw "ROWS" then pure .rows
    else do kw "GROUPS"; pure .groups
  let bound : P FrameBound := do
    if ← eatKw "UNBOUNDED" then
      if ← eatKw "PRECEDING" then return .unboundedPreceding
      kw "FOLLOWING"; return .unboundedFollowing
    if ← eatKw "CURRENT" then kw "ROW"; return .currentRow
    let e ← parseExpr n
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

def parseOrderList : Nat → P (List OrderTerm)
  | 0 => exhausted
  | n + 1 => do
  let one : P OrderTerm := do
    let e ← parseExpr n
    let dir ← if ← eatKw "DESC" then pure SortDir.desc else do let _ ← eatKw "ASC"; pure .asc
    let nulls ← if ← eatKw "NULLS" then do
        if ← eatKw "FIRST" then pure NullsOrder.first else do kw "LAST"; pure .last
      else pure .default
    return .mk e dir nulls
  let mut l := #[← one]
  for _ in steps do
    if !(← eatOp "COMMA") then break
    l := l.push (← one)
  return l.toList

def parseResultCols : Nat → P (List ResultCol)
  | 0 => exhausted
  | n + 1 => do
  let one : P ResultCol := do
    if ← eatOp "STAR" then return .star
    -- table.*
    match ← peekAt 0, ← peekAt 1, ← peekAt 2 with
    | some _, some { tk := .op "DOT", .. }, some { tk := .op "STAR", .. } =>
      let nm ← name; advance; advance; return .tableStar nm
    | _, _, _ =>
      let s0 := (← get).pos
      let e ← parseExpr n
      let txt ← spanText s0 (← get).pos
      if ← eatKw "AS" then return .expr e (some (← name)) txt
      match ← nameOpt with
      | some a => return .expr e (some a) txt
      | none => return .expr e none txt
  let mut l := #[← one]
  for _ in steps do
    if !(← eatOp "COMMA") then break
    l := l.push (← one)
  return l.toList

def parseFromTerm : Nat → P FromItem
  | 0 => exhausted
  | n + 1 => do
  if ← eatOp "LP" then
    if (← isKw "SELECT") || (← isKw "VALUES") || (← isKw "WITH") then
      let q ← parseSelect n
      op "RP"
      return .subquery q (← parseAlias)
    let f ← parseFrom n
    op "RP"
    match ← parseAlias with
    | some a => return .subquery (.mk [] false (.select false [.star] (some f) none [] none []) [] [] none none) (some a)
    | none => return f
  let n1 ← name
  let (sch, nm) ← if ← eatOp "DOT" then do pure (some n1, ← name) else pure (none, n1)
  if ← eatOp "LP" then
    let args ← if ← eatOp "RP" then pure [] else do let a ← parseExprList n; op "RP"; pure a
    return .tableFn sch nm args (← parseAlias)
  let alias ← parseAlias
  let indexed ← if ← eatKw "INDEXED" then do kw "BY"; pure (some (some (← name)))
    else if (← isKw "NOT") && (← isKwAt 1 "INDEXED") then do advance; advance; pure (some none)
    else pure none
  return .table sch nm alias indexed

def parseFrom : Nat → P FromItem
  | 0 => exhausted
  | n + 1 => do
  let mut left ← parseFromTerm n
  for _ in steps do
    let mut kind := JoinKind.inner
    let mut natural := false
    if ← eatOp "COMMA" then
      kind := .cross
    else if (← isKw "JOIN_KW") || (← isKw "JOIN") then
      -- [NATURAL] [LEFT|RIGHT|FULL] [OUTER] | INNER | CROSS  JOIN
      let mut words := #[]
      for _ in steps do
        if !(← isKw "JOIN_KW") then break
        words := words.push (← kwWord); advance
      kw "JOIN"
      natural := words.contains "NATURAL"
      kind := if words.contains "LEFT" then .left else if words.contains "RIGHT" then .right
        else if words.contains "FULL" then .full else if words.contains "CROSS" then .cross else .inner
      if words.contains "CROSS" then kind := .inner
    else break
    let right ← parseFromTerm n
    let on ← if ← eatKw "ON" then some <$> parseExpr n else pure none
    let usingCols ← if ← eatKw "USING" then do
        op "LP"
        let mut l := #[← name]
        for _ in steps do
          if !(← eatOp "COMMA") then break
          l := l.push (← name)
        op "RP"; pure l.toList
      else pure []
    left := .join left kind natural right on usingCols
  return left

def parseSelectCore : Nat → P SelectCore
  | 0 => exhausted
  | n + 1 => do
  if ← eatKw "VALUES" then
    let row : P (List Expr) := do op "LP"; let l ← parseExprList n; op "RP"; return l
    let mut rows := #[← row]
    for _ in steps do
      if !(← eatOp "COMMA") then break
      rows := rows.push (← row)
    return .values rows.toList
  kw "SELECT"
  let distinct ← eatKw "DISTINCT"
  if !distinct then let _ ← eatKw "ALL"
  let cols ← parseResultCols n
  let from_ ← if ← eatKw "FROM" then some <$> parseFrom n else pure none
  let where_ ← if ← eatKw "WHERE" then some <$> parseExpr n else pure none
  let (groupBy, having) ← if ← eatKw "GROUP" then do
      kw "BY"
      let g ← parseExprList n
      let h ← if ← eatKw "HAVING" then some <$> parseExpr n else pure none
      pure (g, h)
    else if ← eatKw "HAVING" then do pure ([], some (← parseExpr n))
    else pure ([], none)
  let windows ← if ← eatKw "WINDOW" then do
      let one : P (Name × Window) := do
        let nm ← name; kw "AS"; op "LP"; let w ← parseWindowBody n; op "RP"; return (nm, w)
      let mut l := #[← one]
      for _ in steps do
        if !(← eatOp "COMMA") then break
        l := l.push (← one)
      pure l.toList
    else pure []
  return .select distinct cols from_ where_ groupBy having windows

def parseWith : Nat → P (List Cte × Bool)
  | 0 => exhausted
  | n + 1 => do
  if !(← eatKw "WITH") then return ([], false)
  let rec_ ← eatKw "RECURSIVE"
  let one : P Cte := do
    let nm ← name
    let cols ← if ← eatOp "LP" then do
        let mut l := #[← name]
        for _ in steps do
          if !(← eatOp "COMMA") then break
          l := l.push (← name)
        op "RP"; pure l.toList
      else pure []
    kw "AS"
    let mat ← if ← eatKw "MATERIALIZED" then pure (some true)
      else if (← isKw "NOT") && (← isKwAt 1 "MATERIALIZED") then do advance; advance; pure (some false)
      else pure none
    op "LP"
    let q ← parseSelect n
    op "RP"
    return .mk nm cols mat q
  let mut l := #[← one]
  for _ in steps do
    if !(← eatOp "COMMA") then break
    l := l.push (← one)
  return (l.toList, rec_)

def parseSelect : Nat → P Select
  | 0 => exhausted
  | n + 1 => do
  let (ctes, rec_) ← parseWith n
  let first ← parseSelectCore n
  let mut rest := #[]
  for _ in steps do
    if ← eatKw "UNION" then
      let all ← eatKw "ALL"
      rest := rest.push (if all then CompoundOp.unionAll else .union, ← parseSelectCore n)
    else if ← eatKw "INTERSECT" then rest := rest.push (.intersect, ← parseSelectCore n)
    else if ← eatKw "EXCEPT" then rest := rest.push (.except, ← parseSelectCore n)
    else break
  let orderBy ← if ← eatKw "ORDER" then do kw "BY"; parseOrderList n else pure []
  let (limit, offset) ← if ← eatKw "LIMIT" then do
      let a ← parseExpr n
      if ← eatKw "OFFSET" then pure (some a, some (← parseExpr n))
      else if ← eatOp "COMMA" then do let b ← parseExpr n; pure (some b, some a)
      else pure (some a, none)
    else pure (none, none)
  return .mk ctes rec_ first rest.toList orderBy limit offset

end

end Sql
