/-
  The JSON SQL functions (json.c: `jsonParseFuncArg`, `jsonReturnFromBlob`,
  `jsonFunctionArgToBlob`, `jsonAppendSqlValue`, the `json*Func` scalar
  functions, the aggregates and the `json_each`/`json_tree` cursor).

  Results carry the JSON subtype (`sqlite3_result_subtype(ctx, 'J')`) as a
  Bool next to the value. The parse cache of json.c (`JsonCache`: four
  entries per statement mapping JSON text to its JSONB, LRU) is the explicit
  state `Cache` of `FM`; it is observable, because an edit function
  (`json_set`, `json_remove`, `json_patch`, …) caches its *output* text with
  the edited blob, and that blob (with TEXTRAW labels, widened headers) is
  what a later `jsonb_*` call on the same text in the same statement returns.
-/
import Sql.Json.Edit
import Sql.Db

namespace Sql.Json

structure CacheEntry where
  json : ByteArray
  b : ByteArray
  nonstd : Bool
  deriving Inhabited

/-- `JsonCache`: oldest first, bat most 4 entries. -/
structure Cache where
  entries : Array CacheEntry := #[]
  deriving Inhabited

abbrev FM := StateT Cache (Except Err)

/-- An SQLITE_ERROR with a message. -/
def mkErr (m : String) : Err := { code := SQLITE_ERROR, msg := m }

def fail {α} (msg : String) : FM α := throw (mkErr msg)

def lossy (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => String.ofList (b.data.toList.map fun c => Char.ofNat c.toNat)

/-- `%Q` -/
def sqlQuote (b : ByteArray) : String :=
  "'" ++ (lossy b).replace "'" "''" ++ "'"

def malformed {α} : FM α := fail "malformed JSON"

def cacheSearch (z : ByteArray) : FM (Option CacheEntry) := do
  let c ← get
  match c.entries.findIdx? (fun e => e.json.data == z.data) with
  | none => return none
  | some i =>
    let e := c.entries[i]!
    set { c with entries := (c.entries.eraseIdx! i).push e }
    return some e

def cacheInsert (e : CacheEntry) : FM Unit := modify fun c =>
  let es := if c.entries.size ≥ 4 then c.entries.extract 1 c.entries.size else c.entries
  { c with entries := es.push e }

/-- The text of a value (`sqlite3_value_text`). -/
def vtext (v : Value) : ByteArray := v.toText?.getD .empty

/-- `jsonParseFuncArg` (flags EDITABLE / NOCACHE; KEEPERROR is `parseKeep`).
    `none` for SQL NULL. -/
def parseArg (v : Value) (noCache : Bool := false) : FM (Option JP) := do
  match v with
  | .null => return none
  | _ =>
  if !noCache then
    if let .text z := v then
      if let some e ← cacheSearch z then
        return some { b := e.b, nonstd := e.nonstd }
  if let .blob b := v then
    if isJsonb b then return some { b }
  let z := vtext v
  if z.size == 0 then malformed
  match convertText (cstr z) with
  | .error _ => malformed
  | .ok st =>
    if !noCache then cacheInsert { json := z, b := st.out, nonstd := st.nonstd }
    return some { b := st.out, nonstd := st.nonstd }

/-- The JSON of a REAL (`%!0.17g`). -/
def realJson (r : Float) : String :=
  if r.isInf then (if r < 0 then "-9.0e+999" else "9.0e+999") else Real.render r

/-- Does a text argument flagged as JSON-subtyped really hold JSON?
    (`exprIsJson` is a static approximation; a subtyped value is always
    canonical JSON, so text that is not is treated as a plain string.) -/
def subtypeOk (v : Value) (sub : Bool) : Bool :=
  sub && match v with
    | .text z => match convertText (cstr z) with
      | .ok st => !st.nonstd
      | .error _ => false
    | _ => false

/-- `jsonAppendSqlValue` -/
def appendSql (s : JStr) (v : Value) (sub : Bool) : JStr :=
  match v with
  | .null => s.adds "null"
  | .real r => { s.adds (realJson r) with printf := true }
  | .int i => s.adds (toString i)
  | .text z => if subtypeOk v sub then s.add z else s.add (quoteString z)
  | .blob b =>
    if isJsonb b then (blobToText { b } 0 s).2.1
    else if s.err == 0 then { s with err := eERR, msg := some "JSON cannot hold BLOB values", buf := .empty }
    else s

/-- `jsonReturnString`: the text (or, for a `jsonb_` function, its JSONB). -/
def returnString (s : JStr) (asBlob : Bool) : FM Value := do
  if s.err == 0 then
    return if asBlob then .blob (textToBlob s.buf) else .text s.buf
  if s.err &&& eTOODEEP != 0 then fail (s.msg.getD "JSON nested too deep")
  if s.err &&& eMALFORMED != 0 then malformed
  fail (s.msg.getD "malformed JSON")

/-- `jsonReturnParse`; `editable`: the parse is a private copy (its output
    text is then cached with this blob, when the text is a heap string). -/
def returnParse (p : JP) (asBlob : Bool) (editable : Bool) : FM (Value × Bool) := do
  if asBlob then return (.blob p.b, false)
  let (_, s, _) := blobToText { b := p.b, delta := 0, depth := p.iDepth } 0 {}
  let v ← returnString s false
  if editable && s.heap then cacheInsert { json := s.buf, b := p.b, nonstd := p.nonstd }
  return (v, true)

/-! ## Integers in JSON (`sqlite3DecOrHexToI64`, `sqlite3Atoi64`) -/

def two63 : Nat := 2 ^ 63
def two64 : Nat := 2 ^ 64

def lexLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | x :: xs, y :: ys => if x < y then true else if x > y then false else lexLt xs ys

/-- `sqlite3Atoi64(z, n)`: (rc, value) -/
def atoi64C (z : ByteArray) : Int × Int := Id.run do
  let n := z.size
  let mut k := 0
  while k < n && isSpaceS (bat z k) do k := k + 1
  let mut neg := false
  if k < n then
    if bat z k == 45 then neg := true; k := k + 1
    else if bat z k == 43 then k := k + 1
  let zStart := k
  while k < n && bat z k == 48 do k := k + 1
  let zNum := k
  let mut u : Nat := 0
  let mut i := 0
  while zNum + i < n && isDigit (bat z (zNum+i)) do
    u := (u * 10 + (bat z (zNum+i) - 48).toNat) % two64
    i := i + 1
  let mut v : Int := if u > two63 - 1 then (if neg then -(two63 : Int) else two63 - 1)
    else if neg then -(u : Int) else u
  let mut rc : Int := 0
  if i == 0 && zStart == zNum then rc := -1
  else if zNum + i < n then
    let mut jj := zNum + i
    while jj < n do
      if !isSpaceS (bat z jj) then rc := 1; break
      jj := jj + 1
  if i < 19 then return (rc, v)
  let digits := (z.extract zNum (zNum + 19)).data.toList
  let cmp : Int := if i > 19 then 1 else
    let p := "9223372036854775808".toUTF8.data.toList
    if digits == p then 0 else if lexLt digits p then -1 else 1
  if cmp < 0 then return (rc, v)
  v := if neg then -(two63 : Int) else two63 - 1
  if cmp > 0 then return (2, v)
  return (if neg then rc else 3, v)

/-- `sqlite3DecOrHexToI64` on a NUL-free string: (rc, i64 value). -/
def decOrHexToI64 (z : ByteArray) : Int × Int := Id.run do
  if bat z 0 == 48 && (bat z 1 == 120 || bat z 1 == 88) then
    let mut i := 2
    while bat z i == 48 do i := i + 1
    let mut k := i
    let mut u : Nat := 0
    while isXdigit (bat z k) do
      u := (u * 16 + hexToInt (bat z k)) % two64
      k := k + 1
    let v : Int := if u ≥ two63 then (u : Int) - two64 else u
    if k - i > 16 then return (2, v)
    if bat z k != 0 then return (1, v)
    return (0, v)
  else
    let mut n := 0
    while n < z.size && (let c := bat z n; c == 43 || c == 45 || c == 32 || c == 10 || c == 9 || isDigit c) do
      n := n + 1
    if n < z.size then n := n + 1
    return atoi64C (z.extract 0 n)

/-- `sqlite3AtoF` succeeding on the whole string. -/
def atofWhole (z : ByteArray) : Option Float :=
  let a := atof z
  if a.digit && a.whole then some a.value else none

/-- Encode a code point as UTF-8 the way `jsonReturnFromBlob` does. -/
def utf8Enc (v : Nat) : ByteArray :=
  if v ≤ 0x7f then ⟨#[v.toUInt8]⟩
  else if v ≤ 0x7ff then ⟨#[(0xc0 ||| (v >>> 6)).toUInt8, (0x80 ||| (v &&& 0x3f)).toUInt8]⟩
  else if v < 0x10000 then
    ⟨#[(0xe0 ||| (v >>> 12)).toUInt8, (0x80 ||| ((v >>> 6) &&& 0x3f)).toUInt8, (0x80 ||| (v &&& 0x3f)).toUInt8]⟩
  else if v == invalidChar then .empty
  else ⟨#[(0xf0 ||| (v >>> 18)).toUInt8, (0x80 ||| ((v >>> 12) &&& 0x3f)).toUInt8,
          (0x80 ||| ((v >>> 6) &&& 0x3f)).toUInt8, (0x80 ||| (v &&& 0x3f)).toUInt8]⟩

/-- Unescape a TEXTJ/TEXT5 payload. -/
def unescapeText (z : ByteArray) : ByteArray := Id.run do
  let sz := z.size
  let mut out := ByteArray.empty
  let mut i := 0
  while i < sz do
    let c := bat z i
    if c == 92 then
      let (v, k) := unescapeOne z i (sz - i)
      out := out ++ utf8Enc v
      i := i + k
    else
      out := out.push c
      i := i + 1
  return out

/-- `jsonReturnFromBlob`: the SQL value of node `i`; containers as JSON
    text (`mode` 1) or JSONB (`mode` 2). -/
def returnFromBlob (p : JP) (i : Nat) (mode : Nat) : Except Err Value := do
  let mal : Except Err Value := throw (mkErr "malformed JSON")
  let (n, sz) := p.psize i
  if n == 0 then return ← mal
  let toDouble (s : ByteArray) : Except Err Value :=
    match atofWhole (cstr s) with
    | some r => pure (.real r)
    | none => throw (mkErr "malformed JSON")
  match (p.typ i).toNat with
  | 0 => if sz != 0 then mal else pure .null
  | 1 => if sz != 0 then mal else pure (.int 1)
  | 2 => if sz != 0 then mal else pure (.int 0)
  | 3 | 4 =>
    if sz == 0 then return ← mal
    let neg := bat p.b (i+n) == 45
    if neg && sz < 2 then return ← mal
    let z := cstr (if neg then sub p.b (i+n+1) (sz-1) else sub p.b (i+n) sz)
    let (rc, v) := decOrHexToI64 z
    if rc == 0 then
      if v < 0 then
        let r := intToRealN ((v + two64).toNat)
        pure (.real (if neg then -r else r))
      else pure (.int (if neg then -v else v))
    else if rc == 3 && neg then pure (.int (-(two63 : Int)))
    else if rc == 1 then mal
    else toDouble (sub p.b (i+n) sz)
  | 5 | 6 => if sz == 0 then mal else toDouble (sub p.b (i+n) sz)
  | 7 | 10 => pure (.text (sub p.b (i+n) sz))
  | 8 | 9 => pure (.text (unescapeText (sub p.b (i+n) sz)))
  | 11 | 12 =>
    if mode == 2 then pure (.blob (sub p.b i (n+sz)))
    else
      let (_, s, _) := blobToText { b := sub p.b i (n+sz) } 0 {}
      if s.err == 0 then pure (.text s.buf)
      else if s.err &&& eTOODEEP != 0 then throw (mkErr "JSON nested too deep")
      else mal
  | _ => mal
where
  intToRealN (u : Nat) : Float := Real.roundScaled u false 0

/-- `jsonFunctionArgToBlob`: an SQL argument as JSONB. -/
def argToBlob (v : Value) (sub : Bool) : FM ByteArray := do
  match v with
  | .null => return ⟨#[tNULL]⟩
  | .blob b => if isJsonb b then return b else fail "JSON cannot hold BLOB values"
  | .text z =>
    if subtypeOk v sub then
      match convertText (cstr z) with
      | .ok st => return st.out
      | .error _ => malformed
    else return node tTEXTRAW z
  | .real r =>
    if r.isInf then return node tFLOAT (bytesOf (if r < 0 then "-9e999" else "9e999"))
    return node tFLOAT (bytesOf (Real.render r))
  | .int i => return node tINT (bytesOf (toString i))

/-- `jsonBadPathError` -/
def badPath {α} (zPath : ByteArray) (rc : Nat) : FM α :=
  if rc == lNOTARRAY then fail s!"not an array element: {sqlQuote zPath}"
  else if rc == lERROR then malformed
  else if rc == lTOODEEP then fail "JSON path too deep"
  else fail s!"bad JSON path: {sqlQuote zPath}"

def pathOf (v : Value) : Option ByteArray :=
  match v with
  | .null => none
  | _ => some (cstr (vtext v))

/-! ## Scalar functions -/

abbrev Args := List (Value × Bool)

def wrongArgs {α} (name : String) : FM α := fail s!"wrong number of arguments to function {name}()"

def argAt (args : Args) (i : Nat) : Value × Bool := args[i]?.getD (.null, false)

/-- `jsonInsertIntoBlob` -/
def insertIntoBlob (args : Args) (eEdit : Nat) (asBlob : Bool) : FM (Option (Value × Bool)) := do
  let argc := args.length
  let editable := argc != 1
  let some p0 ← parseArg (argAt args 0).1 | return none
  let mut p := p0
  let mut i := 1
  while i + 1 < argc do
    let (pv, _) := argAt args i
    if pv.isNull then i := i + 2; continue
    let zPath := (pathOf pv).getD .empty
    if bat zPath 0 != 36 then badPath zPath 0
    let (vv, vs) := argAt args (i+1)
    let ax ← argToBlob vv vs
    let mut rc := 0
    if bat zPath 1 == 0 then
      if eEdit == eREPL || eEdit == eSET then
        p := p.edit 0 p.b.size (some ax) ax.size
      rc := 0
    else
      p := { p with eEdit, ins := ax, delta := 0, iDepth := 0 }
      let (r, p') := lookupStep p 0 zPath 1 0
      rc := r; p := p'
    i := i + 2
    if rc == lNOTFOUND then continue
    if isLookupErr rc then badPath zPath rc
  return some (← returnParse p asBlob editable)

def extractFunc (args : Args) (flags : Nat) : FM (Option (Value × Bool)) := do
  let fJSON := 1
  let fSQL := 2
  let fBLOB := 16
  let argc := args.length
  if argc < 2 then return none
  let some p ← parseArg (argAt args 0).1 | return none
  let mut jx : JStr := {}
  if argc > 2 then jx := jx.addc 91
  for k in [1:argc] do
    let (pv, _) := argAt args k
    let some zPath := pathOf pv | return none
    let mut j := 0
    if bat zPath 0 == 36 then
      j := (lookupStep p 0 zPath 1 0).1
    else if flags &&& 3 != 0 then
      let nPath := zPath.size
      let built : ByteArray :=
        match pv with
        | .int _ => (bytesOf "[" ++ (if bat zPath 0 == 45 then bytesOf "#" else .empty)) ++ zPath ++ bytesOf "]"
        | _ =>
          if zPath.data.all (fun c => isAlnum c || c == 95) then bytesOf "." ++ zPath
          else if bat zPath 0 == 91 && nPath ≥ 3 && bat zPath (nPath - 1) == 93 then zPath
          else bytesOf ".\"" ++ zPath ++ bytesOf "\""
      j := (lookupStep p 0 built 0 0).1
    else
      badPath zPath 0
    if j < p.b.size then
      if argc == 2 then
        if flags &&& fJSON != 0 then
          let (_, s, _) := blobToText { b := p.b, delta := p.delta, depth := p.iDepth } j {}
          return some (← returnString s false, true)
        else
          let v ← liftExcept (returnFromBlob p j (if flags &&& fBLOB != 0 then 2 else 1))
          let sub := flags &&& (fSQL ||| fBLOB) == 0 && p.typ j ≥ tARRAY
          return some (v, sub)
      else
        if jx.buf.size > 0 && bat jx.buf (jx.buf.size - 1) != 91 && bat jx.buf (jx.buf.size - 1) != 123 then
          jx := jx.addc 44
        jx := (blobToText { b := p.b, delta := p.delta, depth := p.iDepth } j jx).2.1
    else if j == lNOTFOUND then
      if argc == 2 then return none
      if jx.buf.size > 0 && bat jx.buf (jx.buf.size - 1) != 91 && bat jx.buf (jx.buf.size - 1) != 123 then
        jx := jx.addc 44
      jx := jx.adds "null"
    else badPath zPath j
  jx := jx.addc 93
  let v ← returnString jx (flags &&& fBLOB != 0)
  return some (v, flags &&& fBLOB == 0)
where
  liftExcept {α} (e : Except Err α) : FM α := match e with
    | .ok a => pure a
    | .error x => throw x

def appendSep (s : JStr) : JStr :=
  if s.buf.size == 0 then s
  else
    let c := bat s.buf (s.buf.size - 1)
    if c == 91 || c == 123 then s else s.addc 44

def textArgs (name : String) (args : Args) (lo hi : Nat) : FM Unit :=
  if args.length < lo || args.length > hi then wrongArgs name else pure ()

/-- `jsonValidFunc` -/
def validFunc (args : Args) : FM (Option (Value × Bool)) := do
  let mut flags := 1
  if args.length == 2 then
    let f := (argAt args 1).1.toInt
    if f < 1 || f > 15 then fail "FLAGS parameter to json_valid() must be between 1 and 15"
    flags := f.toNat % 16
  let v := (argAt args 0).1
  if v.isNull then return none
  if let .blob b := v then
    if isJsonb b then
      let res := if flags &&& 4 != 0 then 1 else if flags &&& 8 != 0 then (if validityCheck b 0 b.size 1 == 0 then 1 else 0) else 0
      return some (.int res, false)
  if flags &&& 3 == 0 then return some (.int 0, false)
  let z := vtext v
  if z.size == 0 then return some (.int 0, false)
  match convertText (cstr z) with
  | .error _ => return some (.int 0, false)
  | .ok st => return some (.int (if flags &&& 2 != 0 || !st.nonstd then 1 else 0), false)

/-- `jsonErrorFunc` -/
def errorPosFunc (v : Value) : FM (Option (Value × Bool)) := do
  if let .blob b := v then
    if isJsonb b then return some (.int (validityCheck b 0 b.size 1), false)
  if v.isNull then return none
  let z := cstr (vtext v)
  match convertText z with
  | .ok _ => return some (.int 0, false)
  | .error st =>
    let mut pos : Nat := 0
    let mut k := 0
    while k < st.iErr && bat z k != 0 do
      if (bat z k) &&& 0xc0 != 0x80 then pos := pos + 1
      k := k + 1
    return some (.int (pos + 1), false)

/-- The scalar JSON functions: `none` if `name` is not one of them; the
    inner `Option` is an SQL NULL result. -/
def scalarF (name : String) (args : Args) : Option (FM (Option (Value × Bool))) :=
  let argc := args.length
  let a0 := (argAt args 0).1
  match name with
  | "json" | "jsonb" => some do
    if argc != 1 then wrongArgs name
    let some p ← parseArg a0 | return none
    returnParse p (name == "jsonb") false
  | "json_array" | "jsonb_array" => some do
    let mut s : JStr := ({} : JStr).addc 91
    for (v, sb) in args do
      s := appendSql (appendSep s) v sb
    s := s.addc 93
    let v ← returnString s (name == "jsonb_array")
    return some (v, true)
  | "json_array_length" => some do
    textArgs name args 1 2
    let some p ← parseArg a0 | return none
    let mut i := 0
    if argc == 2 then
      let some zPath := pathOf (argAt args 1).1 | return none
      let (r, _) := lookupStep p 0 (if bat zPath 0 == 36 then zPath else bytesOf "$@") 1 0
      if isLookupErr r then
        if r == lNOTFOUND then return none
        badPath zPath r
      i := r
    let cnt := if p.typ i == tARRAY then p.arrayCount i else 0
    return some (.int cnt, false)
  | "json_error_position" => some do
    if argc != 1 then wrongArgs name
    errorPosFunc a0
  | "json_extract" => some (extractFunc args 0)
  | "jsonb_extract" => some (extractFunc args 16)
  | "->" => some (extractFunc args 1)
  | "->>" => some (extractFunc args 2)
  | "json_insert" | "jsonb_insert" | "json_set" | "jsonb_set" | "json_array_insert" | "jsonb_array_insert" => some do
    if argc < 1 then return none
    let base := if name.startsWith "jsonb_" then name.drop 6 else name.drop 5
    if argc % 2 == 0 then fail s!"json_{base}() needs an odd number of arguments"
    let e := if base == "insert" then eINS else if base == "set" then eSET else eAINS
    insertIntoBlob args e (name.startsWith "jsonb_")
  | "json_replace" | "jsonb_replace" => some do
    if argc < 1 then return none
    if argc % 2 == 0 then fail "json_replace() needs an odd number of arguments"
    insertIntoBlob args eREPL (name == "jsonb_replace")
  | "json_object" | "jsonb_object" => some do
    if argc % 2 == 1 then fail "json_object() requires an even number of arguments"
    let mut s : JStr := ({} : JStr).addc 123
    let mut k := 0
    while k < argc do
      let (lab, _) := argAt args k
      let .text z := lab | fail "json_object() labels must be TEXT"
      s := (appendSep s).add (quoteString z) |>.addc 58
      let (v, sb) := argAt args (k+1)
      s := appendSql s v sb
      k := k + 2
    s := s.addc 125
    let v ← returnString s (name == "jsonb_object")
    return some (v, true)
  | "json_patch" | "jsonb_patch" => some do
    if argc != 2 then wrongArgs name
    let some t ← parseArg a0 | return none
    let some pp ← parseArg (argAt args 1).1 | return none
    let (rc, t) := mergePatch t 0 pp.b 0 0
    if rc == mOK then returnParse t (name == "jsonb_patch") true
    else if rc == mTOODEEP then fail "JSON nested too deep"
    else malformed
  | "json_pretty" => some do
    textArgs name args 1 2
    let some p ← parseArg a0 | return none
    let indent := if argc == 1 then bytesOf "    " else
      match (argAt args 1).1 with
      | .null => bytesOf "    "
      | v => cstr (vtext v)
    let (_, s, _) := blobToPretty indent 0 { b := p.b, delta := p.delta, depth := p.iDepth } 0 {}
    return some (← returnString s false, false)
  | "json_quote" => some do
    if argc != 1 then wrongArgs name
    let (v, sb) := argAt args 0
    let r ← returnString (appendSql {} v sb) false
    return some (r, true)
  | "json_remove" | "jsonb_remove" => some do
    if argc < 1 then return none
    let some p0 ← parseArg a0 | return none
    let mut p := p0
    for k in [1:argc] do
      let some zPath := pathOf (argAt args k).1 | return none
      if bat zPath 0 != 36 then badPath zPath 0
      if bat zPath 1 == 0 then return none
      p := { p with eEdit := eDEL, delta := 0 }
      let (rc, p') := lookupStep p 0 zPath 1 0
      p := p'
      if isLookupErr rc then
        if rc == lNOTFOUND then continue
        badPath zPath rc
    returnParse p (name == "jsonb_remove") (argc > 1)
  | "json_type" => some do
    textArgs name args 1 2
    let some p ← parseArg a0 | return none
    let mut i := 0
    if argc == 2 then
      let some zPath := pathOf (argAt args 1).1 | return none
      if bat zPath 0 != 36 then badPath zPath 0
      let (r, _) := lookupStep p 0 zPath 1 0
      if isLookupErr r then
        if r == lNOTFOUND then return none
        badPath zPath r
      i := r
    return some (.ofString (typeName (p.typ i)), false)
  | "json_valid" => some do
    textArgs name args 1 2
    validFunc args
  | _ => none

/-! ## Aggregates -/

def aggregateF (name : String) (rows : List Args) : Option (FM (Value × Bool)) :=
  match name with
  | "json_group_array" | "jsonb_group_array" => some do
    let asBlob := name == "jsonb_group_array"
    if rows.isEmpty then
      return (if asBlob then .blob ⟨#[tARRAY]⟩ else .ofString "[]", true)
    let mut s : JStr := ({} : JStr).addc 91
    let mut first := true
    for r in rows do
      if r.length != 1 then wrongArgs name
      if !first && s.buf.size > 1 then s := s.addc 44
      first := false
      let (v, sb) := argAt r 0
      s := appendSql s v sb
    s := s.addc 93
    return (← returnString s asBlob, true)
  | "json_group_object" | "jsonb_group_object" => some do
    let asBlob := name == "jsonb_group_object"
    if rows.isEmpty then
      return (if asBlob then .blob ⟨#[tOBJECT]⟩ else .ofString "{}", true)
    let mut s : JStr := ({} : JStr).addc 123
    let mut first := true
    for r in rows do
      if r.length != 2 then wrongArgs name
      if !first && s.buf.size > 1 then s := s.addc 44
      first := false
      let (lab, _) := argAt r 0
      match lab with
      | .null =>
        s := { s with buf := s.buf.set! 0 64 }
        s := s.addc 64
      | _ =>
        s := (s.add (quoteString (cstr (vtext lab)))).addc 58
        let (v, sb) := argAt r 1
        s := appendSql s v sb
    s := s.addc 125
    if s.err != 0 then return (← returnString s false, true)
    if bat s.buf 0 != 123 then
      let z := s.buf
      let mut out := ByteArray.empty.push 123
      let mut inStr := false
      let mut i := 1
      while i < z.size do
        let c := bat z i
        if c == 34 then inStr := !inStr; out := out.push 34
        else if c == 92 then
          out := out.push 92
          i := i + 1
          out := out.push (bat z i)
        else if c == 64 && !inStr then
          if bat z (i+1) == 44 then i := i + 1
          else if bat out (out.size - 1) == 44 then out := out.extract 0 (out.size - 1)
        else out := out.push c
        i := i + 1
      s := { s with buf := out }
    return (← returnString s asBlob, true)
  | _ => none

/-! ## json_each / json_tree -/

structure Parent where
  iHead : Nat
  iValue : Nat
  iEnd : Nat
  nPath : Nat
  iKey : Int
  deriving Inhabited

structure Cur where
  p : JP
  zJson : Option ByteArray
  i : Nat := 0
  iEnd : Nat := 0
  nRoot : Nat := 0
  eType : UInt8 := 0
  recursive : Bool
  mode : Nat
  parents : Array Parent := #[]
  path : ByteArray := .empty
  rowid : Nat := 0

def Cur.top (c : Cur) : Parent := c.parents[c.parents.size - 1]!

def Cur.skipLabel (c : Cur) : Nat :=
  if c.eType == tOBJECT then
    let (n, sz) := c.p.psize c.i
    let r := c.i + n + sz
    if r ≥ c.p.b.size then c.i else r
  else c.i

def Cur.pathName (c : Cur) : ByteArray :=
  if c.eType == tARRAY then bytesOf s!"[{c.top.iKey}]"
  else
    let (n, sz) := c.p.psize c.i
    let z := sub c.p.b (c.i + n) sz
    let needQuote := sz == 0 || !isAlpha (bat z 0) || !(z.data.all isAlnum)
    let z := cstr z
    if needQuote then bytesOf ".\"" ++ z ++ bytesOf "\"" else bytesOf "." ++ z

def Cur.next (c : Cur) : Except Err Cur := do
  let mut c := c
  let mal : Except Err Cur := throw (mkErr "malformed JSON")
  if c.recursive then
    let i := c.skipLabel
    let x := c.p.typ i
    let (n, sz) := c.p.psize i
    if n == 0 then return ← mal
    let mut levelChange := false
    if x == tOBJECT || x == tARRAY then
      let par : Parent := { iHead := c.i, iValue := i, iEnd := i + n + sz, iKey := -1, nPath := c.path.size }
      if c.eType != 0 && c.parents.size > 0 then c := { c with path := c.path ++ c.pathName }
      c := { c with parents := c.parents.push par, i := i + n }
      levelChange := true
    else c := { c with i := i + n + sz }
    while c.parents.size > 0 && c.i ≥ c.top.iEnd do
      let t := c.top
      c := { c with parents := c.parents.pop, path := c.path.extract 0 t.nPath }
      levelChange := true
    if levelChange then
      c := { c with eType := if c.parents.size > 0 then c.p.typ c.top.iValue else 0 }
  else
    let i := c.skipLabel
    let (n, sz) := c.p.psize i
    if n == 0 then return ← mal
    c := { c with i := i + n + sz }
  if c.eType == tARRAY && c.parents.size > 0 then
    let t := c.top
    c := { c with parents := c.parents.set! (c.parents.size - 1) { t with iKey := t.iKey + 1 } }
  return { c with rowid := c.rowid + 1 }

def Cur.pathLength (c : Cur) : Nat := Id.run do
  let z := c.path
  let mut n := z.size
  if c.rowid == 0 && c.recursive && n ≥ 2 then
    while n > 1 do
      n := n - 1
      if bat z n == 91 || bat z n == 46 then
        let (x, _) := lookupStep { c.p with eEdit := 0 } 0 (z.extract 0 n) 1 0
        if isLookupErr x then continue
        if x + (c.p.psize x).1 == c.i then break
  return n

/-- The ten columns of the current row (key … path, json, root) and the
    subtype of `value`. -/
def Cur.row (c : Cur) : Except Err (List Value × Bool) := do
  let key ← if c.parents.size == 0 then
      if c.nRoot == 1 then pure Value.null else
      let j := c.pathLength
      let n := c.nRoot - j
      if n == 0 then pure .null
      else if bat c.path j == 91 then pure (.int (atoiPrefix (sub c.path (j+1) (n-1))))
      else if bat c.path (j+1) == 34 then pure (.text (sub c.path (j+2) (n-3)))
      else pure (.text (sub c.path (j+1) (n-1)))
    else if c.eType == tOBJECT then returnFromBlob c.p c.i 1
    else pure (.int c.top.iKey)
  let i := c.skipLabel
  let value ← returnFromBlob c.p i c.mode
  let sub := c.p.typ i ≥ tARRAY
  let typ := Value.ofString (typeName (c.p.typ i))
  let atom ← if c.p.typ i < tARRAY then returnFromBlob c.p i 1 else pure .null
  let id := Value.int c.i
  let parent := if c.parents.size > 0 && c.recursive then Value.int c.top.iHead else .null
  let fullkey := Value.text (if c.parents.size > 0 then c.path ++ c.pathName else c.path)
  let path := Value.text (c.path.extract 0 c.pathLength)
  let json := match c.zJson with
    | none => Value.blob c.p.b
    | some z => .text (cstr z)
  let root := Value.text (c.path.extract 0 c.nRoot)
  return ([key, value, typ, atom, id, parent, fullkey, path, json, root], sub)

def eachColumns : List String := ["key", "value", "type", "atom", "id", "parent", "fullkey", "path", "json", "root"]

/-- `jsonEachFilter` and the scan. Rows of all ten columns, with the
    subtype of `value`. -/
def eachRows (name : String) (args : Args) : Except Err (List (List Value × Bool)) := do
  let err {α} (m : String) : Except Err α := throw (mkErr m)
  let rec_ := name.endsWith "_tree"
  let mode := if name.startsWith "jsonb" then 2 else 1
  if args.length > 2 then err s!"too many arguments on {name}() - max 2"
  if args.isEmpty then return []
  let v := (argAt args 0).1
  let (p, zJson) ← match v with
    | .blob b => if isJsonb b then pure (({ b } : JP), none) else parseText (vtext v)
    | .null => return []
    | _ => parseText (vtext v)
  let mut c : Cur := { p, zJson, recursive := rec_, mode }
  let mut i := 0
  if args.length == 2 then
    let rv := (argAt args 1).1
    if rv.isNull then return []
    let zRoot := cstr (vtext rv)
    if bat zRoot 0 != 36 then err s!"bad JSON path: {sqlQuote zRoot}"
    c := { c with nRoot := zRoot.size }
    if bat zRoot 1 == 0 then
      i := 0
      c := { c with i := 0, eType := 0 }
    else
      let (r, p') := lookupStep c.p 0 zRoot 1 0
      if isLookupErr r then
        if r == lNOTFOUND then return []
        err s!"bad JSON path: {sqlQuote zRoot}"
      i := r
      if p'.iLabel != 0 then c := { c with i := p'.iLabel, eType := tOBJECT }
      else c := { c with i := r, eType := tARRAY }
    c := { c with path := zRoot }
  else
    c := { c with i := 0, eType := 0, nRoot := 1, path := bytesOf "$" }
  let (n, sz) := c.p.psize i
  c := { c with iEnd := i + n + sz }
  if c.p.typ i ≥ tARRAY && !rec_ then
    c := { c with i := i + n, eType := c.p.typ i,
                  parents := #[{ iKey := 0, iEnd := c.iEnd, iHead := i + n, iValue := i, nPath := 0 }] }
  let mut out := #[]
  let mut fuel := c.p.b.size + 2
  while c.i < c.iEnd && fuel > 0 do
    out := out.push (← c.row)
    c ← c.next
    fuel := fuel - 1
  return out.toList
where
  parseText (z : ByteArray) : Except Err (JP × Option ByteArray) :=
    match convertText (cstr z) with
    | .ok st => pure ({ b := st.out, nonstd := st.nonstd }, some z)
    | .error _ => throw (mkErr "malformed JSON")

end Sql.Json
