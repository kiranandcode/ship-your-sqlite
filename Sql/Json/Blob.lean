/-
  JSONB, SQLite's binary JSON (json.c of the 3.54.1 amalgamation), byte for
  byte: character classes, node headers, the text → JSONB translator
  (`jsonTranslateTextToBlob`, JSON5 included), JSONB → text
  (`jsonTranslateBlobToText`, `jsonTranslateBlobToPrettyText`), the strict
  validity check (`jsonbValidityCheck`), escapes and label comparison.

  The functions are ports of the C routines with the same names (minus the
  `json` prefix); C's NUL-terminated reads past the end are `at` returning 0.
-/
namespace Sql.Json

/-! ## Bytes -/

@[inline] def bat (b : ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0

theorem lt_of_bat_ne_zero {b : ByteArray} {i : Nat} (h : ¬ bat b i = 0) : i < b.size := by
  unfold bat at h; split at h
  · assumption
  · exact absurd rfl h

def bytesOf (s : String) : ByteArray := s.toUTF8

/-- The bytes up to the first NUL (C string semantics). -/
def cstr (b : ByteArray) : ByteArray := Id.run do
  for h : i in [0:b.size] do
    if b[i] == 0 then return b.extract 0 i
  return b

def sub (b : ByteArray) (i n : Nat) : ByteArray := b.extract i (i + n)

/-! ## Character classes (`sqlite3CtypeMap`, `jsonIsOk`, `jsonIsSpace`) -/

def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
def isAlpha (c : UInt8) : Bool := (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)
def isAlnum (c : UInt8) : Bool := isDigit c || isAlpha c
def isXdigit (c : UInt8) : Bool := isDigit c || (65 ≤ c && c ≤ 70) || (97 ≤ c && c ≤ 102)
/-- `sqlite3Isspace`: space, \t \n \v \f \r -/
def isSpaceS (c : UInt8) : Bool := c == 32 || (9 ≤ c && c ≤ 13)
/-- ctype bit 0x40: `$`, `_`, and bytes ≥ 0x80 -/
def isIdX (c : UInt8) : Bool := c == 36 || c == 95 || c ≥ 128
def jsonId1 (c : UInt8) : Bool := isAlpha c || isIdX c
def jsonId2 (c : UInt8) : Bool := isAlnum c || isIdX c
/-- `jsonIsOk`: not a control character, `"`, `'` or `\`. -/
def isOk (c : UInt8) : Bool := c ≥ 32 && c != 34 && c != 39 && c != 92
/-- `jsonIsspace` (RFC 8259 whitespace) -/
def isJSpace (c : UInt8) : Bool := c == 9 || c == 10 || c == 13 || c == 32

def hexToInt (h : UInt8) : Nat :=
  let h := h.toNat
  let h := h + 9 * ((h >>> 6) &&& 1)
  h &&& 15

def is2Hex (z : ByteArray) (i : Nat) : Bool := isXdigit (bat z i) && isXdigit (bat z (i+1))
def is4Hex (z : ByteArray) (i : Nat) : Bool := is2Hex z i && is2Hex z (i+2)
def hexToInt4 (z : ByteArray) (i : Nat) : Nat :=
  (hexToInt (bat z i) <<< 12) + (hexToInt (bat z (i+1)) <<< 8) + (hexToInt (bat z (i+2)) <<< 4) + hexToInt (bat z (i+3))

def lowerC (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- `sqlite3StrNICmp(z+i, s, n) == 0` (s has no NUL in its first n bytes). -/
def strnieq (z : ByteArray) (i : Nat) (s : String) (n : Nat) : Bool := Id.run do
  let t := bytesOf s
  for k in [0:n] do
    let a := bat z (i+k)
    let b := bat t k
    if lowerC a != lowerC b then return false
    if a == 0 then return true
  return true

/-- `strncmp(z+i, s, n) == 0` -/
def strneq (z : ByteArray) (i : Nat) (s : String) : Bool := Id.run do
  let t := bytesOf s
  for k in [0:t.size] do
    if bat z (i+k) != bat t k then return false
  return true

/-! ## JSONB node types -/

def tNULL : UInt8 := 0
def tTRUE : UInt8 := 1
def tFALSE : UInt8 := 2
def tINT : UInt8 := 3
def tINT5 : UInt8 := 4
def tFLOAT : UInt8 := 5
def tFLOAT5 : UInt8 := 6
def tTEXT : UInt8 := 7
def tTEXTJ : UInt8 := 8
def tTEXT5 : UInt8 := 9
def tTEXTRAW : UInt8 := 10
def tARRAY : UInt8 := 11
def tOBJECT : UInt8 := 12

def typeName (t : UInt8) : String :=
  match t.toNat with
  | 0 => "null" | 1 => "true" | 2 => "false" | 3 | 4 => "integer"
  | 5 | 6 => "real" | 7 | 8 | 9 | 10 => "text" | 11 => "array" | 12 => "object"
  | _ => ""

def maxDepth : Nat := 1000

/-- The header of a node with the minimal size field (`jsonBlobAppendNode`). -/
def header (t : UInt8) (sz : Nat) : ByteArray :=
  if sz ≤ 11 then ⟨#[t ||| (sz.toUInt8 <<< 4)]⟩
  else if sz ≤ 0xff then ⟨#[t ||| 0xc0, sz.toUInt8]⟩
  else if sz ≤ 0xffff then ⟨#[t ||| 0xd0, (sz >>> 8).toUInt8, sz.toUInt8]⟩
  else ⟨#[t ||| 0xe0, (sz >>> 24).toUInt8, (sz >>> 16).toUInt8, (sz >>> 8).toUInt8, sz.toUInt8]⟩

def node (t : UInt8) (payload : ByteArray) : ByteArray := header t payload.size ++ payload

/-- `jsonbPayloadSize`: header size `n` (0 on error) and payload size, with
    the bounds check against `nBlob` and `nBlob - delta`. -/
def payloadSize (b : ByteArray) (delta : Int) (i : Nat) : Nat × Nat :=
  let nb := b.size
  if i ≥ nb then (0, 0) else
  let x := (bat b i).toNat >>> 4
  let r : Option (Nat × Nat) :=
    if x ≤ 11 then some (1, x)
    else if x == 12 then
      if i + 1 ≥ nb then none else some (2, (bat b (i+1)).toNat)
    else if x == 13 then
      if i + 2 ≥ nb then none else some (3, ((bat b (i+1)).toNat <<< 8) + (bat b (i+2)).toNat)
    else if x == 14 then
      if i + 4 ≥ nb then none else
      some (5, ((bat b (i+1)).toNat <<< 24) + ((bat b (i+2)).toNat <<< 16) + ((bat b (i+3)).toNat <<< 8) + (bat b (i+4)).toNat)
    else
      if i + 8 ≥ nb || bat b (i+1) != 0 || bat b (i+2) != 0 || bat b (i+3) != 0 || bat b (i+4) != 0 then none else
      some (9, ((bat b (i+5)).toNat <<< 24) + ((bat b (i+6)).toNat <<< 16) + ((bat b (i+7)).toNat <<< 8) + (bat b (i+8)).toNat)
  match r with
  | none => (0, 0)
  | some (n, sz) =>
    let e : Int := (i + sz + n : Nat)
    if e > nb && e > (nb : Int) - delta then (0, 0) else (n, sz)

/-- The size fields of a header without the bounds check (as
    `jsonAfterEditSizeAdjust` reads it, with `nBlob` set to the allocation). -/
def payloadSizeRaw (b : ByteArray) (i : Nat) : Nat × Nat :=
  let x := (bat b i).toNat >>> 4
  if x ≤ 11 then (1, x)
  else if x == 12 then (2, (bat b (i+1)).toNat)
  else if x == 13 then (3, ((bat b (i+1)).toNat <<< 8) + (bat b (i+2)).toNat)
  else if x == 14 then (5, ((bat b (i+1)).toNat <<< 24) + ((bat b (i+2)).toNat <<< 16) + ((bat b (i+3)).toNat <<< 8) + (bat b (i+4)).toNat)
  else (9, ((bat b (i+5)).toNat <<< 24) + ((bat b (i+6)).toNat <<< 16) + ((bat b (i+7)).toNat <<< 8) + (bat b (i+8)).toNat)

/-! ## JSON5 whitespace -/

/-- `json5Whitespace`: bytes of JSON5 whitespace and comments at `z[n0..]`. -/
def json5Ws (z : ByteArray) (n0 : Nat) : Nat := Id.run do
  let mut n := n0
  -- Every iteration but the last advances `n`, and at `n ≥ z.size` (`bat` is
  -- 0) the loop stops: at most `z.size + 1` iterations.
  for _ in [0:z.size + 1] do
    let c := bat z n
    if c == 9 || c == 10 || c == 11 || c == 12 || c == 13 || c == 32 then n := n + 1
    else if c == 47 then  -- '/'
      if bat z (n+1) == 42 && bat z (n+2) != 0 then
        let mut j := n + 3
        let mut ok := true
        -- `j` advances and the loop stops at a 0 byte (at the latest at `z.size`)
        for _ in [0:z.size + 1] do
          if !(bat z j != 47 || bat z (j-1) != 42) then break
          if bat z j == 0 then ok := false; break
          j := j + 1
        if !ok then break
        n := j + 1
      else if bat z (n+1) == 47 then
        let mut j := n + 2
        -- `j` advances and the loop stops at a 0 byte (at the latest at `z.size`)
        for _ in [0:z.size + 1] do
          let c := bat z j
          if c == 0 then break
          if c == 10 || c == 13 then break
          if c == 0xe2 && bat z (j+1) == 0x80 && (bat z (j+2) == 0xa8 || bat z (j+2) == 0xa9) then
            j := j + 2; break
          j := j + 1
        n := j
        if bat z n != 0 then n := n + 1
      else break
    else if c == 0xc2 then
      if bat z (n+1) == 0xa0 then n := n + 2 else break
    else if c == 0xe1 then
      if bat z (n+1) == 0x9a && bat z (n+2) == 0x80 then n := n + 3 else break
    else if c == 0xe2 then
      if bat z (n+1) == 0x80 then
        let c2 := bat z (n+2)
        if c2 < 0x80 then break
        if c2 ≤ 0x8a || c2 == 0xa8 || c2 == 0xa9 || c2 == 0xaf then n := n + 3 else break
      else if bat z (n+1) == 0x81 && bat z (n+2) == 0x9f then n := n + 3
      else break
    else if c == 0xe3 then
      if bat z (n+1) == 0x80 && bat z (n+2) == 0x80 then n := n + 3 else break
    else if c == 0xef then
      if bat z (n+1) == 0xbb && bat z (n+2) == 0xbf then n := n + 3 else break
    else break
  return n - n0

def strspnJSpace (z : ByteArray) (i : Nat) : Nat := Id.run do
  let mut k := i
  -- `isJSpace 0` is false, so the loop stops at `z.size` at the latest
  for _ in [0:z.size + 1] do
    if !isJSpace (bat z k) then break
    k := k + 1
  return k - i

/-! ## Text → JSONB (`jsonTranslateTextToBlob`) -/

structure PState where
  out : ByteArray := .empty
  iErr : Nat := 0
  depth : Nat := 0
  nonstd : Bool := false

abbrev PM := StateM PState

@[inline] def emit (bs : ByteArray) : PM Unit := modify fun s => { s with out := s.out ++ bs }
@[inline] def setErr (i : Nat) : PM Unit := modify fun s => { s with iErr := i }
@[inline] def nonstd : PM Unit := modify fun s => { s with nonstd := true }

/-- Replace the content from `start` by a node of type `t` around it. -/
def wrapFrom (start : Nat) (t : UInt8) : PM Unit := modify fun s =>
  let payload := s.out.extract start s.out.size
  { s with out := s.out.extract 0 start ++ node t payload }

/-- Is `z[i]` `\` followed by `u` and 4 hex digits (`jsonIs4HexB`)? -/
def is4HexB (z : ByteArray) (i : Nat) : Bool := bat z i == 117 && is4Hex z (i+1)

/-! The loops of the translator scan `z` forward: each iteration advances the
    position by at least one byte, and at the end of `z` (`bat` is 0) every
    loop stops (0 ends a string with an error, is not a digit or a label
    character, and makes `trL` return 0, which ends an array or object with an
    error). So `z.size + 1` iterations always suffice. -/

/-- A string from its delimiter at `z[i]` (the `'` and `"` cases of `tr`). -/
def trString (z : ByteArray) (i : Nat) : PM Int := do
  let cDelim := bat z i
  let mut opcode := tTEXT
  let mut j := i + 1
  for _ in [0:z.size + 1] do
    for _ in [0:z.size + 1] do
      if !isOk (bat z j) then break
      j := j + 1
    let c := bat z j
    if c == cDelim then break
    else if c == 92 then
      j := j + 1
      let c := bat z j
      if c == 34 || c == 92 || c == 47 || c == 98 || c == 102 || c == 110 || c == 114 || c == 116
         || (c == 117 && is4Hex z (j+1)) then
        if opcode == tTEXT then opcode := tTEXTJ
      else if c == 39 || c == 118 || c == 10 || (c == 48 && !isDigit (bat z (j+1)))
         || (c == 0xe2 && bat z (j+1) == 0x80 && (bat z (j+2) == 0xa8 || bat z (j+2) == 0xa9))
         || (c == 120 && is2Hex z (j+1)) then
        opcode := tTEXT5; nonstd
      else if c == 13 then
        if bat z (j+1) == 10 then j := j + 1
        opcode := tTEXT5; nonstd
      else
        setErr j; return -1
    else if c ≤ 0x1f then
      if c == 0 then setErr j; return -1
      opcode := tTEXT5; nonstd
    else if c == 34 then
      opcode := tTEXT5
    j := j + 1
  emit (node opcode (z.extract (i+1) j))
  return (j + 1 : Nat)

def trFinish (z : ByteArray) (i j t : Nat) : PM Int := do
  let i := if bat z i == 43 then i + 1 else i
  emit (node (tINT + t.toUInt8) (z.extract i j))
  return (j : Nat)

def trNumber2 (z : ByteArray) (i : Nat) (t0 : Nat) (_seenE : Bool) : PM Int := do
  let mut t := t0
  let mut seenE := false
  let mut j := i + 1
  for _ in [0:z.size + 1] do
    let c := bat z j
    if isDigit c then j := j + 1; continue
    if c == 46 then
      if t &&& 2 != 0 then setErr j; return -1
      t := t ||| 2
      j := j + 1; continue
    if c == 101 || c == 69 then
      if bat z (j-1) < 48 then
        if bat z (j-1) == 46 && j ≥ i + 2 && isDigit (bat z (j-2)) then
          nonstd; t := t ||| 1
        else setErr j; return -1
      if seenE then setErr j; return -1
      t := t ||| 2
      seenE := true
      let mut c := bat z (j+1)
      if c == 43 || c == 45 then
        j := j + 1
        c := bat z (j+1)
      if c < 48 || c > 57 then setErr j; return -1
      j := j + 1; continue
    break
  if bat z (j-1) < 48 then
    if bat z (j-1) == 46 && j ≥ i + 2 && isDigit (bat z (j-2)) then
      nonstd; t := t ||| 1
    else setErr j; return -1
  trFinish z i j t

/-- `parse_number` (t: bit 0 JSON5, bit 1 float) -/
def trNumber (z : ByteArray) (i : Nat) (t : Nat) (_seenE : Bool) : PM Int := do
  let c := bat z i
  let mut t := t
  if c ≤ 48 then
    if c == 48 then
      if (bat z (i+1) == 120 || bat z (i+1) == 88) && isXdigit (bat z (i+2)) then
        nonstd
        let mut j := i + 3
        for _ in [0:z.size + 1] do
          if !isXdigit (bat z j) then break
          j := j + 1
        return ← trFinish z i j 1
      else if isDigit (bat z (i+1)) then
        setErr (i+1); return -1
    else
      if !isDigit (bat z (i+1)) then
        if (bat z (i+1) == 73 || bat z (i+1) == 105) && strnieq z (i+1) "inf" 3 then
          nonstd
          if c == 45 then emit (node tFLOAT (bytesOf "-9e999")) else emit (node tFLOAT (bytesOf "9e999"))
          return (i + (if strnieq z (i+4) "inity" 5 then 9 else 4) : Nat)
        if bat z (i+1) == 46 then
          nonstd
          return ← trNumber2 z i (t ||| 1) false
        setErr i; return -1
      if bat z (i+1) == 48 then
        if isDigit (bat z (i+2)) then setErr (i+1); return -1
        else if (bat z (i+2) == 120 || bat z (i+2) == 88) && isXdigit (bat z (i+3)) then
          nonstd
          t := t ||| 1
          let mut j := i + 4
          for _ in [0:z.size + 1] do
            if !isXdigit (bat z j) then break
            j := j + 1
          return ← trFinish z i j t
  trNumber2 z i t false

mutual
/-- `jsonTranslateTextToBlob`. Returns the index past the element, 0 at end
    of input, -1 on error, -2, -3, -4, -5 when `}` `]` `,` `:` is seen (with
    `iErr` at it).

    `lvl` is the number of array/object levels that may still be opened; it
    makes the recursion well-founded and never decides anything: from the top
    (`tr`: depth 0, `lvl = maxDepth + 1`) every call has
    `lvl + depth ≥ maxDepth + 1` (an error return may leave `depth` too high,
    never too low), so `trArray`/`trObject` reach `lvl = 0` only after their
    own `depth > maxDepth` check has already failed. -/
def trL (z : ByteArray) (lvl : Nat) (i0 : Nat) : PM Int := do
  let mut i := i0
  for _ in [0:z.size + 1] do
    let c := bat z i
    if c == 9 || c == 10 || c == 13 || c == 32 then
      i := i + 1 + strspnJSpace z (i+1)
    else if c == 11 || c == 12 || c == 47 || c == 0xc2 || c == 0xe1 || c == 0xe2 || c == 0xe3 || c == 0xef then
      let j := json5Ws z i
      if j > 0 then i := i + j; nonstd
      else setErr i; return -1
    else break
  let c := bat z i
  if c == 123 then trObject z lvl i
  else if c == 91 then trArray z lvl i
  else if c == 39 then nonstd; trString z i
  else if c == 34 then trString z i
  else if c == 116 then
    if strneq z i "true" && !isAlnum (bat z (i+4)) then emit ⟨#[tTRUE]⟩; return (i + 4 : Nat)
    setErr i; return -1
  else if c == 102 then
    if strneq z i "false" && !isAlnum (bat z (i+5)) then emit ⟨#[tFALSE]⟩; return (i + 5 : Nat)
    setErr i; return -1
  else if c == 43 then nonstd; trNumber z i 0 false
  else if c == 46 then
    if isDigit (bat z (i+1)) then nonstd; trNumber2 z i 3 false
    else setErr i; return -1
  else if c == 45 || isDigit c then trNumber z i 0 false
  else if c == 125 then setErr i; return -2
  else if c == 93 then setErr i; return -3
  else if c == 44 then setErr i; return -4
  else if c == 58 then setErr i; return -5
  else if c == 0 then return 0
  else
    if c == 110 && strneq z i "null" && !isAlnum (bat z (i+4)) then
      emit ⟨#[tNULL]⟩; return (i + 4 : Nat)
    -- NaN / Inf names
    let names : List (UInt8 × UInt8 × Nat × Bool × String) :=
      [(105, 73, 3, true, "inf"), (105, 73, 8, true, "infinity"), (110, 78, 3, false, "NaN"),
       (113, 81, 4, false, "QNaN"), (115, 83, 4, false, "SNaN")]
    for (c1, c2, nn, isF, m) in names do
      if c != c1 && c != c2 then continue
      if !strnieq z i m nn then continue
      if isAlnum (bat z (i+nn)) then continue
      if isF then emit (node tFLOAT (bytesOf "9e999")) else emit ⟨#[tNULL]⟩
      nonstd
      return (i + nn : Nat)
    setErr i; return -1
termination_by (lvl, 1)

def trArray (z : ByteArray) (lvl : Nat) (i : Nat) : PM Int := do
  let iThis := (← get).out.size
  modify fun s => { s with depth := s.depth + 1 }
  if (← get).depth > maxDepth then setErr i; return -1
  let .succ lvl := lvl | do setErr i; return -1  -- not reached: the depth check above failed (see `trL`)
  let iStart := iThis
  let mut j := i + 1
  for _ in [0:z.size + 1] do
    let x ← trL z lvl j
    if x ≤ 0 then
      if x == -3 then
        j := (← get).iErr
        if (← get).out.size != iStart then nonstd
        break
      if x != -1 then setErr j
      return -1
    j := x.toNat
    let c := bat z j
    if c == 44 then j := j + 1; continue
    else if c == 93 then break
    else
      if isJSpace c then
        j := j + 1 + strspnJSpace z (j+1)
        if bat z j == 44 then j := j + 1; continue
        else if bat z j == 93 then break
      let x ← trL z lvl j
      if x == -4 then j := (← get).iErr + 1; continue
      if x == -3 then j := (← get).iErr; break
    setErr j; return -1
  wrapFrom iThis tARRAY
  modify fun s => { s with depth := s.depth - 1 }
  return (j + 1 : Nat)
termination_by (lvl, 0)

def trObject (z : ByteArray) (lvl : Nat) (i : Nat) : PM Int := do
  let iThis := (← get).out.size
  modify fun s => { s with depth := s.depth + 1 }
  if (← get).depth > maxDepth then setErr i; return -1
  let .succ lvl := lvl | do setErr i; return -1  -- not reached: the depth check above failed (see `trL`)
  let iStart := iThis
  let mut j := i + 1
  for _ in [0:z.size + 1] do
    let iBlob := (← get).out.size
    let mut x ← trL z lvl j
    if x ≤ 0 then
      if x == -2 then
        j := (← get).iErr
        if (← get).out.size != iStart then nonstd
        break
      j := j + json5Ws z j
      let mut op := tTEXT
      let c := bat z j
      let esc := c == 92 && is4HexB z (j+1)
      if esc then op := tTEXTJ
      if jsonId1 c || esc then
        let mut k := j + 1
        for _ in [0:z.size + 1] do
          let ck := bat z k
          if jsonId2 ck && json5Ws z k == 0 then k := k + 1
          else if ck == 92 && is4HexB z (k+1) then op := tTEXTJ; k := k + 1
          else break
        emit (node op (z.extract j k))
        nonstd
        x := (k : Int)
      else
        if x != -1 then setErr j
        return -1
    let t := (bat (← get).out iBlob) &&& 0x0f
    if t < tTEXT || t > tTEXTRAW then setErr j; return -1
    j := x.toNat
    let mut gotColon := false
    if bat z j == 58 then j := j + 1; gotColon := true
    else if isJSpace (bat z j) then
      j := j + 1
      for _ in [0:z.size + 1] do
        if !isJSpace (bat z j) then break
        j := j + 1
      if bat z j == 58 then j := j + 1; gotColon := true
    if !gotColon then
      let x2 ← trL z lvl j
      if x2 != -5 then
        if x2 != -1 then setErr j
        return -1
      j := (← get).iErr + 1
    -- the value
    let xv ← trL z lvl j
    if xv ≤ 0 then
      if xv != -1 then setErr j
      return -1
    j := xv.toNat
    let c := bat z j
    if c == 44 then j := j + 1; continue
    else if c == 125 then break
    else
      if isJSpace c then
        j := j + 1 + strspnJSpace z (j+1)
        if bat z j == 44 then j := j + 1; continue
        else if bat z j == 125 then break
      let x3 ← trL z lvl j
      if x3 == -4 then j := (← get).iErr + 1; continue
      if x3 == -2 then j := (← get).iErr; break
    setErr j; return -1
  wrapFrom iThis tOBJECT
  modify fun s => { s with depth := s.depth - 1 }
  return (j + 1 : Nat)
termination_by (lvl, 0)
end

/-- `jsonTranslateTextToBlob` from the top (depth 0): see `trL`. -/
def tr (z : ByteArray) (i0 : Nat) : PM Int := trL z (maxDepth + 1) i0

/-- `jsonConvertTextToBlob`: the blob, or the parse state bat the error. -/
def convertText (z : ByteArray) : Except PState PState :=
  let (i, st) := (tr z 0).run {}
  if i > 0 then
    let mut_i := Id.run do
      let mut k := i.toNat
      -- `isJSpace 0` is false: the loop stops at `z.size` at the latest
      for _ in [0:z.size + 1] do
        if !isJSpace (bat z k) then break
        k := k + 1
      return k
    if bat z mut_i != 0 then
      let k := mut_i + json5Ws z mut_i
      if bat z k != 0 then .error st
      else .ok { st with nonstd := true }
    else .ok st
  else .error st

/-- `jsonReturnStringAsBlob` / plain translation of well-formed text. -/
def textToBlob (z : ByteArray) : ByteArray := ((tr z 0).run {}).2.out

/-! ## Unescaping and label comparison -/

def invalidChar : Nat := 0x99999

/-- `sqlite3Utf8ReadLimited` -/
def utf8ReadLimited (z : ByteArray) (i n : Nat) : Nat × Nat := Id.run do
  let c0 := (bat z i).toNat
  if c0 < 0xc0 then return (c0, 1)
  let trans : Nat :=
    if c0 < 0xe0 then c0 - 0xc0 else if c0 < 0xf0 then c0 - 0xe0
    else if c0 < 0xf8 then c0 - 0xf0 else if c0 < 0xfc then c0 - 0xf8
    else if c0 < 0xfe then c0 - 0xfc else 0
  let n := if n > 4 then 4 else n
  let mut c := trans
  let mut k := 1
  -- `k < n ≤ 4`
  for _ in [0:n] do
    if !(k < n && (bat z (i+k)) &&& 0xc0 == 0x80) then break
    c := (c <<< 6) + ((bat z (i+k)).toNat &&& 0x3f)
    k := k + 1
  return (c, k)

/-- `jsonBytesToBypass` on z[i..i+n) -/
def bytesToBypass (z : ByteArray) (i0 n : Nat) : Nat := Id.run do
  let mut i := 0
  -- `i` grows by at least 2 per iteration while `i + 1 < n`
  for _ in [0:n] do
    if !(i + 1 < n) then break
    if bat z (i0+i) != 92 then return i
    if bat z (i0+i+1) == 10 then i := i + 2; continue
    if bat z (i0+i+1) == 13 then
      if i + 2 < n && bat z (i0+i+2) == 10 then i := i + 3 else i := i + 2
      continue
    if bat z (i0+i+1) == 0xe2 && i + 3 < n && bat z (i0+i+2) == 0x80
       && (bat z (i0+i+3) == 0xa8 || bat z (i0+i+3) == 0xa9) then
      i := i + 4; continue
    break
  return i

/-- `jsonUnescapeOneChar` on z[i..i+n), z[i] = '\\': (code point, bytes used). -/
def unescapeOne (z : ByteArray) (i n : Nat) : Nat × Nat :=
  if n < 2 then (invalidChar, n) else
  let c := bat z (i+1)
  if c == 117 then
    if n < 6 then (invalidChar, n) else
    let v := hexToInt4 z (i+2)
    if v &&& 0xfc00 == 0xd800 && n ≥ 12 && bat z (i+6) == 92 && bat z (i+7) == 117
       && (hexToInt4 z (i+8)) &&& 0xfc00 == 0xdc00 then
      (((v &&& 0x3ff) <<< 10) + ((hexToInt4 z (i+8)) &&& 0x3ff) + 0x10000, 12)
    else (v, 6)
  else if c == 98 then (8, 2) else if c == 102 then (12, 2) else if c == 110 then (10, 2)
  else if c == 114 then (13, 2) else if c == 116 then (9, 2) else if c == 118 then (11, 2)
  else if c == 48 then ((if n > 2 && isDigit (bat z (i+2)) then invalidChar else 0), 2)
  else if c == 39 || c == 34 || c == 47 || c == 92 then (c.toNat, 2)
  else if c == 120 then
    if n < 4 then (invalidChar, n) else ((hexToInt (bat z (i+2)) <<< 4) ||| hexToInt (bat z (i+3)), 4)
  else if c == 0xe2 || c == 13 || c == 10 then
    let nSkip := bytesToBypass z i n
    if _h : nSkip = 0 then (invalidChar, n)
    else if nSkip == n then (0, n)
    else if bat z (i+nSkip) == 92 then
      let (v, k) := unescapeOne z (i+nSkip) (n-nSkip)
      (v, nSkip + k)
    else
      let (v, k) := utf8ReadLimited z (i+nSkip) (n-nSkip)
      (v, nSkip + k)
  else (invalidChar, 2)
termination_by n
decreasing_by omega

/-- One character of a label for `jsonLabelCompareEscaped`. -/
def labelChar (z : ByteArray) (i n : Nat) (raw : Bool) : Nat × Nat :=
  if n == 0 then (0, 0)
  else if raw || bat z i != 92 then
    let c := (bat z i).toNat
    if c ≥ 0xc0 then utf8ReadLimited z i n else (c, 1)
  else unescapeOne z i n

/-- `jsonLabelCompare`: labels z1[i1..i1+n1), z2[i2..i2+n2) -/
def labelEq (z1 : ByteArray) (i1 n1 : Nat) (raw1 : Bool) (z2 : ByteArray) (i2 n2 : Nat) (raw2 : Bool) : Bool :=
  if raw1 && raw2 then n1 == n2 && (sub z1 i1 n1).data == (sub z2 i2 n2).data
  else go i1 n1 i2 n2
where
  go (i1 n1 i2 n2 : Nat) : Bool :=
    let (c1, k1) := labelChar z1 i1 n1 raw1
    let (c2, k2) := labelChar z2 i2 n2 raw2
    if c1 != c2 then false
    else if c1 == 0 then true
    -- not reached: a nonzero character comes from a nonempty label and
    -- consumes at least one byte of it (`labelChar`)
    else if _h : n1 = 0 ∨ k1 = 0 then false
    else go (i1 + k1) (n1 - k1) (i2 + k2) (n2 - k2)
  termination_by n1
  decreasing_by omega

/-! ## JSONB → text -/

/-- `JsonString`: output, error bits (1 OOM, 2 MALFORMED, 4 TOODEEP, 8 ERR),
    whether the buffer left its 100-byte static space via `jsonPrintf`, and
    the last message given to `sqlite3_result_error`. -/
structure JStr where
  buf : ByteArray := .empty
  err : Nat := 0
  printf : Bool := false
  msg : Option String := none

def eMALFORMED : Nat := 2
def eTOODEEP : Nat := 4
def eERR : Nat := 8

@[inline] def JStr.add (s : JStr) (b : ByteArray) : JStr := { s with buf := s.buf ++ b }
@[inline] def JStr.addc (s : JStr) (c : UInt8) : JStr := { s with buf := s.buf.push c }
@[inline] def JStr.adds (s : JStr) (t : String) : JStr := s.add (bytesOf t)
def JStr.malformed (s : JStr) : JStr := { s with err := s.err ||| eMALFORMED }
def JStr.tooDeep (s : JStr) : JStr :=
  { s with err := s.err ||| eTOODEEP, msg := some "JSON nested too deep", buf := .empty }
def JStr.trim (s : JStr) : JStr :=
  if s.err == 0 then { s with buf := s.buf.extract 0 (s.buf.size - 1) } else s
/-- Is the result a heap string (`!bStatic`): it reached 100 bytes or went through `jsonPrintf(100,…)`. -/
def JStr.heap (s : JStr) : Bool := s.printf || s.buf.size ≥ 100

def hexDigit (n : Nat) : UInt8 := (if n < 10 then 48 + n else 87 + n).toUInt8

/-- `jsonAppendControlChar` -/
def controlEsc (c : UInt8) : ByteArray :=
  match c.toNat with
  | 8 => bytesOf "\\b" | 9 => bytesOf "\\t" | 10 => bytesOf "\\n" | 12 => bytesOf "\\f" | 13 => bytesOf "\\r"
  | n => ⟨#[92, 117, 48, 48, hexDigit (n >>> 4), hexDigit (n &&& 15)]⟩

/-- `jsonAppendString`: the string quoted and escaped. -/
def quoteString (z : ByteArray) : ByteArray := Id.run do
  let mut o := ByteArray.empty.push 34
  for c in z.data do
    if isOk c then o := o.push c
    else if c == 34 || c == 92 then o := (o.push 92).push c
    else if c == 39 then o := o.push c
    else o := o ++ controlEsc c
  return o.push 34

/-- Translation context: the blob, its delta, and the nesting depth (u16). -/
structure TCtx where
  b : ByteArray
  delta : Int := 0
  depth : Nat := 0

def u16inc (d : Nat) : Nat := (d + 1) % 65536
def u16dec (d : Nat) : Nat := (d + 65535) % 65536

/-- `jsonTranslateBlobToText` on blob `b` (with its delta) at nesting depth
    `depth` (u16): append node `i`; returns the index past it and the depth.

    Well-founded on `b.size - i`: a child starts after its parent's header,
    and each child returns an index past its own start (or sets an error,
    which ends the loop over the children). So a loop over the children of a
    node with payload `sz` runs at most `sz + 1` times. -/
def blobToTextD (b : ByteArray) (delta : Int) (depth : Nat) (i : Nat) (s : JStr) : Nat × JStr × Nat :=
  -- `payloadSize` gives `n = 0` here too: same result as the check below
  if _hi : b.size ≤ i then (b.size + 1, s.malformed, depth) else Id.run do
  let (n, sz) := payloadSize b delta i
  if n == 0 then return (b.size + 1, s.malformed, depth)
  let t := (bat b i) &&& 0x0f
  let p := i + n
  let mut s := s
  let mut depth := depth
  -- a child node; `i < j` always holds (`j` starts at `i + n > i` and only grows)
  let child (d j : Nat) (s : JStr) : Nat × JStr × Nat :=
    if _hj : i < j then blobToTextD b delta d j s else (b.size + 1, s.malformed, d)
  match t.toNat with
  | 0 => return (i + 1, s.adds "null", depth)
  | 1 => return (i + 1, s.adds "true", depth)
  | 2 => return (i + 1, s.adds "false", depth)
  | 3 | 5 =>
    if sz == 0 then s := s.malformed
    else s := s.add (sub b p sz)
  | 4 =>
    if sz == 0 then s := s.malformed
    else
      let mut k := 2
      let mut u : Nat := 0
      let mut ovf := false
      if bat b p == 45 then s := s.addc 45; k := k + 1
      else if bat b p == 43 then k := k + 1
      -- `k` counts up to `sz`
      for _ in [0:sz] do
        if !(k < sz) then break
        let c := bat b (p+k)
        if !isXdigit c then s := s.malformed; break
        else if u >>> 60 != 0 then ovf := true
        else u := u * 16 + hexToInt c
        k := k + 1
      s := { s with printf := true }
      s := if ovf then s.adds "9.0e999" else s.adds (toString u)
  | 6 =>
    if sz == 0 then s := s.malformed
    else
      let mut k := 0
      let mut bad := false
      if bat b p == 45 then
        s := s.addc 45
        if sz ≤ 1 then bad := true
        k := 1
      if bad then s := s.malformed
      else
        if bat b (p+k) == 46 then s := s.addc 48
        -- `k` counts up to `sz`
        for _ in [0:sz] do
          if !(k < sz) then break
          let c := bat b (p+k)
          s := s.addc c
          if c == 46 && (k + 1 == sz || !isDigit (bat b (p+k+1))) then s := s.addc 48
          k := k + 1
  | 7 | 8 =>
    s := (s.addc 34).add (sub b p sz) |>.addc 34
  | 9 =>
    s := s.addc 34
    let mut q := p
    let mut sz2 := sz
    -- every iteration that does not stop decreases `sz2` (from `sz`)
    for _ in [0:sz + 1] do
      if !(sz2 > 0) then break
      let mut k := 0
      -- `k` counts up to `sz2`
      for _ in [0:sz2] do
        if !(k < sz2 && (isOk (bat b (q+k)) || bat b (q+k) == 39)) then break
        k := k + 1
      if k > 0 then
        s := s.add (sub b q k)
        if k ≥ sz2 then break
        q := q + k; sz2 := sz2 - k
      let c := bat b q
      if c == 34 then
        s := s.adds "\\\""; q := q + 1; sz2 := sz2 - 1; continue
      if c ≤ 0x1f then
        s := s.add (controlEsc c); q := q + 1; sz2 := sz2 - 1; continue
      if sz2 < 2 then s := s.malformed; break
      let c1 := bat b (q+1)
      if c1 == 39 then s := s.addc 39
      else if c1 == 118 then s := s.adds "\\u000b"
      else if c1 == 120 then
        if sz2 < 4 then s := s.malformed; sz2 := 2
        else
          s := (s.adds "\\u00").add (sub b (q+2) 2)
          q := q + 2; sz2 := sz2 - 2
      else if c1 == 48 then s := s.adds "\\u0000"
      else if c1 == 13 then
        if sz2 > 2 && bat b (q+2) == 10 then q := q + 1; sz2 := sz2 - 1
      else if c1 == 10 then pure ()
      else if c1 == 0xe2 then
        if sz2 < 4 || bat b (q+2) != 0x80 || (bat b (q+3) != 0xa8 && bat b (q+3) != 0xa9) then
          s := s.malformed; sz2 := 2
        else q := q + 2; sz2 := sz2 - 2
      else s := s.add (sub b q 2)
      q := q + 2; sz2 := sz2 - 2
    s := s.addc 34
  | 10 => s := s.add (quoteString (sub b p sz))
  | 11 =>
    s := s.addc 91
    let iEnd := p + sz
    let mut j := p
    depth := u16inc depth
    if depth > maxDepth then s := s.tooDeep
    for _ in [0:sz + 1] do
      if !(j < iEnd && s.err == 0) then break
      let (j', s', d') := child depth j s
      j := j'; s := s'.addc 44; depth := d'
    depth := u16dec depth
    if j > iEnd then s := s.malformed
    if sz > 0 then s := s.trim
    s := s.addc 93
  | 12 =>
    s := s.addc 123
    let iEnd := p + sz
    let mut j := p
    let mut x := 0
    depth := u16inc depth
    if depth > maxDepth then s := s.tooDeep
    for _ in [0:sz + 1] do
      if !(j < iEnd && s.err == 0) then break
      let (j', s', d') := child depth j s
      j := j'; s := s'.addc (if x % 2 == 1 then 44 else 58); depth := d'
      x := x + 1
    depth := u16dec depth
    if x % 2 != 0 || j > iEnd then s := s.malformed
    if sz > 0 then s := s.trim
    s := s.addc 125
  | _ => s := s.malformed
  return (i + n + sz, s, depth)
termination_by b.size - i
decreasing_by all_goals omega

/-- `jsonTranslateBlobToText`: append node `i`; returns the index past it.
    Only the depth of the context changes. -/
def blobToText (cx : TCtx) (i : Nat) (s : JStr) : Nat × JStr × TCtx :=
  let (j, s, d) := blobToTextD cx.b cx.delta cx.depth i s
  (j, s, { cx with depth := d })

/-- `jsonTranslateBlobToPrettyText`. Well-founded on `maxDepth - nIndent`:
    the children are printed only below `maxDepth` (above it the result is
    an error, and json.c's loop does not run). A loop over the children of a
    node with payload `sz` runs at most `sz + 1` times: each child returns an
    index past its start, or sets an error. -/
def blobToPretty (indent : ByteArray) (nIndent : Nat) (cx : TCtx) (i : Nat) (s : JStr) : Nat × JStr × TCtx := Id.run do
  let b := cx.b
  let (n, sz) := payloadSize b cx.delta i
  if n == 0 then return (b.size + 1, s.malformed, cx)
  let ind (s : JStr) (k : Nat) : JStr := Id.run do
    let mut s := s
    for _ in [0:k] do s := s.add indent
    return s
  let t := (bat b i) &&& 0x0f
  if t == tARRAY then
    let mut j := i + n
    let iEnd := j + sz
    let mut s := s.addc 91
    let mut cx := cx
    if j < iEnd then
      s := s.addc 10
      if nIndent + 1 ≥ maxDepth then s := s.tooDeep
      -- else the loop does not run (`tooDeep` sets an error)
      if _hd : nIndent + 1 < maxDepth then
        for _ in [0:sz + 1] do
          if !(s.err == 0) then break
          s := ind s (nIndent + 1)
          let (j', s', cx') := blobToPretty indent (nIndent + 1) cx j s
          j := j'; s := s'; cx := cx'
          if j ≥ iEnd then
            if j > iEnd then s := s.malformed
            break
          s := s.adds ",\n"
      s := s.addc 10
      s := ind s nIndent
    return (iEnd, s.addc 93, cx)
  else if t == tOBJECT then
    let mut j := i + n
    let iEnd := j + sz
    let mut s := s.addc 123
    let mut cx := cx
    if j < iEnd then
      s := s.addc 10
      if nIndent + 1 ≥ maxDepth then s := s.tooDeep
      cx := { cx with depth := (nIndent + 1) % 65536 }
      -- else the loop does not run (`tooDeep` sets an error)
      if _hd : nIndent + 1 < maxDepth then
        for _ in [0:sz + 1] do
          if !(s.err == 0) then break
          s := ind s (nIndent + 1)
          let (j', s', cx') := blobToText cx j s
          j := j'; s := s'; cx := cx'
          if j > iEnd then s := s.malformed; break
          s := s.adds ": "
          let (j', s', cx') := blobToPretty indent (nIndent + 1) cx j s
          j := j'; s := s'; cx := cx'
          if j ≥ iEnd then break
          s := s.adds ",\n"
      s := s.addc 10
      s := ind s nIndent
    return (iEnd, s.addc 125, cx)
  else blobToText cx i s
termination_by maxDepth - nIndent
decreasing_by all_goals omega

/-! ## Strict validity (`jsonbValidityCheck`) -/

/-- 0 if node `i` (ending at `iEnd`) is well-formed, else the 1-based offset
    of the error. Well-founded on `maxDepth + 1 - depth` (json.c's own depth
    limit). Every loop scans the payload `[i + n, k)` with `k = i + n + sz`,
    advancing `j` by at least one byte per iteration: `sz` iterations suffice. -/
def validityCheck (b : ByteArray) (i iEnd depth : Nat) : Nat :=
  if _hd : depth > maxDepth then i + 1 else Id.run do
  let (n, sz) := payloadSize b 0 i
  if n == 0 then return i + 1
  if i + n + sz != iEnd then return i + 1
  let x := (bat b i) &&& 0x0f
  match x.toNat with
  | 0 | 1 | 2 => return if n + sz == 1 then 0 else i + 1
  | 3 =>
    if sz < 1 then return i + 1
    let mut j := i + n
    if bat b j == 45 then
      j := j + 1
      if sz < 2 then return i + 1
    let k := i + n + sz
    for _ in [0:sz] do
      if !(j < k) then break
      if isDigit (bat b j) then j := j + 1 else return j + 1
    return 0
  | 4 =>
    if sz < 3 then return i + 1
    let mut j := i + n
    if bat b j == 45 then
      if sz < 4 then return i + 1
      j := j + 1
    if bat b j != 48 then return i + 1
    if bat b (j+1) != 120 && bat b (j+1) != 88 then return j + 2
    j := j + 2
    let k := i + n + sz
    for _ in [0:sz] do
      if !(j < k) then break
      if isXdigit (bat b j) then j := j + 1 else return j + 1
    return 0
  | 5 | 6 =>
    let mut seen := 0
    if sz < 2 then return i + 1
    let mut j := i + n
    let k := j + sz
    if bat b j == 45 then
      j := j + 1
      if sz < 3 then return i + 1
    if bat b j == 46 then
      if x == tFLOAT then return j + 1
      if !isDigit (bat b (j+1)) then return j + 1
      j := j + 2
      seen := 1
    else if bat b j == 48 && x == tFLOAT then
      if j + 3 > k then return j + 1
      if bat b (j+1) != 46 && bat b (j+1) != 101 && bat b (j+1) != 69 then return j + 1
      j := j + 1
    for _ in [0:sz] do
      if !(j < k) then break
      let c := bat b j
      if isDigit c then j := j + 1; continue
      if c == 46 then
        if seen > 0 then return j + 1
        if x == tFLOAT && (j == k - 1 || !isDigit (bat b (j+1))) then return j + 1
        seen := 1
        j := j + 1; continue
      if c == 101 || c == 69 then
        if seen == 2 then return j + 1
        if j == k - 1 then return j + 1
        if bat b (j+1) == 43 || bat b (j+1) == 45 then
          j := j + 1
          if j == k - 1 then return j + 1
        seen := 2
        j := j + 1; continue
      return j + 1
    if seen == 0 then return i + 1
    return 0
  | 7 =>
    let mut j := i + n
    let k := j + sz
    for _ in [0:sz] do
      if !(j < k) then break
      if !isOk (bat b j) && bat b j != 39 then return j + 1
      j := j + 1
    return 0
  | 8 | 9 =>
    let mut j := i + n
    let k := j + sz
    -- (`unescapeOne` consumes at least one byte: `j + szC - 1 + 1 > j`)
    for _ in [0:sz] do
      if !(j < k) then break
      let c := bat b j
      if !isOk c && c != 39 then
        if c == 34 then
          if x == tTEXTJ then return j + 1
        else if c ≤ 0x1f then
          if x == tTEXTJ then return j + 1
        else if c != 92 || j + 1 ≥ k then return j + 1
        else
          let c1 := bat b (j+1)
          if c1 == 34 || c1 == 92 || c1 == 47 || c1 == 98 || c1 == 102 || c1 == 110 || c1 == 114 || c1 == 116 || c1 == 0 then
            j := j + 1
          else if c1 == 117 then
            if j + 5 ≥ k then return j + 1
            if !is4Hex b (j+2) then return j + 1
            j := j + 1
          else if x != tTEXT5 then return j + 1
          else
            let (cc, szC) := unescapeOne b j (k - j)
            if cc == invalidChar then return j + 1
            j := j + szC - 1
      j := j + 1
    return 0
  | 10 => return 0
  | 11 =>
    let mut j := i + n
    let k := j + sz
    for _ in [0:sz] do
      if !(j < k) then break
      let (n2, sz2) := payloadSize b 0 j
      if n2 == 0 then return j + 1
      if j + n2 + sz2 > k then return j + 1
      let r := validityCheck b j (j + n2 + sz2) (depth + 1)
      if r != 0 then return r
      j := j + n2 + sz2
    return 0
  | 12 =>
    let mut cnt := 0
    let mut j := i + n
    let k := j + sz
    for _ in [0:sz] do
      if !(j < k) then break
      let (n2, sz2) := payloadSize b 0 j
      if n2 == 0 then return j + 1
      if j + n2 + sz2 > k then return j + 1
      if cnt % 2 == 0 then
        let y := (bat b j) &&& 0x0f
        if y < tTEXT || y > tTEXTRAW then return j + 1
      let r := validityCheck b j (j + n2 + sz2) (depth + 1)
      if r != 0 then return r
      cnt := cnt + 1
      j := j + n2 + sz2
    if cnt % 2 != 0 then return j + 1
    return 0
  | _ => return i + 1
termination_by maxDepth + 1 - depth
decreasing_by all_goals omega

/-- `jsonArgIsJsonb` on a blob value. -/
def isJsonb (b : ByteArray) : Bool :=
  if b.size == 0 then false else
  let c := bat b 0
  if c &&& 0x0f > tOBJECT then false else
  let (n, sz) := payloadSize b 0 0
  n > 0 && sz + n == b.size && (c &&& 0x0f > tFALSE || sz == 0)
    && (sz > 7 || (c != 0x7b && c != 0x5b && !isDigit c) || validityCheck b 0 b.size 1 == 0)

end Sql.Json
