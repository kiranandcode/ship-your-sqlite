/-
  Values, affinity, conversions, comparison and arithmetic
  (https://sqlite.org/datatype3.html, checked against sqlite3).
-/
import Sql.Real

namespace Sql

/-- A value: one of SQLite's five storage classes. Text is bytes (UTF-8 as
    written, not validated, as in SQLite). -/
inductive Value where
  | null
  | int (i : Int)          -- within [-2^63, 2^63)
  | real (r : Float)       -- never NaN (a NaN result is NULL)
  | text (s : ByteArray)
  | blob (b : ByteArray)
  deriving Inhabited

def Value.ofString (s : String) : Value := .text s.toUTF8

def minI64 : Int := -(2 ^ 63)
def maxI64 : Int := 2 ^ 63 - 1
def inI64 (i : Int) : Bool := minI64 ≤ i && i ≤ maxI64

/-- Column affinity (datatype3.html §3). `blob` is also "no affinity". -/
inductive Aff where
  | blob | text | numeric | integer | real
  deriving BEq, Repr, Inhabited

/-- Affinity of a declared type name (§3.1): the first matching rule. -/
def affinityOfType (decl : String) : Aff :=
  let u := decl.toUpper
  if (u.splitOn "INT").length > 1 then .integer
  else if (u.splitOn "CHAR").length > 1 || (u.splitOn "CLOB").length > 1 || (u.splitOn "TEXT").length > 1 then .text
  else if (u.splitOn "BLOB").length > 1 || u.isEmpty then .blob
  else if (u.splitOn "REAL").length > 1 || (u.splitOn "FLOA").length > 1 || (u.splitOn "DOUB").length > 1 then .real
  else .numeric

/-! ## Text to number -/

def isSpaceV (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 11 || c == 12 || c == 13
def digitB (c : UInt8) : Option Nat := if 48 ≤ c && c ≤ 57 then some (c - 48).toNat else none

/-- `sqlite3AtoF`: the double of the longest numeric prefix and a state:
    bit 0 a digit was seen, bit 1 a '.' or exponent, bit 2 exact zero, and
    `whole` = the text is that number with only surrounding whitespace.
    The mantissa keeps about 19 digits (later ones only scale), and
    `s · 10^d` is converted with correct rounding (`Real.ofDecimal`). -/
structure AtoF where
  value : Float
  digit : Bool
  frac : Bool
  whole : Bool

def bound : Nat := (2 ^ 64 - 1 - 9) / 10

def atof (z : ByteArray) : AtoF := Id.run do
  let n := z.size
  let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
  let mut i := 0
  while i < n && isSpaceV (at_ i) do i := i + 1
  let mut neg := false
  if at_ i == 45 then neg := true; i := i + 1
  else if at_ i == 43 then i := i + 1
  let mut s : Nat := 0
  let mut d : Int := 0
  let mut digit := false
  let mut frac := false
  -- integer part
  if (digitB (at_ i)).isSome then
    digit := true
    s := (digitB (at_ i)).get!; i := i + 1
    let mut stop := false
    while !stop && (digitB (at_ i)).isSome do
      s := s * 10 + (digitB (at_ i)).get!; i := i + 1
      if s ≥ bound then
        while (digitB (at_ i)).isSome do i := i + 1; d := d + 1
        stop := true
  -- fraction
  if at_ i == 46 then
    if (digitB (at_ (i+1))).isSome then
      i := i + 1; digit := true
      while (digitB (at_ i)).isSome do
        if s < bound then s := s * 10 + (digitB (at_ i)).get!; d := d - 1
        i := i + 1
      frac := true
    else if digit then i := i + 1; frac := true
  if !digit then return ⟨0.0, false, false, false⟩
  -- exponent
  if at_ i == 101 || at_ i == 69 then
    let j0 := i + 1
    let (esign, j) : Int × Nat :=
      if at_ j0 == 45 then (-1, j0 + 1) else if at_ j0 == 43 then (1, j0 + 1) else (1, j0)
    if (digitB (at_ j)).isSome then
      let mut e : Nat := 0
      let mut j := j
      while (digitB (at_ j)).isSome do
        e := if e < 10000 then e * 10 + (digitB (at_ j)).get! else 10000
        j := j + 1
      d := d + esign * e; i := j; frac := true
  let r := if s == 0 then 0.0
    else if d < -348 then 0.0
    else if d > 347 then 1.0 / 0.0
    else Real.ofDecimal s d
  let r := if neg then -r else r
  while i < n && isSpaceV (at_ i) do i := i + 1
  return ⟨r, true, frac, i == n⟩

/-- `sqlite3Atoi64`: the integer of the text when it is an integer literal
    (optional whitespace and sign) that fits in 64 bits; `none` otherwise. -/
def atoi64 (z : ByteArray) : Option Int := Id.run do
  let n := z.size
  let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
  let mut i := 0
  while i < n && isSpaceV (at_ i) do i := i + 1
  let mut neg := false
  if at_ i == 45 then neg := true; i := i + 1
  else if at_ i == 43 then i := i + 1
  let start := i
  let mut v : Nat := 0
  while (digitB (at_ i)).isSome do v := v * 10 + (digitB (at_ i)).get!; i := i + 1
  if i == start then return none
  while i < n && isSpaceV (at_ i) do i := i + 1
  if i != n then return none
  let x : Int := if neg then -(v : Int) else v
  return if inI64 x then some x else none

/-- The integer prefix of a text, as `CAST(x AS INTEGER)` reads it
    (`sqlite3Atoi64` with trailing text allowed; out of range clamps). -/
def atoiPrefix (z : ByteArray) : Int := Id.run do
  let n := z.size
  let at_ (k : Nat) : UInt8 := if k < n then z[k]! else 0
  let mut i := 0
  while i < n && isSpaceV (at_ i) do i := i + 1
  let mut neg := false
  if at_ i == 45 then neg := true; i := i + 1
  else if at_ i == 43 then i := i + 1
  let mut v : Nat := 0
  while (digitB (at_ i)).isSome do v := v * 10 + (digitB (at_ i)).get!; i := i + 1
  let x : Int := if neg then -(v : Int) else v
  return if x > maxI64 then maxI64 else if x < minI64 then minI64 else x

/-! ## Real ↔ integer -/

/-- The integer a REAL truncates to, clamped to the 64-bit range
    (`sqlite3RealToI64`). -/
def realToInt (r : Float) : Int :=
  if r.isNaN then 0
  else if r ≤ -9223372036854775808.0 then minI64
  else if r ≥ 9223372036854775807.0 then maxI64
  else
    let t := if r < 0 then -((-r).floor) else r.floor
    -- exact: |t| < 2^63 and integral
    let b := Real.bits t
    let ex := ((b >>> 52) % 2048 : Nat)
    let m := b % 2 ^ 52 + 2 ^ 52
    let mag : Int := if t == 0 then 0
      else if ex ≥ 1075 then (m * 2 ^ (ex - 1075) : Nat) else (m / 2 ^ (1075 - ex) : Nat)
    if t < 0 then -mag else mag

/-- The double nearest to an integer. -/
def intToReal (i : Int) : Float :=
  if i ≥ 0 then Real.roundScaled i.toNat false 0 else -(Real.roundScaled (-i).toNat false 0)

/-- A REAL that is exactly a 64-bit integer, as that integer
    (`sqlite3VdbeIntegerAffinity`). -/
def realAsInt (r : Float) : Option Int :=
  let i := realToInt r
  if i > minI64 && i < maxI64 && intToReal i == r then some i else none

/-! ## Rendering -/

def intText (i : Int) : ByteArray := (toString i).toUTF8
def realText (r : Float) : ByteArray := (Real.render r).toUTF8

/-- The text of a value (`sqlite3_value_text`): NULL has none. -/
def Value.toText? : Value → Option ByteArray
  | .null => none
  | .int i => some (intText i)
  | .real r => some (realText r)
  | .text s => some s
  | .blob b => some b

/-! ## Affinity application (datatype3.html §3) -/

/-- Numeric affinity on a text: an integer if it is an integer literal that
    fits, else a REAL if it is a number, else unchanged. `tryInt`: a REAL
    that is exactly an integer becomes the integer (NUMERIC, INTEGER). -/
def numericOfText (s : ByteArray) (tryInt : Bool) : Option Value :=
  let a := atof s
  if !a.whole then none
  else if !a.frac then
    match atoi64 s with
    | some i => some (.int i)
    | none => some (.real a.value)
  else if tryInt then
    match realAsInt a.value with
    | some i => some (.int i)
    | none => some (.real a.value)
  else some (.real a.value)

/-- Apply a column affinity to a value being stored or compared. -/
def applyAffinity (aff : Aff) (v : Value) : Value :=
  match aff, v with
  | .text, .int _ | .text, .real _ => .text (v.toText?.getD .empty)
  | .numeric, .text s | .integer, .text s => (numericOfText s true).getD v
  | .real, .text s => match numericOfText s false with
    | some (.int i) => .real (intToReal i)
    | some w => w
    | none => v
  | .numeric, .real r | .integer, .real r => match realAsInt r with
    | some i => .int i
    | none => v
  | .real, .int i => .real (intToReal i)
  | _, _ => v

/-! ## Numeric value of any value (arithmetic operands) -/

/-- The number a value stands for in arithmetic (`sqlite3VdbeMemNumerify`):
    a text or blob is read as its longest numeric prefix; NULL stays NULL. -/
def Value.numeric : Value → Value
  | .text s | .blob s =>
    let a := atof s
    if !a.digit then .int 0
    else if !a.frac then
      -- an integer prefix: the integer if it fits, else the double
      match atoi64 (s.extract 0 (prefixLen s)) with
      | some i => .int i
      | none => .real a.value
    else .real a.value
  | v => v
where
  prefixLen (s : ByteArray) : Nat := Id.run do
    let mut i := 0
    while i < s.size && isSpaceV s[i]! do i := i + 1
    if i < s.size && (s[i]! == 45 || s[i]! == 43) then i := i + 1
    while i < s.size && (digitB s[i]!).isSome do i := i + 1
    return i

def Value.toReal (v : Value) : Float :=
  match v.numeric with
  | .int i => intToReal i
  | .real r => r
  | _ => 0.0

def Value.toInt (v : Value) : Int :=
  match v with
  | .int i => i
  | .real r => realToInt r
  | .text s | .blob s => atoiPrefix s
  | .null => 0

/-! ## SQLite's lenient UTF-8 -/

/-- `sqlite3Utf8Trans1`: the payload bits of a lead byte `0xC0 + i`. -/
def utf8Trans1 (i : Nat) : Nat :=
  if i < 32 then i else if i < 48 then i - 32 else if i < 56 then i - 48
  else [0, 1, 2, 3, 0, 1, 0, 0][i - 56]!

/-- `sqlite3Utf8Read`: the code point at the start of `bs` and the bytes it
    used. A lead byte takes every continuation byte that follows; an overlong,
    surrogate or 0xFFFE/0xFFFF result is U+FFFD; a stray byte is itself. -/
def utf8Read (bs : List UInt8) : Nat × List UInt8 :=
  match bs with
  | [] => (0, [])
  | c :: rest =>
    if c.toNat < 0xC0 then (c.toNat, rest) else
    let rec go (acc : Nat) : List UInt8 → Nat × List UInt8
      | d :: r => if d &&& 0xC0 == 0x80 then go (acc * 64 + (d &&& 0x3F).toNat) r else (acc, d :: r)
      | [] => (acc, [])
    let (v, r) := go (utf8Trans1 (c.toNat - 0xC0)) rest
    let v := if v < 0x80 || v &&& 0xFFFFF800 == 0xD800 || v &&& 0xFFFFFFFE == 0xFFFE then 0xFFFD else v
    (v, r)

/-! ## Comparison -/

/-- Collating sequences. -/
inductive Coll where
  | binary | nocase | rtrim
  deriving BEq, Repr, Inhabited

def collOfName (s : String) : Option Coll :=
  match s.toUpper with
  | "BINARY" => some .binary | "NOCASE" => some .nocase | "RTRIM" => some .rtrim
  | _ => none

def lowerB (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

def cmpBytes (a b : List UInt8) : Ordering :=
  match a, b with
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | x :: xs, y :: ys => if x < y then .lt else if x > y then .gt else cmpBytes xs ys

def collate (c : Coll) (a b : ByteArray) : Ordering :=
  match c with
  | .binary => cmpBytes a.toList b.toList
  | .nocase => cmpBytes (a.toList.map lowerB) (b.toList.map lowerB)
  | .rtrim =>
    let trim (l : List UInt8) := (l.reverse.dropWhile (· == 32)).reverse
    cmpBytes (trim a.toList) (trim b.toList)

/-- Exact comparison of an integer and a double (`sqlite3IntFloatCompare`). -/
def cmpIntReal (i : Int) (r : Float) : Ordering :=
  if r.isNaN then .gt
  else if r ≥ 9223372036854775808.0 then .lt
  else if r < -9223372036854775808.0 then .gt
  else
    let t := realToInt r
    if i < t then .lt else if i > t then .gt
    else
      let ti := intToReal t
      if ti < r then .lt else if ti > r then .gt else .eq

def cmpReal (a b : Float) : Ordering := if a < b then .lt else if a > b then .gt else .eq

def Value.rank : Value → Nat
  | .null => 0 | .int _ | .real _ => 1 | .text _ => 2 | .blob _ => 3

/-- The total order of values (datatype3.html §4.1), with a collation for text. -/
def compareValues (c : Coll) (a b : Value) : Ordering :=
  match a, b with
  | .null, .null => .eq
  | .int x, .int y => compare x y
  | .int x, .real y => cmpIntReal x y
  | .real x, .int y => (cmpIntReal y x).swap
  | .real x, .real y => cmpReal x y
  | .text x, .text y => collate c x y
  | .blob x, .blob y => cmpBytes x.toList y.toList
  | _, _ => compare a.rank b.rank

/-! ## Arithmetic -/

def Value.isNull : Value → Bool
  | .null => true
  | _ => false

/-- A double result: NaN is NULL. -/
def realResult (r : Float) : Value := if r.isNaN then .null else .real r

inductive ArithOp where
  | add | sub | mul | div | rem
  deriving BEq, Repr

/-- `+ - * / %` (sqlite3 OP_Add …): integer arithmetic when both operands are
    integers and nothing overflows, else double arithmetic; division by zero
    and a NaN result are NULL. `%` on doubles works on their integer parts. -/
def arith (op : ArithOp) (a b : Value) : Value :=
  if a.isNull || b.isNull then .null else
  let x := a.numeric
  let y := b.numeric
  let fp : Unit → Value := fun _ =>
    let ra := x.toReal
    let rb := y.toReal
    match op with
    | .add => realResult (ra + rb)
    | .sub => realResult (ra - rb)
    | .mul => realResult (ra * rb)
    | .div => if rb == 0.0 then .null else realResult (ra / rb)
    | .rem =>
      let ia := realToInt ra
      let ib := realToInt rb
      if ib == 0 then .null else
      let ib := if ib == -1 then 1 else ib
      realResult (intToReal (ia.tmod ib))
  match x, y with
  | .int i, .int j =>
    match op with
    | .add => if inI64 (i + j) then .int (i + j) else fp ()
    | .sub => if inI64 (i - j) then .int (i - j) else fp ()
    | .mul => if inI64 (i * j) then .int (i * j) else fp ()
    | .div =>
      if j == 0 then .null
      else if i == minI64 && j == -1 then fp ()
      else .int (i.tdiv j)
    | .rem =>
      if j == 0 then .null
      else .int (i.tmod (if j == -1 then 1 else j))
  | _, _ => fp ()

end Sql
