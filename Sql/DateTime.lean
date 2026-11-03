/-
  Date and time functions (https://sqlite.org/lang_datefunc.html): date, time,
  datetime, julianday, unixepoch, strftime, timediff, and CURRENT_*.

  A port of the `date.c` part of the SQLite 3.54.1 amalgamation, function by
  function and in the same order of operations, because the rounding of the
  doubles it computes with is observable (`computeJD` multiplies a double by
  86400000 and truncates; `'NNN units'` modifiers truncate `r*1000*xform±0.5`;
  `%f`/`%J`/`%s` go through SQLite's printf). State is the C `DateTime`
  struct (`DT`), with the same "valid" flags; every C helper is a function
  `DT → DT`. C integer division and remainder are `Int.tdiv`/`Int.tmod`, the
  64-bit `iJD` wraps like two's complement, and a double converted to an
  integer truncates with x86-64's out-of-range result (`truncI64`/`truncI32`).

  Choices of the semantics (the parameters of the libc/OS boundary):
  * `'now'` (and the no-argument forms, CURRENT_TIME/DATE/TIMESTAMP) reads the
    `Clock` (`sqlite3StmtCurrentTime`: Unix milliseconds, one value for the
    whole statement).
  * `localtime`/`utc`: SQLite calls the C library's `localtime_r`. The
    semantics fixes the time zone to **UTC** (`localtimeR` is `gmtime`), so
    the oracle is run with `TZ=UTC`. Everything else around `localtime_r`
    (the mapping of years outside 1970–2037 into 2000–2003, the
    fixed-point iteration of `utc`, the reset of the error flag) is ported.
  * `sqlite3NotPureFunc` is taken to be true: the semantics does not know
    whether the call is in a CHECK constraint, an index or a generated column
    (where SQLite rejects 'now', 'localtime', 'utc', 'subsec').
-/
import Sql.Db

namespace Sql.DateTime

/-- The clock the semantics reads for 'now' (a parameter of the semantics):
    milliseconds since the Unix epoch. -/
structure Clock where
  unixMs : Int := 0

/-! ## C arithmetic -/

/-- Two's complement wrap to 64 bits. -/
def wrapI64 (x : Int) : Int := (x + 2 ^ 63).emod (2 ^ 64) - 2 ^ 63

/-- `(sqlite3_int64)r` on x86-64 (`cvttsd2si`): truncation; NaN and out of
    range give the "integer indefinite" value -2^63. -/
def truncI64 (r : Float) : Int :=
  if r.isNaN || r ≥ 9223372036854775808.0 || r < -9223372036854775808.0 then minI64
  else realToInt r

/-- `(int)r` on x86-64: truncation; NaN and out of range give -2^31. -/
def truncI32 (r : Float) : Int :=
  if r.isNaN || r ≥ 2147483648.0 || r < -2147483648.0 then -2147483648
  else realToInt r

/-- `(double)i`. -/
@[inline] def fl (i : Int) : Float := intToReal i

@[inline] def ch (c : Char) : UInt8 := c.toNat.toUInt8

/-- The byte at `i` of a C string (0 past the end). -/
@[inline] def at_ (z : ByteArray) (i : Nat) : UInt8 := if i < z.size then z[i]! else 0

@[inline] def isDigit (c : UInt8) : Bool := 48 ≤ c && c ≤ 57
@[inline] def isSpace (c : UInt8) : Bool := isSpaceV c

/-- What `sqlite3_value_text` hands to C code: the bytes up to the first NUL. -/
def cstr (b : ByteArray) : ByteArray := Id.run do
  let mut i := 0
  while i < b.size && b[i]! != 0 do i := i + 1
  return b.extract 0 i

def skipSpace (z : ByteArray) (i : Nat) : Nat := Id.run do
  let mut i := i
  while isSpace (at_ z i) do i := i + 1
  return i

/-- `sqlite3UpperToLower` (ASCII only). -/
@[inline] def lowerC (c : UInt8) : UInt8 := if 65 ≤ c && c ≤ 90 then c + 32 else c

/-- `sqlite3_stricmp(z, lit) == 0`. -/
def stricmp (z : ByteArray) (lit : String) : Bool :=
  let l := lit.toUTF8
  z.size == l.size && (List.range z.size).all fun i => lowerC z[i]! == lowerC l[i]!

/-- `sqlite3_strnicmp(z, lit, n) == 0` for `n ≤ lit` length. -/
def strnicmp (z : ByteArray) (lit : String) (n : Nat) : Bool :=
  let l := lit.toUTF8
  (List.range n).all fun i => lowerC (at_ z i) == lowerC (at_ l i)

/-! ## sqlite3AtoF -/

/-- `sqlite3AtoF`: the sign of the result code (positive: a number with only
    surrounding whitespace; 0: no number; negative: a number followed by
    other text) and the double. -/
def atoF (z : ByteArray) : Int × Float := Id.run do
  let big : Nat := (2 ^ 64 - 1 - 9) / 10
  let mut i := skipSpace z 0
  let mut neg := false
  let mut s : Nat := 0
  let mut d : Int := 0
  let mut mState : Nat := 0
  let mut intPart := false
  let c := at_ z i
  if isDigit c then intPart := true
  else if c == ch '-' then
    neg := true; i := i + 1
    if isDigit (at_ z i) then intPart := true
  else if c == ch '+' then
    i := i + 1
    if isDigit (at_ z i) then intPart := true
  if intPart then
    mState := 1
    s := (at_ z i - 48).toNat; i := i + 1
    let mut stop := false
    while !stop && isDigit (at_ z i) do
      s := s * 10 + (at_ z i - 48).toNat; i := i + 1
      if s ≥ big then
        mState := 9
        while isDigit (at_ z i) do i := i + 1; d := d + 1
        stop := true
  if at_ z i == ch '.' then
    i := i + 1
    if isDigit (at_ z i) then
      mState := mState ||| 1
      while isDigit (at_ z i) do
        if s < big then
          s := s * 10 + (at_ z i - 48).toNat; d := d - 1
        else mState := 11
        i := i + 1
    else if mState == 0 then return (0, 0.0)
    mState := mState ||| 2
  else if mState == 0 then return (0, 0.0)
  if at_ z i == ch 'e' || at_ z i == ch 'E' then
    i := i + 1
    let mut esign : Int := 1
    if at_ z i == ch '-' then esign := -1; i := i + 1
    else if at_ z i == ch '+' then i := i + 1
    if isDigit (at_ z i) then
      let mut e : Nat := (at_ z i - 48).toNat
      i := i + 1
      mState := mState ||| 2
      while isDigit (at_ z i) do
        e := if e < 10000 then e * 10 + (at_ z i - 48).toNat else 10000
        i := i + 1
      d := d + esign * e
    else i := i - 1
  let r : Float :=
    if s == 0 then 0.0
    else if d < -348 then 0.0
    else if d > 347 then 1.0 / 0.0
    else Real.ofDecimal s d
  if s == 0 then mState := mState ||| 4
  let r := if neg then -r else r
  if at_ z i == 0 then return (mState, r)
  if isSpace (at_ z i) then
    i := skipSpace z i
    if at_ z i == 0 then return (mState, r)
  return (-1, r)

/-! ## SQLite's printf, for the conversions date.c uses -/

/-- `%Nd` / `%0Nd`. -/
def fmtInt (v : Int) (width : Nat) (zero : Bool) : String :=
  let digits := toString v.natAbs
  if zero then
    let sign := if v < 0 then "-" else ""
    let w := if v < 0 then width - 1 else width
    sign ++ "".pushn '0' (w - digits.length) ++ digits
  else
    let t := (if v < 0 then "-" else "") ++ digits
    "".pushn ' ' (width - t.length) ++ t

/-- `sqlite3Fp2Convert10(m, e, n)`: `D · 10^P ≈ m · 2^e` with at least `n`
    digits (`n = 18`: rounded; otherwise truncated). `10^p` as a normalized
    64-bit fraction is exact for the exponents date.c produces (|p| < 27). -/
def fp2Convert10 (m : Nat) (e : Int) (n : Nat) : Nat × Int :=
  let p : Int := (n : Int) - 1 - Real.pwr2to10 (e + 63)
  let L := Real.pwr10to2 p
  let x : Nat :=
    if p ≥ 0 then
      if 63 - L ≥ 0 then 10 ^ p.toNat * 2 ^ (63 - L).toNat else 10 ^ p.toNat / 2 ^ (L - 63).toNat
    else
      if 63 - L ≥ 0 then 2 ^ (63 - L).toNat / 10 ^ (-p).toNat else 0
  let h := (m * x) >>> 64
  if n == 18 then
    let h := h >>> (-(e + L + 2)).toNat
    ((h + ((h <<< 1) &&& 2)) >>> 1, -p)
  else (h >>> (-(e + L + 1)).toNat, -p)

/-- `sqlite3FpDecode(r, iRound, 16)` for a finite double: sign, significant
    digits, and the position of the decimal point. -/
def fpDecode (r : Float) (iRound : Int) : Bool × Array Nat × Int := Id.run do
  let neg := r < 0.0
  let r := if neg then -r else r
  if r == 0.0 then return (false, #[0], 1)
  let mxRound : Int := 16
  let b := Real.bits r
  let ex := (b >>> 52) % 2048
  let frac := b % 2 ^ 52
  let (v, e) : Nat × Int :=
    if ex == 0 then
      let nn := 64 - Real.Nat.bitLen frac
      (frac * 2 ^ nn, -1074 - (nn : Int))
    else (frac * 2 ^ 11 + 2 ^ 63, (ex : Int) - 1086)
  let nd : Nat := if iRound ≤ 0 || iRound ≥ 18 then 18 else (iRound + 1).toNat
  let (v, exp) := fp2Convert10 v e nd
  let mut z : Array Nat := (Real.digitsOf v).toArray
  let mut n : Int := z.size
  let mut iDP : Int := n + exp
  let mut iRound := iRound
  if iRound ≤ 0 then
    iRound := iDP - iRound
    if iRound == 0 && z[0]! ≥ 5 then
      iRound := 1
      z := #[0] ++ z
      n := n + 1
      iDP := iDP + 1
  if iRound > 0 && (iRound < n || n > mxRound) then
    if iRound > mxRound then iRound := mxRound
    n := iRound
    if z[iRound.toNat]! ≥ 5 then
      let (z', grew) := Real.incAt (z.extract 0 iRound.toNat) (iRound.toNat - 1)
      z := z'
      if grew then n := n + 1; iDP := iDP + 1
    else z := z.extract 0 iRound.toNat
  z := z.extract 0 n.toNat
  while z.size > 1 && z[z.size - 1]! == 0 do z := z.pop
  return (neg, z, iDP)

def digitStr (z : Array Nat) (a b : Nat) : String :=
  String.ofList ((z.extract a b).toList.map fun d => Char.ofNat (d + 48))

/-- `%W.Pf` (`zero`: the `0` flag). -/
def fmtFixed (r : Float) (prec : Nat) (width : Nat) (zero : Bool) : String := Id.run do
  let (neg, z, iDP) := fpDecode r (-(prec : Int))
  let n := z.size
  let pre := if neg then "-" else ""
  let mut e2 : Int := iDP - 1
  let mut out := ""
  let mut j : Nat := 0
  if e2 < 0 then out := out ++ "0"
  else
    j := min (e2 + 1).toNat n
    out := out ++ digitStr z 0 j
    e2 := e2 - j
    if e2 ≥ 0 then
      out := out.pushn '0' (e2 + 1).toNat
      e2 := -1
  if prec > 0 then out := out ++ "."
  let mut precision := prec
  if e2 < -1 && precision > 0 then
    let nn := min (-1 - e2).toNat precision
    out := out.pushn '0' nn
    precision := precision - nn
  if precision > 0 then
    let nn := min (n - j) precision
    out := out ++ digitStr z j (j + nn)
    precision := precision - nn
    out := out.pushn '0' precision
  let len := pre.length + out.length
  if len < width then
    if zero then return pre ++ "".pushn '0' (width - len) ++ out
    else return "".pushn ' ' (width - len) ++ pre ++ out
  return pre ++ out

/-- `%.16g`. -/
def fmtG16 (r : Float) : String := Id.run do
  let (neg, z, iDP) := fpDecode r 16
  let n := z.size
  let pre := if neg then "-" else ""
  let mut precision : Int := 15
  let exp := iDP - 1
  let isExp := exp < -4 || exp > precision
  if !isExp then precision := precision - exp
  let mut e2 : Int := if isExp then 0 else iDP - 1
  let flagDp := precision > 0
  let mut out := ""
  let mut j : Nat := 0
  if e2 < 0 then out := out ++ "0"
  else
    j := min (e2 + 1).toNat n
    out := out ++ digitStr z 0 j
    e2 := e2 - j
    if e2 ≥ 0 then
      out := out.pushn '0' (e2 + 1).toNat
      e2 := -1
  if flagDp then out := out ++ "."
  if e2 < -1 && precision > 0 then
    let nn := min (-1 - e2) precision
    out := out.pushn '0' nn.toNat
    precision := precision - nn
  if precision > 0 then
    let nn := min ((n : Int) - j) precision
    if nn > 0 then out := out ++ digitStr z j (j + nn.toNat)
  if flagDp then
    let cs := (out.toList.reverse.dropWhile (· == '0'))
    let cs := match cs with
      | '.' :: rest => rest
      | _ => cs
    out := String.ofList cs.reverse
  if isExp then
    let ea := exp.natAbs
    out := out ++ "e" ++ (if exp < 0 then "-" else "+")
      ++ (if ea < 10 then "0" else "") ++ toString ea
  return pre ++ out

/-! ## The DateTime struct -/

/-- C's `DateTime`. -/
structure DT where
  iJD : Int := 0
  Y : Int := 0
  M : Int := 0
  D : Int := 0
  h : Int := 0
  m : Int := 0
  tz : Int := 0
  s : Float := 0.0
  validJD : Bool := false
  validYMD : Bool := false
  validHMS : Bool := false
  nFloor : Int := 0
  rawS : Bool := false
  isError : Bool := false
  useSubsec : Bool := false
  isUtc : Bool := false
  isLocal : Bool := false
  deriving Inhabited

/-- `datetimeError`: zero everything, set `isError`. -/
def datetimeError : DT := { isError := true }

/-- One four-character conversion spec of `getDigits`. -/
structure Spec where
  n : Nat
  lo : Int
  hi : Int
  next : UInt8

/-- Decode a `getDigits` format such as `"40f-21a-21d"`. -/
def specs (f : String) : List Spec :=
  let mx : Char → Int
    | 'a' => 12 | 'b' => 14 | 'c' => 24 | 'd' => 31 | 'e' => 59 | _ => 14712
  let mk (n lo c : Char) (next : UInt8) : Spec :=
    { n := n.toNat - 48, lo := (lo.toNat - 48 : Nat), hi := mx c, next }
  let rec go : List Char → List Spec
    | n :: lo :: c :: sep :: rest => mk n lo c (ch sep) :: go rest
    | [n, lo, c] => [mk n lo c 0]
    | _ => []
  go f.toList

/-- `getDigits`: the values converted, in order (its count is the C result). -/
def getDigits (z : ByteArray) (i0 : Nat) (fmt : List Spec) : List Int := Id.run do
  let mut i := i0
  let mut out : Array Int := #[]
  for sp in fmt do
    let mut v : Int := 0
    for _ in [0:sp.n] do
      if !isDigit (at_ z i) then return out.toList
      v := v * 10 + (at_ z i - 48).toNat
      i := i + 1
    if v < sp.lo || v > sp.hi || (sp.next != 0 && sp.next != at_ z i) then return out.toList
    out := out.push v
    i := i + 1
  return out.toList

/-- `parseTimezone`: `true` on a parse error. -/
def parseTimezone (z : ByteArray) (i0 : Nat) (p : DT) : Bool × DT := Id.run do
  let mut i := skipSpace z i0
  let mut p := { p with tz := 0 }
  let c := at_ z i
  let mut sgn : Int := 0
  if c == ch '-' then sgn := -1
  else if c == ch '+' then sgn := 1
  else if c == ch 'Z' || c == ch 'z' then
    i := i + 1
    p := { p with isLocal := false, isUtc := true }
    i := skipSpace z i
    return (at_ z i != 0, p)
  else return (c != 0, p)
  i := i + 1
  match getDigits z i (specs "20b:20e") with
  | [nHr, nMn] =>
    i := i + 5
    p := { p with tz := sgn * (nMn + nHr * 60) }
    if p.tz == 0 then p := { p with isLocal := false, isUtc := true }
    i := skipSpace z i
    return (at_ z i != 0, p)
  | _ => return (true, p)

/-- `parseHhMmSs`: `true` on a parse error. -/
def parseHhMmSs (z : ByteArray) (i0 : Nat) (p : DT) : Bool × DT := Id.run do
  match getDigits z i0 (specs "20c:20e") with
  | [h, m] =>
    let mut i := i0 + 5
    let mut s : Int := 0
    let mut ms : Float := 0.0
    if at_ z i == ch ':' then
      i := i + 1
      match getDigits z i (specs "20e") with
      | [ss] => s := ss
      | _ => return (true, p)
      i := i + 2
      if at_ z i == ch '.' && isDigit (at_ z (i + 1)) then
        let mut rScale : Float := 1.0
        i := i + 1
        while isDigit (at_ z i) do
          ms := ms * 10.0 + fl (at_ z i).toNat - 48.0
          rScale := rScale * 10.0
          i := i + 1
        ms := ms / rScale
        if ms > 0.999 then ms := 0.999
    if h == 24 && (m != 0 || s != 0 || ms != 0.0) then return (true, p)
    let p := { p with validJD := false, rawS := false, validHMS := true, h := h, m := m, s := fl s + ms }
    return parseTimezone z i p
  | _ => return (true, p)

/-- `computeJD`. -/
def computeJD (p : DT) : DT := Id.run do
  if p.validJD then return p
  let mut p := p
  let mut Y : Int := 2000
  let mut M : Int := 1
  let mut D : Int := 1
  if p.validYMD then
    Y := p.Y; M := p.M; D := p.D
  else if p.validHMS && p.h == 24 then
    p := { p with h := 0 }
    D := 2
  if Y < -4713 || Y > 9999 || p.rawS then return datetimeError
  if M ≤ 2 then Y := Y - 1; M := M + 12
  let A := (Y + 4800).tdiv 100
  let B := 38 - A + A.tdiv 4
  let X1 := (36525 * (Y + 4716)).tdiv 100
  let X2 := (306001 * (M + 1)).tdiv 10000
  p := { p with iJD := truncI64 ((fl (X1 + X2 + D + B) - 1524.5) * 86400000.0), validJD := true }
  if p.validHMS then
    p := { p with iJD := wrapI64 (p.iJD + (p.h * 3600000 + p.m * 60000) + truncI64 (p.s * 1000.0 + 0.5)) }
    if p.tz != 0 then
      p := { p with iJD := wrapI64 (p.iJD - p.tz * 60000), validYMD := false, validHMS := false,
                    tz := 0, isUtc := true, isLocal := false }
  return p

/-- `daysOfMonth` (`1<<M` with x86's shift-count masking). -/
def daysOfMonth (Y M : Int) : Int :=
  if (0x15aa >>> (M.emod 32).toNat) % 2 == 1 then 31
  else if M != 2 then 30
  else if Y.tmod 4 == 0 && (Y.tmod 100 != 0 || Y.tmod 400 == 0) then 29
  else 28

/-- `computeFloor`. -/
def computeFloor (p : DT) : DT :=
  let mxD := daysOfMonth p.Y p.M
  { p with nFloor := if p.D > mxD then p.D - mxD else 0 }

/-- `parseYyyyMmDd`: `true` on a parse error. -/
def parseYyyyMmDd (z : ByteArray) (p : DT) : Bool × DT := Id.run do
  let (neg, i0) := if at_ z 0 == ch '-' then (true, 1) else (false, 0)
  match getDigits z i0 (specs "40f-21a-21d") with
  | [Y0, M0, D0] =>
    let mut Y := Y0
    let mut M := M0
    let mut D := D0
    let mut i := i0 + 10
    while isSpace (at_ z i) || at_ z i == ch 'T' do i := i + 1
    let (rc, p1) := parseHhMmSs z i p
    let mut p := p1
    if !rc then
      if p.h == 24 then
        let mxD := daysOfMonth Y M
        p := { p with h := 0 }
        D := D + 1
        if D > mxD then
          D := D - mxD
          M := M + 1
          if M > 12 then M := 1; Y := Y + 1
    else if at_ z i == 0 then p := { p with validHMS := false }
    else return (true, p)
    p := { p with validJD := false, validYMD := true, Y := if neg then -Y else Y, M := M, D := D }
    p := computeFloor p
    if p.tz != 0 then p := computeJD p
    return (false, p)
  | _ => return (true, p)

def clearYMD_HMS_TZ (p : DT) : DT := { p with validYMD := false, validHMS := false, tz := 0 }

/-- The Julian day (times 86400000) of the Unix epoch. -/
def unixEpochJD : Int := 210866760000000

/-- `setDateTimeToCurrent`: `true` on failure. -/
def setDateTimeToCurrent (clock : Clock) (p : DT) : Bool × DT :=
  let iJD := unixEpochJD + clock.unixMs
  if iJD > 0 then (false, clearYMD_HMS_TZ { p with iJD := iJD, validJD := true, isUtc := true, isLocal := false })
  else (true, { p with iJD := iJD })

/-- `setRawDateNumber`. -/
def setRawDateNumber (p : DT) (r : Float) : DT :=
  let p := { p with s := r, rawS := true }
  if r ≥ 0.0 && r < 5373484.5 then { p with iJD := truncI64 (r * 86400000.0 + 0.5), validJD := true }
  else p

/-- `parseDateOrTime`: `true` on failure. -/
def parseDateOrTime (clock : Clock) (z : ByteArray) (p : DT) : Bool × DT :=
  let (rc, p) := parseYyyyMmDd z p
  if !rc then (false, p) else
  let (rc, p) := parseHhMmSs z 0 p
  if !rc then (false, p) else
  if stricmp z "now" then setDateTimeToCurrent clock p else
  let (arc, r) := atoF z
  if arc > 0 then (false, setRawDateNumber p r) else
  if stricmp z "subsec" || stricmp z "subsecond" then
    setDateTimeToCurrent clock { p with useSubsec := true }
  else (true, p)

/-- `INT_464269060799999`: the iJD of 9999-12-31 23:59:59.999. -/
def maxJD : Int := 464269060799999

def validJulianDay (iJD : Int) : Bool := iJD ≥ 0 && iJD ≤ maxJD

/-- `computeYMD`. -/
def computeYMD (p : DT) : DT :=
  if p.validYMD then p
  else if !p.validJD then { p with Y := 2000, M := 1, D := 1, validYMD := true }
  else if !validJulianDay p.iJD then datetimeError
  else
    let Z := (p.iJD + 43200000).tdiv 86400000
    let alpha := truncI32 ((fl Z + 32044.75) / 36524.25) - 52
    let A := Z + 1 + alpha - (alpha + 100).tdiv 4 + 25
    let B := A + 1524
    let C := truncI32 ((fl B - 122.1) / 365.25)
    let D := (36525 * C.emod 32768).tdiv 100
    let E := truncI32 (fl (B - D) / 30.6001)
    let X1 := truncI32 (30.6001 * fl E)
    let M := if E < 14 then E - 1 else E - 13
    { p with D := B - D - X1, M := M, Y := if M > 2 then C - 4716 else C - 4715, validYMD := true }

/-- `computeHMS`. -/
def computeHMS (p : DT) : DT :=
  if p.validHMS then p else
  let p := computeJD p
  let dayMs := (p.iJD + 43200000).tmod 86400000
  let dayMin := dayMs.tdiv 60000
  { p with s := fl (dayMs.tmod 60000) / 1000.0, m := dayMin.tmod 60, h := dayMin.tdiv 60,
           rawS := false, validHMS := true }

def computeYMD_HMS (p : DT) : DT := computeHMS (computeYMD p)

/-- The fields of `struct tm` the semantics uses. -/
structure Tm where
  year : Int   -- full year (tm_year + 1900)
  mon : Int    -- 1..12 (tm_mon + 1)
  mday : Int
  hour : Int
  min : Int
  sec : Int

/-- `localtime_r` with the time zone fixed to UTC (= `gmtime_r`). -/
def localtimeR (t : Int) : Tm :=
  let days := t.ediv 86400
  let secs := t.emod 86400
  let zz := days + 719468
  let era := zz.ediv 146097
  let doe := zz - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  { year := if m ≤ 2 then y + 1 else y, mon := m, mday := d,
    hour := secs / 3600, min := (secs % 3600) / 60, sec := secs % 60 }

/-- `toLocaltime` (never fails: `localtime_r` of the UTC model is total). -/
def toLocaltime (p : DT) : DT :=
  let p := computeJD p
  let (t, iYearDiff) :=
    if p.iJD < 210866760000000 || p.iJD > 213014145600000 then
      let x := computeYMD_HMS p
      let iYearDiff := (2000 + x.Y.tmod 4) - x.Y
      let x := computeJD { x with Y := x.Y + iYearDiff, validJD := false }
      (x.iJD.tdiv 1000 - 210866760000, iYearDiff)
    else (p.iJD.tdiv 1000 - 210866760000, 0)
  let tm := localtimeR t
  { p with Y := tm.year - iYearDiff, M := tm.mon, D := tm.mday, h := tm.hour, m := tm.min,
           s := fl tm.sec + fl (p.iJD.tmod 1000) * 0.001,
           validYMD := true, validHMS := true, validJD := false, rawS := false, tz := 0,
           isError := false }

/-- `aXformType`: name, `rLimit` (a C `float`, here its exact double), `rXform`. -/
def xforms : List (Nat × String × Float × Float) :=
  [(0, "second", 464269992787968.0, 1.0),
   (1, "minute", 7737900007424.0, 60.0),
   (2, "hour", 128969998336.0, 3600.0),
   (3, "day", 5373485.0, 86400.0),
   (4, "month", 176546.0, 2592000.0),
   (5, "year", 14713.0, 31536000.0)]

/-- `autoAdjustDate`. -/
def autoAdjustDate (p : DT) : DT :=
  if !p.rawS || p.validJD then { p with rawS := false }
  else if p.s ≥ -210866760000.0 && p.s ≤ 253402300799.0 then
    let r := p.s * 1000.0 + 210866760000000.0
    let p := clearYMD_HMS_TZ p
    { p with iJD := truncI64 (r + 0.5), validJD := true, rawS := false }
  else p

/-- `x = M>0 ? (M-1)/12 : (M-12)/12`: the year carry of a month count. -/
def monthCarry (M : Int) : Int := if M > 0 then (M - 1).tdiv 12 else (M - 12).tdiv 12

/-- `sqlite3RealSameAsInt`. -/
def realSameAsInt (r : Float) (i : Int) : Bool :=
  r == 0.0 || (Real.bits r == Real.bits (fl i) && i ≥ -2251799813685248 && i < 2251799813685248)

/-- `parseModifier`: `true` when the modifier is not accepted. -/
def parseModifier (z : ByteArray) (p0 : DT) (idx : Nat) : Bool × DT := Id.run do
  let mut p := p0
  let c0 := lowerC (at_ z 0)
  if c0 == ch 'a' then
    if stricmp z "auto" then
      if idx > 1 then return (true, p)
      return (false, autoAdjustDate p)
    return (true, p)
  else if c0 == ch 'c' then
    if stricmp z "ceiling" then
      return (false, { clearYMD_HMS_TZ (computeJD p) with nFloor := 0 })
    return (true, p)
  else if c0 == ch 'e' then
    if !strnicmp z "end of " 7 then return (true, p)
    if !p.validJD && !p.validYMD && !p.validHMS then return (true, p)
    let rest := z.extract 7 z.size
    p := computeYMD p
    p := { p with validHMS := true, h := 23, m := 59, s := 59.999, rawS := false, tz := 0, validJD := false }
    if stricmp rest "month" then
      p := { p with D := 1, M := p.M + 1 }
      if p.M > 12 then p := { p with Y := p.Y + 1, M := 1 }
      p := computeJD (computeFloor p)
      p := { p with iJD := wrapI64 (p.iJD - (p.nFloor + 1) * 86400000) }
      return (false, clearYMD_HMS_TZ p)
    else if stricmp rest "year" then
      return (false, { p with M := 12, D := 31 })
    else if stricmp rest "day" then return (false, p)
    return (true, p)
  else if c0 == ch 'f' then
    if stricmp z "floor" then
      p := computeJD p
      p := { p with iJD := wrapI64 (p.iJD - p.nFloor * 86400000) }
      return (false, clearYMD_HMS_TZ p)
    return (true, p)
  else if c0 == ch 'j' then
    if stricmp z "julianday" then
      if idx > 1 then return (true, p)
      if p.validJD && p.rawS then return (false, { p with rawS := false })
    return (true, p)
  else if c0 == ch 'l' then
    if stricmp z "localtime" then
      p := if p.isLocal then p else toLocaltime p
      return (false, { p with isUtc := false, isLocal := true })
    return (true, p)
  else if c0 == ch 'u' then
    if stricmp z "unixepoch" && p.rawS then
      if idx > 1 then return (true, p)
      let r := p.s * 1000.0 + 210866760000000.0
      if r ≥ 0.0 && r < 464269060800000.0 then
        p := clearYMD_HMS_TZ p
        return (false, { p with iJD := truncI64 (r + 0.5), validJD := true, rawS := false })
      return (true, p)
    else if stricmp z "utc" then
      if !p.isUtc then
        p := computeJD p
        let iOrigJD := p.iJD
        let mut iGuess := iOrigJD
        let mut iErr : Int := 0
        let mut cnt : Nat := 0
        repeat
          iGuess := wrapI64 (iGuess - iErr)
          let nw := computeJD (toLocaltime { iJD := iGuess, validJD := true })
          iErr := wrapI64 (nw.iJD - iOrigJD)
          let go := iErr != 0 && cnt < 3
          cnt := cnt + 1
          if !go then break
        p := { iJD := iGuess, validJD := true, isUtc := true, isLocal := false }
      return (false, p)
    return (true, p)
  else if c0 == ch 'w' then
    if !strnicmp z "weekday " 8 then return (true, p)
    let arg := z.extract 8 z.size
    let (arc, r) := atoF arg
    if !(arc > 0) then return (true, p)
    if !(r ≥ -6.0 && r ≤ 6.0) then return (true, p)
    let n0 := truncI32 r
    if !realSameAsInt r n0 then return (true, p)
    p := computeYMD_HMS p
    p := computeJD { p with tz := 0, validJD := false }
    let mut Z := ((p.iJD + 129600000).tdiv 86400000).tmod 7
    let n := n0.natAbs
    if Z != n then
      if Z > n then Z := Z - 7
      p := { p with iJD := wrapI64 (p.iJD + (n - Z) * 86400000) }
      if arg.toList.contains (ch '-') then p := { p with iJD := wrapI64 (p.iJD - 7 * 86400000) }
    return (false, clearYMD_HMS_TZ p)
  else if c0 == ch 's' then
    if !strnicmp z "start of " 9 then
      if stricmp z "subsec" || stricmp z "subsecond" then
        return (false, { p with useSubsec := true })
      return (true, p)
    if !p.validJD && !p.validYMD && !p.validHMS then return (true, p)
    let rest := z.extract 9 z.size
    p := computeYMD p
    p := { p with validHMS := true, h := 0, m := 0, s := 0.0, rawS := false, tz := 0, validJD := false }
    if stricmp rest "month" then return (false, { p with D := 1 })
    else if stricmp rest "year" then return (false, { p with M := 1, D := 1 })
    else if stricmp rest "day" then return (false, p)
    return (true, p)
  else if c0 == ch '+' || c0 == ch '-' || isDigit c0 then
    let z0 := at_ z 0
    let mut n := 1
    let mut stop := false
    while !stop && at_ z n != 0 do
      let c := at_ z n
      if c == ch ':' || isSpace c then stop := true
      else if c == ch '-' && ((n == 5 && (getDigits z 1 (specs "40f")).length == 1)
                            || (n == 6 && (getDigits z 1 (specs "50f")).length == 1)) then stop := true
      else n := n + 1
    let (arc, r) := atoF (z.extract 0 n)
    if arc ≤ 0 then return (true, p)
    let mut z2 : Nat := 0
    let mut n2 : Nat := n
    if at_ z n == ch '-' then
      -- (+|-)YYYY-MM-DD [HH:MM[:SS[.FFF]]]
      if z0 != ch '+' && z0 != ch '-' then return (true, p)
      let ds := if n == 5 then getDigits z 1 (specs "40f-20a-20d") else getDigits z 1 (specs "50f-20a-20d")
      match ds with
      | [Y, M, D] =>
        let zo : Nat := if n == 5 then 0 else 1
        if M ≥ 12 then return (true, p)
        if D ≥ 31 then return (true, p)
        p := computeYMD_HMS p
        p := { p with validJD := false }
        let (Y', M', D') := if z0 == ch '-' then (p.Y - Y, p.M - M, -D) else (p.Y + Y, p.M + M, D)
        let x := monthCarry M'
        p := { p with Y := Y' + x, M := M' - x * 12 }
        p := computeJD (computeFloor p)
        p := { p with validHMS := false, validYMD := false, iJD := wrapI64 (p.iJD + D' * 86400000) }
        if at_ z (zo + 11) == 0 then return (false, p)
        if isSpace (at_ z (zo + 11)) && (getDigits z (zo + 12) (specs "20c:20e")).length == 2 then
          z2 := zo + 12; n2 := 2
        else return (true, p)
      | _ => return (true, p)
    if at_ z (z2 + n2) == ch ':' then
      -- (+|-)HH:MM[:SS[.FFF]]
      let zz := if isDigit (at_ z z2) then z2 else z2 + 1
      let (rc, tx) := parseHhMmSs z zz {}
      if rc then return (true, p)
      let tx := computeJD tx
      let t1 := tx.iJD - 43200000
      let day := t1.tdiv 86400000
      let t2 := t1 - day * 86400000
      let t3 := if z0 == ch '-' then -t2 else t2
      p := clearYMD_HMS_TZ (computeJD p)
      return (false, { p with iJD := wrapI64 (p.iJD + t3) })
    -- NNN units
    let k := skipSpace z n
    let u := z.extract k z.size
    let mut nn := u.size
    if nn < 3 || nn > 10 then return (true, p)
    if lowerC u[nn - 1]! == ch 's' then nn := nn - 1
    p := computeJD p
    let rRounder : Float := if r < 0.0 then -0.5 else 0.5
    p := { p with nFloor := 0 }
    let mut rc := true
    for (i, name, lim, xf) in xforms do
      if name.length == nn && strnicmp u name nn && r > -lim && r < lim then
        let mut r := r
        if i == 4 then
          p := computeYMD_HMS p
          let M := p.M + truncI32 r
          let x := monthCarry M
          p := computeFloor { p with Y := p.Y + x, M := M - x * 12 }
          p := { p with validJD := false }
          r := r - fl (truncI32 r)
        else if i == 5 then
          let y := truncI32 r
          p := computeYMD_HMS p
          p := computeFloor { p with Y := p.Y + y }
          p := { p with validJD := false }
          r := r - fl (truncI32 r)
        p := computeJD p
        p := { p with iJD := wrapI64 (p.iJD + truncI64 (r * 1000.0 * xf + rRounder)) }
        rc := false
        break
    return (rc, clearYMD_HMS_TZ p)
  else return (true, p)

/-- `sqlite3_value_text` of an argument, as C sees it; `none` for NULL. -/
def argText (v : Value) : Option ByteArray := v.toText?.map cstr

/-- `isDate`: the parsed and modified time, `none` when the result is NULL. -/
def isDate (clock : Clock) (args : List Value) : Option DT := Id.run do
  match args with
  | [] =>
    let (rc, p) := setDateTimeToCurrent clock {}
    return if rc then none else some p
  | a0 :: mods =>
    let mut p : DT := {}
    match a0 with
    | .int i => p := setRawDateNumber p (fl i)
    | .real r => p := setRawDateNumber p r
    | _ =>
      match argText a0 with
      | none => return none
      | some z =>
        let (rc, p') := parseDateOrTime clock z p
        if rc then return none
        p := p'
    let mut idx := 1
    for v in mods do
      match argText v with
      | none => return none
      | some z =>
        let (rc, p') := parseModifier z p idx
        if rc then return none
        p := p'
      idx := idx + 1
    p := computeJD p
    if p.isError || !validJulianDay p.iJD then return none
    if mods.isEmpty && p.validYMD && p.D > 28 then p := { p with validYMD := false }
    return some p

/-! ## The functions -/

/-- `'0' + v` as a C `char`. -/
def dig (v : Int) : UInt8 := ((48 + v).emod 256).toNat.toUInt8

def bytesOf (l : List Int) : ByteArray := ByteArray.mk (l.map dig).toArray

def ymdBytes (x : DT) : ByteArray :=
  let Y := x.Y.natAbs
  let Y : Int := Y
  let b := ByteArray.mk #[dig ((Y.tdiv 1000).tmod 10), dig ((Y.tdiv 100).tmod 10), dig ((Y.tdiv 10).tmod 10),
    dig (Y.tmod 10), ch '-', dig ((x.M.tdiv 10).tmod 10), dig (x.M.tmod 10), ch '-',
    dig ((x.D.tdiv 10).tmod 10), dig (x.D.tmod 10)]
  if x.Y < 0 then ByteArray.mk #[ch '-'] ++ b else b

def hmsBytes (x : DT) : ByteArray :=
  let hm := ByteArray.mk #[dig ((x.h.tdiv 10).tmod 10), dig (x.h.tmod 10), ch ':',
    dig ((x.m.tdiv 10).tmod 10), dig (x.m.tmod 10), ch ':']
  if x.useSubsec then
    let s := truncI32 (1000.0 * x.s + 0.5)
    hm ++ ByteArray.mk #[dig ((s.tdiv 10000).tmod 10), dig ((s.tdiv 1000).tmod 10), ch '.',
      dig ((s.tdiv 100).tmod 10), dig ((s.tdiv 10).tmod 10), dig (s.tmod 10)]
  else
    let s := truncI32 x.s
    hm ++ ByteArray.mk #[dig ((s.tdiv 10).tmod 10), dig (s.tmod 10)]

def daysAfterJan01 (x : DT) : Int :=
  let j := computeJD { x with validJD := false, M := 1, D := 1 }
  (x.iJD - j.iJD + 43200000).tdiv 86400000

def daysAfterMonday (x : DT) : Int := ((x.iJD + 43200000).tdiv 86400000).tmod 7
def daysAfterSunday (x : DT) : Int := ((x.iJD + 129600000).tdiv 86400000).tmod 7

/-- `y`: the Thursday of the ISO week of `x`. -/
def isoThursday (x : DT) : DT :=
  computeYMD { x with iJD := wrapI64 (x.iJD + (3 - daysAfterMonday x) * 86400000), validYMD := false }

/-- `strftime(FORMAT, ...)`. -/
def strftime (clock : Clock) (args : List Value) : Value := Id.run do
  match args with
  | [] => return .null
  | f0 :: rest =>
    let some f := argText f0 | return .null
    let some x := isDate clock rest | return .null
    let x := computeYMD_HMS (computeJD x)
    let mut out : ByteArray := .empty
    let mut i := 0
    let mut j := 0
    let app (o : ByteArray) (s : String) : ByteArray := o ++ s.toUTF8
    while i < f.size do
      if f[i]! != ch '%' then
        i := i + 1
        continue
      if j < i then out := out ++ f.extract j i
      i := i + 1
      j := i + 1
      let cf := Char.ofNat (at_ f i).toNat
      match cf with
      | 'd' => out := app out (fmtInt x.D 2 true)
      | 'e' => out := app out (fmtInt x.D 2 false)
      | 'f' =>
        let s := if x.s > 59.999 then 59.999 else x.s
        out := app out (fmtFixed s 3 6 true)
      | 'F' => out := app out (fmtInt x.Y 4 true ++ "-" ++ fmtInt x.M 2 true ++ "-" ++ fmtInt x.D 2 true)
      | 'G' => out := app out (fmtInt (isoThursday x).Y 4 true)
      | 'g' => out := app out (fmtInt ((isoThursday x).Y.tmod 100) 2 true)
      | 'H' => out := app out (fmtInt x.h 2 true)
      | 'k' => out := app out (fmtInt x.h 2 false)
      | 'I' | 'l' =>
        let h := if x.h > 12 then x.h - 12 else x.h
        let h := if h == 0 then 12 else h
        out := app out (fmtInt h 2 (cf == 'I'))
      | 'j' => out := app out (fmtInt (daysAfterJan01 x + 1) 3 true)
      | 'J' => out := app out (fmtG16 (fl x.iJD / 86400000.0))
      | 'm' => out := app out (fmtInt x.M 2 true)
      | 'M' => out := app out (fmtInt x.m 2 true)
      | 'p' => out := app out (if x.h ≥ 12 then "PM" else "AM")
      | 'P' => out := app out (if x.h ≥ 12 then "pm" else "am")
      | 'R' => out := app out (fmtInt x.h 2 true ++ ":" ++ fmtInt x.m 2 true)
      | 's' =>
        if x.useSubsec then out := app out (fmtFixed (fl (x.iJD - unixEpochJD) / 1000.0) 3 0 false)
        else out := app out (toString (x.iJD.tdiv 1000 - 210866760000))
      | 'S' => out := app out (fmtInt (truncI32 x.s) 2 true)
      | 'T' => out := app out (fmtInt x.h 2 true ++ ":" ++ fmtInt x.m 2 true ++ ":" ++ fmtInt (truncI32 x.s) 2 true)
      | 'u' | 'w' =>
        let c := daysAfterSunday x
        let c := if c == 0 && cf == 'u' then 7 else c
        out := out.push (dig c)
      | 'U' => out := app out (fmtInt ((daysAfterJan01 x - daysAfterSunday x + 7).tdiv 7) 2 true)
      | 'V' => out := app out (fmtInt ((daysAfterJan01 (isoThursday x)).tdiv 7 + 1) 2 true)
      | 'W' => out := app out (fmtInt ((daysAfterJan01 x - daysAfterMonday x + 7).tdiv 7) 2 true)
      | 'Y' => out := app out (fmtInt x.Y 4 true)
      | '%' => out := out.push (ch '%')
      | _ => return .null
      i := i + 1
    if j < i then out := out ++ f.extract j i
    return .text out

/-- `timediff(A, B)`. -/
def timediff (clock : Clock) (a b : Value) : Value := Id.run do
  let some d1 := isDate clock [a] | return .null
  let some d2 := isDate clock [b] | return .null
  let mut d1 := computeYMD_HMS d1
  let mut d2 := computeYMD_HMS d2
  let mut sign := '+'
  let mut Y : Int := 0
  let mut M : Int := 0
  if d1.iJD ≥ d2.iJD then
    Y := d1.Y - d2.Y
    if Y != 0 then d2 := computeJD { d2 with Y := d1.Y, validJD := false }
    M := d1.M - d2.M
    if M < 0 then Y := Y - 1; M := M + 12
    if M != 0 then d2 := computeJD { d2 with M := d1.M, validJD := false }
    while d1.iJD < d2.iJD do
      M := M - 1
      if M < 0 then M := 11; Y := Y - 1
      d2 := { d2 with M := d2.M - 1 }
      if d2.M < 1 then d2 := { d2 with M := 12, Y := d2.Y - 1 }
      d2 := computeJD { d2 with validJD := false }
    d1 := { d1 with iJD := wrapI64 (d1.iJD - d2.iJD + 148699540800000) }
  else
    sign := '-'
    Y := d2.Y - d1.Y
    if Y != 0 then d2 := computeJD { d2 with Y := d1.Y, validJD := false }
    M := d2.M - d1.M
    if M < 0 then Y := Y - 1; M := M + 12
    if M != 0 then d2 := computeJD { d2 with M := d1.M, validJD := false }
    while d1.iJD > d2.iJD do
      M := M - 1
      if M < 0 then M := 11; Y := Y - 1
      d2 := { d2 with M := d2.M + 1 }
      if d2.M > 12 then d2 := { d2 with M := 1, Y := d2.Y + 1 }
      d2 := computeJD { d2 with validJD := false }
    d1 := { d1 with iJD := wrapI64 (d2.iJD - d1.iJD + 148699540800000) }
  d1 := computeYMD_HMS (clearYMD_HMS_TZ d1)
  return .ofString (String.singleton sign ++ fmtInt Y 4 true ++ "-" ++ fmtInt M 2 true ++ "-"
    ++ fmtInt (d1.D - 1) 2 true ++ " " ++ fmtInt d1.h 2 true ++ ":" ++ fmtInt d1.m 2 true ++ ":"
    ++ fmtFixed d1.s 3 6 true)

def julianday (x : DT) : Value := .real (fl (computeJD x).iJD / 86400000.0)

def unixepoch (x : DT) : Value :=
  let x := computeJD x
  if x.useSubsec then .real (fl (x.iJD - unixEpochJD) / 1000.0)
  else .int (x.iJD.tdiv 1000 - 210866760000)

def date (x : DT) : Value := .text (ymdBytes (computeYMD x))
def time (x : DT) : Value := .text (hmsBytes (computeHMS x))
def datetime (x : DT) : Value :=
  let x := computeYMD_HMS x
  .text (ymdBytes x ++ ByteArray.mk #[ch ' '] ++ hmsBytes x)

def wrongArgs (name : String) : Except Err Value :=
  .error { code := SQLITE_ERROR, msg := s!"wrong number of arguments to function {name}()" }

/-- `none` if `name` is not a date/time function. -/
def scalar? (clock : Clock) (name : String) (args : List Value) : Option (Except Err Value) :=
  let via (f : DT → Value) (args : List Value) : Except Err Value :=
    .ok ((isDate clock args).map f |>.getD .null)
  match name with
  | "julianday" => some (via julianday args)
  | "unixepoch" => some (via unixepoch args)
  | "date" => some (via date args)
  | "time" => some (via time args)
  | "datetime" => some (via datetime args)
  | "strftime" => some (.ok (strftime clock args))
  | "timediff" => some (match args with
    | [a, b] => .ok (timediff clock a b)
    | _ => wrongArgs name)
  | "current_time" => some (if args.isEmpty then via time [] else wrongArgs name)
  | "current_date" => some (if args.isEmpty then via date [] else wrongArgs name)
  | "current_timestamp" => some (if args.isEmpty then via datetime [] else wrongArgs name)
  | _ => none

end Sql.DateTime
