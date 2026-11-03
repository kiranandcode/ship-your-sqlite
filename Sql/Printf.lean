/-
  SQLite's printf (`sqlite3_str_vappendf`, sqlite3.c 32937): the SQL functions
  `printf()` and `format()`, the decimal conversion `round()` goes through
  (`%!.*f`), and `quote()` of a REAL (`%!0.17g`).

  A transcription of the C code on exact integers, not a specification of
  "correct" formatting: the decimal digits come from `sqlite3FpDecode`
  (sqlite3.c 38236), whose digits come from `sqlite3Fp2Convert10` (37598), a
  64-bit fixed-point multiplication by a truncated power of ten that keeps
  `n` digits (`n` = 18 rounds half up, `n` < 18 truncates), then a round-half-up
  of those digits at the requested position (so a double rounding). Checked
  against the native build by `tools/PrintfCheck.lean` on the cases of
  `experiments/printf/rand.c`: 1M random printf()/round()/quote() calls
  (random formats, flags, widths, precisions and argument types), 300k
  round() and 300k quote() calls, and 262k float conversions covering every
  binary exponent: 0 mismatches. Also `tests/sem/printf*.sql`.

  The output accumulator is SQLite's `StrAccum` with `mxAlloc` =
  `SQLITE_LIMIT_LENGTH` (10^9): any append or reservation that would make it
  reach `mxAlloc` turns the whole result into SQLITE_TOOBIG. Lengths are
  checked before a long run of padding is materialized.
-/
import Sql.Db

namespace Sql.Printf

/-- `db->aLimit[SQLITE_LIMIT_LENGTH]`, the accumulator's `mxAlloc`. -/
def mxAlloc : Nat := 1000000000

/-- Byte `i` of a C string (0 past the end). -/
@[inline] def bat (b : ByteArray) (i : Nat) : UInt8 := if i < b.size then b[i]! else 0

/-- A text as C sees it through `sqlite3_value_text`: up to the first NUL. -/
def cstr (b : ByteArray) : ByteArray := Id.run do
  let mut i := 0
  for _ in [0:b.size] do
    if !(i < b.size && b[i]! != 0) then break
    i := i + 1
  return if i == b.size then b else b.extract 0 i

def isCont (c : UInt8) : Bool := c &&& 0xc0 == 0x80

def rep (n : Nat) (c : UInt8) : ByteArray := ⟨Array.replicate n c⟩

def bytesOf (s : String) : ByteArray := s.toUTF8

/-! ## Decimal digits of a double (`sqlite3Fp2Convert10`, `sqlite3FpDecode`) -/

/-- `powerOfTen(p)`: the 64 most significant bits of 10^p, truncated,
    i.e. floor(10^p · 2^(63 - pwr10to2 p)). (The tables of sqlite3.c give
    exactly this for every p in [-348, 347]: `experiments/printf/pow10.c`.) -/
def powerOfTen (p : Int) : Nat :=
  let L := Real.pwr10to2 p
  if p ≥ 0 then
    if 63 - L ≥ 0 then 10 ^ p.toNat * 2 ^ (63 - L).toNat else 10 ^ p.toNat / 2 ^ (L - 63).toNat
  else
    if 63 - L ≥ 0 then 2 ^ (63 - L).toNat / 10 ^ (-p).toNat else 0

/-- `sqlite3Fp2Convert10(m, e, n)`: `m · 2^e ≈ D · 10^P`, `D` with at least
    `n` digits; `m` has bit 63 set. Only the high 64 bits of `m · 10^p` are
    used. `n = 18` rounds the last bit half up (in 64-bit arithmetic), other
    `n` truncate. -/
def fp2Convert10 (m : Nat) (e : Int) (n : Nat) : Nat × Int :=
  let p : Int := (n : Int) - 1 - Real.pwr2to10 (e + 63)
  let L := Real.pwr10to2 p
  let h := (m * powerOfTen p) >>> 64
  if n == 18 then
    let h := h >>> (-(e + L + 2)).toNat
    (((h + ((h <<< 1) &&& 2)) % 2 ^ 64) >>> 1, -p)
  else (h >>> (-(e + L + 1)).toNat, -p)

/-- `FpDecode`: sign, `isSpecial` (1 = Inf, 2 = NaN), the significant digits
    `z` (no trailing zeros) and the position of the decimal point `iDP`
    (the value is 0.z · 10^iDP). -/
structure Dec where
  neg : Bool
  special : Nat
  z : Array Nat
  iDP : Int

/-- `sqlite3FpDecode(&s, r, iRound, mxRound)`. -/
def fpDecode (r : Float) (iRound0 : Int) (mxRound : Nat) : Dec := Id.run do
  let b := Real.bits r
  let mag := b % 2 ^ 63
  if mag == 0 then return ⟨false, 0, #[0], 1⟩
  let neg := b >>> 63 == 1
  let ex := mag >>> 52
  let frac := mag % 2 ^ 52
  if ex == 2047 then return ⟨neg, if frac == 0 then 1 else 2, #[], 0⟩
  let (m, e) : Nat × Int :=
    if ex == 0 then
      let nn := 64 - Real.Nat.bitLen frac
      (frac * 2 ^ nn, -1074 - (nn : Int))
    else (frac * 2 ^ 11 + 2 ^ 63, (ex : Int) - 1086)
  let nconv : Nat := if iRound0 ≤ 0 || iRound0 ≥ 18 then 18 else iRound0.toNat + 1
  let (v, exp) := fp2Convert10 m e nconv
  let mut z := (Real.digitsOf v).toArray
  let mut n := z.size
  let mut iDP : Int := (n : Int) + exp
  let mut iRound := iRound0
  if iRound ≤ 0 then
    iRound := iDP - iRound
    if iRound == 0 && z[0]! ≥ 5 then
      iRound := 1
      z := #[0] ++ z
      n := n + 1
      iDP := iDP + 1
  if iRound > 0 && (iRound < (n : Int) || n > mxRound) then
    if iRound > (mxRound : Int) then iRound := mxRound
    if iRound == 17 then
      -- shorten when the shorter decimal reads back as the same double
      let ar := Real.ofBits mag
      if z[15]! == 9 && z[14]! == 9 then
        let mut jj := 14
        for _ in [0:14] do  -- `jj` counts down from 14
          if !(jj > 0 && z[jj - 1]! == 9) then break
          jj := jj - 1
        let v2 := if jj == 0 then 1 else Real.ofDigits (z.toList.take jj) + 1
        if ar == Real.ofDecimal v2 (exp + n - jj) then iRound := jj + 1
      else if iDP ≥ n || (z[15]! == 0 && z[14]! == 0 && z[13]! == 0) then
        let mut jj := 13
        for _ in [0:13] do  -- `jj` counts down from 13
          if !(jj > 0 && z[jj - 1]! == 0) then break
          jj := jj - 1
        let v2 := Real.ofDigits (z.toList.take jj)
        if ar == Real.ofDecimal v2 (exp + n - jj) then iRound := jj + 1
    let k := iRound.toNat
    if z[k]! ≥ 5 then
      let (z', grew) := Real.incAt (z.extract 0 k) (k - 1)
      z := z'
      n := if grew then k + 1 else k
      if grew then iDP := iDP + 1
    else
      z := z.extract 0 k
      n := k
  for _ in [0:n] do  -- `n` counts down
    if !(n > 0 && z[n - 1]! == 0) then break
    n := n - 1
  return ⟨neg, 0, z.extract 0 n, iDP⟩

/-! ## The conversion table (`fmtinfo[]`) -/

inductive Kind where
  | radix | float | exp | generic | size | string | dynstring | percent | charx
  | escq | escQ | token | srcitem | pointer | escw | ordinal | decimal | escj | escJ
  deriving BEq, Inhabited

structure Info where
  kind : Kind
  base : Nat := 10
  signed : Bool := false
  /-- digits `0123456789ABCDEF` (and exponent letter `E`) vs lower case -/
  upper : Bool := false
  /-- the `#` prefix: `0x`, `0`, `0X` -/
  pre : String := ""
  deriving Inhabited

def info? (c : UInt8) : Option Info :=
  match Char.ofNat c.toNat with
  | 'd' => some { kind := .decimal, signed := true, upper := true }
  | 'i' => some { kind := .decimal, signed := true, upper := true }
  | 'u' => some { kind := .decimal, upper := true }
  | 'e' => some { kind := .exp, signed := true }
  | 'E' => some { kind := .exp, signed := true, upper := true }
  | 'f' => some { kind := .float, signed := true, upper := true }
  | 'g' => some { kind := .generic, signed := true }
  | 'G' => some { kind := .generic, signed := true, upper := true }
  | 'j' => some { kind := .escj }
  | 'J' => some { kind := .escJ }
  | 'Q' => some { kind := .escQ }
  | 'q' => some { kind := .escq }
  | 'w' => some { kind := .escw }
  | 'p' => some { kind := .pointer, base := 16, upper := true, pre := "0x" }
  | 'S' => some { kind := .srcitem }
  | 'T' => some { kind := .token }
  | 'n' => some { kind := .size }
  | 'o' => some { kind := .radix, base := 8, upper := true, pre := "0" }
  | 'x' => some { kind := .radix, base := 16, pre := "0x" }
  | 'X' => some { kind := .radix, base := 16, upper := true, pre := "0X" }
  | '%' => some { kind := .percent }
  | 'r' => some { kind := .ordinal, signed := true, upper := true }
  | 's' => some { kind := .string }
  | 'z' => some { kind := .dynstring }
  | 'c' => some { kind := .charx }
  | _ => none

/-- The flags and sizes of one conversion. -/
structure Spec where
  left : Bool := false
  /-- `'+'`, `' '` or 0 -/
  fprefix : UInt8 := 0
  alt : Bool := false
  alt2 : Bool := false
  zpad : Bool := false
  thou : Bool := false
  width : Int := 0
  precision : Int := -1

/-! ## Fields -/

def digitChar (upper : Bool) (d : Nat) : UInt8 :=
  if d < 10 then (48 + d).toUInt8 else ((if upper then 55 else 87) + d).toUInt8

def toBase (base : Nat) (upper : Bool) (v : Nat) : List UInt8 :=
  let rec go (v : Nat) (acc : List UInt8) (fuel : Nat) : List UInt8 :=
    match fuel with
    | 0 => acc
    | f + 1 =>
      let acc := digitChar upper (v % base) :: acc
      if v / base > 0 then go (v / base) acc f else acc
  go v [] 70

/-- Insert `,` every three characters from the right. -/
def group3 (s : List UInt8) : List UInt8 :=
  let rec go : List UInt8 → Nat → List UInt8
    | [], _ => []
    | c :: rest, k => if k > 0 && k % 3 == 0 then 44 :: c :: go rest (k + 1) else c :: go rest (k + 1)
  (go s.reverse 0).reverse

/-- `%d %i %u %x %X %o %p %r`: the field before the width padding;
    `none` when SQLite's temporary buffer would exceed `mxAlloc`. -/
def intField (inf : Info) (raw : Int) (sp : Spec) : Option ByteArray :=
  let thou := sp.thou && inf.kind == .decimal
  let (lv, pfx) : Nat × UInt8 :=
    if inf.signed then (if raw < 0 then (raw.natAbs, 45) else (raw.toNat, sp.fprefix))
    else ((raw % 2 ^ 64).toNat, 0)
  let alt := sp.alt && lv != 0
  let pw : Int := if pfx != 0 then 1 else 0
  let prec := if sp.zpad && sp.precision < sp.width - pw then sp.width - pw else sp.precision
  if prec ≥ 37 && prec + 10 + (if thou then prec / 3 else 0) > mxAlloc then none else
  let ds := toBase inf.base inf.upper lv
  let ds := if inf.kind == .ordinal then
      let x := lv % 10
      let x := if x ≥ 4 || (lv / 10) % 10 == 1 then 0 else x
      ds ++ (match x with | 1 => "st" | 2 => "nd" | 3 => "rd" | _ => "th").toUTF8.toList
    else ds
  let ds := if prec > ds.length then List.replicate (prec.toNat - ds.length) 48 ++ ds else ds
  let ds := if thou then group3 ds else ds
  let ds := if pfx != 0 then pfx :: ds else ds
  let ds := if alt then inf.pre.toUTF8.toList ++ ds else ds
  some ⟨ds.toArray⟩

/-- `%f %e %E %g %G`. Returns the field and whether it still takes the
    generic width padding (only Inf/NaN do; the others pad themselves);
    `none` when the buffer it reserves would exceed `mxAlloc`. -/
def floatField (inf : Info) (r : Float) (sp : Spec) (nChar : Nat) : Option (ByteArray × Bool) := Id.run do
  let mut precision := if sp.precision < 0 then 6 else sp.precision
  if precision > 100000000 then precision := 100000000
  let mut xt := inf.kind
  if xt == .generic && precision == 0 then precision := 1
  let iRound : Int := if xt == .float then -precision else if xt == .generic then precision else precision + 1
  let s := fpDecode r iRound (if sp.alt2 then 20 else 16)
  let mut z := s.z
  let mut iDP := s.iDP
  if s.special == 2 then
    return some (bytesOf (if sp.zpad then "null" else "NaN"), true)
  if s.special == 1 then
    if sp.zpad then
      z := #[9]; iDP := 1000
    else
      let t := if s.neg then "-Inf" else if sp.fprefix != 0 then String.singleton (Char.ofNat sp.fprefix.toNat) ++ "Inf" else "Inf"
      return some (bytesOf t, true)
  let pfx : UInt8 :=
    if s.neg then
      (if sp.alt && sp.fprefix == 0 && xt == .float && iDP ≤ iRound then 0 else 45)
    else sp.fprefix
  let exp0 := iDP - 1
  let mut flagRtz := sp.alt2
  if xt == .generic then
    precision := precision - 1
    flagRtz := !sp.alt
    if exp0 < -4 || exp0 > precision then xt := .exp
    else
      precision := precision - exp0
      xt := .float
  let mut e2 : Int := if xt == .exp then 0 else iDP - 1
  let szBufNeeded : Int := max e2 0 + precision + sp.width + 10 + (if sp.thou && e2 > 0 then (e2 + 2) / 3 else 0)
  if (nChar : Int) + szBufNeeded + 1 > mxAlloc then return none
  let flagDp := precision > 0 || sp.alt || sp.alt2
  let n := z.size
  let mut out : Array UInt8 := #[]
  if pfx != 0 then out := out.push pfx
  let mut j := 0
  if e2 < 0 then out := out.push 48
  else if sp.thou then
    for _ in [0:(e2 + 1).toNat] do  -- `e2` counts down to -1
      if !(e2 ≥ 0) then break
      if j < n then
        out := out.push (48 + z[j]!).toUInt8; j := j + 1
      else out := out.push 48
      if e2 % 3 == 0 && e2 > 1 then out := out.push 44
      e2 := e2 - 1
  else
    j := min (e2 + 1).toNat n
    for k in [0:j] do out := out.push (48 + z[k]!).toUInt8
    e2 := e2 - j
    if e2 ≥ 0 then
      out := out ++ Array.replicate (e2 + 1).toNat 48
      e2 := -1
  if flagDp then out := out.push 46
  if e2 < -1 && precision > 0 then
    let nn := min (-1 - e2) precision
    out := out ++ Array.replicate nn.toNat 48
    precision := precision - nn
  if precision > 0 then
    let nn := min ((n : Int) - j) precision
    if nn > 0 then
      for k in [j:j + nn.toNat] do out := out.push (48 + z[k]!).toUInt8
      precision := precision - nn
    if precision > 0 && !flagRtz then
      out := out ++ Array.replicate precision.toNat 48
  if flagRtz && flagDp then
    for _ in [0:out.size] do  -- each iteration pops a byte
      if !(out.back? == some 48) then break
      out := out.pop
    if out.back? == some 46 then
      out := if sp.alt2 then out.push 48 else out.pop
  if xt == .exp then
    let mut ex := iDP - 1
    out := out.push (if inf.upper then 69 else 101)
    if ex < 0 then
      out := out.push 45; ex := -ex
    else out := out.push 43
    if ex ≥ 100 then
      out := out.push (48 + ex / 100).toNat.toUInt8
      ex := ex % 100
    out := out.push (48 + ex / 10).toNat.toUInt8
    out := out.push (48 + ex % 10).toNat.toUInt8
  let len := out.size
  if (len : Int) < sp.width then
    let nPad := (sp.width - len).toNat
    if sp.left then out := out ++ Array.replicate nPad 32
    else if !sp.zpad then out := Array.replicate nPad 32 ++ out
    else
      let adj := if pfx != 0 then 1 else 0
      out := out.extract 0 adj ++ Array.replicate nPad 48 ++ out.extract adj out.size
  return some (⟨out⟩, false)

/-- `adjust_width_for_utf8`: with `!`, the width counts characters. -/
def adjWidth (alt2 : Bool) (b : ByteArray) (width : Int) : Int :=
  if alt2 && width > 0 then width + (b.toList.filter isCont).length else width

/-- `%q %Q %w`; `none` when the temporary buffer would exceed `mxAlloc`. -/
def escField (kind : Kind) (arg : Option ByteArray) (sp : Spec) : Option ByteArray := Id.run do
  let isQ := kind == .escQ
  let (esc, needQ) : ByteArray × Nat := match arg with
    | none => (bytesOf (if isQ then "NULL" else "(NULL)"), 0)
    | some s => (s, if isQ then 1 else 0)
  let q : UInt8 := if kind == .escw then 34 else 39
  let mut alt := if kind == .escw then false else sp.alt
  let mut k := sp.precision
  let mut i := 0
  let mut n : Nat := 0
  -- `i` grows and `bat esc i` is 0 from `esc.size` on: `esc.size + 1` iterations
  for _ in [0:esc.size + 1] do
    if !(k != 0 && bat esc i != 0) then break
    let ch := bat esc i
    if ch == q then n := n + 1
    if sp.alt2 && ch &&& 0xc0 == 0xc0 then
      for _ in [0:esc.size + 1] do
        if !isCont (bat esc (i + 1)) then break
        i := i + 1
    i := i + 1
    k := k - 1
  let mut needQuote := needQ
  if alt then
    let pre := (esc.extract 0 i).toList
    let nBack := (pre.filter (· == 92)).length
    let nCtrl := (pre.filter (· ≤ 0x1f)).length
    if nCtrl > 0 || kind == .escq then
      n := n + nBack + 5 * nCtrl
      if isQ then
        n := n + 10
        needQuote := 2
    else alt := false
  n := n + i + 3
  if n > 70 && n > mxAlloc then return none
  let mut out : Array UInt8 := #[]
  if needQuote == 2 then out := out ++ "unistr('".toUTF8.data
  else if needQuote == 1 then out := out.push 39
  let hex := "0123456789abcdef".toUTF8
  for t in [0:i] do
    let ch := esc[t]!
    out := out.push ch
    if ch == q then out := out.push ch
    else if alt && ch == 92 then out := out.push 92
    else if alt && ch ≤ 0x1f then
      out := out.pop ++ #[92, 117, 48, 48, if ch ≥ 0x10 then 49 else 48, hex[(ch &&& 0xf).toNat]!]
  if needQuote != 0 then
    out := out.push 39
    if needQuote == 2 then out := out.push 41
  return some ⟨out⟩

/-- `%j %J`: the escaped text, with its own width padding. -/
def jsonField (kind : Kind) (arg : Option ByteArray) (sp : Spec) : ByteArray := Id.run do
  let mut out : Array UInt8 := #[]
  match arg with
  | none => if kind == .escJ then out := "null".toUTF8.data
  | some esc =>
    if kind == .escJ then out := out.push 34
    let mut px : Int := sp.precision
    if px < 0 then px := 0x7fffffff
    else if sp.alt2 then
      let mut i : Nat := 0
      -- these scans stop at the end of `esc` (`bat` is 0): `esc.size + 1` iterations
      for _ in [0:esc.size + 1] do
        if !((i : Int) < px && bat esc i != 0) then break
        if isCont (bat esc i) then px := px + 1
        i := i + 1
      if (i : Int) == px then
        for _ in [0:esc.size + 1] do
          if !isCont (bat esc px.toNat) then break
          px := px + 1
    let hex := "0123456789abcdef".toUTF8
    let mut i : Nat := 0
    let mut j : Nat := 0
    let mut stop := false
    -- `i` grows until the NUL at `esc.size` at the latest
    for _ in [0:esc.size + 1] do
      if !(!stop && (i : Int) < px) then break
      let ch := bat esc i
      if ch ≤ 0x1f || ch == 34 || ch == 92 then
        if j < i then out := out ++ (esc.extract j i).data
        j := i + 1
        if ch == 0 then stop := true
        else
          out := out.push 92
          if ch > 0x1f then out := out.push ch
          else if (1 <<< ch.toNat) &&& 0x3700 != 0 then
            out := out.push ("btn?fr".toUTF8[ch.toNat - 8]!)
          else
            out := out ++ (#[117, 48, 48, hex[(ch >>> 4).toNat]!, hex[(ch &&& 0xf).toNat]!] : Array UInt8)
      if !stop then i := i + 1
    if j < i then out := out ++ (esc.extract j i).data
    if kind == .escJ then out := out.push 34
  if sp.width > 0 then
    let n := out.size
    let len : Int := if sp.alt2 && n > 0 then n - (out.toList.filter isCont).length else n
    if sp.width > len then
      let spc := Array.replicate (sp.width - len).toNat (32 : UInt8)
      out := if !sp.left && n > 0 then spc ++ out else out ++ spc
  return ⟨out⟩

/-! ## The formatter -/

/-- `(int)` of a 64-bit value. -/
def toI32 (v : Int) : Int :=
  let u := v % 2 ^ 32
  if u ≥ 2 ^ 31 then u - 2 ^ 32 else u

/-- `sqlite3_value_double`. -/
def argReal : Value → Float
  | .null => 0.0
  | .int i => intToReal i
  | .real r => r
  | .text s | .blob s => (atof (cstr s)).value

/-- `sqlite3_value_text`, as a C string; NULL is a null pointer. -/
def argText : Value → Option ByteArray
  | .null => none
  | v => some (cstr (v.toText?.getD .empty))

/-- `sqlite3_str_vappendf` with `SQLITE_PRINTF_SQLFUNC` (arguments read from
    SQL values) into an accumulator limited to `mxAlloc`; `none` is
    SQLITE_TOOBIG. Conversions that are not available to SQL (`%T`, `%S`)
    and unknown ones end the formatting, keeping what was produced. -/
def format (fmt0 : ByteArray) (args : Array Value) : Option ByteArray := Id.run do
  let fmt := cstr fmt0
  let at_ := bat fmt
  let fits (out : ByteArray) (extra : Int) : Bool := (out.size : Int) + extra + 1 ≤ mxAlloc
  -- the generic width padding at the end of the switch
  let pad (b : ByteArray) (width : Int) (left : Bool) : ByteArray :=
    let w := width - b.size
    if w > 0 then (if left then b ++ rep w.toNat 32 else rep w.toNat 32 ++ b) else b
  let mut out : ByteArray := .empty
  let mut used : Nat := 0
  let mut i : Nat := 0
  -- Every loop below advances `i` through `fmt` (each conversion consumes its
  -- `%` and at least one byte; a 0 byte, as at `fmt.size`, ends it), so
  -- `fmt.size + 1` iterations suffice.
  for _ in [0:fmt.size + 1] do
    if !(i < fmt.size) then break
    if at_ i != 37 then
      let st := i
      for _ in [0:fmt.size + 1] do
        if !(i < fmt.size && at_ i != 37) then break
        i := i + 1
      out := out ++ fmt.extract st i
      if !fits out 0 then return none
      if i ≥ fmt.size then break
    -- fmt[i] is '%'
    i := i + 1
    let mut c := at_ i
    if c == 0 then
      out := out.push 37
      if !fits out 0 then return none
      break
    let mut sp : Spec := {}
    let mut done := false
    for _ in [0:fmt.size + 1] do
      if c == 45 then sp := { sp with left := true }
      else if c == 43 then sp := { sp with fprefix := 43 }
      else if c == 32 then sp := { sp with fprefix := 32 }
      else if c == 35 then sp := { sp with alt := true }
      else if c == 33 then sp := { sp with alt2 := true }
      else if c == 48 then sp := { sp with zpad := true }
      else if c == 44 then sp := { sp with thou := true }
      else if c == 108 then
        i := i + 1; c := at_ i
        if c == 108 then
          i := i + 1; c := at_ i
        done := true
      else if 49 ≤ c && c ≤ 57 then
        let mut wx : Nat := (c - 48).toNat
        i := i + 1; c := at_ i
        for _ in [0:fmt.size + 1] do
          if !(48 ≤ c && c ≤ 57) then break
          wx := (wx * 10 + (c - 48).toNat) % 2 ^ 32
          i := i + 1; c := at_ i
        sp := { sp with width := wx % 2 ^ 31 }
        if c != 46 && c != 108 then done := true
        else i := i - 1
      else if c == 42 then
        let v := if used < args.size then args[used]!.toInt else 0
        if used < args.size then used := used + 1
        let w := toI32 v
        if w < 0 then
          sp := { sp with left := true, width := if w ≥ -2147483647 then -w else 0 }
        else sp := { sp with width := w }
        c := at_ (i + 1)
        if c != 46 && c != 108 then
          i := i + 1; c := at_ i
          done := true
      else if c == 46 then
        i := i + 1; c := at_ i
        if c == 42 then
          let v := if used < args.size then args[used]!.toInt else 0
          if used < args.size then used := used + 1
          let pr := toI32 v
          sp := { sp with precision := if pr < 0 then (if pr ≥ -2147483647 then -pr else -1) else pr }
          i := i + 1; c := at_ i
        else
          let mut px : Nat := 0
          for _ in [0:fmt.size + 1] do
            if !(48 ≤ c && c ≤ 57) then break
            px := (px * 10 + (c - 48).toNat) % 2 ^ 32
            i := i + 1; c := at_ i
          sp := { sp with precision := px % 2 ^ 31 }
        if c == 108 then i := i - 1
        else done := true
      else done := true
      if done then break
      i := i + 1; c := at_ i
      if c == 0 then break
    -- c = fmt[i] is the conversion character
    let some inf := info? c | break
    let nextArg : Option Value := if used < args.size then some args[used]! else none
    let use1 : Nat := if used < args.size then used + 1 else used
    match inf.kind with
    | .token | .srcitem => break
    | .size => pure ()
    | .percent =>
      if !fits out (max sp.width 1) then return none
      out := out ++ pad (bytesOf "%") sp.width sp.left
    | .decimal | .radix | .pointer | .ordinal =>
      used := use1
      match intField inf ((nextArg.map Value.toInt).getD 0) sp with
      | none => return none
      | some b =>
        if !fits out (max sp.width b.size) then return none
        out := out ++ pad b sp.width sp.left
    | .float | .exp | .generic =>
      used := use1
      match floatField inf (argReal (nextArg.getD .null)) sp out.size with
      | none => return none
      | some (b, gp) =>
        if !fits out (max sp.width b.size) then return none
        out := out ++ (if gp then pad b sp.width sp.left else b)
    | .string | .dynstring =>
      used := use1
      let s := ((nextArg.getD .null) |> argText).getD .empty
      let len : Nat :=
        if sp.precision ≥ 0 then
          if sp.alt2 then Id.run do
            let mut k := 0
            let mut p := sp.precision
            -- `k` grows; `bat s k` is 0 from `s.size` on
            for _ in [0:s.size + 1] do
              if !(p > 0 && bat s k != 0) then break
              p := p - 1
              let ch := bat s k
              k := k + 1
              if ch ≥ 0xc0 then
                for _ in [0:s.size + 1] do
                  if !isCont (bat s k) then break
                  k := k + 1
            return k
          else min sp.precision.toNat s.size
        else s.size
      let b := s.extract 0 len
      let w := adjWidth sp.alt2 b sp.width
      if !fits out (max w b.size) then return none
      out := out ++ pad b w sp.left
    | .charx =>
      used := use1
      let buf : ByteArray := match (nextArg.getD .null) |> argText with
        | none => ⟨#[0]⟩
        | some s =>
          if s.size == 0 then ⟨#[0]⟩ else Id.run do
            let mut b : Array UInt8 := #[s[0]!]
            if s[0]! &&& 0xc0 == 0xc0 then
              for _ in [0:4] do  -- `b` grows to at most 4 bytes
                if !(b.size < 4 && isCont (bat s b.size)) then break
                b := b.push s[b.size]!
            return ⟨b⟩
      let mut w := sp.width
      let mut copies : Nat := 1
      let mut pre : Nat := 0
      if sp.precision > 1 then
        w := w - (sp.precision - 1)
        if w > 1 && !sp.left then
          pre := (w - 1).toNat; w := 0
        copies := sp.precision.toNat
      let w2 := adjWidth true buf w
      let tail := max (w2 - buf.size) 0
      if !fits out (((pre + copies * buf.size : Nat) : Int) + tail) then return none
      out := out ++ rep pre 32
      for _ in [0:copies - 1] do out := out ++ buf
      out := out ++ pad buf w2 sp.left
    | .escq | .escQ | .escw =>
      used := use1
      match escField inf.kind ((nextArg.getD .null) |> argText) sp with
      | none => return none
      | some b =>
        let w := adjWidth sp.alt2 b sp.width
        if !fits out (max w b.size) then return none
        out := out ++ pad b w sp.left
    | .escj | .escJ =>
      used := use1
      if !fits out sp.width then return none
      out := out ++ jsonField inf.kind ((nextArg.getD .null) |> argText) sp
      if !fits out 0 then return none
    i := i + 1
  return some out

/-! ## The SQL functions -/

def tooBig : Err := { code := SQLITE_TOOBIG, msg := "string or blob too big" }

/-- `printf(fmt, args…)` / `format(…)`: `none` if this module does not implement `name`. -/
def scalar? (name : String) (args : List Value) : Option (Except Err Value) :=
  if name != "printf" && name != "format" then none else
  some <| match args with
    | [] => .ok .null
    | f :: rest => match argText f with
      | none => .ok .null
      | some fmt => match format fmt rest.toArray with
        | some b => .ok (.text b)
        | none => .error tooBig

/-- `round(r, n)` as SQLite computes it (`roundFunc`): unchanged beyond 2^52,
    `(i64)(r ± 0.5)` for `n = 0`, else `%!.*f` read back by `sqlite3AtoF`. -/
def round? (r : Float) (n : Int) : Option Float :=
  if r < -4503599627370496.0 || r > 4503599627370496.0 then some r
  else if n == 0 then some (intToReal (realToInt (if r < 0 then r - 0.5 else r + 0.5)))
  else match format (bytesOf "%!.*f") #[.int n, .real r] with
    | some b => some (atof b).value
    | none => some r

/-- `quote()` of a REAL (`sqlite3QuoteValue`): `%!0.17g`, so an infinity
    shows as `9.0e+999`. -/
def quoteReal? (r : Float) : Option String :=
  (format (bytesOf "%!0.17g") #[.real r]).map fun b => String.fromUTF8! b

end Sql.Printf
