/-
  REAL values: IEEE binary64, decimal conversion both ways, and SQLite's text
  rendering of a REAL.

  Rendering (`render`) is SQLite's `%!.17g` (`sqlite3FpDecode`). It is *not*
  correct rounding to 17 significant digits: the 18-digit intermediate of
  `sqlite3Fp2Convert10` takes its decimal scale from the estimate
  `pwr2to10` (so it has 18 or 19 digits), multiplies by 10^p truncated to 64
  bits, and rounds half up; the result is then rounded to 17 digits and
  shortened when digits 15–16 are `99` or 14–16 are `000` and the shorter
  decimal reads back as the same double. Stated here on exact integers.
  Checked against the native build on 1,614k doubles (every binary exponent),
  0 mismatches (`experiments/real/`); correct rounding to 17 digits differs on
  0.9 % of them.
-/
namespace Sql.Real

/-- The bits of a double. -/
def bits (x : Float) : Nat := x.toBits.toNat
def ofBits (b : Nat) : Float := Float.ofBits b.toUInt64

def Nat.bitLen (n : Nat) : Nat := n.log2 + (if n == 0 then 0 else 1)

/-- The double nearest to `q · 2^(-s)`, plus `sticky` (a nonzero amount below
    one unit of `q`), ties to even. Handles subnormals and overflow. -/
def roundScaled (q : Nat) (sticky : Bool) (s : Int) : Float :=
  if q == 0 then 0.0 else
  let b := Nat.bitLen q
  let E : Int := (b : Int) - 1 - s
  let prec : Int := if E ≥ -1022 then 53 else 53 - (-1022 - E)
  if prec ≤ 0 then
    -- below half the smallest subnormal unless exactly at it or above
    let half : Int := -1075        -- value 2^-1075
    if E > half || (E == half && (sticky || q != 2 ^ (b - 1))) then Float.ofBinaryScientific 1 (-1074)
    else 0.0
  else
    let drop : Int := (b : Int) - prec
    if drop ≤ 0 then Float.ofBinaryScientific q (-s)
    else
      let d := drop.toNat
      let m := q >>> d
      let rem := q % 2 ^ d
      let half := 2 ^ (d - 1)
      let up := rem > half || (rem == half && (sticky || m % 2 == 1))
      let m := if up then m + 1 else m
      Float.ofBinaryScientific m (drop - s)

/-- The double nearest to `d · 10^k` (ties to even), as SQLite's
    `sqlite3Fp10Convert2` computes it (R. Cox's correctly rounded algorithm). -/
def ofDecimal (d : Nat) (k : Int) : Float :=
  if d == 0 then 0.0
  else if k ≥ 0 then roundScaled (d * 10 ^ k.toNat) false 0
  else
    let den := 10 ^ (-k).toNat
    let s : Nat := 64 + Nat.bitLen den
    let num := d * 2 ^ s
    roundScaled (num / den) (num % den != 0) s

def pwr2to10 (x : Int) : Int := (x * 78913) >>> 18
def pwr10to2 (x : Int) : Int := (x * 108853) >>> 15

/-- `sqlite3Fp2Convert10(m, e, 18)` for a positive finite double: digits `D`
    and exponent `x` with the double ≈ `D · 10^x`. -/
def fp2Convert10 (b : Nat) : Nat × Int :=
  let ex := (b >>> 52) % 2048
  let frac := b % 2 ^ 52
  let (v, e) : Nat × Int :=
    if ex == 0 then
      let nn := 64 - Nat.bitLen frac
      (frac * 2 ^ nn, -1074 - (nn : Int))
    else (frac * 2 ^ 11 + 2 ^ 63, (ex : Int) - 1086)
  let p := 17 - pwr2to10 (e + 63)
  let L := pwr10to2 p
  -- 10^p as a 64-bit fraction, truncated: floor(10^p · 2^(63-L))
  let x : Nat :=
    if p ≥ 0 then
      if 63 - L ≥ 0 then 10 ^ p.toNat * 2 ^ (63 - L).toNat else 10 ^ p.toNat / 2 ^ (L - 63).toNat
    else
      if 63 - L ≥ 0 then 2 ^ (63 - L).toNat / 10 ^ (-p).toNat
      else 0
  let h := (v * x) >>> 64
  let h := h >>> (-(e + L + 2)).toNat
  ((h + ((h <<< 1) &&& 2)) >>> 1, -p)

def digitsOf (n : Nat) : List Nat := (Nat.toDigits 10 n).map fun c => c.toNat - '0'.toNat
def ofDigits (ds : List Nat) : Nat := ds.foldl (fun a d => a * 10 + d) 0

/-- Add one at position `j` (0-based) of a digit list, carrying left.
    Returns the digits and whether a new leading digit appeared. -/
def incAt (z : Array Nat) (j : Nat) : Array Nat × Bool :=
  let d := z[j]! + 1
  if d ≤ 9 then (z.set! j d, false) else
  let z := z.set! j 0
  match j with
  | 0 => (#[1] ++ z, true)
  | j + 1 => incAt z j

/-- The length of the prefix `z[0..j)` without its trailing run of digit `d`. -/
def trimBack (z : Array Nat) (d : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => if z[j]! == d then trimBack z d j else j + 1

/-- SQLite's text of a REAL (`%!.17g`): `"Inf"`, `"-Inf"`, `"0.0"`, `"1.5"`,
    `"1.0e-05"`, `"1.2345678901234568e+17"`. NaN never reaches here (SQLite
    turns a NaN result into NULL). -/
def render (r : Float) : String :=
  let b := bits r
  let neg := b >>> 63 == 1
  let sign := if neg then "-" else ""
  let mag := b % 2 ^ 63
  if mag == 0 then "0.0"
  else if (mag >>> 52) == 2047 then sign ++ "Inf"
  else
    let ar := ofBits mag
    let (v, exp) := fp2Convert10 mag
    let z0 := (digitsOf v).toArray
    let n := z0.size
    let iDP0 : Int := n + exp
    let iRound : Nat := Id.run do
      let mut iRound := 17
      if z0[15]! == 9 && z0[14]! == 9 then
        let jj := trimBack z0 9 14
        let v2 := if jj == 0 then 1 else ofDigits (z0.toList.take jj) + 1
        if ar == ofDecimal v2 (exp + n - jj) then iRound := jj + 1
      else if iDP0 ≥ n || (z0[15]! == 0 && z0[14]! == 0 && z0[13]! == 0) then
        let jj := trimBack z0 0 13
        let v2 := ofDigits (z0.toList.take jj)
        if ar == ofDecimal v2 (exp + n - jj) then iRound := jj + 1
      return iRound
    let (z, iDP) : Array Nat × Int :=
      if iRound < n then
        let z := z0.extract 0 iRound
        if z0[iRound]! ≥ 5 then
          let (z', grew) := incAt z (iRound - 1)
          (if grew then z'.extract 0 (iRound + 1) else z', if grew then iDP0 + 1 else iDP0)
        else (z, iDP0)
      else (z0, iDP0)
    -- strip trailing zeros
    let ds := (z.toList.reverse.dropWhile (· == 0)).reverse
    let ds := if ds.isEmpty then [0] else ds
    let cs := ds.map fun d => Char.ofNat (d + '0'.toNat)
    let s := String.ofList cs
    let take (k : Nat) := String.ofList (cs.take k)
    let drop (k : Nat) := String.ofList (cs.drop k)
    let e10 := iDP - 1
    if e10 < -4 || e10 ≥ 17 then
      let mant := take 1 ++ "." ++ (if cs.length > 1 then drop 1 else "0")
      let ea := e10.natAbs
      sign ++ mant ++ "e" ++ (if e10 < 0 then "-" else "+") ++ (if ea < 10 then "0" else "") ++ toString ea
    else if iDP ≤ 0 then sign ++ "0." ++ "".pushn '0' (-iDP).toNat ++ s
    else if iDP ≥ s.length then sign ++ s ++ "".pushn '0' (iDP.toNat - s.length) ++ ".0"
    else sign ++ take iDP.toNat ++ "." ++ drop iDP.toNat

end Sql.Real
