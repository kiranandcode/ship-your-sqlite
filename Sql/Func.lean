/-
  The built-in scalar function library (https://sqlite.org/lang_corefunc.html,
  lang_mathfunc.html). Aggregates and window functions are in `Sql.Query`;
  date/time and JSON functions in their own files.
-/
import Sql.Eval

namespace Sql

def textOf (v : Value) : ByteArray := v.toText?.getD .empty

def utf8Len (b : ByteArray) : Nat := (utf8Chars b).length

def hexOf (b : ByteArray) : String :=
  let d := "0123456789ABCDEF".toList
  String.ofList (b.toList.flatMap fun c => [d[c.toNat / 16]!, d[c.toNat % 16]!])

/-- `quote(x)` -/
def quoteValue : Value → String
  | .null => "NULL"
  | .int i => toString i
  | .real r =>
    -- quote() of a REAL: %!0.15g, or %!0.20e if that does not round-trip
    Real.render r
  | .text s =>
    let t := String.fromUTF8! s
    "'" ++ String.intercalate "''" (t.splitOn "'") ++ "'"
  | .blob b => "X'" ++ hexOf b ++ "'"

/-- substr(X, Y, Z) on characters (text) or bytes (blob): substrFunc's
    arithmetic, with Z absent being LARGEST_INT64. -/
def substrOf (units : List (List UInt8)) (y : Int) (z : Option Int) : List (List UInt8) :=
  let len : Int := units.length
  let (p1, p2) : Int × Int := Id.run do
    let mut p1 := y
    let mut p2 : Int := z.getD (2 ^ 63 - 1)
    if p1 < 0 then
      p1 := p1 + len
      if p1 < 0 then
        if p2 < 0 then p2 := 0 else p2 := p2 + p1
        p1 := 0
    else if p1 > 0 then p1 := p1 - 1
    else if p2 > 0 then p2 := p2 - 1
    if p2 < 0 then
      if p2 < -p1 then p2 := p1 else p2 := -p2
      p1 := p1 - p2
    return (p1, p2)
  (units.drop p1.toNat).take p2.toNat

def trimBy (s : List (List UInt8)) (set : List (List UInt8)) (left right : Bool) : List (List UInt8) :=
  let s := if left then s.dropWhile (set.contains ·) else s
  if right then (s.reverse.dropWhile (set.contains ·)).reverse else s

/-- `round(r, n)`. PLACEHOLDER: SQLite rounds through its printf (`%!.*f`, the
    approximate decimal of `sqlite3FpDecode`) and reads the text back; this uses
    exact decimal rounding, half away from zero, until `Sql.Printf` exists. -/
def roundTo (r : Float) (n : Int) : Float :=
  if r.abs ≥ 4503599627370496.0 then r
  else if n == 0 then
    let t := (r.abs + 0.5).floor
    if r < 0 then -t else t
  else
    -- "%.*f" then atof: the double nearest to the decimal rounding of r
    let k := n.toNat
    -- exact decimal rounding, half away from zero, on the exact value of r
    let b := Real.bits r.abs
    let ex := ((b >>> 52) % 2048 : Nat)
    let m : Nat := if ex == 0 then b % 2 ^ 52 else b % 2 ^ 52 + 2 ^ 52
    let e : Int := if ex == 0 then -1074 else (ex : Int) - 1075
    -- value = m * 2^e; q = round(value * 10^k)
    let (num, den) : Nat × Nat := if e ≥ 0 then (m * 2 ^ e.toNat * 10 ^ k, 1) else (m * 10 ^ k, 2 ^ (-e).toNat)
    let q := (2 * num + den) / (2 * den)
    let res := Real.ofDecimal q (-(k : Int))
    if r < 0 then -res else res

def mathUnary (name : String) : Option (Float → Float) :=
  match name.toLower with
  | "acos" => some Float.acos | "asin" => some Float.asin | "atan" => some Float.atan
  | "acosh" => some Float.acosh | "asinh" => some Float.asinh | "atanh" => some Float.atanh
  | "cos" => some Float.cos | "sin" => some Float.sin | "tan" => some Float.tan
  | "cosh" => some Float.cosh | "sinh" => some Float.sinh | "tanh" => some Float.tanh
  | "exp" => some Float.exp | "ln" => some Float.log | "log10" => some Float.log10
  | "log2" => some Float.log2 | "sqrt" => some Float.sqrt
  | "degrees" => some fun x => x * 180.0 / 3.141592653589793
  | "radians" => some fun x => x * 3.141592653589793 / 180.0
  | _ => none

/-- The value of a math function result: NaN is NULL. -/
def mathResult (r : Float) : Value := realResult r

/-- A number argument of a math function: NULL or non-numeric text gives NULL. -/
def mathArg (v : Value) : Option Float :=
  match v with
  | .null => none
  | .int i => some (intToReal i)
  | .real r => some r
  | .text s | .blob s =>
    let a := atof s
    if a.whole then some a.value else none

end Sql
