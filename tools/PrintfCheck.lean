/- printf_check < cases.txt: compares `Sql.Printf` (printf()/format(),
   round(), quote() of a REAL) with SQLite's answers, as written by
   experiments/printf/rand.c (see there for the line format). -/
import Sql.Printf

open Sql

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toNat - 87

def unhex (s : String) : ByteArray :=
  if s == "-" then .empty else Id.run do
    let cs := s.toList.toArray
    let mut out : ByteArray := .empty
    for i in [0:cs.size / 2] do
      out := out.push (hexVal cs[2 * i]! * 16 + hexVal cs[2 * i + 1]!).toUInt8
    return out

def hexNat (s : String) : Nat := s.foldl (fun a c => a * 16 + hexVal c) 0

def toHex (b : ByteArray) : String :=
  if b.size == 0 then "-" else
  String.join (b.toList.map fun c =>
    let d := "0123456789abcdef".toList
    String.ofList [d[c.toNat / 16]!, d[c.toNat % 16]!])

def parseArg (s : String) : Value :=
  let t := s.drop 1 |>.toString
  match s.front with
  | 'i' => .int t.toInt!
  | 'r' => .real (Real.ofBits (hexNat t))
  | 't' => .text (unhex t)
  | 'b' => .blob (unhex t)
  | _ => .null

def renderResult : Option (Except Err Value) → String
  | some (.ok .null) => "N"
  | some (.ok (.text b)) => "T" ++ toHex b
  | some (.ok _) => "?"
  | some (.error e) => s!"E{e.code}"
  | none => "unimplemented"

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut bad := 0
  let mut tot := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let ws := (line.trimAsciiEnd.toString.splitOn " ")
    match ws with
    | "P" :: rest =>
      let args := rest.takeWhile (· != "=")
      let want := (rest.dropWhile (· != "=")).drop 1 |>.headD ""
      let got := renderResult (Printf.scalar? "printf" (args.map parseArg))
      tot := tot + 1
      if got != want then
        bad := bad + 1
        if bad ≤ 20 then IO.println s!"MISMATCH {line.trimAsciiEnd.toString}\n   got {got}"
    | ["R", b, n, want] =>
      let r := Real.ofBits (hexNat b)
      let got := (Printf.round? r n.toInt!).getD r
      tot := tot + 1
      if Real.bits got != hexNat want then
        bad := bad + 1
        if bad ≤ 20 then IO.println s!"MISMATCH {line.trimAsciiEnd.toString}\n   got {Real.bits got}"
    | ["Q", b, want] =>
      let got := (Printf.quoteReal? (Real.ofBits (hexNat b))).getD ""
      tot := tot + 1
      if toHex got.toUTF8 != want then
        bad := bad + 1
        if bad ≤ 20 then IO.println s!"MISMATCH {line.trimAsciiEnd.toString}\n   got {got}"
    | _ => pure ()
  IO.println s!"{tot} cases, {bad} mismatches"
  return if bad == 0 then 0 else 1
