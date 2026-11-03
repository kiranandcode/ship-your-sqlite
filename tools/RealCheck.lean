/- real_check < lines "HEXBITS text": compares Sql.Real.render with SQLite's
   rendering (experiments/real/render.c output). -/
import Sql.Real

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let mut bad := 0
  let mut tot := 0
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    match (line.trimRight).splitOn " " with
    | [(h : String), (want : String)] =>
      let b := (h.foldl (fun a c => a * 16 + (if c.isDigit then c.toNat - 48 else c.toNat - 87)) 0)
      let got := Sql.Real.render (Sql.Real.ofBits b)
      tot := tot + 1
      if got != want then
        bad := bad + 1
        if bad ≤ 5 then IO.println s!"MISMATCH {h} {want} {got}"
    | _ => pure ()
  IO.println s!"{tot} values, {bad} mismatches"
  return if bad == 0 then 0 else 1
