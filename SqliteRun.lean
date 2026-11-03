/-
  sqlite_run [--fuel N] [--stats] < script.sql

  Runs the Lean Clight export of c/sqlprog.c (the whole sqlite3.c and
  c/driver.c, `Sqlprog.prog`) under Clean's interpreter with the external
  model of `Run.Ext`, the script as fd 0. stdout is what the driver printed.
  Exit codes as clight_run: the program's status; 126 stuck, 127 unsupported
  external case, 124 out of fuel, 125 harness error.
-/
import Sqlprog
import Run.Runner

def fail (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln s!"[sqlite_run] {msg}"
  return code

def main (args : List String) : IO UInt32 := do
  let mut fuel := 0
  let mut stats := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--fuel" :: n :: r => fuel := n.toNat!; rest := r
    | "--stats" :: r => stats := true; rest := r
    | _ :: r => rest := r
    | [] => rest := []
  let input ← (← IO.getStdin).readBinToEnd
  let t0 ← IO.monoMsNow
  let r := Run.runProgram Sqlprog.prog fuel { stdin := input }
  let stdout ← IO.getStdout
  stdout.write r.world.out
  stdout.flush
  (← IO.getStderr).write r.world.err
  let t1 ← IO.monoMsNow
  if stats then
    IO.eprintln s!"[sqlite_run] steps={r.steps} externals={r.externals} flat={r.flat} run_ms={t1 - t0}"
  match r.outcome with
  | .exit code => return (BitVec.ofInt 8 code).toNat.toUInt32
  | .stuck why => fail 126 s!"STUCK after {r.steps} steps: {why}"
  | .unsupported why => fail 127 s!"UNSUPPORTED: {why}"
  | .fuel => fail 124 s!"FUEL exhausted after {r.steps} steps"
  | .noinit why => fail 125 s!"NOINIT: {why}"
