/-
  clight_run FILE.lean [--fuel N] [--stats]

  Elaborates a `clightgen -lean` output in-process against the prebuilt
  CCLib/Clightdefs (no .olean written), evaluates `<Namespace>.prog`, and runs
  it with `Run.runProgram`. For small programs (the pilot); the SQLite export
  is compiled to .oleans instead (PHASES.md 1.2).

  stdout : the bytes the program wrote to fd 1 (fd 2 goes to stderr)
  exit   : the program's status; 125 harness error, 126 stuck (undefined
           behaviour, or an external outside the model), 127 unsupported
           external case, 124 out of fuel.

  The in-process elaboration is ship-your-tcc's `clight_run` (ATTRIBUTION.md).
-/
import Lean
import Run.Runner

open Lean Elab

def fail (code : UInt32) (msg : String) : IO UInt32 := do
  IO.eprintln s!"[clight_run] {msg}"
  return code

unsafe def loadProg (file : System.FilePath) : IO (Except String CC.Program) := do
  let input ← IO.FS.readFile file
  let lines := input.splitOn "\n"
  let body := String.intercalate "\n" (lines.map fun l =>
    if l.startsWith "import " then "" else l)
  let ns? := lines.findSome? fun l =>
    if l.startsWith "namespace " then some ((l.drop 10).trimRight.toString) else none
  let some ns := ns? | return .error "no `namespace` line in the generated file"
  let env ← importModules #[{ module := `Clightdefs }, { module := `CCLib }] {} (loadExts := true)
  let (env, msgs) ← Lean.Elab.process body env {} (some file.toString)
  if msgs.hasErrors then
    let errs ← msgs.toList.filterMapM fun m => do
      if m.severity == .error then return some (← m.toString) else return none
    return .error s!"generated file does not elaborate:\n{String.intercalate "\n" (errs.take 5)}"
  let name := ns.toName ++ `prog
  match env.evalConst CC.Program {} name (checkMeta := false) with
  | .ok p => return .ok p
  | .error e => return .error s!"cannot evaluate {name}: {e}"

unsafe def main (args : List String) : IO UInt32 := do
  let mut file? : Option String := none
  let mut fuel := 0
  let mut stats := false
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--fuel" :: n :: r => fuel := n.toNat!; rest := r
    | "--stats" :: r => stats := true; rest := r
    | f :: r => file? := some f; rest := r
    | [] => rest := []
  let some file := file? | fail 125 "usage: clight_run FILE.lean [--fuel N] [--stats]"
  let sysroot ← findSysroot
  let extra := (← IO.getEnv "CLIGHT_LEAN_PATH").map (System.SearchPath.parse ·) |>.getD []
  initSearchPath sysroot extra
  enableInitializersExecution
  let t0 ← IO.monoMsNow
  let prog ← match ← loadProg file with
    | .ok p => pure p
    | .error e => return ← fail 125 e
  let t1 ← IO.monoMsNow
  let r := Run.runProgram prog fuel
  let stdout ← IO.getStdout
  stdout.write r.world.out
  stdout.flush
  (← IO.getStderr).write r.world.err
  let t2 ← IO.monoMsNow
  if stats then
    IO.eprintln s!"[clight_run] steps={r.steps} externals={r.externals} load_ms={t1 - t0} run_ms={t2 - t1}"
  match r.outcome with
  | .exit code => return (BitVec.ofInt 8 code).toNat.toUInt32
  | .stuck why => fail 126 s!"STUCK: {why}"
  | .unsupported why => fail 127 s!"UNSUPPORTED: {why}"
  | .fuel => fail 124 s!"FUEL exhausted after {r.steps} steps"
  | .noinit why => fail 125 s!"NOINIT: {why}"
