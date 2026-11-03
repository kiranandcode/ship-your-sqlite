/-
  Whole-program runner: Clean's `CC.doStep` (proved sound, `doStep_sound`)
  plus the external-call model of `Run.Ext` at the states where `doStep` stops
  on an `EF_external` call.

  Adapted from ship-your-tcc's `lean/ClightRun/ClightRun/Run.lean`
  (ATTRIBUTION.md): the pure tail-recursive loop and the stuck-state
  diagnosis are theirs; the external model and the `World` threading are ours.
-/
import CCLib
import Run.Ext

namespace Run
open CC

/-- Why the pure loop stopped. -/
inductive Stop where
  | done (r : Integers.Int)
  | stuck (s : State)
  | fuel (s : State)

instance : Inhabited Stop := ⟨.done 0⟩

/-- Run `doStep` until a final state, a stuck state, or `limit` steps
    (`limit = 0`: unbounded). Tail-recursive, so it compiles to a loop. -/
partial def runPure (ge : CGenv) (s : State) (n limit : Nat) : Stop × Nat :=
  match s with
  | .Returnstate (.Vint r) .Kstop _ => (.done r, n)
  | _ =>
    if limit != 0 && n ≥ limit then (.fuel s, n) else
    match doStep ge s with
    | some (_, s') => runPure ge s' (n + 1) limit
    | none => (.stuck s, n)

/-- How a run ended. -/
inductive Outcome where
  | exit (code : Int)
  | stuck (why : String)
  | unsupported (why : String)
  | fuel
  | noinit (why : String)

structure Result where
  outcome : Outcome
  world : World
  steps : Nat
  externals : Nat

def describeStmt : Stmt → String
  | .Sskip => "Sskip" | .Sassign .. => "Sassign" | .Sset .. => "Sset"
  | .Scall .. => "Scall" | .Sbuiltin _ ef .. =>
      (match ef with
       | .EF_builtin n _ => s!"Sbuiltin {n}" | .EF_external n _ => s!"Sbuiltin(external) {n}"
       | .EF_runtime n _ => s!"Sbuiltin(runtime) {n}"
       | .EF_vload _ => "volatile load" | .EF_vstore _ => "volatile store"
       | .EF_inline_asm .. => "inline asm" | _ => "Sbuiltin")
  | .Ssequence .. => "Ssequence" | .Sifthenelse .. => "Sifthenelse"
  | .Sloop .. => "Sloop" | .Sbreak => "Sbreak" | .Scontinue => "Scontinue"
  | .Sreturn .. => "Sreturn" | .Sswitch .. => "Sswitch" | .Slabel .. => "Slabel"
  | .Sgoto .. => "Sgoto"

def describeStuck (names : Ident → String) : State → String
  | .State f s _ _ _ _ =>
    let fn := (names <$> f.fn_params.head?.map (·.1)).getD "?"
    s!"stuck at statement {describeStmt s} (function with first parameter {fn})"
  | .Callstate (.External ef _ _ _) _ _ _ =>
    match ef with
    | .EF_external n _ => s!"call to unsupported external function {n}"
    | .EF_builtin n _ => s!"call to unsupported builtin {n}"
    | .EF_runtime n _ => s!"call to runtime helper {n}"
    | .EF_malloc => "malloc failed" | .EF_free => "invalid free"
    | _ => "stuck at external call"
  | .Callstate (.Internal _) _ _ _ => "stuck at function entry"
  | .Returnstate v .Kstop _ => s!"main returned a non-int value {repr v}"
  | .Returnstate .. => "stuck at return"

/-- Run program `p` from `main` with the external model. `args` are main's arguments. -/
def runProgram (p : Program) (limit : Nat) (w0 : World := {}) : Result := Id.run do
  let ge := p.globalenv
  let fail (o : Outcome) (w : World) (n e : Nat) : Result := ⟨o, w, n, e⟩
  let some m0 := p.initMem | return fail (.noinit "global initialisation failed") w0 0 0
  let some b := Genv.findSymbol ge.genv_genv p.prog_main | return fail (.noinit "no main") w0 0 0
  let some f := Genv.findFunctPtr ge.genv_genv b | return fail (.noinit "main is not a function") w0 0 0
  let args : List Val ← match typeOfFundef f with
    | .Tfunction [] _ _ => pure []
    | .Tfunction [_, _] _ _ => pure [.Vint 0, .Vlong 0]
    | _ => return fail (.noinit "unsupported type for main") w0 0 0
  let mut s : State := .Callstate f args .Kstop m0
  let mut w := w0
  let mut total := 0
  let mut ext := 0
  let names : Ident → String := fun i => toString (repr i)
  repeat
    let (stop, n) := runPure ge s 0 (if limit == 0 then 0 else limit - total)
    total := total + n
    match stop with
    | .done r => return ⟨.exit (Integers.Int.signed r), w, total, ext⟩
    | .fuel _ => return ⟨.fuel, w, total, ext⟩
    | .stuck st =>
      match st with
      | .Callstate (.External (.EF_external name _) _ _ _) vargs k m =>
        match callExternal w name vargs m with
        | none => return ⟨.stuck (describeStuck names st), w, total, ext⟩
        | some (.error (.ub msg)) => return ⟨.stuck s!"{name}: {msg}", w, total, ext⟩
        | some (.error (.unsupported msg)) => return ⟨.unsupported s!"{name}: {msg}", w, total, ext⟩
        | some (.ok r) =>
          w := r.world
          total := total + 1
          ext := ext + 1
          if let some c := w.exited then return ⟨.exit c, w, total, ext⟩
          s := .Returnstate r.ret k r.mem
      | _ => return ⟨.stuck (describeStuck names st), w, total, ext⟩
  return ⟨.fuel, w, total, ext⟩

end Run
