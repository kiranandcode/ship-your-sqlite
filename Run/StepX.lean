/-
  The semantics the refinement theorem is about (BRIEF.md D6/D8, TRUST.md):
  Clean's executable Clight step `CC.doStep`, which Clean proves sound against
  its `Step` relation (`doStep_sound`), extended by the three rules of
  TRUST.md: the external-call model, variadic calls, and the flat placement of
  blocks; and the non-volatile volatile accesses, which are Clight's own rule.

  The relation is defined from `doStep`, not from Clean's `Step`, because
  `Step` mentions the axiom `externalFunctionsSem` (it appears in the axioms of
  `doStep_sound`), and our theorems must not depend on axioms; `doStep`
  depends only on Lean's standard three. Every extension rule applies only
  where `doStep` is stuck, except `undefByte`, which replaces a step of
  `doStep` that stored `Vundef` from a byte load (TRUST.md, extension 3).

  `Run.runProgram` executes exactly this relation; proving that (a total,
  fuel-bounded runner with `run_sound : … → StarX …`) is Phase 3.1.
-/
import Run.Runner

namespace Run
open CC

/-- A state of the extended semantics: the outside world and the Clight state. -/
structure XState where
  world : World
  st : State

def extName : ExtFun → String
  | .EF_external n _ | .EF_builtin n _ | .EF_runtime n _ => n
  | _ => ""

/-- Record the variadic block of the activation entered by a variadic call. -/
def registerVa (w : World) (s' : State) (vb : Block) : World :=
  match s' with
  | .State _ _ _ e' _ _ =>
    match activationKey e' with
    | some key => { w with va := (key, vb) :: w.va }
    | none => w
  | _ => w

/-- A Clean step that stored `Vundef` from a byte load into a temporary (the
    runner's `undefByte` case). -/
def isUndefByteLoad : State → State → Prop
  | .State _ (.Sset id (.Ederef _ (.Tint .I8 _ _))) _ _ _ _, .State _ _ _ _ le' _ => le'.get id = some .Vundef
  | _, _ => False

inductive StepX (ge : CGenv) : XState → XState → Prop where
  /-- a step of Clean's Clight interpreter (`doStep_sound`: a Clight `Step`);
      a byte load that stores `Vundef` is `undefByte` instead -/
  | clight {w s t s'} :
      doStep ge s = some (t, s') →
      ¬ isUndefByteLoad s s' →
      StepX ge ⟨w, s⟩ ⟨w, s'⟩
  /-- extension 1: the external-call model -/
  | external {w ef targs tres cc vargs k m r} :
      doStep ge (.Callstate (.External ef targs tres cc) vargs k m) = none →
      vaBuiltin w (extName ef) vargs k m = none →
      (match ef with | .EF_external .. => true | _ => false) = true →
      callExternal w (extName ef) vargs m = some (.ok r) →
      r.world.exited = none →
      StepX ge ⟨w, .Callstate (.External ef targs tres cc) vargs k m⟩ ⟨r.world, .Returnstate r.ret k r.mem⟩
  /-- extension 2: va_start, va_arg, va_copy, va_end -/
  | vaStep {w ef targs tres cc vargs k m r} :
      doStep ge (.Callstate (.External ef targs tres cc) vargs k m) = none →
      vaBuiltin w (extName ef) vargs k m = some (.ok r) →
      StepX ge ⟨w, .Callstate (.External ef targs tres cc) vargs k m⟩ ⟨r.world, .Returnstate r.ret k r.mem⟩
  /-- extension 2: a call passing variadic arguments to an internal function -/
  | varCall {w f optid a al k e le m fd fixed extra vb m1 t s'} :
      doStep ge (.State f (.Scall optid a al) k e le m) = none →
      evalVarCall ge e le m a al = some (fd, fixed, extra) →
      (match fd with | .Internal _ => true | _ => false) = true →
      stashVarargs m extra = some (vb, m1) →
      doStep ge (.Callstate fd fixed (.Kcall optid f e le k) m1) = some (t, s') →
      StepX ge ⟨w, .State f (.Scall optid a al) k e le m⟩ ⟨registerVa w s' vb, s'⟩
  /-- extension 2: a call passing variadic arguments to an external function -/
  | varCallExt {w f optid a al k e le m name sg targs tres cc fixed extra r} :
      doStep ge (.State f (.Scall optid a al) k e le m) = none →
      evalVarCall ge e le m a al = some (.External (.EF_external name sg) targs tres cc, fixed, extra) →
      callExternal w name (fixed ++ extra) m = some (.ok r) →
      StepX ge ⟨w, .State f (.Scall optid a al) k e le m⟩ ⟨r.world, .State f .Sskip k e (setOpttemp optid r.ret le) r.mem⟩
  /-- Clight's `VolatileLoad.nonvol` (Clean's interpreter does not execute it) -/
  | vload {w f optid chunk tyargs al k e le m b ofs v} :
      doEvalExprlist ge e le m al tyargs = some [.Vptr b ofs] →
      Genv.blockIsVolatile ge.genv_genv b = false →
      Mem.load chunk m b (Integers.Ptrofs.unsigned ofs) = some v →
      StepX ge ⟨w, .State f (.Sbuiltin optid (.EF_vload chunk) tyargs al) k e le m⟩
        ⟨w, .State f .Sskip k e (setOpttemp optid v le) m⟩
  /-- Clight's `VolatileStore.nonvol` -/
  | vstore {w f optid chunk tyargs al k e le m b ofs v m'} :
      doEvalExprlist ge e le m al tyargs = some [.Vptr b ofs, v] →
      Genv.blockIsVolatile ge.genv_genv b = false →
      Mem.store chunk m b (Integers.Ptrofs.unsigned ofs) v = some m' →
      StepX ge ⟨w, .State f (.Sbuiltin optid (.EF_vstore chunk) tyargs al) k e le m⟩
        ⟨w, .State f .Sskip k e (setOpttemp optid .Vundef le) m'⟩
  /-- extension 3: the statement's expressions under the flat placement -/
  | flat {w f stmt k e le m stmt' t s'} :
      doStep ge (.State f stmt k e le m) = none →
      flatStmt ge e le m stmt = some stmt' →
      doStep ge (.State f stmt' k e le m) = some (t, s') →
      StepX ge ⟨w, .State f stmt k e le m⟩ ⟨w, s'⟩
  /-- extension 3: a byte load of a stored pointer or uninitialised byte -/
  | undefByte {w f id pe sg a k e le m stmt' t s'} :
      flatStmt ge e le m (.Sset id (.Ederef pe (.Tint .I8 sg a))) = some stmt' →
      doStep ge (.State f stmt' k e le m) = some (t, s') →
      StepX ge ⟨w, .State f (.Sset id (.Ederef pe (.Tint .I8 sg a))) k e le m⟩ ⟨w, s'⟩

/-- Reflexive-transitive closure. -/
inductive StarX (ge : CGenv) : XState → XState → Prop where
  | refl (x) : StarX ge x x
  | step {x y z} : StepX ge x y → StarX ge y z → StarX ge x z

/-- The arguments `runProgram` passes to `main`: none, or `argc = 0, argv = NULL`. -/
def mainArgs (f : FunDef) : Option (List Val) :=
  match typeOfFundef f with
  | .Tfunction [] _ _ => some []
  | .Tfunction [_, _] _ _ => some [Val.Vint 0, Val.Vlong 0]
  | _ => none

/-- The initial state of a program run on input `input` (fd 0), as `runProgram` builds it. -/
inductive InitialX (p : Program) (input : ByteArray) : XState → Prop where
  | mk {m0 b f vs} :
      p.initMem = some m0 →
      Genv.findSymbol p.globalenv.genv_genv p.prog_main = some b →
      Genv.findFunctPtr p.globalenv.genv_genv b = some f →
      mainArgs f = some vs →
      InitialX p input ⟨{ stdin := input }, .Callstate f vs .Kstop m0⟩

/-- A final state: `main` returned, or `exit` was called. -/
inductive FinalX : XState → Prop where
  | ret {w r m} : FinalX ⟨w, .Returnstate (.Vint r) .Kstop m⟩
  | exit {w ef targs tres cc vargs k m r} (ge : CGenv) :
      callExternal w (extName ef) vargs m = some (.ok r) → r.world.exited.isSome →
      FinalX ⟨w, .Callstate (.External ef targs tres cc) vargs k m⟩

/-- The program, run on `input`, terminates having written `out` to stdout. -/
def ClightRuns (p : Program) (input out : ByteArray) : Prop :=
  ∃ x0 x1, InitialX p input x0 ∧ StarX p.globalenv x0 x1 ∧ FinalX x1 ∧ x1.world.out = out

end Run
