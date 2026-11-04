/-
  The interpreter is sound for the denotation (Phase 2.6g): whenever a run of
  the interpreter, with any choices and fuel, does not run out of fuel, its
  output is an output of the script in the denotation.

  Not proved yet: `sound_Statement` is a `Prop` (CLAUDE.md law 2), listed
  under Obligations in PHASES.md.
-/
import Sql.Den.Exec
import Sql.Derives

namespace Sql.Den

/-- The interpreter is sound for the denotation. -/
def sound_Statement : Prop :=
  ∀ (ch : Choices) (fuel : Nat) (src : ByteArray),
    (Sql.runScriptWith ch fuel src).exhausted = false →
      Den.Derives src (Sql.runScriptWith ch fuel src).out

/-- With soundness, the interpreter's relation (`Sql.Derives`: some choices
    and fuel) is contained in the denotation. -/
theorem derives_of_sound (h : sound_Statement) {src out : ByteArray} :
    Sql.Derives src out → Den.Derives src out := by
  intro hd
  cases hd with
  | intro ch fuel complete output =>
    rw [← output]
    exact h ch fuel src complete

/-- With soundness, the executable's output (`sql_run`) is denoted when its
    fuel does not run out. -/
theorem runScript_den (h : sound_Statement) (src : ByteArray)
    (hx : (Sql.runScriptWith {} evalFuel src).exhausted = false) :
    Den.Derives src (Sql.runScript src) :=
  h {} evalFuel src hx

end Sql.Den
