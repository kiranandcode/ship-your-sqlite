/-
  The interpreter is sound for the denotation (Phase 2.6g): whenever a run of
  the interpreter, with any choices and fuel, does not run out of fuel, its
  output is an output of the script in the denotation.

  Proved: `sound` (the simulation of the interpreter by the denotation,
  Sql/Den/Sim*.lean).
-/
import Sql.Den.SimScript
import Sql.Derives

namespace Sql.Den

/-- The interpreter is sound for the denotation. -/
def sound_Statement : Prop :=
  ∀ (ch : Choices) (fuel : Nat) (src : ByteArray),
    (Sql.runScriptWith ch fuel src).exhausted = false →
      Den.Derives src (Sql.runScriptWith ch fuel src).out

/-- The interpreter is sound for the denotation: the simulation of the
    driver's loop (`loopI_sound`) from the initial state, whose clock the
    denotation chooses to be the oracle's. -/
theorem sound : sound_Statement := by
  intro ch fuel src hx
  have hrun : Sql.runScriptWith ch fuel src =
      let st := loopI fuel src (List.range (src.size + 1))
        { out := ByteArray.empty, ctx := { db := {}, choices := ch }, toks := tokenize src 0 }
      { out := st.out, exhausted := st.ctx.exhausted || !st.finished } := rfl
  rw [hrun] at hx ⊢
  simp only [Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false] at hx
  obtain ⟨hex, hfin⟩ := hx
  unfold Den.Derives Den.runScript
  rw [Nd.mem_bind]
  refine ⟨ch.clockMs, trivial, ?_⟩
  rw [Nd.mem_bind]
  refine ⟨_, loopI_sound fuel src _ _ rfl hex, ?_⟩
  simp only [projD, hfin]
  exact Nd.mem_pure.mpr rfl

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

/-- The interpreter's relation (`Sql.Derives`: some choices and fuel) is
    contained in the denotation. -/
theorem derives (src out : ByteArray) (h : Sql.Derives src out) : Den.Derives src out :=
  derives_of_sound sound h

/-- The executable's output (`sql_run`) is denoted when its fuel does not run out. -/
theorem runScript_denoted (src : ByteArray) (hx : (Sql.runScriptWith {} evalFuel src).exhausted = false) :
    Den.Derives src (Sql.runScript src) :=
  runScript_den sound src hx

end Sql.Den
