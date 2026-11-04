/-
  The interpreter's statements and scripts are simulated by the denotation
  (Phase 2.6g): `runStmt` (the denotation picks the clock per statement; the
  interpreter's, the oracle's, is one choice), the driver's rounds, and the
  script.
-/
import Sql.Den.SimExecAll

namespace Sql.Den

open Sql

namespace Sim

/-- A value the denotation chooses: the one that simulates. -/
theorem anyOf_bind {α β : Type} {ch : Choices} {P : α → Prop} {m : M β} {n : α → D β} (a : α) (ha : P a)
    (h : Sim ch m (n a)) : Sim ch m (anyOf P >>= n) where
  exhausted_mono := h.exhausted_mono
  choices_eq := h.choices_eq
  sound := fun c hch hx => by
    rw [mem_outcomes_bind]
    exact ⟨(.ok a, proj c), mem_outcomes_lift.mpr ⟨a, ha, rfl⟩, h.sound c hch hx⟩

/-- An update of the state that the projection commutes with for the runs
    with oracle `ch`. -/
theorem modify_ch {ch : Choices} (f : Ctx → Ctx) (g : DCtx → DCtx)
    (hcomm : ∀ c, c.choices = ch → proj (f c) = g (proj c)) (hex : ∀ c, (f c).exhausted = c.exhausted)
    (hch : ∀ c, (f c).choices = c.choices) :
    Sim ch (_root_.modify f : M Unit) (_root_.modify g : D Unit) where
  exhausted_mono := fun c _ h => by
    show (f c).exhausted = true; rw [hex]; exact h
  choices_eq := fun c h => by
    show (f c).choices = ch; rw [hch]; exact h
  sound := fun c h _ => by
    show (Except.ok (), proj (f c)) ∈ _
    rw [hcomm c h]; exact mem_outcomes_modify.mpr rfl

end Sim

/-- A statement: the denotation's clock for it is the oracle's. -/
theorem sim_runStmt {ch : Choices} (fuel : Nat) (s : Stmt) : Sim ch (Sql.runStmt fuel s) (Den.runStmt s) := by
  unfold Sql.runStmt Den.runStmt
  refine Sim.anyOf_bind ch.clockMs trivial ?_
  refine Sim.bind (Sim.modify_ch _ _ (fun c hc => by simp [proj, hc]) (fun _ => rfl) (fun _ => rfl)) fun _ => ?_
  sim

/-! ## The driver -/

/-- The driver's state seen through the projection. -/
def projD (st : DriverState Ctx) : DriverState DCtx := { st with ctx := proj st.ctx }

def projStep : ForInStep (DriverState Ctx) → ForInStep (DriverState DCtx)
  | .done b => .done (projD b)
  | .yield b => .yield (projD b)

/-- The interpreter's statements, as the driver runs them. -/
abbrev runI (fuel : Nat) (stmt : Stmt) (ctx : Ctx) : Id (Except Err (Except Err (Array (Array Value))) × Ctx) :=
  (Sql.runStmt fuel stmt).run.run ctx

/-- The denotation's statements, as the driver runs them. -/
abbrev runD (stmt : Stmt) (ctx : DCtx) : Nd (Except Err (Except Err (Array (Array Value))) × DCtx) :=
  (Den.runStmt stmt).run.run ctx

/-- The interpreter's round of the driver. -/
abbrev stepI (fuel : Nat) (src : ByteArray) (st : DriverState Ctx) : ForInStep (DriverState Ctx) :=
  Id.run (driverStep src (runI fuel) st)

theorem stepI_sound {ch : Choices} (fuel : Nat) (src : ByteArray) (st : DriverState Ctx) (hch : st.ctx.choices = ch)
    (hx : (stepI fuel src st).value.ctx.exhausted = false) :
    projStep (stepI fuel src st) ∈ driverStep src runD (projD st) := by
  unfold stepI driverStep projD at *
  rcases hs : seekTok src st.toks st.ti st.pos with ⟨toks, ti⟩
  simp only [hs] at hx ⊢
  rcases hp : parseNextTok src toks ti with _ | ⟨stmt, tail⟩ | ⟨msg, tail⟩
  all_goals simp only [hp] at hx ⊢
  · exact Nd.mem_pure.mpr rfl
  · have hsound := (sim_runStmt (ch := ch) fuel stmt).sound st.ctx hch hx
    rw [Nd.mem_bind]
    exact ⟨_, hsound, Nd.mem_pure.mpr rfl⟩
  · exact Nd.mem_pure.mpr rfl

theorem stepI_choices {ch : Choices} (fuel : Nat) (src : ByteArray) (st : DriverState Ctx) (hch : st.ctx.choices = ch) :
    (stepI fuel src st).value.ctx.choices = ch := by
  unfold stepI driverStep
  rcases hs : seekTok src st.toks st.ti st.pos with ⟨toks, ti⟩
  rcases hp : parseNextTok src toks ti with _ | ⟨stmt, tail⟩ | ⟨msg, tail⟩
  all_goals simp only [hp]
  · exact hch
  · exact (sim_runStmt (ch := ch) fuel stmt).choices_eq st.ctx hch
  · exact hch

theorem stepI_mono {ch : Choices} (fuel : Nat) (src : ByteArray) (st : DriverState Ctx) (hch : st.ctx.choices = ch)
    (hx : st.ctx.exhausted = true) : (stepI fuel src st).value.ctx.exhausted = true := by
  unfold stepI driverStep
  rcases hs : seekTok src st.toks st.ti st.pos with ⟨toks, ti⟩
  rcases hp : parseNextTok src toks ti with _ | ⟨stmt, tail⟩ | ⟨msg, tail⟩
  all_goals simp only [hp]
  · exact hx
  · exact (sim_runStmt (ch := ch) fuel stmt).exhausted_mono st.ctx hch hx
  · exact hx

/-- The interpreter's driver loop. -/
abbrev loopI (fuel : Nat) (src : ByteArray) (xs : List Nat) (st : DriverState Ctx) : DriverState Ctx :=
  Id.run (forIn xs st fun _ st => driverStep src (runI fuel) st)

theorem loopI_cons (fuel : Nat) (src : ByteArray) (x : Nat) (xs : List Nat) (st : DriverState Ctx) :
    loopI fuel src (x :: xs) st =
      (match stepI fuel src st with | .done b => b | .yield b => loopI fuel src xs b) := by
  simp only [loopI, stepI, List.forIn_cons]
  cases driverStep src (runI fuel) st <;> rfl

theorem loopI_inv {ch : Choices} (fuel : Nat) (src : ByteArray) :
    ∀ (xs : List Nat) (st : DriverState Ctx), st.ctx.choices = ch →
      (loopI fuel src xs st).ctx.choices = ch ∧
        (st.ctx.exhausted = true → (loopI fuel src xs st).ctx.exhausted = true) := by
  intro xs
  induction xs with
  | nil => intro st hch; exact ⟨hch, id⟩
  | cons x xs ih =>
    intro st hch
    have hc := stepI_choices fuel src st hch
    have hm := stepI_mono fuel src st hch
    rw [loopI_cons]
    rcases h : stepI fuel src st with b | b
    all_goals rw [h] at hc hm
    · exact ⟨hc, hm⟩
    · obtain ⟨h1, h2⟩ := ih b hc
      exact ⟨h1, fun he => h2 (hm he)⟩

theorem loopI_sound {ch : Choices} (fuel : Nat) (src : ByteArray) :
    ∀ (xs : List Nat) (st : DriverState Ctx), st.ctx.choices = ch →
      (loopI fuel src xs st).ctx.exhausted = false →
      projD (loopI fuel src xs st) ∈ forIn xs (projD st) (fun _ st => driverStep src runD st) := by
  intro xs
  induction xs with
  | nil => intro st _ _; exact Nd.mem_pure.mpr rfl
  | cons x xs ih =>
    intro st hch hx
    have hsound := stepI_sound fuel src st hch
    have hc := stepI_choices fuel src st hch
    rw [loopI_cons] at hx ⊢
    simp only [List.forIn_cons]
    rw [Nd.mem_bind]
    rcases h : stepI fuel src st with b | b
    all_goals rw [h] at hsound hc hx
    all_goals simp only [] at hx ⊢
    · exact ⟨projStep (.done b), hsound hx, Nd.mem_pure.mpr rfl⟩
    · have hb : b.ctx.exhausted = false := by
        cases hb : b.ctx.exhausted
        · rfl
        · rw [(loopI_inv fuel src xs b hc).2 hb] at hx; exact absurd hx (by decide)
      exact ⟨projStep (.yield b), hsound hb, ih b hc hx⟩

end Sql.Den
