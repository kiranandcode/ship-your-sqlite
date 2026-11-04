/-
  The simulation of the interpreter by the denotation (Phase 2.6g).

  `Sim m n`: the interpreter's computation `m : M α` is simulated by the
  meaning `n : D α`. From any interpreter state, the outcome of `m` (its result
  and the state reached, seen through `proj`) is one of the outcomes of `n`
  from the projected state, unless some fuel ran out. Two invariants make it
  compose: the choice oracle is never changed, and a run that has run out of
  fuel stays so.
-/
import Sql.Den.Exec

namespace Sql.Den

open Sql

/-- The interpreter's state as the denotation sees it: the database, the
    JSON parse cache and the clock (the oracle's, the same for every statement). -/
def proj (c : Ctx) : DCtx := { db := c.db, jsonCache := c.jsonCache, clockMs := c.choices.clockMs }

/-- The outcome of an interpreter computation from a state. -/
def runM {α : Type} (m : M α) (c : Ctx) : Except Err α × Ctx := (m.run).run c

/-- `m` is simulated by `n`, for runs with choice oracle `ch`. -/
structure Sim {α : Type} (ch : Choices) (m : M α) (n : D α) : Prop where
  /-- a run that ran out of fuel stays so -/
  exhausted_mono : ∀ c : Ctx, c.choices = ch → c.exhausted = true → (runM m c).2.exhausted = true
  /-- the choice oracle is not changed -/
  choices_eq : ∀ c : Ctx, c.choices = ch → (runM m c).2.choices = ch
  /-- the outcome is denoted, unless some fuel ran out -/
  sound : ∀ c : Ctx, c.choices = ch → (runM m c).2.exhausted = false →
    ((runM m c).1, proj (runM m c).2) ∈ n.outcomes (proj c)

namespace Sim

theorem mem_outcomes_pure {α : Type} {a : α} {d : DCtx} :
    (Except.ok a, d) ∈ (pure a : D α).outcomes d := by
  show (Except.ok a, d) ∈ (pure (Except.ok a, d) : Nd _)
  exact Nd.mem_pure.mpr rfl

theorem pure {α : Type} {ch : Choices} (a : α) : Sim ch (pure a : M α) (pure a : D α) where
  exhausted_mono := fun _ _ h => h
  choices_eq := fun _ h => h
  sound := fun c _ _ => mem_outcomes_pure

theorem throw {α : Type} {ch : Choices} (e : Err) : Sim ch (throw e : M α) (throw e : D α) where
  exhausted_mono := fun _ _ h => h
  choices_eq := fun _ h => h
  sound := fun c _ _ => by
    show (Except.error e, proj c) ∈ (Pure.pure (Except.error e, proj c) : Nd _)
    exact Nd.mem_pure.mpr rfl

/-- The outcomes of a bind in `D`: those of the first computation's errors,
    and those of the continuation from each of its results. -/
theorem mem_outcomes_bind {α β : Type} {n : D α} {g : α → D β} {d : DCtx} {o : Except Err β × DCtx} :
    o ∈ (n >>= g).outcomes d ↔
      ∃ o₁ ∈ n.outcomes d, match o₁ with
        | (.ok a, d₁) => o ∈ (g a).outcomes d₁
        | (.error e, d₁) => o = (.error e, d₁) := by
  simp only [D.outcomes, bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind, StateT.run,
    ExceptT.bindCont, Nd.mem_ofSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨⟨r, d₁⟩, h₁, h₂⟩
    refine ⟨(r, d₁), h₁, ?_⟩
    cases r with
    | ok a => exact h₂
    | error e => exact h₂
  · rintro ⟨⟨r, d₁⟩, h₁, h₂⟩
    refine ⟨(r, d₁), h₁, ?_⟩
    cases r with
    | ok a => exact h₂
    | error e => exact h₂

theorem runM_bind {α β : Type} (m : M α) (f : α → M β) (c : Ctx) :
    runM (m >>= f) c = match runM m c with
      | (.ok a, c₁) => runM (f a) c₁
      | (.error e, c₁) => (.error e, c₁) := by
  simp only [runM, bind, ExceptT.bind, ExceptT.mk, ExceptT.run, StateT.bind, StateT.run, ExceptT.bindCont]
  rcases h : (m c) with ⟨r, c₁⟩
  cases r <;> rfl

theorem bind {α β : Type} {ch : Choices} {m : M α} {n : D α} {f : α → M β} {g : α → D β}
    (hm : Sim ch m n) (hf : ∀ a, Sim ch (f a) (g a)) : Sim ch (m >>= f) (n >>= g) where
  exhausted_mono := by
    intro c hch hc
    rw [runM_bind]
    have h₁ := hm.exhausted_mono c hch hc
    have h₂ := hm.choices_eq c hch
    rcases h : runM m c with ⟨r, c₁⟩
    rw [h] at h₁ h₂
    cases r with
    | ok a => exact (hf a).exhausted_mono c₁ h₂ h₁
    | error e => exact h₁
  choices_eq := by
    intro c hch
    rw [runM_bind]
    have h₁ := hm.choices_eq c hch
    rcases h : runM m c with ⟨r, c₁⟩
    rw [h] at h₁
    cases r with
    | ok a => exact (hf a).choices_eq c₁ h₁
    | error e => exact h₁
  sound := by
    intro c hch hx
    rw [mem_outcomes_bind]
    have hm' := hm.sound c hch
    have h₂ := hm.choices_eq c hch
    rw [runM_bind] at hx ⊢
    rcases h : runM m c with ⟨r, c₁⟩
    rw [h] at hm' h₂
    cases r with
    | ok a =>
      simp only [h] at hx ⊢
      -- the first computation did not run out of fuel either
      have hx₁ : c₁.exhausted = false := by
        cases hc : c₁.exhausted
        · rfl
        · rw [(hf a).exhausted_mono c₁ h₂ hc] at hx; exact absurd hx (by decide)
      exact ⟨(.ok a, proj c₁), hm' hx₁, (hf a).sound c₁ h₂ hx⟩
    | error e =>
      simp only [h] at hx ⊢
      exact ⟨(.error e, proj c₁), hm' hx, rfl⟩

/-! ### State -/

theorem mem_outcomes_get {d : DCtx} {o : Except Err DCtx × DCtx} :
    o ∈ (get : D DCtx).outcomes d ↔ o = (.ok d, d) := by
  simp only [D.outcomes, get, getThe, MonadStateOf.get, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.mk, ExceptT.run, StateT.get, StateT.run, Functor.map, StateT.map]
  constructor
  · rintro ⟨a, ha, rfl⟩; cases ha; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

theorem mem_outcomes_modify {g : DCtx → DCtx} {d : DCtx} {o : Except Err Unit × DCtx} :
    o ∈ (modify g : D Unit).outcomes d ↔ o = (.ok (), g d) := by
  simp only [D.outcomes, modify, modifyGet, MonadStateOf.modifyGet, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.run, StateT.modifyGet, StateT.run,
    Functor.map, StateT.map]
  constructor
  · rintro ⟨a, ha, rfl⟩; cases ha; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

theorem mem_outcomes_set {d' d : DCtx} {o : Except Err PUnit × DCtx} :
    o ∈ (set d' : D PUnit).outcomes d ↔ o = (.ok ⟨⟩, d') := by
  simp only [D.outcomes, set, MonadStateOf.set, liftM, monadLift,
    MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.run, StateT.set, StateT.run,
    Functor.map, StateT.map]
  constructor
  · rintro ⟨a, ha, rfl⟩; cases ha; rfl
  · rintro rfl; exact ⟨_, rfl, rfl⟩

/-- Reading the state: the interpreter's continuation on `c` is simulated by
    the denotation's on `proj c`. -/
theorem get_bind {α : Type} {ch : Choices} {f : Ctx → M α} {g : DCtx → D α}
    (hf : ∀ c, c.choices = ch → Sim ch (f c) (g (proj c))) :
    Sim ch (get >>= f) (get >>= g) where
  exhausted_mono := fun c hch hc => (hf c hch).exhausted_mono c hch hc
  choices_eq := fun c hch => (hf c hch).choices_eq c hch
  sound := fun c hch hx => by
    rw [mem_outcomes_bind]
    exact ⟨(.ok (proj c), proj c), mem_outcomes_get.mpr rfl, (hf c hch).sound c hch hx⟩

/-- An update of the state that the projection commutes with, and that
    keeps the fuel flag and the oracle. -/
theorem modify {ch : Choices} (f : Ctx → Ctx) (g : DCtx → DCtx)
    (hcomm : ∀ c, proj (f c) = g (proj c)) (hex : ∀ c, (f c).exhausted = c.exhausted)
    (hch : ∀ c, (f c).choices = c.choices) :
    Sim ch (modify f : M Unit) (modify g : D Unit) where
  exhausted_mono := fun c _ h => by
    show (f c).exhausted = true; rw [hex]; exact h
  choices_eq := fun c h => by
    show (f c).choices = ch; rw [hch]; exact h
  sound := fun c _ _ => by
    show (Except.ok (), proj (f c)) ∈ _
    rw [hcomm]; exact mem_outcomes_modify.mpr rfl

/-- Back to a saved state (with the same oracle). -/
theorem restoreTo {ch : Choices} (saved : Ctx) (db : Db) (hs : saved.choices = ch) :
    Sim ch (Sql.restoreTo saved db) (Den.restoreTo (proj saved) db) where
  exhausted_mono := fun c _ h => h
  choices_eq := fun _ _ => hs
  sound := fun c _ _ => mem_outcomes_set.mpr rfl

theorem getDb {ch : Choices} : Sim ch Sql.getDb Den.getDb :=
  get_bind fun _ _ => pure _

end Sim

end Sql.Den
