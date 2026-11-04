/-
  The simulation of the interpreter's join by the denotation (Phase 2.6g):
  the loops (`joinLoopsM` by `joinLoops`, the automatic index's skipped rows
  being rows the denotation rejects), the plan (`joinPrepareM` by
  `joinPrepare`, the executable's nesting order being one of the
  denotation's), and `evalFromWhereS` by `joinRun`.
-/
import Sql.Den.SimSelectBase

namespace Sql.Den

open Sql

namespace Sim

theorem attemptM {α : Type} {ch : Choices} {m : M α} {n : D α} (h : Sim ch m n) :
    Sim ch (Sql.attemptM m) (Den.attempt n) := by
  unfold Sql.attemptM Den.attempt
  sim

theorem mem_attempt_ok {α : Type} {n : D α} {a : α} {s s' : DCtx} (h : (Except.ok a, s') ∈ n.outcomes s) :
    (Except.ok (Except.ok a), s') ∈ (Den.attempt n).outcomes s := by
  unfold Den.attempt
  rw [mem_outcomes_tryCatch]
  refine ⟨(.ok (.ok a), s'), ?_, rfl⟩
  rw [mem_outcomes_bind]
  exact ⟨(.ok a, s'), h, mem_outcomes_pure⟩

/-- A row the interpreter skips: the denotation's check rejects it, with no
    effect, and goes on as the interpreter does. -/
theorem skipped {β : Type} {ch : Choices} {n : D Bool} {k : Except Err Bool → D β} {a : β}
    (hn : ∀ s, (Except.ok false, s) ∈ n.outcomes s) (hk : k (.ok false) = Pure.pure a) :
    Sim ch (Pure.pure a : M β) (Den.attempt n >>= k) :=
  of_mem fun s => by
    rw [mem_outcomes_bind]
    exact ⟨(.ok (.ok false), s), mem_attempt_ok (hn s), by show _ ∈ (k (.ok false)).outcomes s; rw [hk]; exact mem_outcomes_pure⟩

/-- The interpreter's loops are simulated by the denotation's: the same
    loops, but for the rows the automatic index skips, which the denotation's
    conjuncts reject (`h_skip`). -/
theorem joinLoopsM {σ : Type} {ch : Choices} (nL : Nat) (nest : Array Nat)
    (rowsAt : Nat → Array Cur → M (Array (Array Cur))) (rowsAt' : Nat → Array Cur → D (Array (Array Cur)))
    (place : Array Cur → Nat → Array Cur → Array Cur) (skip : Nat → Array Cur → Bool)
    (check : Array Cur → Nat → M Bool) (check' : Array Cur → Nat → D Bool)
    (step : σ → Array Cur → M (σ × Bool)) (step' : σ → Array Cur → D (σ × Bool))
    (h_rowsAt : ∀ k pre, Sim ch (rowsAt k pre) (rowsAt' k pre))
    (h_check : ∀ cur d, Sim ch (check cur d) (check' cur d))
    (h_skip : ∀ d cur, skip d cur = true → ∀ s, (Except.ok false, s) ∈ (check' cur d).outcomes s)
    (h_step : ∀ acc cur, Sim ch (step acc cur) (step' acc cur)) :
    ∀ d pre acc, Sim ch (Sql.joinLoopsM nL nest rowsAt place skip check step d pre acc)
      (Den.joinLoops nL nest rowsAt' place check' step' d pre acc) := by
  intro d
  induction h : nL - d using Nat.strong_induction_on generalizing d with
  | _ n ih =>
    intro pre acc
    rw [Sql.joinLoopsM.eq_1, Den.joinLoops.eq_1]
    by_cases hd : d < nL
    · simp only [hd, if_true]
      have h_joinLoopsM : ∀ pre acc, Sim ch (Sql.joinLoopsM nL nest rowsAt place skip check step (d + 1) pre acc)
          (Den.joinLoops nL nest rowsAt' place check' step' (d + 1) pre acc) :=
        fun pre acc => ih (nL - (d + 1)) (by omega) (d + 1) rfl pre acc
      sim
      -- the rows the index skips
      all_goals exact Sim.skipped (h_skip _ _ (by assumption)) rfl
    · simp only [hd, if_false]
      exact Sim.pure _

/-- A sandboxed computation leaves the state as it was, but for the
    oracle's counters and (only setting it) the fuel flag. -/
theorem runM_sandbox {α : Type} (m : M α) (dflt : α) (c : Ctx) :
    ∃ (r : α) (c₂ : Ctx), runM (Sql.sandbox m dflt) c =
      (.ok r, { c with orderPos := c₂.orderPos, prng := c₂.prng, exhausted := c.exhausted || c₂.exhausted }) := by
  unfold Sql.sandbox
  simp only [runM_bind]
  have hg : runM (get : M Ctx) c = (.ok c, c) := rfl
  rw [hg]
  simp only []
  rw [runM_tryCatch]
  rcases h : runM m c with ⟨r, c₁⟩
  cases r with
  | ok a => exact ⟨a, c₁, rfl⟩
  | error e => exact ⟨dflt, c₁, rfl⟩

/-- A sandboxed computation (the executable's sizing of a join) has no
    effect the denotation sees. -/
theorem sandbox_bind {α β : Type} {ch : Choices} {m : M α} {dflt : α} {k : α → M β} {n : D β}
    (hk : ∀ a, Sim ch (k a) n) : Sim ch (Sql.sandbox m dflt >>= k) n where
  exhausted_mono := fun c hch hc => by
    obtain ⟨r, c₂, h⟩ := runM_sandbox m dflt c
    rw [runM_bind, h]
    exact (hk r).exhausted_mono _ hch (by simp [hc])
  choices_eq := fun c hch => by
    obtain ⟨r, c₂, h⟩ := runM_sandbox m dflt c
    rw [runM_bind, h]
    exact (hk r).choices_eq _ hch
  sound := fun c hch hx => by
    obtain ⟨r, c₂, h⟩ := runM_sandbox m dflt c
    rw [runM_bind, h] at hx ⊢
    exact (hk r).sound { c with orderPos := c₂.orderPos, prng := c₂.prng, exhausted := c.exhausted || c₂.exhausted } hch hx

/-- The executable's nesting order is one of the denotation's. -/
theorem chooseNest {ch : Choices} (condC : QEnv → Expr → M Bool) (q : QEnv) (leaves : Array FromItem)
    (leafSrcs : Array (Array Src)) (leafRows : Array (Option (Array (Array Cur))))
    (conds : List Expr) (aliases : List (Name × Expr)) :
    Sim ch (Sql.chooseNest condC q leaves leafSrcs leafRows conds aliases) (Den.permA (Array.range leaves.size)) := by
  unfold Sql.chooseNest
  apply sandbox_bind
  intro n0
  apply chooseOrder_perm
  unfold nestGuard
  split
  · rename_i h
    rw [Array.toList_range]
    exact List.isPerm_iff.mp h
  · exact List.Perm.refl _

end Sim

/-- The interpreter's plan of a join is one of the denotation's. -/
theorem sim_joinPrepareM {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (q : QEnv) (f : FromItem)
    (where_ : Option Expr) (aliases : List (Name × Expr)) :
    Sim ch (Sql.joinPrepareM (Sql.evalFrom fuel q) (Sql.tableFnSrc fuel) (Sql.condHolds fuel) q f where_ aliases)
      (Den.joinPrepare q f where_ aliases) := by
  select_ih ih
  unfold Sql.joinPrepareM Den.joinPrepare
  sim

end Sql.Den
