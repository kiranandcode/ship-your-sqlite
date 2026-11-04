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
import Mathlib.Data.List.Perm.Basic

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

theorem err {α : Type} {ch : Choices} (m : String) (code : Nat) :
    Sim ch (Sql.err m code : M α) (Den.err m code : D α) := throw _

/-! ### Loops -/

theorem forIn_list {α β : Type} {ch : Choices} (xs : List α) (b : β)
    {f : α → β → M (ForInStep β)} {g : α → β → D (ForInStep β)}
    (h : ∀ a b, Sim ch (f a b) (g a b)) : Sim ch (forIn xs b f) (forIn xs b g) := by
  induction xs generalizing b with
  | nil => exact pure b
  | cons x xs ih =>
    simp only [List.forIn_cons]
    apply bind (h x b)
    intro r
    cases r with
    | done b => exact pure b
    | yield b => exact ih b

theorem forIn_range {β : Type} {ch : Choices} (r : Std.Legacy.Range) (b : β)
    {f : Nat → β → M (ForInStep β)} {g : Nat → β → D (ForInStep β)}
    (h : ∀ a b, Sim ch (f a b) (g a b)) : Sim ch (forIn r b f) (forIn r b g) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  exact forIn_list _ b h

theorem forIn'_list {α β : Type} {ch : Choices} (xs : List α) (b : β)
    {f : (a : α) → a ∈ xs → β → M (ForInStep β)} {g : (a : α) → a ∈ xs → β → D (ForInStep β)}
    (h : ∀ a ha b, Sim ch (f a ha b) (g a ha b)) : Sim ch (forIn' xs b f) (forIn' xs b g) := by
  induction xs generalizing b with
  | nil => exact pure b
  | cons x xs ih =>
    simp only [List.forIn'_cons]
    apply bind (h x _ b)
    intro r
    cases r with
    | done b => exact pure b
    | yield b => exact ih b (fun a ha b => h a _ b)

theorem forIn'_range {β : Type} {ch : Choices} (r : Std.Legacy.Range) (b : β)
    {f : (a : Nat) → a ∈ r → β → M (ForInStep β)} {g : (a : Nat) → a ∈ r → β → D (ForInStep β)}
    (h : ∀ a ha b, Sim ch (f a ha b) (g a ha b)) : Sim ch (forIn' r b f) (forIn' r b g) := by
  simp only [Std.Legacy.Range.forIn'_eq_forIn'_range']
  exact forIn'_list _ b (fun a ha b => h a _ b)

theorem forIn_array {α β : Type} {ch : Choices} (xs : Array α) (b : β)
    {f : α → β → M (ForInStep β)} {g : α → β → D (ForInStep β)}
    (h : ∀ a b, Sim ch (f a b) (g a b)) : Sim ch (forIn xs b f) (forIn xs b g) := by
  simp only [← Array.forIn_toList]
  exact forIn_list _ b h

theorem mapM_list {α β : Type} {ch : Choices} (xs : List α) {f : α → M β} {g : α → D β}
    (h : ∀ a, Sim ch (f a) (g a)) : Sim ch (xs.mapM f) (xs.mapM g) := by
  induction xs with
  | nil => exact pure []
  | cons x xs ih =>
    simp only [List.mapM_cons]
    exact bind (h x) fun a => bind ih fun as => pure (a :: as)

theorem mapM_array {α β : Type} {ch : Choices} (xs : Array α) {f : α → M β} {g : α → D β}
    (h : ∀ a, Sim ch (f a) (g a)) : Sim ch (xs.mapM f) (xs.mapM g) := by
  simp only [Array.mapM_eq_mapM_toList]
  exact bind (mapM_list _ h) fun as => pure as.toArray

theorem foldlM_list {α β : Type} {ch : Choices} (xs : List α) (b : β)
    {f : β → α → M β} {g : β → α → D β}
    (h : ∀ b a, Sim ch (f b a) (g b a)) : Sim ch (xs.foldlM f b) (xs.foldlM g b) := by
  induction xs generalizing b with
  | nil => exact pure b
  | cons x xs ih =>
    simp only [List.foldlM_cons]
    exact bind (h b x) fun b => ih b

/-! ### Errors -/

theorem runM_tryCatch {α : Type} (m : M α) (k : Err → M α) (c : Ctx) :
    runM (tryCatch m k) c = match runM m c with
      | (.ok a, c₁) => (.ok a, c₁)
      | (.error e, c₁) => runM (k e) c₁ := by
  show ((ExceptT.tryCatch m k).run).run c = _
  simp only [ExceptT.tryCatch, ExceptT.mk, ExceptT.run, runM]
  rw [StateT.run_bind]
  rcases h : StateT.run m c with ⟨r, c₁⟩
  cases r <;> rfl

theorem mem_outcomes_tryCatch {α : Type} {n : D α} {k : Err → D α} {d : DCtx} {o : Except Err α × DCtx} :
    o ∈ (tryCatch n k).outcomes d ↔
      ∃ o₁ ∈ n.outcomes d, match o₁ with
        | (.ok a, d₁) => o = (.ok a, d₁)
        | (.error e, d₁) => o ∈ (k e).outcomes d₁ := by
  show o ∈ ((ExceptT.tryCatch n k).run).run d ↔ _
  simp only [ExceptT.tryCatch, ExceptT.mk, ExceptT.run, bind, StateT.bind, StateT.run, D.outcomes,
    Nd.mem_ofSet, Set.mem_setOf_eq]
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

theorem tryCatch {α : Type} {ch : Choices} {m : M α} {n : D α} {k : Err → M α} {l : Err → D α}
    (hm : Sim ch m n) (hk : ∀ e, Sim ch (k e) (l e)) : Sim ch (tryCatch m k) (tryCatch n l) where
  exhausted_mono := by
    intro c hch hc
    rw [runM_tryCatch]
    have h₁ := hm.exhausted_mono c hch hc
    have h₂ := hm.choices_eq c hch
    rcases h : runM m c with ⟨r, c₁⟩
    rw [h] at h₁ h₂
    cases r with
    | ok a => exact h₁
    | error e => exact (hk e).exhausted_mono c₁ h₂ h₁
  choices_eq := by
    intro c hch
    rw [runM_tryCatch]
    have h₁ := hm.choices_eq c hch
    rcases h : runM m c with ⟨r, c₁⟩
    rw [h] at h₁
    cases r with
    | ok a => exact h₁
    | error e => exact (hk e).choices_eq c₁ h₁
  sound := by
    intro c hch hx
    rw [mem_outcomes_tryCatch]
    have hm' := hm.sound c hch
    have h₂ := hm.choices_eq c hch
    rw [runM_tryCatch] at hx ⊢
    rcases h : runM m c with ⟨r, c₁⟩
    rw [h] at hm' h₂
    cases r with
    | ok a =>
      simp only [h] at hx ⊢
      exact ⟨(.ok a, proj c₁), hm' hx, rfl⟩
    | error e =>
      simp only [h] at hx ⊢
      have hx₁ : c₁.exhausted = false := by
        cases hc : c₁.exhausted
        · rfl
        · rw [(hk e).exhausted_mono c₁ h₂ hc] at hx; exact absurd hx (by decide)
      exact ⟨(.error e, proj c₁), hm' hx₁, (hk e).sound c₁ h₂ hx⟩

/-! ### The oracle's choices are the denotation's -/

theorem permute_go_perm {α : Type} : ∀ (k c : Nat) (l : List α), (permute.go k c l).Perm l := by
  intro k
  induction k with
  | zero => intro c l; simp [permute.go]
  | succ k ih =>
    intro c l
    cases l with
    | nil => simp [permute.go]
    | cons y ys =>
      simp only [permute.go]
      split
      · rename_i x hx
        have hi : c % (y :: ys).length < (y :: ys).length := Nat.mod_lt _ (by simp)
        have hx' : (y :: ys)[c % (y :: ys).length] = x := by
          rw [List.getElem?_eq_getElem hi] at hx; exact Option.some.inj hx
        refine List.Perm.trans (List.Perm.cons x (ih _ _)) ?_
        rw [← hx']
        exact List.getElem_cons_eraseIdx_perm hi
      · exact List.Perm.refl _

/-- The oracle's orders are permutations. -/
theorem permute_perm {α : Type} (code : Nat) (xs : Array α) :
    (permute code xs).toList.Perm xs.toList := by
  unfold permute
  split
  · exact List.Perm.refl _
  · exact permute_go_perm _ _ _

theorem mem_outcomes_lift {α : Type} {s : Nd α} {d : DCtx} {o : Except Err α × DCtx} :
    o ∈ (liftM s : D α).outcomes d ↔ ∃ a, a ∈ s ∧ o = (.ok a, d) := by
  simp only [D.outcomes, liftM, monadLift, MonadLift.monadLift, ExceptT.lift, ExceptT.mk, ExceptT.run,
    StateT.run, StateT.map, StateT.lift, Functor.map, Nd.mem_bind, Nd.mem_pure]
  constructor
  · intro h
    obtain ⟨p, hp, ho⟩ := h
    obtain ⟨b, hb, hb'⟩ := hp
    subst hb'
    exact ⟨b, hb, ho⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(a, d), ⟨a, ha, rfl⟩, rfl⟩

/-- A permutation chosen by the oracle is one of the denotation's. -/
theorem chooseOrder {α : Type} {ch : Choices} (xs : Array α) : Sim ch (Sql.chooseOrder xs) (Den.permA xs) where
  exhausted_mono := fun c _ h => h
  choices_eq := fun _ h => h
  sound := fun c hch _ => by
    show (Except.ok (permute (c.choices.order c.orderPos) xs), proj { c with orderPos := c.orderPos + 1 }) ∈
      ((Den.perm xs.toList >>= fun l => Pure.pure l.toArray : D (Array α))).outcomes (proj c)
    rw [mem_outcomes_bind]
    refine ⟨(.ok (permute (c.choices.order c.orderPos) xs).toList, proj c), ?_, ?_⟩
    · exact mem_outcomes_lift.mpr ⟨_, permute_perm _ _, rfl⟩
    · simp only [Array.toArray_toList]
      exact mem_outcomes_pure

/-- A value the oracle draws is one of the denotation's. -/
theorem pure_any {α : Type} {ch : Choices} {P : α → Prop} (a : α) (h : P a) :
    Sim ch (Pure.pure a : M α) (anyOf P) where
  exhausted_mono := fun _ _ h => h
  choices_eq := fun _ h => h
  sound := fun c _ _ => mem_outcomes_lift.mpr ⟨a, h, rfl⟩

/-- Running out of fuel is simulated by anything (it ends the run's claim). -/
theorem outOfFuel {α : Type} {ch : Choices} (n : D α) : Sim ch (Sql.outOfFuel : M α) n where
  exhausted_mono := fun _ _ _ => rfl
  choices_eq := fun _ h => h
  sound := fun c _ hx => by
    have : (runM (Sql.outOfFuel : M α) c).2.exhausted = true := rfl
    rw [this] at hx; exact absurd hx (by decide)

end Sim

end Sql.Den
