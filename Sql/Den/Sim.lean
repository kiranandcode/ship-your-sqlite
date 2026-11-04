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

/-- `pure` of values equal up to unfolding (the two sides' matchers). -/
theorem pure_eq {α : Type} {ch : Choices} {a b : α} (h : a = b) : Sim ch (Pure.pure a : M α) (Pure.pure b : D α) :=
  h ▸ pure a

theorem map {α β : Type} {ch : Choices} (f : α → β) {m : M α} {n : D α} (h : Sim ch m n) :
    Sim ch (f <$> m) (f <$> n) := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  exact bind h fun a => pure (f a)

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

theorem forM_list {α : Type} {ch : Choices} (xs : List α) {f : α → M PUnit} {g : α → D PUnit}
    (h : ∀ a, Sim ch (f a) (g a)) : Sim ch (xs.forM f) (xs.forM g) := by
  induction xs with
  | nil => exact pure _
  | cons x xs ih => exact bind (h x) fun _ => ih

theorem forM_list_eq {α : Type} {ch : Choices} {xs ys : List α} {f : α → M PUnit} {g : α → D PUnit}
    (hxs : xs = ys) (h : ∀ a, Sim ch (f a) (g a)) : Sim ch (xs.forM f) (ys.forM g) :=
  hxs ▸ forM_list xs h

theorem forM_option {α : Type} {ch : Choices} (o : Option α) {f : α → M PUnit} {g : α → D PUnit}
    (h : ∀ a, Sim ch (f a) (g a)) : Sim ch (o.forM f) (o.forM g) := by
  cases o with
  | none => exact pure _
  | some a => exact h a

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

theorem filterMapM_array {α β : Type} {ch : Choices} (xs : Array α) {f : α → M (Option β)} {g : α → D (Option β)}
    (h : ∀ a, Sim ch (f a) (g a)) : Sim ch (xs.filterMapM f) (xs.filterMapM g) := by
  unfold Array.filterMapM
  rw [← Array.foldlM_toList, ← Array.foldlM_toList]
  exact foldlM_list _ _ fun b a => bind (h a) fun o => by cases o <;> exact pure _

/-- An early `return` tunnelled through `try` (the `do` elaborator's
    `EarlyReturn.runK`). -/
theorem earlyReturn_runK {ρ α β : Type} {ch : Choices} (x : Except ρ α) {r : ρ → M β} {r' : ρ → D β}
    {p : α → M β} {p' : α → D β} (hr : ∀ a, Sim ch (r a) (r' a)) (hp : ∀ a, Sim ch (p a) (p' a)) :
    Sim ch (EarlyReturn.runK x r p) (EarlyReturn.runK x r' p') := by
  cases x
  · exact hr _
  · exact hp _

/-- The early `return` itself. -/
theorem earlyReturn_return {ρ α : Type} {ch : Choices} (r : ρ) :
    Sim ch (EarlyReturnT.return r : EarlyReturnT ρ M α) (EarlyReturnT.return r : EarlyReturnT ρ D α) :=
  Sim.pure (Except.error r)

/-! ### Loops over collections equal up to unfolding

The interpreter's and the denotation's loops run over the same collection,
written with distinct auxiliary matchers; `sim` proves the equality by `rfl`. -/

theorem forIn_list_eq {α β : Type} {ch : Choices} {xs ys : List α} {b b' : β}
    {f : α → β → M (ForInStep β)} {g : α → β → D (ForInStep β)}
    (hx : xs = ys) (hb : b = b') (h : ∀ a b, Sim ch (f a b) (g a b)) :
    Sim ch (forIn xs b f) (forIn ys b' g) := hx ▸ hb ▸ forIn_list xs b h

theorem forIn_array_eq {α β : Type} {ch : Choices} {xs ys : Array α} {b b' : β}
    {f : α → β → M (ForInStep β)} {g : α → β → D (ForInStep β)}
    (hx : xs = ys) (hb : b = b') (h : ∀ a b, Sim ch (f a b) (g a b)) :
    Sim ch (forIn xs b f) (forIn ys b' g) := hx ▸ hb ▸ forIn_array xs b h

theorem forIn_range_eq {β : Type} {ch : Choices} {r r' : Std.Legacy.Range} {b b' : β}
    {f : Nat → β → M (ForInStep β)} {g : Nat → β → D (ForInStep β)}
    (hx : r = r') (hb : b = b') (h : ∀ a b, Sim ch (f a b) (g a b)) :
    Sim ch (forIn r b f) (forIn r' b' g) := hx ▸ hb ▸ forIn_range r b h

theorem mapM_list_eq {α β : Type} {ch : Choices} {xs ys : List α} {f : α → M β} {g : α → D β}
    (hx : xs = ys) (h : ∀ a, Sim ch (f a) (g a)) : Sim ch (xs.mapM f) (ys.mapM g) :=
  hx ▸ mapM_list xs h

theorem mapM_array_eq {α β : Type} {ch : Choices} {xs ys : Array α} {f : α → M β} {g : α → D β}
    (hx : xs = ys) (h : ∀ a, Sim ch (f a) (g a)) : Sim ch (xs.mapM f) (ys.mapM g) :=
  hx ▸ mapM_array xs h

theorem foldlM_list_eq {α β : Type} {ch : Choices} {xs ys : List α} {b b' : β}
    {f : β → α → M β} {g : β → α → D β}
    (hx : xs = ys) (hb : b = b') (h : ∀ b a, Sim ch (f b a) (g b a)) :
    Sim ch (xs.foldlM f b) (ys.foldlM g b') := hx ▸ hb ▸ foldlM_list xs b h

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

/-- A draw of the oracle's PRNG is one of the denotation's values. -/
theorem draw {α : Type} {ch : Choices} {P : α → Prop} (f : Choices → Nat → α) (hP : ∀ s, P (f ch s)) :
    Sim ch (Sql.draw f) (anyOf P) where
  exhausted_mono := fun _ _ h => h
  choices_eq := fun _ h => h
  sound := fun c hch _ => by
    show (Except.ok (f c.choices c.prng), proj { c with prng := c.prng + 1 }) ∈ _
    exact mem_outcomes_lift.mpr ⟨_, hch ▸ hP c.prng, rfl⟩

/-- An interpreter result that is an outcome of the denotation from every
    state, without changing it. -/
theorem of_mem {α : Type} {ch : Choices} {a : α} {n : D α} (h : ∀ d, (Except.ok a, d) ∈ n.outcomes d) :
    Sim ch (Pure.pure a : M α) n where
  exhausted_mono := fun _ _ h => h
  choices_eq := fun _ h => h
  sound := fun c _ _ => h (proj c)

/-- The interpreter's order is one of the denotation's: the identity. -/
theorem perm_self {α β : Type} {ch : Choices} {m : M β} {xs : List α} {g : List α → D β}
    (h : Sim ch m (g xs)) : Sim ch m (Den.perm xs >>= g) where
  exhausted_mono := h.exhausted_mono
  choices_eq := h.choices_eq
  sound := fun c hch hx => by
    rw [mem_outcomes_bind]
    exact ⟨(.ok xs, proj c), mem_outcomes_lift.mpr ⟨xs, List.Perm.refl _, rfl⟩, h.sound c hch hx⟩

/-- A permutation of a permutation of `ys`. -/
theorem chooseOrder_perm {α : Type} {ch : Choices} {xs ys : Array α} (hp : xs.toList.Perm ys.toList) :
    Sim ch (Sql.chooseOrder xs) (Den.permA ys) where
  exhausted_mono := fun c _ h => h
  choices_eq := fun _ h => h
  sound := fun c hch _ => by
    show (Except.ok (permute (c.choices.order c.orderPos) xs), proj { c with orderPos := c.orderPos + 1 }) ∈
      ((Den.perm ys.toList >>= fun l => Pure.pure l.toArray : D (Array α))).outcomes (proj c)
    rw [mem_outcomes_bind]
    refine ⟨(.ok (permute (c.choices.order c.orderPos) xs).toList, proj c), ?_, ?_⟩
    · exact mem_outcomes_lift.mpr ⟨_, (permute_perm _ _).trans hp, rfl⟩
    · simp only [Array.toArray_toList]
      exact mem_outcomes_pure

/-- Running out of fuel is simulated by anything (it ends the run's claim). -/
theorem outOfFuel {α : Type} {ch : Choices} (n : D α) : Sim ch (Sql.outOfFuel : M α) n where
  exhausted_mono := fun _ _ _ => rfl
  choices_eq := fun _ h => h
  sound := fun c _ hx => by
    have : (runM (Sql.outOfFuel : M α) c).2.exhausted = true := rfl
    rw [this] at hx; exact absurd hx (by decide)

end Sim

/-! ## The lockstep tactic

The interpreter's and the denotation's definitions are the same code (the
denotation is derived from the interpreter); `sim` walks both in step:
binds, state, loops, `try`, `match`/`if` (split on the interpreter's side,
the denotation's reduced with the same hypotheses), the oracle's orders, and
the recursive calls by the hypotheses in context. -/

open Lean Elab Tactic Meta in
/-- Close `Sim ch (Sql.f …) (Den.f …)` by the induction hypothesis `h_f` in
    context, or else by the lemma `Sim.f`, chosen by the interpreter side's
    head `f`, then unified at default transparency (the two sides' arguments
    can differ in their auxiliary matchers, which elaborate separately). -/
elab "sim_by_head" : tactic => withMainContext do
  let t ← whnfR (← getMainTarget)
  let (fn, args) := t.getAppFnArgs
  unless fn == ``Sql.Den.Sim && args.size == 4 do throwError "sim_by_head: not a Sim goal"
  -- a local function (a `let` the goal's lets were lifted into): unfold it,
  -- and the denotation side's head too, in this goal only
  if let .fvar fv := args[2]!.getAppFn then
    let some d ← fv.findDecl? | throwError "sim_by_head: unknown local"
    unless d.isLet do
      -- a function parameter `f`: its hypothesis `h_f`
      let some h := (← getLCtx).findFromUserName? (.mkSimple ("h_" ++ d.userName.toString))
        | throwError "sim_by_head: local {d.userName} has no value"
      evalTactic (← `(tactic| apply $(mkIdent h.userName)))
      return
    let mut fvs := #[fv]
    if let .fvar gv := args[3]!.getAppFn then
      if let some d' ← gv.findDecl? then
        if d'.isLet then fvs := fvs.push gv
    let g ← getMainGoal
    let t' ← zetaDeltaFVars (← g.getType) fvs
    replaceMainGoal [← g.replaceTargetDefEq t']
    -- the unfolded function applied: beta-reduce
    evalTactic (← `(tactic| try simp only []))
    return
  let .const f _ := args[2]!.getAppFn | throwError "sim_by_head: no head constant"
  -- only the interpreter's own functions (`Sql.f`)
  unless f.getPrefix == `Sql do throwError "sim_by_head: {f} is not an interpreter function"
  let short := f.getString!
  if let some d := (← getLCtx).findFromUserName? (.mkSimple ("h_" ++ short)) then
    evalTactic (← `(tactic| apply $(mkIdent d.userName)))
  else
    let lem := (`Sql.Den.Sim).append (.mkSimple short)
    unless (← getEnv).contains lem do throwError "sim_by_head: no lemma for {f}"
    evalTactic (← `(tactic| apply $(mkIdent lem)))

open Lean Elab Tactic Meta in
/-- Rewrite with `h : lhs = rhs`, `lhs` a matcher application, the subterms
    of the goal that are another matcher's applications definitionally equal
    to `lhs`: the interpreter's and the denotation's copies of a match are
    distinct auxiliary constants, so after `split` on the interpreter's, the
    hypothesis rewrites the denotation's this way. -/
elab "sim_rw_match " h:ident : tactic => withMainContext do
  let hd ← getLocalDeclFromUserName h.getId
  let some (ty, lhs, rhs) := (← instantiateMVars hd.type).eq? | throwError "sim_rw_match: not an equation"
  let .const lf _ := lhs.getAppFn | throwError "sim_rw_match: no head"
  unless ← isMatcher lf do throwError "sim_rw_match: not a matcher"
  let target ← instantiateMVars (← getMainTarget)
  let cands ← IO.mkRef (#[] : Array Lean.Expr)
  forEachExpr target fun t => do
    if let .const tf _ := t.getAppFn then
      if tf != lf && t.getAppNumArgs == lhs.getAppNumArgs then
        if ← isMatcher tf then cands.modify (·.push t)
  let mut found : Option Lean.Expr := none
  for t in ← cands.get do
    if ← withNewMCtxDepth (isDefEq t lhs) then
      found := some t; break
  let some t := found | throwError "sim_rw_match: no matching subterm"
  let abst ← kabstract target t
  let motive := Lean.mkLambda `x .default ty abst
  let eqP ← mkExpectedTypeHint hd.toExpr (← mkEq t rhs)
  let proof ← mkCongrArg motive eqP
  let newTarget := abst.instantiate1 rhs
  replaceMainGoal [← (← getMainGoal).replaceTargetEq newTarget proof]


open Lean Elab Tactic Meta in
/-- When a side of the goal is a match on a local definition (one of the
    goal's lets, lifted by `lift_lets`), unfold that definition there. -/
elab "sim_zeta_discr" : tactic => withMainContext do
  let t ← whnfR (← getMainTarget)
  let (fn, args) := t.getAppFnArgs
  unless fn == ``Sql.Den.Sim && args.size == 4 do throwError "sim_zeta_discr: not a Sim goal"
  let mut done := false
  for side in [args[2]!, args[3]!] do
    let .const f _ := side.getAppFn | continue
    unless ← isMatcher f do continue
    for a in side.getAppArgs do
      if let .fvar fv := a then
        if let some d ← fv.findDecl? then
          if d.isLet then
            let g ← getMainGoal
            let t' ← zetaDeltaFVars (← g.getType) #[fv]
            replaceMainGoal [← g.replaceTargetDefEq t']
            done := true
  unless done do throwError "sim_zeta_discr: nothing to unfold"

/-- One lockstep step of a simulation proof. Lemmas are applied up to
    reducible unfolding only, so that a failed attempt is cheap; the side
    conditions they leave (equalities of the two sides' pure values, which
    differ in their auxiliary matchers) are closed by `rfl`. -/
syntax "sim_step" : tactic
macro_rules
  | `(tactic| sim_step) => `(tactic| first
      | with_reducible exact Sim.pure _
      | with_reducible exact Sim.throw _
      | with_reducible exact Sim.err _ _
      | with_reducible exact Sim.getDb
      | with_reducible exact Sim.chooseOrder _
      | with_reducible exact Sim.outOfFuel _
      | sim_by_head
      | assumption
      | (with_reducible apply Sim.bind; rotate_left; intro _)
      | (with_reducible apply Sim.map)
      | ((with_reducible apply Sim.pure_eq); rfl)
      | (with_reducible apply Sim.get_bind; intro _ _)
      | ((with_reducible apply Sim.modify) <;> intro _ <;> rfl)
      | (with_reducible apply Sim.tryCatch; rotate_left; intro _)
      | ((with_reducible apply Sim.forIn_list_eq); rfl; rfl; intro _ _)
      | ((with_reducible apply Sim.forIn_array_eq); rfl; rfl; intro _ _)
      | ((with_reducible apply Sim.forIn_range_eq); rfl; rfl; intro _ _)
      | (with_reducible apply Sim.forIn'_range; intro _ _ _)
      | (with_reducible apply Sim.forIn'_list; intro _ _ _)
      | ((with_reducible apply Sim.mapM_list_eq); rfl; intro _)
      | ((with_reducible apply Sim.mapM_array_eq); rfl; intro _)
      | ((with_reducible apply Sim.foldlM_list_eq); rfl; rfl; intro _ _)
      | sim_zeta_discr
      -- a hypothesis a lemma asks for (a simulation for all arguments)
      | intro _
      -- the interpreter's match (or if); the hypothesis it gives rewrites
      -- the denotation's (up to defeq: their matchers are distinct constants)
      | (split <;> (try simp only [*]) <;> (try (rename_i h; first | sim_rw_match h | erw [h]))
          <;> (try simp only []))
      | (with_reducible apply Sim.forM_list; intro _)
      | (with_reducible apply Sim.forM_option; intro _)
      | ((with_reducible apply Sim.forM_list_eq); rfl; intro _)
      | (with_reducible apply Sim.filterMapM_array; intro _)
      | ((with_reducible apply Sim.earlyReturn_runK) <;> intro _)
      | (with_reducible exact Sim.earlyReturn_return _))

/-- A simulation proof by lockstep. Last, the goals where the two sides'
    matches were split apart (after the interpreter's catch-all case the
    denotation's match is split too): their hypotheses contradict. -/
macro "sim" : tactic =>
  `(tactic| ((try simp only []); (repeat' sim_step); (all_goals (try (exfalso; solve_by_elim (maxDepth := 3))))))

end Sql.Den
