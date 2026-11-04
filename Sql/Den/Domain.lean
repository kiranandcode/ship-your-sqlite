/-
  The semantic domain of the denotational semantics (Phase 2.6, PHASES.md).

  A computation denotes the set of its possible terminating outcomes:
  `Nd α := Set α` with `pure a = {a}` and `s >>= f = ⋃ a ∈ s, f a`, ordered by
  inclusion (the Hoare powerdomain of a discrete set). Divergence contributes
  no outcome: `∅` is the least element. The meaning monad `D` is the
  interpreter's `ExceptT Err (StateM Ctx)` with `Id` replaced by `Nd`.

  Every recursive meaning function is a `partial_fixpoint`: core Lean's
  `Lean.Order.fix` in the CCPO below, lifted through `StateT` and `ExceptT`.
  `fix_eq_lfp` shows that it is Mathlib's least fixed point (`OrderHom.lfp`,
  Knaster–Tarski) of the same functional.
-/
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Lattice
import Sql.Exec

namespace Sql.Den

universe u v

/-- Sets of outcomes. -/
def Nd (α : Type u) : Type u := Set α

namespace Nd

/-- The outcomes, as a set. -/
def toSet {α : Type u} (s : Nd α) : Set α := s

/-- The outcome set with members `s`. -/
def ofSet {α : Type u} (s : Set α) : Nd α := s

instance {α : Type u} : Membership α (Nd α) := ⟨fun s a => a ∈ s.toSet⟩

theorem mem_def {α : Type u} {s : Nd α} {a : α} : a ∈ s ↔ a ∈ s.toSet := Iff.rfl

@[simp] theorem mem_ofSet {α : Type u} {s : Set α} {a : α} : a ∈ ofSet s ↔ a ∈ s := Iff.rfl

instance : Monad Nd where
  pure a := ofSet {b | b = a}
  bind s f := ofSet {b | ∃ a, a ∈ s ∧ b ∈ f a}

@[simp] theorem mem_pure {α : Type u} {a b : α} : b ∈ (pure a : Nd α) ↔ b = a := Iff.rfl

@[simp] theorem mem_bind {α β : Type u} {s : Nd α} {f : α → Nd β} {b : β} :
    b ∈ (s >>= f) ↔ ∃ a, a ∈ s ∧ b ∈ f a := Iff.rfl

@[simp] theorem mem_map {α β : Type u} {s : Nd α} {f : α → β} {b : β} :
    b ∈ (f <$> s) ↔ ∃ a, a ∈ s ∧ b = f a := Iff.rfl

@[ext] theorem ext {α : Type u} {s t : Nd α} (h : ∀ a, a ∈ s ↔ a ∈ t) : s = t := Set.ext h

instance : LawfulMonad Nd := LawfulMonad.mk'
  (id_map := fun x => by ext a; simp)
  (pure_bind := fun x f => by ext a; simp)
  (bind_assoc := fun x f g => by
    ext a; simp only [mem_bind]
    constructor
    · rintro ⟨b, ⟨c, hc, hb⟩, ha⟩; exact ⟨c, hc, b, hb, ha⟩
    · rintro ⟨c, hc, b, hb, ha⟩; exact ⟨b, ⟨c, hc, hb⟩, ha⟩)
  (bind_pure_comp := fun f x => by ext a; simp)

/-! ### The order: inclusion -/

open Lean.Order in
instance instPartialOrder {α : Type u} : Lean.Order.PartialOrder (Nd α) where
  rel s t := ∀ a, a ∈ s → a ∈ t
  rel_refl := fun _ h => h
  rel_trans := fun h₁ h₂ a ha => h₂ a (h₁ a ha)
  rel_antisymm := fun h₁ h₂ => ext fun a => ⟨h₁ a, h₂ a⟩

/-- The union of a family of outcome sets. -/
def sup {α : Type u} (c : Nd α → Prop) : Nd α := ofSet {a | ∃ s, c s ∧ a ∈ s}

open Lean.Order in
theorem sup_is_sup {α : Type u} (c : Nd α → Prop) : is_sup c (sup c) := by
  intro x
  constructor
  · intro h s hs a ha; exact h a ⟨s, hs, ha⟩
  · intro h a ha
    obtain ⟨s, hs, ha⟩ := ha
    exact h s hs a ha

open Lean.Order in
/-- Every family has a least upper bound, so chains do: a CCPO. -/
instance instCCPO {α : Type u} : Lean.Order.CCPO (Nd α) where
  has_csup {c} _ := ⟨sup c, sup_is_sup c⟩

open Lean.Order in
instance instMonoBind : Lean.Order.MonoBind Nd where
  bind_mono_left {_ _ a₁ a₂ f} h := by
    intro b hb
    simp only [mem_bind] at hb ⊢
    obtain ⟨a, ha, hb⟩ := hb
    exact ⟨a, h a ha, hb⟩
  bind_mono_right {_ _ a f₁ f₂} h := by
    intro b hb
    simp only [mem_bind] at hb ⊢
    obtain ⟨x, hx, hb⟩ := hb
    exact ⟨x, hx, h x b hb⟩

/-- Mathlib's order on outcome sets: inclusion, a complete lattice. -/
instance instCompleteLattice {α : Type u} : CompleteLattice (Nd α) :=
  inferInstanceAs (CompleteLattice (Set α))

theorem le_iff_rel {α : Type u} (s t : Nd α) : s ≤ t ↔ Lean.Order.PartialOrder.rel s t :=
  ⟨fun h a ha => h ha, fun h a ha => h a ha⟩

/-! ### Choices -/

/-- Any value satisfying `p`. -/
def any {α : Type u} (p : α → Prop) : Nd α := ofSet {a | p a}

/-- Any permutation of `xs`: an order SQL leaves to the plan. -/
def perm {α : Type u} (xs : List α) : Nd (List α) := any (·.Perm xs)

@[simp] theorem mem_any {α : Type u} {p : α → Prop} {a : α} : a ∈ any p ↔ p a := Iff.rfl

@[simp] theorem mem_perm {α : Type u} {xs ys : List α} : ys ∈ perm xs ↔ ys.Perm xs := Iff.rfl

end Nd

/-! ## The meaning monad -/

/-- The state a meaning function reads and writes: the database and json.c's
    parse cache (per statement). The interpreter's other fields (its choice
    oracle, fuel flag) have no counterpart here. -/
structure DCtx where
  db : Db
  jsonCache : Json.Cache := {}
  deriving Inhabited

/-- A computation: from a state, the set of its outcomes (a result or an
    error, with the state reached). -/
abbrev D (α : Type) : Type := ExceptT Err (StateT DCtx Nd) α

/-- The outcomes of `m` from state `c`. -/
def D.outcomes {α : Type} (m : D α) (c : DCtx) : Nd (Except Err α × DCtx) := (m.run).run c

/-- Mathlib's complete lattice on computations (pointwise inclusion). -/
instance {α : Type} : CompleteLattice (D α) :=
  inferInstanceAs (CompleteLattice (DCtx → Nd (Except Err α × DCtx)))

/-- Any permutation of `xs`. -/
def perm {α : Type} (xs : List α) : D (List α) := liftM (Nd.perm xs : Nd _)

/-- Any value satisfying `p`. -/
def anyOf {α : Type} (p : α → Prop) : D α := liftM (Nd.any p : Nd _)

/-! ## Least fixed points: core's `fix` is Mathlib's `lfp` -/

open Lean.Order in
/-- On a CCPO whose order is that of a Mathlib complete lattice, the fixed
    point `partial_fixpoint` takes (`Lean.Order.fix`) is the least fixed point
    of Knaster–Tarski. -/
theorem fix_eq_lfp {α : Type u} [Lean.Order.CCPO α] [_root_.CompleteLattice α]
    (horder : ∀ a b : α, PartialOrder.rel a b ↔ a ≤ b)
    (F : α → α) (hF : Lean.Order.monotone F) :
    Lean.Order.fix F hF =
      OrderHom.lfp ⟨F, fun a b hab => (horder _ _).1 (hF a b ((horder _ _).2 hab))⟩ := by
  set G : α →o α := ⟨F, fun a b hab => (horder _ _).1 (hF a b ((horder _ _).2 hab))⟩
  apply le_antisymm
  · -- fix is below every pre-fixed point, in particular the lfp
    rw [← horder]
    apply fix_induct hF (fun x => PartialOrder.rel x (OrderHom.lfp G))
    · intro c hc h
      exact csup_le hc h
    · intro x hx
      have h1 : F x ≤ F (OrderHom.lfp G) := G.monotone ((horder _ _).1 hx)
      have h2 : F (OrderHom.lfp G) = OrderHom.lfp G := OrderHom.map_lfp G
      exact (horder _ _).2 (h2 ▸ h1)
  · -- the lfp is below every fixed point, in particular fix
    apply OrderHom.lfp_le
    exact le_of_eq (fix_eq hF).symm

end Sql.Den
