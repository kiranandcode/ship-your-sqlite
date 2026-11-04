/-
  SQLite's nested loops over the sources of a join (Phase 2.6), as a meaning
  function parameterised by the actions of each depth, and its monotonicity in
  those actions (so that the meaning functions that use it, whose actions
  call back into the mutual recursion, are `partial_fixpoint`s). The plan of
  a join (`Sql.JoinPlan`) is the interpreter's.
-/
import Sql.Den.Domain
import Sql.Select

namespace Sql.Den

open Sql Lean.Order

/-- An action's outcome as a value: its result, or the error it raised. -/
def attempt {α : Type} (m : D α) : D (Except Err α) :=
  tryCatch (do return .ok (← m)) (fun e => return .error e)

@[partial_fixpoint_monotone]
theorem monotone_attempt {α : Type} {γ : Type w} [Lean.Order.PartialOrder γ] (f : γ → D α)
    (hf : monotone f) : monotone (fun x => attempt (f x)) := by
  unfold attempt
  repeat' monotonicity
  all_goals first | exact hf | exact monotone_apply _ _ hf

/-- SQLite's nested loops over the `nL` leaves of a join, the leaf at depth
    `d` being `nest[d]`: from depth `d` with partial row `pre`, each row of
    the leaf that passes the depth's conjuncts goes one level deeper, and a
    completed row goes to `step`, which may end the loops (`false`). The
    result: `step`'s state, whether to go on, and the error that ended the
    loops, if any, with `step`'s state from before it (the rows a SELECT has
    handed out stay out). -/
def joinLoops {σ : Type} (nL : Nat) (nest : Array Nat)
    (rowsAt : Nat → Array Cur → D (Array (Array Cur)))
    (place : Array Cur → Nat → Array Cur → Array Cur)
    (check : Array Cur → Nat → D Bool) (step : σ → Array Cur → D (σ × Bool))
    (d : Nat) (pre : Array Cur) (acc : σ) : D (σ × Bool × Option Err) := do
  if d < nL then
    let k := nest[d]!
    match ← attempt (rowsAt k pre) with
    | .error e => return (acc, false, some e)
    | .ok rows =>
      let mut acc := acc
      for row in rows do
        let cur := place pre k row
        match ← attempt (check cur d) with
        | .error e => return (acc, false, some e)
        | .ok false => continue
        | .ok true =>
          if d + 1 = nL then
            match ← attempt (step acc cur) with
            | .error e => return (acc, false, some e)
            | .ok (a, more) =>
              acc := a
              if !more then return (acc, false, none)
          else
            let (a, more, e?) ← joinLoops nL nest rowsAt place check step (d + 1) cur acc
            acc := a
            if e?.isSome || !more then return (acc, more, e?)
      return (acc, true, none)
  else return (acc, true, none)
termination_by nL - d

/-- `joinLoops` is monotone in the actions of the depths. -/
@[partial_fixpoint_monotone]
theorem monotone_joinLoops {σ : Type} {γ : Type w} [Lean.Order.PartialOrder γ] (nL : Nat) (nest : Array Nat)
    (rowsAt : γ → Nat → Array Cur → D (Array (Array Cur)))
    (place : Array Cur → Nat → Array Cur → Array Cur)
    (check : γ → Array Cur → Nat → D Bool) (step : γ → σ → Array Cur → D (σ × Bool))
    (hr : monotone rowsAt) (hc : monotone check) (hs : monotone step) :
    ∀ (d : Nat) (pre : Array Cur) (acc : σ),
      monotone (fun x => joinLoops nL nest (rowsAt x) place (check x) (step x) d pre acc) := by
  intro d
  induction h : nL - d using Nat.strong_induction_on generalizing d with
  | _ n ih =>
    intro pre acc
    conv => arg 1; ext x; rw [joinLoops.eq_1]
    by_cases hd : d < nL
    · simp only [hd, if_true]
      repeat' monotonicity
      all_goals first
        | exact monotone_apply _ _ (monotone_apply _ _ hr)
        | exact monotone_apply _ _ (monotone_apply _ _ hc)
        | exact monotone_apply _ _ (monotone_apply _ _ hs)
        | exact ih (nL - (d + 1)) (by omega) (d + 1) rfl _ _
    · simp only [hd, if_false]
      exact monotone_const _

/-- A join: its plan, then its loops from depth 0 (the interpreter's
    `evalFromWhereS`). The result: the sources, `step`'s state, and the error
    that ended the loops, if any. -/
def joinRun {σ : Type} (prep : D JoinPlan) (rowsAt : JoinPlan → Nat → Array Cur → D (Array (Array Cur)))
    (check : JoinPlan → Array Cur → Nat → D Bool) (init : σ)
    (step : σ → Array Src → Array Cur → D (σ × Bool)) : D (Array Src × σ × Option Err) := do
  let p ← prep
  let (acc, _, failure) ← joinLoops p.leaves.size p.nest (rowsAt p) p.place (check p) (step · p.srcs ·) 0 p.empty init
  return (p.srcs, acc, failure)

/-- `joinRun` is monotone in its actions. -/
@[partial_fixpoint_monotone]
theorem monotone_joinRun {σ : Type} {γ : Type w} [Lean.Order.PartialOrder γ] (prep : γ → D JoinPlan)
    (rowsAt : γ → JoinPlan → Nat → Array Cur → D (Array (Array Cur)))
    (check : γ → JoinPlan → Array Cur → Nat → D Bool) (init : σ)
    (step : γ → σ → Array Src → Array Cur → D (σ × Bool))
    (hp : monotone prep) (hr : monotone rowsAt) (hc : monotone check) (hs : monotone step) :
    monotone (fun x => joinRun (prep x) (rowsAt x) (check x) init (step x)) := by
  unfold joinRun
  apply monotone_bind
  · exact hp
  · apply monotone_of_monotone_apply
    intro p
    apply monotone_bind
    · apply monotone_joinLoops
      · exact monotone_apply p _ hr
      · exact monotone_apply p _ hc
      · apply monotone_of_monotone_apply; intro a
        apply monotone_of_monotone_apply; intro c
        exact monotone_apply c _ (monotone_apply p.srcs _ (monotone_apply a _ hs))
    · exact monotone_const _

end Sql.Den
