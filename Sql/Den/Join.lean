/-
  SQLite's nested loops over the sources of a join (Phase 2.6), as a meaning
  function parameterised by the actions of each depth, and its monotonicity in
  those actions (so that the meaning functions that use it, whose actions
  call back into the mutual recursion, are `partial_fixpoint`s).
-/
import Sql.Den.Domain
import Sql.Select

namespace Sql.Den

open Sql Lean.Order

/-- A join prepared for SQLite's nested loops (`joinPrepare`): the leaves
    of the chain of inner joins, their sources, the rows of the table leaves
    (in scan order; a table-valued function's are computed per partial row),
    the nesting order (depth → leaf), each conjunct with the depth where the
    last leaf it names is bound, and the result-column aliases. -/
structure JoinPlan where
  leaves : Array FromItem
  leafSrcs : Array (Array Src)
  leafRows : Array (Option (Array (Array Cur)))
  nest : Array Nat
  byDepth : List (Nat × Expr)
  aliases : List (Name × Expr)

namespace JoinPlan

/-- The sources of all leaves, in FROM's order. -/
def srcs (p : JoinPlan) : Array Src := p.leafSrcs.foldl (· ++ ·) #[]

/-- Where each leaf's columns start in a row. -/
def offsets (p : JoinPlan) : Array Nat :=
  (p.leafSrcs.foldl (fun (acc : Array Nat × Nat) ss => (acc.1.push acc.2, acc.2 + ss.size)) (#[], 0)).1

/-- The partial row with no leaf bound. -/
def empty (p : JoinPlan) : Array Cur := Array.replicate p.srcs.size none

/-- Bind leaf `k` to row `r` in a partial row. -/
def place (p : JoinPlan) (cur : Array Cur) (k : Nat) (r : Array Cur) : Array Cur := Id.run do
  let mut c := cur
  for h : j in [0:r.size] do c := c.set! (p.offsets[k]! + j) r[j]
  return c

/-- The plan, the depth of each conjunct computed from the names it uses
    (the leaves whose sources those names hit). -/
def make (leaves : Array FromItem) (leafSrcs : Array (Array Src)) (leafRows : Array (Option (Array (Array Cur))))
    (nest : Array Nat) (conds : List Expr) (aliases : List (Name × Expr)) : JoinPlan :=
  let srcs := leafSrcs.foldl (· ++ ·) #[]
  let leafOf : Array Nat := (leafSrcs.mapIdx fun i ss => Array.replicate ss.size i).foldl (· ++ ·) #[]
  let leavesOf (e : Expr) : List Nat := Id.run do
    let mut ls : List Nat := []
    for (t, c) in exprRefs e do
      for h : si in [0:srcs.size] do
        let s := srcs[si]
        let hit := match t with
          | some tn => nameEq s.alias tn
          | none => s.cols.any (fun (n, _, _) => nameEq n c) || (s.hasRowid && isRowidName c)
        if hit && !ls.contains leafOf[si]! then ls := leafOf[si]! :: ls
    return ls
  let depthOf : Array Nat := Id.run do
    let mut d := Array.replicate leaves.size 0
    for h : i in [0:nest.size] do d := d.set! nest[i] i
    return d
  { leaves, leafSrcs, leafRows, nest, aliases,
    byDepth := conds.map fun e => ((leavesOf e).foldl (fun m l => max m depthOf[l]!) 0, e) }

end JoinPlan

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

end Sql.Den
