/-
  The functions of the interpreter's query block that `sim` does not prove
  alone (Phase 2.6g): the join (`Sql/Den/SimJoin.lean`), and the recursive
  CTE, whose queue the interpreter runs for at most `fuel` rounds and the
  denotation to empty (a least fixed point).
-/
import Sql.Den.SimJoin

namespace Sql.Den

open Sql

/-- The interpreter's rounds of a recursive CTE are the denotation's, unless
    the fuel runs out. -/
theorem sim_cteLoopM {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (steps : Nat) (q : QEnv) (n : Name) (cols : Array ColMeta) (others : List (Name × CteVal))
      (with_ : List Cte) (wrec : Bool) (recursive : List SelectCore) (ob : List OrderTerm)
      (distinctMode : Bool) (limit : Option Int) (offset : Int) (queue seen out : Array (Array Value))
      (skipped : Int),
      Sim ch (Sql.cteLoopM (Sql.evalExpr fuel) (Sql.runSelect fuel) steps q n cols others with_ wrec recursive ob
          distinctMode limit offset queue seen out skipped)
        (Den.cteLoop q n cols others with_ wrec recursive ob distinctMode limit offset queue seen out skipped) := by
  select_ih ih
  intro steps
  induction steps with
  | zero =>
    intros
    unfold Sql.cteLoopM Den.cteLoop
    sim
  | succ steps h_cteLoopM =>
    intros
    unfold Sql.cteLoopM Den.cteLoop
    sim

theorem sim_cteRows {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (n : Name) (cv0 : CteVal), Sim ch (Sql.cteRows (fuel + 1) q n cv0) (Den.cteRows q n cv0) := by
  have h_cteLoopM := sim_cteLoopM ih fuel
  select_ih ih
  intros
  unfold Sql.cteRows Den.cteRows
  sim

end Sql.Den
