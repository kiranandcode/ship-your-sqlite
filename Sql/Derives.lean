/-
  The relational semantics of SQL (Phase 2.5): the outputs a script may
  produce. SQL leaves some choices to the implementation (PHASES.md,
  "Unspecified choices"): the order the plan visits rows (row order without
  ORDER BY, ORDER BY ties, group and DISTINCT representatives, the input
  order of aggregates), SQLite's PRNG, the random rowid after 2^63−1. The
  executable semantics `runScriptWith` takes them as a `Choices` argument;
  a derivation is a run with some choices and enough fuel.
-/
import Sql.Exec

namespace Sql

/-- `out` is an output of `src`: a run with some choices whose fuel did not
    run out. The refinement theorem (Phase 3) states that SQLite's output on
    `src` is one. -/
inductive Derives (src out : ByteArray) : Prop where
  | intro (choices : Choices) (fuel : Nat)
      (complete : (runScriptWith choices fuel src).exhausted = false)
      (output : (runScriptWith choices fuel src).out = out)

/-- The executable semantics is sound: when its fuel does not run out, its
    output is a derivation's. -/
theorem runScript_derives (src : ByteArray)
    (h : (runScriptWith {} evalFuel src).exhausted = false) :
    Derives src (runScript src) :=
  ⟨{}, evalFuel, h, rfl⟩

end Sql
