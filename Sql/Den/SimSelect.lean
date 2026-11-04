/-
  The interpreter's query evaluation is simulated by the denotation
  (Phase 2.6g): for every fuel, each function of the interpreter's mutual
  block (`Sql/Select.lean`) is simulated by its denotation.
-/
import Sql.Den.Sim

namespace Sql.Den

open Sql

/-! Helpers of the block (not recursive) -/

theorem Sim.limitValue {ch : Choices} (v : Value) : Sim ch (Sql.limitValue v) (Den.limitValue v) := by
  unfold Sql.limitValue Den.limitValue
  repeat' (first | exact Sim.pure _ | exact Sim.err _ _ | exact Sim.throw _ | (split <;> (try simp only [*])))

theorem Sim.checkArity {ch : Choices} (n : Name) (k : Nat) : Sim ch (Sql.checkArity n k) (Den.checkArity n k) := by
  unfold Sql.checkArity Den.checkArity
  simp only []
  repeat' (first | exact Sim.pure _ | exact Sim.err _ _ | exact Sim.throw _ | (split <;> (try simp only [*])))

theorem Sim.affOf {ch : Choices} (env : Env) (e : Expr) : Sim ch (Sql.affOf env e) (Den.affOf env e) := by
  unfold Sql.affOf Den.affOf
  exact Sim.bind Sim.getDb fun _ => Sim.pure _

macro_rules | `(tactic| sim_helper) => `(tactic| first
  | with_reducible exact Sim.affOf _ _
  | with_reducible exact Sim.limitValue _
  | with_reducible exact Sim.checkArity _ _)

/-- Every function of the interpreter's query block, at `fuel`, is simulated
    by its denotation. -/
structure SelectSim (ch : Choices) (fuel : Nat) : Prop where
  evalExpr : ∀ (q : QEnv) (e : Expr), Sim ch (Sql.evalExpr fuel q e) (Den.evalExpr q e)
  compareRows : ∀ (q : QEnv) (op : BinOp) (xs : List Expr) (ys : List Expr), Sim ch (Sql.compareRows fuel q op xs ys) (Den.compareRows q op xs ys)
  valueOf : ∀ (q : QEnv) (r0 : Resolved), Sim ch (Sql.valueOf fuel q r0) (Den.valueOf q r0)
  evalAgg : ∀ (q : QEnv) (n : Name) (distinct : Bool) (args : List Expr) (star : Bool) (ob : List OrderTerm) (filter : Option Expr), Sim ch (Sql.evalAgg fuel q n distinct args star ob filter) (Den.evalAgg q n distinct args star ob filter)
  aggFinish : ∀ (q : QEnv) (n : Name) (star : Bool) (args : List Expr) (coll : Coll) (vals : Array (List Value)) (jflags : Option (Array (List Bool))), Sim ch (Sql.aggFinish fuel q n star args coll vals jflags) (Den.aggFinish q n star args coll vals jflags)
  callAgg : ∀ (_q : QEnv) (name : String) (vals : Array (List Value)) (flags : List Bool) (rowFlags : Option (Array (List Bool))), Sim ch (Sql.callAgg fuel _q name vals flags rowFlags) (Den.callAgg _q name vals flags rowFlags)
  argIsJson : ∀ (q : QEnv) (a : Expr), Sim ch (Sql.argIsJson fuel q a) (Den.argIsJson q a)
  callFn : ∀ (q : QEnv) (n : Name) (args : List Expr) (distinct : Bool), Sim ch (Sql.callFn fuel q n args distinct) (Den.callFn q n args distinct)
  callFnST : ∀ (q : QEnv) (n : Name) (args : List Expr) (_distinct : Bool), Sim ch (Sql.callFnST fuel q n args _distinct) (Den.callFnST q n args _distinct)
  condJump : ∀ (q : QEnv) (e : Expr) (sense : Bool) (jn : Bool), Sim ch (Sql.condJump fuel q e sense jn) (Den.condJump q e sense jn)
  condHolds : ∀ (q : QEnv) (e : Expr), Sim ch (Sql.condHolds fuel q e) (Den.condHolds q e)
  evalExprST : ∀ (q : QEnv) (e : Expr), Sim ch (Sql.evalExprST fuel q e) (Den.evalExprST q e)
  scalarFn : ∀ (n : Name) (vs : List Value) (colls : List (Option (Coll × Bool))), Sim ch (Sql.scalarFn fuel n vs colls) (Den.scalarFn n vs colls)
  resolveWindow : ∀ (windows : List (Name × Window)) (w : Window), Sim ch (Sql.resolveWindow fuel windows w) (Den.resolveWindow windows w)
  computeWindow : ∀ (ctxs : Array QEnv) (windows : List (Name × Window)) (call : Expr), Sim ch (Sql.computeWindow fuel ctxs windows call) (Den.computeWindow ctxs windows call)
  evalFromWhere : ∀ (q : QEnv) (f : FromItem) (where_ : Option Expr) (aliases : List (Name × Expr)), Sim ch (Sql.evalFromWhere fuel q f where_ aliases) (Den.evalFromWhere q f where_ aliases)
  namedSource : ∀ (q : QEnv) (sch : Option Name) (n : Name) («alias» : Name), Sim ch (Sql.namedSource fuel q sch n «alias») (Den.namedSource q sch n «alias»)
  cteRows : ∀ (q : QEnv) (n : Name) (cv0 : CteVal), Sim ch (Sql.cteRows fuel q n cv0) (Den.cteRows q n cv0)
  evalFrom : ∀ (q : QEnv) (f0 : FromItem), Sim ch (Sql.evalFrom fuel q f0) (Den.evalFrom q f0)
  viewCols : Sim ch (Sql.viewCols fuel) Den.viewCols
  tableFnSrc : ∀ (n : Name) («alias» : Option Name), Sim ch (Sql.tableFnSrc fuel n «alias») (Den.tableFnSrc n «alias»)
  tableFunction : ∀ (n : Name) (argsJ : List (Value × Bool)), Sim ch (Sql.tableFunction fuel n argsJ) (Den.tableFunction n argsJ)
  expandCols : ∀ (srcs : Array Src) (cols : List ResultCol), Sim ch (Sql.expandCols fuel srcs cols) (Den.expandCols srcs cols)
  runCore : ∀ (q : QEnv) (core : SelectCore) (orderBy : List OrderTerm) (noRows : Bool) (lim : Option Nat) (off : Nat) (stream : Bool), Sim ch (Sql.runCore fuel q core orderBy noRows lim off stream) (Den.runCore q core orderBy noRows lim off stream)
  runSelect : ∀ (q : QEnv) (sel : Select) (cap : Bool) (stream : Bool), Sim ch (Sql.runSelect fuel q sel cap stream) (Den.runSelect q sel cap stream)

set_option hygiene false in
/-- The induction hypotheses of the query block, named `h_<function>`. -/
macro_rules | `(tactic| sim_ih) => `(tactic| first
  | with_reducible exact h_evalExpr _ _
  | with_reducible exact h_compareRows _ _ _ _
  | with_reducible exact h_valueOf _ _
  | with_reducible exact h_evalAgg _ _ _ _ _ _ _
  | with_reducible exact h_aggFinish _ _ _ _ _ _ _ _ _ _
  | with_reducible exact h_callAgg _ _ _ _ _ _ _ _
  | with_reducible exact h_argIsJson _ _
  | with_reducible exact h_callFn _ _ _ _
  | with_reducible exact h_callFnST _ _ _ _
  | with_reducible exact h_condJump _ _ _ _
  | with_reducible exact h_condHolds _ _
  | with_reducible exact h_evalExprST _ _
  | with_reducible exact h_scalarFn _ _ _ _ _
  | with_reducible exact h_resolveWindow _ _ _
  | with_reducible exact h_computeWindow _ _ _ _
  | with_reducible exact h_evalFromWhere _ _ _ _ _
  | with_reducible exact h_namedSource _ _ _ _
  | with_reducible exact h_cteRows _ _ _
  | with_reducible exact h_evalFrom _ _
  | with_reducible exact h_viewCols
  | with_reducible exact h_tableFnSrc _ _
  | with_reducible exact h_tableFunction _ _ _
  | with_reducible exact h_expandCols _ _
  | with_reducible exact h_runCore _ _ _ _ _ _ _
  | with_reducible exact h_runSelect _ _ _ _)

theorem selectSim_zero (ch : Choices) : SelectSim ch 0 where
  evalExpr := by intros; rw [Sql.evalExpr]; exact Sim.outOfFuel _
  compareRows := by intros; rw [Sql.compareRows]; exact Sim.outOfFuel _
  valueOf := by intros; rw [Sql.valueOf]; exact Sim.outOfFuel _
  evalAgg := by intros; rw [Sql.evalAgg]; exact Sim.outOfFuel _
  aggFinish := by intros; rw [Sql.aggFinish]; exact Sim.outOfFuel _
  callAgg := by intros; rw [Sql.callAgg]; exact Sim.outOfFuel _
  argIsJson := by intros; rw [Sql.argIsJson]; exact Sim.outOfFuel _
  callFn := by intros; rw [Sql.callFn]; exact Sim.outOfFuel _
  callFnST := by intros; rw [Sql.callFnST]; exact Sim.outOfFuel _
  condJump := by intros; rw [Sql.condJump]; exact Sim.outOfFuel _
  condHolds := by intros; rw [Sql.condHolds]; exact Sim.outOfFuel _
  evalExprST := by intros; rw [Sql.evalExprST]; exact Sim.outOfFuel _
  scalarFn := by intros; rw [Sql.scalarFn]; exact Sim.outOfFuel _
  resolveWindow := by intros; rw [Sql.resolveWindow]; exact Sim.outOfFuel _
  computeWindow := by intros; rw [Sql.computeWindow]; exact Sim.outOfFuel _
  evalFromWhere := by intros; rw [Sql.evalFromWhere]; exact Sim.outOfFuel _
  namedSource := by intros; rw [Sql.namedSource]; exact Sim.outOfFuel _
  cteRows := by intros; rw [Sql.cteRows]; exact Sim.outOfFuel _
  evalFrom := by intros; rw [Sql.evalFrom]; exact Sim.outOfFuel _
  viewCols := by intros; rw [Sql.viewCols]; exact Sim.outOfFuel _
  tableFnSrc := by intros; rw [Sql.tableFnSrc]; exact Sim.outOfFuel _
  tableFunction := by intros; rw [Sql.tableFunction]; exact Sim.outOfFuel _
  expandCols := by intros; rw [Sql.expandCols]; exact Sim.outOfFuel _
  runCore := by intros; rw [Sql.runCore]; exact Sim.outOfFuel _
  runSelect := by intros; rw [Sql.runSelect]; exact Sim.outOfFuel _

theorem sim_evalExpr {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (e : Expr), Sim ch (Sql.evalExpr (fuel + 1) q e) (Den.evalExpr q e) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.evalExpr Den.evalExpr; sim

theorem sim_compareRows {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (op : BinOp) (xs : List Expr) (ys : List Expr), Sim ch (Sql.compareRows (fuel + 1) q op xs ys) (Den.compareRows q op xs ys) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.compareRows Den.compareRows; sim

theorem sim_valueOf {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (r0 : Resolved), Sim ch (Sql.valueOf (fuel + 1) q r0) (Den.valueOf q r0) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.valueOf Den.valueOf; sim

theorem sim_evalAgg {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (n : Name) (distinct : Bool) (args : List Expr) (star : Bool) (ob : List OrderTerm) (filter : Option Expr), Sim ch (Sql.evalAgg (fuel + 1) q n distinct args star ob filter) (Den.evalAgg q n distinct args star ob filter) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.evalAgg Den.evalAgg; sim

theorem sim_aggFinish {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (n : Name) (star : Bool) (args : List Expr) (coll : Coll) (vals : Array (List Value)) (jflags : Option (Array (List Bool))), Sim ch (Sql.aggFinish (fuel + 1) q n star args coll vals jflags) (Den.aggFinish q n star args coll vals jflags) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.aggFinish Den.aggFinish; sim

theorem sim_callAgg {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (_q : QEnv) (name : String) (vals : Array (List Value)) (flags : List Bool) (rowFlags : Option (Array (List Bool))), Sim ch (Sql.callAgg (fuel + 1) _q name vals flags rowFlags) (Den.callAgg _q name vals flags rowFlags) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.callAgg Den.callAgg; sim

theorem sim_argIsJson {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (a : Expr), Sim ch (Sql.argIsJson (fuel + 1) q a) (Den.argIsJson q a) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.argIsJson Den.argIsJson; sim

theorem sim_callFn {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (n : Name) (args : List Expr) (distinct : Bool), Sim ch (Sql.callFn (fuel + 1) q n args distinct) (Den.callFn q n args distinct) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.callFn Den.callFn; sim

theorem sim_callFnST {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (n : Name) (args : List Expr) (_distinct : Bool), Sim ch (Sql.callFnST (fuel + 1) q n args _distinct) (Den.callFnST q n args _distinct) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.callFnST Den.callFnST; sim

theorem sim_condJump {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (e : Expr) (sense : Bool) (jn : Bool), Sim ch (Sql.condJump (fuel + 1) q e sense jn) (Den.condJump q e sense jn) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.condJump Den.condJump; sim

theorem sim_condHolds {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (e : Expr), Sim ch (Sql.condHolds (fuel + 1) q e) (Den.condHolds q e) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.condHolds Den.condHolds; sim

theorem sim_evalExprST {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (e : Expr), Sim ch (Sql.evalExprST (fuel + 1) q e) (Den.evalExprST q e) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.evalExprST Den.evalExprST; sim

theorem sim_scalarFn {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (n : Name) (vs : List Value) (colls : List (Option (Coll × Bool))), Sim ch (Sql.scalarFn (fuel + 1) n vs colls) (Den.scalarFn n vs colls) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.scalarFn Den.scalarFn; sim

theorem sim_resolveWindow {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (windows : List (Name × Window)) (w : Window), Sim ch (Sql.resolveWindow (fuel + 1) windows w) (Den.resolveWindow windows w) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.resolveWindow Den.resolveWindow; sim

theorem sim_computeWindow {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (ctxs : Array QEnv) (windows : List (Name × Window)) (call : Expr), Sim ch (Sql.computeWindow (fuel + 1) ctxs windows call) (Den.computeWindow ctxs windows call) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.computeWindow Den.computeWindow; sim

theorem sim_evalFromWhere {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (f : FromItem) (where_ : Option Expr) (aliases : List (Name × Expr)), Sim ch (Sql.evalFromWhere (fuel + 1) q f where_ aliases) (Den.evalFromWhere q f where_ aliases) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.evalFromWhere Den.evalFromWhere; sim

theorem sim_namedSource {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (sch : Option Name) (n : Name) («alias» : Name), Sim ch (Sql.namedSource (fuel + 1) q sch n «alias») (Den.namedSource q sch n «alias») := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.namedSource Den.namedSource; sim

theorem sim_cteRows {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (n : Name) (cv0 : CteVal), Sim ch (Sql.cteRows (fuel + 1) q n cv0) (Den.cteRows q n cv0) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.cteRows Den.cteRows; sim

theorem sim_evalFrom {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (f0 : FromItem), Sim ch (Sql.evalFrom (fuel + 1) q f0) (Den.evalFrom q f0) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.evalFrom Den.evalFrom; sim

theorem sim_viewCols {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    Sim ch (Sql.viewCols (fuel + 1)) Den.viewCols := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.viewCols Den.viewCols; sim

theorem sim_tableFnSrc {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (n : Name) («alias» : Option Name), Sim ch (Sql.tableFnSrc (fuel + 1) n «alias») (Den.tableFnSrc n «alias») := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.tableFnSrc Den.tableFnSrc; sim

theorem sim_tableFunction {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (n : Name) (argsJ : List (Value × Bool)), Sim ch (Sql.tableFunction (fuel + 1) n argsJ) (Den.tableFunction n argsJ) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.tableFunction Den.tableFunction; sim

theorem sim_expandCols {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (srcs : Array Src) (cols : List ResultCol), Sim ch (Sql.expandCols (fuel + 1) srcs cols) (Den.expandCols srcs cols) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.expandCols Den.expandCols; sim

theorem sim_runCore {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (core : SelectCore) (orderBy : List OrderTerm) (noRows : Bool) (lim : Option Nat) (off : Nat) (stream : Bool), Sim ch (Sql.runCore (fuel + 1) q core orderBy noRows lim off stream) (Den.runCore q core orderBy noRows lim off stream) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.runCore Den.runCore; sim

theorem sim_runSelect {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) :
    ∀ (q : QEnv) (sel : Select) (cap : Bool) (stream : Bool), Sim ch (Sql.runSelect (fuel + 1) q sel cap stream) (Den.runSelect q sel cap stream) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_scalarFn, h_resolveWindow, h_computeWindow, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect⟩ := ih
  intros; unfold Sql.runSelect Den.runSelect; sim

end Sql.Den
