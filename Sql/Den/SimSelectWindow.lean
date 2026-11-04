/-
  The simulation of `windowRowValue` (Phase 2.6g), by cases on the window
  function's name: each case alone is within the elaboration budget (the
  match on the name reduces to one branch, which inlines only the closures
  it uses).
-/
import Sql.Den.SimSelectBase

namespace Sql.Den

open Sql

theorem sim_windowRowValue_row_number {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "row_number") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_rank {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "rank") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_dense_rank {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "dense_rank") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_percent_rank {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "percent_rank") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_cume_dist {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "cume_dist") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_ntile {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "ntile") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_lag {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "lag") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_lead {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "lead") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_first_value {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "first_value") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_last_value {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "last_value") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_nth_value {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h : name = "nth_value") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  subst h
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue_default {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat)
    (h0 : name ≠ "row_number")
    (h1 : name ≠ "rank")
    (h2 : name ≠ "dense_rank")
    (h3 : name ≠ "percent_rank")
    (h4 : name ≠ "cume_dist")
    (h5 : name ≠ "ntile")
    (h6 : name ≠ "lag")
    (h7 : name ≠ "lead")
    (h8 : name ≠ "first_value")
    (h9 : name ≠ "last_value")
    (h10 : name ≠ "nth_value") :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  obtain ⟨h_evalExpr, h_compareRows, h_valueOf, h_evalAgg, h_aggFinish, h_callAgg, h_argIsJson, h_callFn, h_callFnST, h_condJump, h_condHolds, h_evalExprST, h_resolveWindow, h_computeWindow, h_windowRowValue, h_windowPartition, h_evalFromWhere, h_namedSource, h_cteRows, h_evalFrom, h_viewCols, h_tableFnSrc, h_tableFunction, h_expandCols, h_runCore, h_runSelect, h_limitOffset, h_runSimple, h_runUnionAll, h_runCompound⟩ := ih
  unfold Sql.windowRowValue Den.windowRowValue
  sim

theorem sim_windowRowValue {ch : Choices} {fuel : Nat} (ih : SelectSim ch fuel) (ctxs : Array QEnv) (name : String) (n : Name)
    (args : List Expr) (star : Bool) (ord : List OrderTerm) (frame : Option Frame) (okeys : Array (Array Value))
    (ocolls : List Coll) (odirs : List (SortDir × NullsOrder)) (argv : Array (List Value)) (pass : Array Bool)
    (p : Array Nat) (pi : PeerInfo) (j : Nat) :
    Sim ch (Sql.windowRowValue (fuel + 1) ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j)
      (Den.windowRowValue ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j) := by
  by_cases h0 : name = "row_number"
  · exact sim_windowRowValue_row_number ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h0
  by_cases h1 : name = "rank"
  · exact sim_windowRowValue_rank ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h1
  by_cases h2 : name = "dense_rank"
  · exact sim_windowRowValue_dense_rank ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h2
  by_cases h3 : name = "percent_rank"
  · exact sim_windowRowValue_percent_rank ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h3
  by_cases h4 : name = "cume_dist"
  · exact sim_windowRowValue_cume_dist ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h4
  by_cases h5 : name = "ntile"
  · exact sim_windowRowValue_ntile ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h5
  by_cases h6 : name = "lag"
  · exact sim_windowRowValue_lag ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h6
  by_cases h7 : name = "lead"
  · exact sim_windowRowValue_lead ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h7
  by_cases h8 : name = "first_value"
  · exact sim_windowRowValue_first_value ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h8
  by_cases h9 : name = "last_value"
  · exact sim_windowRowValue_last_value ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h9
  by_cases h10 : name = "nth_value"
  · exact sim_windowRowValue_nth_value ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h10
  exact sim_windowRowValue_default ih ctxs name n args star ord frame okeys ocolls odirs argv pass p pi j h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

end Sql.Den
