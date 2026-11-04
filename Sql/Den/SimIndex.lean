/-
  The automatic index of the interpreter's join is sound for the
  denotation (Phase 2.6g): a conjunct compiled to a pure test (`PCond`)
  evaluates, in the denotation, to that test's value, from every state and
  without changing it (`Ret`). So a row the index skips is a row the
  denotation's conjuncts reject.
-/
import Sql.Den.Sim

namespace Sql.Den

open Sql

/-- `n` has the outcome `a` from every state, which it leaves unchanged. -/
def Ret {α : Type} (n : D α) (a : α) : Prop := ∀ s, (Except.ok a, s) ∈ n.outcomes s

namespace Ret

theorem pure {α : Type} (a : α) : Ret (Pure.pure a : D α) a := fun _ => Sim.mem_outcomes_pure

theorem bind {α β : Type} {m : D α} {f : α → D β} {a : α} {b : β} (hm : Ret m a) (hf : Ret (f a) b) :
    Ret (m >>= f) b := fun s => by
  rw [Sim.mem_outcomes_bind]
  exact ⟨(.ok a, s), hm s, hf s⟩

theorem getDb_bind {β : Type} {f : Db → D β} {b : β} (hf : ∀ db, Ret (f db) b) : Ret (Den.getDb >>= f) b :=
  fun s => by
    rw [Sim.mem_outcomes_bind]
    refine ⟨(.ok s.db, s), ?_, hf s.db s⟩
    unfold Den.getDb
    rw [Sim.mem_outcomes_bind]
    exact ⟨(.ok s, s), Sim.mem_outcomes_get.mpr rfl, Sim.mem_outcomes_pure⟩

/-- A loop whose body has a constant outcome is the pure loop. -/
theorem forIn {α β : Type} (xs : List α) (init : β) (f : α → β → D (ForInStep β)) (g : α → β → ForInStep β)
    (h : ∀ a b, Ret (f a b) (g a b)) :
    Ret (forIn xs init f) (Id.run (forIn xs init (fun a b => (Pure.pure (g a b) : Id (ForInStep β))))) := by
  induction xs generalizing init with
  | nil => exact Ret.pure _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    refine Ret.bind (h x init) ?_
    cases g x init with
    | done b => exact Ret.pure _
    | yield b => exact ih b

end Ret

/-- The affinity of an expression whose affinity needs no subquery. -/
theorem ret_affOf (env : Env) (e : Expr) (v : Option Aff) (h : ∀ sub, exprAff env e sub = v) :
    Ret (Den.affOf env e) v := by
  unfold Den.affOf
  exact Ret.getDb_bind fun db => h _ ▸ Ret.pure _

/-- A compiled term's value: a column of the innermost scope (read from its
    current row) or a literal. -/
theorem ret_term (q : QEnv) (sc : Scope) (hf : q.env.frames[0]? = some sc) (e : Expr) (t : PTerm)
    (h : compileTerm q.env e = some t) : Ret (Den.evalExpr q e) (t.eval sc.cur) := by
  unfold compileTerm at h
  split at h
  · rename_i sch tn c
    split at h
    · rename_i si ci hr
      cases h
      intro s
      rw [Den.evalExpr.eq_def]
      simp only [hr]
      rw [Den.valueOf.eq_def]
      simp only [hf, PTerm.eval, curValue]
      rcases h' : sc.cur[si]? with _ | _ | r <;> simp only [] <;> exact Sim.mem_outcomes_pure
    · contradiction
  · cases h
    intro s
    rw [Den.evalExpr.eq_def]
    exact Sim.mem_outcomes_pure
  · contradiction

theorem syntaxFuel_succ : syntaxFuel = (syntaxFuel - 1) + 1 := by unfold syntaxFuel; rfl

/-- A compiled term is a column or a literal. -/
theorem compileTerm_shape {env : Env} {e : Expr} {t : PTerm} (h : compileTerm env e = some t) :
    (∃ sch tn c si ci, e = .col sch tn c ∧ resolveCol env tn c = .ok (.col 0 si ci) ∧ t = .col si ci) ∨
      (∃ v, e = .lit v ∧ t = .lit v) := by
  unfold compileTerm at h
  split at h
  · split at h
    · rename_i sch tn c _ si ci hr
      cases h
      exact .inl ⟨sch, tn, c, si, ci, rfl, hr, rfl⟩
    · contradiction
  · rename_i v
    cases h
    exact .inr ⟨v, rfl, rfl⟩
  · contradiction

/-- A compiled term's affinity (needing no subquery). -/
theorem exprAff_term {env : Env} {e : Expr} {t : PTerm} (h : compileTerm env e = some t)
    (sub : Env → Select → Option Aff) : exprAff env e sub = t.aff env := by
  rcases compileTerm_shape h with ⟨sch, tn, c, si, ci, rfl, hr, rfl⟩ | ⟨v, rfl, rfl⟩
  · rw [exprAff]
    simp only [hr, PTerm.aff]
    cases colMetaOf env (.col 0 si ci) <;> rfl
  · rw [exprAff.eq_def]; rfl

/-- A compiled term's collation. -/
theorem exprColl_term {env : Env} {e : Expr} {t : PTerm} (h : compileTerm env e = some t) :
    exprColl env e = t.coll env := by
  rcases compileTerm_shape h with ⟨sch, tn, c, si, ci, rfl, hr, rfl⟩ | ⟨v, rfl, rfl⟩
  · rw [exprColl]
    simp only [hr, PTerm.coll]
    cases colMetaOf env (.col 0 si ci) <;> rfl
  · rw [exprColl.eq_def]; rfl

theorem cmpColl_terms {env : Env} {a b : Expr} {ta tb : PTerm} (ha : compileTerm env a = some ta)
    (hb : compileTerm env b = some tb) : cmpColl env a b = cmpCollOf (ta.coll env) (tb.coll env) := by
  simp only [cmpColl, exprColl_term ha, exprColl_term hb]

theorem ret_affOf_term {env : Env} {e : Expr} {t : PTerm} (h : compileTerm env e = some t) :
    Ret (Den.affOf env e) (t.aff env) :=
  ret_affOf env e _ (exprAff_term h)

/-- A comparison of compiled terms. -/
theorem ret_cmp (q : QEnv) (sc : Scope) (hf : q.env.frames[0]? = some sc) (op : BinOp) (a b : Expr)
    (ta tb : PTerm) (hop : op = .lt ∨ op = .le ∨ op = .gt ∨ op = .ge ∨ op = .eq ∨ op = .ne)
    (ha : compileTerm q.env a = some ta) (hb : compileTerm q.env b = some tb) :
    Ret (Den.evalExpr q (.binop op a b))
      (compareOp op (cmpAff (ta.aff q.env) (tb.aff q.env)) (cmpCollOf (ta.coll q.env) (tb.coll q.env)) (ta.eval sc.cur) (tb.eval sc.cur)) := by
  rw [← cmpColl_terms ha hb]
  have k : Ret (do
      let x ← Den.evalExpr q a
      let y ← Den.evalExpr q b
      let a' ← Den.affOf q.env a
      let b' ← Den.affOf q.env b
      return compareOp op (cmpAff a' b') (cmpColl q.env a b) x y)
      (compareOp op (cmpAff (ta.aff q.env) (tb.aff q.env)) (cmpColl q.env a b) (ta.eval sc.cur) (tb.eval sc.cur)) :=
    Ret.bind (ret_term q sc hf a ta ha) (Ret.bind (ret_term q sc hf b tb hb)
      (Ret.bind (ret_affOf_term ha) (Ret.bind (ret_affOf_term hb) (Ret.pure _))))
  rcases compileTerm_shape ha with ⟨_, _, _, _, _, rfl, _, rfl⟩ | ⟨_, rfl, rfl⟩ <;>
  rcases compileTerm_shape hb with ⟨_, _, _, _, _, rfl, _, rfl⟩ | ⟨_, rfl, rfl⟩ <;>
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl <;>
  (rw [Den.evalExpr.eq_def]; exact k)

/-- The loop of an IN list of compiled terms. -/
theorem ret_inList_loop (q : QEnv) (sc : Scope) (hf : q.env.frames[0]? = some sc) (x : Expr) (v : Value)
    (aff : Option Aff) (haff : Ret (Den.affOf q.env x) aff) :
    ∀ (its : List Expr) (tis : List PTerm), its.mapM (compileTerm q.env) = some tis → ∀ st : Bool × Bool,
    Ret (forIn its st fun it (__s : Bool × Bool) => do
                let w ← Den.evalExpr q it
                let __do_lift ← Den.affOf q.env x
                if (truth (compareOp BinOp.eq __do_lift (cmpColl q.env x it) v w) == some true) = true then
                    pure (ForInStep.done (__s.1, true))
                  else
                    if (compareOp BinOp.eq __do_lift (cmpColl q.env x it) v w).isNull = true then
                      pure (ForInStep.yield (true, __s.2))
                    else pure (ForInStep.yield (__s.1, __s.2)))
      (inListScan v aff st ((tis.zip (its.map (cmpColl q.env x))).map fun (t, c) => (t.eval sc.cur, c))) := by
  intro its
  induction its with
  | nil =>
    intro tis h st
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact Ret.pure _
  | cons it its ih =>
    intro tis h st
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨t, ht, ts, hts, rfl⟩ := h
    simp only [List.forIn_cons, List.map_cons, List.zip_cons_cons, inListScan]
    refine Ret.bind (a :=
      if truth (compareOp BinOp.eq aff (cmpColl q.env x it) v (t.eval sc.cur)) == some true then
        ForInStep.done (st.1, true)
      else if (compareOp BinOp.eq aff (cmpColl q.env x it) v (t.eval sc.cur)).isNull then
        ForInStep.yield (true, st.2) else ForInStep.yield (st.1, st.2))
      ?_ ?_
    · refine Ret.bind (ret_term q sc hf it t ht) ?_
      refine Ret.bind haff ?_
      split <;> (try split) <;> exact Ret.pure _
    · by_cases h1 : (truth (compareOp BinOp.eq aff (cmpColl q.env x it) v (t.eval sc.cur)) == some true) = true
      · simp only [h1, if_true]
        exact Ret.pure _
      · by_cases h2 : (compareOp BinOp.eq aff (cmpColl q.env x it) v (t.eval sc.cur)).isNull = true
        · simp only [h1, h2, if_true, if_false, Bool.false_eq_true]
          exact ih ts hts _
        · simp only [h1, h2, if_false, Bool.false_eq_true]
          exact ih ts hts _

/-- The collations of an IN list's comparisons, from the compiled terms. -/
theorem zip_colls {env : Env} {x : Expr} {tx : PTerm} (hx : compileTerm env x = some tx) :
    ∀ (items : List Expr) (tis : List PTerm), items.mapM (compileTerm env) = some tis →
      tis.zip (items.map (cmpColl env x)) = tis.map fun t => (t, cmpCollOf (tx.coll env) (t.coll env)) := by
  intro items
  induction items with
  | nil =>
    intro tis h
    simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
    subst h; rfl
  | cons it its ih =>
    intro tis h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨t, ht, ts, hts, rfl⟩ := h
    simp only [List.map_cons, List.zip_cons_cons, ih ts hts, cmpColl_terms hx ht]

/-- An IN list of compiled terms. -/
theorem ret_inList (q : QEnv) (sc : Scope) (hf : q.env.frames[0]? = some sc) (x : Expr) (items : List Expr)
    (tx : PTerm) (tis : List PTerm) (hx : compileTerm q.env x = some tx)
    (hits : items.mapM (compileTerm q.env) = some tis) (hne : items.isEmpty = false) :
    Ret (Den.evalExpr q (.inList false x items))
      (inListValue (tx.eval sc.cur) (tx.aff q.env)
        ((tis.map fun t => (t, cmpCollOf (tx.coll q.env) (t.coll q.env))).map fun (t, c) => (t.eval sc.cur, c))) := by
  rw [← zip_colls hx items tis hits]
  rw [Den.evalExpr.eq_def]
  simp only []
  refine Ret.bind (ret_term q sc hf x tx hx) ?_
  simp only [hne, Bool.false_eq_true, if_false]
  refine Ret.bind (ret_inList_loop q sc hf x (tx.eval sc.cur) _ (ret_affOf_term hx) items tis hits (false, false)) ?_
  unfold inListValue
  by_cases hv : (tx.eval sc.cur).isNull = true
  · simp only [hv, if_true]
    exact Ret.pure _
  · simp only [hv, if_false, Bool.false_eq_true]
    exact Ret.pure _

/-- A compiled conjunct's jump is the denotation's `condJump`. -/
theorem ret_condJump (q : QEnv) (sc : Scope) (hf : q.env.frames[0]? = some sc) :
    ∀ (k : Nat) (e : Expr) (c : PCond), compileCondK q.env k e = some c → ∀ sense jn,
      Ret (Den.condJump q e sense jn) (c.jump sc.cur sense jn) := by
  intro k
  induction k with
  | zero => intro e c h; simp [compileCondK] at h
  | succ k ih =>
    intro e c h sense jn
    unfold compileCondK at h
    split at h
    · rename_i op a b
      split at h
      · -- AND
        split at h
        · rename_i hc
          split at h
          · rename_i ca cb hca hcb
            cases h
            simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hc
            obtain ⟨⟨halt, hsa⟩, hsb⟩ := hc
            rw [Den.condJump.eq_def]
            simp only [halt, hsa, Bool.false_and, Bool.false_eq_true, if_false, PCond.jump]
            rcases hp : jumpPlan true sense jn with ⟨⟨s1, j1⟩, short, ⟨s2, j2⟩⟩
            simp only []
            refine Ret.bind (ih a ca hca s1 j1) ?_
            split
            · exact Ret.pure _
            · exact ih b cb hcb s2 j2
          · contradiction
        · contradiction
      · -- OR
        split at h
        · rename_i hc
          split at h
          · rename_i ca cb hca hcb
            cases h
            simp only [Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none] at hc
            obtain ⟨⟨halt, hsa⟩, hsb⟩ := hc
            rw [Den.condJump.eq_def]
            simp only [halt, hsa, Bool.false_and, Bool.false_eq_true, if_false, PCond.jump]
            rcases hp : jumpPlan false sense jn with ⟨⟨s1, j1⟩, short, ⟨s2, j2⟩⟩
            simp only []
            refine Ret.bind (ih a ca hca s1 j1) ?_
            split
            · exact Ret.pure _
            · exact ih b cb hcb s2 j2
          · contradiction
        · contradiction
      -- comparisons
      all_goals first
        | contradiction
        | (split at h
           · rename_i ta tb hta htb
             cases h
             rw [Den.condJump.eq_def]
             exact Ret.bind (ret_cmp q sc hf _ a b ta tb (by simp) hta htb) (Ret.pure _)
           · contradiction)
    · -- NOT
      rename_i a
      obtain ⟨ca, hca, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [Den.condJump.eq_def]
      exact ih a ca hca (!sense) jn
    · -- IN list
      rename_i x items
      split at h
      · contradiction
      · rename_i hne
        split at h
        · rename_i tx tis hx hits
          cases h
          rw [Den.condJump.eq_def]
          exact Ret.bind (ret_inList q sc hf x items tx tis hx hits (by simpa using hne)) (Ret.pure _)
        · contradiction
    · contradiction

theorem ret_condHolds (q : QEnv) (sc : Scope) (hf : q.env.frames[0]? = some sc) (k : Nat) (e : Expr)
    (c : PCond) (h : compileCondK q.env k e = some c) :
    Ret (Den.condHolds q e) (!(c.jump sc.cur false true)) := by
  rw [Den.condHolds.eq_def]
  exact Ret.bind (ret_condJump q sc hf k e c h false true) (Ret.pure _)

/-- The loop of a depth's check over conjuncts `es`, when the automatic
    index rules the row out on them: each compiled conjunct before the
    rejecting one holds (and has no effect), the rejecting one ends the loop. -/
theorem loop_prefix (cur : Array Cur) (env0 : Env)
    (body : Expr → Option Bool × Unit → D (ForInStep (Option Bool × Unit)))
    (hb : ∀ e c, compileConj env0 e = some c →
      Ret (body e (none, ())) (if c.jump cur false true then .done (some false, ()) else .yield (none, ()))) :
    ∀ es : List Expr, skipPrefix cur (es.map (compileConj env0)) = true →
      Ret (forIn es (none, ()) body) (some false, ()) := by
  intro es
  induction es with
  | nil => intro h; simp [skipPrefix] at h
  | cons e es ih =>
    intro h
    simp only [List.map_cons] at h
    rcases hc : compileConj env0 e with _ | c
    · rw [hc] at h; simp [skipPrefix] at h
    · rw [hc] at h
      simp only [skipPrefix, Bool.or_eq_true] at h
      simp only [List.forIn_cons]
      refine Ret.bind (hb e c hc) ?_
      by_cases hj : c.jump cur false true = true
      · simp only [hj, if_true]
        exact Ret.pure _
      · simp only [hj] at h ⊢
        simp only [Bool.false_eq_true, false_or] at h
        exact ih h

/-! ### The scope's current row does not change what the conjuncts compile to -/

/-- Two environments that resolve names alike (they differ in current rows). -/
structure SameScope (env1 env2 : Env) : Prop where
  res : ∀ t n, resolveCol env1 t n = resolveCol env2 t n
  colMeta : ∀ r, colMetaOf env1 r = colMetaOf env2 r

theorem resolveCol_cur (base : Env) (srcs : Array Src) (c1 c2 : Array Cur) (al : List (Name × Expr))
    (fs : List Scope) (t : Option Name) (n : Name) :
    resolveCol { base with frames := { srcs, cur := c1, aliases := al } :: fs, group := none } t n =
    resolveCol { base with frames := { srcs, cur := c2, aliases := al } :: fs, group := none } t n := by
  unfold resolveCol
  simp only [resolveCol.go]

theorem colMetaOf_cur (base : Env) (srcs : Array Src) (c1 c2 : Array Cur) (al : List (Name × Expr))
    (fs : List Scope) (r : Resolved) :
    colMetaOf { base with frames := { srcs, cur := c1, aliases := al } :: fs, group := none } r =
    colMetaOf { base with frames := { srcs, cur := c2, aliases := al } :: fs, group := none } r := by
  cases r with
  | col fi si ci => cases fi <;> rfl
  | _ => rfl

/-- The join's scope with two current rows. -/
theorem sameScope_cur (base : Env) (srcs : Array Src) (c1 c2 : Array Cur) (al : List (Name × Expr))
    (fs : List Scope) :
    SameScope { base with frames := { srcs, cur := c1, aliases := al } :: fs, group := none }
      { base with frames := { srcs, cur := c2, aliases := al } :: fs, group := none } :=
  ⟨resolveCol_cur base srcs c1 c2 al fs, colMetaOf_cur base srcs c1 c2 al fs⟩

namespace SameScope

variable {env1 env2 : Env} (h : SameScope env1 env2)
include h

theorem termAff (t : PTerm) : t.aff env1 = t.aff env2 := by
  cases t <;> simp only [PTerm.aff, h.colMeta]

theorem termColl (t : PTerm) : t.coll env1 = t.coll env2 := by
  cases t <;> simp only [PTerm.coll, h.colMeta]

theorem alwaysTF (x : Expr) : Sql.alwaysTF env1 x = Sql.alwaysTF env2 x := by
  unfold Sql.alwaysTF
  split <;> simp only [h.res]

theorem simplifyAndOr (x : Expr) : Sql.simplifyAndOr env1 x = Sql.simplifyAndOr env2 x := by
  fun_induction Sql.simplifyAndOr env1 x <;> simp_all [Sql.simplifyAndOr, andOrPick, h.alwaysTF]

theorem andOrAlt (x : Expr) : Sql.andOrAlt env1 x = Sql.andOrAlt env2 x := by
  unfold Sql.andOrAlt
  simp only [h.simplifyAndOr, h.alwaysTF]

theorem compileTerm (x : Expr) : Sql.compileTerm env1 x = Sql.compileTerm env2 x := by
  unfold Sql.compileTerm
  simp only [h.res]

theorem compileCondK : ∀ k x, Sql.compileCondK env1 k x = Sql.compileCondK env2 k x := by
  intro k
  induction k with
  | zero => intro x; rfl
  | succ k ih =>
    intro x
    have hct : Sql.compileTerm env1 = Sql.compileTerm env2 := funext h.compileTerm
    simp only [Sql.compileCondK, ih, h.andOrAlt, hct, h.termAff, h.termColl]

end SameScope

/-- A row the automatic index skips is one the denotation's check rejects,
    without effect. -/
theorem skipRow_rejects (q : QEnv) (p : JoinPlan) (d : Nat) (cur : Array Cur)
    (hskip : skipRow (p.pconds { q.env with frames := p.scope p.empty :: q.env.frames, group := none }) d cur = true) :
    ∀ s, (Except.ok false, s) ∈ (Den.joinCheck q p cur d).outcomes s := by
  intro s
  have hsame := sameScope_cur q.env p.srcs p.empty cur p.aliases q.env.frames
  unfold skipRow JoinPlan.pconds at hskip
  rw [Array.getElem?_map] at hskip
  have hskip' : skipPrefix cur ((p.orders[d]?.getD []).map
      (compileConj { q.env with frames := p.scope p.empty :: q.env.frames, group := none })) = true := by
    cases h : p.orders[d]? with
    | none => rw [h] at hskip; simp [skipPrefix] at hskip
    | some es => rw [h] at hskip; exact hskip
  rw [Den.joinCheck.eq_def]
  simp only []
  refine (?_ : Ret _ false) s
  refine Ret.bind (loop_prefix cur _ _ ?_ _ hskip') (Ret.pure _)
  intro e c hc
  unfold compileConj at hc
  split at hc
  · contradiction
  · rename_i hagg
    simp only [Bool.not_eq_true] at hagg
    simp only [hagg, Bool.false_eq_true, if_false]
    simp only [JoinPlan.scope] at hc
    rw [hsame.compileCondK] at hc
    refine Ret.bind (ret_condHolds { q with env := { q.env with frames := { srcs := p.srcs, cur, aliases := p.aliases } :: q.env.frames, group := none } }
      { srcs := p.srcs, cur, aliases := p.aliases } rfl syntaxFuel e c hc) ?_
    by_cases hj : c.jump cur false true = true
    · simp only [hj, Bool.not_true, Bool.not_false, if_true]
      exact Ret.pure _
    · simp only [Bool.not_eq_true] at hj
      simp only [hj, Bool.not_false, Bool.not_true, Bool.false_eq_true, if_false]
      exact Ret.pure _

end Sql.Den
