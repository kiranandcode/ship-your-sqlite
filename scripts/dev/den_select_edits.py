#!/usr/bin/env python3
"""Phase 2.6: the hand edits of Sql/Den/Select.lean after scripts/dev/denize.py
(choices as sets, no fuel, no strategy)."""
import re, sys
p = sys.argv[1] if len(sys.argv) > 1 else 'Sql/Den/Select.lean'
s = open(p).read()
def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:80]); s = s.replace(a, b)
def sub_block(start, end_marker, new):
    global s
    i = s.index(start); j = s.index(end_marker, i)
    s = s[:i] + new + s[j:]

rep('''      match DateTime.scalar? { unixMs := (← get).choices.clockMs } n.toLower vs with''',
    '''      match DateTime.scalar? { unixMs := (← get).clockMs } n.toLower vs with''')
rep('''def condHolds (q : QEnv) (e : Expr) : D Bool :=
  match fuel with
  | 0 => outOfFuel
  | fuel + 1 => do return !(← condJump q e false true)''', '''def condHolds (q : QEnv) (e : Expr) : D Bool := do
  return !(← condJump q e false true)''')
rep('''      -- random(), randomblob(N): SQLite's PRNG; the semantics allows any value
      -- (Phase 2.5 states this as a choice); this executable draws from a counter
      | "random" =>
        if nargs != 0 then wrong
        let c ← get
        let seed := c.db.prng
        set { c with db := { c.db with prng := seed + 1 } }
        let x : Nat := c.choices.random seed 0 % 2 ^ 64
        return .int (if x ≥ 2 ^ 63 then (x : Int) - 2 ^ 64 else x)''', '''      -- random(), randomblob(N): SQLite's PRNG, any value
      | "random" =>
        if nargs != 0 then wrong
        let x ← anyOf fun (x : Int) => -2 ^ 63 ≤ x ∧ x < 2 ^ 63
        return .int x''')
rep('''        let c ← get
        let seed := c.db.prng
        set { c with db := { c.db with prng := seed + 1 } }
        return .blob ⟨(Array.range n.toNat).map fun i => (c.choices.random seed (i + 1) % 256).toUInt8⟩''', '''        let b ← anyOf fun (b : ByteArray) => b.size = n.toNat
        return .blob b''')
rep('''        kept ← chooseOrder kept''', '''        kept ← permA kept''')
rep('''        out ← chooseOrder out''', '''        out ← permA out''')
open(p, 'w').write(s)

# --- the join: SQLite's nested loops, without strategy ---
s = open(p).read()
rep('''          leafRows := leafRows.push (some (← chooseOrder rs))''',
    '''          leafRows := leafRows.push (some (← permA rs))''')
i = s.index('def evalFromWhereS')
a = s.index('      let srcs := leafSrcs.foldl (· ++ ·) #[]\n', i)
b = s.index('      return (srcs, acc, failure)\n', i) + len('      return (srcs, acc, failure)\n')
s = s[:a] + '''      let srcs := leafSrcs.foldl (· ++ ·) #[]
      let nL := leaves.size
      -- the leaf of each source position, and each leaf's first position
      let leafOf : Array Nat := (leafSrcs.mapIdx fun i ss => Array.replicate ss.size i).foldl (· ++ ·) #[]
      let offsets : Array Nat := (leafSrcs.foldl (fun (acc : Array Nat × Nat) ss => (acc.1.push acc.2, acc.2 + ss.size)) (#[], 0)).1
      let conds := onConds ++ (where_.map conjuncts).getD []
      -- the leaves an expression names (by the sources its names hit)
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
      -- the order of the loops (depth → leaf): any, as the plan picks; a
      -- table-valued function's arguments name earlier leaves, so with one
      -- the order is FROM's
      let hasFn := leafRows.any (·.isNone)
      let nest ← if hasFn then pure (Array.range nL) else permA (Array.range nL)
      let depthOf : Array Nat := Id.run do
        let mut d := Array.replicate nL 0
        for h : i in [0:nest.size] do d := d.set! nest[i] i
        return d
      -- a conjunct is tested at the depth where the last leaf it names is bound
      let byDepth := conds.map fun e => ((leavesOf e).foldl (fun m l => max m depthOf[l]!) 0, e)
      let frameQ (cur : Array Cur) : QEnv :=
        { q with env := { q.env with frames := { srcs, cur, aliases } :: q.env.frames, group := none } }
      -- the conjuncts of depth d on a row, in an order the plan picks; the
      -- first that does not hold rejects the row
      let check (cur : Array Cur) (d : Nat) : D Bool := do
        let order ← perm ((byDepth.filter (·.1 == d)).map (·.2))
        for e in order do
          if hasAgg e then err "misuse of aggregate function"
          if !(← condHolds (frameQ cur) e) then return false
        return true
      let place (cur : Array Cur) (k : Nat) (r : Array Cur) : Array Cur := Id.run do
        let mut c := cur
        for h : j in [0:r.size] do c := c.set! (offsets[k]! + j) r[j]
        return c
      -- the rows of leaf `k` after the partial row `pre`
      let rowsAt (k : Nat) (pre : Array Cur) : D (Array (Array Cur)) := do
        match leafRows[k]! with
        | some rs => return rs
        | none =>
          match leaves[k]! with
          | .tableFn _ n args _ =>
            let qp := { q with env := { q.env with frames := { srcs, cur := pre } :: q.env.frames } }
            let vs ← args.mapM (evalExpr qp)
            let rs ← tableFunction n (vs.zip (← args.mapM (argIsJson qp)))
            return rs.map fun r => #[some r]
          | _ => return #[]
      let (acc, _, failure) ← joinLoops nL nest rowsAt place check (step · srcs ·) 0
        (Array.replicate srcs.size none) init
      return (srcs, acc, failure)
''' + s[b:]
# joinLoops, attempt and their monotonicity: Sql/Den/Join.lean
s = s.replace('import Sql.Den.Domain', 'import Sql.Den.Join', 1)
open(p, 'w').write(s)

# --- recursive CTEs: the queue as a least fixed point ---
s = open(p).read()
i = s.index('def cteRows')
a = s.index('        let mut out : Array (Array Value) := #[]\n        let mut skipped : Int := 0\n', i)
b = s.index('        if !finished && !queue.isEmpty then outOfFuel\n        return (cols, out)\n', i) + len('        if !finished && !queue.isEmpty then outOfFuel\n        return (cols, out)\n')
s = s[:a] + '''        -- the queue, run to empty: a least fixed point (a recursive CTE that
        -- never empties its queue has no outcome)
        let out ← cteLoop q n cols others with_ wrec (recursive.map (·.2)) ob distinctMode limit offset
          queue seen #[] 0
        return (cols, out)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The rows of a recursive CTE `n` from the queue on (setupQueue/the loop of
    multiSelect's recursive case): take the first row (or, with ORDER BY,
    the least), hand it out unless OFFSET skips it or LIMIT is reached, and
    queue the rows the recursive SELECTs give on it (UNION: unless seen). -/
def cteLoop (q : QEnv) (n : Name) (cols : Array ColMeta) (others : List (Name × CteVal))
    (with_ : List Cte) (wrec : Bool) (recursive : List SelectCore) (ob : List OrderTerm)
    (distinctMode : Bool) (limit : Option Int) (offset : Int)
    (queue seen out : Array (Array Value)) (skipped : Int) : D (Array (Array Value)) := do
  if queue.isEmpty then return out
  -- ORDER BY on a recursive CTE makes the queue a priority queue
  let (row, rest') ← if ob.isEmpty then pure (queue[0]!, queue.extract 1 queue.size)
    else do
      let keys ← queue.mapM fun r => ob.toArray.mapM fun (.mk e _ _) =>
        evalExpr { q with env := { q.env with frames := { srcs := #[metaSrc n cols], cur := #[some { rowid := 0, vals := r }] } :: q.env.frames } } e
      let dirs := ob.map fun (.mk _ d nl) => (d, nl)
      let mut best := 0
      for i in List.range queue.size do
        if i > 0 && lexCompare [] dirs keys[i]! keys[best]! == .lt then best := i
      pure (queue[best]!, (queue.extract 0 best) ++ (queue.extract (best + 1) queue.size))
  let mut queue := rest'
  let mut skipped := skipped
  let mut out := out
  if skipped < offset then skipped := skipped + 1
  else
    if let some l := limit then
      if l ≥ 0 && out.size ≥ l.toNat then return out
    out := out.push row
  let ctesRow := (n, CteVal.rows cols #[row]) :: others
  let mut seen := seen
  for c in recursive do
    let (_, rows) ← runSelect { q with ctes := ctesRow } (.mk with_ wrec c [] [] none none)
    for r in rows do
      if distinctMode then
        if seen.any (rowsEq [] r) then continue
        seen := seen.push r
      queue := queue.push r
  cteLoop q n cols others with_ wrec recursive ob distinctMode limit offset queue seen out skipped
''' + s[b:]
# the original partial_fixpoint after cteRows is now after cteLoop

open(p, 'w').write(s)

# --- `alias` is a keyword under Mathlib: quote it ---
s = open(p).read()
s = re.sub(r'(?<![.\w«])alias(?![\w»])', '«alias»', s)
open(p, 'w').write(s)

# --- view columns: the interpreter's deterministic computation (debt: static) ---
s = open(p).read()
i = s.index('/-- The columns of views for `Sql.Pragma`')
j = s.index('partial_fixpoint', i); j = s.index('\n', j) + 1
s = s[:i] + '''/-- The columns of views for `Sql.Pragma`: the interpreter's (deterministic)
    computation on the corresponding state. Debt (PHASES 2.6): it runs the
    view's SELECT with the interpreter's fuel; to be replaced by the static
    column analysis. -/
def viewCols : D Pragma.ViewCols := do
  let c ← get
  let ctx : Ctx := { db := c.db, jsonCache := c.jsonCache }
  return ((Sql.viewCols evalFuel).run.run ctx).1.toOption.getD (fun _ => .error { code := SQLITE_ERROR, msg := "internal: view columns" })
''' + s[j:]
open(p, 'w').write(s)

# --- the join as a plan (data) and closures over it, run by joinLoops ---
s = open(p).read()
i = s.index('/-- FROM with WHERE: a chain of inner joins is evaluated as nested loops, each')
j = s.index('/-- The rows of a named table, view or CTE, with its source description. -/')
s = s[:i] + '''/-- A join prepared for the loops: the leaves of the chain of inner joins
    with their sources and (for tables) rows in scan order, the nesting order,
    each conjunct with its depth, and where each leaf's columns start. -/
def joinPrepare (q : QEnv) (f : FromItem) (where_ : Option Expr) (aliases : List (Name × Expr)) :
    D JoinPlan := do
  let (leavesL, onConds) := innerChain f
  let leaves := leavesL.toArray
  -- a table-valued function's rows depend on earlier leaves (its arguments)
  let mut leafSrcs : Array (Array Src) := #[]
  let mut leafRows : Array (Option (Array (Array Cur))) := #[]
  for lf in leaves do
    match lf with
    | .tableFn _ n _ «alias» =>
      leafSrcs := leafSrcs.push #[← tableFnSrc n «alias»]
      leafRows := leafRows.push none
    | _ =>
      let (ss, rs) ← evalFrom q lf
      leafSrcs := leafSrcs.push ss
      -- the order the plan scans the leaf in
      leafRows := leafRows.push (some (← permA rs))
  let nL := leaves.size
  -- the order of the loops: any, as the plan picks; FROM's with a
  -- table-valued function (its arguments name earlier leaves)
  let nest ← if leafRows.any (·.isNone) then pure (Array.range nL) else permA (Array.range nL)
  return JoinPlan.make leaves leafSrcs leafRows nest (onConds ++ (where_.map conjuncts).getD []) aliases
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The rows of leaf `k` after the partial row `pre`. -/
def joinRowsAt (q : QEnv) (p : JoinPlan) (k : Nat) (pre : Array Cur) : D (Array (Array Cur)) := do
  match p.leafRows[k]! with
  | some rs => return rs
  | none =>
    match p.leaves[k]! with
    | .tableFn _ n args _ =>
      let qp := { q with env := { q.env with frames := { srcs := p.srcs, cur := pre } :: q.env.frames } }
      let vs ← args.mapM (evalExpr qp)
      let rs ← tableFunction n (vs.zip (← args.mapM (argIsJson qp)))
      return rs.map fun r => #[some r]
    | _ => return #[]
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- The conjuncts of depth `d` on a row, in an order the plan picks; the
    first that does not hold rejects the row. -/
def joinCheck (q : QEnv) (p : JoinPlan) (cur : Array Cur) (d : Nat) : D Bool := do
  let qr := { q with env := { q.env with frames := { srcs := p.srcs, cur, aliases := p.aliases } :: q.env.frames, group := none } }
  let order ← perm ((p.byDepth.filter (·.1 == d)).map (·.2))
  for e in order do
    if hasAgg e then err "misuse of aggregate function"
    if !(← condHolds qr e) then return false
  return true
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

/-- A FROM clause joined and filtered by WHERE: its sources and rows. -/
def evalFromWhere (q : QEnv) (f : FromItem) (where_ : Option Expr) (aliases : List (Name × Expr)) :
    D (Array Src × Array (Array Cur)) := do
  let p ← joinPrepare q f where_ aliases
  let (rows, _, failure) ← joinLoops p.leaves.size p.nest (joinRowsAt q p) p.place (joinCheck q p)
    (fun acc cur => pure (acc.push cur, true)) 0 p.empty (#[] : Array (Array Cur))
  if let some e := failure then throw e
  return (p.srcs, rows)
partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity

''' + s[j:]
rep('''          let (srcs, a, failure) ← evalFromWhereS q f where_ aliases0 ({} : StreamAcc) step''',
    '''          let p ← joinPrepare q f where_ aliases0
          let srcs := p.srcs
          let (a, _, failure) ← joinLoops p.leaves.size p.nest (joinRowsAt q p) p.place (joinCheck q p)
            (step · srcs ·) 0 p.empty ({} : StreamAcc)''')
open(p, 'w').write(s)
