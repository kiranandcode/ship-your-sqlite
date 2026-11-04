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
rep('''    let x ← draw fun ch seed =>
      let x : Nat := ch.random seed 0 % 2 ^ 64
      if x ≥ 2 ^ 63 then ((x : Int) - 2 ^ 64 : Int) else (x : Int)
    return .int x''', '''    let x ← anyOf fun (x : Int) => -2 ^ 63 ≤ x ∧ x < 2 ^ 63
    return .int x''')
rep('''    let b ← draw fun ch seed => (⟨(Array.range n.toNat).map fun i => (ch.random seed (i + 1) % 256).toUInt8⟩ : ByteArray)
    return .blob b''', '''    let b ← anyOf fun (b : ByteArray) => b.size = n.toNat
    return .blob b''')
rep('''    kept ← chooseOrder kept''', '''    kept ← permA kept''')
rep('''    out ← chooseOrder out''', '''    out ← permA out''')
open(p, 'w').write(s)

# joinLoops, joinRun, attempt and their monotonicity: Sql/Den/Join.lean
s = open(p).read()
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



# --- the join as a plan (data) and closures over it, run by joinLoops ---
s = open(p).read()
i = s.index('/-- FROM with WHERE: a chain of inner joins is evaluated as nested loops, each')
j = s.index('/-- A FROM clause joined and filtered by WHERE: its sources and rows. -/')
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

''' + s[j:]
# the interpreter's evalFromWhereS (plan, then loops) is joinRun here
s, k = re.subn(r'evalFromWhereS q f where_ (\w+)', r'joinRun (joinPrepare q f where_ \1) (joinRowsAt q) (joinCheck q)', s)
assert k == 2, k
open(p, 'w').write(s)
