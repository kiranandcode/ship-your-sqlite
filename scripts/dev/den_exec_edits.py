#!/usr/bin/env python3
"""Phase 2.6: the hand edits of Sql/Den/Exec.lean after scripts/dev/denize.py."""
import re, sys
p = sys.argv[1] if len(sys.argv) > 1 else 'Sql/Den/Exec.lean'
s = open(p).read()
def rep(a, b):
    global s
    assert s.count(a) == 1, (s.count(a), a[:80]); s = s.replace(a, b)

s = s.replace('import Sql.Den.Domain', 'import Sql.Den.Resolve', 1)
s = re.sub(r'(?<![.\w«])alias(?![\w»])', '«alias»', s)
rep('''  let cands ← draw fun ch seed => (List.range 100).map fun i => (((ch.rowid (seed + i + 1) % 2 ^ 62 : Nat) : Int) + 1)''',
    '''  let cands ← anyOf fun (l : List Int) => l.length = 100 ∧ ∀ c ∈ l, 1 ≤ c ∧ c ≤ 2 ^ 62''')
s = s.replace('← chooseOrder ', '← permA ')
rep('''  -- json.c's parse cache lives for one statement
  modify fun c => { c with jsonCache := {} }''', '''  -- json.c's parse cache lives for one statement; 'now' is fixed for it
  let clockMs ← anyOf fun (_ : Int) => True
  modify fun c => { c with jsonCache := {}, clockMs }''')
i = s.index('/-- Run a script as the driver does, with the implementation\'s choices `ch`')
j = s.index('end Sql.Den', i)
s = s[:i] + '''/-- ⟦src⟧: the outputs of a script, run as the driver runs it (statement by
    statement, printing rows and errors), each statement's meaning applied to
    the state. The loop is bounded by the script's length (every round but the
    last moves past at least one byte); were the bound reached, the run would
    have no outcome. -/
def runScript (src : ByteArray) : Nd ByteArray := do
  -- the clock before the first statement is never read (each statement picks its own)
  let clockMs ← Nd.any fun (_ : Int) => True
  let st ← forIn (List.range (src.size + 1))
    ({ out := ByteArray.empty, ctx := ({ db := {}, clockMs } : DCtx), toks := tokenize src 0 } : DriverState DCtx)
    fun _ st => driverStep src (fun stmt ctx => (runStmt stmt).run.run ctx) st
  if !st.finished then Nd.any fun _ => False else return st.out

/-- `out` is an output of the script `src` (the denotation). -/
def Derives (src out : ByteArray) : Prop := out ∈ runScript src

''' + s[j:]
open(p, 'w').write(s)
