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
  let mut out := ByteArray.empty
  let mut ctx : DCtx := { db := {} }
  let mut finished := false
  let mut pos := 0
  -- the script is tokenized once; a statement starts at the first token at or
  -- after its byte offset, unless the offset falls inside a token (after the
  -- driver's skip to the next ';'), when the rest is tokenized again from there
  let mut toks := tokenize src 0
  let mut ti := 0
  for _ in [0:src.size + 1] do
    for _ in [ti:toks.size] do
      if toks[ti]!.start < pos then ti := ti + 1 else break
    if ti > 0 && toks[ti - 1]!.stop > pos then
      toks := toks.extract 0 (ti - 1) ++ tokenize src pos
      ti := ti - 1
    match parseNextTok src toks ti with
    | .empty => finished := true; break
    | .error msg tail =>
      out := out ++ renderErr { code := SQLITE_ERROR, msg }
      if tail ≤ pos then
        -- no progress: skip to after the next ';'
        let mut i := pos
        for _ in [pos:src.size] do
          if src[i]! != 59 then i := i + 1 else break
        pos := if i < src.size then i + 1 else src.size
      else pos := tail
    | .ok stmt tail =>
      pos := tail
      match ← (runStmt stmt).run.run ctx with
      | (.ok (.ok rows), ctx') =>
        ctx := ctx'
        for r in rows do out := out ++ renderRow r
      | (.ok (.error e), ctx') | (.error e, ctx') =>
        ctx := ctx'
        for r in e.printed do out := out ++ renderRow r
        out := out ++ renderErr e
        if let some t := e.tail then pos := t
  if !finished then Nd.any fun _ => False else return out

/-- `out` is an output of the script `src` (the denotation). -/
def Derives (src out : ByteArray) : Prop := out ∈ runScript src

''' + s[j:]
open(p, 'w').write(s)
