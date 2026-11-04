#!/usr/bin/env python3
"""Phase 2.6g: split the interpreter's scalarFn (one match over 43 function
names) into a chain of functions of a few cases each, out of the mutual block
(it calls none of its functions), so that each has a simulation proof within
the elaboration budget. random()/randomblob() get a chunk of their own."""
import re
p = 'Sql/Select.lean'
s = open(p).read()
i = s.index('def scalarFn (fuel : Nat) (n : Name)')
doc_i = s.rindex('/--', 0, i)
j = s.index('/-- A window definition with its base window', i)
blk = s[i:j]
lines = blk.split('\n')
mi = next(k for k, l in enumerate(lines) if l.strip() == 'match name with')
pre = lines[:mi]          # header lines (fuel wrapper, lets)
lets = [l for l in pre if l.startswith('      let ')]
cases_lines = lines[mi + 1:]
# split into cases at indentation 6
cases = []
for l in cases_lines:
    if l.startswith('      | '):
        cases.append([l])
    elif cases:
        cases[-1].append(l)
# trailing blank lines
while cases and cases[-1] and cases[-1][-1].strip() == '':
    cases[-1].pop()
default = cases[-1]; body = cases[:-1]
assert default[0].startswith('      | _ =>'), default[0]
def is_random(c): return c[0].startswith('      | "random"') or c[0].startswith('      | "randomblob"')
chunks = []
cur = []
for c in body:
    if is_random(c):
        if cur: chunks.append(cur); cur = []
        chunks.append([c]) if not (chunks and chunks[-1] and is_random(chunks[-1][0])) else chunks[-1].append(c)
        continue
    cur.append(c)
    if len(cur) == 8: chunks.append(cur); cur = []
if cur: chunks.append(cur)
def ded(l): return l[4:] if l.startswith('    ') else l
out = []
N = len(chunks)
# each part falls back to the next: defined last part first
for k in reversed(range(N)):
    ch = chunks[k]
    nm = f'scalarFn{k + 1}'
    nxt = f'scalarFn{k + 2} n vs colls' if k + 1 < N else None
    out.append(f'/-- Scalar functions, part {k + 1} of {N} (`scalarFn`). -/')
    out.append(f'def {nm} (n : Name) (vs : List Value) (colls : List (Option (Coll × Bool))) : M Value := do')
    for l in lets: out.append(ded(l))
    out.append('  match name with')
    for c in ch:
        for l in c: out.append(ded(l))
    if nxt:
        out.append(f'  | _ => {nxt}')
    else:
        for l in default: out.append(ded(l))
    out.append('')
out.append('/-- A scalar function (sqlite3.c\'s func.c and friends), by name. -/')
out.append('def scalarFn (n : Name) (vs : List Value) (colls : List (Option (Coll × Bool))) : M Value :=')
out.append('  scalarFn1 n vs colls')
out.append('')
new_fns = '\n'.join(out)
# remove from the block, insert before the mutual block
s = s[:doc_i] + s[j:]
mut = s.index('\nmutual\n', s.index('def QEnv.noGroup'))
s = s[:mut] + '\n' + new_fns + s[mut:]
s = s.replace('scalarFn fuel ', 'scalarFn ')
open(p, 'w').write(s)
print(N, 'chunks:', [len(c) for c in chunks])
