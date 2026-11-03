#!/usr/bin/env python3
"""Phase 2.5 helper: turn the `partial def`s of a mutual block into total
functions recursive on a `fuel : Nat` argument.

    scripts/dev/fuelize.py FILE BLOCK_FIRST_FUNCTION [--calls NAME,NAME,...]

Each `partial def F (params) : T := BODY` of the mutual block that starts with
BLOCK_FIRST_FUNCTION becomes

    def F (fuel : Nat) (params) : T :=
      match fuel with
      | 0 => throw fuelErr
      | fuel + 1 =>
        BODY                      (indented by 4)

and every use of a function of the block (and of the NAMEs given with --calls,
functions of other files that already take fuel) gets `fuel` as its first
argument. Recursion is then structural on fuel."""
import re, sys

path, first = sys.argv[1], sys.argv[2]
extra = []
if '--calls' in sys.argv:
    extra = [x for x in sys.argv[sys.argv.index('--calls') + 1].split(',') if x]
src = open(path).read()
lines = src.split('\n')
# locate the block
start = None
for i, l in enumerate(lines):
    if re.match(r'partial def ' + re.escape(first) + r'\b', l):
        start = i; break
assert start is not None, 'block not found'
m = start
while lines[m].strip() != 'mutual': m -= 1
e = start
while lines[e].strip() != 'end': e += 1
block = lines[m + 1:e]
names = [re.match(r'partial def (\w+)', l).group(1) for l in block if l.startswith('partial def ')]
allnames = names + extra
# split the block into definitions (with their leading doc comments)
defs, cur = [], []
for l in block:
    if (l.startswith('partial def ') or l.startswith('/--')) and cur and not (cur[-1].startswith('/--') or (cur and cur[0].startswith('/--') and not any(x.startswith('partial def') for x in cur))):
        defs.append(cur); cur = []
    cur.append(l)
if cur: defs.append(cur)

def transform(d):
    # d: list of lines: optional doc lines, then `partial def NAME ...` header possibly multi-line ending with `:=` [rest]
    out = []
    i = 0
    while not d[i].startswith('partial def'):
        out.append(d[i]); i += 1
    # header lines until the first ':=' outside brackets
    hdr = []
    depth = 0
    found = None
    while found is None:
        line = d[i]
        j = 0
        while j < len(line):
            c = line[j]
            if c in '([{': depth += 1
            elif c in ')]}': depth -= 1
            elif c == '"':
                j += 1
                while j < len(line) and line[j] != '"':
                    j += 2 if line[j] == '\\' else 1
            elif line.startswith(':=', j) and depth == 0:
                found = j; break
            j += 1
        hdr.append(line)
        if found is None: i += 1
    body = d[i + 1:]
    last = hdr[-1]
    k = found
    head_part, rest = last[:k], last[k + 2:].strip()
    hdr[-1] = head_part + ':='
    hdr[0] = re.sub(r'^partial def (\w+)', r'def \1 (fuel : Nat)', hdr[0])
    out += hdr
    out.append('  match fuel with')
    out.append('  | 0 => throw fuelErr')
    out.append('  | fuel + 1 =>')
    if rest:
        out.append('    ' + rest)
    for b in body:
        out.append(('    ' + b) if b.strip() else b)
    return out

newblock = []
for d in defs:
    if any(l.startswith('partial def') for l in d):
        newblock += transform(d)
    else:
        newblock += d
text = '\n'.join(newblock)
# calls
for n in allnames:
    text = re.sub(r'(?<![\w.\'])(?<!def )' + re.escape(n) + r'(?![\w\'])', n + ' fuel', text)
# undo in headers: `def NAME fuel (fuel : Nat)` -> `def NAME (fuel : Nat)`
for n in names:
    text = text.replace(f'def {n} fuel (fuel : Nat)', f'def {n} (fuel : Nat)')
lines[m + 1:e] = text.split('\n')
open(path, 'w').write('\n'.join(lines))
print(f'{path}: {len(names)} functions fuelized: {", ".join(names)}')
