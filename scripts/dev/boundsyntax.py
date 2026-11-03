#!/usr/bin/env python3
"""Phase 2.5 helper: make pure, equation-style `partial def F : T → R` (or
`partial def F (params) : T → R`) over syntax total, as a worker `F.go` with a
depth bound `k` and a wrapper `F` passing `syntaxFuel`.

    scripts/dev/boundsyntax.py FILE NAME=DEFAULT [NAME=DEFAULT ...]

DEFAULT is the result when the bound is exhausted (never for parsed syntax:
syntaxFuel is far above SQLite's depth limits). All functions named are
treated as one group: calls among them become `G.go k`."""
import re, sys
path = sys.argv[1]
spec = dict(a.split('=', 1) for a in sys.argv[2:])
names = list(spec)
src = open(path).read()
for n in names:
    m = re.search(r'^partial def ' + n + r'\b(.*?):\s*(\S+)\s*→\s*(.+?)\s*$', src, re.M)
    assert m, n
    params, argty, resty = m.group(1).strip(), m.group(2), m.group(3)
    # body: lines after the header until the next top-level item
    start = m.end() + 1
    nxt = re.search(r'^(partial def |def |end$|/--|@\[|mutual$|-- )', src[start:], re.M)
    end = start + (nxt.start() if nxt else len(src) - start)
    body = src[start:end]
    pnames = ' '.join(re.findall(r'\((\w+)\s*:', params))
    new = (f'def {n}.go (k : Nat) {params} (x : {argty}) : {resty} :=\n'
           f'  match k with\n  | 0 => {spec[n]}\n  | k + 1 =>\n  match x with\n' + body)
    wrapper = f'def {n} {params} (x : {argty}) : {resty} := {n}.go syntaxFuel {pnames} x\n'.replace('  ', ' ')
    src = src[:m.start()] + new + '\x00WRAP' + n + '\x00\n' + src[end:]
    spec[n] = (spec[n], wrapper)
# calls inside the workers
for n in names:
    src = re.sub(r'(?<![\w.])' + n + r'(?![\w.\'])', '(' + n + '.go k)', src)
    src = src.replace(f'def ({n}.go k).go (k : Nat)', f'def {n}.go (k : Nat)')
    src = src.replace(f'def ({n}.go k)', f'def {n}')
# wrappers after the group (after the next `end` if in a mutual block, else in place)
for n in names:
    marker = '\x00WRAP' + n + '\x00'
    wrapper = spec[n][1].replace(f'({n}.go k).go', f'{n}.go').replace(f'({n}.go k)', f'{n}')
    i = src.index(marker)
    j = src.find('\nend\n', i)
    k2 = src.find('\nmutual\n', i)
    in_mutual = src.rfind('\nmutual\n', 0, i) > src.rfind('\nend\n', 0, i)
    src = src.replace(marker + '\n', '')
    if in_mutual:
        j = src.find('\nend\n', src.find(n + '.go', 0))
        # place after the end of this mutual block
        endpos = src.find('\nend\n', src.index(f'def {n}.go'))
        src = src[:endpos + 5] + '\n' + wrapper + src[endpos + 5:]
    else:
        pos = src.index(f'def {n}.go')
        nxt = re.search(r'^(partial def |def |end$|/--|@\[|mutual$)', src[pos + 5:], re.M)
        ins = pos + 5 + nxt.start()
        src = src[:ins] + wrapper + '\n' + src[ins:]
# outside the group, calls are to the wrappers
last = max(src.index(f'def {n} ') for n in names if f'def {n} ' in src)
head, tail = src[:last], src[last:]
for n in names:
    tail = tail.replace('(' + n + '.go k)', n)
src = head + tail
open(path, 'w').write(src)
print('bounded:', ', '.join(names))
