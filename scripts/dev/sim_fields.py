#!/usr/bin/env python3
"""Phase 2.6g helper: the fields `name : ∀ args, Sim ch (Sql.name fuel args)
(Den.name args)` of a simulation structure, from the fuel-taking definitions of
an interpreter module's mutual block.

    scripts/dev/sim_fields.py SRC.lean FIRST_FUNCTION"""
import re, sys
src, first = sys.argv[1], sys.argv[2]
s = open(src).read()
i = s.index(f'def {first} (fuel : Nat)')
start = s.rindex('\nmutual\n', 0, i)
end = s.index('\nend\n', i)
blk = s[start:end]
for m in re.finditer(r'^def (\w+) ', blk, re.M):
    name = m.group(1)
    j = m.end()
    depth = 0; k = j
    while True:
        c = blk[k]
        if c in '([{': depth += 1
        elif c in ')]}': depth -= 1
        elif blk.startswith(':=', k) and depth == 0: break
        k += 1
    head = ' '.join(blk[j:k].split())
    # split the header into binders and the result type
    binders = []
    depth = 0; cur = ''; p = 0
    while p < len(head):
        c = head[p]
        if c in '([{':
            if depth == 0: cur = ''
            depth += 1
        if depth > 0: cur += c
        if c in ')]}':
            depth -= 1
            if depth == 0: binders.append(cur)
        if depth == 0 and c == ':':
            res = head[p + 1:].strip(); break
        p += 1
    if '(fuel : Nat)' not in binders: continue
    bs = [b for b in binders if b != '(fuel : Nat)']
    if any(b.startswith('{') for b in bs):
        print(f'  -- {name}: implicit binders, by hand'); continue
    names = []
    decls = []
    for b in bs:
        inner = b[1:-1]
        lhs, ty = inner.split(':', 1)
        ty = ty.split(':=')[0].strip()
        for v in lhs.split():
            names.append(v); decls.append(f'({v} : {ty})')
    res_ty = res.replace('M ', '', 1) if res.startswith('M ') else res
    args = ' '.join(names)
    print(f'  {name} : ∀ {" ".join(decls)}, Sim ch (Sql.{name} fuel {args}) (Den.{name} {args})' if decls else
          f'  {name} : Sim ch (Sql.{name} fuel) Den.{name}')
