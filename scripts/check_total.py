#!/usr/bin/env python3
"""Gate for Phase 2.5: the semantics must be total. Lists, per file of Sql/,
every `partial def` and every `while`/`repeat` loop (Lean compiles these
through `Loop`, whose `forIn` is a partial definition, so a function that uses
them is opaque to proofs).

    scripts/check_total.py [FILES...]     # exit 1 if anything is found"""
import glob, re, sys, os
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
files = sys.argv[1:] or sorted(glob.glob(os.path.join(ROOT, 'Sql/**/*.lean'), recursive=True))
total = 0
for f in files:
    src = open(f).read()
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    hits = []
    for i, line in enumerate(src.split('\n'), 1):
        code = line.split('--')[0]
        if re.search(r'\bpartial\s+def\b', code): hits.append((i, 'partial def'))
        if re.search(r'(^|\s)(while|repeat)\b', code): hits.append((i, 'loop'))
    if hits:
        total += len(hits)
        rel = os.path.relpath(f, ROOT)
        print(f'{rel}: {sum(1 for h in hits if h[1] == "partial def")} partial, {sum(1 for h in hits if h[1] == "loop")} loops')
print(f'total: {total}')
sys.exit(1 if total else 0)
