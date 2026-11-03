#!/usr/bin/env python3
"""Coverage of the end goal (PHASES.md "Coverage"): all of SQLite.

    scripts/coverage.py          # markdown table

export    functions of sqlite3.c that are definitions of the built Lean program
          (build/gen/Sqlprog, `lake build Sqlprog`) / functions clightgen
          produces for sqlite3.c alone (build/export/Sqlite3.lean; checked to
          contain every function of a gcc -O0 object, see PHASES.md 1.1)
run       differential scripts passing (build/diff, scripts/difftest.sh) /
          scripts in tests/sql and tests/sem
semantics rows of coverage/features.tsv marked `semantics` and `diff` in
          coverage/status.tsv / rows of features.tsv
proof     functions with a proved specification (Proof/**: `theorem spec_<fn>`)
          / functions of sqlite3.c in the export
"""
import glob, os, re, subprocess
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

def defs(paths, kind='Function'):
    names = set()
    for p in paths:
        for m in re.finditer(r"^def f_([\w']+) : " + kind + r" :=", open(p).read(), re.M):
            names.add(m.group(1))
    return names

total = defs(['build/export/Sqlite3.lean'])
built_ok = os.path.exists('.lake/build/lib/lean/Sqlprog.olean')
in_prog = defs(glob.glob('build/gen/Sqlprog/*.lean')) if built_ok else set()
exported = total & in_prog

scripts = sorted(glob.glob('tests/sql/*.sql') + glob.glob('tests/sem/*.sql'))
passed = 0
for s in scripts:
    n = os.path.splitext(os.path.basename(s))[0]
    f = {k: f'build/diff/{n}.{k}' for k in ('gcc', 'ccomp', 'lean')}
    if all(os.path.exists(x) for x in f.values()):
        a, b, c = (open(x, 'rb').read() for x in f.values())
        if a == b == c and os.path.getmtime(f['lean']) >= os.path.getmtime(s):
            passed += 1

feats = [l.split('\t') for l in open('coverage/features.tsv').read().splitlines()[1:]]
status = {}
if os.path.exists('coverage/status.tsv'):
    for l in open('coverage/status.tsv').read().splitlines()[1:]:
        fid, st = l.split('\t')[:2]
        status[fid] = st
sem = sum(1 for f in feats if status.get(f[0]) == 'diff')
by_area = {}
for f in feats:
    a = by_area.setdefault(f[1], [0, 0]); a[1] += 1
    if status.get(f[0]) == 'diff': a[0] += 1

proved = set()
for p in glob.glob('Proof/**/*.lean', recursive=True):
    proved |= set(re.findall(r'^theorem spec_(\w+)', open(p).read(), re.M))
proved &= exported

print('| measure | covered | total |\n|---|---|---|')
print(f'| export (functions of sqlite3.c in the built Lean program) | {len(exported)} | {len(total)} |')
print(f'| run (differential scripts: Lean export = gcc = ccomp) | {passed} | {len(scripts)} |')
print(f'| semantics (features implemented and differentially tested) | {sem} | {len(feats)} |')
for a, (c, t) in sorted(by_area.items()):
    print(f'| &nbsp;&nbsp;{a} | {c} | {t} |')
print(f'| proof (functions with a proved spec) | {len(proved)} | {len(total)} |')
