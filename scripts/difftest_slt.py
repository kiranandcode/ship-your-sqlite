#!/usr/bin/env python3
"""Differential test on sqllogictest files: sql_run vs driver-gcc, per query.

    scripts/difftest_slt.py [--timeout S] FILE.test ...

Each file is converted (scripts/slt2sql.py), run on both, and its output split
at the `'Q<n>'` markers; a query whose order is unspecified (rowsort,
valuesort) is compared as a multiset of lines. Prints per-file counts and the
first mismatches; writes build/slt/out/<name>.{sql,order,want,got}."""
import os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, 'build/slt/out')

def split(text):
    secs, cur, key = {}, [], 0
    for l in text.split('\n'):
        if l.startswith("'Q") and l.endswith("'") and l[2:-1].isdigit():
            secs[key] = cur; cur = []; key = int(l[2:-1])
        else:
            cur.append(l)
    secs[key] = cur
    return secs

def main():
    args = sys.argv[1:]
    timeout = 600
    if args and args[0] == '--timeout':
        timeout = int(args[1]); args = args[2:]
    os.makedirs(OUT, exist_ok=True)
    tq = tbad = 0
    for f in args:
        name = os.path.splitext(os.path.basename(f))[0]
        base = os.path.join(OUT, name)
        subprocess.run([sys.executable, os.path.join(ROOT, 'scripts/slt2sql.py'), f, base + '.sql', base + '.order'], check=True)
        script = open(base + '.sql', 'rb').read()
        want = subprocess.run([os.path.join(ROOT, 'build/native/driver-gcc')], input=script, capture_output=True).stdout
        try:
            got = subprocess.run([os.path.join(ROOT, '.lake/build/bin/sql_run')], input=script, capture_output=True, timeout=timeout).stdout
        except subprocess.TimeoutExpired:
            print(f'{name}: TIMEOUT'); continue
        open(base + '.want', 'wb').write(want); open(base + '.got', 'wb').write(got)
        w, g = split(want.decode('utf-8', 'replace')), split(got.decode('utf-8', 'replace'))
        order = dict(l.split('\t') for l in open(base + '.order').read().split('\n') if l)
        bad = []
        for k in w:
            a, b = w[k], g.get(k)
            if b is None: bad.append(k); continue
            if order.get(str(k), 'nosort') != 'nosort':
                a, b = sorted(a), sorted(b)
            if a != b: bad.append(k)
        nq = len(w)
        tq += nq; tbad += len(bad)
        print(f'{name}: {nq - len(bad)}/{nq} sections agree' + (f'; first mismatches: {bad[:5]}' if bad else ''))
    print(f'TOTAL: {tq - tbad}/{tq} sections agree')

if __name__ == '__main__':
    main()
