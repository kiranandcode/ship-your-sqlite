#!/usr/bin/env python3
"""experiments/fuzz/first_diff.py SCRIPT.sql: the first statement (one per
line) after which sql_run's output differs from driver-gcc's."""
import subprocess, sys, os
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
lines = open(sys.argv[1]).read().split('\n')
def run(exe, n):
    src = '\n'.join(lines[:n]) + '\n'
    return subprocess.run([exe], input=src.encode(), capture_output=True, env=dict(os.environ, TZ='UTC')).stdout
want = lambda n: run(os.path.join(ROOT, 'build/native/driver-gcc'), n)
got = lambda n: run(os.path.join(ROOT, '.lake/build/bin/sql_run'), n)
lo, hi = 0, len(lines)
if want(hi) == got(hi): print('no difference'); sys.exit(0)
while hi - lo > 1:
    mid = (lo + hi) // 2
    if want(mid) == got(mid): lo = mid
    else: hi = mid
print(f'line {hi}: {lines[hi-1]}')
w, g = want(hi).decode(errors='replace').split('\n'), got(hi).decode(errors='replace').split('\n')
print('want tail:', w[-6:]); print('got tail: ', g[-6:])
