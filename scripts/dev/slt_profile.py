#!/usr/bin/env python3
"""scripts/dev/slt_profile.py SCRIPT.sql [CHUNK] [LIMIT_S]: time sql_run on growing
prefixes (at statement ends, every CHUNK statements) to find slow statements."""
import subprocess, sys, time, os, re
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
src = open(sys.argv[1]).read()
chunk = int(sys.argv[2]) if len(sys.argv) > 2 else 200
limit = float(sys.argv[3]) if len(sys.argv) > 3 else 60
ends = [m.end() for m in re.finditer(r';[ \t]*\n', src)]
prev = 0.0
for i in range(chunk, len(ends) + chunk, chunk):
    i = min(i, len(ends))
    t = time.time()
    try:
        subprocess.run([os.path.join(ROOT, '.lake/build/bin/sql_run')], input=src[:ends[i-1]].encode(), capture_output=True, timeout=limit)
        d = time.time() - t
    except subprocess.TimeoutExpired:
        print(f'statements {i-chunk}-{i}: timeout ({limit}s)', flush=True); break
    print(f'statements {i-chunk}-{i}: +{d-prev:.2f}s (cumulative {d:.2f}s)', flush=True)
    prev = d
    if i == len(ends): break
