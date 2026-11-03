#!/usr/bin/env python3
"""For each mismatching fuzz script in build/fuzz, print the first query whose
output differs, with the schema statements and both outputs.
    experiments/fuzz/triage.py [N]"""
import glob, os, subprocess, sys
sys.stdout.reconfigure(line_buffering=True)
os.environ['TZ'] = 'UTC'
n = int(sys.argv[1]) if len(sys.argv) > 1 else 10
D = sys.argv[2] if len(sys.argv) > 2 else 'build/fuzz'
for f in sorted(glob.glob(D + '/s*.sql'))[:n]:
    stmts = [l for l in open(f, encoding='utf-8', errors='replace').read().split('\n') if l]
    setup = [s for s in stmts if not s.startswith('SELECT')]
    qs = [s for s in stmts if s.startswith('SELECT')]
    def run(binp, q):
        try:
            return subprocess.run([binp], input=('\n'.join(setup + [q]) + '\n').encode(), capture_output=True, timeout=30).stdout
        except subprocess.TimeoutExpired:
            return b'TIMEOUT'
    for q in qs:
        a = run('build/native/driver-gcc', q); b = run('.lake/build/bin/sql_run', q)
        if a != b:
            print('==', os.path.basename(f)); print('\n'.join(setup)); print(q)
            print('  want:', a.decode('utf-8', 'replace')[:300].replace('\n', ' / '))
            print('  got: ', b.decode('utf-8', 'replace')[:300].replace('\n', ' / '))
            break
