#!/usr/bin/env python3
"""Systematic sweep of the calendar and of the millisecond rounding: sql_run
against driver-gcc (TZ=UTC) on
  * every 397th day from -4713-11-24 to 9999-12-31 (all strftime fields,
    'localtime', and the month/year arithmetic), and
  * every 13th 10-microsecond fraction of a second (parse, %f, subsec, %J).

    TZ=UTC python3 experiments/datetime/sweep.py
"""
import os, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ORACLE = os.path.join(ROOT, "build/native/driver-gcc")
SEM = os.path.join(ROOT, ".lake/build/bin/sql_run")

def run(binary, script):
    p = subprocess.run([binary], input=script.encode(), stdout=subprocess.PIPE,
                       env=dict(os.environ, TZ="UTC"), timeout=1200)
    return p.stdout.decode("utf-8", "replace").split("\n")

def main():
    stmts = []
    jd = 0.0
    while jd < 5373484.5:
        stmts.append("SELECT strftime('%%F %%T %%j %%U %%V %%W %%G %%g %%u %%w %%J %%s', %r), "
                     "datetime(%r, 'localtime'), date(%r, '+1 month'), date(%r, '-13 months', 'floor'), "
                     "date(%r, '+1 year'), timediff(%r, '2000-02-29 12:00');" % ((jd,) * 6))
        jd += 397.31
    for ms in range(0, 100000, 13):
        f = "%05d" % ms
        stmts.append("SELECT strftime('%%f %%s %%J', '2000-01-01 00:00:%s.%s', 'subsec'), "
                     "datetime('1969-12-31 23:59:%s.%s', 'subsec'), julianday('2000-01-01 00:00:%s.%s'), "
                     "unixepoch('1969-12-31 23:59:%s.%s', 'subsec');"
                     % (f[:2], f[2:] + "1", f[:2], f[2:], f[:2], f[2:] + "49", f[:2], f[2:] + "5"))
    bad = 0
    step = 2000
    for k in range(0, len(stmts), step):
        chunk = stmts[k:k + step]
        script = "\n".join(chunk) + "\n"
        want, got = run(ORACLE, script), run(SEM, script)
        for i, s in enumerate(chunk):
            w = want[i] if i < len(want) else "<missing>"
            g = got[i] if i < len(got) else "<missing>"
            if w != g:
                bad += 1
                if bad <= 20:
                    print("MISMATCH %s\n   sqlite: %s\n   lean:   %s" % (s, w, g))
    print("statements: %d  mismatches: %d" % (len(stmts), bad))
    return 0 if bad == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
