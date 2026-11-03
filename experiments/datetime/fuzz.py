#!/usr/bin/env python3
"""Randomized differential test of the date/time functions: sql_run (the Lean
semantics) against driver-gcc (SQLite 3.54.1), both run with TZ=UTC.

    TZ=UTC python3 experiments/datetime/fuzz.py [--scripts N] [--per M] [--seed S] [--out DIR]

Every statement is `SELECT <one date expression>;`, so each prints exactly one
line and the outputs compare line by line. Prints the number of expressions
and of mismatches, and the first mismatches. 'now' is used only under typeof()
(the oracle reads the real clock).
"""
import argparse, os, random, subprocess, sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
ORACLE = os.path.join(ROOT, "build/native/driver-gcc")
SEM = os.path.join(ROOT, ".lake/build/bin/sql_run")

def q(s):
    return "'" + s.replace("'", "''") + "'"

def rnum(r, small=False):
    k = r.random()
    if k < 0.3:
        return str(r.randint(-50, 50) if small else r.randint(-100000, 100000))
    if k < 0.55:
        return "%.*f" % (r.randint(0, 6), r.uniform(-1000, 1000) if small else r.uniform(-1e6, 1e6))
    if k < 0.7:
        return r.choice(["0", "-0", "0.5", "-0.5", ".5", "5.", "1e2", "1.5e1", "-2e0", "1e-3", "0.0001",
                         "12", "365", "-366", "1000000", "14712", "14713", "176545", "176546",
                         "5373484", "5373485", "+3", "+0", "1e10", "-1e10", "464269992787967",
                         "7737900007423", "128969998335", "0.999999", "0.0005", "2.5", "-1.25"])
    if k < 0.85:
        return str(r.randint(-3, 3) * 12 + r.randint(-1, 1))
    return "%.3f" % r.uniform(-100, 100)

def rdate(r):
    k = r.random()
    if k < 0.75:
        Y = r.choice([r.randint(1900, 2100), r.randint(0, 9999), r.randint(1, 30),
                      r.choice([0, 1, 4, 100, 400, 1582, 1600, 1700, 1800, 1900, 1969, 1970,
                                2000, 2038, 2100, 2400, 9998, 9999])])
        s = "%04d" % Y
        if r.random() < 0.08: s = "-" + s
        M = r.choice([r.randint(1, 12)] * 8 + [0, 13, r.randint(1, 12)])
        D = r.choice([r.randint(1, 28)] * 5 + [29, 30, 31, 0, 32, r.randint(1, 31)])
        s += "-%02d-%02d" % (M, D)
        if r.random() < 0.02: s = s[:-1]
        if r.random() < 0.65:
            s += r.choice([" ", "T", " ", "T", "  ", " T"]) + rtime(r)
        elif r.random() < 0.05:
            s += r.choice([" ", "x", "T", "Z"])
        return s
    if k < 0.9:
        return rtime(r)
    return r.choice(["", "junk", "2000", "2000-01", "now!", "12", "12:3", "1:30", "2000/01/01",
                     "2451545", "2451545.5", " 2451545 ", "1700000000", "-1", "0", "1e6",
                     "5373484.5", "+2451545", "2451545x", ".5", "5."])

def rtime(r):
    h = r.choice([r.randint(0, 23)] * 6 + [24, 25, 0, 23])
    m = r.choice([r.randint(0, 59)] * 6 + [60, 0])
    s = "%02d:%02d" % (h, m)
    if r.random() < 0.7:
        s += ":%02d" % r.choice([r.randint(0, 59)] * 6 + [60, 0])
        if r.random() < 0.5:
            s += "." + "".join(r.choice("0123456789") for _ in range(r.choice([1, 2, 3, 3, 3, 4, 6, 9, 20])))
            if r.random() < 0.05: s += "9" * 30
    if r.random() < 0.15:
        s += r.choice(["Z", "z", " Z", "+00:00", "-00:00", "+05:30", "-08:00", "+14:00", "-14:59",
                       "+15:00", "+05:60", "+0530", " +01:00", "+01:00 ", "Zx", "+1:00"])
    return s

UNITS = ["day", "days", "hour", "hours", "minute", "minutes", "second", "seconds", "month",
         "months", "year", "years", "DAYS", "Hours", "MONTH", "Years", "s", "fortnight", "dayss",
         "sec"]

def rmod(r):
    k = r.random()
    if k < 0.4:
        n = rnum(r, small=r.random() < 0.7)
        if r.random() < 0.6 and not n.startswith(("-", "+")): n = r.choice(["+", "-", ""]) + n
        sp = r.choice([" "] * 8 + ["", "  "])
        return n + sp + r.choice(UNITS) + r.choice([""] * 15 + [" ", "x"])
    if k < 0.5:
        sign = r.choice(["+", "-", "+", "-", ""])
        s = "%02d:%02d" % (r.randint(0, 25), r.randint(0, 60))
        if r.random() < 0.5: s += ":%02d" % r.randint(0, 59)
        if r.random() < 0.3: s += ".%d" % r.randint(0, 9999)
        if r.random() < 0.05: s = s[1:]
        return sign + s
    if k < 0.6:
        sign = r.choice(["+", "-", "+", "-", ""])
        y = r.choice(["%04d" % r.randint(0, 20), "%04d" % r.randint(0, 9999), "%05d" % r.randint(0, 15000)])
        s = "%s-%02d-%02d" % (y, r.randint(0, 13), r.randint(0, 32))
        if r.random() < 0.3:
            s += " %02d:%02d" % (r.randint(0, 24), r.randint(0, 59))
            if r.random() < 0.5: s += ":%02d.%03d" % (r.randint(0, 59), r.randint(0, 999))
        return sign + s
    if k < 0.7:
        return r.choice(["start of ", "end of ", "Start Of ", "END OF "]) + r.choice(["day", "month", "year", "week", "Day", "MONTH", "x"])
    if k < 0.78:
        return "weekday " + r.choice(["0", "1", "2", "3", "4", "5", "6", "7", "-1", "-3", "-6", "-0", "1.5", "2e0", "3 ", " 4", "x", "-7"])
    return r.choice(["unixepoch", "julianday", "auto", "localtime", "utc", "subsec", "subsecond",
                     "floor", "ceiling", "UNIXEPOCH", "Auto", "LocalTime", "UTC", "", "now", "junk",
                     "5", "+5", "start", "weekday"])

def rarg(r):
    k = r.random()
    if k < 0.65: return q(rdate(r))
    if k < 0.75:
        return r.choice([str(r.randint(0, 5373484)), "%.6f" % r.uniform(0, 5373485),
                         "%.9f" % r.uniform(2440000, 2470000), str(r.randint(-2**40, 2**40)),
                         "%.3f" % r.uniform(-1e11, 3e11), str(r.randint(-10, 10)), "NULL",
                         "1e300", "-0.0", str(r.randint(0, 2**31))])
    if k < 0.85:
        return r.choice([str(r.randint(-210866760000, 253402300799)), str(r.randint(0, 2000000000)),
                         "%.4f" % r.uniform(-2e9, 2e9)])
    return r.choice([q(rdate(r)), str(r.randint(2400000, 2500000)) + ".5"])

SPECS = list("deFfGgHkIljJmMpPRsSTuwUVWY%") + ["C", "D", "h", "y", "q", ""]

def rfmt(r):
    parts = []
    for _ in range(r.randint(0, 6)):
        if r.random() < 0.8: parts.append("%" + r.choice(SPECS[:-6] * 4 + SPECS[-6:]))
        else: parts.append(r.choice([" ", "-", ":", "x", "T", "é", "%%", "|"]))
    return "".join(parts)

def rclean_date(r):
    s = "%04d-%02d-%02d" % (r.choice([r.randint(1900, 2100), r.randint(0, 9999)]), r.randint(1, 12), r.randint(1, 31))
    if r.random() < 0.7:
        s += " %02d:%02d:%02d" % (r.randint(0, 23), r.randint(0, 59), r.randint(0, 59))
        if r.random() < 0.5: s += ".%03d" % r.randint(0, 999)
    return s

def rclean_mod(r):
    k = r.random()
    if k < 0.5:
        n = r.choice([str(r.randint(-400, 400)), "%.3f" % r.uniform(-400, 400), str(r.randint(-100000, 100000))])
        return n + " " + r.choice(["day", "days", "hours", "minutes", "seconds", "months", "years"])
    if k < 0.6:
        return r.choice(["+", "-"]) + "%02d:%02d:%02d.%03d" % (r.randint(0, 23), r.randint(0, 59), r.randint(0, 59), r.randint(0, 999))
    if k < 0.7:
        return r.choice(["+", "-"]) + "%04d-%02d-%02d" % (r.randint(0, 50), r.randint(0, 11), r.randint(0, 30))
    if k < 0.8:
        return r.choice(["start of ", "end of "]) + r.choice(["day", "month", "year"])
    if k < 0.9:
        return "weekday %d" % r.randint(-6, 6)
    return r.choice(["localtime", "utc", "subsec", "floor", "ceiling"])

def rexpr(r):
    if r.random() < 0.5:
        fn = r.choice(["date", "time", "datetime", "julianday", "unixepoch", "strftime", "timediff"])
        if fn == "timediff":
            return "timediff(%s, %s)" % (q(rclean_date(r)), q(rclean_date(r)))
        a0 = r.choice([q(rclean_date(r))] * 6 + ["%.6f" % r.uniform(1e6, 5e6), "%d, 'unixepoch'" % r.randint(-60000000000, 250000000000),
                                              "%.3f, 'unixepoch'" % r.uniform(-6e10, 2.5e11), "%d, 'auto'" % r.randint(-60000000000, 250000000000)])
        args = [a0] + [q(rclean_mod(r)) for _ in range(r.choice([0, 1, 1, 2, 3]))]
        if fn == "strftime": args = [q(rfmt(r))] + args
        return "%s(%s)" % (fn, ", ".join(args))
    fn = r.choice(["date", "time", "datetime", "julianday", "unixepoch", "strftime", "strftime", "timediff", "datetime"])
    if fn == "timediff":
        return "timediff(%s, %s)" % (rarg(r), rarg(r))
    nmod = r.choice([0, 0, 1, 1, 1, 2, 2, 3, 4, 6])
    args = [rarg(r)] + [q(rmod(r)) for _ in range(nmod)]
    now = r.random() < 0.03
    if now: args = []
    if fn == "strftime":
        args = [q(rfmt(r))] + args
    e = "%s(%s)" % (fn, ", ".join(args))
    # 'now' reads the real clock in the oracle: only its type is comparable
    return "typeof(%s)" % e if now else e

def run(binary, script):
    p = subprocess.run([binary], input=script.encode(), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       env=dict(os.environ, TZ="UTC"), timeout=600)
    return p.stdout.decode("utf-8", "replace").split("\n")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--scripts", type=int, default=10)
    ap.add_argument("--per", type=int, default=2000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--show", type=int, default=20)
    args = ap.parse_args()
    total = bad = 0
    shown = 0
    for k in range(args.scripts):
        r = random.Random(args.seed * 1000003 + k)
        exprs = [rexpr(r) for _ in range(args.per)]
        script = "".join("SELECT %s;\n" % e for e in exprs)
        want = run(ORACLE, script)
        got = run(SEM, script)
        if len(want) != len(got):
            print("script %d: line counts differ (%d vs %d)" % (k, len(want), len(got)))
        for i, e in enumerate(exprs):
            w = want[i] if i < len(want) else "<missing>"
            g = got[i] if i < len(got) else "<missing>"
            total += 1
            if w != g:
                bad += 1
                if shown < args.show:
                    shown += 1
                    print("MISMATCH %s\n   sqlite: %s\n   lean:   %s" % (e, w, g))
    print("expressions: %d  mismatches: %d" % (total, bad))
    return 0 if bad == 0 else 1

if __name__ == "__main__":
    sys.exit(main())
