#!/usr/bin/env python3
"""cmp.py script.sql want got seed: print each statement whose output differs
(outputs are split at the `'MARK k'` rows that gen.py interleaves)."""
import sys


def split(path):
    blocks = {}
    cur = None
    with open(path, "rb") as f:
        for line in f.read().split(b"\n"):
            if line.startswith(b"'MARK ") and line.endswith(b"'"):
                cur = int(line[6:-1])
                blocks[cur] = []
            elif cur is not None:
                blocks[cur].append(line)
    return blocks


def main():
    script, want, got, seed = sys.argv[1:5]
    stmts = {}
    with open(script, "rb") as f:
        lines = f.read().split(b"\n")
    for i in range(0, len(lines) - 1, 2):
        m = lines[i]
        if m.startswith(b"select 'MARK "):
            stmts[int(m[13:-2])] = lines[i + 1]
    w = split(want)
    g = split(got)
    out = sys.stdout.buffer
    for k in sorted(stmts):
        if w.get(k) != g.get(k):
            out.write(b"### seed %s stmt %d\n" % (seed.encode(), k))
            out.write(stmts[k] + b"\n")
            out.write(b"--- want\n" + b"\n".join(w.get(k, [b"<missing>"])) + b"\n")
            out.write(b"--- got\n" + b"\n".join(g.get(k, [b"<missing>"])) + b"\n")


main()
