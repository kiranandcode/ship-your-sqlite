#!/usr/bin/env python3
"""Convert a sqllogictest .test file into a driver script (scripts/difftest_slt.sh).

    scripts/slt2sql.py FILE.test OUT.sql OUT.order

Keeps the records that apply to SQLite (drops `onlyif <other>` and
`skipif sqlite`). Before each query it emits `select 'Q<n>';`, so the output
can be split per query; OUT.order lists, per query number, whether its row
order is specified ("nosort") or not ("rowsort"/"valuesort"). The expected
results in the .test file are not used: the oracle is the native driver."""
import sys

def records(lines):
    rec = []
    for l in lines:
        if l.strip() == '':
            if rec: yield rec
            rec = []
        elif not l.startswith('#'):
            rec.append(l.rstrip('\n'))
    if rec: yield rec

def main():
    src, out, order = sys.argv[1:4]
    lines = open(src, encoding='utf-8', errors='replace').readlines()
    sql, orders = [], []
    n = 0
    for rec in records(lines):
        skip = False
        while rec and (rec[0].startswith('skipif') or rec[0].startswith('onlyif')):
            w = rec[0].split()
            if w[0] == 'skipif' and w[1] == 'sqlite': skip = True
            if w[0] == 'onlyif' and w[1] != 'sqlite': skip = True
            rec = rec[1:]
        if skip or not rec: continue
        head = rec[0].split()
        if head[0] == 'statement':
            sql.append('\n'.join(rec[1:]) + ';')
        elif head[0] == 'query':
            body = []
            for l in rec[1:]:
                if l.strip() == '----': break
                body.append(l)
            n += 1
            mode = head[2] if len(head) > 2 else 'nosort'
            orders.append(f'{n}\t{mode}')
            sql.append(f"select 'Q{n}';")
            sql.append('\n'.join(body) + ';')
        # hash-threshold, halt, etc. are ignored
    open(out, 'w').write('\n'.join(sql) + '\n')
    open(order, 'w').write('\n'.join(orders) + '\n')

if __name__ == '__main__':
    main()
