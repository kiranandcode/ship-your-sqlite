#!/usr/bin/env python3
"""Random SQL scripts for the semantics differential (sql_run vs driver-gcc).

    experiments/fuzz/gen.py SEED N_QUERIES > script.sql

A random schema (columns of every affinity, collations, constraints), random
rows of every storage class, then queries mixing joins, subqueries, CASE,
casts, LIKE/GLOB, IN, BETWEEN, aggregates with GROUP BY/HAVING, window
functions, compound selects and LIMIT. Every query is ordered by all its
result columns, so row order is fully specified."""
import random, sys

seed, nq = int(sys.argv[1]), int(sys.argv[2])
R = random.Random(seed)
TYPES = ['INTEGER', 'INT', 'TEXT', 'REAL', 'NUMERIC', 'BLOB', '', 'VARCHAR(10)', 'DOUBLE', 'BOOLEAN']
COLLS = ['', '', '', ' COLLATE NOCASE', ' COLLATE RTRIM', ' COLLATE BINARY']

def lit():
    k = R.randrange(10)
    if k == 0: return 'NULL'
    if k == 1: return str(R.randint(-5, 5))
    if k == 2: return str(R.choice([0, 1, -1, 2**31, 2**63 - 2, -2**63, 10**15]))
    if k == 3: return R.choice(['0.5', '-1.25', '1e10', '3.0', '0.1', '-0.0', '1e308', '2.5e-3'])
    if k == 4: return "'" + R.choice(['', 'a', 'A', 'abc', 'ABC ', ' x', '10', '1.5', '1e2', 'é', 'aBc', '-3', '0x10', "it''s"]) + "'"
    if k == 5: return R.choice(["x''", "x'00'", "x'41'", "x'ff00'"])
    if k == 6: return R.choice(['TRUE', 'FALSE'])
    return str(R.randint(-100, 100))

class Schema:
    def __init__(self):
        self.tables = {}

def gen_schema(sc, out):
    for ti in range(R.randint(1, 3)):
        name = f't{ti}'
        cols = []
        defs = []
        for ci in range(R.randint(1, 4)):
            c = f'c{ci}'
            ty = R.choice(TYPES)
            d = f'{c} {ty}{R.choice(COLLS)}'
            if R.random() < 0.1: d += ' NOT NULL DEFAULT 0'
            if R.random() < 0.1: d += ' UNIQUE'
            cols.append(c); defs.append(d)
        if R.random() < 0.3:
            defs[0] = defs[0].replace(defs[0].split()[1], 'INTEGER', 1) + ' PRIMARY KEY' if len(defs[0].split()) > 1 else defs[0] + ' INTEGER PRIMARY KEY'
        out.append(f'CREATE TABLE {name}({", ".join(defs)});')
        sc.tables[name] = cols
        for _ in range(R.randint(0, 8)):
            vals = ', '.join(lit() for _ in cols)
            out.append(f'INSERT OR IGNORE INTO {name} VALUES ({vals});')
        if R.random() < 0.3:
            out.append(f'CREATE INDEX i{ti} ON {name}({R.choice(cols)});')

FUNCS1 = ['abs', 'length', 'lower', 'upper', 'typeof', 'quote', 'hex', 'trim', 'round', 'sign', 'unicode', 'octet_length', 'ltrim', 'zeroblob', 'likely']
FUNCS2 = ['coalesce', 'ifnull', 'nullif', 'instr', 'substr', 'round', 'max', 'min', 'glob', 'like', 'concat', 'iif']
AGGS = ['count', 'sum', 'total', 'avg', 'min', 'max', 'group_concat']

def expr(cols, depth=0, agg=False):
    if depth > 3 or R.random() < 0.3:
        if cols and R.random() < 0.6: return R.choice(cols)
        return lit()
    k = R.randrange(16)
    e = lambda: expr(cols, depth + 1, agg)
    if k == 0: return f'({e()} {R.choice(["+", "-", "*", "/", "%"])} {e()})'
    if k == 1: return f'({e()} {R.choice(["=", "==", "!=", "<>", "<", "<=", ">", ">=", "IS", "IS NOT"])} {e()})'
    if k == 2: return f'({e()} {R.choice(["AND", "OR"])} {e()})'
    if k == 3: return f'(NOT {e()})'
    if k == 4: return f'({e()} || {e()})'
    if k == 5: return f'{R.choice(FUNCS1)}({e()})'
    if k == 6: return f'{R.choice(FUNCS2)}({e()}, {e()})'
    if k == 7: return f'CAST({e()} AS {R.choice(["INTEGER", "TEXT", "REAL", "NUMERIC", "BLOB"])})'
    if k == 8: return f'CASE {e()} WHEN {e()} THEN {e()} ELSE {e()} END'
    if k == 9: return f'CASE WHEN {e()} THEN {e()} END'
    if k == 10: return f'({e()} {R.choice(["", "NOT "])}BETWEEN {e()} AND {e()})'
    if k == 11: return f'({e()} {R.choice(["", "NOT "])}IN ({e()}, {e()}, {e()}))'
    if k == 12: return f"({e()} {R.choice(['LIKE', 'GLOB', 'NOT LIKE'])} {R.choice(['%a%', 'a_c', '*b*', '1%', '%', ''])!r})".replace('"', "'")
    if k == 13: return f'({e()} IS {R.choice(["", "NOT "])}NULL)'
    if k == 14: return f'({e()} {R.choice(["&", "|", "<<", ">>"])} {e()})'
    if k == 15: return f'{R.choice(["-", "+", "~"])}{e()}'
    return lit()

def query(sc):
    t1 = R.choice(list(sc.tables))
    srcs = [(t1, 'a')]
    from_ = f'{t1} a'
    if R.random() < 0.4 and len(sc.tables) > 0:
        t2 = R.choice(list(sc.tables))
        j = R.choice(['JOIN', 'LEFT JOIN', 'CROSS JOIN', ','])
        cols1 = [f'a.{c}' for c in sc.tables[t1]]
        cols2 = [f'b.{c}' for c in sc.tables[t2]]
        on = f' ON {expr(cols1 + cols2, 2)}' if j in ('JOIN', 'LEFT JOIN') else ''
        from_ += f' {j} {t2} b{on}'
        srcs.append((t2, 'b'))
    cols = [f'{al}.{c}' for t, al in srcs for c in sc.tables[t]]
    kind = R.randrange(5)
    if kind == 0:  # aggregate
        g = R.choice(cols)
        ag = R.choice(AGGS); x = R.choice(cols)
        # group_concat's input order is the plan's: make it specified
        a = f'group_concat({x} ORDER BY quote({x}))' if ag == 'group_concat' else f'{ag}({R.choice(["", "DISTINCT "])}{x})'
        having = f' HAVING {expr(cols, 2)}' if R.random() < 0.3 else ''
        return f'SELECT {g}, {a}, count(*) FROM {from_} GROUP BY {g}{having} ORDER BY 1, 2, 3;'
    if kind == 1:  # window
        w = R.choice(['row_number()', 'rank()', 'dense_rank()', f'sum({R.choice(cols)})', f'count({R.choice(cols)})', f'lag({R.choice(cols)})'])
        c = R.choice(cols)
        return f'SELECT {c}, {w} OVER (ORDER BY {c}, rowid) FROM {t1} a ORDER BY 1, 2;' if len(srcs) == 1 else f'SELECT {c} FROM {from_} ORDER BY 1;'
    if kind == 2:  # compound
        c1 = expr(cols, 1); c2 = expr([f'a.{c}' for c in sc.tables[t1]], 1)
        return f'SELECT {c1} FROM {from_} {R.choice(["UNION", "UNION ALL", "INTERSECT", "EXCEPT"])} SELECT {c2} FROM {t1} a ORDER BY 1;'
    if kind == 3:  # subquery
        t2 = R.choice(list(sc.tables))
        sub = f'(SELECT {R.choice(["max", "min", "count"])}(x.{R.choice(sc.tables[t2])}) FROM {t2} x WHERE {expr([f"x.{c}" for c in sc.tables[t2]] + cols, 2)})'
        return f'SELECT {expr(cols, 1)}, {sub} FROM {from_} ORDER BY 1, 2;'
    es = [expr(cols) for _ in range(R.randint(1, 3))]
    where = f' WHERE {expr(cols)}' if R.random() < 0.6 else ''
    order = ', '.join(str(i + 1) for i in range(len(es)))
    lim = f' LIMIT {R.randint(0, 5)}' if R.random() < 0.2 else ''
    dist = 'DISTINCT ' if R.random() < 0.2 else ''
    return f'SELECT {dist}{", ".join(es)} FROM {from_}{where} ORDER BY {order}{lim};'

def dml(sc):
    t = R.choice(list(sc.tables)); cols = sc.tables[t]
    k = R.randrange(3)
    if k == 0:
        oc = R.choice(['', 'OR IGNORE ', 'OR REPLACE ', 'OR FAIL ', 'OR ABORT '])
        rows = ', '.join('(' + ', '.join(expr([], 2) for _ in cols) + ')' for _ in range(R.randint(1, 3)))
        st = f'INSERT {oc}INTO {t} VALUES {rows};'
    elif k == 1:
        sets = ', '.join(f'{c} = {expr(cols, 2)}' for c in R.sample(cols, R.randint(1, len(cols))))
        st = f'UPDATE {R.choice(["", "OR IGNORE ", "OR REPLACE "])}{t} SET {sets} WHERE {expr(cols, 1)};'
    else:
        st = f'DELETE FROM {t} WHERE {expr(cols, 1)};'
    order = ', '.join(str(i + 1) for i in range(len(cols) + 1))
    return st + f'\nSELECT rowid, {", ".join(cols)} FROM {t} ORDER BY {order};\nSELECT changes();'

dmlmode = len(sys.argv) > 3 and sys.argv[3] == 'dml'
out = []
sc = Schema()
gen_schema(sc, out)
for _ in range(nq):
    out.append(dml(sc) if dmlmode and R.random() < 0.5 else query(sc))
print('\n'.join(out))
