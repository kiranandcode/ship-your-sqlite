#!/usr/bin/env python3
"""Generate coverage/features.tsv: one row per SQL feature of the D7 build of
SQLite (PHASES.md "Coverage"). Built-in functions, pragmas and table-valued
modules are enumerated by SQLite itself (the native driver, same flags as the
export); statements, clauses, expression forms and value rules are listed
from the SQL documentation (https://sqlite.org/lang.html).

    scripts/gen_features.py            # rewrites coverage/features.tsv
Columns: id, area, name, source."""
import os, subprocess, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DRIVER = os.path.join(ROOT, 'build/native/driver-gcc')

def q(sql):
    out = subprocess.run([DRIVER], input=sql.encode(), capture_output=True, check=True).stdout.decode()
    return [line.strip("'") for line in out.splitlines()]

STATEMENTS = """ALTER TABLE RENAME|ALTER TABLE RENAME COLUMN|ALTER TABLE ADD COLUMN|ALTER TABLE DROP COLUMN|
ANALYZE|ATTACH|DETACH|BEGIN|COMMIT|END|ROLLBACK|SAVEPOINT|RELEASE|ROLLBACK TO|
CREATE TABLE|CREATE TABLE AS SELECT|CREATE TEMP TABLE|CREATE INDEX|CREATE UNIQUE INDEX|CREATE INDEX partial|
CREATE INDEX on expressions|CREATE VIEW|CREATE TRIGGER BEFORE|CREATE TRIGGER AFTER|CREATE TRIGGER INSTEAD OF|
CREATE TRIGGER FOR EACH ROW WHEN|CREATE VIRTUAL TABLE|DELETE|DELETE LIMIT|DROP INDEX|DROP TABLE|DROP TRIGGER|DROP VIEW|
EXPLAIN|EXPLAIN QUERY PLAN|INSERT VALUES|INSERT SELECT|INSERT DEFAULT VALUES|INSERT OR REPLACE|INSERT OR IGNORE|
INSERT OR ABORT|INSERT OR FAIL|INSERT OR ROLLBACK|REPLACE|UPSERT DO NOTHING|UPSERT DO UPDATE|RETURNING|
PRAGMA|REINDEX|SELECT|UPDATE|UPDATE FROM|UPDATE LIMIT|VACUUM|VACUUM INTO|WITH|WITH RECURSIVE|WITH MATERIALIZED"""
CLAUSES = """FROM table|FROM subquery|FROM table-valued function|JOIN INNER|JOIN LEFT|JOIN RIGHT|JOIN FULL|JOIN CROSS|
JOIN NATURAL|JOIN USING|comma join|WHERE|GROUP BY|HAVING|aggregate without GROUP BY|bare columns in aggregate|
ORDER BY|ORDER BY COLLATE|NULLS FIRST/LAST|LIMIT|OFFSET|DISTINCT|ALL|UNION|UNION ALL|INTERSECT|EXCEPT|
VALUES clause|WINDOW clause|OVER partition|OVER order|frame ROWS|frame RANGE|frame GROUPS|frame EXCLUDE|
FILTER clause|aggregate ORDER BY|INDEXED BY|NOT INDEXED|AS alias"""
EXPRS = """literal integer|literal real|literal hex integer|literal string|literal blob|NULL|TRUE/FALSE|
bound parameter|column reference|unary -|unary +|~|NOT|concat operator|* / %|+ -|<< >> &|bitwise or|< <= > >=|= == != <>|
IS|IS NOT|IS DISTINCT FROM|IN list|IN subquery|NOT IN|BETWEEN|LIKE|LIKE ESCAPE|GLOB|REGEXP|MATCH|AND|OR|
CASE simple|CASE searched|CAST|COLLATE|EXISTS|scalar subquery|correlated subquery|row value|-> ->>|
function call|DISTINCT aggregate|RAISE|ISNULL/NOTNULL"""
SEMANTICS = """storage classes|type affinity of columns|affinity of expressions|comparison affinity rules|
collating sequence BINARY|collating sequence NOCASE|collating sequence RTRIM|three-valued logic|NULL in aggregates|
NULL in DISTINCT/GROUP BY|integer overflow to REAL|division by zero is NULL|text to number conversion|
REAL to text rendering|rowid tables|INTEGER PRIMARY KEY alias|AUTOINCREMENT|WITHOUT ROWID|STRICT tables|
generated columns VIRTUAL|generated columns STORED|NOT NULL constraint|UNIQUE constraint|CHECK constraint|
PRIMARY KEY constraint|FOREIGN KEY constraint|ON DELETE/UPDATE actions|DEFAULT values|ON CONFLICT resolution|
deferred constraints|transactions and savepoints|autocommit|recursive triggers|error messages and codes|
changes()/last_insert_rowid()|sqlite_schema contents|temporary databases|attached databases"""

def rows():
    for area, block in (('statement', STATEMENTS), ('clause', CLAUSES), ('expression', EXPRS),
                        ('semantics', SEMANTICS)):
        for name in block.replace('\n', '').split('|'):
            if name.strip():
                yield area, name.strip(), 'lang.html'
    for name in q('select distinct name from pragma_function_list order by name;'):
        yield 'function', name, 'pragma_function_list'
    for name in q('select name from pragma_pragma_list order by name;'):
        yield 'pragma', name, 'pragma_pragma_list'
    # table-valued functions of the default build (pragma_module_list lists
    # only the registered non-eponymous ones; these were checked one by one;
    # generate_series is shell.c's, not sqlite3.c's)
    for name in ('json_each', 'json_tree', 'jsonb_each', 'jsonb_tree', 'pragma_* table-valued functions'):
        yield 'module', name, 'checked on the oracle'

def main():
    out = ['id\tarea\tname\tsource']
    for i, (area, name, src) in enumerate(rows(), 1):
        out.append(f'F{i:04d}\t{area}\t{name}\t{src}')
    os.makedirs(os.path.join(ROOT, 'coverage'), exist_ok=True)
    open(os.path.join(ROOT, 'coverage/features.tsv'), 'w').write('\n'.join(out) + '\n')
    print(f'{len(out) - 1} features')

if __name__ == '__main__':
    main()
