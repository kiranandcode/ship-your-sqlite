#!/usr/bin/env python3
"""Write coverage/status.tsv: a feature of coverage/features.tsv is `diff` when
a differential test the semantics passes (scripts/difftest_sem.sh results in
build/diffsem, sqllogictest sections in build/slt/out) exercises it, by the
pattern below; otherwise `open`. Functions: a call `name(`; pragmas:
`pragma name`; others: a regular expression per feature.

    scripts/gen_status.py"""
import glob, os, re
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)

PAT = {
 'ALTER TABLE RENAME': r'alter\s+table\s+\w+\s+rename\s+to', 'ALTER TABLE RENAME COLUMN': r'rename\s+column',
 'ALTER TABLE ADD COLUMN': r'add\s+column', 'ALTER TABLE DROP COLUMN': r'drop\s+column',
 'ANALYZE': r'^\s*analyze', 'ATTACH': r'^\s*attach', 'DETACH': r'^\s*detach', 'BEGIN': r'\bbegin\b\s*;',
 'COMMIT': r'\bcommit\b', 'END': r'\bend\s*;', 'ROLLBACK': r'\brollback\s*;', 'SAVEPOINT': r'\bsavepoint\b',
 'RELEASE': r'\brelease\b', 'ROLLBACK TO': r'rollback\s+to', 'CREATE TABLE': r'create\s+table',
 'CREATE TABLE AS SELECT': r'create\s+table\s+\w+\s+as\s+select', 'CREATE TEMP TABLE': r'create\s+temp(orary)?\s+table',
 'CREATE INDEX': r'create\s+index', 'CREATE UNIQUE INDEX': r'create\s+unique\s+index',
 'CREATE INDEX partial': r'create\s+(unique\s+)?index[^;]*\bwhere\b', 'CREATE INDEX on expressions': r'create\s+index\s+\w+\s+on\s+\w+\s*\([^;]*[(+*|]',
 'CREATE VIEW': r'create\s+(temp\s+)?view', 'CREATE TRIGGER BEFORE': r'create\s+trigger[^;]*\bbefore\b',
 'CREATE TRIGGER AFTER': r'create\s+trigger[^;]*\bafter\b', 'CREATE TRIGGER INSTEAD OF': r'instead\s+of',
 'CREATE TRIGGER FOR EACH ROW WHEN': r'create\s+trigger[^;]*\bwhen\b', 'CREATE VIRTUAL TABLE': r'create\s+virtual',
 'DELETE': r'\bdelete\s+from', 'DROP INDEX': r'drop\s+index', 'DROP TABLE': r'drop\s+table', 'DROP TRIGGER': r'drop\s+trigger',
 'DROP VIEW': r'drop\s+view', 'EXPLAIN': r'^\s*explain\s+(?!query)', 'EXPLAIN QUERY PLAN': r'explain\s+query\s+plan',
 'INSERT VALUES': r'insert\s+into[^;]*values', 'INSERT SELECT': r'insert\s+into\s+\w+(\([^)]*\))?\s+select',
 'INSERT DEFAULT VALUES': r'default\s+values', 'INSERT OR REPLACE': r'insert\s+or\s+replace', 'INSERT OR IGNORE': r'or\s+ignore',
 'INSERT OR ABORT': r'or\s+abort', 'INSERT OR FAIL': r'or\s+fail', 'INSERT OR ROLLBACK': r'or\s+rollback',
 'REPLACE': r'^\s*replace\s+into', 'UPSERT DO NOTHING': r'do\s+nothing', 'UPSERT DO UPDATE': r'do\s+update', 'RETURNING': r'\breturning\b',
 'PRAGMA': r'\bpragma\b', 'REINDEX': r'\breindex\b', 'SELECT': r'\bselect\b', 'UPDATE': r'\bupdate\s+\w+\s+set',
 'UPDATE FROM': r'update\s+\w+\s+set[^;]*\bfrom\b', 'UPDATE LIMIT': r'update[^;]*\blimit\b', 'DELETE LIMIT': r'delete[^;]*\blimit\b',
 'VACUUM': r'\bvacuum\b', 'VACUUM INTO': r'vacuum\s+into', 'WITH': r'\bwith\b', 'WITH RECURSIVE': r'with\s+recursive', 'WITH MATERIALIZED': r'\bmaterialized\b',
 'FROM table': r'\bfrom\s+\w+', 'FROM subquery': r'from\s*\(\s*select', 'FROM table-valued function': r'from\s+(json_each|json_tree|generate_series|pragma_\w+)\s*\(',
 'JOIN INNER': r'\b(inner\s+)?join\b', 'JOIN LEFT': r'left\s+(outer\s+)?join', 'JOIN RIGHT': r'right\s+(outer\s+)?join',
 'JOIN FULL': r'full\s+(outer\s+)?join', 'JOIN CROSS': r'cross\s+join', 'JOIN NATURAL': r'natural\s+join', 'JOIN USING': r'\busing\s*\(',
 'comma join': r'from\s+\w+(\s+\w+)?\s*,\s*\w+', 'WHERE': r'\bwhere\b', 'GROUP BY': r'group\s+by', 'HAVING': r'\bhaving\b',
 'aggregate without GROUP BY': r'select\s+(count|sum|avg|min|max)\(', 'bare columns in aggregate': r'select\s+\w+\s*,\s*max\(|select\s+max\(\w+\)\s*,\s*\w',
 'ORDER BY': r'order\s+by', 'ORDER BY COLLATE': r'order\s+by[^;]*collate', 'NULLS FIRST/LAST': r'nulls\s+(first|last)',
 'LIMIT': r'\blimit\b', 'OFFSET': r'\boffset\b', 'DISTINCT': r'\bdistinct\b', 'ALL': r'union\s+all|select\s+all', 'UNION': r'\bunion\b',
 'UNION ALL': r'union\s+all', 'INTERSECT': r'\bintersect\b', 'EXCEPT': r'\bexcept\b', 'VALUES clause': r'^\s*values|\(\s*values',
 'WINDOW clause': r'\bwindow\s+\w+\s+as', 'OVER partition': r'partition\s+by', 'OVER order': r'over\s*\(\s*order', 'frame ROWS': r'\brows\s+between',
 'frame RANGE': r'\brange\s+between', 'frame GROUPS': r'\bgroups\s+between', 'frame EXCLUDE': r'\bexclude\b', 'FILTER clause': r'filter\s*\(\s*where',
 'aggregate ORDER BY': r'\w\s*\([^()]*\border\s+by[^()]*\)', 'INDEXED BY': r'indexed\s+by', 'NOT INDEXED': r'not\s+indexed', 'AS alias': r'\bas\s+\w+',
 'literal integer': r'\b\d+\b', 'literal real': r'\d\.\d|\de\d', 'literal hex integer': r'0x[0-9a-f]', 'literal string': r"'", 'literal blob': r"x'",
 'NULL': r'\bnull\b', 'TRUE/FALSE': r'\b(true|false)\b', 'bound parameter': r'\?\d*|:\w+', 'column reference': r'select\s+[a-z_]\w*\s+from',
 'unary -': r'[(,=\s]-\w', 'unary +': r'[(,=\s]\+\w', '~': r'~', 'NOT': r'\bnot\b', 'concat operator': r'\|\|', '* / %': r'\*|/|%', '+ -': r'\+',
 '<< >> &': r'<<|>>|[^&]&[^&]', 'bitwise or': r'[^|]\|[^|]', '< <= > >=': r'<=|>=', '= == != <>': r'!=|<>', 'IS': r'\bis\b', 'IS NOT': r'is\s+not', 'IS DISTINCT FROM': r'is\s+(not\s+)?distinct\s+from',
 'IN list': r'\bin\s*\(\s*[^s(]', 'IN subquery': r'\bin\s*\(\s*select', 'NOT IN': r'not\s+in', 'BETWEEN': r'\bbetween\b', 'LIKE': r'\blike\b',
 'LIKE ESCAPE': r'\bescape\b', 'GLOB': r'\bglob\b', 'REGEXP': r'\bregexp\b', 'MATCH': r'\bmatch\b', 'AND': r'\band\b', 'OR': r'\bor\b',
 'CASE simple': r'case\s+\w+\s+when', 'CASE searched': r'case\s+when', 'CAST': r'\bcast\s*\(', 'COLLATE': r'\bcollate\b', 'EXISTS': r'\bexists\s*\(',
 'scalar subquery': r'\(\s*select', 'correlated subquery': r'\(\s*select[^)]*\bwhere\b[^)]*\w+\.\w+', 'row value': r'\(\s*\w+\s*,\s*\w+\s*\)\s*(=|<|>)',
 '-> ->>': r'->', 'function call': r'\w\(', 'DISTINCT aggregate': r'\w\(\s*distinct', 'RAISE': r'\braise\s*\(', 'ISNULL/NOTNULL': r'\b(isnull|notnull)\b',
}
SEM = {  # value-rule features: the test files that exercise them
 'storage classes': 'typeof(', 'type affinity of columns': 'create table', 'affinity of expressions': 'cast(', 'comparison affinity rules': '=',
 'collating sequence BINARY': 'collate binary', 'collating sequence NOCASE': 'nocase', 'collating sequence RTRIM': 'rtrim',
 'three-valued logic': 'null and', 'NULL in aggregates': 'count(', 'NULL in DISTINCT/GROUP BY': 'distinct', 'integer overflow to REAL': '9223372036854775807',
 'division by zero is NULL': '/0', 'text to number conversion': "'10' +", 'REAL to text rendering': '.5', 'rowid tables': 'rowid',
 'INTEGER PRIMARY KEY alias': 'integer primary key', 'AUTOINCREMENT': 'autoincrement', 'WITHOUT ROWID': 'without rowid', 'STRICT tables': 'strict',
 'generated columns VIRTUAL': 'generated always', 'generated columns STORED': 'stored', 'NOT NULL constraint': 'not null', 'UNIQUE constraint': 'unique',
 'CHECK constraint': 'check', 'PRIMARY KEY constraint': 'primary key', 'FOREIGN KEY constraint': 'references', 'ON DELETE/UPDATE actions': 'on delete',
 'DEFAULT values': 'default', 'ON CONFLICT resolution': 'or replace', 'deferred constraints': 'deferrable', 'transactions and savepoints': 'savepoint',
 'autocommit': 'begin', 'recursive triggers': 'recursive_triggers', 'error messages and codes': 'nosuch', 'changes()/last_insert_rowid()': 'changes()',
 'sqlite_schema contents': 'sqlite_schema', 'temporary databases': 'temp table', 'attached databases': 'attach',
}

def passing_texts():
    out = []
    for w in glob.glob('build/diffsem/*.want'):
        g = w[:-5] + '.got'
        n = os.path.basename(w)[:-5]
        src = [p for p in glob.glob(f'tests/*/{n}.sql')]
        if src and os.path.exists(g) and open(w, 'rb').read() == open(g, 'rb').read():
            out.append(open(src[0], encoding='utf-8', errors='replace').read().lower())
    for w in glob.glob('build/slt/out/*.want'):
        g = w[:-5] + '.got'
        if os.path.exists(g) and open(w, 'rb').read() == open(g, 'rb').read():
            out.append(open(w[:-5] + '.sql', encoding='utf-8', errors='replace').read().lower())
    return out

def main():
    texts = passing_texts()
    feats = [l.split('\t') for l in open('coverage/features.tsv').read().splitlines()[1:]]
    rows = ['id\tstatus\tname']
    for fid, area, name, _ in feats:
        if area == 'function':
            pat = r'(?<![\w.])' + re.escape(name.lower()) + r'\s*\(' if name not in ('->', '->>') else re.escape(name)
            # current_date, current_time, current_timestamp are also keywords
            if name.startswith('current_'): pat = r'\b' + name.lower() + r'\b'

        elif area == 'pragma':
            pat = r'pragma\s+(\w+\.)?' + re.escape(name.lower()) + r'\b|pragma_' + re.escape(name.lower())
        elif area == 'module':
            pat = re.escape(name.split()[0].lower()).replace(r'\*', r'\w+') + r'\s*\('
        elif area == 'semantics':
            pat = re.escape(SEM.get(name, '\x00').lower())
        else:
            pat = PAT.get(name)
            if pat is None:
                rows.append(f'{fid}\topen\t{name}'); continue
        hit = any(re.search(pat, t, re.M) for t in texts)
        rows.append(f'{fid}\t{"diff" if hit else "open"}\t{name}')
    open('coverage/status.tsv', 'w').write('\n'.join(rows) + '\n')
    n = sum(1 for r in rows[1:] if '\tdiff\t' in r)
    print(f'{n}/{len(rows) - 1} features exercised by passing differential tests')

if __name__ == '__main__':
    main()
