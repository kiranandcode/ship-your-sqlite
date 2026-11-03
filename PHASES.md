# PHASES: plan, ledger, obstructions

**End goal: all of SQLite.** The whole `sqlite3.c` (D1, default build) exported
to Lean Clight; a semantics of the whole SQL dialect SQLite implements; one
refinement theorem about the whole program (`SqliteRefines_Statement`,
BRIEF.md). Phase P only stands the pipeline up. Anything reduced along the way
is a row in **Gaps**, and stays there until it is closed.

## Coverage (the numbers that measure progress)

`scripts/coverage.py` (to be written in phase 1) prints three tables:

| measure | numerator | denominator | today |
|---|---|---|---|
| export | functions of `sqlite3.c` in the elaborated Lean program | functions defined in `sqlite3.c` (from clightgen's output of the full file) | 0 / ? |
| run | differential scripts on which Clean's interpreter on the export matches the native binary | scripts in the corpus | 0 / 0 |
| semantics | SQL features (rows of `coverage/features.tsv`) the semantics implements and that pass the differential | rows of `features.tsv` | 0 / ? |
| proof | functions of `sqlite3.c` with a proved spec used by the refinement | functions in the export | 0 / ? |

`coverage/features.tsv` lists every statement of SQLite's grammar
(lang.html), every expression form, every built-in function
(`pragma_function_list`: 185 names in the default build with math functions),
every pragma (`pragma_pragma_list`: 66), the collations, the virtual tables in
`sqlite3.c` (`pragma_module_list`, `json_each`/`json_tree`, `sqlite_dbpage`,
…), and the type-affinity and NULL rules, one row each. It is generated from
the oracle where SQLite can enumerate itself, and from the documentation
otherwise.

## Phase P: pilot (stand up the pipeline)

| step | exit criterion | status |
|---|---|---|
| P.1 build clean | `ccomp`, `clightgen` for x86_64-linux in `build/clean/install` (`scripts/build_clean.sh`) | running |
| P.2 Lean side | root Lake project on 4.32.1 requiring CCLib (D4); `lake build` builds CCLib + our runner | |
| P.3 tiny program | `c/pilot/hello.c` (arithmetic, structs, a loop, a call through a pointer, output through `putchar`/`write`): clightgen → Lean → our runner prints the same bytes as `gcc` | |
| P.4 externals | runner executes external calls with `Run/Ext.lean` (D5): `write`, `malloc`/`free`/`realloc`, `mem*`/`str*` | |
| P.5 minimal SQLite | clightgen on `sqlite3.c` (default flags); every rejection recorded below. If needed, a temporary reduced build (`SQLITE_OMIT_*`) to get *something* through, recorded under Gaps | |

## Phase 1: the whole of `sqlite3.c` through clightgen and the interpreter

| step | exit criterion | status |
|---|---|---|
| 1.1 export | `clightgen -lean` accepts the full amalgamation with the D7 flags; workarounds keep functionality (compiler flags such as `-fstruct-passing`, `-funstructured-switch`, `-fbitfields`; source-preserving preprocessing; patches to *clightgen*, not to SQLite, where possible) | |
| 1.2 elaborate | the generated Lean elaborates within the default heartbeat budget: split into chunks by the generator (one module per group of functions), never by raising limits | |
| 1.3 driver | `c/driver.c`: reads a script, runs each statement, prints rows (`|`-separated, SQLite's text rendering), errors, and changes; same binary semantics natively and in Clight | |
| 1.4 run | Clean's interpreter runs the export on small scripts and matches the native driver byte for byte; step counts and wall time recorded | |
| 1.5 externals complete | every external symbol of the export has a model in `Run/Ext.lean` or is shown unreachable for `:memory:` databases; the file VFS (`os_unix.c` part) runs against an in-memory file system model | |

## Phase 2: the SQL semantics

Written against `sqlite3` as the criterion, tested before anything is proved.
The semantics is a Lean definition `Sql.Derives` with an executable `Sql.run`
proved equal to it.

| step | exit criterion | status |
|---|---|---|
| 2.1 values | storage classes, affinity, comparison and collation, NULL and three-valued logic, numeric conversions and SQLite's text rendering of REAL | |
| 2.2 core | CREATE TABLE, INSERT, SELECT with WHERE / ORDER BY / GROUP BY / aggregates, LIMIT/OFFSET (the pilot slice) | |
| 2.3 the rest of the dialect | joins (all kinds), subqueries, compound selects, CTEs incl. recursive, window functions, views, triggers, indexes (as observable through ordering and constraints), constraints and ON CONFLICT, UPSERT, RETURNING, transactions/savepoints, ALTER TABLE, pragmas that affect results, the built-in function library, JSON, date/time | |
| 2.4 differential | `scripts/difftest.sh`: `Sql.run` vs the native driver on sqllogictest, SQLite's pure-SQL tests and generated scripts; every disagreement classified | |

## Phase 3: refinement

Decomposition (to be tested by a pilot before it is adopted): SQLite compiles
SQL to VDBE bytecode and runs it over a B-tree. Three layers, one theorem:

1. **storage**: `btree.c`/`pager.c`/`pcache*.c`/the VFS over the external
   model refine an abstract map of tables and indexes;
2. **VM**: `sqlite3VdbeExec` and the `vdbe*.c` helpers refine a VDBE semantics
   over that abstract store;
3. **compiler**: the parser and code generator (`parse.y`, `select.c`,
   `where*.c`, `expr.c`, `insert.c`, …) produce, for each statement, a VDBE
   program whose VDBE semantics is the SQL semantics of the statement.

| step | exit criterion | status |
|---|---|---|
| 3.1 statement | `SqliteRefines_Statement` stated in Lean, with `Admissible` as a named-field structure; external model as a parameter (D6) | |
| 3.2 pilot proof | one end-to-end instance on a fixed small script, to measure the per-function cost | |
| 3.3 coverage | the proof column of the coverage table reaches all functions | |

## Obligations (`def …_Statement : Prop`)

| name | file | statement | status |
|---|---|---|---|
| `SqliteRefines_Statement` | (3.1) | BRIEF.md | not stated |

## Gaps (reductions to close)

| gap | introduced in | why | how it closes |
|---|---|---|---|

## Obstructions (machine-checked evidence, not workarounds)

| id | what | evidence | consequence |
|---|---|---|---|

## Clightgen rejections log (P.5 / 1.1)

| construct | where in `sqlite3.c` | clightgen message | workaround | keeps functionality? |
|---|---|---|---|---|
