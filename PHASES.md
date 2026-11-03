# PHASES: plan, ledger, obstructions

**End goal: all of SQLite.** The whole `sqlite3.c` (D1, default build) exported
to Lean Clight; a semantics of the whole SQL dialect SQLite implements; one
refinement theorem about the whole program (`SqliteRefines_Statement`,
BRIEF.md). Phase P only stands the pipeline up. Anything reduced along the way
is a row in **Gaps**, and stays there until it is closed.

## Coverage (the numbers that measure progress)

`scripts/coverage.py` prints the table (`scripts/gen_features.py` regenerates the feature list):

| measure | numerator | denominator | 2026-11-03 |
|---|---|---|---|
| export | functions of `sqlite3.c` that are definitions of the built Lean program | functions clightgen produces for `sqlite3.c` (a superset of the 2,638 functions of a gcc -O0 object; the 4 extra are static inline helpers gcc drops) | **2642 / 2642** |
| run | differential scripts on which Clean's interpreter on the export matches the gcc and ccomp builds | scripts in `tests/sql` | **6 / 6** |
| semantics | rows of `coverage/features.tsv` the semantics implements and that pass the differential (`coverage/status.tsv`) | rows of `features.tsv` | 0 / 393 |
| proof | functions of `sqlite3.c` with a proved spec used by the refinement | functions in the export | 0 / 2642 |

`coverage/features.tsv` lists every statement of SQLite's grammar
(lang.html), every expression form, every built-in function
(`pragma_function_list`: 140 names in the D7 build; the 185 of the CLI include shell.c's),
every pragma (`pragma_pragma_list`: 66), the collations, the virtual tables in
`sqlite3.c` (`pragma_module_list`, `json_each`/`json_tree`, `sqlite_dbpage`,
…), and the type-affinity and NULL rules, one row each. It is generated from
the oracle where SQLite can enumerate itself, and from the documentation
otherwise.

## Phase P: pilot (stand up the pipeline)

| step | exit criterion | status |
|---|---|---|
| P.1 build clean | `ccomp`, `clightgen` for x86_64-linux in `build/clean/install` (`scripts/build_clean.sh`) | done (108 s at -j8 with the existing opam switch) |
| P.2 Lean side | root Lake project on 4.32.1 requiring CCLib (D4); `lake build` builds CCLib + our runner | done |
| P.3 tiny program | `c/pilot/hello.c` (arithmetic, structs, a loop, a call through a pointer, output through `putchar`/`write`): clightgen → Lean → our runner prints the same bytes as `gcc` | done: same output and exit code, 892 Clight steps |
| P.4 externals | runner executes external calls with `Run/Ext.lean` (D5): `write`, `malloc`/`free`/`realloc`, `mem*`/`str*` | done; variadic calls too (O1): `c/pilot/vararg{,2}.c` match gcc |
| P.5 minimal SQLite | clightgen on `sqlite3.c` (default flags); every rejection recorded below. If needed, a temporary reduced build (`SQLITE_OMIT_*`) to get *something* through, recorded under Gaps | done without any reduction: the **full** amalgamation goes through (2.5 s, 47 MB of Lean, 2,642 functions); no reduced build was needed |

## Phase 1: the whole of `sqlite3.c` through clightgen and the interpreter

| step | exit criterion | status |
|---|---|---|
| 1.1 export | done (see the log below). `clightgen -lean` accepts the full amalgamation with the D7 flags; workarounds keep functionality (compiler flags such as `-fstruct-passing`, `-funstructured-switch`, `-fbitfields`; source-preserving preprocessing; patches to *clightgen*, not to SQLite, where possible) | |
| 1.2 elaborate | the generated Lean elaborates within the default heartbeat budget: split into chunks by the generator (one module per group of functions), never by raising limits | done: as one file, 4 definitions exceed the default recursion depth (`sqlite3VdbeExec`, `sqlite3Pragma` and `composites` in the code generator, `yy_reduce` in the elaborator; 2 min, 9.7 GB). `scripts/split_export.py` lifts every `Stmt`/`LStmts` subterm of height ≥ 40 into its own definition (193 lifted), chunks the three long lists, and writes 28 modules + Idents + Prog; `--check` re-inlines and compares tokens. `lake build Sqlprog` succeeds with default limits |
| 1.3 driver | `c/driver.c`: reads a script, runs each statement, prints rows (`|`-separated, SQLite's text rendering), errors, and changes; same binary semantics natively and in Clight | done: rows in quote() style (NULL, numbers as SQLite renders them, 'text', X'blob'), `error: <extended code>: <message>`; `c/sqlprog.c` = sqlite3.c + driver.c as one unit |
| 1.4 run | Clean's interpreter runs the export on small scripts and matches the native driver byte for byte; step counts and wall time recorded | `scripts/difftest.sh`: **6 of 6** scripts of `tests/sql/` pass (joins of every kind, subqueries, recursive CTEs, window functions, compound selects, constraints, ON CONFLICT, UPSERT, RETURNING, ALTER TABLE, generated columns, STRICT, WITHOUT ROWID, views, indexes, triggers incl. RAISE, savepoints, foreign keys with cascade, pragmas, the core/date/math/JSON function library, json_each/json_tree, generate_series); 0.86M–5.6M Clight steps per script, 1.5–9.4 s. First script: `tests/sql/basic.sql` (types, NULL logic, aggregates, an error, Unicode, JSON, math) is byte-identical to the gcc and ccomp builds; 860,144 Clight steps, 2,983 external calls, 1.5 s (`sqlite_run`) |
| 1.5 externals complete | every external symbol of the export has a model in `Run/Ext.lean` or is shown unreachable for `:memory:` databases; the file VFS (`os_unix.c` part) runs against an in-memory file system model | |

## Phase 2: the SQL semantics

Written against `sqlite3` as the criterion, tested before anything is proved.
`Sql/`: `Real` (REAL rendering), `Value` (storage classes, affinity, atof/atoi,
comparison, arithmetic), `Lex`/`Keywords` (generated from SQLite's tables),
`Ast`, `Parse`/`ParseStmt` (with `sqlite3_prepare`'s tail positions),
`Db`, `Eval`/`Query`/`Select` (expressions, joins, grouping, windows, CTEs),
`Exec` (statements, constraints, triggers, transactions, ALTER, foreign keys),
and the library lanes `Printf`, `DateTime`, `Json`, `Pragma`. The executable
`sql_run` prints what `c/driver.c` prints.

| step | exit criterion | status |
|---|---|---|
| 2.1 values | storage classes, affinity, comparison and collation, NULL and three-valued logic, numeric conversions and SQLite's text rendering of REAL | done: REAL rendering is SQLite's integer algorithm (0 mismatches on 1.6M doubles); atof as `sqlite3AtoF` |
| 2.2 core | CREATE TABLE, INSERT, SELECT with WHERE / ORDER BY / GROUP BY / aggregates, LIMIT/OFFSET | done |
| 2.3 the rest of the dialect | joins, subqueries, compound selects, CTEs incl. recursive, window functions, views, triggers, indexes, constraints and ON CONFLICT, UPSERT, RETURNING, transactions/savepoints, ALTER TABLE, pragmas, the function library, JSON, date/time | most done (see coverage); lanes: printf **merged** (0 mismatches on 1.8M random calls), date/time, JSON and pragmas running; open: ATTACH, EXPLAIN (see Gaps), VACUUM INTO, virtual tables beyond the built-in table-valued functions |
| 2.4 differential | `scripts/difftest_sem.sh` (tests/sem, tests/sql) and `scripts/difftest_slt.py` (sqllogictest) | tests/sem+tests/sql: 17/20 (the 3 others need date/JSON); sqllogictest: select1 1001/1001, select2 and select3 all agree, evidence/ 330/330 after fixes |
| 2.5 total and relational | make `Sql` total (fuel = SQLite's own limits: recursion depth of triggers, a fuel for recursive CTEs), then define `Sql.Derives` with the unspecified orders and choices (row order without ORDER BY, random(), bare-column rows) as nondeterminism, and prove `Sql.run` sound for it | |

### Phase 2 lanes

Independent libraries, each a sub-agent in its own worktree behind a fixed
interface, merged when its own randomized differential reaches 0 mismatches:
`Sql.Printf` (printf/format/round/quote: merged), `Sql.DateTime`, `Sql.Json`,
`Sql.Pragma`.

### Phase 2 debts

- `partial def` throughout the evaluator (2.5).
- A runtime error in the middle of a streaming SELECT: SQLite has already
  printed the earlier rows; the semantics prints only the error.
- The executable's choices where SQLite's are unspecified (row order without
  ORDER BY, random()) are SQLite's in the cases tested; 2.5 makes them
  nondeterministic choices in `Derives`.

### Phase 2 design notes

- `Sql/Value.lean`: `Value = null | int (i : Int64) | real (r : binary64) | text (UTF-8 bytes) | blob`;
  affinity (`TEXT`, `NUMERIC`, `INTEGER`, `REAL`, `BLOB`) by SQLite's name rules; the
  comparison order (NULL < numbers < text < blob), collations, numeric/text
  conversions. **REAL → text** is not `%.17g`: SQLite renders with `%!.17g`
  through `sqlite3FpDecode` (sqlite3.c 38236): 18 significant digits from
  `sqlite3Fp2Convert10`, rounded to 17, then shortened only when digits 15–16 are
  `99` (round the prefix up) or 14–16 are `000` (or the value is integral) **and**
  the shorter form round-trips. So `0.1` → `0.1` but `0.1+0.7` →
  `0.79999999999999993`, `pi()` → `3.1415926535897931`. The semantics states
  this on exact rationals; whether `sqlite3Fp2Convert10` is correctly rounded
  is a property to test, then prove.
- `Sql/Syntax.lean`, `Sql/Lex.lean`, `Sql/Parse.lean`: the theorem is about
  script *text*, so the semantics parses, including the error outcomes
  (`near "X": syntax error`, `incomplete input`).
- `Sql/Db.lean`: schema (tables, columns with declared type/affinity, constraints,
  indexes as uniqueness and ordering facts, views, triggers) and contents (rowid →
  record); `Sql/Eval.lean`: expressions; `Sql/Select.lean`: the relational core;
  `Sql/Exec.lean`: statements, transactions, the driver's output format.
- `Sql.run (fuel) : script → output` executable; `Sql.Derives` defined from it.
- `scripts/difftest_sem.sh`: `Sql.run` vs `driver-gcc` on `tests/sql` and
  sqllogictest; `coverage/status.tsv` records per feature `diff` when its tests pass.
- Running cost of the Clight export for the larger corpus: 280 MB and ~1 M
  steps/s per `sqlite_run` process, so a sqllogictest file runs in parallel
  processes, not in one.

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
| O2 | CompCert's block memory model gives no meaning to comparing pointers into different blocks with `<`/`<=`/… (and to `==` unless both are valid), nor to comparing a pointer with a nonzero integer: a pointer cast to `uptr` is still a `Vptr`, and `cmplu_bool` returns `none`. SQLite does this on purpose: `sqlite3DbRealloc`, `sqlite3DbFree`, `sqlite3DbMallocSize` (lookaside: `(uptr)p < (uptr)db->lookaside.pEnd`), `SQLITE_WITHIN` in the page cache | `echo "select 1;" \| sqlite_run`: stuck at the `if` of `sqlite3DbRealloc` after 80,640 steps | extension (`Run/Flat.lean`): blocks are placed at `b·2^33 + 2^32`. Where Clean's evaluation fails because a pointer is used as an integer, the pointer is its flat address: comparisons, subtraction across blocks (BUGS.md #1), integer arithmetic on a pointer cast to an integer (`%p` in `sqlite3_str_vappendf`), and byte loads of a stored pointer (BUGS.md #2; an uninitialised byte reads as 0, one choice of C's unspecified value). Applied by rewriting the expressions of the current step and running `doStep` on the result. `select 1;` needs it at 218 of 177,926 steps. Part of D6/D8 |
| O1 | Clight (Rocq CompCert's and Clean's port alike) has no rule for a call that passes variadic arguments: `step_call` evaluates the arguments with `eval_exprlist … tyargs`, one parameter type per argument, so the call is stuck; and `__builtin_va_start`, `__compcert_va_int32/int64/float64` are uninterpreted externals. SQLite has 20 variadic functions (`sqlite3MPrintf`, `sqlite3ErrorMsg`, `sqlite3NestedParse`, `sqlite3VdbeExplain`, …) and they are called on every path that builds an error message or nested SQL | `c/pilot/vararg.c`: gcc exits 42, Clean's interpreter is stuck at the first `Scall` (3 steps) | the runner gives these calls the meaning of CompCert's back ends (`Run/Runner.lean`, "Variadic calls"): variadic arguments stored in a fresh block, 8-byte slots, `va_list` cursor in its first word. `c/pilot/vararg2.c` (va_list passed down, int/long/pointer/double, a call with no variadic argument) matches gcc. For the proofs this is part of our step relation's extension (D6), stated in Lean, not hidden in the runner |

## Clightgen rejections log (P.5 / 1.1)

| construct | where in `sqlite3.c` | clightgen message | workaround | keeps functionality? |
|---|---|---|---|---|
| `PTHREAD_MUTEX_RECURSIVE` undeclared | 31174 (`pthreadMutexAlloc`) | `use of undeclared identifier` | `-D_DEFAULT_SOURCE` (config/sqlite.flags): CompCert preprocesses with `-std=c99`, which turns off glibc's default feature macros that gcc's default `gnu17` has | yes: the same declarations a native gcc build sees |
| struct parameters | 128331, 180938, 183637, 184516–186435 (the JSON and window code) | `function parameter of struct or union type (consider adding option [-fstruct-passing])` | `-fstruct-passing` (`CG_FLAGS` in scripts/env.sh), as ship-your-tcc uses | yes |
| `__atomic_load_n`/`__atomic_store_n` | `AtomicLoad`/`AtomicStore` (15114) | warning only: implicit declaration; would become calls to an unknown external with an `int` prototype | `-D__has_extension(x)=0`: gcc's preprocessor answers `__has_extension(c_atomic)` with 1, which selects the intrinsics. With it SQLite takes its own portable branch, `(*(PTR))` and `(*(PTR) = (VAL))` | yes: relaxed atomic loads/stores of aligned words are plain loads/stores in a sequential semantics. Observable difference: `PRAGMA compile_options` shows `ATOMIC_INTRINSICS=0`; the ccomp oracle has the same |
| `INFINITY` | 37628, 37658 (`sqlite3Fp10Convert2`) | warning: float constant too large | none needed: glibc's non-GNU `INFINITY` is `1e10000f`, which CompCert rounds to +∞ as C requires | yes |
