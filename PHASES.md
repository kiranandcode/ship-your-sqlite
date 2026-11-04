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
| 1.4b larger corpus | the export on every `tests/sem` script | 13 of 14 core/printf scripts pass; `printf.sql` exceeds the 20-minute budget (printf widths around 10^8, a few seconds natively, far too slow interpreted): a resource limit, not a mismatch |
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
| 2.3 the rest of the dialect | joins, subqueries, compound selects, CTEs incl. recursive, window functions, views, triggers, indexes, constraints and ON CONFLICT, UPSERT, RETURNING, transactions/savepoints, ALTER TABLE, pragmas, the function library, JSON, date/time | done except EXPLAIN / EXPLAIN QUERY PLAN (decision pending) and VACUUM INTO (needs the file system model): 391 of 394 features differentially tested (`scripts/coverage.py`), including ANALYZE (sqlite_stat1), every conflict resolution with ROLLBACK, RAISE kinds, unistr/unistr_quote/subtype |
| 2.4 differential | `scripts/difftest_sem.sh` (tests/sem, tests/sql) and `scripts/difftest_slt.py` (sqllogictest), the random differential `experiments/fuzz/` (`first_diff.py` bisects a script to its first differing statement) | tests/sem+tests/sql: 64/64; sqllogictest: select1–5 and evidence/, all 9,219 queries agree. Fuzz (20 statements per script): queries seeds 5100–5199, 1 differs; DML seeds 7000–7199, 3 differ; all four are unspecified choices (index scan order, random rowid), which `Sql.Derives` covers |
| 2.5 total and relational | make `Sql` total (fuel = SQLite's own limits: recursion depth of triggers, a fuel for recursive CTEs), then define `Sql.Derives` with the unspecified orders and choices (row order without ORDER BY, random(), bare-column rows) as nondeterminism, and prove `Sql.run` sound for it | **`Sql` is total** (gate `scripts/check_total.py`: 263 hits at the start, 0 now; no `partial def`, no `while`/`repeat` anywhere in `Sql/`). Evaluator (Select, Query, Eval, Resolve, Exec, Pragma): the mutual blocks take a `fuel : Nat` decreasing on every call, `0` calls `outOfFuel` (sets `Ctx.exhausted`, throws); `runStmt` takes the fuel, `runScript` passes `evalFuel` (10⁹). It bounds recursion depth (SQLite stops at SQLITE_MAX_EXPR_DEPTH / SQLITE_MAX_TRIGGER_DEPTH = 1000) and the rounds of a recursive CTE (unbounded in SQLite). Pure walks over syntax take `syntaxFuel` (10⁶). Parser: structural fuel `32 · (tokens left + 1)`, never exhausted (each recursive call consumes a token within 16 silent calls; argument in `fuelPerToken`'s doc comment), exhaustion a distinct internal error; SQLite's own parser limits ("Recursion limit", "Expression tree is too large") are not modelled (a gap, below). Lexer, numeric conversion, rendering, JSON, printf, date/time: recursion on the bytes left or json.c's depth limit, loops bounded by the input size (each bound argued in a comment). Behaviour unchanged throughout (60/60 semantic scripts, 5,653/5,653 sqllogictest queries, 999,738 rendered REALs, the JSON/printf/datetime differentials, fuzz). `Sql.Derives` (`Sql/Derives.lean`):`runScriptWith (ch : Choices) (fuel : Nat)` returns the output and whether fuel ran out; `Derives src out` is a named-constructor inductive (some choices and some fuel give `out` without exhaustion); `runScript_derives` (the executable is sound) is proved by construction, axioms `propext`, `Classical.choice`, `Quot.sound` only. Choices modelled: the nesting order of an inner join's loops and the scan order of each of its tables, the order of a SELECT core's joined rows (after WHERE: decides group and DISTINCT representatives and aggregate input order) and of its output rows (row order without ORDER BY, ORDER BY ties), as Lehmer codes; `random()`/`randomblob()` draws; the random rowid's candidates. UPDATE/DELETE row order and the FROM row an UPDATE … FROM uses. **Not yet:** page counts |

### Phase 2 lanes

Independent libraries, each a sub-agent in its own worktree behind a fixed
interface, merged when its own randomized differential reaches 0 mismatches:
`Sql.Printf` (printf/format/round/quote: merged), `Sql.DateTime`, `Sql.Json`,
`Sql.Pragma`.

### Unspecified choices (become nondeterminism in `Sql.Derives`, 2.5)

Where SQLite's output depends on its query plan, not on SQL. The executable
semantics makes SQLite's choice in the simple cases (rowid-order scans); the
relational semantics must allow every choice, and the differential tests
compare modulo these choices:

| choice | example | what SQLite does |
|---|---|---|
| row order without ORDER BY, and the order of ORDER BY ties | `select a from t` | scan order of the chosen plan (rowid, or an index) |
| which of several equal-comparing values represents a group, a DISTINCT or a compound row | `0` vs `0.0`, `'a'` vs `'A'` under NOCASE | the first one in the plan's scan order (with rules for UNION: a later SELECT's row replaces an equal earlier one; tested) |
| input order of an aggregate without ORDER BY | `group_concat(x)` over a join | the plan's loop order |
| `random()`, `randomblob()`, the rowid after 2^63−1 | | SQLite's PRNG (deterministic in the Clight model: fixed clock and pid) |
| `page_count`, `freelist_count` beyond the root pages | | the B-tree's page layout (Sql.Pragma models root pages only) |

The random differential (`experiments/fuzz/`) checks ties as multisets; the
other choices still show up as differences (a bare column read through an
index scan, the random rowid after 2^63−1) and are triaged by hand.

### Phase 2 debts

- A runtime error in the middle of a SELECT: the rows SQLite printed before
  it are modelled for a SELECT without aggregates, windows or ORDER BY and for
  UNION ALL of such (`Err.printed`). Not yet: an ORDER BY the plan satisfies
  through an index (SQLite streams; the semantics sorts), GROUP BY output
  (groups come out one by one after the sorter), UNION/INTERSECT/EXCEPT.
- The executable's choices where SQLite's are unspecified are SQLite's in the
  cases tested; `Derives` quantifies over them (`Choices`), except the page
  layout (2.5).

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

## Phase 2.6: the denotational semantics (Kiran, 2026-11-04)

The specification is a denotational semantics, `Sql/Den/`: meaning functions
from syntax to sets of outcomes, with least fixed points for every recursion,
and no fuel, choice oracle or evaluation strategy. The interpreter (`Sql/`,
`sql_run`) stays as the executable tested against `sqlite3`, and is proved
sound for the denotation: if it finishes, its output is in the denotation.

### Design

- **Domain.** `Nd α := Set α`, the monad of sets of outcomes (`pure a = {a}`,
  `s >>= f = ⋃ a ∈ s, f a`), ordered by inclusion. The meaning monad is the
  interpreter's with `Id` replaced by `Nd`: `D α := ExceptT Err (StateT DCtx Nd) α`,
  so a computation is `DCtx → Set (Except Err α × DCtx)` (the state is kept
  with an error, as SQLite keeps an ON CONFLICT FAIL statement's rows).
  *Why sets, ordered by ⊆ (the Hoare, "may" powerdomain of a discrete set):*
  the refinement theorem says every terminating behaviour of SQLite is a
  denoted outcome, so the denotation is the set of possible terminating
  outcomes; divergence contributes nothing (∅ is ⊥), and the least fixed
  point is the smallest such set, i.e. the strongest theorem (a larger fixed
  point would admit junk outcomes for a non-terminating recursive CTE).
  `Part` is the deterministic special case (at most one outcome) and cannot
  express row order, ties or `random()`.
- **Fixed points.** `Nd` is a complete lattice, hence a CCPO; core Lean lifts
  the CCPO and monotone-bind instances through `ExceptT` and `StateT`, so
  every recursive meaning function (expressions with subqueries, queries,
  CTEs including recursive ones, statements, triggers including recursive
  triggers) is defined with `partial_fixpoint`, i.e. as `Lean.Order.fix`, the
  least fixed point; monotonicity is proved by the `monotonicity` tactic.
  `Sql/Den/Domain.lean` proves that this fixed point is Mathlib's
  `OrderHom.lfp` of the same functional on the complete lattice (Knaster–Tarski),
  so the order theory is Mathlib's.
- **Nondeterminism as sets.** Where SQL leaves the choice to the plan, the
  denotation takes all of them: `perm xs = {ys | ys ~ xs}` (`List.Perm`) for
  scan order, the nesting order of a join, the order of the rows a SELECT
  hands out (ORDER BY then only constrains it: any order sorted by the keys,
  so ties are free), group representatives and aggregate input order;
  `random()`, `randomblob()`, the random rowid after 2^63−1 and the clock
  are any value of their type.
- **No strategy.** FROM is the product of its sources visited in some nested
  order, WHERE a filter; a SELECT hands out rows one by one over that
  sequence (so an error leaves the rows printed before it, and LIMIT ends the
  sequence), which is observable behaviour, not strategy. No automatic
  index, greedy nesting, memoisation or fuel.
- **Shared, deterministic.** Value-level functions stay total functions and
  are used by both: values and conversions, comparison, affinity, collation,
  casts, arithmetic, printf, date/time, JSON, the parser, name resolution,
  schema-text rewriting, PRAGMA computations. Walks over syntax are
  well-founded recursions on the term (`sizeOf`, list elements through
  `List.attach`, `syntax_wf`): `hasAgg`, `hasWindow`, `hasSubquery`, the
  name references (`exprRefs` …), `coreRefers`, `replaceWindows`,
  `simplifyAndOr` (structural), PRAGMA's `dataType`. An alias's expression
  is resolved in its own SELECT's scope without the aliases (as SQLite
  resolves result columns: `Env.aliasScope`), so `exprAff`/`exprColl`
  terminate on (visible aliases, size). Two bounds remain in shared
  functions, each cutting a recursion that is not over syntax (Gaps).
- **Scripts.** `⟦src⟧ : Set ByteArray`: the driver's loop over the statements
  the parser finds, each statement's meaning applied to the state.

### Soundness and precision

- `Sql.Den.sound_Statement`: for all choices, fuel and scripts, if
  `runScriptWith ch fuel src` does not run out of fuel, its output is in
  `⟦src⟧`. By induction on fuel for each of the interpreter's mutual blocks,
  unfolding the denotation with `fix_eq`, plus one lemma per strategy of the
  interpreter (the automatic index visits exactly the matching rows; greedy
  nesting and the choice oracle pick an element of `perm`; memoised local
  conjuncts are evaluated as in the nested loop).
- `Sql.Derives` becomes membership in `⟦src⟧`; the theorem of
  `Spec/Refines.lean` refers to the denotation.
- Precision (later): the converse, every denoted outcome is the interpreter's
  for some choices and fuel, so that the denotation has no outcome beyond the
  plan's choices.

| step | exit criterion | status |
|---|---|---|
| 2.6a Mathlib | pinned to v4.32.1 (the toolchain's tag), oleans from the cache, builds on /data | done (`lakefile.toml`, rev 520045a) |
| 2.6b domain | `Nd`, `D`, their order, CCPO and MonoBind instances, `perm`, `fix = lfp` | done (`Sql/Den/Domain.lean`): plus monotonicity lemmas for `try … catch` and loops over ranges, which core lacks; `Sql/Den/Join.lean`: SQLite's nested loops as `joinLoops`, monotone in the actions of its depths |
| 2.6c expressions | `⟦e⟧` for every expression form, scalar and aggregate functions through the shared library | first version with 2.6d (`Sql/Den/Select.lean`) |
| 2.6d queries | FROM, WHERE, GROUP BY, HAVING, windows, DISTINCT, ORDER BY, LIMIT, compounds, CTEs (recursive as least fixed points), streaming and partial output | first version (`Sql/Den/Select.lean`, 1,689 lines, axioms propext/choice/Quot.sound): derived from the interpreter by `scripts/dev/denize.py` (no fuel, `M` → `D`, every recursive meaning function a `partial_fixpoint`) and `scripts/dev/den_select_edits.py` (choices as sets: scan, nesting and output orders `perm`, `random()`/`randomblob()` any value, the clock a per-statement state; the join as a plan and `joinLoops`, no index, greedy nesting or memo, a depth's conjuncts in any order; a recursive CTE's queue as `cteLoop`, a least fixed point). Debts: `viewCols` (view column metadata for PRAGMA) calls the interpreter; pure syntax walks (`exprRefs`, `hasAgg`, `exprAff`, …) still carry `syntaxFuel` |
| 2.6e statements | DML with conflict resolution, triggers (recursive as least fixed points), foreign keys, DDL, transactions, PRAGMA, ATTACH | first version (`Sql/Den/Resolve.lean`, `Sql/Den/Exec.lean`): UPDATE/DELETE order and UPDATE FROM's row `perm`, the random rowid any 100 candidates in [1, 2^62] (SQLITE_FULL if all taken; the interpreter now does exactly this), the clock any value per statement |
| 2.6f scripts | `⟦src⟧`, `Derives` redefined, `Spec/Refines.lean` updated | done: `Den.runScript : ByteArray → Nd ByteArray` (the driver's loop), `Den.Derives src out := out ∈ runScript src`; `Spec/Refines.lean`'s `sound` field refers to it (CCLib and Mathlib build together) |
| 2.6g soundness | `sound_Statement` proved | **done**: `Sql.Den.sound : sound_Statement` (`Sql/Den/Sound.lean`; axioms `propext`, `Classical.choice`, `Quot.sound`), and `derives` (the choice-oracle relation `Sql.Derives` is contained in the denotation), `runScript_denoted` (the executable's output is denoted when its fuel does not run out). **The simulation** (`Sql/Den/Sim.lean`): `Sim ch m n` (from any state with oracle `ch`, the interpreter's outcome, projected, is denoted unless fuel ran out; it keeps the oracle and never clears the fuel flag, so it composes through bind), lemmas for the monad, state, loops, `try`, early return, the oracle's choices, and the lockstep tactic `sim` (walks the two definitions, which are the same code; splits the interpreter's matches and rewrites the denotation's copies, whose auxiliary matchers are distinct constants; applies the induction hypotheses and helper lemmas by the head of the interpreter's side). **Blocks**, each by induction on fuel over a structure with one field per function, generated (`gen_simselect.py`, `gen_simblock.py`, `gen_simcases.py`): query (`selectSim`, 37 functions; the join in `SimJoin`: plan, loops, the automatic index's skipped rows being rows the denotation's check rejects (`SimIndex`: a compiled conjunct's pure test is the denotation's value, from every state, without effect; the compilation does not depend on the current row); the recursive CTE's rounds by induction), Resolve (`resolveSim`), Exec (`execSim`, `execStmt` per statement kind), `runStmt` (the denotation picks the clock per statement; the oracle's is one choice), the driver's loop (`loopI_sound`, with the invariants: the oracle kept, exhaustion monotone). **Interpreter changes for the proof** (behaviour unchanged unless stated; 75/75 semantic scripts, select1–5 8,889/8,889 throughout): large functions split (`scalarFn`, `runSelect`, `computeWindow`, `runCore` → `runStream`/`runGrouped`/`runRows`/`windowOut`/`aggCtxs`/`groupCtx`, `insertRow`, INSERT/UPDATE/CREATE TABLE into their own functions); the join is the denotation's plan (`joinPrepareM`) and loops (`joinLoopsM`), the nesting order chosen on a sandboxed state; the automatic index is a compiled pure test (`PCond`: comparisons and IN lists of columns and literals, AND/OR/NOT), the memo of own conjuncts is gone (select4 109 s, was 68 s); the recursive CTE's rounds are `cteLoopM`; the driver's round (`driverStep`) is shared by the two semantics; the random rowid's 100 candidates are one draw of the oracle (the PRNG advances by one per pick: an unspecified choice). **Next:** precision (the converse), the remaining syntax-fuel debts, Phase 3 |
| 2.7a precision: plan | the denotation's choices are exactly the oracle's | open. The converse of soundness (`precise_Statement`: every denoted output is the interpreter's for some choices and fuel), so that the differential tests, which exercise the interpreter, constrain all of the denotation. Steps: (1) choices that are the plan's in SQLite are made where the plan makes them: the order of a depth's conjuncts once per join (in `joinPrepare`), not per row; the automatic index skips a row only when the compiled conjuncts before the rejecting one (in that order) are all compiled; the clock per statement in the oracle (`Choices.clock`, per statement, as `sqlite3StmtCurrentTime`); (2) every permutation has a Lehmer code (`permute` is onto the permutations); (3) a converse simulation: from a denoted outcome, a fuel and an oracle realising its choices (spliced from the choices of the parts, the oracle's counters only increasing), by fixed-point induction on the denotation (least fixed points: admissible) |

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
| 3.1 statement | `SqliteRefines_Statement` stated in Lean, with `Admissible` as a named-field structure; external model as a parameter (D6) | stated (`Spec/Refines.lean`): `Refines p` has fields `terminates` and `sound` (not an ↔: `Derives` is nondeterministic, the program deterministic); `Admissible` has fields `noExplain` (decision 2 pending), `memoryDatabasesOnly`, `noVacuum`, `statementSize` (≤ 500 tokens, for the unmodelled parser limits). **False as stated** on the scripts of BUGS.md #3 until decision 1 (a fourth extension for x86's float→int conversion, or a premise). The clock is a choice (`Choices.clockMs`), as is the external model's `World.clock` |
| 3.2 pilot proof | one end-to-end instance on a fixed small script, to measure the per-function cost | |
| 3.3 coverage | the proof column of the coverage table reaches all functions | |

## Obligations (`def …_Statement : Prop`)

| name | file | statement | status |
|---|---|---|---|
| `SqliteRefines_Statement` | `Spec/Refines.lean` | `Refines Sqlprog.prog` (BRIEF.md), `sound` into `Den.Derives` | stated; open; false on BUGS.md #3 until decision 1 |
| `Den.sound_Statement` | `Sql/Den/Sound.lean` | the interpreter's output, when its fuel does not run out, is denoted | **proved** (`Sql.Den.sound`, 2.6g) |

## Gaps (reductions to close)

| gap | introduced in | why | how it closes |
|---|---|---|---|
| SQLite's parser limits: "Recursion limit" (parser stack, ~500 nested subqueries/CASEs, ~3000 nested parentheses) and "Expression tree is too large (maximum depth 1000)" are not modelled: the semantics accepts deeper input | 2.5 | the descent parser's depth does not match yacc's stack; never modelled | model both limits as checks (stack depth of SQLite's LALR automaton, SQLITE_MAX_EXPR_DEPTH on the built tree) |
| a scalar subquery whose FROM names a CTE or a table-valued function has no affinity in comparisons (SQLite: its first column's) | 2.5 | `subqueryAffK` resolves tables, views and FROM subqueries only | carry the CTEs in `Env` |
| the affinity of a scalar subquery (`subqueryAffK`/`selectMetaK`) resolves views with a bound (`syntaxFuel`) | 2.6 (fuel in the spec) | the recursion goes through the schema's view definitions | a measure on the views not yet entered (SQLite rejects circular views) |
| the parser's fuel (`32 · (tokens left + 1)`, never exhausted: argued in `fuelPerToken`'s doc comment) is in the denotation's driver | 2.5/2.6 (fuel in the spec) | the descent parser is total by that bound | prove the bound sufficient (each recursive call consumes a token within 16 silent calls), or a lexicographic measure |

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
