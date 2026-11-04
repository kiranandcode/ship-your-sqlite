# Brief: ship-your-sqlite

Take SQLite as the definition of SQL. Write a semantics of the whole SQL
dialect SQLite implements, in Lean 4. Prove that SQLite's C source, exported
to Lean as Clight, refines that semantics: on every script, the output the
Clight program produces is the output the semantics derives.

Scope: **all of SQLite**, not a core subset.
- the full amalgamation `sqlite3.c` of a pinned release, in its default build,
  through `clightgen -lean`. A workaround for a clightgen limit must keep the
  functionality. An `SQLITE_OMIT_*` or reduced build is allowed only as a
  temporary pilot step, and is recorded in PHASES.md as a gap to close;
- the whole SQL dialect in the semantics: DDL, DML, joins, subqueries, CTEs
  (recursive too), window functions, triggers, views, indexes, constraints,
  transactions and savepoints, the pragmas that affect results, collations, the
  built-in function library (core, aggregate, date/time, math, JSON), type
  affinity, NULL and three-valued logic;
- the refinement theorem about the whole program, not a fragment.

The pilot slice exists only to stand the pipeline up.

## Background

- **ship-your-interpreter** (syi, `~/Documents/code/syi`): a C WHILE
  interpreter's bare-metal RV64 ELF refines a big-step semantics written for
  it (`endToEnd_refinement`). This project applies the same idea one level up:
  the reference implementation is the C source of SQLite, and its semantics is
  Clight, not a machine model.
- **ship-your-tcc** (`~/Documents/code/ship-your-tcc`) already built
  Certora/clean at the same commit, ran `clightgen -lean` plus Clean's Lean
  interpreter as a differential oracle on 345 programs (2 Lean-port bugs found,
  `DIFFERENTIAL.md`), and patched CCLib so that external calls are a parameter
  of the step relation (its `patches/certora/0002-cclib-extsem-param.patch`).
  We copy its build recipe and lessons, with attribution.
- **ship-your-libtommath**: the coverage discipline (`scripts/coverage.py`:
  functions proved / total), the obligation ledger and the laws.
- **Certora/clean** (https://github.com/Certora/clean): a CompCert 3.17 fork.
  `clightgen -lean` exports Clight as Lean 4; `export/CCLib` is a Lean port of
  Clight's small-step semantics with CompCert's block memory model, an
  interpreter proved sound (`doStep_sound`), determinism, and a
  total-correctness separation logic. External calls are axiomatised
  (`externalFunctionsSem`), volatile accesses are not covered, and the port is
  validated by differential testing, not proved equal to the Rocq semantics.
  See `export/LEAN.md` of the pinned commit.

## The theorem we are after

```
structure Refines (p : CC.Program) : Prop where
  terminates : ∀ script, Admissible script → ∃ out, ClightRuns p script out
  sound : ∀ script, Admissible script → ∀ out, ClightRuns p script out → Sql.Derives script out

theorem sqlite_refines : Refines Sqlprog.prog
```

(`Spec/Refines.lean`.) Not an `↔`: `Sql.Derives` is nondeterministic where SQL
leaves the choice to the implementation (row order without ORDER BY, ties,
group representatives, `random()`, the clock; `Sql.Choices`), while the
program is deterministic, so the program's output is one of the derived
outputs. `terminates` with `sound` says the program has an output and every
output it has is derived.

- `sqliteProg` is the Lean Clight program `clightgen -lean` produces from the
  pinned `sqlite3.c` linked with our fixed driver `c/driver.c` (reads a script,
  runs it with `sqlite3_exec`/`sqlite3_prepare_v2`, prints rows and errors in a
  canonical format).
- `ClightRuns` is Clean's `Step` relation run to a final state, with the
  libc/OS boundary given by an explicit external-call model (a parameter, not
  an axiom), and `out` the bytes the driver writes.
- `Sql.Derives` is our SQL semantics (`Sql/`), executable as `Sql.run` so that
  it can be differentially tested against `sqlite3`.
- `Admissible` collects the honest premises, each a named field of a
  structure documented with what removes it: no EXPLAIN (pending decision),
  in-memory databases only (no file system model yet), no VACUUM, statements of
  at most 500 tokens (SQLite's parser limits are not modelled).

Until it is proved it is `def SqliteRefines_Statement : Prop` in PHASES.md.

## Correctness criterion and oracles

`sqlite3` is the criterion. Every claim about the semantics is first checked
differentially: the semantics' output against the native build of the same
`driver.c` + `sqlite3.c` (same flags), on sqllogictest, SQLite's own test
scripts where they are pure SQL, and generated scripts. Disagreements are bugs
in the semantics until shown otherwise. The Clight export is checked the same
way: Clean's interpreter running `sqliteProg` against the native binary.

## Decisions

| id | decision | why | status |
|---|---|---|---|
| D1 | SQLite **3.54.1** amalgamation (`sqlite-amalgamation-3540100.zip`, SHA3-256 `92281c86…`), fetched by `scripts/fetch_sqlite.sh`, not vendored | latest release on 2026-11-03; 9.5 MB of C | taken |
| D2 | Certora/clean **123f7f7** (upstream HEAD on 2026-11-03, the commit ship-your-tcc uses), fetched by `scripts/fetch_clean.sh`, never vendored | CompCert's INRIA licence is non-commercial and this repository is public | taken |
| D3 | clightgen target **x86_64-linux**, preprocessed by the host gcc 15.2 against glibc headers | the native oracle is compiled against the same headers and configuration, so `HAVE_*` choices agree; LP64 little-endian like Clean's `Archi.lean` (AArch64 parameters) | taken; NaN parameters to check |
| D4 | Lean **4.32.1**, Clean's pinned toolchain; CCLib is a Lake `git` dependency at D2's commit (`subDir = "export"`), so nothing of it is in this repository | no port needed; ship-your-tcc's 4.34 port is available if we must move | taken |
| D5 | Running the export: our runner wraps Clean's `doStep` and executes `Callstate (External …)` states itself with an executable libc/OS model (`Run/Ext.lean`), so no CCLib patch is needed to *run* | `doExternalCall` refuses unknown externals; SQLite calls ~80 libc/POSIX functions | taken |
| D6 | Proving: the external semantics must be a parameter, not Clean's axiom (our laws forbid axioms in the theorem's footprint) | ship-your-tcc's `StepWith X` patch does exactly this | open: adopt tcc's patch (kept under `patches/clean/`) or route libc through C; decide in Phase 3 |
| D8 | The semantics the theorem is about is **Clean's `Step` extended** by exactly three things, each stated in Lean in this repository: (1) the external model (`Run/Ext.lean`); (2) variadic calls and `va_*` (O1, `Run/Runner.lean`); (3) a flat placement of blocks for the pointer comparisons CompCert leaves undefined (O2, `Run/Flat.lean`). Volatile accesses to non-volatile blocks are not an extension: they are Clean's `VolatileLoad.nonvol`/`VolatileStore.nonvol`, which its interpreter just does not execute | keeps clightgen, CCLib and SQLite unmodified and the whole program in scope; the alternatives were patching CCLib (CompCert-licensed code) or compiling features out of SQLite (against the scope) | **adopted** (2026-11-03); documented in TRUST.md |
| D7 | Configuration: the default build (no `-D` flags). The oracle and the export use the same flag file `config/sqlite.flags`. `SQLITE_ENABLE_MATH_FUNCTIONS` (on in the official CLI, off in a bare `sqlite3.c` build) is added to the flag file so the math library is in scope | the scope: the default build, and the built-in function library | taken (reversible) |

## Laws

The sibling projects' laws, unchanged: no `sorry`, `axiom`, `native_decide`
or `bv_decide`; never raise `maxHeartbeats`/`maxRecDepth`; named-field
structures, not ∃/∧ towers; generated files are generated (change the
generator); obstructions go in PHASES.md with the evidence. Details in
CLAUDE.md.
