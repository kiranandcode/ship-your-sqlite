# ship-your-sqlite

A semantics of SQL, validated against SQLite and proved against it.

SQLite is the reference implementation of SQL in practice. This project takes
it as the correctness criterion: it exports the whole C source of SQLite
(the `sqlite3.c` amalgamation of a pinned release) to Lean 4 as Clight, writes
a semantics of the SQL dialect SQLite implements, and aims to prove that the
Clight program refines the semantics: on every script, what SQLite prints is
what the semantics derives. The semantics is differentially tested against
`sqlite3` before anything is proved about it.

It is a "ship your interpreter" project, after
[ship-your-interpreter](https://github.com/BasisResearch/ship-your-interpreter)
(a C interpreter's RV64 binary against an LLM-written semantics), with
siblings for TinyCC and libtommath.

- Plan, scope and decisions: [BRIEF.md](BRIEF.md) (and Kiran's scope note,
  [SCOPE-FROM-KIRAN.md](SCOPE-FROM-KIRAN.md): all of SQLite, not a subset)
- Phases, coverage, obligations, gaps and obstructions: [PHASES.md](PHASES.md)
- What the theorem's semantics adds to CompCert's Clight: [TRUST.md](TRUST.md)
- Discipline: [CLAUDE.md](CLAUDE.md)
- Provenance: [ATTRIBUTION.md](ATTRIBUTION.md)

## Status (2026-11-03)

- **The export.** The **full** `sqlite3.c` of SQLite 3.54.1 (default build,
  plus the math functions; 2,642 functions, 47 MB of Lean) goes through
  Certora/clean's `clightgen -lean` and builds with Lean's default limits. It
  **runs** under Clean's interpreter with an explicit libc model and the three
  extensions of Clight described in [TRUST.md](TRUST.md) (variadic calls, and
  pointers used as integers under a flat placement of blocks). Its output is
  byte-identical to the gcc and ccomp builds on the differential scripts
  (`scripts/difftest.sh`).
- **The semantics.** `Sql/` is a semantics of SQLite's SQL in Lean 4, written
  against `sqlite3` as the criterion and run as `sql_run`. It covers:
  - every statement kind except EXPLAIN and VACUUM INTO;
  - joins of every kind, subqueries, compound selects, recursive CTEs and window functions;
  - triggers, including INSTEAD OF, foreign keys with their actions, UPSERT and RETURNING;
  - ALTER TABLE with SQLite's rewriting of the stored SQL, transactions and savepoints, TEMP and attached in-memory databases;
  - prepare-time name resolution, and the core, math, printf, date/time and JSON/JSONB function libraries.
- **Differential results** against `sqlite3`:
  - `tests/sem` + `tests/sql`: all 64 scripts agree;
  - sqllogictest: `select1`–`select3` and `evidence/` agree on all 5,653 queries;
  - REAL rendering: 0 mismatches on 1.6M doubles;
  - printf/round/quote: 0 in 1.8M random calls;
  - date/time: 0 in 181k;
  - JSON: 0 in 13k random statements;
  - random scripts (`experiments/fuzz/`): the remaining differences are
    choices SQL leaves to the plan (scan order through an index, the random
    rowid after 2^63−1).
- **Totality and the relational semantics.** `Sql/` has no `partial def` and
  no `while` loop (`scripts/check_total.py`). `Sql.Derives` (`Sql/Derives.lean`)
  is the set of outputs a script may produce: the executable semantics with
  the implementation's choices (`Sql.Choices`: row orders, `random()`, the
  clock) as a parameter; the executable is sound for it.
- **The theorem**, stated in `Spec/Refines.lean` and not yet proved: on an
  admissible script, the Clight program terminates and its output is derived.
- **Coverage:** `python3 scripts/coverage.py`.
- **SQLite behaviour found:** places where SQLite relies on behaviour that is
  undefined in CompCert's memory model, one of them undefined in ISO C too
  ([BUGS.md](BUGS.md)).

## Building

Everything large is fetched, never committed. CompCert's licence is
non-commercial and this repository is public, so Clean is fetched at a pinned
commit, and so is SQLite.

```sh
scripts/fetch_clean.sh      # Certora/clean @123f7f7 into build/clean/src
scripts/fetch_sqlite.sh     # SQLite 3.54.1 amalgamation, SHA3-256 checked
scripts/build_clean.sh      # ccomp + clightgen (needs the opam switch named in the script)
lake build                  # CCLib (fetched by Lake from the same commit) + the runner
```

## Credits

- **CompCert**, by Xavier Leroy and the CompCert team at **INRIA**,
  commercially distributed by **AbsInt**. Its Clight, its memory model and
  `clightgen` are the foundation of this work. CompCert is distributed under
  the INRIA Non-Commercial License Agreement (some files dual-licensed under
  the LGPL); none of it is in this repository.
- **[Certora/clean](https://github.com/Certora/clean)**, Certora's CompCert
  3.17 fork: `clightgen -lean`, the Lean 4 port of Clight's semantics
  (CCLib), its interpreter, determinism proof and separation logic. Used at
  commit `123f7f7`, fetched, not vendored.
- **[SQLite](https://sqlite.org)**, by D. Richard Hipp and the SQLite
  developers, in the public domain. Fetched at release 3.54.1.
- Method, tooling and discipline from ship-your-interpreter, ship-your-tcc
  and ship-your-libtommath (ATTRIBUTION.md).
- The idea came from a friend of Kiran's.
