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
- Discipline: [CLAUDE.md](CLAUDE.md)
- Provenance: [ATTRIBUTION.md](ATTRIBUTION.md)

## Status (2026-11-03)

- Pilot: Certora/clean's `ccomp` and `clightgen` build for x86_64-linux;
  `c/pilot/hello.c` goes through `clightgen -lean` and our runner (Clean's
  `doStep` plus an executable libc model) prints the same bytes as gcc.
- The **full** `sqlite3.c` of SQLite 3.54.1 (default build, plus the math
  functions) is accepted by `clightgen -lean` with `-fstruct-passing` and two
  preprocessor-only flags (`config/sqlite.flags`): 2,642 functions, 47 MB of
  Lean.
- The export **runs**: Clean's interpreter, with an explicit external model
  and three stated extensions of Clight (variadic calls, and pointers used as
  integers under a flat placement of blocks; BRIEF.md D8, PHASES.md O1/O2),
  gives byte-identical output to the gcc and ccomp builds on all six
  differential scripts of `tests/sql/` (`scripts/difftest.sh`), which cover
  joins, CTEs, window functions, triggers, constraints, UPSERT, transactions,
  pragmas and the JSON, date and math functions.
- Two places where SQLite relies on behaviour CompCert leaves undefined,
  one of them undefined in ISO C too (BUGS.md).

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
