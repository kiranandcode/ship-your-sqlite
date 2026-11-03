# Attribution and provenance

## Fetched, not vendored

| what | source | pin | licence |
|---|---|---|---|
| Certora/clean (CompCert 3.17 fork, `clightgen -lean`, CCLib) | https://github.com/Certora/clean | `123f7f7767e215aceb4821f0d044336d78103ade` (`scripts/env.sh`, `lakefile.toml`) | INRIA Non-Commercial License Agreement; some files dual LGPL-2.1+ (see its LICENSE) |
| SQLite amalgamation | https://sqlite.org/2026/sqlite-amalgamation-3540100.zip | 3.54.1, SHA3-256 `92281c86e2957f9b9305890f9ac04204caa7b677cc868dc326d942689df28e30` | public domain |

## Copied or adapted code

| file here | from | how |
|---|---|---|
| `Run/Runner.lean` | ship-your-tcc `lean/ClightRun/ClightRun/Run.lean` | the pure `runPure` loop, the stuck-state diagnosis and the `Callstate (External …)` interception; the external model and `World` threading are new |
| `ClightRun.lean` | ship-your-tcc `lean/ClightRun/Main.lean` | in-process elaboration of a generated file (`loadProg`) and the exit-code convention |
| `scripts/build_clean.sh` | ship-your-tcc `scripts/build_certora_ccomp.sh` | same recipe and opam switch; target changed to x86_64-linux |
