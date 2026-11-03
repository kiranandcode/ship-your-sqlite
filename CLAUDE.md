# ship-your-sqlite — discipline

The whole of SQLite (SCOPE-FROM-KIRAN.md): `sqlite3.c` exported by Clean's
`clightgen -lean`, a semantics of the whole SQL dialect, and a refinement
theorem about the whole program. Plan: BRIEF.md. Ledger: PHASES.md.

## Before any work
* Read BRIEF.md, PHASES.md and SCOPE-FROM-KIRAN.md.
* Reuse, don't rebuild: ship-your-tcc already built Clean, ran its
  interpreter as an oracle and patched CCLib for parametric externals. Copy
  with a row in ATTRIBUTION.md. Sibling repositories are read-only.

## Laws
1. **Elaboration budget.** Never raise `maxHeartbeats`/`maxRecDepth`. A timeout
   means the construction is wrong; change the generator or the abstraction.
2. **No `sorry`/`axiom`/`native_decide`/`bv_decide`.** An unproved theorem is a
   `def …_Statement : Prop` listed in PHASES.md; a gap is a named, typed premise
   with a doc comment saying what discharges it. Clean's own axioms
   (`externalFunctionsSem`, …) must not be in the footprint of our theorems
   (BRIEF.md D6). Check with `#print axioms`.
3. **Named-field structures**, not ∃/∧ towers.
4. **Generated files are generated.** The Lean export of SQLite comes from
   `clightgen`; change flags, the generator or a patch, never the output.
5. **Obstructions** go in PHASES.md with machine-checked evidence (a reproducer
   in `c/pilot/`, a log). Workarounds must keep functionality; a reduction is a
   row under Gaps.
6. **Duplication is a signal.** Factor before the third similar proof.

## Licensing (public repository)
Never commit CompCert or Clean sources, or files generated from them in bulk
(the SQLite export is regenerated, not committed). Patches to Clean, if any,
are small and live in `patches/clean/`.

## Machine (aws-dev, shared)
* Everything big on /data: `TMPDIR=/data/home/kirancodes/tmp/sqlite-build`
  (`scripts/env.sh` sets it), build trees under `build/` (gitignored). Never
  write big files to /tmp or /.
* At most 2 heavy builds at once, each under
  `systemd-run --user --scope -p MemoryMax=16G` (`syscap` in env.sh). Check
  `free -g` first. Don't kill processes you didn't start.

## Git
Small commits, pushed to origin main (public). No secrets, no force-push.
