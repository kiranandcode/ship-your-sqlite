# Source me:  . scripts/env.sh
# Paths and pins for ship-your-sqlite. Everything big lives under build/ (gitignored)
# on /data; never under /tmp or /.
_sys_here=$(cd "$(dirname "${BASH_SOURCE[0]:-$0}")" && pwd)
export SYS_ROOT=$(cd "$_sys_here/.." && pwd)
export TMPDIR=${TMPDIR:-/data/home/kirancodes/tmp/sqlite-build}
mkdir -p "$TMPDIR"

# Certora/clean (CompCert 3.17 fork with clightgen -lean). Not vendored: CompCert's
# licence is non-commercial, so it is fetched at this commit by scripts/fetch_clean.sh.
export CLEAN_REPO=https://github.com/Certora/clean.git
export CLEAN_COMMIT=123f7f7767e215aceb4821f0d044336d78103ade
export CLEAN_DIR="$SYS_ROOT/build/clean"
export CLEAN_SRC="$CLEAN_DIR/src"
export CLEAN_INSTALL="$CLEAN_DIR/install"
export CCOMP="$CLEAN_INSTALL/bin/ccomp"
export CLIGHTGEN="$CLEAN_INSTALL/bin/clightgen"
# opam switch with OCaml 4.14.2, Rocq 9.1.0, Menhir 20260209 (see scripts/build_clean.sh)
export CLEAN_OPAM_SWITCH=${CLEAN_OPAM_SWITCH:-certora-clean}

# SQLite amalgamation, pinned release (public domain). Fetched, not vendored (9 MB).
export SQLITE_VERSION=3.54.1
export SQLITE_VERNUM=3540100
export SQLITE_YEAR=2026
export SQLITE_SHA3_256=92281c86e2957f9b9305890f9ac04204caa7b677cc868dc326d942689df28e30
export SQLITE_DIR="$SYS_ROOT/build/sqlite"
export SQLITE_SRC="$SQLITE_DIR/sqlite-amalgamation-$SQLITE_VERNUM"

# Heavy jobs: at most 2 at once, each capped.
syscap() { systemd-run --user --scope -q -p MemoryMax=16G "$@"; }
unset _sys_here
