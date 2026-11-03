#!/bin/bash
# Configure and build Certora/clean's ccomp + clightgen (x86_64-linux) into
# build/clean/install. Needs the opam switch $CLEAN_OPAM_SWITCH:
#   opam switch create certora-clean ocaml-base-compiler.4.14.2 --no-switch --repos=default,rocq-released
#   opam install --switch=certora-clean coq.9.1.0 menhir.20260209
# (this switch already exists on aws-dev; ship-your-tcc created it).
# Target x86_64-linux: the preprocessor is the host gcc with glibc headers, the
# same headers the native sqlite3 oracle is compiled against.
set -euo pipefail
. "$(dirname "$0")/env.sh"
[ -d "$CLEAN_SRC/.git" ] || "$SYS_ROOT/scripts/fetch_clean.sh"
for p in "$SYS_ROOT"/patches/clean/*.patch; do
  [ -e "$p" ] || continue
  git -C "$CLEAN_SRC" apply --reverse --check "$p" 2>/dev/null || git -C "$CLEAN_SRC" apply "$p"
done
cd "$CLEAN_SRC"
opam exec --switch="$CLEAN_OPAM_SWITCH" -- ./configure -prefix "$CLEAN_INSTALL" -clightgen x86_64-linux
start=$(date +%s)
syscap opam exec --switch="$CLEAN_OPAM_SWITCH" -- make -j8 all
syscap opam exec --switch="$CLEAN_OPAM_SWITCH" -- make install
echo "clean build+install took $(( $(date +%s) - start ))s"
