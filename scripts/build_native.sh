#!/bin/bash
# The native oracles: c/driver.c + sqlite3.c with the flags of config/sqlite.flags,
#   build/native/driver-gcc    gcc -O1 (what users run)
#   build/native/driver-ccomp  Clean's ccomp (the same preprocessing and front end as the export)
#   build/native/sqlite3       the sqlite3 shell, same flags (sanity checks only)
set -euo pipefail
. "$(dirname "$0")/env.sh"
out="$SYS_ROOT/build/native"; mkdir -p "$out"
flags=$(cat "$SYS_ROOT/config/sqlite.flags")
gcc -O1 $flags -I"$SQLITE_SRC" -o "$out/driver-gcc" "$SYS_ROOT/c/driver.c" "$SQLITE_SRC/sqlite3.c" -lm
gcc -O1 $flags -o "$out/sqlite3" "$SQLITE_SRC/shell.c" "$SQLITE_SRC/sqlite3.c" -lm
syscap "$CCOMP" -O $CG_FLAGS $flags -I"$SQLITE_SRC" -o "$out/driver-ccomp" "$SYS_ROOT/c/driver.c" "$SQLITE_SRC/sqlite3.c" -lm
ls -l "$out"
