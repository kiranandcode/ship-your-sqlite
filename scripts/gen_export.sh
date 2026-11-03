#!/bin/bash
# Generate the Lean export of c/sqlprog.c (sqlite3.c + c/driver.c) into build/gen:
#   clightgen -lean -normalize $CG_FLAGS $(config/sqlite.flags)  ->  build/export/Sqlprog.lean
#   scripts/split_export.py --check                              ->  build/gen/Sqlprog{,/*}.lean
# Then `lake build Sqlprog` (lean_lib with srcDir build/gen).
set -euo pipefail
. "$(dirname "$0")/env.sh"
mkdir -p "$SYS_ROOT/build/export"
flags=$(cat "$SYS_ROOT/config/sqlite.flags")
"$CLIGHTGEN" -lean -normalize $CG_FLAGS $flags -I"$SQLITE_SRC" -I"$SYS_ROOT/c" \
  -o "$SYS_ROOT/build/export/Sqlprog.lean" "$SYS_ROOT/c/sqlprog.c" 2> >(grep -v "magnitude of floating-point constant\|__has_extension. redefined" >&2)
rm -rf "$SYS_ROOT/build/gen/Sqlprog"
python3 "$SYS_ROOT/scripts/split_export.py" "$SYS_ROOT/build/export/Sqlprog.lean" "$SYS_ROOT/build/gen" --check
