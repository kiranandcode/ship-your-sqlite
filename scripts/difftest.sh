#!/bin/bash
# Differential test: every script runs on the native gcc and ccomp builds of
# c/driver.c + sqlite3.c and on the Lean export under Clean's interpreter
# (sqlite_run). Prints one line per script and a summary; outputs in
# build/diff/<name>.{gcc,ccomp,lean,lean.err}.
#   scripts/difftest.sh [script.sql ...]      (default: tests/sql/*.sql)
set -uo pipefail
# the semantics takes the time zone to be UTC (Sql/DateTime.lean)
export TZ=UTC
. "$(dirname "$0")/env.sh"
out="$SYS_ROOT/build/diff"; mkdir -p "$out"
run="$SYS_ROOT/.lake/build/bin/sqlite_run"
[ $# -gt 0 ] || set -- "$SYS_ROOT"/tests/sql/*.sql
pass=0; fail=0
for f in "$@"; do
  n=$(basename "$f" .sql)
  "$SYS_ROOT/build/native/driver-gcc" < "$f" > "$out/$n.gcc" 2>&1
  "$SYS_ROOT/build/native/driver-ccomp" < "$f" > "$out/$n.ccomp" 2>&1
  timeout 1200 "$run" --stats < "$f" > "$out/$n.lean" 2> "$out/$n.lean.err"; rc=$?
  st=$(grep -o 'steps=[0-9]* externals=[0-9]* flat=[0-9]* run_ms=[0-9]*' "$out/$n.lean.err")
  if cmp -s "$out/$n.gcc" "$out/$n.ccomp" && cmp -s "$out/$n.ccomp" "$out/$n.lean" && [ $rc -eq 0 ]; then
    pass=$((pass+1)); echo "PASS $n  $st"
  else
    fail=$((fail+1)); echo "FAIL $n  rc=$rc $st"
    cmp -s "$out/$n.gcc" "$out/$n.ccomp" || echo "     gcc and ccomp differ"
    grep -v '^\[sqlite_run\] steps' "$out/$n.lean.err" | head -3 | sed 's/^/     /'
    diff "$out/$n.ccomp" "$out/$n.lean" | head -6 | sed 's/^/     /'
  fi
done
echo "passed $pass of $((pass+fail))"
[ $fail -eq 0 ]
