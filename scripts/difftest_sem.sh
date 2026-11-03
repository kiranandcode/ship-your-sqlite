#!/bin/bash
# Differential test of the SQL semantics: Sql.runScript (sql_run) against the
# native driver (driver-gcc) on each script. Outputs in build/diffsem/.
#   scripts/difftest_sem.sh [script.sql ...]     (default: tests/sql/*.sql tests/sem/*.sql)
set -uo pipefail
# the semantics takes the time zone to be UTC (Sql/DateTime.lean)
export TZ=UTC
. "$(dirname "$0")/env.sh"
out="$SYS_ROOT/build/diffsem"; mkdir -p "$out"
[ $# -gt 0 ] || set -- "$SYS_ROOT"/tests/sem/*.sql "$SYS_ROOT"/tests/sql/*.sql
pass=0; fail=0
for f in "$@"; do
  n=$(basename "$f" .sql)
  "$SYS_ROOT/build/native/driver-gcc" < "$f" > "$out/$n.want" 2>&1
  timeout 120 "$SYS_ROOT/.lake/build/bin/sql_run" < "$f" > "$out/$n.got" 2> "$out/$n.err"
  if cmp -s "$out/$n.want" "$out/$n.got"; then pass=$((pass+1)); echo "PASS $n"
  else
    fail=$((fail+1)); echo "FAIL $n ($(diff "$out/$n.want" "$out/$n.got" | grep -c '^[<>]') lines differ)"
    [ -n "${VERBOSE:-}" ] && diff "$out/$n.want" "$out/$n.got" | head -20 | sed 's/^/     /'
  fi
done
echo "semantics: passed $pass of $((pass+fail))"
[ $fail -eq 0 ]
