#!/bin/bash
# experiments/json/dt.sh file.sql ... : diff the native driver (oracle) against
# sql_run on each script; prints PASS/FAIL and the first lines of the diff.
R=$(cd "$(dirname "$0")/../.." && pwd)
st=0
for f in "$@"; do
  want=$(mktemp); got=$(mktemp)
  "$R/build/native/driver-gcc" < "$f" > "$want" 2>&1
  timeout 120 "$R/.lake/build/bin/sql_run" < "$f" > "$got" 2>&1
  if cmp -s "$want" "$got"; then echo "PASS $f"
  else echo "FAIL $f"; diff "$want" "$got" | head -"${N:-30}"; st=1; fi
  rm -f "$want" "$got"
done
exit $st
