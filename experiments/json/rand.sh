#!/bin/bash
# Randomized differential of the JSON functions: sql_run against the native
# driver on generated scripts (experiments/json/gen.py).
#   experiments/json/rand.sh SEEDS STATEMENTS_PER_SEED [--nest]
# Prints the number of mismatching statements; mismatches go to
# $OUT/mismatch.txt (OUT defaults to build-local scratch under $TMPDIR).
R=$(cd "$(dirname "$0")/../.." && pwd)
seeds=${1:-10}; n=${2:-500}; flag=${3:-}
OUT=${OUT:-/data/home/kirancodes/tmp/sqlite-build/json-rand}
mkdir -p "$OUT"; : > "$OUT/mismatch.txt"
total=0; bad=0
for s in $(seq 1 "$seeds"); do
  python3 -I "$R/experiments/json/gen.py" "$s" "$n" $flag > "$OUT/s.sql"
  "$R/build/native/driver-gcc" < "$OUT/s.sql" > "$OUT/want" 2>&1
  timeout 600 "$R/.lake/build/bin/sql_run" < "$OUT/s.sql" > "$OUT/got" 2>&1
  python3 -I "$R/experiments/json/cmp.py" "$OUT/s.sql" "$OUT/want" "$OUT/got" "$s" >> "$OUT/mismatch.txt"
  total=$((total + n))
done
bad=$(grep -c '^### ' "$OUT/mismatch.txt")
echo "statements: $total  mismatches: $bad  (details: $OUT/mismatch.txt)"
