#!/bin/bash
# experiments/fuzz/run.sh FIRST_SEED N_SEEDS [QUERIES]: semantics vs driver-gcc on random scripts.
# Mismatching scripts are kept in build/fuzz/.
cd "$(dirname "$0")/../.."
export TZ=UTC
mkdir -p build/fuzz
bad=0
for s in $(seq $1 $(($1 + $2 - 1))); do
  python3 experiments/fuzz/gen.py $s ${3:-30} > build/fuzz/s$s.sql
  build/native/driver-gcc < build/fuzz/s$s.sql > build/fuzz/s$s.want 2>&1
  timeout 60 .lake/build/bin/sql_run < build/fuzz/s$s.sql > build/fuzz/s$s.got 2>&1
  if cmp -s build/fuzz/s$s.want build/fuzz/s$s.got; then rm build/fuzz/s$s.*; else bad=$((bad+1)); fi
done
echo "fuzz: $bad of $2 scripts differ"
