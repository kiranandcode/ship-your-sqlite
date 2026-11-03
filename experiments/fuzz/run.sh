#!/bin/bash
# experiments/fuzz/run.sh FIRST_SEED N_SEEDS [QUERIES] [dml]: semantics vs driver-gcc on random scripts.
# Mismatching scripts are kept in $FUZZ_OUT (default build/fuzz/).
cd "$(dirname "$0")/../.."
export TZ=UTC
D=${FUZZ_OUT:-build/fuzz}
mkdir -p $D
bad=0
for s in $(seq $1 $(($1 + $2 - 1))); do
  python3 experiments/fuzz/gen.py $s ${3:-30} ${4:-} > $D/s$s.sql
  build/native/driver-gcc < $D/s$s.sql > $D/s$s.want 2>&1
  timeout 60 .lake/build/bin/sql_run < $D/s$s.sql > $D/s$s.got 2>&1
  if cmp -s $D/s$s.want $D/s$s.got; then rm $D/s$s.*
  elif cmp -s <(sort $D/s$s.want) <(sort $D/s$s.got); then ties=$((ties+1)); rm $D/s$s.*
  else bad=$((bad+1)); fi
done
echo "fuzz: $bad of $2 scripts differ (and ${ties:-0} differ only in the order of ties, which SQL leaves unspecified)"
