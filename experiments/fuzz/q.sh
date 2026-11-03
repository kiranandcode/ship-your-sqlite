#!/bin/bash
# experiments/fuzz/q.sh SEEDFILE 'SQL': run SQL after the seed's setup on both, side by side
f=$1; shift
(grep -v "^SELECT" $f; echo "$@") > /tmp/q.$$.sql 2>/dev/null || true
cd "$(dirname "$0")/../.."
setup=$(grep -v "^SELECT" $f)
printf "%s\n%s\n" "$setup" "$*" | TZ=UTC build/native/driver-gcc > build/q.want
printf "%s\n%s\n" "$setup" "$*" | TZ=UTC .lake/build/bin/sql_run > build/q.got
paste -d'#' build/q.want build/q.got | tail -${N:-12}
rm -f /tmp/q.$$.sql
