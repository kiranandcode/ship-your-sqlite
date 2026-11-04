#!/bin/bash
# Phase 2.6: regenerate Sql/Den/{Select,Resolve,Exec}.lean from the interpreter
# (scripts/dev/denize.py, then the hand edits of den_*_edits.py).
set -e
cd "$(dirname "$0")/../.."
python3 scripts/dev/denize.py Sql/Select.lean Sql/Den/Select.lean --skip attemptM,joinLoopsM,sandbox,greedyOrder,chooseNest,joinPrepareM >/dev/null
python3 scripts/dev/den_select_edits.py
python3 scripts/dev/denize.py Sql/Resolve.lean Sql/Den/Resolve.lean >/dev/null
sed -i 's/^import Sql.Den.Domain$/import Sql.Den.Select/' Sql/Den/Resolve.lean
python3 - <<'PY'
import re
p='Sql/Den/Resolve.lean'; s=open(p).read()
s=re.sub(r'(?<![.\w«])alias(?![\w»])', '«alias»', s); open(p,'w').write(s)
PY
python3 scripts/dev/denize.py Sql/Exec.lean Sql/Den/Exec.lean >/dev/null
python3 scripts/dev/den_exec_edits.py
