#!/usr/bin/env python3
"""Phase 2.6 helper: derive the denotational counterpart of an interpreter
module (a starting point, edited by hand afterwards).

    scripts/dev/denize.py SRC.lean OUT.lean [--names a,b,...]

Keeps the definitions of SRC that are monadic (`M`) or take fuel, with their
doc comments and mutual blocks; drops the pure ones (the denotation uses
them from namespace `Sql`). In what it keeps:
  * the `(fuel : Nat)` parameter and the `match fuel with | 0 => outOfFuel |
    fuel + 1 =>` wrapper go, and so does the `fuel` argument of calls;
  * the monad `M` becomes `D`;
  * every definition of a mutual block gets `partial_fixpoint`.
The result is in namespace `Sql.Den` (so names resolve to the denotation's
definitions first, then to the interpreter's pure ones)."""
import re, sys

src, out = sys.argv[1], sys.argv[2]
text = open(src).read()
lines = text.split('\n')

# top-level items: (start, end) line ranges, with leading doc comments
starts = re.compile(r'^(partial def |def |theorem |structure |inductive |instance |abbrev |mutual$|end$|end |namespace |open |section|/-!|/--|@\[|-- |variable|import )')
items = []
i = 0
while i < len(lines):
    if starts.match(lines[i]) or (lines[i].strip() == '' and False):
        j = i + 1
        if lines[i].startswith('/--'):
            # doc comment: through its end, then the declaration it documents
            while '-/' not in lines[j - 1]:
                j += 1
            k = j
            while k < len(lines) and not starts.match(lines[k]):
                k += 1
            # the documented declaration
            k += 1
            while k < len(lines) and not starts.match(lines[k]):
                k += 1
            items.append((i, k)); i = k; continue
        while j < len(lines) and not starts.match(lines[j]):
            j += 1
        items.append((i, j)); i = j
    else:
        i += 1

def is_monadic(block):
    head = block.split(':=')[0]
    return bool(re.search(r'(\bM\b|\(fuel : Nat\))', head))

names = []
kept = []
in_mutual = False
mutual_buf = []
for (a, b) in items:
    blk = '\n'.join(lines[a:b])
    first = lines[a]
    if first.strip() == 'mutual':
        in_mutual = True; mutual_buf = [blk]; continue
    if in_mutual:
        mutual_buf.append(blk)
        if first.startswith('end'):
            in_mutual = False
            body = '\n'.join(mutual_buf)
            if re.search(r'\bM\b|\(fuel : Nat\)', body):
                kept.append(('mutual', body))
        continue
    if re.match(r'^(/--|partial def |def )', first) and is_monadic(blk.split('\ndef ')[-1] if first.startswith('/--') else blk):
        kept.append(('def', blk))

for kind, blk in kept:
    for m in re.finditer(r'^(?:partial )?def ([\w.]+)', blk, re.M):
        names.append(m.group(1))

# the monotonicity proof: lets reduced first (the `monotonicity` tactic cannot
# split a match on a let-bound variable, as do-notation makes for loops with
# early returns), then the compositional lemmas
PF = "partial_fixpoint monotonicity by (try simp only []); repeat' monotonicity"

def transform(blk, mutual):
    # fuel wrappers
    blk = re.sub(r'\n  match fuel with\n  \| 0 => outOfFuel\n  \| fuel \+ 1 => do\n', '\n  do\n', blk)
    blk = re.sub(r'\n  match fuel with\n  \| 0 => outOfFuel\n  \| fuel \+ 1 =>\n', '\n', blk)
    blk = re.sub(r'\(fuel : Nat\) ', '', blk)
    # fuel arguments of calls
    for n in sorted(set(names), key=len, reverse=True):
        blk = re.sub(r'(?<![\w.])' + re.escape(n) + r' fuel(?![\w\'])', n, blk)
    # and of calls to the other modules' meaning functions
    blk = re.sub(r'(?<!match)(?<=[\w)\]]) fuel(?=[\s)\]])', '', blk)
    # the monad
    blk = re.sub(r'(?<=[:(→\s])M(?= [\w(\[{])', 'D', blk)
    blk = blk.replace('partial def ', 'def ')
    if mutual:
        # partial_fixpoint after each definition of the block
        parts = re.split(r'(?m)^(?=(?:/--(?:(?!-/).)*-/\n)?def )', blk, flags=re.S)
        out = []
        for p in parts:
            if re.search(r'^def ', p, re.M) and 'partial_fixpoint' not in p.rstrip().split('\n')[-1]:
                body = p.rstrip('\n')
                if body.endswith('\nend'):
                    body = body[:-4].rstrip('\n') + '\n' + PF + '\nend'
                else:
                    body = body + '\n' + PF
                out.append(body + '\n\n')
            else:
                out.append(p)
        blk = ''.join(out).replace('\n\n\nend', '\nend')
    return blk

res = ['/-', f'  The denotation of {src} (Phase 2.6): derived by scripts/dev/denize.py, then',
       '  edited where the interpreter has fuel, a choice oracle or a strategy.', '-/',
       'import Sql.Den.Domain', '', 'namespace Sql.Den', '', 'open Sql Lean.Order', '']
for kind, blk in kept:
    res.append(transform(blk, kind == 'mutual'))
    res.append('')
res.append('end Sql.Den')
open(out, 'w').write('\n'.join(res) + '\n')
print(f'{out}: {len(names)} definitions: {" ".join(names)}')
