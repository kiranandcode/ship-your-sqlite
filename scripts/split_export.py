#!/usr/bin/env python3
"""Split a `clightgen -lean` output into Lean modules that elaborate and compile
within Lean's default limits (CLAUDE.md law 1: never raise maxRecDepth).

    scripts/split_export.py IN.lean OUTDIR [--height H] [--chunk BYTES] [--check]

The input is one generated file `namespace N … end N` with, in order: the
`Info` namespace, identifier defs (`def _x : Ident`), global variables
(`def v_x : GlobVar Ty`), functions (`def f_x : Function`), `composites`,
`global_definitions`, `public_idents` and `prog`.

Output (namespace N throughout, module prefix N):
    OUTDIR/N/Idents.lean      Info and the identifiers
    OUTDIR/N/Part<k>.lean     global variables and functions, ~BYTES each
    OUTDIR/N/Prog.lean        composites (in chunks), global_definitions,
                              public_idents, prog
    OUTDIR/N.lean             imports Prog

Two transformations, both definitional (the resulting `prog` unfolds to the
original term):
  * a `Stmt`/`LStmts` subterm of a function body whose nesting height reaches
    H is lifted into its own `def f_x_sK : Stmt` (or `LStmts`), bottom-up, so
    every definition has height at most about H;
  * `composites` is split into chunks of 32 joined with `++`.

`--check` re-inlines the lifted definitions and compares the token stream of
every function with the input's.
"""
import os, re, sys
sys.setrecursionlimit(1_000_000)

HEIGHT = 40
CHUNK = 1_500_000


def groups(text):
    """Parenthesis tree of `text`: list of (start, end, children) for top-level
    groups; strings are skipped."""
    stack = [(None, [])]
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            i += 1
            while text[i] != '"':
                i += 2 if text[i] == '\\' else 1
        elif c == '(':
            stack.append((i, []))
        elif c == ')':
            start, ch = stack.pop()
            stack[-1][1].append((start, i + 1, ch))
        i += 1
    assert len(stack) == 1, "unbalanced parentheses"
    return stack[0][1]


LIFT = (('(Stmt.', 'Stmt'), ('(LStmts.', 'LStmts'))


def lift_function(name, text, height, out_defs):
    """Return the body text with deep Stmt/LStmts groups replaced by names; the
    lifted definitions are appended to out_defs in dependency order."""
    counter = [0]

    def walk(g):
        start, end, ch = g
        # returns (replacement pieces for [start,end), effective height)
        pieces, pos, h = [], start, 0
        for c in ch:
            sub, hc = walk(c)
            pieces.append(text[pos:c[0]])
            pieces.append(sub)
            pos = c[1]
            h = max(h, hc)
        pieces.append(text[pos:end])
        body = ''.join(pieces)
        h += 1
        if h >= height:
            for prefix, ty in LIFT:
                if text.startswith(prefix, start):
                    counter[0] += 1
                    nm = f'{name}_s{counter[0]}'
                    out_defs.append(f'def {nm} : {ty} :=\n{body}\n')
                    return nm, 0
        return body, h

    pieces, pos = [], 0
    for g in groups(text):
        sub, _ = walk(g)
        pieces.append(text[pos:g[0]])
        pieces.append(sub)
        pos = g[1]
    pieces.append(text[pos:])
    return ''.join(pieces)


def split_defs(src):
    """Header (up to the first ident def), list of (name, text) defs, trailer."""
    lines = src.split('\n')
    starts = [i for i, l in enumerate(lines) if l.startswith('def ')]
    first = starts[0]
    # the Info namespace belongs to the header
    header = '\n'.join(lines[:first])
    end_ns = max(i for i, l in enumerate(lines) if l.startswith('end '))
    defs = []
    for a, b in zip(starts, starts[1:] + [end_ns]):
        t = '\n'.join(lines[a:b])
        nm = lines[a].split()[1]
        defs.append((nm, t.rstrip() + '\n'))
    return header, defs, '\n'.join(lines[end_ns:])


def tokens(s):
    return re.findall(r'"(?:\\.|[^"\\])*"|[A-Za-z_\'][\w\'.]*|\d+|\S', s)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    height = HEIGHT
    chunk = CHUNK
    if '--height' in sys.argv:
        height = int(sys.argv[sys.argv.index('--height') + 1]); args.remove(str(height))
    if '--chunk' in sys.argv:
        chunk = int(sys.argv[sys.argv.index('--chunk') + 1]); args.remove(str(chunk))
    check = '--check' in sys.argv
    inp, outdir = args
    src = open(inp).read()
    header, defs, _ = split_defs(src)
    ns = re.search(r'^namespace (\w+)$', header, re.M).group(1)
    pre = 'import Clightdefs\n'
    opening = 'open CC\n\nnamespace ' + ns + '\n\n'
    closing = '\nend ' + ns + '\n'
    os.makedirs(os.path.join(outdir, ns), exist_ok=True)

    idents = [t for n, t in defs if re.match(r"def [\w']+ : Ident :=", t)]
    parts, cur, size = [], [], 0
    tail = {}
    nlifted = 0
    for n, t in defs:
        if re.match(r"def [\w']+ : Ident :=", t):
            continue
        if n in ('composites', 'global_definitions', 'public_idents', 'prog'):
            tail[n] = t
            continue
        if n.startswith('f_'):
            lifted = []
            t2 = lift_function(n, t, height, lifted)
            if check:
                inl = t2
                for d in reversed(lifted):
                    m = re.match(r'def (\w+) : \w+ :=\n', d)
                    inl = re.sub(r'\b' + m.group(1) + r'\b', lambda _: d[m.end():].rstrip('\n'), inl, count=1)
                assert tokens(inl) == tokens(t), f'--check failed for {n}'
            nlifted += len(lifted)
            t = ''.join(lifted) + '\n' + t2
        cur.append(t); size += len(t)
        if size >= chunk:
            parts.append(cur); cur, size = [], 0
    if cur:
        parts.append(cur)

    def write(rel, imports, body):
        with open(os.path.join(outdir, rel), 'w') as f:
            f.write(pre + ''.join(f'import {i}\n' for i in imports) + opening + body + closing)

    info = header[header.index('namespace Info'):]
    write(f'{ns}/Idents.lean', [], info.strip() + '\n\n' + '\n'.join(idents))
    for k, p in enumerate(parts):
        write(f'{ns}/Part{k}.lean', [f'{ns}.Idents'], '\n'.join(p))

    # the three long list literals, in chunks joined with ++
    def chunked(name, size):
        t = tail[name]
        m = re.match(r'def \w+ : (.*?) :=', t)
        ty = m.group(1)
        body = t[m.end():].strip()
        assert body.startswith('[') and body.endswith(']')
        inner = body[1:-1]
        # items are separated by top-level commas (outside (), [], strings)
        items, depth, cur, i = [], 0, 0, 0
        while i < len(inner):
            c = inner[i]
            if c == '"':
                i += 1
                while inner[i] != '"':
                    i += 2 if inner[i] == '\\' else 1
            elif c in '([{': depth += 1
            elif c in ')]}': depth -= 1
            elif c == ',' and depth == 0:
                items.append(inner[cur:i].strip()); cur = i + 1
            i += 1
        if inner[cur:].strip():
            items.append(inner[cur:].strip())
        out, names = [], []
        for k in range(0, len(items), size):
            nm = f'{name}_{k // size}'
            names.append(nm)
            out.append(f'def {nm} : {ty} :=\n[' + ',\n '.join(items[k:k + size]) + ']\n')
        out.append(f'def {name} : {ty} :=\n  ' + ' ++ '.join(names) + '\n')
        return '\n'.join(out), len(items), len(names)
    comp, ncomp, nchunks = chunked('composites', 32)
    gdefs, _, _ = chunked('global_definitions', 128)
    pubs, _, _ = chunked('public_idents', 256)
    write(f'{ns}/Prog.lean', [f'{ns}.Part{k}' for k in range(len(parts))],
          comp + '\n' + gdefs + '\n' + pubs + '\n' + tail['prog'])
    with open(os.path.join(outdir, f'{ns}.lean'), 'w') as f:
        f.write(f'import {ns}.Prog\n')
    print(f'{ns}: {len(idents)} idents, {len(parts)} parts, {nlifted} lifted statements, '
          f'{ncomp} composites in {nchunks} chunks' + (', check ok' if check else ''))


if __name__ == '__main__':
    main()
