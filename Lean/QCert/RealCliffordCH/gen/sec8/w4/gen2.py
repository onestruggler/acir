"""Engine runs for the fixed-width equations of Appendices D.3, D.4 (packages (ii), (iii)),
with symmetric table entries (solve2.py, Sec8/D/W3/Sym.lean).

    python gen2.py D3.json OUT.lean TITLE IMPORTS EQ [EQ ...]

Earlier equations (the token words of W4/A.lean, read from it, and of the modules
generated before, read from their `.lean` files) enter the tables relabelled through
`WS.rel_entry`.  Each equation follows the paper's chain, every step solved by
`solve2.Solver`; the run is checked by tok.Engine and written as `tNNN`; the exported ones
also get `eNNN : Derivable (theory 4) lNNN rNNN` (the SmallDefs letters to the tokens).
"""
import json
import os
import re
import sys

sys.stdout.reconfigure(encoding='utf-8')
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
sys.path.insert(0, HERE)
import model  # noqa: E402
from gen_small import dec  # noqa: E402

import conv  # noqa: E402
import solve2  # noqa: E402
import sym  # noqa: E402
import tok  # noqa: E402

NL = chr(10)
LEAN_DIR = os.path.join(HERE, '..', '..', '..', 'Sec8', 'D', 'W4')


# ----------------------------------------------------------------------------- Lean parsing

def parse_tok(s):
    s = s.strip()
    m = re.fullmatch(r't([HZCKS]) (\d+)', s)
    if m:
        return ('s', m.group(1), int(m.group(2)))
    m = re.fullmatch(r'tg \.(\w+) \[([\d, ]*)\] \[(.*)\]', s)
    if m:
        tg = tuple(int(x) for x in m.group(2).split(',') if x.strip())
        cs = tuple((int(a), b == 'true') for a, b in re.findall(r'\((\d+), (true|false)\)', m.group(3)))
        return ('g', m.group(1), tg, cs)
    m = re.fullmatch(r'tp (\d+) \[(.*?)\] \[([\d, ]*)\]', s)
    if m:
        w = tuple((a, int(b)) for a, b in re.findall(r'L\.([HZCKS]) (\d+)', m.group(2)))
        ps = tuple(int(x) for x in m.group(3).split(',') if x.strip())
        return ('p', int(m.group(1)), w, ps)
    raise ValueError(s)


def split_top(s):
    """Split a Lean list body at top-level commas."""
    out, depth, cur = [], 0, ''
    for ch in s:
        if ch in '[(':
            depth += 1
        elif ch in '])':
            depth -= 1
        if ch == ',' and depth == 0:
            out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return out


def parse_word(s):
    s = s.strip()
    assert s[0] == '[' and s[-1] == ']', s
    body = s[1:-1]
    return [parse_tok(x) for x in split_top(body)] if body.strip() else []


def read_known(path):
    """name -> (L, R) for every `tNAME` with `def LNAME`, `def RNAME` in a module."""
    txt = open(path, encoding='utf-8').read()
    defs = {}
    for m in re.finditer(r'^def ([LR])(\w+) : List Tk := (\[.*?\])\n', txt, re.M | re.S):
        defs[(m.group(1), m.group(2))] = parse_word(m.group(3).replace('\n', ' '))
    out = {}
    for m in re.finditer(r'^theorem t(\w+) \(ih : IH (\d)\)', txt, re.M):
        n = m.group(1)
        if ('L', n) in defs and ('R', n) in defs:
            out[n] = (defs[('L', n)], defs[('R', n)])
    return out


# ----------------------------------------------------------------------------- chains

def diag_tokens(N, D, env):
    return conv.word(N, [dec(g) for g in D['gates']], env)


def chain_words(d, n, N, env):
    st = d['statements'][str(n)]
    L, R = diag_tokens(N, st[0], env), diag_tokens(N, st[-1], env)
    out = []
    for ch in d['proofs'].get(str(n), []):
        out.append([diag_tokens(N, D, env) for D in ch['diags']])
    return L, R, out


def full_chain(chains, L, R):
    cs = [c for c in chains if c]
    if not cs:
        return [list(L), list(R)]
    ws = list(cs[0])
    for c in cs[1:]:
        if c[0] == ws[-1]:
            ws += c[1:]
        else:
            break
    if (ws[0] == list(R) or ws[-1] == list(L)) and not (ws[0] == list(L)):
        ws = list(reversed(ws))
    return ws


class Eq:
    def __init__(self, n, L, R, steps, table):
        self.n, self.L, self.R, self.steps, self.table = n, L, R, steps, table


def compact(ctx, L, R, steps, n, M):
    """Keep the table entries used, renumbered in order of first use."""
    T, fixed = [], []
    for s in steps:
        if s[0] == 'rw':
            e = ctx.table[s[2]]
            if e not in T:
                T.append(e)
            s = ('rw', s[1], T.index(e), s[3])
        fixed.append(s)
    eng = tok.Engine(M, [(a, b) for a, b, _ in T])
    w, bad = eng.run(L, fixed)
    assert w == list(R), (n, bad, w)
    return Eq(n, L, R, fixed, T)


def solve_words(S, ws, budget=3000, log=None):
    steps = []
    for i in range(len(ws) - 1):
        S.start(budget)
        try:
            st = S.solve(ws[i], ws[i + 1])
        except solve2.Fail as e:
            raise solve2.Fail(f'step {i}: {e}')
        ok, bad = S.verify(ws[i], ws[i + 1], st)
        assert ok, (i, bad)
        if log:
            log(f'  step {i}: {len(st)} engine steps')
        steps += st
    return steps


# ----------------------------------------------------------------------------- Lean output

def lean_run(e, N, ih_n):
    name = str(e.n)
    M = N - 1
    out = []
    out.append(f'def L{name} : List Tk := {tok.lean_word(e.L)}' + NL)
    out.append(f'def R{name} : List Tk := {tok.lean_word(e.R)}' + NL)
    tbl = '[' + (',' + NL + '  ').join(f'({tok.lean_word(a)}, {tok.lean_word(b)})'
                                       for a, b, _ in e.table) + ']'
    out.append(f'def T{name} : Tbl := {tbl}' + NL)
    steps = (',' + NL + '    ').join(tok.lean_step(s) for s in e.steps)
    out.append(f'theorem run{name} : check {M} T{name} L{name} R{name}' + NL
               + f'    [{steps}] = true := by' + NL + '  decide +kernel' + NL)
    allD = f'AllD.nil {N}'
    for _, _, p in reversed(e.table):
        allD = f'AllD.cons ({p}) ({allD})'
    out.append(f'theorem t{name} (ih : IH {ih_n}) : Derivable (theory {N}) (wcT {N} L{name}) '
               f'(wcT {N} R{name}) :=' + NL + f'  check_sound ih ({allD}) run{name}' + NL)
    return NL.join(out)
