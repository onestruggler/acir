"""Derivations for Examples/Groups/XCXCCX-4bit, emitted as Engine steps.

A word is a tuple of letters (kind, shift), diagram order.  An equation
is (name, arity, lhs, rhs): lhs = rhs on the bottom `arity` wires of a
circuit of any width; at shift s it is lift⁼ applied s times.  A
derivation is a list of waypoint words; consecutive waypoints are joined
by a breadth-first search over single rewrites (any equation, any shift,
either direction, any occurrence up to commuting letters), and the
result is a list of Engine steps: `perm ys` and `rw i e`.
"""
from collections import deque
import itertools
import sys

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xc import ARITY, perm  # noqa: E402

KINDS = ('X', 'CX', 'CCX', 'SW')
KORD = {'X': 0, 'CX': 1, 'CCX': 2, 'SW': 3}


def parse(s):
    """'X1 CX0 SW2' -> (('X',1),('CX',0),('SW',2))."""
    out = []
    for tok in s.split():
        k = tok.rstrip('0123456789')
        out.append((k, int(tok[len(k):])))
    return tuple(out)


def show(w):
    return ' '.join('%s%d' % l for l in w) or 'ε'


def wires(l):
    k, s = l
    return set(range(s, s + ARITY[k]))


def dep(a, b):
    return bool(wires(a) & wires(b))


def canon(w):
    """Lexicographic normal form of the trace of w."""
    w = list(w)
    out = []
    while w:
        best = None
        for i, l in enumerate(w):
            if any(dep(w[j], l) for j in range(i)):
                continue
            key = (l[1], KORD[l[0]])
            if best is None or key < best[0]:
                best = (key, i)
        out.append(w.pop(best[1]))
    return tuple(out)


def bring_together(w, S):
    """Linearisation of w with the positions S (increasing) contiguous, in order, or None."""
    lo, hi = S[0], S[-1]
    Sset = set(S)
    before, block, after = [], [], []
    for p in range(lo, hi + 1):
        l = w[p]
        if p in Sset:
            if any(dep(a, l) for a in after):
                return None
            block.append(l)
        else:
            if not any(dep(b, l) for b in block) and not any(dep(a, l) for a in after):
                before.append(l)
            else:
                rest = [w[q] for q in S if q > p]
                if any(dep(r, l) for r in rest):
                    return None
                after.append(l)
    lin = tuple(w[:lo]) + tuple(before) + tuple(block) + tuple(after) + tuple(w[hi + 1:])
    return lin, lo + len(before)


def closure(w):
    """reach[i] = set of j > i reachable from i in the dependency DAG of w."""
    n = len(w)
    reach = [set() for _ in range(n)]
    for i in range(n - 1, -1, -1):
        for j in range(i + 1, n):
            if dep(w[i], w[j]):
                reach[i].add(j)
                reach[i] |= reach[j]
    return reach


def occurrences(w, pat):
    """(linearisation, index) for every occurrence of pat in the trace of w."""
    m = len(pat)
    if m == 0:
        for i in range(len(w) + 1):
            yield w, i
        return
    n = len(w)
    reach = closure(w)
    cands = [[p for p in range(n) if w[p] == pat[t]] for t in range(m)]

    def rec(t, acc, used):
        if t == m:
            yield list(acc)
            return
        for p in cands[t]:
            if p in used:
                continue
            ok = True
            for u in range(t):
                q = acc[u]
                # a path q -> p needs u < t (true); a path p -> q contradicts the pattern order
                if q in reach[p]:
                    ok = False
                    break
            if ok:
                acc.append(p)
                used.add(p)
                yield from rec(t + 1, acc, used)
                used.discard(p)
                acc.pop()
    seen = set()
    for S in rec(0, [], set()):
        Sset = set(S)
        succ = set()
        for s in S:
            succ |= reach[s]
        pred = set(i for i in range(n) if i not in Sset and any(s in reach[i] for s in S))
        if (succ - Sset) & pred:
            continue
        before = [w[i] for i in range(n) if i not in Sset and i not in succ]
        after = [w[i] for i in range(n) if i not in Sset and i in succ]
        lin = tuple(before) + tuple(w[s] for s in S) + tuple(after)
        r = (lin, len(before))
        if r not in seen:
            seen.add(r)
            yield r


def shifted(w, s):
    return tuple((k, x + s) for k, x in w)


class Lib:
    def __init__(self, width):
        self.width = width
        self.eqs = []   # (name, arity, lhs, rhs)

    def add(self, name, arity, lhs, rhs, check=True):
        if check:
            assert perm(lhs, arity) == perm(rhs, arity), name
        self.eqs.append((name, arity, tuple(lhs), tuple(rhs)))

    def instances(self, allow=None):
        for name, a, l, r in self.eqs:
            if allow is not None and name not in allow:
                continue
            for s in range(0, self.width - a + 1):
                L, R = shifted(l, s), shifted(r, s)
                yield (name, s, False), L, R
                yield (name, s, True), R, L


def agda_eq(name, s, rev):
    e = name
    for _ in range(s):
        e = 'lift⁼ (%s)' % e if ' ' in e else 'lift⁼ %s' % e
    if rev:
        e = 'sym⁼ (%s)' % e if ' ' in e else 'sym⁼ %s' % e
    return e


def neighbours(lib, w, maxlen, allow=None):
    for tag, P, Q in lib.instances(allow):
        for lin, i in occurrences(w, P):
            res = lin[:i] + Q + lin[i + len(P):]
            if len(res) <= maxlen:
                yield res, (lin, i, tag)


def connect(lib, a, b, depth=4, maxlen=None, allow=None):
    """Steps from a to b, iterative deepening up to `depth` rewrites."""
    last = None
    for d in range(1, depth + 1):
        try:
            return connect1(lib, a, b, d, maxlen, allow)
        except RuntimeError as e:
            last = e
    raise last


def connect1(lib, a, b, depth=4, maxlen=None, allow=None):
    """Steps from a to b: list of (lin, i, tag), at most `depth` rewrites."""
    cb = canon(b)
    if canon(a) == cb:
        return []
    if maxlen is None:
        maxlen = max(len(a), len(b)) + 4
    start = canon(a)
    prev = {start: None}
    frontier = deque([(start, 0)])
    while frontier:
        w, d = frontier.popleft()
        if d >= depth:
            continue
        for res, step in neighbours(lib, w, maxlen, allow):
            c = canon(res)
            if c in prev:
                continue
            prev[c] = (w, step)
            if c == cb:
                steps = []
                x = c
                while prev[x] is not None:
                    pw, st = prev[x]
                    steps.append(st)
                    x = pw
                return list(reversed(steps))
            frontier.append((c, d + 1))
    raise RuntimeError('no connection within depth %d: %s  ->  %s' % (depth, show(a), show(b)))


def agda_letter(l):
    k, s = l
    base = {'X': 'Xₗ', 'CX': 'CXₗ', 'CCX': 'CCXₗ', 'SW': 'σₗ'}[k]
    return base + ' ↥' * s


def agda_list(w):
    if not w:
        return '[]'
    return '(' + ' ∷ '.join(agda_letter(l) for l in w) + ' ∷ [])'


def derivation(lib, name, arity, waypoints, depth=4, allow=None, typ=None, indent='  '):
    """Agda text of a derived equation `name`, from the waypoint words."""
    ws = [parse(x) if isinstance(x, str) else tuple(x) for x in waypoints]
    lhs, rhs = ws[0], ws[-1]
    assert perm(lhs, lib.width) == perm(rhs, lib.width), (name, 'unsound')
    steps = []
    cur = lhs
    for nxt in ws[1:]:
        for lin, i, (en, s, rev) in connect(lib, cur, nxt, depth=depth, allow=allow):
            steps.append('perm %s' % agda_list(lin))
            steps.append('rw %d (%s)' % (i, agda_eq(en, s, rev)))
            P = None
            for (nm, a, l, r) in lib.eqs:
                if nm == en:
                    P, Q = (shifted(r, s), shifted(l, s)) if rev else (shifted(l, s), shifted(r, s))
            cur = lin[:i] + Q + lin[i + len(P):]
        if canon(cur) != canon(nxt):
            raise RuntimeError('waypoint mismatch at ' + show(nxt))
    if cur != rhs:
        steps.append('perm %s' % agda_list(rhs))
    nn = {1: '₁₊ n', 2: '₂₊ n', 3: '₃₊ n', 4: '₄₊ n'}[arity]
    typ = typ or 'Eqn (%s)' % nn
    body = (' ∷\n' + indent + '   ').join(steps) if steps else ''
    stl = '(' + body + ' ∷ [])' if steps else '[]'
    return ('%s : %s\n%s = derive %s\n%s%s\n%s%s\n%srefl\n' %
            (name, typ, name, agda_list(lhs), indent, agda_list(rhs), indent, stl, indent))


BASE = [
    ('r1⁼', 1, 'X0 X0', ''),
    ('r2⁼', 2, 'CX0 X1 CX0 X1', 'X0'),
    ('r3⁼', 2, 'CX0 SW0 CX0 SW0 CX0', 'SW0'),
    ('r4⁼', 3, 'CCX0 X2 CCX0 X2', 'CX0'),
    ('r5⁼', 3, 'SW1 CCX0 SW1', 'CCX0'),
    ('r6⁼', 3, 'SW0 CX0 SW0 CCX0 SW0 CX0 SW0', 'SW0 CCX0 SW0 CCX0 SW0 CCX0 SW0'),
    ('r7⁼', 4, 'CCX1 CX0 CCX1', 'SW0 CCX1 SW0 CX0'),
    ('σσ⁼', 2, 'SW0 SW0', ''),
    ('σX⁼', 2, 'X0 SW0', 'SW0 X1'),
    ('σCX⁼', 3, 'CX0 SW1 SW0', 'SW1 SW0 CX1'),
    ('σσσ⁼', 3, 'SW0 SW1 SW0', 'SW1 SW0 SW1'),
    ('σCCX⁼', 4, 'CCX0 SW2 SW1 SW0', 'SW2 SW1 SW0 CCX1'),
]


def base_lib(width, upto=None):
    lib = Lib(width)
    for nm, a, l, r in BASE:
        if a <= width:
            lib.add(nm, a, parse(l), parse(r))
    return lib
