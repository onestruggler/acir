#!/usr/bin/env python3
"""Derivation search for four-wire {X, CX, CCX} circuits over placed gates.

Letters are placed gates on the four wires 0..3 (wire 0 the bottom one,
bit 0 of a state): X_t, CX_{c->t} and CCX_{{a,b}->t} with black controls
(4 + 12 + 12 = 28 letters; white controls are written with X letters).
Words are in diagram order: the first letter acts first.

Steps of a derivation (what the Agda side checks):

  narrow   a block lin[i:j] of the linearisation lin of the current word,
           all of whose letters lie on one triple W of wires, is replaced
           by another word `new` on W with the same function (completeness
           on three wires);
  rule7    rule (7) under a relabelling pi of the wires, in either
           direction, at position i of the linearisation lin:
               CCX_{p3,p2->p1} CX_{p1->p0} CCX_{p3,p2->p1}
             = CCX_{p3,p2->p0} CX_{p1->p0}              (p_k = pi[k]);
           "fwd" rewrites the left side into the right side.

`lin` is always a linearisation of the current word: the same trace up to
the interchange of letters on disjoint wires.

Two engines, tried in this order for each target (`solve`):

basic (class Search): bidirectional breadth-first search over traces
  (trace canonical form, so interchange is free), with
  * narrow steps on each of the four triples, from tables of short words
    per function (breadth-first search over the 8! functions of a triple
    with its placed gates as generators): every block of consecutive
    letters on the triple is re-spelled by a shortest word, or a whole
    block by a word exposing a chosen letter at either end; and a pair
    g g is inserted next to a letter sharing a wire with g;
  * the 12 distinct instances of rule (7) (24 relabellings), both ways;
  * optionally library lemmas (all relabellings, both ways) as macro moves.

macro (class Macro): bidirectional breadth-first search over narrow-reduced
  words (every block on a triple replaced greedily by the canonical
  shortest word of its function), where one move inserts a relator word at
  a cut of the word and reduces again.  The relator words are the
  rotations of rule (7)'s relator a b a b c and of its inverse, conjugated
  by X on any set of the wires of its controls (the paper's polarity
  changes), and the relators u inv(v) of library lemmas u = v (all
  relabellings, rotations, inverses, and X on up to `lemma_polar` wires).
  The depth counts relator insertions, so the narrow glue is free; only
  insertions that cancel letters at a boundary of the cut are tried.  A
  move is expanded into basic steps by a short basic search (with the
  lemmas as exact patterns) or else by its recipe: the relator built from
  the empty word by pair insertions and one rule (7) step (or the lemma's
  own derivation), then the recorded reduction.  If the bidirectional
  macro search fails, a best-first reduction of the relator l inv(r) to
  the empty word is tried.

Scheduling (`main`): the targets run in a process pool; a job takes the
equations found so far as its lemma library, and a target that failed is
tried again once the library has grown (E1 needs E6d and E7, E3 needs E7).
At the end the targets derived with lemmas are searched once more with the
whole library (`--improve`; the meeting chosen is the one whose relators
expand to the fewest rule (7) steps), and long derivations are re-polished
(`--repolish`).  Lemma uses are always inlined, so every emitted derivation
consists of narrow and rule7 steps only.  A found derivation is shortened
(`shorten`: jumps along single narrow steps or single moves; `research`:
windows re-derived by the basic engine).

Alphabet: by default the 19 gates in which wire 0 is never a control (the
group Gamma of the paper's first certificate layer, which contains every
target); its rule (7) instances are the three with target 0.  `--set
alpha=all` uses all 28 gates (full 8! tables, all 12 instances); it is
slower and gave longer derivations (E6d: 61 steps against 30).

Every emitted derivation is re-checked by replaying its steps, twice:
`check_derivation` (the search's own trace canonical form and semantics)
and `independent_check` (its own gate semantics, and trace equivalence by
per-wire projections), whose verdict is stored in the results.

    python pg_search.py [--procs 8] [--set key=value]   # -> pg_results.json
    python pg_search.py --resume FILE --improve 1 --repolish 600
    python pg_search.py --check pg_results.json
"""
import sys
sys.dont_write_bytecode = True

import heapq  # noqa: E402
import itertools  # noqa: E402
import json  # noqa: E402
import os  # noqa: E402
import pickle  # noqa: E402
import tempfile  # noqa: E402
import time  # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))

# ---------------------------------------------------------------- letters

LETTERS = []          # ('X', t) | ('CX', c, t) | ('CCX', a, b, t), a > b
for _t in range(4):
    LETTERS.append(('X', _t))
for _c in range(4):
    for _t in range(4):
        if _c != _t:
            LETTERS.append(('CX', _c, _t))
for _t in range(4):
    _o = sorted((w for w in range(4) if w != _t), reverse=True)
    for _a, _b in itertools.combinations(_o, 2):
        LETTERS.append(('CCX', _a, _b, _t))
NL = len(LETTERS)
LIDX = {l: i for i, l in enumerate(LETTERS)}
B1 = [bytes((l,)) for l in range(NL)]
E = b''


def X(t):
    return LIDX[('X', t)]


def CX(c, t):
    return LIDX[('CX', c, t)]


def CCX(a, b, t):
    a, b = max(a, b), min(a, b)
    return LIDX[('CCX', a, b, t)]


WM = [sum(1 << w for w in LETTERS[l][1:]) for l in range(NL)]


def act(l, x):
    k = LETTERS[l]
    if k[0] == 'X':
        return x ^ (1 << k[1])
    if k[0] == 'CX':
        return x ^ (((x >> k[1]) & 1) << k[2])
    return x ^ ((((x >> k[1]) & (x >> k[2])) & 1) << k[3])


P16 = [tuple(act(l, x) for x in range(16)) for l in range(NL)]


def func(word):
    """Function of a word on the 16 states (diagram order)."""
    p = list(range(16))
    for l in word:
        q = P16[l]
        p = [q[v] for v in p]
    return tuple(p)


def name(l):
    k = LETTERS[l]
    if k[0] == 'X':
        return 'X%d' % k[1]
    if k[0] == 'CX':
        return 'CX%d>%d' % (k[1], k[2])
    return 'CCX%d%d>%d' % (k[1], k[2], k[3])


def show(w):
    return ' '.join(name(l) for l in w) or 'e'


def to_json_letter(l):
    k = LETTERS[l]
    return [k[0]] + list(k[1:])


def from_json_letter(j):
    if j[0] == 'X':
        return X(j[1])
    if j[0] == 'CX':
        return CX(j[1], j[2])
    return CCX(j[1], j[2], j[3])


def jw(w):
    return [to_json_letter(l) for l in w]


def parse(s):
    """'CX1>2 CCX32>0 X2' -> word."""
    out = []
    for tok in s.split():
        if tok.startswith('CCX'):
            out.append(CCX(int(tok[3]), int(tok[4]), int(tok[6])))
        elif tok.startswith('CX'):
            out.append(CX(int(tok[2]), int(tok[4])))
        elif tok.startswith('X'):
            out.append(X(int(tok[1])))
        else:
            raise ValueError(tok)
    return bytes(out)


def inv(w):
    """Inverse word: every letter is an involution."""
    return bytes(reversed(w))


def relabel_letter(l, s):
    """Letter l with wire w renamed s[w]."""
    k = LETTERS[l]
    if k[0] == 'X':
        return X(s[k[1]])
    if k[0] == 'CX':
        return CX(s[k[1]], s[k[2]])
    return CCX(s[k[1]], s[k[2]], s[k[3]])


def relabel(w, s):
    return bytes(relabel_letter(l, s) for l in w)


PERMS = list(itertools.permutations(range(4)))

# the gamma layer: wire 0 is never a control
GAMMA = frozenset(l for l in range(NL)
                  if LETTERS[l][0] == 'X' or 0 not in LETTERS[l][1:-1])
ALL = frozenset(range(NL))

# ---------------------------------------------------------------- traces


def canon(w):
    """Lexicographic normal form of the trace of w (letters on disjoint
    wires commute)."""
    rem = list(w)
    out = []
    wm = WM
    while rem:
        blocked = 0
        best = 99
        bi = 0
        for i, l in enumerate(rem):
            m = wm[l]
            if not (m & blocked) and l < best:
                best = l
                bi = i
            blocked |= m
            if blocked == 15:
                break
        out.append(best)
        del rem[bi]
    return bytes(out)


def reach_masks(w):
    """reach[i]: bit mask of the positions j > i reachable from i."""
    n = len(w)
    reach = [0] * n
    wm = WM
    for i in range(n - 1, -1, -1):
        mi = wm[w[i]]
        r = 0
        for j in range(i + 1, n):
            if mi & wm[w[j]]:
                r |= (1 << j) | reach[j]
        reach[i] = r
    return reach


def occurrences(w, pat, reach=None):
    """(lin, i): every convex occurrence of the word pat in the trace of w,
    with lin a linearisation of w in which lin[i:i+len(pat)] == pat."""
    n = len(w)
    m = len(pat)
    if m == 0 or m > n:
        return
    if reach is None:
        reach = reach_masks(w)
    cands = []
    for t in range(m):
        c = [p for p in range(n) if w[p] == pat[t]]
        if not c:
            return
        cands.append(c)
    pdep = [[v for v in range(u) if WM[pat[u]] & WM[pat[v]]] for u in range(m)]
    pos = [0] * m
    seen = set()

    def rec(t, used):
        if t == m:
            yield used
            return
        for p in cands[t]:
            if used >> p & 1:
                continue
            ok = True
            for v in pdep[t]:
                if pos[v] > p:
                    ok = False
                    break
            if ok:
                pos[t] = p
                yield from rec(t + 1, used | (1 << p))

    for S in rec(0, 0):
        succ = 0
        for t in range(m):
            succ |= reach[pos[t]]
        after = succ & ~S
        if after:
            bad = False
            for i in range(n):
                if (after >> i & 1) and (reach[i] & S):
                    bad = True
                    break
            if bad:
                continue
        before = bytes(w[i] for i in range(n) if not (S >> i & 1) and not (after >> i & 1))
        lin = before + bytes(pat) + bytes(w[i] for i in range(n) if after >> i & 1)
        r = (lin, len(before))
        if r not in seen:
            seen.add(r)
            yield r


_LG = {}


def lin_group(w, tm, early=True):
    """A linearisation of w emitting letters inside the wire mask tm as early
    (early=True) or as late as possible."""
    key = (w, tm, early)
    r = _LG.get(key)
    if r is not None:
        return r
    r = _lin_group(w, tm, early)
    if len(_LG) < 400000:
        _LG[key] = r
    return r


def _lin_group(w, tm, early):
    rem = list(w)
    out = []
    wm = WM
    while rem:
        blocked = 0
        pick = -1
        fallback = -1
        for i, l in enumerate(rem):
            m = wm[l]
            if not (m & blocked):
                inside = not (m & ~tm)
                if inside == early:
                    pick = i
                    break
                if fallback < 0:
                    fallback = i
            blocked |= m
            if blocked == 15:
                break
        if pick < 0:
            pick = fallback
        out.append(rem.pop(pick))
    return bytes(out)


def runs(lin, tm):
    """Maximal segments [i, j) of letters inside the wire mask tm."""
    out = []
    n = len(lin)
    i = 0
    wm = WM
    while i < n:
        if wm[lin[i]] & ~tm:
            i += 1
            continue
        j = i
        while j < n and not (wm[lin[j]] & ~tm):
            j += 1
        out.append((i, j))
        i = j
    return out


# ---------------------------------------------------------------- triples

TRIPLES = [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]
TM = [sum(1 << w for w in T) for T in TRIPLES]
TIDX = {T: i for i, T in enumerate(TRIPLES)}


def triples_of(l):
    return [ti for ti in range(4) if not (WM[l] & ~TM[ti])]


def local_perm(l, ti):
    T = TRIPLES[ti]
    out = []
    for s in range(8):
        x = 0
        for k in range(3):
            x |= ((s >> k) & 1) << T[k]
        y = act(l, x)
        out.append(sum(((y >> T[k]) & 1) << k for k in range(3)))
    return tuple(out)


LP = [[local_perm(l, ti) if not (WM[l] & ~TM[ti]) else None for l in range(NL)]
      for ti in range(4)]
ID8 = tuple(range(8))


_LF = [dict() for _ in range(4)]


def lfunc(word, ti):
    """Function of a word on triple ti, as a permutation of 8 local states."""
    c = _LF[ti]
    p = c.get(word)
    if p is not None:
        return p
    lp = LP[ti]
    p = ID8
    for l in word:
        q = lp[l]
        p = tuple(q[i] for i in p)
    if len(c) < 400000:
        c[word] = p
    return p


def lcomp(p, q):
    """first p then q"""
    return tuple(q[i] for i in p)


class Table:
    """Short words per function on one triple: shortest words up to `cap`
    (distinct traces), and a canonical one (`best`)."""

    def __init__(self, ti, alphabet, cap=6):
        self.ti = ti
        gens = [l for l in sorted(alphabet) if not (WM[l] & ~TM[ti])]
        self.gens = gens
        lp = LP[ti]
        dist = {ID8: 0}
        words = {ID8: [E]}
        frontier = [ID8]
        d = 0
        while frontier:
            nxt = []
            for p in frontier:
                wl = words[p]
                for g in gens:
                    q = lp[g]
                    p2 = tuple(q[i] for i in p)
                    dd = dist.get(p2)
                    if dd is None:
                        dist[p2] = d + 1
                        words[p2] = []
                        nxt.append(p2)
                        dd = d + 1
                    if dd == d + 1:
                        lst = words[p2]
                        if len(lst) < cap:
                            for w in wl:
                                cw = canon(w + B1[g])
                                if cw not in lst:
                                    lst.append(cw)
                                    if len(lst) >= cap:
                                        break
            frontier = nxt
            d += 1
        self.dist = dist
        self.words = words
        self.best = {p: min(ws, key=lambda w: (len(w), bin(sum(WM[l] for l in w)).count('1'), w))
                     for p, ws in words.items()}


_TABLES = {}


def tables(alpha_name, cap=6):
    key = (alpha_name, cap)
    if key in _TABLES:
        return _TABLES[key]
    cache = os.path.join(os.environ.get('PG_CACHE', tempfile.gettempdir()),
                         'pg_tables_v2_%s_%d.pickle' % (alpha_name, cap))
    tabs = None
    if os.path.exists(cache):
        try:
            with open(cache, 'rb') as fh:
                tabs = pickle.load(fh)
        except Exception:
            tabs = None
    if tabs is None:
        alpha = GAMMA if alpha_name == 'gamma' else ALL
        tabs = [Table(ti, alpha, cap) for ti in range(4)]
        try:
            with open(cache, 'wb') as fh:
                pickle.dump(tabs, fh)
        except Exception:
            pass
    _TABLES[key] = tabs
    return tabs


# ---------------------------------------------------------------- rule (7)


def r7_sides(pi):
    """Rule (7) relabelled by pi (wire k -> pi[k]): (lhs, rhs)."""
    x, y, z, t = pi[3], pi[2], pi[1], pi[0]
    a, b, c = CCX(x, y, z), CX(z, t), CCX(x, y, t)
    return bytes((a, b, a)), bytes((c, b))


R7 = {}   # (lhs, rhs) -> pi (one representative relabelling)
for _pi in PERMS:
    _l, _r = r7_sides(_pi)
    R7.setdefault((_l, _r), _pi)
R7_INSTANCES = [(l, r, pi) for (l, r), pi in R7.items()]
assert len(R7_INSTANCES) == 12
for _l, _r, _pi in R7_INSTANCES:
    assert func(_l) == func(_r)

# ---------------------------------------------------------------- steps
# A step is a tuple:
#   ('narrow', ti, lin, i, j, new)      lin[i:j] (on triple ti) -> new
#   ('rule7', pi, d, lin, i)            d = 'fwd' | 'bwd'
#   ('lemma', lid, sigma, d, lin, i)    a library equation (macro)


def step_result(st, lib=None):
    if st[0] == 'narrow':
        _, ti, lin, i, j, new = st
        return lin[:i] + new + lin[j:]
    if st[0] == 'rule7':
        _, pi, d, lin, i = st
        lhs, rhs = r7_sides(pi)
        P, Q = (lhs, rhs) if d == 'fwd' else (rhs, lhs)
        return lin[:i] + Q + lin[i + len(P):]
    _, lid, sigma, d, lin, i = st
    u, v = lib.sides(lid, sigma, d)
    return lin[:i] + v + lin[i + len(u):]


def step_reverse(st, lib=None):
    """The step run backwards (from its result to its source)."""
    if st[0] == 'narrow':
        _, ti, lin, i, j, new = st
        lin2 = lin[:i] + new + lin[j:]
        return ('narrow', ti, lin2, i, i + len(new), lin[i:j])
    if st[0] == 'rule7':
        _, pi, d, lin, i = st
        lhs, rhs = r7_sides(pi)
        P, Q = (lhs, rhs) if d == 'fwd' else (rhs, lhs)
        lin2 = lin[:i] + Q + lin[i + len(P):]
        return ('rule7', pi, 'bwd' if d == 'fwd' else 'fwd', lin2, i)
    _, lid, sigma, d, lin, i = st
    u, v = lib.sides(lid, sigma, d)
    lin2 = lin[:i] + v + lin[i + len(u):]
    return ('lemma', lid, sigma, 'bwd' if d == 'fwd' else 'fwd', lin2, i)


def step_shift(st, pre, post):
    """The step inside the context pre . _ . post."""
    if st[0] == 'narrow':
        _, ti, lin, i, j, new = st
        return ('narrow', ti, pre + lin + post, i + len(pre), j + len(pre), new)
    _, pi, d, lin, i = st
    return ('rule7', pi, d, pre + lin + post, i + len(pre))


def step_relabel(st, s):
    """The step with wire w renamed s[w]."""
    if st[0] == 'narrow':
        _, ti, lin, i, j, new = st
        T = tuple(sorted(s[w] for w in TRIPLES[ti]))
        return ('narrow', TIDX[T], relabel(lin, s), i, j, relabel(new, s))
    _, pi, d, lin, i = st
    return ('rule7', tuple(s[p] for p in pi), d, relabel(lin, s), i)


def step_json(st):
    if st[0] == 'narrow':
        _, ti, lin, i, j, new = st
        return {'kind': 'narrow', 'triple': list(TRIPLES[ti]), 'lin': jw(lin),
                'i': i, 'j': j, 'new': jw(new)}
    _, pi, d, lin, i = st
    return {'kind': 'rule7', 'perm': list(pi), 'dir': d, 'lin': jw(lin), 'i': i}


def check_derivation(lhs, rhs, steps_json):
    """Replay the steps (JSON form) from lhs and compare with rhs.
    Independent of the search: only the definitions of the moves."""
    cur = canon(lhs)
    if func(lhs) != func(rhs):
        return False, 'unsound target'
    for k, st in enumerate(steps_json):
        lin = bytes(from_json_letter(x) for x in st['lin'])
        if canon(lin) != cur:
            return False, 'step %d: lin is not a linearisation of the current word' % k
        i = st['i']
        if st['kind'] == 'narrow':
            T = tuple(st['triple'])
            if T not in TIDX:
                return False, 'step %d: bad triple' % k
            ti = TIDX[T]
            j = st['j']
            new = bytes(from_json_letter(x) for x in st['new'])
            if not (0 <= i <= j <= len(lin)):
                return False, 'step %d: bad block' % k
            old = lin[i:j]
            if any(WM[l] & ~TM[ti] for l in old + new):
                return False, 'step %d: letter off the triple' % k
            if func(old) != func(new):
                return False, 'step %d: narrow step changes the function' % k
            cur = canon(lin[:i] + new + lin[j:])
        elif st['kind'] == 'rule7':
            pi = tuple(st['perm'])
            if sorted(pi) != [0, 1, 2, 3]:
                return False, 'step %d: bad relabelling' % k
            lhs7, rhs7 = r7_sides(pi)
            P, Q = (lhs7, rhs7) if st['dir'] == 'fwd' else (rhs7, lhs7)
            if lin[i:i + len(P)] != P:
                return False, 'step %d: rule (7) does not match' % k
            cur = canon(lin[:i] + Q + lin[i + len(P):])
        else:
            return False, 'step %d: unknown kind' % k
    if cur != canon(rhs):
        return False, 'end word differs from the right-hand side'
    return True, 'ok'


# ---------------------------------------------------------------- targets

def edge_toffoli(s, s2):
    """The edge Toffoli on wires {3,2,1} for two 3-bit states (w3 w2 w1)
    differing in one wire: target that wire, controls the other two,
    black if their common value is 1, white (X before and after) if 0."""
    bits = {3: int(s[0]), 2: int(s[1]), 1: int(s[2])}
    bits2 = {3: int(s2[0]), 2: int(s2[1]), 1: int(s2[2])}
    diff = [w for w in (3, 2, 1) if bits[w] != bits2[w]]
    assert len(diff) == 1
    t = diff[0]
    cs = [w for w in (3, 2, 1) if w != t]
    xs = bytes(X(c) for c in cs if bits[c] == 0)
    return xs + B1[CCX(cs[0], cs[1], t)] + xs


GRAY = ['110', '111', '101', '100', '000', '001', '011', '010']


def make_targets():
    T = {}
    T['E1'] = (parse('CX1>2 CCX32>0 CX1>2'), parse('CCX32>0 CCX31>0'))
    T['E2'] = (parse('CCX32>1 CCX32>0'), parse('CCX32>0 CCX32>1'))
    T['E3'] = (parse('CCX32>0 CCX31>0'), parse('CCX31>0 CCX32>0'))
    T['E4'] = (parse('CCX32>0 CX1>0'), parse('CX1>0 CCX32>0'))
    T['E5'] = (parse('CX3>1 CCX32>0'), parse('CCX32>0 CX3>1'))
    C = parse('CCX32>0')
    for k in range(5):
        e = edge_toffoli(GRAY[k + 2], GRAY[k + 3])
        T['E6' + 'abcde'[k]] = (e + C, C + e)
    T['E7'] = (parse('CCX32>1 CCX31>0 CCX32>1 CCX31>0'), parse('CCX32>0'))
    T['E8'] = (parse('CCX21>0 CX3>0'), parse('CX3>0 CCX21>0'))
    for nm, (l, r) in T.items():
        assert func(l) == func(r), nm
    return T


TARGETS = make_targets()


# ---------------------------------------------------------------- lemma library

class Library:
    """Derived equations u = v with a derivation (basic steps) from u to v.
    A lemma is used in any relabelling sigma and either direction."""

    def __init__(self):
        self.items = []      # (name, u, v, steps)

    def add(self, name_, u, v, steps):
        self.items.append((name_, bytes(u), bytes(v), list(steps)))
        return len(self.items) - 1

    def sides(self, lid, sigma, d):
        _, u, v, _ = self.items[lid]
        u, v = relabel(u, sigma), relabel(v, sigma)
        return (u, v) if d == 'fwd' else (v, u)

    def derivation(self, lid, sigma, d):
        _, u, v, steps = self.items[lid]
        st = steps if d == 'fwd' else [step_reverse(s) for s in reversed(steps)]
        return [step_relabel(s, sigma) for s in st]

    def instances(self, alpha):
        """(P, Q, lid, sigma, d), one per distinct (P, Q)."""
        seen = set()
        out = []
        for lid, (_, u, v, _) in enumerate(self.items):
            for sigma in PERMS:
                for d in ('fwd', 'bwd'):
                    P, Q = self.sides(lid, sigma, d)
                    if not all(x in alpha for x in P + Q):
                        continue
                    key = (canon(P), canon(Q))
                    if key in seen:
                        continue
                    seen.add(key)
                    out.append((canon(P), Q, lid, sigma, d))
        return out


def expand(steps, lib):
    """Replace every lemma step by the lemma's derivation in context."""
    out = []
    for st in steps:
        if st[0] != 'lemma':
            out.append(st)
            continue
        _, lid, sigma, d, lin, i = st
        P, Q = lib.sides(lid, sigma, d)
        pre, post = lin[:i], lin[i + len(P):]
        for s in lib.derivation(lid, sigma, d):
            out.append(step_shift(s, pre, post))
    return out


# ---------------------------------------------------------------- search

class Search:
    """Bidirectional breadth-first search over traces."""

    def __init__(self, alpha='gamma', maxseg=6, expose=True, insert=True, cap=6,
                 lib=None, use_r7=True):
        self.alpha_name = alpha
        self.alpha = GAMMA if alpha == 'gamma' else ALL
        self.tabs = tables(alpha, cap)
        self.maxseg = maxseg
        self.expose = expose
        self.insert = insert
        self.lib = lib
        self.r7 = []
        if use_r7:
            for l, r, pi in R7_INSTANCES:
                if all(x in self.alpha for x in l + r):
                    self.r7.append((l, r, pi, 'fwd'))
                    self.r7.append((r, l, pi, 'bwd'))
        self.lem = lib.instances(self.alpha) if lib is not None else []
        self.ins_tri = {g: triples_of(g)[0] for g in self.alpha}
        self.alpha_sorted = sorted(self.alpha)

    def moves(self, w, maxlen):
        """{result: step} for every move from the canonical word w."""
        out = {}
        n = len(w)
        reach = reach_masks(w)
        for P, Q, pi, d in self.r7:
            for lin, i in occurrences(w, P, reach):
                res = canon(lin[:i] + Q + lin[i + len(P):])
                if len(res) <= maxlen and res not in out and res != w:
                    out[res] = ('rule7', pi, d, lin, i)
        for P, Q, lid, sigma, d in self.lem:
            if len(w) - len(P) + len(Q) > maxlen:
                continue
            for lin, i in occurrences(w, P, reach):
                res = canon(lin[:i] + Q + lin[i + len(P):])
                if res not in out and res != w:
                    out[res] = ('lemma', lid, sigma, d, lin, i)
        for ti in range(4):
            tm = TM[ti]
            tab = self.tabs[ti]
            words, best, gens = tab.words, tab.best, tab.gens
            lp = LP[ti]
            for lin in {lin_group(w, tm, True), lin_group(w, tm, False)}:
                for (a, b) in runs(lin, tm):
                    for i in range(a, b):
                        for j in range(i + 1, min(b, i + self.maxseg) + 1):
                            seg = lin[i:j]
                            f = lfunc(seg, ti)
                            cseg = canon(seg)
                            wl = words.get(f)
                            if wl is None:      # letters outside the table's alphabet
                                continue
                            alts = [x for x in wl if x != cseg and len(x) <= len(seg) + 1]
                            if self.expose and i == a and j == b:
                                for g in gens:
                                    q = lp[g]
                                    x1 = best.get(lcomp(q, f))
                                    if x1 is not None:
                                        alts.append(B1[g] + x1)
                                    x2 = best.get(lcomp(f, q))
                                    if x2 is not None:
                                        alts.append(x2 + B1[g])
                            for alt in alts:
                                if n - (j - i) + len(alt) > maxlen:
                                    continue
                                res = canon(lin[:i] + alt + lin[j:])
                                if res not in out and res != w:
                                    out[res] = ('narrow', ti, lin, i, j, alt)
        if self.insert and n + 2 <= maxlen:
            for p in range(n + 1):
                nb = (WM[w[p - 1]] if p > 0 else 0) | (WM[w[p]] if p < n else 0)
                for g in self.alpha_sorted:
                    if not (WM[g] & nb):
                        continue
                    gg = B1[g] + B1[g]
                    res = canon(w[:p] + gg + w[p:])
                    if res not in out:
                        out[res] = ('narrow', self.ins_tri[g], w, p, p, gg)
        return out

    def connect(self, a, b, depth, maxlen=None, time_limit=None, max_states=3000000,
                log=None):
        """Steps from a to b (at most `depth`), or None; and the depth reached."""
        ca, cb = canon(a), canon(b)
        if ca == cb:
            return [], 0
        if maxlen is None:
            maxlen = max(len(a), len(b)) + 4
        t0 = time.time()
        fwd = {ca: None}
        bwd = {cb: None}
        ff, fb = [ca], [cb]
        df = db = 0
        while df + db < depth and ff and fb:
            expand_f = len(ff) <= len(fb)
            frontier, seen, other = (ff, fwd, bwd) if expand_f else (fb, bwd, fwd)
            nxt = []
            meet = None
            for w in frontier:
                for res in self.moves(w, maxlen):
                    if res in seen:
                        continue
                    seen[res] = w
                    nxt.append(res)
                    if res in other:
                        meet = res
                        break
                if meet is not None:
                    break
                if (time_limit and time.time() - t0 > time_limit) or \
                        len(fwd) + len(bwd) > max_states:
                    if log:
                        log('  stopped at depth %d+%d (%d states, %.0fs)'
                            % (df, db, len(fwd) + len(bwd), time.time() - t0))
                    return None, df + db
            if expand_f:
                ff = nxt
                df += 1
            else:
                fb = nxt
                db += 1
            if log:
                log('  depth %d+%d: frontier %d/%d, seen %d/%d, %.1fs'
                    % (df, db, len(ff), len(fb), len(fwd), len(bwd), time.time() - t0))
            if meet is not None:
                steps = []
                x = meet
                while fwd[x] is not None:
                    pw = fwd[x]
                    steps.append(self.moves(pw, maxlen)[x])
                    x = pw
                steps.reverse()
                x = meet
                while bwd[x] is not None:
                    pw = bwd[x]
                    steps.append(step_reverse(self.moves(pw, maxlen)[x], self.lib))
                    x = pw
                return steps, df + db
        return None, df + db


# ---------------------------------------------------------------- macro engine
#
# Words are kept narrow-reduced: every block on a triple is replaced by the
# canonical shortest word of its function (greedily, until nothing gets
# shorter; then blocks are re-spelled canonically while the trace gets
# lexicographically smaller).  One move inserts a relator word at a cut of
# the word and reduces again.  The relator words are the rotations of
# rule (7)'s relator a b a b c and of its inverse, conjugated by X on any
# set of the wires x, y, z of its controls (the paper's polarity changes),
# and the relators of library lemmas.  A move is expanded into basic steps
# by a short basic search, or else by its recipe: the relator built from
# nothing by pair insertions and one rule (7) step, then the reduction.


class Normalizer:
    def __init__(self, tabs, canonical=True):
        self.tabs = tabs
        self.canonical = canonical
        self.cache = {}

    def reduce_once(self, w):
        best_eq = None
        for ti in range(4):
            tm = TM[ti]
            tab = self.tabs[ti]
            dist, bestw = tab.dist, tab.best
            for early in (True, False):
                lin = lin_group(w, tm, early)
                for (a, b) in runs(lin, tm):
                    seg = lin[a:b]
                    f = lfunc(seg, ti)
                    d = dist.get(f)
                    if d is None:
                        continue
                    if d < b - a:
                        new = bestw[f]
                        return canon(lin[:a] + new + lin[b:]), ('narrow', ti, lin, a, b, new)
                    if self.canonical and best_eq is None:
                        new = bestw[f]
                        if seg != new and canon(seg) != new:
                            res = canon(lin[:a] + new + lin[b:])
                            if res < w:
                                best_eq = (res, ('narrow', ti, lin, a, b, new))
        return best_eq

    def normalize(self, w, record=False):
        w = canon(w)
        if not record:
            r = self.cache.get(w)
            if r is not None:
                return r, None
        w0 = w
        steps = []
        while True:
            r = self.reduce_once(w)
            if r is None:
                break
            w, st = r
            steps.append(st)
        if len(self.cache) < 300000:
            self.cache[w0] = w
        return w, steps


def boundary(word, ti, left):
    """The block on triple ti at the left (left=True) or right end of the
    word: (function, length), or None."""
    tm = TM[ti]
    lin = lin_group(word, tm, left)
    if not lin:
        return None
    if left:
        k = 0
        while k < len(lin) and not (WM[lin[k]] & ~tm):
            k += 1
        return (lfunc(lin[:k], ti), k) if k else None
    k = len(lin)
    while k > 0 and not (WM[lin[k - 1]] & ~tm):
        k -= 1
    return (lfunc(lin[k:], ti), len(lin) - k) if k < len(lin) else None


def r7_relator_words(alpha, polar=True):
    """(word, recipe) for the rotations of rule (7)'s relator and its inverse,
    conjugated by X on any subset of the control wires."""
    out = []
    seen = set()
    for l, r, pi in R7_INSTANCES:
        if not all(x in alpha for x in l + r):
            continue
        A, B, C = l[0], l[1], r[0]
        R = bytes((A, B, A, B, C))
        x, y, z = pi[3], pi[2], pi[1]
        subsets = [()]
        if polar:
            subsets = [S for k in range(4) for S in itertools.combinations((x, y, z), k)]
        for rname, rr in (('R', R), ('Rinv', inv(R))):
            for k in range(5):
                rot = rr[k:] + rr[:k]
                for S in subsets:
                    XS = bytes(X(s) for s in S)
                    word = XS + rot + XS
                    key = canon(word)
                    if key in seen:
                        continue
                    seen.add(key)
                    out.append((word, ('r7', pi, rname, k, S)))
    return out


def base_relator(rec):
    """(steps from the empty word, the word r) for the base relator of a
    recipe: rule (7)'s a b a b c or its inverse, or a lemma's u inv(v)."""
    if rec[0] == 'r7':
        _, pi, rname, k, S = rec
        lhs, rhs = r7_sides(pi)
        A, B, C = lhs[0], lhs[1], rhs[0]
        if rname == 'R':
            sub = [('narrow', triples_of(C)[0], E, 0, 0, B1[C] + B1[C]),
                   ('narrow', triples_of(B)[0], B1[C] + B1[C], 1, 1, B1[B] + B1[B]),
                   ('rule7', pi, 'bwd', bytes((C, B, B, C)), 0)]
            return sub, bytes((A, B, A, B, C))
        sub = [('narrow', triples_of(A)[0], E, 0, 0, B1[A] + B1[A]),
               ('narrow', triples_of(B)[0], bytes((A, A)), 1, 1, B1[B] + B1[B]),
               ('narrow', triples_of(A)[0], bytes((A, B, B, A)), 2, 2, B1[A] + B1[A]),
               ('rule7', pi, 'fwd', bytes((A, B, A, A, B, A)), 0)]
        return sub, bytes((C, B, A, B, A))
    _, lid, sigma, d, k, S, invflag, lib = rec
    u, v = lib.sides(lid, sigma, d)
    dd = d
    if invflag:
        u, v = v, u
        dd = 'bwd' if d == 'fwd' else 'fwd'
    # v inv(v) by nested pairs, then v -> u by the lemma read backwards
    sub = []
    s = E
    for idx in range(len(v)):
        g = v[idx]
        m2 = len(s) // 2
        st = ('narrow', triples_of(g)[0], s, m2, m2, B1[g] + B1[g])
        sub.append(st)
        s = step_result(st)
    assert s == v + inv(v)
    for st in lib.derivation(lid, sigma, 'bwd' if dd == 'fwd' else 'fwd'):
        sub.append(step_shift(st, E, inv(v)))
    return sub, u + inv(v)


def recipe_steps(rec):
    """Basic steps deriving a relator word X_S rot_k(r) X_S from the empty
    word (conjugation of the base relator r by r[:k] X_S); returns
    (steps, final word as a linearisation)."""
    if rec[0] == 'r7':
        k, S = rec[3], rec[4]
    else:
        k, S = rec[4], rec[5]
    sub, r = base_relator(rec)
    XS = bytes(X(s) for s in S)
    c = r[:k] + XS
    steps = []
    cur = E
    for idx in range(len(c) - 1, -1, -1):
        g = c[idx]
        mid = len(cur) // 2
        st = ('narrow', triples_of(g)[0], cur, mid, mid, B1[g] + B1[g])
        steps.append(st)
        cur = step_result(st)
    rc = inv(c)
    assert cur == rc + c
    for st in sub:
        steps.append(step_shift(st, rc, c))
    cur = rc + r + c
    assert canon(step_result(steps[-1])) == canon(cur)
    base = len(XS)
    for t in range(k):
        p = base + (k - t)
        assert cur[p - 1] == cur[p] == r[t]
        st = ('narrow', triples_of(r[t])[0], cur, p - 1, p + 1, E)
        steps.append(st)
        cur = step_result(st)
    return steps, cur


class Macro:
    """Search over narrow-reduced words; a move inserts a relator word."""

    def __init__(self, alpha='gamma', polar=True, cap=6, canonical=True, lib=None,
                 lemma_polar=False, minsave=2):
        self.minsave = minsave
        self.alpha_name = alpha
        self.alpha = GAMMA if alpha == 'gamma' else ALL
        self.tabs = tables(alpha, cap)
        self.norm = Normalizer(self.tabs, canonical)
        self.rel = r7_relator_words(self.alpha, polar)
        self.lib = lib
        if lib is not None:
            self.rel += lemma_relator_words(lib, self.alpha, lemma_polar)
        # signatures of the relator words' boundary blocks
        self.sigL = [dict() for _ in range(4)]
        self.sigR = [dict() for _ in range(4)]
        for idx, (word, rec) in enumerate(self.rel):
            for ti in range(4):
                b = boundary(word, ti, True)
                if b is not None:
                    self.sigL[ti].setdefault(b, []).append(idx)
                b = boundary(word, ti, False)
                if b is not None:
                    self.sigR[ti].setdefault(b, []).append(idx)
        self.basic = Search(alpha, lib=None)
        self.basic_lib = None
        # rule (7) steps a relator word expands to
        lemma_r7 = [sum(1 for st in it[3] if st[0] == 'rule7') for it in lib.items] if lib else []
        self.rel_cost = [1 if rec[0] == 'r7' else max(1, lemma_r7[rec[1]]) for _, rec in self.rel]

    def cuts(self, w):
        lins = {w}
        for ti in range(4):
            lins.add(lin_group(w, TM[ti], True))
            lins.add(lin_group(w, TM[ti], False))
        out = {}
        for lin in lins:
            for k in range(len(lin) + 1):
                L, R = lin[:k], lin[k:]
                key = (canon(L), canon(R))
                if key not in out:
                    out[key] = (L, R)
        return list(out.values())

    def candidates(self, L, R, minsave=2):
        cand = set()
        for ti in range(4):
            tab = self.tabs[ti]
            dist = tab.dist
            bl = boundary(L, ti, False)
            if bl is not None:
                fL, nL = bl
                for (f, nr), idxs in self.sigL[ti].items():
                    d = dist.get(lcomp(fL, f))
                    if d is not None and nL + nr - d >= minsave:
                        cand.update(idxs)
            br = boundary(R, ti, True)
            if br is not None:
                fR, nR = br
                for (f, nr), idxs in self.sigR[ti].items():
                    d = dist.get(lcomp(f, fR))
                    if d is not None and nR + nr - d >= minsave:
                        cand.update(idxs)
        return cand

    def moves(self, w, maxlen):
        """{result: (L, R, relator index)}"""
        out = {}
        for L, R in self.cuts(w):
            for idx in self.candidates(L, R, self.minsave):
                word = self.rel[idx][0]
                res, _ = self.norm.normalize(L + word + R)
                if len(res) <= maxlen and res != w and res not in out:
                    out[res] = (L, R, idx)
        return out

    def reduce_search(self, r, maxlen, max_expand=20000, time_limit=None, log=None):
        """Best-first search from the relator word r to the empty word.
        Returns the list of macro moves [(w, L, R, idx, w')] or None."""
        t0 = time.time()
        start, _ = self.norm.normalize(r)
        if start == E:
            return [], start
        parent = {start: None}
        heap = [(len(start), 0, start)]
        cnt = 0
        while heap:
            ln, dep, w = heapq.heappop(heap)
            cnt += 1
            if cnt > max_expand or (time_limit and time.time() - t0 > time_limit):
                if log:
                    log('  stopped: %d expanded, %d seen, %.0fs' % (cnt, len(parent), time.time() - t0))
                return None, start
            for res, mv in self.moves(w, maxlen).items():
                if res in parent:
                    continue
                parent[res] = (w, mv)
                if res == E:
                    path = []
                    x = res
                    while parent[x] is not None:
                        pw, (L, R, idx) = parent[x]
                        path.append((pw, L, R, idx, x))
                        x = pw
                    path.reverse()
                    if log:
                        log('  found: %d moves, %d expanded, %.1fs' % (len(path), cnt, time.time() - t0))
                    return path, start
                heapq.heappush(heap, (len(res), dep + 1, res))
            if log and cnt % 200 == 0:
                log('  %d expanded, %d seen, best len %d, %.0fs'
                    % (cnt, len(parent), heap[0][0] if heap else -1, time.time() - t0))
        return None, start

    def bidir(self, a, b, depth, maxlen, time_limit=None, max_states=400000, log=None,
              meet_time=60, extra_levels=1):
        """Bidirectional breadth-first search between the reduced forms of a
        and b.  Once the frontiers meet, the search goes on for up to
        `extra_levels` further levels (within `meet_time` seconds) collecting
        meetings, and the path whose relators expand to the fewest rule (7)
        steps is chosen.  Returns (prefix steps a -> reduced a, macro path,
        macro path on b's side, suffix steps reduced b -> b) or None."""
        t0 = time.time()
        na, sa = self.norm.normalize(a, record=True)
        nb, sb = self.norm.normalize(b, record=True)
        fwd = {na: None}
        bwd = {nb: None}
        ff, fb = [na], [nb]
        df = db = 0
        meets = [na] if na == nb else []
        t_meet = None
        stop_level = None
        while df + db < depth and ff and fb:
            if meets and (stop_level is None or df + db >= stop_level):
                break
            expand_f = len(ff) <= len(fb)
            frontier, seen, other = (ff, fwd, bwd) if expand_f else (fb, bwd, fwd)
            nxt = []
            cut_short = False
            for w in frontier:
                for res, mv in self.moves(w, maxlen).items():
                    if res in seen:
                        continue
                    seen[res] = (w, mv)
                    nxt.append(res)
                    if res in other:
                        meets.append(res)
                        if t_meet is None:
                            t_meet = time.time()
                            stop_level = df + db + 1 + extra_levels
                if t_meet is not None and time.time() - t_meet > meet_time:
                    cut_short = True
                    break
                if (time_limit and time.time() - t0 > time_limit) or \
                        len(fwd) + len(bwd) > max_states:
                    if meets:
                        cut_short = True
                        break
                    if log:
                        log('  stopped at depth %d+%d' % (df, db))
                    return None, df + db
            if expand_f:
                ff = nxt
                df += 1
            else:
                fb = nxt
                db += 1
            if log:
                log('  depth %d+%d: frontier %d/%d, meetings %d, %.1fs'
                    % (df, db, len(ff), len(fb), len(meets), time.time() - t0))
            if cut_short:
                break
        if not meets:
            return None, df + db

        def chain(tab, x):
            out = []
            while tab[x] is not None:
                pw, (L, R, idx) = tab[x]
                out.append((pw, L, R, idx, x))
                x = pw
            return out

        def cost(m):
            mv = chain(fwd, m) + chain(bwd, m)
            return (sum(self.rel_cost[x[3]] for x in mv), len(mv))

        best = min(meets, key=cost)
        if log:
            log('  %d meetings, best cost %s' % (len(meets), cost(best)))
        fpath = chain(fwd, best)
        fpath.reverse()
        bpath = chain(bwd, best)               # pw -> x on b's side, from the meeting
        return (sa, fpath, bpath, sb), df + db

    def expand_move(self, mv, refine=0, refine_time=30):
        """Basic steps for one macro move (w, L, R, idx, w')."""
        w, L, R, idx, w2 = mv
        word, rec = self.rel[idx]
        if refine:
            st, _ = self.basic.connect(w, w2, refine, maxlen=max(len(w), len(w2)) + 4,
                                       time_limit=refine_time, max_states=300000)
            if st is not None:
                return st
            if rec[0] == 'lemma':
                # the lemma itself, by exact matching, between narrow steps
                if self.basic_lib is None:
                    self.basic_lib = Search(self.alpha_name, lib=self.lib)
                st, _ = self.basic_lib.connect(w, w2, refine, maxlen=max(len(w), len(w2)) + 6,
                                               time_limit=refine_time, max_states=300000)
                if st is not None:
                    return expand(st, self.lib)
        rs, fin = recipe_steps(rec)
        assert canon(fin) == canon(word), (rec, show(fin), show(word))
        steps = [step_shift(st, L, R) for st in rs]
        res, ns = self.norm.normalize(L + fin + R, record=True)
        assert res == w2, (show(res), show(w2))
        return steps + ns


def lemma_relator_words(lib, alpha, polar=False):
    """(word, recipe) for the relators u inv(v) of the library lemmas, their
    rotations and inverses, in all relabellings."""
    out = []
    seen = set()
    for lid, (nm, u, v, _) in enumerate(lib.items):
        for sigma in PERMS:
            uu, vv = relabel(u, sigma), relabel(v, sigma)
            if not all(x in alpha for x in uu + vv):
                continue
            r0 = uu + inv(vv)
            wires_r = sorted(set(w for l in r0 for w in LETTERS[l][1:]))
            subsets = [S for k in range(min(int(polar), len(wires_r)) + 1)
                       for S in itertools.combinations(wires_r, k)]
            for invflag in (False, True):
                rr = inv(r0) if invflag else r0
                for k in range(len(rr)):
                    rot = rr[k:] + rr[:k]
                    for S in subsets:
                        XS = bytes(X(s) for s in S)
                        word = XS + rot + XS
                        key = canon(word)
                        if key in seen:
                            continue
                        seen.add(key)
                        out.append((word, ('lemma', lid, sigma, 'fwd', k, S, invflag, lib)))
    return out


def insert_inverse_pair(u, v):
    """Steps u -> u inv(v) v (pairs of letters inserted at the end of u)."""
    steps = []
    cur = E
    for idx in range(len(v) - 1, -1, -1):
        g = v[idx]
        mid = len(cur) // 2
        st = ('narrow', triples_of(g)[0], u + cur, len(u) + mid, len(u) + mid, B1[g] + B1[g])
        steps.append(st)
        cur = step_result(st)[len(u):]
    assert cur == inv(v) + v
    return steps


def from_reduction(M, u, v, path, refine=0, log=None):
    """Basic steps u -> v from a reduction of the relator u inv(v) to the
    empty word (path of macro moves)."""
    r = u + inv(v)
    steps = insert_inverse_pair(u, v)
    _, ns = M.norm.normalize(r, record=True)
    steps += [step_shift(st, E, v) for st in ns]
    for mv in path:
        for st in M.expand_move(mv, refine=refine):
            steps.append(step_shift(st, E, v))
    return steps


def from_bidir(M, u, v, res, refine=0):
    """Basic steps u -> v from a bidirectional macro path."""
    sa, fpath, bpath, sb = res
    steps = list(sa)
    for mv in fpath:
        steps += M.expand_move(mv, refine=refine)
    for mv in bpath:   # bpath[k] = (pw, L, R, idx, x) with pw -> x towards v's side reversed
        ex = M.expand_move(mv, refine=refine)
        steps += [step_reverse(st) for st in reversed(ex)]
    steps += [step_reverse(st) for st in reversed(sb)]
    return steps


# ---------------------------------------------------------------- shortening

def narrow_link(a, b):
    """A single narrow step from the trace a to the trace b, or None."""
    a, b = list(a), list(b)
    P = []
    while True:
        found = False
        ma = minimal_positions(a)
        mb = minimal_positions(b)
        vb = {}
        for i in mb:
            vb.setdefault(b[i], i)
        for i in ma:
            if a[i] in vb:
                l = a[i]
                P.append(l)
                del a[i]
                del b[vb[l]]
                found = True
                break
        if not found:
            break
    S = []
    while True:
        found = False
        ma = maximal_positions(a)
        mb = maximal_positions(b)
        vb = {}
        for i in mb:
            vb.setdefault(b[i], i)
        for i in ma:
            if a[i] in vb:
                l = a[i]
                S.append(l)
                del a[i]
                del b[vb[l]]
                found = True
                break
        if not found:
            break
    S.reverse()
    x, y = bytes(a), bytes(b)
    sup = 0
    for l in x + y:
        sup |= WM[l]
    tis = [ti for ti in range(4) if not (sup & ~TM[ti])]
    if not tis:
        return None
    if func(x) != func(y):
        return None
    P, S = bytes(P), bytes(S)
    return ('narrow', tis[0], P + x + S, len(P), len(P) + len(x), y)


def minimal_positions(w):
    out = []
    blocked = 0
    for i, l in enumerate(w):
        if not (WM[l] & blocked):
            out.append(i)
        blocked |= WM[l]
    return out


def maximal_positions(w):
    out = []
    blocked = 0
    for i in range(len(w) - 1, -1, -1):
        if not (WM[w[i]] & blocked):
            out.append(i)
        blocked |= WM[w[i]]
    return out


def traces_of(start, steps):
    T = [canon(start)]
    for st in steps:
        T.append(canon(step_result(st)))
    return T


def shorten(start, steps, basic=None, window=60, log=None):
    """Greedy shortcuts: from each word jump to the farthest later word that
    a single narrow step (or a single basic move) reaches."""
    T = traces_of(start, steps)
    N = len(T) - 1
    last = {}
    for k, t in enumerate(T):
        last[t] = k
    out = []
    i = 0
    while i < N:
        if last[T[i]] > i:          # the word comes back later: cut the loop
            i = last[T[i]]
            continue
        best_j, best_st = i + 1, steps[i]
        for j in range(min(N, i + window), i + 1, -1):
            st = narrow_link(T[i], T[j])
            if st is not None:
                best_j, best_st = j, st
                break
        if basic is not None and best_j < min(N, i + window):
            mv = basic.moves(T[i], max(len(T[i]) + 4, 12))
            for j in range(min(N, i + window), best_j, -1):
                if T[j] in mv:
                    best_j, best_st = j, mv[T[j]]
                    break
        out.append(best_st)
        i = best_j
    if log:
        log('  shortened %d -> %d steps' % (len(steps), len(out)))
    return out


def research(start, steps, basic, depth=6, span=12, time_limit=20, total_time=300, log=None):
    """Windowed re-search: replace the steps between two words of the
    derivation by a shorter basic derivation, when one is found."""
    t0 = time.time()
    steps = list(steps)
    failed = set()
    improved = True
    while improved and time.time() - t0 < total_time:
        improved = False
        T = traces_of(start, steps)
        N = len(T) - 1
        # try the largest windows first
        for gap in range(min(span, N), 2, -1):
            if time.time() - t0 > total_time:
                break
            for i in range(0, N - gap + 1):
                j = i + gap
                if (T[i], T[j]) in failed or T[i] == T[j]:
                    continue
                d = min(depth, gap - 1)
                ml = max(max(len(T[k]) for k in range(i, j + 1)), len(T[i]) + 4)
                ml = min(ml, max(len(T[i]), len(T[j])) + 6)
                st, _ = basic.connect(T[i], T[j], d, maxlen=ml, time_limit=time_limit,
                                      max_states=400000)
                if st is not None and len(st) < gap:
                    steps = steps[:i] + st + steps[j:]
                    improved = True
                    if log:
                        log('  window %d..%d: %d -> %d steps (%d total)' % (i, j, gap, len(st), len(steps)))
                    break
                failed.add((T[i], T[j]))
                if time.time() - t0 > total_time:
                    break
            if improved:
                break
    return steps


# ---------------------------------------------------------------- driver

CONFIG = {
    'alpha': 'gamma',          # letters: 'gamma' (wire 0 never a control) or 'all'
    'basic_depth': 7,          # basic search: total depth (both sides)
    'basic_extra': 6,          # words at most max(|lhs|, |rhs|) + extra letters
    'basic_time': 150,
    'basic_states': 1000000,
    'macro_depth': 8,          # macro search: relator insertions (both sides)
    'macro_extra': 6,
    'macro_time': 600,
    'macro_time_retry': 300,   # later attempts (with lemmas) meet early or not at all
    'macro_states': 300000,
    'reduce_expand': 4000,     # best-first reduction of u inv(v): expansions
    'reduce_extra': 6,
    'reduce_time': 150,
    'lemma_polar': 1,          # lemma relators also conjugated by X on up to this many wires
    'minsave': 2,              # a relator must cancel this many letters at a boundary
    'refine': 4,               # depth of the basic search refining one macro move
    'polish_span': 10,         # windowed re-search
    'polish_depth': 6,
    'polish_window_time': 15,
    'polish_time': 400,
}


def describe_relator(M, idx):
    """A short description of the relator word M.rel[idx]: the rule (7)
    instance (relabelling, rotation, inverse, X-polarity wires) or the lemma."""
    word, rec = M.rel[idx]
    if rec[0] == 'r7':
        _, pi, rname, k, S = rec
        return {'relator': 'rule7', 'perm': list(pi), 'inverse': rname == 'Rinv', 'rotation': k,
                'x_wires': list(S)}
    _, lid, sigma, d, k, S, invflag, lib = rec
    return {'relator': 'lemma', 'lemma': lib.items[lid][0], 'relabel': list(sigma),
            'inverse': invflag, 'rotation': k, 'x_wires': list(S)}


def flat_record(nm, l, r, steps, t, info):
    js = [step_json(s) for s in steps]
    ok, msg = check_derivation(l, r, js)
    rec = {'name': nm, 'lhs': jw(l), 'rhs': jw(r), 'found': True, 'checked': ok,
           'check': msg, 'length': len(js),
           'rule7_steps': sum(1 for s in js if s['kind'] == 'rule7'),
           'narrow_steps': sum(1 for s in js if s['kind'] == 'narrow'),
           'time': round(t, 1)}
    rec.update(info)
    rec['lemmas_used'] = sorted({d['lemma'] for d in info.get('macro_relators', [])
                                 if d['relator'] == 'lemma'})
    rec['steps'] = js
    return rec


def polish(l, steps, basic, cfg, log=None):
    steps = shorten(l, steps, basic=basic)
    steps = research(l, steps, basic, depth=cfg['polish_depth'], span=cfg['polish_span'],
                     time_limit=cfg['polish_window_time'], total_time=cfg['polish_time'], log=log)
    return shorten(l, steps, basic=basic)


def solve(nm, l, r, cfg, lib=None, log=None):
    """Search for a derivation of l = r: the basic search first, then the
    macro search (bidirectional, then by reduction of the relator), with
    the lemmas of `lib` as extra relators.  Returns a record (dict)."""
    t0 = time.time()
    alpha = cfg['alpha']
    tried = []
    basic = Search(alpha)
    # 1. basic bidirectional search
    if cfg['basic_depth'] > 0:
        st, d = basic.connect(l, r, cfg['basic_depth'], maxlen=max(len(l), len(r)) + cfg['basic_extra'],
                              time_limit=cfg['basic_time'], max_states=cfg['basic_states'])
        tried.append({'engine': 'basic', 'depth_reached': d, 'found': st is not None,
                      'time': round(time.time() - t0, 1)})
        if st is not None:       # shortest within the basic moves: only cut loops
            steps = shorten(l, st, basic=basic)
            return flat_record(nm, l, r, steps, time.time() - t0,
                               {'engine': 'basic', 'search_depth': d, 'tried': tried})
    # 2. macro search, bidirectional
    M = Macro(alpha, lib=lib, lemma_polar=cfg['lemma_polar'], minsave=cfg['minsave'])
    t1 = time.time()
    res, d = M.bidir(l, r, cfg['macro_depth'], max(len(l), len(r)) + cfg['macro_extra'],
                     time_limit=cfg['macro_time'], max_states=cfg['macro_states'], log=log)
    tried.append({'engine': 'macro-bidir', 'depth_reached': d, 'found': res is not None,
                  'time': round(time.time() - t1, 1)})
    if res is not None:
        sa, fp, bp, sb = res
        steps = from_bidir(M, l, r, res, refine=cfg['refine'])
        steps = polish(l, steps, basic, cfg, log)
        return flat_record(nm, l, r, steps, time.time() - t0,
                           {'engine': 'macro-bidir', 'macro_moves': len(fp) + len(bp),
                            'macro_relators': [describe_relator(M, mv[3]) for mv in fp + bp],
                            'lemmas': [x[0] for x in lib.items] if lib else [],
                            'search_depth': d, 'tried': tried})
    # 3. macro search, best-first reduction of the relator l inv(r)
    t1 = time.time()
    path, _ = M.reduce_search(l + inv(r), max(len(l), len(r)) * 2 + cfg['reduce_extra'],
                              max_expand=cfg['reduce_expand'], time_limit=cfg['reduce_time'], log=log)
    tried.append({'engine': 'macro-reduce', 'found': path is not None,
                  'time': round(time.time() - t1, 1)})
    if path is not None:
        steps = from_reduction(M, l, r, path, refine=cfg['refine'])
        steps = polish(l, steps, basic, cfg, log)
        return flat_record(nm, l, r, steps, time.time() - t0,
                           {'engine': 'macro-reduce', 'macro_moves': len(path),
                            'macro_relators': [describe_relator(M, mv[3]) for mv in path],
                            'lemmas': [x[0] for x in lib.items] if lib else [],
                            'tried': tried})
    return {'name': nm, 'lhs': jw(l), 'rhs': jw(r), 'found': False,
            'time': round(time.time() - t0, 1), 'tried': tried}


def _job(job):
    nm, l, r, cfg, lib_items = job
    lib = None
    if lib_items:
        lib = Library()
        for it in lib_items:
            lib.add(*it)
    try:
        return solve(nm, l, r, cfg, lib)
    except Exception:      # report, do not lose the other targets
        import traceback
        return {'name': nm, 'lhs': jw(l), 'rhs': jw(r), 'found': False,
                'error': traceback.format_exc()[-2000:]}


def _polish_job(job):
    """Re-polish a found derivation with a larger budget."""
    nm, l, r, steps_js, cfg, seconds = job
    t0 = time.time()
    basic = Search(cfg['alpha'])
    steps = steps_from_json(steps_js)
    c = dict(cfg)
    c['polish_time'] = seconds
    c['polish_span'] = max(cfg['polish_span'], 14)
    new = polish(l, steps, basic, c)
    return nm, [step_json(st) for st in new], time.time() - t0


def steps_from_json(js):
    out = []
    for st in js:
        lin = bytes(from_json_letter(x) for x in st['lin'])
        if st['kind'] == 'narrow':
            out.append(('narrow', TIDX[tuple(st['triple'])], lin, st['i'], st['j'],
                        bytes(from_json_letter(x) for x in st['new'])))
        else:
            out.append(('rule7', tuple(st['perm']), st['dir'], lin, st['i']))
    return out


CONVENTIONS = {
    'wires': "wire 0 is the bottom wire (bit 0 of a state); the paper's wires 1,2,3,4 are 3,2,1,0",
    'order': 'diagram order: the first letter of a word acts first',
    'letters': '["X",t], ["CX",c,t], ["CCX",a,b,t] (controls a > b, then target), black controls',
    'narrow': 'lin[i:j] (all letters on the triple) is replaced by new (a word on the triple with '
              'the same function)',
    'rule7': 'perm p: CCX_{p3,p2->p1} CX_{p1->p0} CCX_{p3,p2->p1} = CCX_{p3,p2->p0} CX_{p1->p0}; '
             'fwd rewrites the left side at lin[i:i+3] into the right side, bwd the right side at '
             'lin[i:i+2] into the left side',
    'lin': 'a linearisation of the current word (the same trace up to interchange of letters on '
           'disjoint wires); the next word is lin with the block replaced; the last word equals '
           'rhs up to interchange',
}


def independent_check(path):
    """Re-check every derivation of a results file with code of its own:
    gate semantics on the 16 states, trace equivalence by projections (two
    words are the same trace exactly when, for every wire, the letters
    touching that wire come in the same order), narrow steps by wires and
    semantics, rule (7) by its definition.  Returns {name: (ok, message)}."""

    def gate(j):
        k = j[0]
        if k == 'X':
            return (), j[1]
        if k == 'CX':
            return (j[1],), j[2]
        if k == 'CCX':
            if len(j) != 4 or j[1] == j[2]:
                raise ValueError('bad letter %r' % (j,))
            return (j[1], j[2]), j[3]
        raise ValueError('bad letter %r' % (j,))

    def wires(j):
        cs, t = gate(j)
        ws = set(cs) | {t}
        if len(ws) != len(cs) + 1 or not ws <= {0, 1, 2, 3}:
            raise ValueError('bad letter %r' % (j,))
        return ws

    def run(word):
        out = []
        for x in range(16):
            for j in word:
                cs, t = gate(j)
                if all((x >> c) & 1 for c in cs):
                    x ^= 1 << t
            out.append(x)
        return out

    def key(j):                    # CCX controls are an unordered pair
        if j[0] == 'CCX':
            return ('CCX', max(j[1], j[2]), min(j[1], j[2]), j[3])
        return tuple(j)

    def same_trace(u, v):
        if sorted(map(key, u)) != sorted(map(key, v)):
            return False
        for w in range(4):
            if [key(j) for j in u if w in wires(j)] != [key(j) for j in v if w in wires(j)]:
                return False
        return True

    def r7(p, d):
        a = ['CCX', p[3], p[2], p[1]]
        b = ['CX', p[1], p[0]]
        c = ['CCX', p[3], p[2], p[0]]
        lhs, rhs = [a, b, a], [c, b]
        return (lhs, rhs) if d == 'fwd' else (rhs, lhs)

    def same_letter(x, y):
        if x[0] != y[0]:
            return False
        if x[0] == 'CCX':
            return {x[1], x[2]} == {y[1], y[2]} and x[3] == y[3]
        return list(x) == list(y)

    with open(path) as fh:
        data = json.load(fh)
    report = {}
    for rec in data['targets']:
        nm = rec['name']
        if not rec.get('found'):
            report[nm] = (None, 'no derivation')
            continue
        try:
            lhs, rhs = rec['lhs'], rec['rhs']
            if run(lhs) != run(rhs):
                raise ValueError('the two sides have different functions')
            cur = [list(j) for j in lhs]
            for k, st in enumerate(rec['steps']):
                lin = [list(j) for j in st['lin']]
                if not same_trace(lin, cur):
                    raise ValueError('step %d: lin is not the current word up to interchange' % k)
                i = st['i']
                if st['kind'] == 'narrow':
                    T = set(st['triple'])
                    j_ = st['j']
                    new = [list(x) for x in st['new']]
                    if len(T) != 3 or not T <= {0, 1, 2, 3} or not 0 <= i <= j_ <= len(lin):
                        raise ValueError('step %d: bad narrow step' % k)
                    if any(not wires(x) <= T for x in lin[i:j_] + new):
                        raise ValueError('step %d: letter off the triple' % k)
                    if run(lin[i:j_]) != run(new):
                        raise ValueError('step %d: narrow step changes the function' % k)
                    cur = lin[:i] + new + lin[j_:]
                elif st['kind'] == 'rule7':
                    p = st['perm']
                    if sorted(p) != [0, 1, 2, 3] or st['dir'] not in ('fwd', 'bwd'):
                        raise ValueError('step %d: bad rule (7) step' % k)
                    P_, Q_ = r7(p, st['dir'])
                    seg = lin[i:i + len(P_)]
                    if len(seg) != len(P_) or not all(same_letter(x, y) for x, y in zip(seg, P_)):
                        raise ValueError('step %d: rule (7) does not match' % k)
                    cur = lin[:i] + Q_ + lin[i + len(P_):]
                else:
                    raise ValueError('step %d: unknown kind' % k)
            if not same_trace(cur, [list(j) for j in rhs]):
                raise ValueError('the last word is not the right-hand side up to interchange')
            report[nm] = (True, 'ok, %d steps' % len(rec['steps']))
        except ValueError as e:
            report[nm] = (False, str(e))
    return report


def main(argv):
    import argparse
    from multiprocessing import Pool
    ap = argparse.ArgumentParser(description='Derivation search over placed gates on four wires.')
    ap.add_argument('--targets', default='E4,E8,E2,E5,E6a,E6d,E6b,E6c,E6e,E7,E3,E1',
                    help='targets, in the order in which they are scheduled')
    ap.add_argument('--procs', type=int, default=8)
    ap.add_argument('--out', default=os.path.join(HERE, 'pg_results.json'))
    ap.add_argument('--attempts', type=int, default=4,
                    help='attempts per target; a target is retried once the lemma library '
                         'has grown since its last attempt')
    ap.add_argument('--set', action='append', default=[],
                    help='override a CONFIG entry, e.g. --set macro_depth=10')
    ap.add_argument('--resume', metavar='FILE',
                    help='start from the (re-checked) derivations of an earlier results file')
    ap.add_argument('--repolish', type=int, default=0, metavar='SECONDS',
                    help='at the end, re-polish every derivation longer than 9 steps for this long')
    ap.add_argument('--improve', type=int, default=1,
                    help='re-run targets derived with lemmas with the whole library at the end')
    ap.add_argument('--check', metavar='FILE',
                    help='only re-check the derivations of a results file')
    args = ap.parse_args(argv)
    for nm, (l, r) in TARGETS.items():
        assert func(l) == func(r), nm         # every target is semantically true
    if args.check:
        for nm, (ok, msg) in independent_check(args.check).items():
            print('%-4s %s %s' % (nm, {True: 'OK  ', False: 'FAIL', None: '--  '}[ok], msg))
        return
    cfg = dict(CONFIG)
    for kv in args.set:
        k, v = kv.split('=', 1)
        cfg[k] = v if isinstance(CONFIG[k], str) else type(CONFIG[k])(v)
    names = args.targets.split(',')
    results = {}
    attempts = {nm: [] for nm in names}       # library sizes at the attempts
    lib_items = []                            # (name, lhs, rhs, steps)
    t0 = time.time()
    if args.resume:                           # derivations found by an earlier run
        with open(args.resume) as fh:
            old_data = json.load(fh)
        checks = independent_check(args.resume)
        for rec in old_data['targets']:
            nm = rec['name']
            if rec.get('found') and checks.get(nm, (False,))[0] and nm in attempts:
                results[nm] = rec
                attempts[nm].append(0)
                lib_items.append((nm, TARGETS[nm][0], TARGETS[nm][1], steps_from_json(rec['steps'])))
        print('resumed: %s' % ','.join(x[0] for x in lib_items), flush=True)

    def lib_snapshot():
        return list(lib_items)

    def runnable():
        out = []
        for nm in names:
            if results.get(nm, {}).get('found') or nm in running:
                continue
            a = attempts[nm]
            if len(a) >= args.attempts:
                continue
            if a and a[-1] >= len(lib_items):
                continue                      # nothing new to try with
            out.append(nm)
        return out

    running = {}
    log_lines = []

    def say(s):
        print(s, flush=True)
        log_lines.append(s)

    with Pool(args.procs) as pool:
        while True:
            for nm in runnable():
                if len(running) >= args.procs:
                    break
                rcfg = dict(cfg)
                if attempts[nm]:              # the basic search has had its chance
                    rcfg['basic_depth'] = 0
                    rcfg['macro_time'] = cfg['macro_time_retry']
                    rcfg['reduce_time'] = min(cfg['reduce_time'], 60)
                attempts[nm].append(len(lib_items))
                snap = lib_snapshot()
                say('[%5.0fs] start %s (attempt %d, lemmas: %s)'
                    % (time.time() - t0, nm, len(attempts[nm]), ','.join(x[0] for x in snap) or '-'))
                running[nm] = pool.apply_async(_job, ((nm, TARGETS[nm][0], TARGETS[nm][1], rcfg, snap),))
            if not running:
                break
            done = [nm for nm, ar in running.items() if ar.ready()]
            if not done:
                time.sleep(2)
                continue
            for nm in done:
                rec = running.pop(nm).get()
                rec['attempt'] = len(attempts[nm])
                prev = results.get(nm)
                if rec.get('found') or prev is None:
                    if prev is not None and 'tried' in prev:
                        rec['earlier_attempts'] = prev.get('earlier_attempts', []) + [prev['tried']]
                    results[nm] = rec
                else:
                    prev.setdefault('earlier_attempts', []).append(rec.get('tried', rec.get('error')))
                if rec.get('found') and rec.get('checked'):
                    lib_items.append((nm, TARGETS[nm][0], TARGETS[nm][1], steps_from_json(rec['steps'])))
                    msg = 'found, %d steps (%d rule7), %s, %.0fs, %s' % (
                        rec['length'], rec['rule7_steps'], rec['check'], rec['time'], rec.get('engine'))
                else:
                    msg = 'not found (%s)' % (rec.get('tried') or rec.get('error'))
                say('[%5.0fs] %s: %s' % (time.time() - t0, nm, msg))
        if args.improve:
            # targets derived with lemmas: once more with the whole library
            # (the search prefers relators that expand to fewer rule (7) steps)
            jobs = {}
            for nm in names:
                rec = results.get(nm)
                if not rec or not rec.get('found') or not rec.get('lemmas'):
                    continue
                snap = [it for it in lib_items if it[0] != nm]
                if len(snap) <= len(rec['lemmas']):
                    continue
                rcfg = dict(cfg)
                rcfg['basic_depth'] = 0
                rcfg['macro_time'] = cfg['macro_time_retry']
                say('[%5.0fs] improve %s (lemmas: %s)' % (time.time() - t0, nm, ','.join(x[0] for x in snap)))
                jobs[nm] = pool.apply_async(_job, ((nm, TARGETS[nm][0], TARGETS[nm][1], rcfg, snap),))
            for nm, ar in jobs.items():
                rec = ar.get()
                old = results[nm]
                if rec.get('found') and rec.get('checked') and rec['length'] < old['length']:
                    rec['attempt'] = old.get('attempt')
                    rec['improved_from'] = old['length']
                    results[nm] = rec
                    say('[%5.0fs] %s: improved %d -> %d steps' % (time.time() - t0, nm, old['length'], rec['length']))
                else:
                    say('[%5.0fs] %s: kept %d steps (%s)' % (time.time() - t0, nm, old['length'],
                                                             rec.get('length', 'not found')))
        if args.repolish > 0:
            jobs = []
            for nm in names:
                rec = results.get(nm)
                if rec and rec.get('found') and rec['length'] > 9:
                    jobs.append((nm, TARGETS[nm][0], TARGETS[nm][1], rec['steps'], cfg, args.repolish))
            for nm, js, t in pool.imap_unordered(_polish_job, jobs):
                rec = results[nm]
                ok, msg = check_derivation(TARGETS[nm][0], TARGETS[nm][1], js)
                if ok and len(js) < rec['length']:
                    say('[%5.0fs] %s: re-polished %d -> %d steps (%.0fs)' % (time.time() - t0, nm, rec['length'], len(js), t))
                    rec['polished_from'] = rec['length']
                    rec['steps'] = js
                    rec['length'] = len(js)
                    rec['rule7_steps'] = sum(1 for x in js if x['kind'] == 'rule7')
                    rec['narrow_steps'] = sum(1 for x in js if x['kind'] == 'narrow')
                    rec['checked'], rec['check'] = ok, msg
                else:
                    say('[%5.0fs] %s: re-polish kept %d steps' % (time.time() - t0, nm, rec['length']))
    out = {'conventions': CONVENTIONS, 'config': cfg, 'total_time': round(time.time() - t0, 1),
           'log': log_lines,
           'targets': [results[nm] for nm in TARGETS if nm in results]}
    with open(args.out, 'w') as fh:
        json.dump(out, fh, indent=1)
    # an independent re-check of what was written (own semantics, own trace test)
    report = independent_check(args.out)
    for rec in out['targets']:
        ok, msg = report.get(rec['name'], (None, 'missing'))
        rec['independent_check'] = msg if ok is not None else 'no derivation'
        if ok is False:
            rec['checked'] = False
        say('  %-4s %s' % (rec['name'], rec['independent_check']))
    out['summary'] = [
        {k: rec.get(k) for k in ('name', 'found', 'length', 'rule7_steps', 'narrow_steps', 'time',
                                 'engine', 'macro_moves', 'lemmas_used', 'attempt', 'independent_check')}
        if rec.get('found') else
        {'name': rec['name'], 'found': False,
         'depth_reached': {t.get('engine'): t.get('depth_reached') for t in rec.get('tried', [])},
         'error': rec.get('error')}
        for rec in out['targets']]
    with open(args.out, 'w') as fh:
        json.dump(out, fh, indent=1)
    say('wrote %s (%.0fs)' % (args.out, time.time() - t0))


if __name__ == '__main__':
    main(sys.argv[1:])
