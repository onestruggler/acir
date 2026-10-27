"""Bidirectional search for derivations in a PROP presentation on the framework's circuits.

Letters: (gate, off) — the gate's bottom wire is `off`; scalars are (gate, off) too (a scalar
moved up `off` times).  Words are tuples in operator order (index 0 is applied last), as
`FreeMonoid.toList` in Lean.  A circuit in time order is reversed to get its operator word.

Equations carry a Lean description used to generate the `DEqn` list.
"""
from collections import deque
import itertools

class Frag:
    def __init__(self, arity, scalars, axioms, syms, lean_pres):
        self.arity = arity            # gate -> number of wires
        self.scalars = scalars        # names of 0-ary gates
        self.axioms = axioms          # name -> (k, lhs_time, rhs_time) with letters (g, off)
        self.syms = syms              # name -> (k, lhs_time, rhs_time)
        self.lean_pres = lean_pres

def span(fr, a):
    g, off = a
    k = fr.arity[g]
    if k == 0: return None
    return (off, off + k)

def apart(fr, a, b):
    sa, sb = span(fr, a), span(fr, b)
    if sa is None or sb is None: return True
    return sa[1] <= sb[0] or sb[1] <= sa[0]

def shift_word(word, p):
    return tuple((g, off + p) for (g, off) in word)

def op(time_word):
    return tuple(reversed(time_word))

def instances(fr, n, lemmas=()):
    """All equations available on n wires: (lhs_op, rhs_op, lean)."""
    eqs = []
    def place(kind, name, k, l, r):
        for m in range(0, n - k + 1):
            p = n - k - m
            # pad m keeps offsets; shiftN p adds p
            eqs.append((op(shift_word(l, p)), op(shift_word(r, p)), (kind, name, m, p)))
    for name, (k, l, r) in fr.axioms.items():
        place('ax', name, k, l, r)
    for name, (k, l, r) in fr.syms.items():
        if k <= n: place('sym', name, k, l, r)
    for name, (k, l, r) in lemmas:
        if k <= n: place('lem', name, k, l, r)
    for s in fr.scalars:
        for m in range(0, n):
            p = n - 1 - m
            eqs.append((((s, p + 1),), ((s, p),), ('scal', s, m, p)))
    return [e for e in eqs if True]

def moves(fr, word, eqs, maxlen):
    out = []
    L = len(word)
    for ei, (l, r, _) in enumerate(eqs):
        for (a, b, rev) in ((l, r, False), (r, l, True)):
            la = len(a)
            if L - la + len(b) > maxlen: continue
            if la == 0:
                for i in range(L + 1):
                    out.append((word[:i] + b + word[i:], ('rw', i, ei, rev)))
            else:
                for i in range(L - la + 1):
                    if word[i:i + la] == a:
                        out.append((word[:i] + b + word[i + la:], ('rw', i, ei, rev)))
    for i in range(L - 1):
        if word[i] != word[i + 1] and apart(fr, word[i], word[i + 1]):
            out.append((word[:i] + (word[i + 1], word[i]) + word[i + 2:], ('swap', i)))
    return out

def invert_step(step, before, after, eqs):
    """The step taking `after` back to `before`."""
    if step[0] == 'swap':
        return ('swap', step[1])
    _, i, ei, rev = step
    return ('rw', i, ei, not rev)

def search(fr, n, start, goal, lemmas=(), maxlen=14, maxnodes=2_000_000):
    eqs = instances(fr, n, lemmas)
    start, goal = tuple(start), tuple(goal)
    if start == goal: return eqs, []
    fwd = {start: None}; bwd = {goal: None}
    qf = deque([start]); qb = deque([goal])
    def path(meet):
        steps = []
        x = meet
        while fwd[x] is not None:
            prev, st = fwd[x]
            steps.append(st); x = prev
        steps.reverse()
        x = meet
        while bwd[x] is not None:
            nxt, st = bwd[x]   # st takes nxt -> x (generated from nxt); we need x -> nxt
            steps.append(invert_step(st, nxt, x, eqs)); x = nxt
        return steps
    nodes = 0
    while qf and qb:
        # expand the smaller frontier, one layer
        if len(qf) <= len(qb):
            for _ in range(len(qf)):
                w = qf.popleft()
                for w2, st in moves(fr, w, eqs, maxlen):
                    if w2 not in fwd:
                        fwd[w2] = (w, st); qf.append(w2); nodes += 1
                        if w2 in bwd: return eqs, path(w2)
        else:
            for _ in range(len(qb)):
                w = qb.popleft()
                for w2, st in moves(fr, w, eqs, maxlen):
                    if w2 not in bwd:
                        bwd[w2] = (w, st); qb.append(w2); nodes += 1
                        if w2 in fwd: return eqs, path(w2)
        if nodes > maxnodes:
            return eqs, None
    return eqs, None

def replay(fr, eqs, start, steps):
    w = tuple(start)
    for st in steps:
        if st[0] == 'swap':
            i = st[1]; assert apart(fr, w[i], w[i + 1]); w = w[:i] + (w[i + 1], w[i]) + w[i + 2:]
        else:
            _, i, ei, rev = st
            l, r, _ = eqs[ei]
            a, b = (r, l) if rev else (l, r)
            assert w[i:i + len(a)] == a, (w, st)
            w = w[:i] + b + w[i + len(a):]
    return w

def prune(eqs, steps):
    """Keep only the equations used, renumbered."""
    used = sorted({st[2] for st in steps if st[0] == 'rw'})
    ren = {e: j for j, e in enumerate(used)}
    eqs2 = [eqs[e] for e in used]
    steps2 = [st if st[0] == 'swap' else ('rw', st[1], ren[st[2]], st[3]) for st in steps]
    return eqs2, steps2
