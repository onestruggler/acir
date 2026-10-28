"""Relations derived by normalisation (Lemma 5.4 and Proposition 5.7).

Relation 71 (`CXZ B₈`, corrected) resists both the supplement's derivation
(its (5.6)-(5.8) fail) and the relator search (`derive.collapse`).  It is
derived here the way the paper derives everything: its relator `l r⁻¹`,
put before a normal form `N`, is rewritten into `N` by the other typed
relations of Appendix B, which the normalisation of Section 5.1 never
needs relation 71 for on this input.  So `l r⁻¹ N = N`, hence `l r⁻¹ = 1`
(`Holds.of_absorb`) and `l = r` (`Holds.of_relator`).

The rewriting is the push procedure of `Push.lean` on a flat word: the
rightmost dirty gate is moved right, past the boxes on other wires, to the
first box it meets, and the typed relation for that gate and box (or two
boxes) replaces them, its dirty gates in the form `tables.dirty` gives
(as in `Tables.lean`); two equal involutions that meet cancel.  `N` (a
normal form on three wires, `NF71`) was chosen by a search over normal
forms and rotations of the relator for a short derivation (`search`).
Each rewrite becomes `engine` steps with the relation's typed equation.
"""
import random

import derive
import engine
import paper
from engine import Deriv, canon, strip_w
from tables import TA, bty, dirty, split, tB

CLEAN = ('A', 'B', 'C', 'D', 'E')

# A normal form on three wires, as boxes (kind, index, lowest wire).
NF71 = [('A', 1, 2), ('C', 1, 2), ('D', 2, 1), ('D', 1, 0), ('E', 1, 0), ('A', 2, 1),
        ('B', 1, 1), ('C', 1, 2), ('D', 3, 1), ('E', 1, 1), ('A', 2, 2), ('C', 2, 2),
        ('E', 1, 2)]


def wires(t):
    k = t[0]
    if k == 'neg':
        return set()
    if k in ('A', 'C', 'E'):
        return {t[2]}
    if k in ('B', 'D'):
        return {t[2], t[2] + 1}
    if k in ('CZ', 'CXZ'):
        return {t[1], t[1] + 1}
    return {t[1]}


def shift(t, s):
    if t[0] == 'neg':
        return t
    if t[0] in CLEAN:
        return (t[0], t[1], t[2] + s)
    return (t[0], t[1] + s)


def letters(t):
    k = t[0]
    if k in CLEAN:
        n = 2 if k in ('B', 'D') else 1
        return paper.expand([('box', k, t[1], tuple(range(t[2], t[2] + n)))])
    if k == 'neg':
        return [('m',)]
    w = t[1]
    return {'H': [('H', w)], 'Z': [('Z', w)], 'X': [('H', w), ('Z', w), ('H', w)],
            'CZ': [('C', w)], 'CXZ': [('H', w + 1), ('C', w), ('H', w + 1), ('C', w)]}[k]


def word(tokens):
    return [a for t in tokens for a in letters(t)]


def from_letters(ls):
    return [('neg',) if a[0] == 'm' else ('CZ', a[1]) if a[0] == 'C' else a for a in ls]


def box_token(g):
    return (g[1], g[2], min(g[3]))


def rules(recs):
    """The typed relations of Figures 3-9 as rewrite rules: the dirty gate
    and boxes on the left (in the relation's frame) to the boxes and dirty
    gates on the right."""
    out = {}
    for rec in recs:
        num, fig = rec[0], rec[1]
        if not 3 <= fig <= 9:
            continue
        lg, rb, rd, rn = split(rec)
        g = lg[0]
        if g[0] == 'CZ':
            g = ('CZ', min(g[1], g[2]))
        elif g[0] == 'CXZ':
            assert g[1] == g[2] + 1, num
            g = ('CXZ', g[2])
        lb = tuple(box_token(b) for b in lg[1:])
        rbt = [box_token(b) for b in rb]
        last = rbt[-1]
        cur, dbl = None, False
        if last[0] == 'B':
            cur, dbl = last[2] + 1, tB(*bty(last[1]))
        elif last[0] == 'A':
            cur, dbl = last[2], TA[last[1]]
        out[(g, lb)] = (rbt, dirty(rd, rn, cur, dbl), num)
    return out


def step(tokens, R):
    """One rewrite of the rightmost dirty gate: (tokens, relation number or
    'cancel'), or None when no dirty gate is left."""
    idx = None
    for p in range(len(tokens) - 1, -1, -1):
        if tokens[p][0] not in CLEAN and tokens[p][0] != 'neg':
            idx = p
            break
    if idx is None:
        return None
    g = tokens[idx]
    gw = wires(g)
    # two equal involutions meet
    if g[0] in ('H', 'Z', 'CZ', 'X'):
        q = idx - 1
        while q >= 0 and not (wires(tokens[q]) & gw):
            q -= 1
        if q >= 0 and tokens[q] == g:
            return tokens[:q] + tokens[q + 1:idx] + tokens[idx + 1:], 'cancel'
    q = idx + 1
    while not (wires(tokens[q]) & gw):
        q += 1
    for nb in (1, 2):
        boxes = tokens[q:q + nb]
        s = min(min(wires(t)) for t in [g] + boxes)
        key = (shift(g, -s), tuple(shift(b, -s) for b in boxes))
        if key in R:
            rb, out, num = R[key]
            new = [shift(b, s) for b in rb] + [shift(o, s) for o in out]
            return tokens[:idx] + tokens[idx + 1:q] + new + tokens[q + nb:], num
    raise ValueError('no relation for', g, tokens[q:q + 2])


def normalise(tokens, R):
    trace, used = [], []
    while True:
        r = step(tokens, R)
        if r is None:
            return trace, used
        tokens, n = r
        trace.append(tokens)
        used.append(n)


def nid(n, s=0):
    """The normal form of the identity on the wires s, ..., s + n - 1."""
    if n == 0:
        return []
    return ([('A', 1, s)] + [('B', 1, c) for c in range(s, s + n - 1)] + [('C', 1, s + n - 1)] +
            [('D', 1, c) for c in range(s + n - 2, s - 1, -1)] + [('E', 1, s)] + nid(n - 1, s + 1))


def search(L, R, recs, k=3, tries=4000, seed=11):
    """A normal form and a rotation of the relator of l = r with a short
    normalisation that does not use l = r: how NF71 was found."""
    rules_ = rules(recs)
    rel = L + R[::-1]
    rng = random.Random(seed)
    best = None
    seen = set()
    for _ in range(tries):
        ls = [('C', rng.randrange(k - 1)) if c == 'C' else (c, rng.randrange(k))
              for c in (rng.choice('HZC') for _ in range(rng.randint(5, 60)))]
        trace, _ = normalise(from_letters(ls) + nid(k), rules_)
        N = tuple(t for t in trace[-1] if t[0] != 'neg')
        if N in seen:
            continue
        seen.add(N)
        for i in range(len(rel)):
            trace, used = normalise(from_letters(rel[i:] + rel[:i]) + list(N), rules_)
            cost = sum(1 for u in used if u != 'cancel')
            if best is None or cost < best[0]:
                best = (cost, i, list(N))
    return best


def derivation(num, recs, tnames, N=NF71):
    """A derivation of `l r⁻¹ N = N` for relation `num` by the other typed
    relations: (k, first word, last word, steps)."""
    R = {r[0]: r for r in recs}
    _, _, _, (lg, ln), (rg, rn), _ = R[num]
    L, Rw = derive.letters(lg, ln), derive.letters(rg, rn)
    first = L + Rw[::-1] + word(N)
    trace, used = normalise(from_letters(L + Rw[::-1]) + list(N), rules(recs))
    assert num not in used
    assert [t for t in trace[-1] if t[0] != 'neg'] == list(N)
    k = max(paper.width(first), 1)
    d = Deriv(first, k)
    for u, toks in zip(used, trace):
        names = ['R2', 'R3', 'R5'] if u == 'cancel' else [tnames[u]]
        if not (engine.try_step(d, names, word(toks)) or derive.solve_inv(d, word(toks))):
            raise ValueError('step not found', num, u)
    last = word(N)
    derive.reorder_to_canon(d, last)
    assert d.word == last
    return k, first, last, d.steps
