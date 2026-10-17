# The canonical configurations of the P' rules' index tuples under the
# affine elimination (five-qubit-plan.md, "The decoding from five wires
# on"): translate the first point to 0, then each point either is in the
# span of the images so far (it keeps its image) or gets a new basis
# vector (pivot: the first set bit at or above the rank, cleared
# elsewhere, swapped to the rank).  Counts, per rule, the outputs over
# all index tuples satisfying the rule's distinctness conditions, and
# checks that the uniform gadget skeleton of every letter is correct.
import sys
from itertools import product

N4 = 4                   # images land in F_2^4; patterns are realised there


def elim(points, n=N4):
    """the canonical images of the points (tuples of bits, wire 0 first)."""
    pts = [list(p) for p in points]
    a0 = pts[0][:]
    pts = [[x ^ y for x, y in zip(p, a0)] for p in pts]
    r = 0
    for i in range(len(pts)):
        b = pts[i]
        if not any(b[r:]):
            continue
        piv = next(j for j in range(r, n) if b[j])
        # clear the other bits: CX(piv -> j) for every other set bit j
        for j in range(n):
            if j != piv and b[j]:
                for p in pts:
                    if p[piv]: p[j] ^= 1
        if piv != r:
            for p in pts:
                p[piv], p[r] = p[r], p[piv]
        r += 1
    return tuple(tuple(p) for p in pts)


# rules: (name, number of indices, predicate on the index tuple as points)
def distinct(*ix): return len(set(ix)) == len(ix)

RULES = [
    ('pp-id', 1, lambda a: True),
    ('pp-ord', 2, lambda a, b: True),
    ('pp-comm', 4, lambda a, b, c, d: True),
    ('pp-tele', 3, lambda a, b, c: True),
    ('px-sq', 2, lambda a, b: a != b),
    ('px-braid', 3, lambda a, b, c: distinct(a, b, c)),
    ('px-shrink1', 3, lambda a, b, c: distinct(a, b, c)),
    ('px-shrink2', 3, lambda a, b, c: distinct(a, b, c)),
    ('px-shrink3', 3, lambda a, b, c: distinct(a, b, c)),
    ('px-shrink4', 3, lambda a, b, c: distinct(a, b, c)),
    ('px-inv', 2, lambda a, b: a != b),
    ('px-sign', 3, lambda c, a, b: a != b),
    ('px-conj', 3, lambda a, b, c: distinct(a, b, c)),
    ('px-conj2', 2, lambda a, b: a != b),
    ('px-comm', 4, lambda a, a1, b, b1: distinct(a, a1, b, b1)),
    ('dx-split', 4, lambda a, b, c, d: a != b and c != d),
    ('ki-sink', 4, lambda a, b, s, t: a != b),
    ('ki-pp', 4, lambda a, b, s, x: a != b and x not in (a, b) and s not in (a, b)),
    ('ki-px', 5, lambda a, b, s, x, y: a != b and x != y and distinct(a, b, x, y) and s not in (a, b, x, y)),
    ('ki-ki', 5, lambda a, b, c, d, s: distinct(a, b, c, d, s)),
    ('ki-swap', 4, lambda j, k, l, s: distinct(j, k, l, s)),
    ("ki-swap'", 4, lambda j, k, l, s: distinct(j, k, l, s)),
    ('ki-x', 3, lambda a, b, s: distinct(a, b, s)),
    ('ki-16', 3, lambda a, b, s: distinct(a, b, s)),
    ('ki-ii', 3, lambda a, b, s: distinct(a, b, s)),
    ('ki-sq', 3, lambda a, b, s: distinct(a, b, s)),
    ('ki-yb', 5, lambda j, k, l, m, s: distinct(j, k, l, m, s)),
]


def count():
    pts = list(product((0, 1), repeat=N4))
    total = 0
    for name, k, ok in RULES:
        outs = set()
        for t in product(pts, repeat=k - 1):
            tup = (pts[0],) + t          # the first point at 0 loses nothing
            if ok(*tup):
                outs.add(elim(tup))
        total += len(outs)
        print(f'{name:12s} {k} indices: {len(outs)} configurations')
    print('total', total)


if __name__ == '__main__':
    count()


# The elimination as affine words (letters ('X', v), ('CX', u, v)), checked:
# each pattern's images are what the word's bit map gives.
def elim_word(points, n):
    import affine
    a0 = points[0]
    word = [('X', i) for i in range(n) if a0[i]]          # applied first
    cur = lambda p: affine.act(list(reversed(word)), p)    # word in time order
    r = 0
    pat = []
    imgs = []
    for p in points:
        b = cur(p)
        if not any(b[r:]):
            pat.append(('old', b[:r]))
            continue
        j = next(i for i in range(r, n) if b[i])
        for i in range(n):
            if i != j and b[i]:
                word.append(('CX', j, i))
        if j != r:
            word += [('CX', j, r), ('CX', r, j), ('CX', j, r)]
        pat.append(('new',))
        r += 1
    return list(reversed(word)), pat, r


def check_elim(n=6, trials=20000):
    import random, affine
    rnd = random.Random(3)
    for _ in range(trials):
        k = rnd.randint(1, 5)
        pts = [tuple(rnd.randint(0, 1) for _ in range(n)) for _ in range(k)]
        w, pat, r = elim_word(pts, n)
        assert r <= 4
        rr = 0
        for p, s in zip(pts, pat):
            img = affine.act(w, p)
            if s[0] == 'new':
                assert img == tuple(1 if i == rr else 0 for i in range(n)), (pts, pat)
                rr += 1
            else:
                assert img == tuple(s[1]) + (0,) * (n - len(s[1])), (pts, pat)
    print('elimination ok on', n, 'wires,', trials, 'random tuples')
