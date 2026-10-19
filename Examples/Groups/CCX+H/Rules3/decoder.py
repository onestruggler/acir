"""The decoder: each auxiliary generator on eight levels as a list of
segments, alternating theta-words (Natural tokens) and 'H' (H on wire 0).

  X_ab  = [ W(t_ab) ]                       t_ab: W(D8) letter word of the transposition
  M_a   = [ W(k_a), H, CCX0, H, W(k_a)^-1 ]  k_a: a permutation sending 7 to a
  K_s   = [ W(r_s) th1, H, th2, H, th3 W(r_s)^-1 ]   r_s: a permutation with r(i) = s_i
  IH    = [ H ]
with K0123 = th1 H0 th2 H0 th3.  W(w) = tokens of a letter word.
"""
import json, os, itertools
from syn import M, inv, theta_word, LETW, LET, _canon_sp
from tree import mat_mul, S
import d8norm as D8
from fractions import Fraction as F
from deriv import mm, I8, NBW, d, rd

HERE = os.path.dirname(os.path.abspath(__file__))


def perm_letters(p):
    """letter word (tuple of LET names) for the pure permutation e_i -> e_{p[i]}"""
    t = tuple((p[i], 1) for i in range(8))
    return tuple(_canon_sp(t))


def lw_tokens(lw):
    out = ()
    for x in lw:
        out += LETW[x]
    return out


def lw_inv(lw):
    return tuple(reversed(lw))   # every letter is an involution


# K0123 as a matrix (columns, scaled)
def kmat(s):
    h = [[1, 1, 1, 1], [1, -1, 1, -1], [1, 1, -1, -1], [1, -1, -1, 1]]
    rows = [[F(1 if i == j else 0) for j in range(8)] for i in range(8)]
    for x, i in enumerate(s):
        for y, j in enumerate(s):
            rows[i][j] = F(h[x][y], 2)
    return [[(int(rows[i][j] * S), 0) for i in range(8)] for j in range(8)]


def find_core():
    """K0123 = th1 H0 th2 H0 th3 with short theta-words"""
    K = kmat((0, 1, 2, 3))
    best = None
    for a in NBW:
        A = mm(a, ('H0',))
        for b in NBW:
            B = mat_mul(A, mm(b, ('H0',)))
            if rd(B, K) == 0:
                c = theta_word(mat_mul(geo_T(B), K))
                cand = (a, b, c)
                if best is None or sum(map(len, cand)) < sum(map(len, best)):
                    best = cand
    return best


def geo_T(m):
    import geo
    return geo.transpose(m)


CORE = find_core()
assert mm(CORE[0], ('H0',), CORE[1], ('H0',), CORE[2]) == kmat((0, 1, 2, 3))


def r_perm(s):
    """a permutation with p(i) = s_i for i < 4, the rest in increasing order"""
    rest = [x for x in range(8) if x not in s]
    p = list(s) + rest
    return p


def k_perm(a):
    """a permutation sending 7 to a (and a to 7)"""
    p = list(range(8))
    p[7], p[a] = a, 7
    return p


def dec(gen):
    """segments of an auxiliary generator (dict from the json)"""
    g, lv = gen['gate'], gen['levels']
    if g == 'X':
        a, b = lv
        p = list(range(8)); p[a], p[b] = b, a
        return [('T', perm_letters(p))]
    if g == 'M':
        kw = perm_letters(k_perm(lv[0]))
        return [('T', kw), 'H', ('T', ('CCX0',)), 'H', ('T', lw_inv(kw))]
    if g == 'K':
        rw = perm_letters(r_perm(lv))
        return [('T', rw, CORE[0]), 'H', ('T', (), CORE[1]), 'H', ('T', (), CORE[2] + lw_tokens(lw_inv(rw)))]
    if g == 'IH':
        return ['H']
    raise ValueError(g)


def seg_tokens(sg):
    """theta-word of a segment: ('T', letterword) or ('T', letterword, tokens)"""
    out = lw_tokens(sg[1])
    if len(sg) > 2:
        out += sg[2]
    return out


def word_tokens(segs):
    out = ()
    for sg in segs:
        out += ('H0',) if sg == 'H' else seg_tokens(sg)
    return out


REL = json.load(open(os.path.join(HERE, '..', 'three_qubit_relations.json')))
AUX = REL['auxiliary_generators']

if __name__ == "__main__":
    print("core lengths", [len(x) for x in CORE])
    # check the decoder against the semantics of the generators
    bad = 0
    for i, gen in enumerate(AUX):
        segs = dec(gen)
        m = M(word_tokens(segs))
        if gen['gate'] == 'K':
            ok = m == kmat(tuple(gen['levels']))
        elif gen['gate'] == 'M':
            a = gen['levels'][0]
            ok = all((m[j][j][0] == (-S if j == a else S)) for j in range(8))
        else:
            ok = True
        bad += not ok
    print("generators", len(AUX), "bad", bad)
