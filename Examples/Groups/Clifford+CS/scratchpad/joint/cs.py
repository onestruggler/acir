# Semantics of Clifford+CS circuits on N wires, by fingerprints over F_p.
#
# A word is a list of gates; the generators are ('iI',), ('S', w),
# ('K', w), ('CS', a, b) (any two wires), and the macros of derivn.py
# expand to them (to_generators).  Operators are compared by applying
# the word to two fixed random vectors over F_p, p = 998244353
# (p = 1 mod 4, so i = sqrt(-1) and 1/(1+i) live in F_p).  Words are
# matrix products, the last letter acting first; every gate is a
# symmetric matrix, so the other reading gives the transposes and the
# same equations.  Wire w is bit w of a basis index.
import random

P = 998244353
I = pow(3, (P - 1) // 4, P)
assert I * I % P == P - 1
GINV = pow((1 + I) % P, P - 2, P)          # 1/(1+i)
MI = P - I                                 # -i


def bit(x, w):
    return (x >> w) & 1


class Sem:
    def __init__(self, n, seed=7, nvec=2):
        self.n = n
        self.dim = 1 << n
        rnd = random.Random(seed)
        self.vecs = [[rnd.randrange(P) for _ in range(self.dim)] for _ in range(nvec)]

    # ----------------------------------------------------- one gate
    def apply(self, g, v):
        k = g[0]; D = self.dim
        if k == 'iI':
            return [I * a % P for a in v]
        if k == 'iIi':
            return [MI * a % P for a in v]
        if k in ('S', 'Sd', 'Z'):
            w = g[1]; c = {'S': I, 'Sd': MI, 'Z': P - 1}[k]
            return [c * a % P if bit(x, w) else a for x, a in enumerate(v)]
        if k == 'X':
            m = 1 << g[1]
            return [v[x ^ m] for x in range(D)]
        if k in ('K', 'Kd'):
            w = g[1]; m = 1 << w; out = [0] * D
            for x in range(D):
                if x & m: continue
                y = x | m; a, b = v[x], v[y]
                out[x] = GINV * (a + b) % P; out[y] = GINV * (a - b) % P
            if k == 'Kd':
                out = [I * a % P for a in out]          # K^-1 = i K
            return out
        if k in ('CS', 'CSd', 'CZ'):
            a_, b_ = g[1], g[2]; c = {'CS': I, 'CSd': MI, 'CZ': P - 1}[k]
            return [c * e % P if bit(x, a_) and bit(x, b_) else e for x, e in enumerate(v)]
        if k == 'CX':
            c_, t = g[1], g[2]; m = 1 << t
            return [v[x ^ m] if bit(x, c_) else v[x] for x in range(D)]
        if k == 'SWAP':
            a_, b_ = g[1], g[2]
            def sw(x):
                return x ^ (1 << a_) ^ (1 << b_) if bit(x, a_) != bit(x, b_) else x
            return [v[sw(x)] for x in range(D)]
        if k in ('CK', 'CKd'):
            c_, t = g[1], g[2]; m = 1 << t; out = list(v)
            for x in range(D):
                if not bit(x, c_) or x & m: continue
                y = x | m; a, b = v[x], v[y]
                out[x] = GINV * (a + b) % P; out[y] = GINV * (a - b) % P
                if k == 'CKd':
                    out[x] = I * out[x] % P; out[y] = I * out[y] % P
            return out
        if k == 'CCZ':
            a_, b_, c_ = g[1:]
            return [(P - e) % P if bit(x, a_) and bit(x, b_) and bit(x, c_) else e for x, e in enumerate(v)]
        if k == 'TOFF':
            t, c1, c2 = g[1:]; m = 1 << t
            return [v[x ^ m] if bit(x, c1) and bit(x, c2) else v[x] for x in range(D)]
        if k in ('BOX', 'BOXd'):
            ctrls = g[2:]
            return [(P - e) % P if all(bit(x, c) for c in ctrls) else e for x, e in enumerate(v)]
        if k in ('SBOX', 'SBOXd'):
            x_, ctrls = g[2], g[3]; c = I if k == 'SBOX' else MI
            return [c * e % P if bit(x, x_) and all(bit(x, w) for w in ctrls) else e for x, e in enumerate(v)]
        raise ValueError(g)

    def run(self, word, v):
        for g in reversed(word):
            v = self.apply(g, v)
        return v

    def fp(self, word):
        return tuple(e for v in self.vecs for e in self.run(word, v))

    def eq(self, a, b):
        return self.fp(a) == self.fp(b)


# ------------------------------------------------------- the generators
def to_generators(word):
    """every macro letter as a word in iI, S, K, CS (boxes are expected
    to be flattened first)."""
    out = []
    for g in word:
        out += _gen(g)
    return out


def _gen(g):
    k = g[0]
    if k in ('iI', 'S', 'K'):
        return [g]
    if k == 'CS':
        return [g]
    if k == 'iIi':
        return [('iI',)] * 3
    if k == 'Sd':
        return [('S', g[1])] * 3
    if k == 'Kd':
        return [('K', g[1]), ('iI',)]
    if k == 'Z':
        return [('S', g[1])] * 2
    if k == 'X':
        w = g[1]
        return [('K', w), ('S', w), ('S', w), ('K', w), ('iI',)]
    if k == 'CSd':
        return [('CS',) + g[1:]] * 3
    if k == 'CZ':
        return [('CS',) + g[1:]] * 2
    if k == 'CX':
        c, t = g[1:]
        return [('K', t), ('CS', c, t), ('CS', c, t), ('K', t), ('iI',)]
    if k == 'SWAP':
        a, b = g[1:]
        return _gen(('CX', a, b)) + _gen(('CX', b, a)) + _gen(('CX', a, b))
    if k == 'CK':
        c, t = g[1:]
        return [('CS', c, t), ('K', t), ('CS', c, t), ('K', t), ('CS', c, t),
                ('S', c), ('S', c), ('S', c), ('iI',)]
    if k == 'CKd':
        c, t = g[1:]
        return [('S', c)] + _gen(('CK', c, t))
    if k == 'CCZ':
        a, b, c = g[1:]
        return ([('CS', b, c)] + _gen(('CX', a, b)) + [('CS', b, c)] * 3 + _gen(('CX', a, b))
                + [('CS', a, c)])
    if k == 'TOFF':
        t, c1, c2 = g[1:]
        return [('K', t)] + _gen(('CCZ', t, c1, c2)) + [('K', t), ('iI',)]
    raise ValueError(('not a basic macro', g))
