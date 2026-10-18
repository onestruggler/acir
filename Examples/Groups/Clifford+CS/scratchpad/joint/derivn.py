# Derivations of five-wire identities, step by step.
#
# Letters are gate tuples on wires 0 .. N-1:
#   ('iI',) ('iIi',)                     the scalar i and its inverse
#   ('S', w) ('Sd', w) ('K', w) ('Kd', w) ('X', w) ('Z', w)
#   ('CS', a, b) ('CSd', a, b) ('CZ', a, b) ('SWAP', a, b)   symmetric
#   ('CX', c, t) ('CK', c, t) ('CKd', c, t)                  control, target
#   ('CCZ', a, b, c) ('TOFF', t, c1, c2)
#   ('BOX', u, c1, .., ck) ('BOXd', ...)  the box: -1 where the controls
#       are set, the identity on its dashed wire u, by Clement's recursion
#       BOX(u; a, b, r..) = CCZ(u,a,b) TOFF(u;a,b) BOX(a; u, r..)
#                           TOFF(u;a,b) CCZ(u,a,b) BOX(a; u, r..),
#       BOX(u; a, b) = CZ(a, b); BOXd is the reverse word;
#   ('SBOX', u, x, (c1, c2), A) ('SBOXd', ...)  the doubly controlled S
#       Sigma(x; c1, c2 | u, A) = BOX(u; x, c1, c2, A) TOFF(A; c1, c2)
#       CS(x, A) TOFF(A; c1, c2) CSd(x, A); with one control
#       SBOX(u, x, (c,), A) = CS(x, c).
# These are the spellings of Five/Letters.agda (scratchpad/five/mac5.py),
# so that unfolding a box is definitional there.
#
# A step of a derivation replaces a segment of the current word:
#   win    a segment and its replacement on at most four wires, with the
#          same operator (one Lemma 5.1 step given completeness on four);
#   comm   two adjacent letters on disjoint wires (structural);
#   lemma  an earlier lemma, or an axiom of w5lib.L, at a renaming of
#          its wires, either way;
#   transport  the controlled image of one side of a two-wire equation
#          to that of the other (joint/tr.py);
#   unfold / fold   a box and its one-level unfolding.
# Each step is checked semantically.  The recorded steps are what
# five/load5.py and five/lower5.py read: (kind, k, n, info), k the
# position and n the length of the replaced segment.
import os
import cs

N = int(os.environ.get("DERIVN_N", "5"))   # the width; windows have at most N - 1 wires
SCALARS = ('iI', 'iIi')
BOXES = ('BOX', 'BOXd', 'SBOX', 'SBOXd')
SYM = ('CS', 'CSd', 'CZ', 'SWAP', 'CCZ')

INV = {'iI': 'iIi', 'iIi': 'iI', 'S': 'Sd', 'Sd': 'S', 'K': 'Kd', 'Kd': 'K',
       'X': 'X', 'Z': 'Z', 'CS': 'CSd', 'CSd': 'CS', 'CZ': 'CZ', 'SWAP': 'SWAP',
       'CX': 'CX', 'CK': 'CKd', 'CKd': 'CK', 'CCZ': 'CCZ', 'TOFF': 'TOFF',
       'BOX': 'BOXd', 'BOXd': 'BOX', 'SBOX': 'SBOXd', 'SBOXd': 'SBOX'}


def norm1(g):
    k = g[0]
    if k in SCALARS:
        return (k,)
    if k in SYM:
        return (k,) + tuple(sorted(g[1:]))
    if k == 'TOFF':
        return (k, g[1]) + tuple(sorted(g[2:]))
    if k in ('SBOX', 'SBOXd'):
        return (k, g[1], g[2], tuple(g[3]), g[4])
    return tuple(g)


def norm(word):
    return [norm1(g) for g in word]


def inv(word):
    out = []
    for g in reversed(word):
        out.append((INV[g[0]],) + tuple(g[1:]))
    return norm(out)


# ------------------------------------------------------------ wires
def support(g):
    """every wire the letter's spelling touches (a box's dashed and
    borrowed wires included)."""
    k = g[0]
    if k in SCALARS:
        return frozenset()
    if k in ('SBOX', 'SBOXd'):
        u, x, ctrls, A = g[1], g[2], g[3], g[4]
        return frozenset((u, x, A) + tuple(ctrls)) if len(ctrls) > 1 else frozenset((x,) + tuple(ctrls))
    return frozenset(g[1:])


def supp(word):
    s = frozenset()
    for g in word:
        s |= support(g)
    return s


def relabel_word(word, pi):
    """the wires renamed by pi (a dict; missing wires fixed)."""
    f = lambda w: pi.get(w, w)
    out = []
    for g in word:
        k = g[0]
        if k in SCALARS:
            out.append(g)
        elif k in ('SBOX', 'SBOXd'):
            out.append((k, f(g[1]), f(g[2]), tuple(f(c) for c in g[3]), f(g[4])))
        else:
            out.append((k,) + tuple(f(w) for w in g[1:]))
    return norm(out)


# ------------------------------------------------------------ boxes
def unfold1(g):
    k = g[0]
    if k in ('BOX', 'BOXd'):
        u, ctrls = g[1], g[2:]
        if len(ctrls) == 2:
            return [('CZ',) + tuple(sorted(ctrls))]
        a, b, rest = ctrls[0], ctrls[1], ctrls[2:]
        ccz = norm1(('CCZ', u, a, b)); tf = norm1(('TOFF', u, a, b))
        sub = (k, a, u) + tuple(rest)
        if k == 'BOX':
            return [ccz, tf, sub, tf, ccz, sub]
        return [sub, ccz, tf, sub, tf, ccz]
    if k in ('SBOX', 'SBOXd'):
        u, x, ctrls, A = g[1], g[2], tuple(g[3]), g[4]
        if len(ctrls) == 1:
            return [norm1(('CS' if k == 'SBOX' else 'CSd', x, ctrls[0]))]
        c1, c2 = ctrls
        bx = ('BOX', u, x, c1, c2, A); tf = norm1(('TOFF', A, c1, c2))
        s = ('SBOX', u, x, (A,), c2); sd = ('SBOXd', u, x, (A,), c2)
        if k == 'SBOX':
            return [bx, tf, s, tf, sd]
        return [s, tf, sd, tf, ('BOXd',) + bx[1:]]
    raise ValueError(('not a box', g))


def is_box(g):
    return g[0] in BOXES


def flatten(word):
    out = []
    for g in word:
        if is_box(g):
            out += flatten(unfold1(g))
        else:
            out.append(norm1(g))
    return out


# ------------------------------------------------------------ semantics
class Width:
    def __init__(self, n):
        self.n = n
        self.sem = cs.Sem(n)

    def fp(self, word):
        return self.sem.fp(norm(word))

    def matrix(self, g):
        return self.sem.fp([norm1(g)])


W = Width(N)


def fp(word):
    return W.fp(word)


def show(word):
    out = []
    for g in word:
        k = g[0]
        if k in ('SBOX', 'SBOXd'):
            out.append(f"{k}({g[1]};{g[2]};{''.join(map(str, g[3]))};{g[4]})")
        elif k in ('BOX', 'BOXd'):
            out.append(f"{k}({g[1]};{''.join(map(str, g[2:]))})")
        else:
            out.append(k + ''.join(str(w) for w in g[1:]))
    return ' '.join(out) if out else 'eps'


# ------------------------------------------------------------ derivations
QUIET = bool(os.environ.get('DERIV_QUIET'))
DERIVATIONS = []
BY_NAME = {}


class Derivation:
    def __init__(self, name, lhs, rhs, lemmas):
        self.name, self.lhs, self.rhs = name, norm(lhs), norm(rhs)
        self.cur = list(self.lhs); self.steps = []; self.lemmas = lemmas
        assert name not in lemmas, f'{name}: already a lemma'
        assert fp(self.lhs) == fp(self.rhs), f'{name}: not semantically valid'

    def _set(self, new, kind, info, k, n):
        self.steps.append((kind, k, n, info))
        self.cur = new

    def _replace(self, k, n, rep, kind, info, check=True):
        seg = self.cur[k:k + n]; rep = norm(rep)
        if check:
            assert fp(seg) == fp(rep), f'{self.name}: {kind} at {k} changes the operator: {show(seg)} -> {show(rep)}'
        self._set(self.cur[:k] + rep + self.cur[k + n:], kind, info, k, n)

    def win(self, k, n, rep):
        seg = self.cur[k:k + n]
        s = supp(seg) | supp(rep)
        assert len(s) <= N - 1, f'{self.name}: window {show(seg)} -> {show(rep)} on {sorted(s)}'
        self._replace(k, n, rep, 'win', None)

    def comm(self, k):
        g, h = self.cur[k], self.cur[k + 1]
        assert not (support(g) & support(h)), f'{self.name}: {show([g])}, {show([h])} not disjoint'
        self._replace(k, 2, [h, g], 'comm', None, check=False)

    def lemma(self, name, k, fwd=True, pi=None):
        l, r = self.lemmas[name]
        if pi:
            l, r = relabel_word(l, pi), relabel_word(r, pi)
        src, dst = (l, r) if fwd else (r, l)
        assert self.cur[k:k + len(src)] == list(src), \
            f'{self.name}: {name} does not match at {k}: {show(self.cur[k:k + len(src)])} vs {show(src)}'
        info = (name, dict(pi), fwd) if pi else (name, fwd)
        self._replace(k, len(src), dst, 'lemma', info, check=False)

    def transport(self, k, src, dst, el, er, t, b=1):
        """the controlled image src of el (control wire t, colour b) at k to
        dst, that of er, for an equation el = er of letters on at most two
        wires off t: a transport of a two-wire derivation (recorded as
        (el, er, t, b), the joint paper's step, which five/lower5.py reads)."""
        assert self.cur[k:k + len(src)] == list(src),             f'{self.name}: transport does not match at {k}: {show(self.cur[k:k + len(src)])} vs {show(src)}'
        assert fp(el) == fp(er), f'{self.name}: transport of an unsound equation'
        self._replace(k, len(src), dst, 'transport', (tuple(norm(el)), tuple(norm(er)), t, b), check=False)

    def unfold(self, k):
        g = self.cur[k]
        self._replace(k, 1, unfold1(g), 'unfold', None, check=False)

    def fold(self, k, g):
        us = norm(unfold1(g))
        assert self.cur[k:k + len(us)] == us, f'{self.name}: fold {show([g])} at {k}'
        self._replace(k, len(us), [g], 'fold', None, check=False)

    def done(self):
        assert self.cur == self.rhs, f'{self.name}: not finished: at {show(self.cur)}, want {show(self.rhs)}'
        if not QUIET:
            print(f'ok   {self.name}: {len(self.steps)} steps', flush=True)
        self.lemmas[self.name] = (self.lhs, self.rhs)
        DERIVATIONS.append(self); BY_NAME[self.name] = self
        return self
