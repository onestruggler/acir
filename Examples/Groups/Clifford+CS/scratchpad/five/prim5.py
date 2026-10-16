# Primitive five-wire derivations: the steps that the Agda chain engine
# (Five/Chain) accepts, each checked here semantically.  A line is a list
# of macro letters (joint/derivn.py's gate tuples, normalised by `norm`);
# every letter has the canonical spelling of mac5.py.
#
#   W  a literal window: the letters of the segment and of its
#      replacement are spelled off one wire m and have the same operator:
#      Windows.win at the width-4 words with wire m deleted, one
#      evaluation at width 4 (complete4);
#   P  a placed window: every letter avoids wire m semantically, those
#      whose spelling crosses m through a respelling lemma (`place m u`),
#      the rest literally: Five.PWin.pwin, one evaluation at width 4;
#   C  the structural commutation of a letter spelled within the bottom i
#      wires and one spelled within the top 5 - i (i = 1 .. 4);
#   Z  a scalar letter (unlifted) passing any letter (Central-Scalars);
#   R  a re-bracketing: the same basic letters (by-assoc), or the one-level
#      unfolding of a box (definitional: `refl`);
#   A  a five-wire rule at its canonical placement;
#   L  an earlier lemma, forward or backward.
import sys, os
HERE = os.path.dirname(os.path.abspath(__file__))
JOINT = os.path.join(os.path.dirname(HERE), 'joint')
sys.path.insert(0, HERE); sys.path.insert(0, JOINT)
import mac5
import derivn

N = 5
SCALARS = ('iI', 'iIi')
BOXES = ('BOX', 'BOXd', 'SBOX', 'SBOXd', 'KBOX', 'KBOXd')

UNLIFTED = (('iI', 0), ('iIi', 0))
def is_scalar(g): return g[0] in SCALARS
def is_box(g): return g[0] in BOXES

def norm1(g):
    k = g[0]
    if k in SCALARS: return (k, g[1] if len(g) > 1 else 0)
    if k in ('CS', 'CSd', 'CZ', 'SWAP', 'CCZ'): return (k,) + tuple(sorted(g[1:]))
    if k == 'TOFF': return (k, g[1]) + tuple(sorted(g[2:]))
    return tuple(g)

def norm(word): return [norm1(g) for g in word]

def joint(g):
    """back to joint's letter (an unlifted scalar)."""
    return (g[0],) if is_scalar(g) else g

# ------------------------------------------------------------- spellings
_TREE = {}
def tree(g):
    if g not in _TREE:
        if is_box(g):
            _TREE[g] = ('cat', [tree(norm1(h)) for h in derivn.unfold1(g)])
        else:
            _TREE[g] = mac5.mac_tree(g)
    return _TREE[g]

def word_of(t):
    if t[0] == 'cat': return [b for s in t[1] for b in word_of(s)]
    return mac5.word_of(t)

_BASIC = {}
def basic1(g):
    if g not in _BASIC: _BASIC[g] = tuple(word_of(tree(g)))
    return _BASIC[g]

def basic(word): return [b for g in word for b in basic1(g)]

_SP = {}
def spelled(g):
    """the wires the basic letters of g touch (a scalar its lift)."""
    if g not in _SP:
        s = set()
        for name, sh in basic1(g):
            s.add(sh)
            if name == 'CS': s.add(sh + 1)
        _SP[g] = frozenset(s)
    return _SP[g]

def semsupp(g):
    if is_scalar(g): return frozenset()
    return derivn.support(g)

def gsupp(word):
    s = set()
    for g in word: s |= semsupp(g)
    return s

# ------------------------------------------------------------- semantics
W5 = derivn.Width(N)
_FP = {}
def fp1(g):
    return W5.matrix(joint(g))

def fpw(word):
    return W5.fp([joint(g) for g in word])

def show(word):
    out = []
    for g in word:
        if g[0] in ('SBOX', 'SBOXd', 'KBOX', 'KBOXd'):
            out.append(f"{g[0]}({g[1]};{g[2]};{''.join(map(str, g[3]))};{g[4]})")
        elif g[0] in ('BOX', 'BOXd'):
            out.append(f"{g[0]}({g[1]};{''.join(map(str, g[2:]))})")
        elif is_scalar(g):
            out.append(g[0] + (str(g[1]) if g[1] else ''))
        else:
            out.append(g[0] + ''.join(str(w) for w in g[1:]))
    return ' '.join(out) if out else 'eps'

def split(g, h):
    """(i, bottom-first?) when g, h are spelled within the bottom i wires
    and the top 5 - i wires in some order, else None."""
    sg, sh = spelled(g), spelled(h)
    for i in range(1, N):
        lo, hi = set(range(i)), set(range(i, N))
        if sg <= lo and sh <= hi: return (i, True)
        if sh <= lo and sg <= hi: return (i, False)
    return None

# respellings available for the placed window: (letter, m) -> lemma name;
# filled by respell.py
RESPELL = {}

# the steps of every finished derivation, by name
STEPS = {}

def resp_ok(g, m):
    """whether g has a respelling at m: it avoids m semantically, and its
    spelling avoids m or a respelling lemma exists."""
    if is_box(g): return False
    if is_scalar(g): return g[1] != m
    if m in semsupp(g): return False
    return m not in spelled(g) or (g, m) in RESPELL

class Prim:
    """a primitive derivation from lhs; steps recorded for the emitter."""
    def __init__(self, name, lhs, rhs, lemmas, check=True):
        self.name, self.lhs, self.rhs = name, list(lhs), list(rhs)
        self.cur = list(lhs); self.steps = []; self.lemmas = lemmas
        if check:
            assert fpw(self.lhs) == fpw(self.rhs), f'{name}: not semantically valid'

    def _set(self, k, n, ys, kind, info, check=True):
        seg = self.cur[k:k + n]
        if check:
            assert fpw(seg) == fpw(ys), f'{self.name}: {kind} step changes the operator: {show(seg)} -> {show(ys)}'
        self.steps.append((kind, k, n, list(seg), list(ys), info))
        self.cur = self.cur[:k] + list(ys) + self.cur[k + n:]

    def W(self, k, n, ys, m):
        seg = self.cur[k:k + n]
        for g in seg + list(ys):
            assert m not in spelled(g), f'{self.name}: {show([g])} is spelled on wire {m}'
        self._set(k, n, ys, 'W', m)

    def P(self, k, n, ys, m):
        seg = self.cur[k:k + n]
        for g in seg + list(ys):
            assert resp_ok(g, m), f'{self.name}: {show([g])} has no respelling at {m}'
        self._set(k, n, ys, 'P', m)

    def U(self, k, g2):
        g = self.cur[k]
        assert is_scalar(g) and is_scalar(g2) and g[0] == g2[0], f'{self.name}: U on {show([g])}'
        self._set(k, 1, [g2], 'U', None, check=False)

    def C(self, k):
        g, h = self.cur[k], self.cur[k + 1]
        i = split(g, h)
        assert i is not None, f'{self.name}: C needs a split of the wires: {show([g, h])}'
        self._set(k, 2, [h, g], 'C', i, check=False)

    def Z(self, k):
        g, h = self.cur[k], self.cur[k + 1]
        assert (g in UNLIFTED or h in UNLIFTED), f'{self.name}: Z needs the unlifted scalar: {show([g, h])}'
        self._set(k, 2, [h, g], 'Z', g in UNLIFTED, check=False)

    def R(self, k, n, ys, check=True, tag=None):
        seg = self.cur[k:k + n]
        if check:
            assert basic(seg) == basic(ys), f'{self.name}: R changes the letters: {show(seg)} -> {show(ys)}'
        self._set(k, n, ys, 'R', tag, check=False)

    def A(self, k, name, src, dst, forward=True):
        assert self.cur[k:k + len(src)] == list(src), f'{self.name}: {name} does not match at {k}: {show(self.cur[k:k+len(src)])}'
        self._set(k, len(src), dst, 'A', (name, forward))

    def L(self, name, k, forward=True):
        l, r = self.lemmas[name]
        src, dst = (l, r) if forward else (r, l)
        assert self.cur[k:k + len(src)] == list(src), f'{self.name}: lemma {name} does not match at {k}: {show(self.cur[k:k+len(src)])} vs {show(src)}'
        self._set(k, len(src), list(dst), 'L', (name, forward), check=False)

    def done(self):
        assert self.cur == self.rhs, f'{self.name}: not finished: at {show(self.cur)}, want {show(self.rhs)}'
        self.lemmas[self.name] = (self.lhs, self.rhs)
        STEPS[self.name] = self.steps
        return self
