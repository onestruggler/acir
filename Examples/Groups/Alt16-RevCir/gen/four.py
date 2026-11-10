"""Four wires: derivations from the rules (1)-(7), letter by letter.

The macro derivations of gen/search (words of placed coloured gates,
rewritten by three-wire steps and pair lemmas) are compiled here into the
steps of FourWire.agda and Frames.agda, replayed exactly as Agda's engine
runs them, and written out as Agda (mk_four.py).

Letters, one character each (Letters.agda):
    a b d f     X on the wires 0, 1, 2, 3
    c e g       CX with target 0, 1, 2 and the control one wire up
    s t u       Ex on the wires 0 1, 1 2, 2 3
    T U         CCX with target 0, 1 and the controls above it
A placed gate is spelled h B h^-1: a base letter B (a, c or T) in a frame
h, a word in the NOT gates and swaps that puts NOT on the white controls
and brings the target and the controls to the bottom wires.

Kinds of step (an equation, used left to right at a position):
    Bot(l, r)        two words on the bottom three wires, same function
    Top(l, r)        the same on the top three wires
    HS(u, v)         two words in the NOT gates and swaps, same function
    FR(p, q, b, c)   p b p^-1 = q c q^-1, a change of frame
    Named            a rule of FourWire.agda, or a lemma derived before
"""
import os
import sys

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, 'search'))

import macro as M          # noqa: E402

# ----------------------------------------------------------------------
# Letters and their functions on the sixteen states (bit k = wire k)

BOT = frozenset('abdcestT')
TOPL = frozenset('bdfegtuU')
HLET = frozenset('abdfstu')
UP = dict(zip('abdcestT', 'bdfegtuU'))
DOWN = {v: k for k, v in UP.items()}
XL = 'abdf'
EL = 'stu'


def _bit(s, k):
    return (s >> k) & 1


def _letter(ch):
    if ch in XL:
        k = XL.index(ch)
        return tuple(s ^ (1 << k) for s in range(16))
    if ch in 'ceg':
        k = 'ceg'.index(ch)
        return tuple(s ^ (_bit(s, k + 1) << k) for s in range(16))
    if ch in EL:
        k = EL.index(ch)
        out = []
        for s in range(16):
            u, v = _bit(s, k), _bit(s, k + 1)
            out.append(s & ~(3 << k) | (v << k) | (u << (k + 1)))
        return tuple(out)
    k = 'TU'.index(ch)
    return tuple(s ^ ((_bit(s, k + 1) & _bit(s, k + 2)) << k) for s in range(16))


LF = {ch: _letter(ch) for ch in 'abdfcegstuTU'}
IDF = tuple(range(16))


def func(word):
    p = IDF
    for ch in word:
        q = LF[ch]
        p = tuple(q[v] for v in p)
    return p


def rev(w):
    return w[::-1]


def up(w):
    return ''.join(UP[c] for c in w)


def down(w):
    return ''.join(DOWN[c] for c in w)


def wire_perm(word):
    """Where a word in the NOT gates and swaps sends the content of each
    wire: position of wire w's content after the word."""
    pos = list(range(4))                  # pos[w] = position of wire w's content
    for ch in word:
        if ch in EL:
            k = EL.index(ch)
            pos = [k + 1 if p == k else k if p == k + 1 else p for p in pos]
    return pos


# ----------------------------------------------------------------------
# Frames.agda's normal form, mirrored

TAB = {
    (0, 'a'): ('a', 0, 0), (0, 'b'): ('b', 0, 0), (0, 'd'): ('d', 0, 0),
    (0, 'f'): ('', 1, 0), (0, 's'): ('s', 0, 0), (0, 't'): ('t', 0, 0),
    (0, 'u'): ('', 0, 1),
    (1, 'a'): ('a', 0, 1), (1, 'b'): ('b', 0, 1), (1, 'd'): ('', 1, 1),
    (1, 'f'): ('d', 0, 1), (1, 's'): ('s', 0, 1), (1, 't'): ('', 0, 2),
    (1, 'u'): ('', 0, 0),
    (2, 'a'): ('a', 0, 2), (2, 'b'): ('', 1, 2), (2, 'd'): ('b', 0, 2),
    (2, 'f'): ('d', 0, 2), (2, 's'): ('', 0, 3), (2, 't'): ('', 0, 1),
    (2, 'u'): ('t', 0, 2),
    (3, 'a'): ('', 1, 3), (3, 'b'): ('a', 0, 3), (3, 'd'): ('b', 0, 3),
    (3, 'f'): ('d', 0, 3), (3, 's'): ('', 0, 2), (3, 't'): ('s', 0, 3),
    (3, 'u'): ('t', 0, 3),
}
REP = ['', 'u', 'ut', 'uts']
for (_r, _y), (_b, _e, _r2) in TAB.items():
    assert func(REP[_r] + _y) == func(_b + ('f' if _e else '') + REP[_r2]), (_r, _y)


def hnorm(u):
    q, e, r = '', 0, 0
    for y in u:
        b, e2, r = TAB[(r, y)]
        q += b
        e ^= e2
    return q, e, r


def ok_st(s, t):
    return s[2] == t[2] and s[1] == t[1] and func(s[0]) == func(t[0])


def frame_ok(p, p2, b, b2):
    s = hnorm(rev(p) + p2)
    t = hnorm(rev(p2) + p)
    return (ok_st(hnorm(p + rev(p)), ('', 0, 0)) and s[2] == 0 and t[2] == 0
            and t[1] == s[1] and func(s[0] + b2 + t[0]) == func(b))


# ----------------------------------------------------------------------
# Equations

class Eq:
    lhs = rhs = ''


class Bot(Eq):
    def __init__(self, l, r):
        assert set(l + r) <= BOT and func(l) == func(r), (l, r)
        self.l, self.r, self.lhs, self.rhs = l, r, l, r

    def sym(self):
        return Bot(self.r, self.l)

    def agda(self, i):
        return 'bo %d "%s" "%s"' % (i, self.l, self.r)


class Top(Eq):
    def __init__(self, l, r):
        assert set(l + r) <= BOT and func(l) == func(r), (l, r)
        self.l, self.r, self.lhs, self.rhs = l, r, up(l), up(r)

    def sym(self):
        return Top(self.r, self.l)

    def agda(self, i):
        return 'to %d "%s" "%s"' % (i, self.l, self.r)


class HS(Eq):
    def __init__(self, u, v):
        assert set(u + v) <= HLET and ok_st(hnorm(u), hnorm(v)), (u, v)
        assert func(u) == func(v)
        self.lhs, self.rhs = u, v

    def sym(self):
        return HS(self.rhs, self.lhs)

    def agda(self, i):
        return 'hs %d "%s" "%s"' % (i, self.lhs, self.rhs)


class FR(Eq):
    def __init__(self, p, p2, b, b2):
        assert set(p + p2) <= HLET and set(b + b2) <= BOT
        assert frame_ok(p, p2, b, b2), (p, p2, b, b2)
        self.args = (p, p2, b, b2)
        self.lhs = p + b + rev(p)
        self.rhs = p2 + b2 + rev(p2)
        assert func(self.lhs) == func(self.rhs)

    def sym(self):
        p, p2, b, b2 = self.args
        return FR(p2, p, b2, b)

    def agda(self, i):
        return 'fr %d "%s" "%s" "%s" "%s"' % ((i,) + self.args)


class Named(Eq):
    def __init__(self, name, lhs, rhs, back=False):
        assert func(lhs) == func(rhs), name
        self.name, self.back = name, back
        self.lhs, self.rhs = (rhs, lhs) if back else (lhs, rhs)
        self.base = (lhs, rhs)

    def sym(self):
        return Named(self.name, self.base[0], self.base[1], not self.back)

    def agda(self, i):
        return '%s %d %s' % ('rwˢ' if self.back else 'rw', i, self.name)


def sem(l, r):
    """A step that evaluation decides, of whichever kind fits."""
    s = set(l + r)
    if s <= BOT:
        return Bot(l, r)
    if s <= TOPL:
        return Top(down(l), down(r))
    if s <= HLET:
        return HS(l, r)
    raise ValueError((l, r))


# The rules of FourWire.agda that involve all four wires.
R7 = Named('r7⁼', 'UcU', 'sUsc')
NAT = Named('nat-ccx⁼', 'Tuts', 'utsU')
AX = {n: Named(n, l, r) for n, l, r in [
    ('comm-x3-x0', 'fa', 'af'), ('comm-cx2-x0', 'ga', 'ag'),
    ('comm-ex2-x0', 'ua', 'au'), ('comm-ccx1-x0', 'Ua', 'aU'),
    ('comm-x3-cx0', 'fc', 'cf'), ('comm-cx2-cx0', 'gc', 'cg'),
    ('comm-ex2-cx0', 'uc', 'cu'), ('comm-x3-ex0', 'fs', 'sf'),
    ('comm-cx2-ex0', 'gs', 'sg'), ('comm-ex2-ex0', 'us', 'su'),
    ('comm-x3-ccx0', 'fT', 'Tf')]}


class Proof:
    """A derivation under construction: the steps, replayed as they are
    added."""

    def __init__(self, start):
        self.start = self.cur = start
        self.steps = []

    def rw(self, i, eq):
        n = len(eq.lhs)
        assert self.cur[i:i + n] == eq.lhs, (self.cur, i, eq.lhs, eq.rhs)
        self.cur = self.cur[:i] + eq.rhs + self.cur[i + n:]
        self.steps.append((i, eq))

    def run(self, steps, off=0):
        for i, eq in steps:
            self.rw(off + i, eq)


def backwards(steps):
    return [(i, eq.sym()) for i, eq in reversed(steps)]


# ----------------------------------------------------------------------
# Lemmas

class Library:
    def __init__(self):
        self.lemmas = []          # (name, lhs, rhs, steps, comment)
        self.count = 0

    def add(self, prefix, proof, rhs, comment='', name=None):
        assert proof.cur == rhs, (prefix, proof.cur, rhs)
        assert proof.steps, prefix
        self.count += 1
        if name is None:
            name = '%s%d' % (prefix, self.count)
        self.lemmas.append((name, proof.start, rhs, proof.steps, comment))
        return Named(name, proof.start, rhs)

    def steps(self):
        return sum(len(l[3]) for l in self.lemmas)


LIB = Library()

# ----------------------------------------------------------------------
# Placed gates and their spelling

GATES = M.GATES
NG = M.NG


def supp(g):
    t, cs = GATES[g]
    return [t] + [c for c, _ in cs]


def bubble(wires):
    """The swaps that bring the given wires, in order, to the positions
    0, 1, ..."""
    at = list(range(4))                   # at[p] = wire at position p
    out = ''
    for k, w in enumerate(wires):
        p = at.index(w)
        while p > k:
            out += EL[p - 1]
            at[p - 1], at[p] = at[p], at[p - 1]
            p -= 1
    return out


def frame_of(g):
    """(h, B): the gate is h B h^-1."""
    t, cs = GATES[g]
    nots = ''.join(XL[c] for c, v in cs if not v)
    return nots + bubble([t] + [c for c, _ in cs]), 'acT'[len(cs)]


def sp(g):
    t, cs = GATES[g]
    if not cs:
        return XL[t]
    h, B = frame_of(g)
    return h + B + rev(h)


for _g in range(NG):
    assert func(sp(_g)) == M.F[_g], M.gname(_g)
    if all(w < 3 for w in supp(_g)):
        assert set(sp(_g)) <= BOT


def spw(gs):
    return ''.join(sp(g) for g in gs)


TRIPLE_FRAME = {(0, 1, 2): '', (0, 1, 3): 'u', (0, 2, 3): 'tu', (1, 2, 3): 'stu'}


def relabel(g, triple):
    t, cs = GATES[g]
    ix = {w: k for k, w in enumerate(triple)}
    return M.GID[(ix[t], tuple(sorted((ix[c], v) for c, v in cs)))]


def to_frame(g, p, b):
    """Steps, at offsets from the start of the gate's spelling, that turn
    sp(g) into p b p^-1."""
    t, cs = GATES[g]
    target = p + b + rev(p)
    assert func(target) == M.F[g]
    if sp(g) == target:
        return []
    if not cs:
        return [(0, HS(XL[t], target))]
    h, B = frame_of(g)
    if wire_perm(rev(h) + p)[3] == 3:
        return [(0, FR(h, p, B, b))]
    assert B == 'c'
    steps = [(len(h), Top('', 'tt')), (len(h) + 1, AX['comm-ex2-cx0'])]
    if (h + 'u', B) != (p, b):
        steps.append((0, FR(h + 'u', p, B, b)))
    return steps


# ----------------------------------------------------------------------
# The symmetries: the 384 words in the NOT gates and swaps

def _hwords():
    best = {IDF: ''}
    frontier = [IDF]
    while frontier:
        nxt = []
        for p in frontier:
            for ch in 'abdfstu':
                q = LF[ch]
                p2 = tuple(q[v] for v in p)
                if p2 not in best:
                    best[p2] = best[p] + ch
                    nxt.append(p2)
        frontier = nxt
    return sorted(best.values(), key=lambda w: (len(w), w))


HWORDS = _hwords()
assert len(HWORDS) == 384


def act(W, g):
    """The gate W g W^-1."""
    return M.FID[func(W + sp(g) + rev(W))]


def find_sym(pairs):
    """A word W with W g0 W^-1 = g for every (g0, g) in pairs, or None."""
    for W in HWORDS:
        if all(act(W, g0) == g for g0, g in pairs):
            return W
    return None


# ----------------------------------------------------------------------
# Small lemmas about gates

_INV = {}


def inv(g):
    """sp(g) sp(g) -> empty."""
    if g in _INV:
        return _INV[g]
    w = sp(g)
    t, cs = GATES[g]
    if not cs:
        eq = sem(w + w, '')
    else:
        h, B = frame_of(g)
        pr = Proof(w + w)
        if h:
            pr.rw(len(h) + 1, HS(rev(h) + h, ''))
        pr.rw(len(h), Bot(B + B, ''))
        if h:
            pr.rw(0, HS(h + rev(h), ''))
        eq = pr.steps[0][1] if len(pr.steps) == 1 else LIB.add('I', pr, '', 'inverse ' + M.gname(g))
    _INV[g] = eq
    return eq


def _target(W, g0):
    t, cs = GATES[g0]
    if not cs:
        return W, XL[t]
    h, B = frame_of(g0)
    return W + h, B


def frame_all(pr, off, W, gates0):
    """The word at off is sp(W gates0 W^-1), gate by gate; turn it into
    W sp(gates0) W^-1."""
    if not W or not gates0:
        return
    Wr = rev(W)
    x = off
    for g0 in gates0:
        pr.run(to_frame(act(W, g0), *_target(W, g0)), x)
        x += len(W) + len(sp(g0)) + len(W)
    x = off + len(W)
    for k, g0 in enumerate(gates0):
        x += len(sp(g0))
        if k + 1 < len(gates0):
            pr.rw(x, HS(Wr + W, ''))


def unframe_all(pr, off, W, gates0):
    """The word at off is W sp(gates0) W^-1; turn it into
    sp(W gates0 W^-1), gate by gate."""
    if not W:
        return
    Wr = rev(W)
    if not gates0:
        pr.rw(off, HS(W + Wr, ''))
        return
    x = off + len(W)
    for k, g0 in enumerate(gates0):
        x += len(sp(g0))
        if k + 1 < len(gates0):
            pr.rw(x, HS('', Wr + W))
            x += 2 * len(W)
    x = off
    for g0 in gates0:
        g = act(W, g0)
        pr.run(backwards(to_frame(g, *_target(W, g0))), x)
        x += len(sp(g))


def transport(base, lg0, rg0, W):
    """base: sp(lg0) -> sp(rg0).  The proof of sp(W lg0 W^-1) ->
    sp(W rg0 W^-1), each gate conjugated by W."""
    lg = [act(W, g) for g in lg0]
    rg = [act(W, g) for g in rg0]
    pr = Proof(spw(lg))
    frame_all(pr, 0, W, lg0)
    pr.rw(len(W), base)
    unframe_all(pr, 0, W, rg0)
    assert pr.cur == spw(rg)
    return lg, rg, pr


# ----------------------------------------------------------------------
# Commuting two gates on disjoint wires

_COMM = {}
DSHIFT = 'tsut'                # brings the wires 2 3 to 0 1
_DC = []


def dc():
    """D c D^-1 -> g: CX on the wires 2 3 as CX on the wires 0 1 moved."""
    if not _DC:
        pr = Proof(DSHIFT + 'c' + rev(DSHIFT))
        pr.rw(0, HS('tsut', 'tust'))
        pr.rw(5, HS('tust', 'tsut'))
        pr.rw(2, Bot('stcts', 'e'))
        pr.rw(0, Top('stcts', 'e'))
        _DC.append(LIB.add('C', pr, 'g', 'CX on the top two wires'))
    return _DC[0]


def comm(g, h):
    """sp(g) sp(h) -> sp(h) sp(g), for gates on disjoint wires."""
    if (g, h) in _COMM:
        return _COMM[(g, h)]
    assert not (M.MASK[g] & M.MASK[h])
    (tg, cg), (th, ch) = GATES[g], GATES[h]
    pr = Proof(sp(g) + sp(h))
    if not cg and not ch:
        x, y = sp(g), sp(h)
        if x + y == 'fa':
            eq = AX['comm-x3-x0']
        elif x + y == 'af':
            eq = AX['comm-x3-x0'].sym()
        else:
            eq = sem(x + y, y + x)
        _COMM[(g, h)] = eq
        return eq
    if not cg:
        x = sp(g)
        hh, B = frame_of(h)
        y = [c for c in XL if func(x + hh) == func(hh + c)][0]
        if hh:
            pr.rw(0, HS(x + hh, hh + y))
        if y + B == 'fT':
            pr.rw(len(hh), AX['comm-x3-ccx0'])
        elif y + B == 'fc':
            pr.rw(len(hh), AX['comm-x3-cx0'])
        else:
            pr.rw(len(hh), Bot(y + B, B + y))
        if hh:
            pr.rw(len(hh) + 1, HS(y + rev(hh), rev(hh) + x))
    elif not ch:
        other = comm(h, g)
        pr.rw(0, other.sym())
    else:
        # two CX gates on complementary pairs of wires
        assert len(cg) == 1 and len(ch) == 1
        nots = ''.join(XL[c] for c, v in list(cg) + list(ch) if not v)
        f = nots + bubble([tg, cg[0][0], th, ch[0][0]])
        pr.run(to_frame(g, f, 'c'))
        n1 = 2 * len(f) + 1
        pr.run(to_frame(h, f + DSHIFT, 'c'), n1)
        # f c f^-1 f D c D^-1 f^-1
        if f:
            pr.rw(len(f) + 1, HS(rev(f) + f, ''))
        pr.rw(len(f) + 1, dc())
        pr.rw(len(f), AX['comm-cx2-cx0'].sym())
        pr.rw(len(f), dc().sym())
        if f:
            pr.rw(len(f) + 9, HS('', rev(f) + f))
        pr.run(backwards(to_frame(h, f + DSHIFT, 'c')), 0)
        pr.run(backwards(to_frame(g, f, 'c')), len(sp(h)))
    eq = LIB.add('C', pr, sp(h) + sp(g), 'commute %s , %s' % (M.gname(g), M.gname(h)))
    _COMM[(g, h)] = eq
    return eq


# ----------------------------------------------------------------------
# Pair lemmas

import pairs as P          # noqa: E402

FULL_PAIR = dict(M.PAIR)
_BASE = {}                 # orbit key -> list of ((g0, h0), Named)
_E = {}


def pair_word(g, h):
    k = FULL_PAIR[(g, h)]
    return [g, h, g, h], ([] if k == -1 else [k])


def add_base(g0, h0, eq):
    """eq: sp(g0 h0 g0 h0) -> sp(k).  Registers it and the lemma for the
    other order as the bases of their orbit."""
    key = P.orbit_key(g0, h0)
    l, r = pair_word(g0, h0)
    assert eq.lhs == spw(l) and eq.rhs == spw(r)
    # h g h g -> k, from g h g h -> k
    l2, r2 = pair_word(h0, g0)
    assert r2 == r
    pr = Proof(spw(l2))
    n = len(pr.cur)
    if r:
        pr.rw(n, inv(r[0]).sym())            # ... k k
    pr.rw(n, eq.sym())                       # h g h g . g h g h . k
    for x in (g0, h0, g0, h0):
        n -= len(sp(x))
        pr.rw(n, inv(x))
    other = LIB.add('P', pr, spw(r2), 'pair %s , %s' % (M.gname(h0), M.gname(g0)))
    _BASE[key] = [((g0, h0), eq), ((h0, g0), other)]
    _E[(g0, h0)] = eq
    _E[(h0, g0)] = other


def E(g, h):
    """sp(g h g h) -> sp(k), an instance of a pair lemma."""
    if (g, h) in _E:
        return _E[(g, h)]
    key = P.orbit_key(g, h)
    assert key in _BASE, 'orbit of %s , %s not derived yet' % (M.gname(g), M.gname(h))
    for (g0, h0), base in _BASE[key]:
        W = find_sym([(g0, g), (h0, h)])
        if W is not None:
            break
    else:
        raise AssertionError('no symmetry')
    l0, r0 = pair_word(g0, h0)
    lg, rg, pr = transport(base, l0, r0, W)
    assert (lg, rg) == pair_word(g, h)
    eq = LIB.add('P', pr, spw(rg), 'pair %s , %s' % (M.gname(g), M.gname(h)))
    _E[(g, h)] = eq
    return eq


def pair_steps(g, h, new):
    """Steps for sp(g h) -> sp(new), new one of h g / h g k / k h g."""
    k = FULL_PAIR[(g, h)]
    G, H = sp(g), sp(h)
    pr = Proof(G + H)
    if tuple(new[:2]) == (h, g):
        # g h -> h h g h -> h g g h g h -> h g k
        pr.rw(0, inv(h).sym())
        pr.rw(len(H), inv(g).sym())
        pr.rw(len(H) + len(G), E(g, h))
    else:
        # g h -> g h g g -> g h g h h g -> k h g
        assert tuple(new[1:]) == (h, g)
        pr.rw(len(G) + len(H), inv(g).sym())
        pr.rw(len(G) + len(H) + len(G), inv(h).sym())
        pr.rw(0, E(g, h))
    assert pr.cur == spw(new), (pr.cur, spw(new))
    return pr.steps


# ----------------------------------------------------------------------
# Compiling a macro derivation

def occurrences(word):
    seen = {}
    out = []
    for g in word:
        k = seen.get(g, 0)
        seen[g] = k + 1
        out.append((g, k))
    return out


def compile_macro(start, steps, goal=()):
    """The derivation sp(start) -> sp(goal) that follows the macro steps."""
    cur = list(start)
    pr = Proof(spw(cur))

    def off(j):
        return len(spw(cur[:j]))

    for st in steps:
        lin = list(st['lin'])
        # bring the word to the linearisation the step is stated for
        want = {o: i for i, o in enumerate(occurrences(lin))}
        key = [want[o] for o in occurrences(cur)]
        n = len(cur)
        for a in range(n):
            for j in range(n - 1 - a):
                if key[j] > key[j + 1]:
                    pr.rw(off(j), comm(cur[j], cur[j + 1]))
                    cur[j], cur[j + 1] = cur[j + 1], cur[j]
                    key[j], key[j + 1] = key[j + 1], key[j]
        assert cur == lin
        i = st['i']
        if st['kind'] == 'narrow':
            j = st['j']
            old, new = cur[i:j], list(st['new'])
            triple = tuple(st['triple'])
            if len(triple) < 3:
                triple = [t for t in TRIPLE_FRAME if set(triple) <= set(t)][0]
            p = TRIPLE_FRAME[triple]
            o = off(i)
            if not p:
                pr.rw(o, Bot(spw(old), spw(new)))
            else:
                pr_ = rev(p)
                b_old = [sp(relabel(g, triple)) for g in old]
                b_new = [sp(relabel(g, triple)) for g in new]
                x = o
                if not old:
                    pr.rw(o, HS('', p + pr_))
                for g, b in zip(old, b_old):
                    pr.run(to_frame(g, p, b), x)
                    x += 2 * len(p) + len(b)
                x = o + len(p)
                for k, b in enumerate(b_old):
                    x += len(b)
                    if k + 1 < len(b_old):
                        pr.rw(x, HS(pr_ + p, ''))
                pr.rw(o + len(p), Bot(''.join(b_old), ''.join(b_new)))
                if not new:
                    pr.rw(o, HS(p + pr_, ''))
                else:
                    x = o + len(p)
                    for k, b in enumerate(b_new):
                        x += len(b)
                        if k + 1 < len(b_new):
                            pr.rw(x, HS('', pr_ + p))
                            x += 2 * len(p)
                    x = o
                    for g, b in zip(new, b_new):
                        pr.run(backwards(to_frame(g, p, b)), x)
                        x += len(sp(g))
            cur[i:j] = new
        elif st['kind'] == 'pair':
            g, h = st['old']
            assert cur[i:i + 2] == [g, h]
            pr.run(pair_steps(g, h, st['new']), off(i))
            cur[i:i + 2] = list(st['new'])
        else:
            (k,) = st['old']
            g, h = st['new'][:2]
            assert cur[i] == k and list(st['new']) == [g, h, g, h]
            pr.rw(off(i), E(g, h).sym())
            cur[i:i + 1] = list(st['new'])
        assert pr.cur == spw(cur)
    assert cur == list(goal), (cur, goal)
    return pr


def relator_to_equation(lhs, rhs, rel_eq):
    """rel_eq: sp(lhs rhs^-1) -> empty.  The proof of sp(lhs) -> sp(rhs)."""
    pr = Proof(spw(lhs))
    n = len(pr.cur)
    for g in reversed(rhs):
        pr.rw(n, inv(g).sym())           # insert g g, inside out
        n += len(sp(g))
    pr.rw(0, rel_eq)
    assert pr.cur == spw(rhs)
    return pr
