# Piece against piece: a three-wire piece black on c (hybsep2.Bar, Tof)
# passes a three-wire piece coloured white on c (Barenco's word or a
# Toffoli between X letters).  The white piece is rewritten, by one window
# on its own wires, into white units and one plain white Barenco or
# Toffoli, each of which the black piece passes:
#   - white units and Toffolis: hybsep2 (spellings, configurations I-IV);
#   - a white Barenco on Q's target off Q's control: group by group, the
#     two roots being powers of one root of V (hybsep.pass_groups);
#   - on the fourth wire u controlled by Q's control x: a commutator
#     [Lambda_not-c(alpha_u), Lambda_x(beta_u)] of units Q passes;
#   - the other placements: conjugated there by a white Fredkin, three
#     white Toffolis.
# A black Toffoli is handled through the duality X_c: it passes a white
# piece when the piece, its colour on c exchanged, passes the white
# Toffoli.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import Derivation, fp, norm, show, inv, supp
import passes as P
from passes import L
import gadgetlib as GL
from gadgetlib import lam, INV1, wnorm, winv
import hybsep2 as H
from hybsep2 import Bar, Tof, spell_pass, seq_pass, via, wtof, wtof_pass, find_comm, groups_of
from hybsep import pass_groups, white
from dec import barenco, inv1
from hybsep2 import alg

XW = list(GL.XW)                                    # X = K S S K^-1 as a one-qubit word

def xs(S): return [('X', w) for w in sorted(S)]
def wword(c, w, word):
    """Lambda_not-c(word on w) as letters."""
    return norm(white(c, [l for g in word for l in lam(c, w, g)]))
def bword(c, w, word):
    return norm([l for g in word for l in lam(c, w, g)])

# ------------------------------------------------------------ white Barencos
class WBar:
    """L_{not-c, y}((wv)^2 on t), spelled X_c barenco(wv, c, y, t) X_c."""
    def __init__(self, wv, c, y, t): self.wv, self.c, self.y, self.t = list(wv), c, y, t
    def word(self): return norm(white(self.c, barenco(self.wv, self.c, self.y, self.t)))
    def groups(self):
        g = groups_of(norm(barenco(self.wv, self.c, self.y, self.t)))
        c = self.c
        return [norm(white(c, g[0])), norm(white(c, g[1])), g[2], norm(white(c, g[3])), g[4]]
    def __repr__(self): return f'WBar({"".join(self.wv)};~{self.c},{self.y}->{self.t})'

def fredkin(c, a, b):
    """Lambda_not-c(SWAP(a, b)) as three white Toffolis (units)."""
    return [wtof(a, c, b), wtof(b, c, a), wtof(a, c, b)]

def bar_wbar(Q, R):
    """the black Barenco Q passes the plain white Barenco R."""
    Qw = Q.word(); Rw = R.word()
    name = P.pname([tuple(Qw)], [tuple(Rw)])
    if name in L: return name
    c, x, t = Q.c, Q.x, Q.t
    u = ({0, 1, 2, 3} - {c, x, t}).pop()
    assert R.c == c
    if {R.y, R.t} <= {x, t}:
        return P.done_as(name, [tuple(Qw)], [tuple(Rw)], lambda d: d.win(0, len(Qw) + len(Rw), Rw + Qw))
    if (R.t, R.y) == (t, u):
        Gs = R.groups(); Gf = [l for g in Gs for l in g]
        inner = pass_groups(f'{Q!r} passes groups of {R!r}', groups_of(Qw), Gs)
        return via(name, Qw, Rw, Gf, None, inner)
    if (R.t, R.y) == (u, x):
        a, b = find_comm(R.wv)
        units = ([tuple(wword(c, u, [g])) for g in a] + [tuple(bword(x, u, [g])) for g in b]
                 + [tuple(wword(c, u, [g])) for g in winv(a)] + [tuple(bword(x, u, [g])) for g in winv(b)])
        E = [l for z in units for l in z]
        assert fp(E) == fp(Rw), 'commutator form'
        inner = seq_pass(f'{Q!r} passes comm {R!r}', Qw, units, lambda z: spell_pass(Q, z))
        return via(name, Qw, Rw, E, None, inner)
    # conjugate by a white Fredkin into one of the cases above
    if (R.t, R.y) == (x, u): a, b, R2 = x, u, WBar(R.wv, c, x, u)
    elif (R.t, R.y) == (u, t): a, b, R2 = t, u, WBar(R.wv, c, u, t)
    else: raise H.Fail(('placement', repr(Q), repr(R)))
    F = fredkin(c, a, b)
    units = F + [tuple(R2.word())] + F
    E = [l for z in units for l in z]
    assert fp(E) == fp(Rw), 'Fredkin form'
    def fn(z):
        if z == tuple(R2.word()): return bar_wbar(Q, R2)
        return wtof_pass(Q, z[1][1], [w for w in z[1][2:] if w != c][0])
    inner = seq_pass(f'{Q!r} passes Fredkin {R!r}', Qw, units, fn)
    return via(name, Qw, Rw, E, None, inner)

# ------------------------------------------------------------ coloured pieces
def parse(Rl, c):
    """a coloured piece X_S core X_S -> (S, core)."""
    k = 0
    while Rl[k][0] == 'X': k += 1
    S = [g[1] for g in Rl[:k]]
    core = Rl[k:len(Rl) - k]
    assert Rl[len(Rl) - k:] == Rl[:k] and c in S
    return S, core

def is_bar(core): return any(g[0] == 'CX' for g in core)

def bar_of(core, c):
    """(wv, y, t) with core = barenco(wv, c, y, t) normalised."""
    cxs = [g for g in core if g[0] == 'CX']
    a, y = cxs[0][1], cxs[0][2]
    assert a == c, ('the CNOT between the controls must come from c', show(core))
    t = [w for g in core for w in g[1:] if w not in (c, y)][0]
    i = core.index(cxs[0])
    letters = core[:i]
    wv = [{'CS': 'S', 'CK': 'K', 'S': 'i'}[g[0]] for g in letters]
    assert norm(barenco(wv, c, y, t)) == list(core), show(core)
    return wv, y, t

def white_factors(Rl, c):
    """units, each a white unit or a plain white Barenco or white Toffoli,
    with product the coloured piece Rl (one window on its wires)."""
    S, core = parse(Rl, c)
    if is_bar(core):
        wv, y, t = bar_of(core, c)
        G = alg(wv) + alg(wv)
        out = []; mid = []
        root = wv
        if y in S:                                   # L_{~c,~y}(G) = Lambda_~c(G) L_{~c,y}(G^-1)
            mid.append(tuple(wword(c, t, wnorm(G))))
            root = inv1(wv)
        mid.append(('WBAR', tuple(root), y, t))
        if t in S:                                   # conjugated by Lambda_~c(X_t)
            xw = tuple(wword(c, t, XW))
            mid = [xw] + mid + [xw]
        return mid
    # a Toffoli: X on its target is dropped, X on the other control kept
    (g,) = core
    z, a, b = g[1], g[2], g[3]
    o = b if a == c else a
    if o in S:
        return [tuple(norm(white(c, [('CX', c, z)]))), wtof(z, c, o)]
    return [wtof(z, c, o)]

def unit_of(f, c):
    if f[0] == 'WBAR': return tuple(WBar(list(f[1]), c, f[2], f[3]).word())
    return f

def bar_white_piece(Q, Rl):
    """the black Barenco Q passes the coloured white piece Rl."""
    Qw = Q.word(); Rl = norm(list(Rl))
    name = P.pname([tuple(Qw)], [tuple(Rl)])
    if name in L: return name
    c = Q.c
    fs = white_factors(Rl, c)
    units = [unit_of(f, c) for f in fs]
    E = [l for z in units for l in z]
    assert fp(norm(E)) == fp(Rl), ('factors', show(Rl))
    def fn(z):
        f = fs[units.index(z)]
        if f[0] == 'WBAR': return bar_wbar(Q, WBar(list(f[1]), c, f[2], f[3]))
        if any(g[0] == 'TOFF' for g in z): return H.coloured_pass(Q, z)
        return spell_pass(Q, z)
    inner = seq_pass(f'{Q!r} passes factors of {show(Rl)}', Qw, units, fn)
    if E == Rl: return inner if inner == name else via(name, Qw, Rl, E, None, inner)
    return via(name, Qw, Rl, E, None, inner)

# ------------------------------------------------------------ black Toffolis, by duality
class WTof:
    """Toff(z; not-c, w) as a piece: a white CCZ between white K's on z."""
    def __init__(self, z, c, w): self.z, self.c, self.w = z, c, w
    def word(self, sp=None): return list(wtof(self.z, self.c, self.w))
    def spellings(self):
        z, c, w = self.z, self.c, self.w
        alt = wword(c, z, ['K']) + norm([('CZ', w, z)] + H.ccz_sp(c, w, z)) + wword(c, z, ['Kd'])
        return [self.word(), norm(alt)]
    def wires(self): return {self.z, self.c, self.w}
    def __repr__(self): return f'WTof({self.z};~{self.c},{self.w})'

def black_factors(Rl, c):
    """units, black units and plain black Barencos or Toffolis, with product
    the coloured piece Rl black on c (one window on its wires)."""
    k = 0
    while Rl[k][0] == 'X': k += 1
    S = [g[1] for g in Rl[:k]]; core = Rl[k:len(Rl) - k]
    assert c not in S
    if is_bar(core):
        wv, y, t = bar_of(core, c)
        G = alg(wv) + alg(wv); root = wv; mid = []
        if y in S:
            mid.append(('U', tuple(bword(c, t, wnorm(G)))))
            root = inv1(wv)
        mid.append(('BAR', Bar(root, c, y, t)))
        if t in S:
            xw = ('U', tuple(bword(c, t, XW)))
            mid = [xw] + mid + [xw]
        return mid
    (g,) = core
    z, a, b = g[1], g[2], g[3]
    o = b if a == c else a
    if o in S:
        return [('U', tuple(norm([('CX', c, z)]))), ('TOF', Tof(z, c, o))]
    return [('TOF', Tof(z, c, o))]

def atom_word(f): return list(f[1]) if f[0] == 'U' else f[1].word()

def black_passes_wtof(Rl, z, c, w):
    """the coloured black piece Rl passes Toff(z; not-c, w)."""
    T = list(wtof(z, c, w)); Rl = norm(list(Rl))
    name = P.pname([tuple(Rl)], [tuple(T)])
    if name in L: return name
    fs = black_factors(Rl, c)
    E = [l for f in fs for l in atom_word(f)]
    assert fp(norm(E)) == fp(Rl)
    W = WTof(z, c, w)
    d = Derivation(name, Rl + T, T + Rl, L)
    if E != Rl: d.win(0, len(Rl), E)
    pos = len(E)
    for f in reversed(fs):
        aw = atom_word(f); pos -= len(aw)
        if f[0] == 'BAR': d.lemma(wtof_pass(f[1], z, w), pos)
        elif f[0] == 'U': d.lemma(pass_spelled(tuple(aw), WTofG(z, c, w)), pos)
        else: d.lemma(tof_wtof(f[1], z, w), pos)
    if E != Rl: d.win(len(T), len(T) + len(E), Rl)
    d.done(); return name

def toggle(Rl, c):
    """X_c R X_c with the X letters merged: the piece with its colour on c exchanged."""
    k = 0
    while Rl[k][0] == 'X': k += 1
    S = set(g[1] for g in Rl[:k]) ^ {c}; core = Rl[k:len(Rl) - k]
    return norm(xs(S) + list(core) + xs(S))

def tof_white_piece(Q, Rl):
    """the black Toffoli Q passes the coloured white piece Rl."""
    Ql = Q.word(); Rl = norm(list(Rl)); c = Q.c
    name = P.pname([tuple(Ql)], [tuple(Rl)])
    if name in L: return name
    Rt = toggle(Rl, c); Qt = list(wtof(Q.z, c, Q.w))
    inner = black_passes_wtof(Rt, Q.z, c, Q.w)
    X = [('X', c)]
    d = Derivation(name, Ql + Rl, Rl + Ql, L)
    d.win(0, 1, X + Qt + X)
    p = 1 + len(Qt)
    d.win(p, p + 1 + len(Rl), Rt + X)                  # X_c R -> R~ X_c
    d.lemma(inner, 1, forward=False)                  # Q~ R~ -> R~ Q~
    d.win(0, 1 + len(Rt), Rl + X)                     # X_c R~ -> R X_c
    d.win(len(Rl), len(Rl) + 2 + len(Qt), Ql)
    d.done(); return name

def piece_piece(Q, Rl):
    return bar_white_piece(Q, Rl) if isinstance(Q, Bar) else tof_white_piece(Q, Rl)

# ------------------------------------------------------------ both sides respelled
def gspellings(X):
    """spellings of a piece as lists of groups (a white unit kept whole)."""
    if isinstance(X, tuple) or isinstance(X, list): return [[list(X)]]
    if hasattr(X, 'gsp'): return X.gsp()
    return [[[l] for l in s] for s in X.spellings()]

def wordof(X): return list(X) if isinstance(X, (tuple, list)) else X.word()

def _ok(ga, gb):
    sa, sb = supp(ga), supp(gb)
    if not (sa & sb): return True
    return len(sa | sb) <= 3 and fp(norm(ga + gb)) == fp(norm(gb + ga))

def pass_spelled(A, B):
    """A passes B, both respelled by one window each so that every group of
    one meets every group of the other in a window or not at all."""
    Aw, Bw = norm(wordof(A)), norm(wordof(B))
    name = P.pname([tuple(Aw)], [tuple(Bw)])
    if name in L: return name
    for sa in gspellings(A):
        for sb in gspellings(B):
            if all(_ok(ga, gb) for ga in sa for gb in sb):
                fa = norm([l for g in sa for l in g]); fb = norm([l for g in sb for l in g])
                inner = pass_groups(f'groups [{show(fa)}] [{show(fb)}]', [norm(g) for g in sa], [norm(g) for g in sb])
                d = Derivation(name, Aw + Bw, Bw + Aw, L)
                if fb != Bw: d.win(len(Aw), len(Aw) + len(Bw), fb)
                if fa != Aw: d.win(0, len(Aw), fa)
                d.lemma(inner, 0)
                if fa != Aw: d.win(len(fb), len(fb) + len(fa), Aw)
                if fb != Bw: d.win(0, len(fb), Bw)
                d.done(); return name
    raise H.Fail(('no joint spelling', show(Aw), show(Bw)))

def wtof_g(z, c, w):
    """the white Toffoli's spellings as groups."""
    whole = [list(wtof(z, c, w))]
    out = [whole]
    for (a, b) in ((w, z), (z, w)):
        out.append([wword(c, z, ['K'])] + [[l] for l in norm([('CZ', w, z)] + H.ccz_sp(c, a, b))] + [wword(c, z, ['Kd'])])
    return out

class WTofG:
    def __init__(self, z, c, w): self.z, self.c, self.w = z, c, w
    def word(self): return list(wtof(self.z, self.c, self.w))
    def gsp(self): return wtof_g(self.z, self.c, self.w)

class TofG:
    """a black Toffoli's spellings: whole, and CK(c,z) CCZ CK(c,z)^-1 with the CCZ spelled both ways."""
    def __init__(self, z, c, w): self.z, self.c, self.w = z, c, w
    def word(self): return norm([('TOFF', self.z, self.c, self.w)])
    def gsp(self):
        z, c, w = self.z, self.c, self.w
        out = [[self.word()]]
        for e in (c, w, z):
            o = [v for v in (c, w, z) if v != e]
            for (a, b) in ((o[0], o[1]), (o[1], o[0])):
                out.append([[l] for l in norm([('CK', c, z)] + H.ccz_sp(e, a, b) + [('CKd', c, z)])])
                out.append([[l] for l in norm([('K', z)] + H.ccz_sp(e, a, b) + [('Kd', z)])])
        return out

def tof_wtof(Q, y, v):
    """the black Toffoli Q = Toff(z; c, w) passes Toff(y; not-c, v)."""
    z, c, w = Q.z, Q.c, Q.w
    u = ({0, 1, 2, 3} - {z, c, w}).pop()
    T = list(wtof(y, c, v)); Ql = Q.word()
    name = P.pname([tuple(Ql)], [tuple(T)])
    if name in L: return name
    if {y, v} <= {z, w}:
        return P.done_as(name, [tuple(Ql)], [tuple(T)], lambda d: d.win(0, len(Ql) + len(T), T + Ql))
    if y == z: return P.prove([tuple(Ql)], [tuple(T)])
    if v == z:                                         # white K's on y and z bring the target to z
        units = [tuple(wword(c, y, ['K'])), tuple(wword(c, z, ['K'])), wtof(z, c, y),
                 tuple(wword(c, z, ['Kd'])), tuple(wword(c, y, ['Kd']))]
        E = [l for x in units for l in x]
        assert fp(norm(E)) == fp(norm(T))
        def fn(x):
            if x == wtof(z, c, y): return P.prove([tuple(Ql)], [x])
            return pass_spelled(TofG(z, c, w), x)
        inner = seq_pass(f'{Q!r} passes K-conj {show(T)}', Ql, units, fn)
        return via(name, Ql, T, E, None, inner)
    return pass_spelled(TofG(z, c, w), WTofG(y, c, v))
