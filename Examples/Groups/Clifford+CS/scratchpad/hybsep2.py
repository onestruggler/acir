# Separated commutation of three-wire pieces black on a wire c against
# gates white on c, at four wires: the toolkit for the hybrid's far facts
# once the hybrid is a product of such pieces (t_lf.LF, Barenco's
# three-control decomposition, registered here as a provisional axiom).
#
# A piece Q is a Barenco word L_cx(W^2_t) (black on c and x) or a
# Toffoli Toff(z; c, w).  A three-wire piece may be respelled by one
# window, so each white letter is passed by the spelling whose letters it
# meets only in windows or not at all (`spell_pass`): the c-spelling
# (Barenco with c as the CNOT control) for a white unit off the piece,
# the x-spelling for a gate diagonal on x.  On top of it:
#   - the four white Toffolis Toff(y; not-c, v) the piece does not hold
#     (configurations I-IV), I by the white Barenco of V (hybsep.bar_tof
#     generalised), III as I conjugated by white K's, II and IV as a white
#     CCZ conjugated by a white K;
#   - a white K-free gadget: its target word split off (ca_split), then
#     the diagonal core spelled [Toff, CS] with the CS on a wire the piece
#     sees diagonally, or, when the gadget's target is the piece's, the
#     piece as a commutator [Lambda_c(alpha), Lambda_x(beta)] of units,
#     which the controlled action carries across.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import Derivation, fp, norm, show, inv, supp
import passes as P
from passes import L
import gadgetlib as GL
from gadgetlib import Gad, lam, nc_unit, INV1, wnorm, winv, W1, _fp1
from dec import barenco, inv1

def alg(w):
    """a root word of dec's alphabet (S, K, the phase i) as a word over S, Sd, K, Kd."""
    return [h for g in w for h in (['K'] * 6 if g == 'i' else [g])]
from hybsep import pass_groups, white

class Fail(Exception): pass

# ------------------------------------------------------------ pieces
class Bar:
    """L_cx((wv)^2 on t), spelled by Barenco's word with root wv."""
    def __init__(self, wv, c, x, t): self.wv, self.c, self.x, self.t = wv, c, x, t
    def word(self, sp='c'):
        a, b = (self.c, self.x) if sp == 'c' else (self.x, self.c)
        return norm(barenco(self.wv, a, b, self.t))
    def spellings(self):
        out = [self.word('c'), self.word('x')]
        try:
            out.append(norm(comm_units(self)))
        except Exception: pass
        return out
    def wires(self): return {self.c, self.x, self.t}
    def __repr__(self): return f'Bar({self.wv};{self.c},{self.x}->{self.t})'

def ccz_sp(c, a, b):
    """CCZ(c, a, b) with c only in CS letters, the CNOT from a to b."""
    return [('CS', c, a), ('CS', c, b), ('CX', a, b), ('CSd', c, b), ('CX', a, b)]

class Tof:
    """Toff(z; c, w), black on c."""
    def __init__(self, z, c, w): self.z, self.c, self.w = z, c, w
    def word(self, sp=None): return norm([('TOFF', self.z, self.c, self.w)])
    def spellings(self):
        z, c, w = self.z, self.c, self.w
        return [self.word(), norm([('CK', c, z)] + ccz_sp(c, w, z) + [('CKd', c, z)])]
    def wires(self): return {self.z, self.c, self.w}
    def __repr__(self): return f'Tof({self.z};{self.c},{self.w})'

# ------------------------------------------------------------ letterwise passing
def commutes(a, b): return fp(norm(list(a) + list(b))) == fp(norm(list(b) + list(a)))

def letter_ok(a, b):
    """letter a passes the unit b by one window or by disjointness."""
    sa, sb = supp([a]), supp(list(b))
    if not (sa & sb): return True
    return len(sa | sb) <= 3 and commutes([a], b)

def pass_word(d, pos, A, b):
    """at pos: the word A then the unit b; b moves to the front, letter by letter of A."""
    b = list(b)
    for i in range(len(A) - 1, -1, -1):
        a = A[i]; q = pos + i
        if not (supp([a]) & supp(b)):
            for j in range(len(b)): d.comm(q + j)
        else:
            d.win(q, q + 1 + len(b), b + [a])

def spell_pass(Q, b):
    """lemma: Q passes the unit b, through a spelling of Q met letterwise."""
    Qw = Q.word(); b = tuple(norm(list(b)))
    name = P.pname([tuple(Qw)], [b])
    if name in L: return name
    if not commutes(Qw, b): raise Fail(('do not commute', repr(Q), show(list(b))))
    if len(supp(Qw) | supp(list(b))) <= 3:
        return P.done_as(name, [tuple(Qw)], [b], lambda d: d.win(0, len(Qw) + len(b), list(b) + Qw))
    for s in Q.spellings():
        if all(letter_ok(a, b) for a in s):
            def st(d, s=s):
                if s != Qw: d.win(0, len(Qw), s)
                pass_word(d, 0, s, b)
                if s != Qw: d.win(len(b), len(b) + len(s), Qw)
            return P.done_as(name, [tuple(Qw)], [b], st)
    raise Fail(('no spelling', repr(Q), show(list(b))))

def seq_pass(name, Qw, units, fn):
    """Q passes the units in turn; fn(unit) names the lemma Q u -> u Q."""
    if name in L: return name
    fl = [g for u in units for g in u]
    d = Derivation(name, Qw + fl, fl + Qw, L)
    pos = 0
    for u in units:
        d.lemma(fn(u), pos); pos += len(u)
    d.done(); return name

def via(name, Qw, B, Bx, lem, inner):
    """Q B -> B Q from B -> Bx (lemma lem, or a window when lem is None)
    and inner: Q Bx -> Bx Q."""
    if name in L: return name
    d = Derivation(name, Qw + B, B + Qw, L)
    if lem is None: d.win(len(Qw), len(Qw) + len(B), Bx)
    else: d.lemma(lem, len(Qw))
    d.lemma(inner, 0)
    if lem is None: d.win(0, len(Bx), B)
    else: d.lemma(lem, 0, forward=False)
    d.done(); return name

# ------------------------------------------------------------ white Toffolis
def wtof(y, c, v):
    """Toff(y; not-c, v)."""
    return tuple(norm([('X', c), ('TOFF', y, c, v), ('X', c)]))

def wunit(c, w, g): return tuple(norm(white(c, lam(c, w, g))))

def groups_of(word):
    cx = [k for k, g in enumerate(word) if g[0] == 'CX']
    a, b = cx
    return [word[:a], [word[a]], word[a + 1:b], [word[b]], word[b + 1:]]

def config_I(Q, u):
    """Q (a Barenco) passes Toff(t; not-c, u), u off Q: hybsep.bar_tof for any root."""
    t, c = Q.t, Q.c
    T = list(wtof(t, c, u)); Qw = Q.word()
    name = P.pname([tuple(Qw)], [tuple(T)])
    if name in L: return name
    Gg = groups_of(norm(barenco('SSKS', c, u, t)))
    G = [white(c, Gg[0]), white(c, Gg[1]), Gg[2], white(c, Gg[3]), Gg[4]]
    Gi = [norm(inv(list(g))) for g in reversed(G)]
    U = [white(c, [('CS', c, t)] * 3)]
    Ui = [norm(inv(list(g))) for g in reversed(U)]
    Szi = [white(c, [('CSd', c, u)])]
    E = [norm(list(g)) for g in Szi + Gi + U + Gi + Ui]
    Ew = [g for gr in E for g in gr]
    assert fp(norm(Ew)) == fp(norm(T)), 'expansion'
    inner = pass_groups(f'{Q!r} passes white iX via V2 conjugates {u}', groups_of(Qw), E)
    return via(name, Qw, T, Ew, None, inner)

def config_III(Q, u):
    """Q passes Toff(u; not-c, t): config I conjugated by white K on u and t."""
    t, c = Q.t, Q.c
    T = list(wtof(u, c, t)); Qw = Q.word()
    name = P.pname([tuple(Qw)], [tuple(T)])
    if name in L: return name
    units = [wunit(c, u, 'K'), wunit(c, t, 'K'), wtof(t, c, u), wunit(c, t, 'Kd'), wunit(c, u, 'Kd')]
    Ew = [g for x in units for g in x]
    assert fp(norm(Ew)) == fp(norm(T)), 'config III expansion'
    def fn(x):
        if x == wtof(t, c, u): return config_I(Q, u)
        return spell_pass(Q, x)
    inner = seq_pass(f'{Q!r} passes III units {u}', Qw, units, fn)
    return via(name, Qw, T, Ew, None, inner)

def config_II_IV(Q, y, v):
    """Q passes Toff(y; not-c, v), {y, v} = {x, u}: a white CCZ conjugated by a white K on y."""
    c, x = Q.c, Q.x
    T = list(wtof(y, c, v)); Qw = Q.word()
    name = P.pname([tuple(Qw)], [tuple(T)])
    if name in L: return name
    o = v if y == x else y                               # the wire off Q
    letters = [('CZ', x, o)] + ccz_sp(c, x, o)            # X_c CCZ(c,x,o) X_c
    units = [wunit(c, y, 'K')] + [tuple(norm([g])) for g in letters] + [wunit(c, y, 'Kd')]
    Ew = [g for z in units for g in z]
    assert fp(norm(Ew)) == fp(norm(T)), 'config II/IV expansion'
    inner = seq_pass(f'{Q!r} passes II/IV units {y} {v}', Qw, units, lambda z: spell_pass(Q, z))
    return via(name, Qw, T, Ew, None, inner)

def wtof_pass(Q, y, v):
    """Q (a Barenco) passes Toff(y; not-c, v)."""
    c, x, t = Q.c, Q.x, Q.t
    u = ({0, 1, 2, 3} - {c, x, t}).pop()
    T = wtof(y, c, v)
    if {y, v} <= {x, t}: return spell_pass(Q, T)
    if (y, v) == (t, u): return config_I(Q, u)
    if (y, v) == (u, t): return config_III(Q, u)
    return config_II_IV(Q, y, v)

# ------------------------------------------------------------ white K-free gadgets
LET = {'CS': 'S', 'CSd': 'Sd', 'CK': 'K', 'CKd': 'Kd'}

def find_comm(wv):
    """(alpha, beta), one-qubit words with alpha beta alpha^-1 beta^-1 = wv wv exactly."""
    target = _fp1(alg(wv) + alg(wv))
    els = sorted(W1.values(), key=len)
    best = None
    for a in els:
        for b in els:
            if _fp1(a + b + winv(a) + winv(b)) == target:
                if best is None or len(a) + len(b) < len(best[0]) + len(best[1]): best = (a, b)
    return best

def comm_units(Q):
    """Q as A N A^-1 N^-1, A = Lambda_c(alpha_t), N = Lambda_x(beta_t), as letters."""
    a, b = find_comm(Q.wv)
    A = [lam(Q.c, Q.t, g)[0] for g in a]
    N = [lam(Q.x, Q.t, g)[0] for g in b]
    Ai = [lam(Q.c, Q.t, g)[0] for g in winv(a)]
    Ni = [lam(Q.x, Q.t, g)[0] for g in winv(b)]
    return A + N + Ai + Ni

def move_left(d, pos, letters, g, colour_c):
    """at pos: the unit letters (each Lambda_ctrl(h_t), t = g.t), then the
    gadget g; g moves to pos.  Returns the gadget it has become."""
    cur = g
    for i in range(len(letters) - 1, -1, -1):
        l = letters[i]; h = LET[l[0]]
        ctrl = [w for w in l[1:] if w != g.t][0]
        if ctrl in cur.W:
            d.lemma(GL.unit_pass(ctrl, g.t, h, True, cur), pos + i)
        else:
            nm, cur2 = GL.ca(ctrl, h, cur)
            d.lemma(nm, pos + i); cur = cur2
    return cur

def same_target(Q, g):
    """Q passes the diagonal gadget g (d = ()), same target, c white in g."""
    Qw = Q.word(); gl = g.letters()
    name = P.pname([tuple(Qw)], [tuple(gl)])
    if name in L: return name
    cu = comm_units(Q)
    assert fp(norm(cu)) == fp(Qw), 'commutator form'
    d = Derivation(name, Qw + gl, gl + Qw, L)
    d.win(0, len(Qw), cu)
    g2 = move_left(d, 0, cu, g, True)
    assert g2.letters() == gl, (g2, g)
    d.win(len(gl), len(gl) + len(cu), Qw)
    d.done(); return name

def distribute(d, p, W, f):
    """at p: X_W f X_W (f a list of letters); afterwards the coloured units
    X_{W_i} f_i X_{W_i}, W_i = W meeting f_i.  Returns their letters."""
    xs = [('X', w) for w in sorted(W)]; k = len(xs)
    pos = p + k
    for i in range(len(f) - 1):                        # X_W X_W after each letter but the last
        pos += 1
        d.win(pos, pos, xs + xs)
        pos += 2 * k
    # each segment X_W f_i X_W: drop the X's off f_i
    out = []; q = p
    for i, g in enumerate(f):
        Wi = [w for w in sorted(W) if w in g[1:]]
        cur = xs + [g] + xs
        for w in sorted(W):
            if w in Wi: continue
            l = cur.index(('X', w)); r = len(cur) - 1 - cur[::-1].index(('X', w))
            while l + 1 < r:
                d.comm(q + l); cur[l], cur[l + 1] = cur[l + 1], cur[l]; l += 1
            d.win(q + l, q + l + 2, []); del cur[l:l + 2]
        seg = [('X', w) for w in Wi] + [g] + [('X', w) for w in Wi]
        assert cur == seg, (cur, seg)
        out.append(tuple(seg)); q += len(seg)
    return out

def coloured_pass(Q, unit):
    """Q passes a coloured letter of a [Toff, CS] core (white on c when it holds c)."""
    xs = [g[1] for g in unit if g[0] == 'X']
    core = [g for g in unit if g[0] != 'X']
    if len(core) == 1 and core[0][0] == 'TOFF' and Q.c in core[0][2:]:
        y = core[0][1]; o = [w for w in core[0][2:] if w != Q.c][0]
        if len(supp(list(unit)) | Q.wires()) <= 3: return spell_pass(Q, unit)
        if o not in xs: return wtof_pass(Q, y, o)
        # X_o Toff(y; not-c, o) X_o = Lambda_not-c(X_y) Toff(y; not-c, o)
        Qw = Q.word()
        name = P.pname([tuple(Qw)], [tuple(unit)])
        if name in L: return name
        units = [tuple(norm(white(Q.c, [('CX', Q.c, y)]))), wtof(y, Q.c, o)]
        Ew = [g for z in units for g in z]
        assert fp(norm(Ew)) == fp(norm(list(unit)))
        inner = seq_pass(f'{Q!r} passes II-white units {y} {o}', Qw, units,
                         lambda z: wtof_pass(Q, y, o) if z == wtof(y, Q.c, o) else spell_pass(Q, z))
        return via(name, Qw, list(unit), Ew, None, inner)
    return spell_pass(Q, unit)

def gather(g, f, lem, units):
    """lemma: the gadget's letters -> the coloured units of its form f."""
    name = f'distribute {g!r} {show(f)}'
    if name in L: return name
    e = Derivation(name, g.letters(), [x for un in units for x in un], L)
    if lem: e.lemma(lem, len(g.W))
    distribute(e, 0, g.W, f)
    e.done(); return name

def diag_gadget_pass(Q, g):
    """Q passes the diagonal gadget g, white on Q.c."""
    assert not g.d and Q.c in g.W
    if g.t == Q.t: return same_target(Q, g)
    Qw = Q.word(); gl = g.letters()
    name = P.pname([tuple(Qw)], [tuple(gl)])
    if name in L: return name
    u = ({0, 1, 2, 3} - Q.wires()).pop()
    k = u if g.t == Q.x else Q.x
    lem, f = GL.form_lemma(g.t, k, g.e)
    d = Derivation(name, Qw + gl, gl + Qw, L)
    if lem: d.lemma(lem, len(Qw) + len(g.W))
    units = distribute(d, len(Qw), g.W, f)
    p = 0
    for un in units:
        d.lemma(coloured_pass(Q, un), p); p += len(un)
    d.lemma(gather(g, f, lem, units), 0, forward=False)
    d.done(); return name

def gadget_pass(Q, g):
    """Q passes the K-free gadget g, white on Q.c: its target word split off."""
    Qw = Q.word(); gl = g.letters()
    name = P.pname([tuple(Qw)], [tuple(gl)])
    if name in L: return name
    if not g.d: return diag_gadget_pass(Q, g)
    sA, sm, g0 = GL.ca_split(g, Q.c)
    smi = [GL.cunit(Q.c, g.t, INV1[y], False) for y in reversed(g.d)]
    units = list(sm) + [tuple(g0.letters())] + smi
    def fn(z):
        if z == tuple(g0.letters()): return diag_gadget_pass(Q, g0)
        return spell_pass(Q, z)
    inner = seq_pass(f'{Q!r} passes split {g!r}', Qw, units, fn)
    d = Derivation(name, Qw + gl, gl + Qw, L)
    d.lemma(sA, len(Qw)); d.lemma(inner, 0); d.lemma(sA, 0, forward=False)
    d.done(); return name

class CCZp:
    """CCZ(c, w, z) as a piece: c only in CS letters in its other spellings."""
    def __init__(self, c, w, z): self.c, self.w, self.z = c, w, z
    def word(self, sp=None): return norm([('CCZ', self.c, self.w, self.z)])
    def spellings(self):
        c, w, z = self.c, self.w, self.z
        return [self.word(), norm(ccz_sp(c, w, z)), norm(ccz_sp(c, z, w))]
    def wires(self): return {self.c, self.w, self.z}
    def __repr__(self): return f'CCZ({self.c},{self.w},{self.z})'

def ccz_gadget_pass(Z, g):
    """CCZ(c, w, z) passes the K-free gadget g white on c."""
    Zw = Z.word(); gl = g.letters()
    name = P.pname([tuple(Zw)], [tuple(gl)])
    if name in L: return name
    sA, sm, g0 = GL.ca_split(g, Z.c)
    smi = [GL.cunit(Z.c, g.t, INV1[y], False) for y in reversed(g.d)]
    g0l = tuple(g0.letters())
    units = list(sm) + [g0l] + smi
    def fn(z):
        if z == g0l: return P.prove([tuple(Zw)], GL.gu(g0))
        return spell_pass(Z, z)
    inner = seq_pass(f'{Z!r} passes split {g!r}', Zw, units, fn)
    if not g.d: return inner if inner == name else via(name, Zw, gl, gl, None, inner)
    d = Derivation(name, Zw + gl, gl + Zw, L)
    d.lemma(sA, len(Zw)); d.lemma(inner, 0); d.lemma(sA, 0, forward=False)
    d.done(); return name

def tof_gadget_pass(T, g):
    """Toff(z; c, w) passes the K-free gadget g white on c: CK(c,z) CCZ CK(c,z)^-1."""
    Tw = T.word(); gl = g.letters()
    name = P.pname([tuple(Tw)], [tuple(gl)])
    if name in L: return name
    c, z, w = T.c, T.z, T.w
    Z = CCZp(c, w, z)
    sp = norm([('CK', c, z)]) + Z.word() + norm([('CKd', c, z)])
    assert fp(sp) == fp(Tw)
    d = Derivation(name, Tw + gl, gl + Tw, L)
    d.win(0, 1, sp)
    d.lemma(GL.unit_pass(c, z, 'Kd', True, g), 2)
    d.lemma(ccz_gadget_pass(Z, g), 1)
    d.lemma(GL.unit_pass(c, z, 'K', True, g), 0)
    d.win(len(gl), len(gl) + 3, Tw)
    d.done(); return name

def piece_gadget_pass(Q, g):
    return gadget_pass(Q, g) if isinstance(Q, Bar) else tof_gadget_pass(Q, g)
