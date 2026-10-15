# The hybrid's shift fact at n = 4: l_c l_{c+1} k_c = k_{c+1} l_c l_{c+1}
# (three transport classes, which differ only in the hybrid's roles).
#
# At the class representative with the targets on wires 0 and 1, the two
# rotations A (target 0) and B (target 1) and their copies white on the
# common controls 2, 3 merge (consec4.merge_all) into F = A' B', a
# permutation of the target pair: SWAP01 X0 Lambda_not-1(X0).  So
#   A B Hc = F X^-1 Hc = F Hc X^-1                 (the copies are separated)
#          = SWAP X0 Z Hc X^-1 = SWAP X0 Hc Z X^-1 (Z white on 1, Hc black)
#          = Hc1 F X^-1 = Hc1 A B,
# SWAP X0 conjugating Hc = X0 H X0 to Hc1 by relabelling.
import sys, os, itertools
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
from deriv import Derivation, fp, norm, show, inv, relabel, rename_letter, BY_NAME
import passes as P
from passes import L
import gadgetlib as G
from gadgetlib import Gad
import facts4 as F
import consec4 as C4
import hyb_classes as HC
import hybsep2 as H
from hybfar import AX, lf_at
from hybsym import sym
from blocks import BD
from t_lf import HD

def ren(word, pi): return norm([rename_letter(g, pi) for g in word])

def perm_of(mid):
    ps = [p for p in itertools.permutations(range(4)) if ren(HD, p) == list(mid)]
    assert ps, show(list(mid))
    return ps[0]

def sym_at(mid):
    """lemma: mid -> mid with its single control exchanged with the second
    control of Barenco's pair.  Returns (lemma, new mid)."""
    pi = perm_of(mid)
    s = sym()
    name = relabel(s, pi, L)
    return name, L[name][1]

def respell_hyb(m1, m2):
    """lemma m1 -> m2, two spellings of one hybrid (same target and controls):
    Barenco's controls exchanged by windows, the single control by the symmetry."""
    m1, m2 = norm(list(m1)), norm(list(m2))
    if m1 == m2: return None
    name = f'respell hyb {show(m1)[:40]} -> {show(m2)[:40]}'
    if name in L: return name
    t1, s1, p1 = HC.hyb_roles(m1); t2, s2, p2 = HC.hyb_roles(m2)
    assert t1 == t2
    d = Derivation(name, m1, m2, L)
    cur = m1
    if s1 != s2:
        # bring s2 out of the pair: the symmetry exchanges the single with the second Barenco control
        pi = perm_of(cur)
        if pi[2] != s2:
            cur2 = ren(HD, (pi[0], pi[2], pi[1], pi[3]))
            _bar_windows(d, cur, cur2, pi[3]); cur = cur2
        nm, cur3 = sym_at(cur)
        d.lemma(nm, 0); cur = norm(list(cur3))
    if cur != m2:
        _bar_windows(d, cur, m2, HC.hyb_roles(m2)[1])
    d.done(); return name

def _bar_windows(d, cur, want, sgl):
    """the runs of cur off the single control sgl (Barenco and its inverse): windows to want's."""
    n = len(cur); i = 0
    while i < n:
        j = i
        while j < n and sgl not in cur[j][1:]: j += 1
        if j > i and cur[i:j] != want[i:j]: d.win(i, j, want[i:j])
        i = j + 1

# ------------------------------------------------------------ hybrid against a separated K-free gadget
def hyb_pass_gad(mid, g, c):
    """the hybrid mid (black on every control) passes the gadget g white on c."""
    mid = norm(list(mid)); gl = g.letters()
    name = P.pname([tuple(mid)], [tuple(gl)])
    if name in L: return name
    t, s, pair = HC.hyb_roles(mid)
    d = Derivation(name, mid + gl, gl + mid, L)
    cur = mid; pre = None
    if c == s:
        pre, cur = sym_at(mid)
        d.lemma(pre, 0)
    lf, pieces = lf_at(cur, c)
    d.lemma(lf, 0)
    pos = len(L[lf][1])
    for q in reversed(pieces):
        pos -= len(q.word())
        d.lemma(H.piece_gadget_pass(q, g), pos)
    d.lemma(lf, len(gl), forward=False)
    if pre: d.lemma(pre, len(gl), forward=False)
    d.done(); return name

def _resolve(d, p, have, want):
    """at p: one-qubit letters have -> want (same operator), by sorting per
    wire (comm steps), one window per wire, and sorting into want's order."""
    cur = list(have)
    key = lambda g: g[1]
    tgt = sorted(cur, key=key)                      # stable
    for k in range(len(tgt)):
        j = next(i for i in range(k, len(cur)) if cur[i] is tgt[k])
        while j > k:
            d.comm(p + j - 1); cur[j - 1], cur[j] = cur[j], cur[j - 1]; j -= 1
    wsort = sorted(want, key=key)
    q = p
    for w in sorted(set(g[1] for g in have + want)):
        a = [g for g in cur if g[1] == w]; b = [g for g in wsort if g[1] == w]
        if a != b: d.win(q, q + len(a), b)
        q += len(b)
    cur = list(wsort)
    for k in range(len(want)):
        j = next(i for i in range(k, len(cur)) if cur[i] == want[k] and (i == k or True))
        j = cur.index(want[k], k)
        while j > k:
            d.comm(p + j - 1); cur[j - 1], cur[j] = cur[j], cur[j - 1]; j -= 1

def xconj_gad(b, g):
    """X_b g X_b -> g' (a gadget): (lemma, g')."""
    W = set(g.W); dd = list(g.d)
    for w in b:
        if w == g.t: dd = list(G.XW) + dd
        else: W ^= {w}
    g2 = Gad(g.t, sorted(W), dd, g.e)
    xs = [('X', w) for w in sorted(b)]
    name = f'xconj {sorted(b)} {g!r}'
    if name in L: return name, g2
    lhs = xs + g.letters() + xs
    d = Derivation(name, lhs, g2.letters(), L)
    core = G.core(g.t, g.e)
    npre = len(xs) + len(g.W) + len(g.d)
    pre2 = len(g2.W) + len(g2.d)
    _resolve(d, 0, lhs[:npre], g2.letters()[:pre2])
    m = len(xs) + len(g.W) + len(g.d)
    _resolve(d, pre2 + len(core), lhs[npre + len(core):], g2.letters()[pre2 + len(core):])
    d.done(); return name, g2

def ins_x(d, p, b):
    """at p insert X_b X_b, one wire at a time (sorted, then sorted)."""
    for j, w in enumerate(reversed(sorted(b))):
        d.win(p + j, p + j, [('X', w), ('X', w)])
    # now rev(xs) + xs; sort the first half
    xs = [('X', w) for w in sorted(b)]
    cur = list(reversed(xs))
    for k in range(len(xs)):
        j = cur.index(xs[k], k)
        while j > k:
            d.comm(p + j - 1); cur[j - 1], cur[j] = cur[j], cur[j - 1]; j -= 1

def hblock_pass_gad(bits, mid, g, c):
    """the hybrid block (bits, mid) passes the gadget g, separated on c."""
    b = [w for w in range(4) if bits[w]]
    mid = norm(list(mid))
    hl = norm(F.flatB((bits, tuple(mid)))); gl = g.letters()
    name = P.pname([tuple(hl)], [tuple(gl)])
    if name in L: return name
    if not b: return hyb_pass_gad(mid, g, c)
    xs = [('X', w) for w in sorted(b)]; k = len(xs)
    xn, g2 = xconj_gad(b, g)
    xn2, g3 = xconj_gad(b, g2)
    assert g3.letters() == gl, (g3, g)
    inner = hyb_pass_gad(mid, g2, c)
    d = Derivation(name, hl + gl, gl + hl, L)
    ins_x(d, len(hl) + len(gl), b)                  # X_b mid X_b g X_b X_b
    d.lemma(xn, k + len(mid))                       # X_b mid g' X_b
    d.lemma(inner, k)                               # X_b g' mid X_b
    ins_x(d, k + len(g2.letters()), b)              # X_b g' X_b X_b mid X_b
    d.lemma(xn2, 0)                                 # g X_b mid X_b
    d.done(); return name

if __name__ == "__main__" and "test" in sys.argv:
    # tests: the hybrid blocks of the shift's representative against white copies
    from t_shift2 import best
    A, B, Hc, Hc1 = best[2]
    gA = Gad(0, (), ['S', 'K'], -1)
    for W in [(3,), (2,), (2, 3)]:
        g = Gad(0, W, ['S', 'K'], -1)
        n = hblock_pass_gad(Hc[0], Hc[1], g, W[0] if W != (2, 3) else 3)
        print('ok', n[:70])

# ------------------------------------------------------------ the shift
from hybsym import pass_inv
from consec4 import copies, gl, merge_all, R as R0g

def pass_seq(name, Aw, units, fn):
    if name in L: return name
    fl = [x for u in units for x in u]
    d = Derivation(name, Aw + fl, fl + Aw, L)
    p = 0
    for u in units:
        d.lemma(fn(u), p); p += len(u)
    d.done(); return name

def merge_B(gB):
    """gB . copies(gB) -> a two-wire word, gB = Gad(1, (), d, e): the canonical merge relabelled."""
    g0 = Gad(0, (), gB.d, gB.e)
    out0 = norm([('X', 0), ('CX', 1, 0), ('CZ', 0, 1), ('X', 0)]) if list(gB.d) != list(R0g.d) else norm([('CX', 1, 0), ('CZ', 0, 1)])
    # find the merged two-wire word numerically among short candidates
    m = merge_all(g0, out0)
    return relabel(m, (1, 0, 2, 3), L)

def shift_fact(blocks):
    """A B Hc -> Hc1 A B at a representative with the targets on wires 0 and 1."""
    A, B, Hc, Hc1 = blocks
    kA, kB = F.sem(A), F.sem(B)
    Al, Bl = norm(F.flatB(F.cblock(kA))), norm(F.flatB(F.cblock(kB)))
    Hl, H1l = norm(F.flatB(Hc)), norm(F.flatB(Hc1))
    name = f'shift {F.kname(kA)} {F.kname(kB)} {show(Hl)[:30]}'
    if name in L: return name
    gA, gB = F.gad_of(kA), F.gad_of(kB)
    assert gA.t == 0 and gB.t == 1 and not gA.W and not gB.W
    rho, kap = copies(gA), copies(gB)
    X = gl(rho + kap); Xi = norm(inv(X))
    mA = merge_all(gA, norm([('CX', 1, 0), ('CZ', 0, 1)])) if gA.letters() == R0g.letters() else None
    assert mA
    mB = merge_B(gB)
    Fw = L[mA][1] + L[mB][1]
    # Pm: gA gB rho kap -> Fw
    pm = f'Pm {gA!r} {gB!r}'
    if pm not in L:
        bd = BD(pm, [gA.letters(), gB.letters()] + [g.letters() for g in rho + kap], Fw)
        gs = [gA, gB] + rho + kap
        for k in range(3):                              # rho_k left past gB
            i = 2 + k
            bd.swap(i - 1, C4.pass_lemma(gB, gs[i]))
            gs[i - 1], gs[i] = gs[i], gs[i - 1]
        bd.join(0, 4); bd.lem(0, 1, [L[mA][1]], mA)
        bd.join(1, 4); bd.lem(1, 1, [L[mB][1]], mB)
        bd.done()
    # Hc passes the copies, hence their inverse
    bits, mid = Hc
    def fn(u):
        g = (rho + kap)[[tuple(x.letters()) for x in rho + kap].index(u)]
        c = 3 if 3 in g.W else 2
        return hblock_pass_gad(bits, mid, g, c)
    hx = pass_seq(f'Hc passes copies {show(Hl)[:30]}', Hl, [tuple(g.letters()) for g in rho + kap], fn)
    hxi = pass_inv(hx, Hl, X)
    # conjF': Fw Hc -> Hc1 Fw
    Z = norm([('X', 1), ('CX', 1, 0), ('X', 1)]); Phi = [('SWAP', 0, 1), ('X', 0)]
    assert fp(norm(Phi + Z)) == fp(Fw), 'F = SWAP X0 Z'
    assert bits == (1, 0, 0, 0)
    t, s, pair = HC.hyb_roles(mid)
    pre = None; midz = norm(list(mid))
    if s == 1:
        pre, midz = sym_at(mid); midz = norm(list(midz))
    lf, pieces = lf_at(midz, 1)
    zh = f'Z passes {show(Hl)[:30]}'
    if zh not in L:
        e = Derivation(zh, Z + Hl, Hl + Z, L)
        e.win(0, 4, [('X', 0)] + Z)                     # Z X0 -> X0 Z
        if pre: e.lemma(pre, 1 + len(Z))
        e.lemma(lf, 1 + len(Z))
        pos = 1
        for q in pieces:                                # Z q -> q Z, left to right
            e.lemma(H.spell_pass(q, tuple(Z)), pos, forward=False)
            pos += len(q.word())
        e.lemma(lf, 1, forward=False)
        if pre: e.lemma(pre, 1, forward=False)
        p = 1 + len(mid)
        e.win(p, p + len(Z) + 1, [('X', 0)] + Z)
        e.done()
    cf = f'conjF {show(Hl)[:30]}'
    if cf not in L:
        e = Derivation(cf, Fw + Hl, H1l + Fw, L)
        e.win(0, len(Fw), Phi + Z)
        e.lemma(zh, 2)                                  # SWAP X0 Hc Z
        e.win(1, 3, [])                                 # X0 X0 -> eps : SWAP mid X0 Z
        p = 1 + len(mid)
        e.win(p, p, [('SWAP', 0, 1), ('SWAP', 0, 1)])
        e.swapconj(0, len(mid), 0)                      # mid' SWAP X0 Z
        mid2 = e.cur[:len(mid)]
        rs = respell_hyb(mid2, H1l)
        if rs: e.lemma(rs, 0)
        e.win(len(H1l), len(e.cur), Fw)
        e.done()
    d = Derivation(name, Al + Bl + Hl, H1l + Al + Bl, L)
    na, nb = F.b2g(kA), F.b2g(kB)
    if na: d.lemma(na, 0)
    if nb: d.lemma(nb, len(gA.letters()))
    p = len(gA.letters()) + len(gB.letters())
    P.insert_inverse(d, p, X)                           # gA gB X Xi Hc
    d.lemma(pm, 0)                                      # Fw Xi Hc
    d.lemma(hxi, len(Fw), forward=False)                # Fw Hc Xi
    d.lemma(cf, 0)                                      # Hc1 Fw Xi
    d.lemma(pm, len(H1l), forward=False)                # Hc1 gA gB X Xi
    P.cancel_inverse(d, len(H1l) + p, X)
    if nb: d.lemma(nb, len(H1l) + len(gA.letters()), forward=False)
    if na: d.lemma(na, len(H1l), forward=False)
    d.done(); return name

def rep01(c):
    import t_shiftcls as SC
    Gp = F.group(); best = None
    blocks = [F.decoded(c, 'l'), F.decoded(c + 1, 'l'), F.decoded(c, 'k'), F.decoded(c + 1, 'k')]
    for ops in Gp:
        bt = F.TF(ops, blocks)
        s = [SC.sem(b) for b in bt]
        if (s[0][2], s[1][2], s[2][2][0], s[3][2][0]) == (0, 1, 0, 1):
            key = tuple(s)
            if best is None or key < best[0]: best = (key, ops, bt)
    return best

if __name__ == '__main__' and 'shift' in sys.argv:
    done = {}
    for c in range(14):
        key, ops, bt = rep01(c)
        if key in done: print(c, 'same class as', done[key]); continue
        try:
            n = shift_fact(bt); done[key] = c
            print(c, 'shift derived:', n[:60], len(BY_NAME[n].steps), 'steps', key[2:])
        except Exception as ex:
            import traceback; traceback.print_exc(limit=4)
            print(c, 'FAIL', key, repr(ex)[:300])
