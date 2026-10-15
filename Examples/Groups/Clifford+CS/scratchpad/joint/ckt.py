# (F1) for ck-tct, by the paper's route (Proposition three): with
# A = X0 CK(0->1) X0, T = Toff(1; 2, 3), B = T CS01 T, the controlled rule
# is lambda1_4(A) lambda1_4(B) = lambda1_4(B) lambda1_4(A), and
#   (P1) ckt-A   lambda1_4(A) = lambda0_0(CK(4->1))      (normal forms)
#   (P2) ckt-B   lambda1_4(B) = lambda1_0(T CS(4,1) T)    (the plain T Sigma T:
#                (F5)/(F4) for T at the control 4 and at the control 0,
#                T T = eps transported, and the S-box symmetry)
#   (P3)         lambda0_0(.) and lambda1_0(.) commute by (F4) for the
#                control wire 0, generator by generator (lamcalc.bubble).
# The frame of the control 0 is the frame of the control 4 under the swap
# of the wires 0, 4 (lamcalc.SWAP04): in it CK(4->1) is the generator word
# of CK(0) and T CS(4,1) T that of B.
import derivn, cross, boxbox, f1, f1rules, lamcalc, ssym
from derivn import Derivation, show
from lamcalc import ID, SWAP04, L0, L1, G

P = SWAP04


def gens_of(letters):
    out = []
    for g in letters:
        if g[0] == 'iI':
            out.append(('I',))
        elif g[0] in ('S', 'K'):
            out.append(g)
        else:
            out.append(('CS', min(g[1:])))
    return out


A = gens_of(f1rules.X(0) + f1rules.CK(0) + f1rules.X(0))
T = gens_of(f1rules.Toff(1))
CK0 = gens_of(f1rules.CK(0))
B = T + [('CS', 0)] + T

def l0(gs, pi): return [x for g in gs for x in L0(g, pi)]
def l1(gs, pi): return [x for g in gs for x in L1(g, pi)]
def gw(gs, pi): return [x for g in gs for x in G(g, pi)]


def nf_lemma(L, name, lhs, rhs, idle):
    """lhs = rhs by normal forms (both sides to small letters and boxes)."""
    dr = Derivation(f'nf-{name}', rhs, rhs, L)
    dr.rhs = None
    pr = f1.nf(dr, idle, L)
    nfr = list(dr.cur)
    dr.rhs = derivn.norm(nfr)
    dr.done()
    d = Derivation(name, lhs, rhs, L)
    pl = f1.nf(d, idle, L)
    bl, br = d.cur[pl:], nfr[pr:]
    assert [g[1] for g in bl] == [g[1] for g in br], f'{name}: boxes {show(bl)} vs {show(br)}'
    for q in range(len(bl)):
        boxbox.reorder(d, pl + q, br[q][2:])
    sm = d.cur[:pl] + nfr[:pr]
    assert len(derivn.supp(sm)) <= derivn.N - 1, f'{name}: {show(d.cur[:pl])} vs {show(nfr[:pr])}'
    d.win(0, pl, nfr[:pr])
    d.lemma(f'nf-{name}', 0, fwd=False)
    d.done()


def build(L):
    boxbox.SPAWN = True; cross.USE_MEMO = True
    # (P1)
    nf_lemma(L, 'ckt-A', l1(A, ID), l0(CK0, P), None)
    # T T = eps, controlled at 4 (the domain wire 0 idle)
    nf_lemma(L, 'ckt-TT', l1(T, ID) + l1(T, ID), [], 0)
    # T Sigma T = lambda1(T) Sigma lambda1(T), at the control 4
    S4 = L1(('CS', 0), ID)
    d = Derivation('ckt-TST', gw(T, ID) + S4 + gw(T, ID), l1(T, ID) + S4 + l1(T, ID), L)
    n = lamcalc.split(d, 0, T, ID)                 # L0(T) L1(T) S G(T)
    lamcalc.split(d, n + 1, T, ID)                 # L0(T) L1(T) S L0(T) L1(T)
    n0, n1 = len(l0(T, ID)), len(l1(T, ID))
    # the second L0(T) left past S and L1(T)
    lamcalc.bubble_back(d, n0, T, T + [('CS', 0)], ID)
    # L0(T) L0(T) L1(T) S L1(T): the X4 pairs between the blocks cancel
    k = 0
    while k + 1 < 2 * n0:
        if d.cur[k] == ('X', 4) and d.cur[k + 1] == ('X', 4):
            d.win(k, 2, [])
        else:
            k += 1
    m = len(d.cur) - len(d.rhs)                     # what is left of the two L0(T)
    # X4 L1(T) L1(T) X4
    assert d.cur[0] == ('X', 4) and d.cur[m - 1] == ('X', 4), show(d.cur[:m])
    d.lemma('ckt-TT', 1)
    d.win(0, 2, [])
    d.done()
    # (P2)
    S0 = L1(('CS', 0), P)
    d = Derivation('ckt-B', l1(B, ID), l1(B, P), L)
    d.lemma('ckt-TST', 0, fwd=False)               # G(T) S G(T)
    k = len(gw(T, ID))
    d.lemma('S-sym-xt', k, pi={3: 2, 0: 0, 1: 4, 2: 1, 4: 3})
    assert d.cur[k] == S0[0], show(d.cur[k:k + 1])
    d.lemma('ckt-TST', 0, pi=P)
    d.done()
    # (P3) and the rule
    l, r = f1rules.CK(0), None
    lhs = l1(A, ID) + l1(B, ID)
    rhs = l1(B, ID) + l1(A, ID)
    d = Derivation('F1-ck-tct@0', lhs, rhs, L)
    d.lemma('ckt-A', 0)
    d.lemma('ckt-B', len(l0(CK0, P)))
    lamcalc.bubble(d, 0, CK0, B, P)
    d.lemma('ckt-B', 0, fwd=False)
    d.lemma('ckt-A', len(l1(B, ID)), fwd=False)
    d.done()
    return L


if __name__ == '__main__':
    import box, boxsym, boxdash, f0, f4, f4cs, f5, boxtoff, boxck
    derivn.QUIET = True
    L = box.build({})
    f5.build(L); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
    f0.build(L); f4.build(L, verbose=False); f4cs.build(L, verbose=False)
    boxtoff.build(L); boxck.build(L); ssym.build(L)
    # the rule's controlled sides are these words
    for n_, l_, r_ in f1rules.items():
        if n_ == 'ck-tct@0':
            assert f1rules.lam1(l_) == l1(A, ID) + l1(B, ID), 'lhs'
            assert f1rules.lam1(r_) == l1(B, ID) + l1(A, ID), 'rhs'
    build(L)
    print('ck-tct derived')
