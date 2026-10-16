# (F1) for ck-tct, by the joint paper's route (Proposition three), with the
# transports of two-wire equations as the axioms TR2 (tr.py).
#
# A = X0 CK(0->1) X0, T = Toff(1; 2, 3), B = T CS01 T; the controlled rule
# is lambda1_4(A) lambda1_4(B) = lambda1_4(B) lambda1_4(A), and
#   ckt-A   lambda1_4(A) = lambda0_0(CK(4->1)).  With D = X0 CS01 X0, TR2
#           writes lambda1_4(A) as lambda1_4(A D) lambda1_4(D^-1); A D is
#           block diagonal in the wire 0 with det W = -1, so de-borrowing
#           makes lambda1_4(A D) a circuit on the wires 0, 1, 4, and
#           lambda1_4(D^-1) is X0 Sigma^3 X0 (F5, F4, and the S-box
#           symmetry).  On the other side lambda0_0(CK(4->1)) is
#           X0 lambda1_0(CK(4->1) CS(4,1)) Sigma'^3 X0 by TR2, and
#           de-borrowing for the control wire 0 makes the first factor a
#           circuit on 0, 1, 4 as well; the two three-wire circuits are
#           a window.
#   ckt-TT  lambda1_4(T) lambda1_4(T) = eps: lambda1 of the CCZ is one box
#           (f1big's L-CCZ-1), CK S4 CK = eps, and the box is an involution.
#   ckt-B   lambda1_4(B) = lambda1_0(T CS(4,1) T): (F5)/(F4) for T at the
#           control 4, ckt-TT, the S-box symmetry, and the same at 0.
#   and lambda0_0(.), lambda1_0(.) commute by (F4) for the control wire 0.
import derivn, f1, f1big, f1rules, lamcalc, tr
from derivn import Derivation, show, relabel_word
from lamcalc import ID, SWAP04, L0, L1, G
from tr import l1, l0, letters, gens_of, rel_gens

P = SWAP04
piA = {2: 0, 3: 1, 0: 2, 1: 3}                  # the canonical frame onto the wires 0, 1
pi0 = {2: 4, 3: 1, 4: 0, 0: 2, 1: 3}            # onto the wires 4, 1, the control 0
X0 = ('X', 0)
SSYM = {3: 2, 0: 0, 1: 4, 2: 1, 4: 3}           # S-sym-xt: Sigma(0,1;4) to Sigma(4,1;0)

Xg = gens_of(f1rules.X(0))
CK0 = gens_of(f1rules.CK(0))
CS0 = [('CS', 0)]
A = Xg + CK0 + Xg
D = Xg + CS0 + Xg
Dinv = Xg + CS0 * 3 + Xg
T = gens_of(f1rules.Toff(1))
B = T + CS0 + T

S4 = L1(('CS', 0), ID)[0]                         # Sigma(0, 1; 4)
S0 = L1(('CS', 0), P)[0]                          # Sigma(4, 1; 0)


def c(gs):
    return rel_gens(gs, piA)                      # piA is an involution


def build(L):
    # de-borrowing for the two pieces
    _, LamA = tr.deborrow(L, 'deb-AD', c(A + D))
    _, Lam0 = tr.deborrow(L, 'deb-CKS', c(CK0 + CS0))
    LamA, Lam0 = relabel_word(LamA, piA), relabel_word(Lam0, pi0)
    assert len(derivn.supp(LamA + [X0] + Lam0)) == 3

    # lambda1_4(D^-1) = X0 Sigma^3 X0
    d = Derivation('ckt-Dinv', [X0] + [S4] * 3 + [X0], l1(Dinv), L)
    d.win(0, 1, letters(Xg))
    n = len(letters(Xg))
    d.win(n + 3, 1, letters(Xg))
    m = lamcalc.split(d, 0, Xg, ID)                # L0 L1 S^3 G
    lamcalc.split(d, m + 3, Xg, ID)                # L0 L1 S^3 L0 L1
    lamcalc.bubble(d, 0, Xg, Xg + CS0 * 3, ID)    # L1 S^3 L0 L0 L1
    k = len(l1(Xg)) + 3
    d.win(k, 2 * len(l0(Xg)), [])
    d.done()

    # the right-hand side to the middle
    M = [X0] + Lam0 + [X0, X0] + [S0] * 3 + [X0]
    d = Derivation('ckt-A-R', l0(CK0, P), M, L)
    k = 0
    while k + 1 < len(d.cur):
        if d.cur[k] == X0 and d.cur[k + 1] == X0:
            d.win(k, 2, [])
        else:
            k += 1
    tr.tr2(d, 1, c(CK0), c(CK0 + CS0 + CS0 * 3), pi0)
    d.lemma('deb-CKS', 1, pi=pi0)
    d.win(1 + len(Lam0), 0, [X0, X0])
    d.done()

    # (P1)
    d = Derivation('ckt-A', l1(A), l0(CK0, P), L)
    tr.tr2(d, 0, c(A), c(A + D + Dinv), piA)
    d.lemma('deb-AD', 0, pi=piA)
    k = len(LamA)
    d.lemma('ckt-Dinv', k, fwd=False)
    for j in range(3):
        d.lemma('S-sym-xt', k + 1 + j, pi=SSYM)
        assert d.cur[k + 1 + j] == S0, show(d.cur[k + 1 + j:k + 2 + j])
    d.win(0, len(LamA), [X0] + Lam0 + [X0])
    d.lemma('ckt-A-R', 0, fwd=False)
    d.done()

    # T T = eps, controlled at 4
    ccz = f1big.piece_lemma(L, f1big.P('CCZ', 1))
    cczg = gens_of(f1rules.CCZ(1))
    assert L[ccz][0] == l1(cczg), 'L-CCZ-1 is not lambda1 of the CCZ'
    d = Derivation('ckt-TT', l1(T) + l1(T), [], L)
    d.lemma(ccz, 1)
    d.lemma(ccz, 5)
    assert [g[0] for g in d.cur] == ['CK', 'BOX', 'CK', 'S', 'CK', 'BOX', 'CK', 'S'], show(d.cur)
    d.win(2, 3, [])
    d.lemma('box2', 1, pi=f1.cross.box_pi(d.cur[1]))
    d.win(0, 3, [])
    d.done()

    # T Sigma T = lambda1(T) Sigma lambda1(T), at the control 4
    d = Derivation('ckt-TST', letters(T) + [S4] + letters(T), l1(T) + [S4] + l1(T), L)
    n = lamcalc.split(d, 0, T, ID)                 # L0(T) L1(T) S G(T)
    lamcalc.split(d, n + 1, T, ID)                 # L0(T) L1(T) S L0(T) L1(T)
    n0 = len(l0(T))
    lamcalc.bubble_back(d, n0, T, T + CS0, ID)     # L0(T) L0(T) L1(T) S L1(T)
    k, hi = 0, 2 * n0
    while k + 1 < hi:
        if d.cur[k] == ('X', 4) and d.cur[k + 1] == ('X', 4):
            d.win(k, 2, [])
            hi -= 2
        else:
            k += 1
    assert d.cur[0] == ('X', 4), show(d.cur[:3])
    d.lemma('ckt-TT', 1)
    d.win(0, 2, [])
    d.done()

    # (P2)
    d = Derivation('ckt-B', l1(B), l1(B, P), L)
    d.lemma('ckt-TST', 0, fwd=False)               # G(T) S G(T)
    k = len(letters(T))
    d.lemma('S-sym-xt', k, pi=SSYM)
    assert d.cur[k] == S0, show(d.cur[k:k + 1])
    d.lemma('ckt-TST', 0, pi=P)
    d.done()

    # (P3) and the rule
    lhs, rhs = l1(A) + l1(B), l1(B) + l1(A)
    for n_, l_, r_ in f1rules.items():
        if n_ == 'ck-tct@0':
            assert f1rules.lam1(l_) == lhs and f1rules.lam1(r_) == rhs, 'not the controlled rule'
    d = Derivation('F1-ck-tct@0', lhs, rhs, L)
    d.lemma('ckt-A', 0)
    d.lemma('ckt-B', len(l0(CK0, P)))
    lamcalc.bubble(d, 0, CK0, B, P)
    d.lemma('ckt-B', 0, fwd=False)
    d.lemma('ckt-A', len(l1(B)), fwd=False)
    d.done()
    return L


if __name__ == '__main__':
    import time
    import box, boxsym, boxdash, boxbox, f0, f4, f4cs, f5, boxtoff, boxck, ssym
    t0 = time.time()
    derivn.QUIET = True
    L = box.build({})
    f5.build(L); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
    f0.build(L); f4.build(L, verbose=False); f4cs.build(L, verbose=False)
    boxtoff.build(L); boxck.build(L); ssym.build(L)
    print(f'base {time.time() - t0:.0f}s', flush=True)
    derivn.QUIET = False
    build(L)
    print(f'ck-tct derived, {len(tr.TRS)} TR2 axioms, {time.time() - t0:.0f}s')
    for nm, u, v in tr.TRS:
        print(' ', nm, u, '=', v)
