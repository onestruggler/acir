# (F1) by de-borrowing (the joint paper's Proposition three): the items
# whose controlled K sits on the target of an S-box, which resist the box
# normal forms, at the placements where the transports TR2 they need do
# not rest on them (TR2 rests on the items at the offsets 2-4).
#
# A piece Q = c K c^j (c a CS gate, K on one of its wires x, j = 1 or 3)
# is block diagonal in the other wire y of c, with det W = -1 or 1, so
# de-borrowing (tr.deborrow) turns lambda1(Q) into a circuit on three
# wires.  Then
#   CS-K0@o, CS-K1@o (o = 0, 1)   Q K S = S K Q: both sides on the wires
#                                  of c and 4 after de-borrowing, a window;
#   rel-269@o (o = 0, 1)           Q_hi K Q_lo = Q_lo K Q_hi (j = 1), both
#                                  sides on o .. o+2 and 4, a window;
#   rel-272@o (o = 0, 1)           the same with j = 3, after inserting c^4
#                                  (TR2), up to the controlled comm-CSu-CS.
import derivn, f1, f1rules, tr
from derivn import Derivation, show, relabel_word
from tr import l1

SIGMA = f1rules.SIGMA


def pi_for(v):
    """the renaming of the canonical frame (CS on 2, 3) onto the CS on
    v, v + 1, matching the borrowed wires of its S-box."""
    if v == 2:
        return {}
    s = SIGMA[v]
    pi = {2: v, 3: v + 1, 0: s[1], 1: s[4], 4: 4}
    assert sorted(pi.values()) == list(range(5)), pi
    assert relabel_word([SIGMA[2]], pi) == [s], (relabel_word([SIGMA[2]], pi), s)
    return {a: b for a, b in pi.items() if a != b}


CS2 = [('CS', 2)]
# name: (word, block wire y, target x), canonical frame
PIECES = {
    'deb-Q-lo': (CS2 + [('K', 3)] + CS2 * 3, 2, 3),
    'deb-Q-hi': (CS2 + [('K', 2)] + CS2 * 3, 3, 2),
    'deb-P-lo': (CS2 + [('K', 3)] + CS2, 2, 3),
    'deb-P-hi': (CS2 + [('K', 2)] + CS2, 3, 2),
}


def piece(L, name, v):
    """the piece's de-borrowing lemma, and Lambda, on the CS at v, v + 1."""
    w, y, x = PIECES[name]
    tr.deborrow(L, name, w, y=y, x=x)
    return relabel_word(L[name][1], pi_for(v))


def deb(d, name, v, k):
    d.lemma(name, k, pi=pi_for(v) or None)


def rule(name):
    for n_, l_, r_ in f1rules.items():
        if n_ == name:
            return f1rules.lam1(l_), f1rules.lam1(r_)
    raise KeyError(name)


def cs_k(L, j, o):
    """CS-K<j>@o: K on the wire o + j."""
    nm = f'CS-K{j}@{o}'
    l, r = rule(nm)
    c, K, S = [('CS', o)], [('K', o + j)], [('S', o + j)]
    assert l == l1(c + K + c + K + S) and r == l1(S + K + c + K + c), nm
    pn = 'deb-P-hi' if j == 0 else 'deb-P-lo'
    lam = piece(L, pn, o)
    d = Derivation(f'F1-{nm}', l, r, L)
    deb(d, pn, o, 0)                                 # Lambda l1(K S)
    d.win(0, len(d.cur), l1(S + K) + lam)            # three wires
    d.lemma(pn, len(l1(S + K)), fwd=False, pi=pi_for(o) or None)
    d.done()


def two_pieces(L, nm, j, o):
    """rel-269@o (j = 1) or rel-272@o (j = 3)."""
    l, r = rule(nm)
    lo, hi, K = [('CS', o)], [('CS', o + 1)], [('K', o + 1)]
    pl, ph = ('deb-P-lo', 'deb-P-hi') if j == 1 else ('deb-Q-lo', 'deb-Q-hi')
    lam = {'lo': piece(L, pl, o), 'hi': piece(L, ph, o + 1)}
    pn = {'lo': (pl, o), 'hi': (ph, o + 1)}
    cs = {'lo': lo, 'hi': hi}

    def side(d, first, second):
        if j == 3:
            # first K first^3 K second K first: insert second^4 after the second K
            n = len(l1(cs[first] + K + cs[first] * 3 + K + cs[second] + K))
            tr.tr2(d, n, [], CS2 * 4, pi_for(pn[second][1]))
        deb(d, pn[first][0], pn[first][1], 0)
        p = len(lam[first]) + 1
        deb(d, pn[second][0], pn[second][1], p)
        return p + len(lam[second])

    if j == 1:
        assert l == l1(hi + K + hi + K + lo + K + lo) and r == l1(lo + K + lo + K + hi + K + hi), nm
    else:
        assert l == l1(hi + K + hi * 3 + K + lo + K + hi) and r == l1(lo + K + lo * 3 + K + hi + K + lo), nm
        comm = f'F1-comm-CSu-CS@{o}'
        if comm not in L:
            f1.build(L, verbose=False, only=[f'comm-CSu-CS@{o}'])
        assert L[comm] == (derivn.norm(l1(hi + lo)), derivn.norm(l1(lo + hi))), comm
    dr = Derivation(f'deb-{nm}-R', r, r, L)
    dr.rhs = None
    m = side(dr, 'lo', 'hi')
    mid = list(dr.cur)
    dr.rhs = derivn.norm(mid)
    dr.done()
    d = Derivation(f'F1-{nm}', l, r, L)
    k = side(d, 'hi', 'lo')
    if j == 3:
        d.lemma(comm, k, fwd=False)                  # l1(lo hi) -> l1(hi lo)
    d.win(0, k, mid[:m])
    assert d.cur == mid, show(d.cur)
    d.lemma(f'deb-{nm}-R', 0, fwd=False)
    d.done()


ITEMS = ['CS-K0@0', 'CS-K0@1', 'CS-K1@0', 'CS-K1@1', 'rel-269@0', 'rel-269@1', 'rel-272@0', 'rel-272@1']


def build(L, only=None):
    for nm in ITEMS:
        if only and nm not in only:
            continue
        if nm.startswith('CS-K'):
            cs_k(L, int(nm[4]), int(nm[-1]))
        else:
            two_pieces(L, nm, 1 if nm.startswith('rel-269') else 3, int(nm[-1]))
    return L


if __name__ == '__main__':
    import time
    import box, boxsym, boxdash, boxbox, f0, f4, f4cs, f5, boxtoff, boxck
    t0 = time.time()
    derivn.QUIET = True
    L = box.build({})
    f5.build(L); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
    f0.build(L); f4.build(L, verbose=False); f4cs.build(L, verbose=False)
    boxtoff.build(L); boxck.build(L)
    print(f'base {time.time() - t0:.0f}s', flush=True)
    derivn.QUIET = False
    build(L)
    print(f'de-borrowed items derived, {len(tr.TRS)} TR2 axioms, {time.time() - t0:.0f}s')
