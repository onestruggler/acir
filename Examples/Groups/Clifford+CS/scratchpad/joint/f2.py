# (F2) on five wires: lambda1(g) lambda1(h) = lambda1(h) lambda1(g) for
# generators g, h of the four-wire domain on disjoint wires (the scalar
# disjoint from everything).
#
# Most items cross one image over the other (cross.py); where a K sits on
# a borrowed wire of an S-box the S-box's borrowed wires are exchanged
# first (F0), so that the K is on its dashed wire.  The one pair of
# disjoint CS gates goes through (AX), as in the paper:
#     Sigma01 = lambda0(CS01)^-1 CS01             (F5)
#     CS01 Sigma23 = Sigma23 CS01                  (AX: CS(u,A) of Sigma23)
#     lambda0(CS01)^-1 Sigma23 = Sigma23 lambda0(CS01)^-1     (F4)
import derivn, engine, cross, boxdash, f4, f0
from derivn import Derivation, show, unfold1, supp, inv
from engine import Stuck

X4 = ('X', 4)


def wires(g):
    if g[0] == 'I':
        return set()
    if g[0] in ('S', 'K'):
        return {g[1]}
    return {g[1], g[1] + 1}


def cancel_pair(d, k):
    """[g, g^-1] at k -> [], unfolding boxes down to four-wire windows."""
    g, h = d.cur[k], d.cur[k + 1]
    if len(supp([g, h])) <= derivn.N - 1:
        d.win(k, 2, [])
        return
    n = len(unfold1(g))
    d.unfold(k)
    d.unfold(k + n)
    for t in range(n):
        cancel_pair(d, k + n - 1 - t)


def inv_lemmas(L, g):
    """inv-<g>: [g, g^-1] -> [], invr-<g>: [g^-1, g] -> []."""
    gi = inv([g])[0]
    for name, w in ((f'inv-{show([g])}', [g, gi]), (f'invr-{show([g])}', [gi, g])):
        if name in L:
            continue
        d = Derivation(name, w, [], L)
        cancel_pair(d, 0)
        d.done()


def _sboxes(d):
    return [k for k, g in enumerate(d.cur) if g[0] == 'SBOX' and len(g[3]) == 2]


def item(L, g, h, sw):
    a, b = f4.lam1(g), f4.lam1(h)
    name = f'F2-{f4.gname(g)}-{f4.gname(h)}'
    d = Derivation(name, a + b, b + a, L)
    if sw:
        for k in _sboxes(d):
            f0.switch(d, k)
    a2, b2 = d.cur[:len(a)], d.cur[len(a):]
    if len(supp(a2 + b2)) <= derivn.N - 1:
        d.win(0, len(a2 + b2), b2 + a2)
    elif not any(derivn.is_box(x) for x in b2):
        i, m = cross.pass_left(d, len(a2), len(b2), 0)
        if m > len(b2):
            engine.simplify(d, i, m)
    elif not any(derivn.is_box(x) for x in a2):
        i, m = cross.pass_right(d, 0, len(a2), len(a2) + len(b2))
        if m > len(a2):
            engine.simplify(d, i, m)
    else:
        raise Stuck(('two S-boxes', name))
    if sw:
        for k in _sboxes(d):
            f0.switch(d, k, fwd=False)
    cross.close(d)
    d.done()


def ax_s23(L):
    """CS(0,1) passes Sigma23 = SBOX(0, 2, (4,3), 1): CS(u, A) by (AX)."""
    S23 = f4.SIGMA[2]
    cs = ('CS', 0, 1)
    d = Derivation('AX-S23', [cs, S23], [S23, cs], L)
    cross.deep_unfold(d, 1)
    nm, pi = boxdash.direct(cs, d.cur[1])
    d.lemma(nm, 0, pi=pi)
    d.lemma('AX', 1)
    cross.deep_fold(d, 0, S23)
    d.done()


def cs_pair(L):
    S01, S23 = f4.SIGMA[0], f4.SIGMA[2]
    S01d = inv([S01])[0]
    inv_lemmas(L, S01)
    ax_s23(L)
    d = Derivation('F2-CS0-CS2', [S01, S23], [S23, S01], L)
    d.win(0, 0, [X4, X4])
    d.lemma(f'invr-{show([S01])}', 1, fwd=False)   # X4 S01d S01 X4 S01 S23
    d.win(2, 0, [X4, X4])                          # X4 S01d X4 X4 S01 X4 S01 S23
    d.lemma('F5-01', 3)                            # X4 S01d X4 CS01 S23
    d.lemma('AX-S23', 3)                           # X4 S01d X4 S23 CS01
    d.win(4, 0, [X4, X4])
    d.lemma(f'inv-{show([S01])}', 5, fwd=False)
    d.win(6, 0, [X4, X4])                          # X4 S01d X4 S23 X4 S01 X4 X4 S01d X4 CS01
    d.lemma('F4-CS0-CS2', 3, fwd=False)            # X4 S01d X4 X4 S01 X4 S23 X4 S01d X4 CS01
    d.win(2, 2, [])
    d.lemma(f'invr-{show([S01])}', 1)
    d.win(0, 2, [])                                # S23 X4 S01d X4 CS01
    d.lemma('F5-01', 4, fwd=False)                 # S23 X4 S01d X4 X4 S01 X4 S01
    d.win(3, 2, [])
    d.lemma(f'invr-{show([S01])}', 2)
    d.win(1, 2, [])
    d.done()


def build(L, verbose=True):
    gens = f4.GENS
    ok, bad = [], []
    for p, g in enumerate(gens):
        for h in gens[p + 1:]:
            if wires(g) & wires(h):
                continue
            if g[0] == 'CS' and h[0] == 'CS':
                continue
            err = None
            for sw in (False, True):
                try:
                    item(L, g, h, sw); err = None; break
                except (Stuck, AssertionError) as e:
                    err = err or str(e)[:200]
            (bad if err else ok).append((g, h, err))
    cs_pair(L)
    if verbose:
        print(len(ok) + 1, 'F2 items derived,', len(bad), 'not')
        for g, h, e in bad:
            print('  ', f4.gname(g), f4.gname(h), e)
    return L


if __name__ == '__main__':
    import box, boxsym, boxbox, f5, f4cs
    derivn.QUIET = True
    L = box.build({})
    from w5lib import L as AXL
    L.update(AXL)
    f5.build(L); boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L)
    f0.build(L); f4cs.build(L, verbose=False)
    build(L)
