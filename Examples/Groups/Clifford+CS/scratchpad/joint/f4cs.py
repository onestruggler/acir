# (F4) for two S-boxes: lambda0(CS_i) lambda1(CS_j) = lambda1(CS_j) lambda0(CS_i).
#
# Each letter of lambda1(CS_j) = Sigma_j commutes with lambda0(CS_i) as an
# operator (the box is diagonal, the Toffolis are controlled black by wire
# 4 where lambda0(CS_i) is the identity, the CS letters are diagonal).  So
# Sigma_j is unfolded and its letters move left one at a time: the box by
# box_left (box-box, Toffoli and X corrections, collected afterwards), the
# others by cross.pass_left.  An item that does not go through this way is
# the conjugate by X4 of the reversed item.
import derivn, engine, cross, boxbox, f4, f0
from derivn import Derivation, show, unfold1
from engine import Stuck

X4 = ('X', 4)


def direct(L, i, j, swi=False, swj=False):
    a, b = f4.lam0(('CS', i)), f4.lam1(('CS', j))
    name = f'F4-CS{i}-CS{j}'
    d = Derivation(name, a + b, b + a, L)
    if swi: f0.switch(d, 1)
    if swj: f0.switch(d, 3)
    Si, Sj = d.cur[1], d.cur[3]
    cross.deep_unfold(d, 3)
    k = boxbox.box_left(d, 3, 0)                 # the box of Sigma_j at 0
    hi = boxbox.collect(d, 1, len(d.cur) - 4)
    inner = derivn.norm(unfold1(Si))
    want = [X4] + [derivn.norm(unfold1(g))[0] if g[0] in ("SBOX", "SBOXd") else g for g in inner] + [X4]
    assert d.cur[1:hi] == want, f"{name}: lambda0 region {show(d.cur[1:hi])}"
    for q, g in enumerate(inner):
        if g[0] in ("SBOX", "SBOXd"):
            d.fold(2 + q, g)
    d.fold(2, Si)
    for t in range(4):
        p = len(d.cur) - 4 + t
        g = d.cur[p]
        i2, m = cross.pass_left(d, p, 1, 1 + t)
        if m > 1:
            m = engine.simplify(d, i2, m)
        assert d.cur[i2:i2 + m] == [g], f'{name}: {show([g])} came out as {show(d.cur[i2:i2 + m])}'
    cross.deep_fold(d, 0, Sj)
    if swj: f0.switch(d, 0, fwd=False)
    if swi: f0.switch(d, 2, fwd=False)
    d.done()


def by_symmetry(L, i, j):
    a, b = f4.lam0(('CS', i)), f4.lam1(('CS', j))
    d = Derivation(f'F4-CS{i}-CS{j}', a + b, b + a, L)
    d.win(4, 0, [X4, X4])                        # X4 Si X4 Sj X4 X4
    d.lemma(f'F4-CS{j}-CS{i}', 1, fwd=False)     # X4 X4 Sj X4 Si X4
    d.win(0, 2, [])
    d.done()


def build(L, verbose=True):
    bad = []
    for i in range(3):
        for j in range(3):
            s = cross._save(None) if False else None
            err = None
            for swi, swj in ((False, False), (True, False), (False, True), (True, True)):
                try:
                    direct(L, i, j, swi, swj); err = None; break
                except (Stuck, AssertionError) as e:
                    err = err or str(e)[:300]
            if err:
                bad.append((i, j, err))
    left = []
    for i, j, e in bad:
        if f'F4-CS{j}-CS{i}' in L:
            by_symmetry(L, i, j)
        else:
            left.append((i, j, e))
    if verbose:
        print(9 - len(left), 'S-box items derived,', len(left), 'not')
        for i, j, e in left:
            print('  ', i, j, e)
    return L


if __name__ == '__main__':
    import box, boxsym, boxdash
    derivn.QUIET = True
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L); boxdash.build(L); boxbox.build(L); f0.build(L)
    build(L)
