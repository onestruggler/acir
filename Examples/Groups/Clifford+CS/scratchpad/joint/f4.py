# (F4) on five wires: lambda0(g) and lambda1(h) commute, for all generators
# g, h of a four-wire domain (control wire 4), lambda1 the controlled
# functor of Lambda.agda: the scalar to S4, S_v to CS(v,4), K_v to
# CK(4 -> v), the CS of the pairs 01, 12, 23 to the S-boxes; lambda0 is
# X4 lambda1 X4.
import sys
import derivn, engine, box, boxsym, boxdash, cross
from derivn import Derivation, show, norm1
from engine import Stuck

X4 = ('X', 4)
GENS = [('I',)] + [('S', v) for v in range(4)] + [('K', v) for v in range(4)] + [('CS', v) for v in range(3)]
SIGMA = {0: ('SBOX', 2, 0, (4, 1), 3), 1: ('SBOX', 0, 1, (4, 2), 3), 2: ('SBOX', 0, 2, (4, 3), 1)}


def lam1(g):
    if g[0] == 'I': return [('S', 4)]
    if g[0] == 'S': return [norm1(('CS', g[1], 4))]
    if g[0] == 'K': return [('CK', 4, g[1])]
    return [SIGMA[g[1]]]


def lam0(g): return [X4] + lam1(g) + [X4]


def gname(g): return g[0] + (str(g[1]) if len(g) > 1 else '')


def f4(L, g, h):
    a, b = lam0(g), lam1(h)
    name = f'F4-{gname(g)}-{gname(h)}'
    d = Derivation(name, a + b, b + a, L)
    if len(derivn.supp(a + b)) <= derivn.N - 1:
        d.win(0, len(a + b), b + a)
    elif not any(derivn.is_box(x) for x in b):
        # lambda1(h) moves left across lambda0(g)
        i, m = cross.pass_left(d, len(a), len(b), 0)
        engine.simplify(d, 0, m)
        if d.cur[:len(b)] != b:
            engine.simplify(d, 0, len(d.cur))
    else:
        # lambda0(g) moves right across lambda1(h)
        i, m = cross.pass_right(d, 0, len(a), len(a) + len(b))
        engine.simplify(d, i, m)
    cross.close(d)
    d.done()
    return name


def build(L, verbose=True):
    ok, bad = [], []
    for g in GENS:
        for h in GENS:
            if g[0] == "CS" and h[0] == "CS":
                continue                  # f4cs.py
            try:
                f4(L, g, h); ok.append((g, h))
            except (Stuck, AssertionError) as e:
                bad.append((g, h, str(e)[:160]))
    if verbose:
        print(len(ok), "F4 items derived (the S-box pairs in f4cs.py),", len(bad), "not")
        for g, h, e in bad[:40]:
            print('  ', gname(g), gname(h), e)
    return L


if __name__ == '__main__':
    import os
    os.environ['DERIV_QUIET'] = '1'
    derivn.QUIET = True
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L); boxdash.build(L)
    build(L)
