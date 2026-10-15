# The doubly controlled S is symmetric in its three wires:
#
#   S-sym-xt   Sigma(x; t, y | u, A) = Sigma(t; x, y | u, A)
#   S-sym-ty   Sigma(x; t, y | u, A) = Sigma(x; y, t | u, A)
#
# Both S-boxes are the same box (up to the order of its controls) times a
# four-wire diagonal word on x, t, y, A with the phase i^(xty) (-1)^(xtyA),
# so one window and a reordering of the box.  Canonical: x, t, y, u, A =
# 0, 1, 2, 3, 4.
import derivn, cross, boxbox
from derivn import Derivation, show

S0 = ('SBOX', 3, 0, (1, 2), 4)


def build(L):
    for name, S1 in (('S-sym-xt', ('SBOX', 3, 1, (0, 2), 4)), ('S-sym-ty', ('SBOX', 3, 0, (2, 1), 4))):
        d = Derivation(name, [S0], [S1], L)
        n = cross.deep_unfold(d, 0)
        want = derivn.norm(derivn.unfold1(S1))
        bx = [g for g in want if g[0] == 'BOX'][0]
        boxbox.reorder(d, 0, bx[2:])
        inner = [g if g[0] not in ('SBOX', 'SBOXd') else derivn.norm(derivn.unfold1(g))[0] for g in want]
        d.win(1, n - 1, inner[1:])
        cross.deep_fold(d, 0, S1)
        d.done()
    return L


if __name__ == '__main__':
    import box, boxsym
    L = box.build({})
    boxsym.build(L); boxsym.build_perms(L)
    build(L)
    print(len(L), 'lemmas')
