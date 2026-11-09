"""The base cases of block commutation for the controlled A8.

X_nu = Q G Q^-1 is the matching nu = Q mu0 Q^-1 controlled by wire 3, and
Gbar = X3 G X3 is mu0 controlled by wire 3 = 0; they commute.  Up to
conjugation by the centraliser of mu0 there are five union types of
(mu0, nu); one short three-wire circuit Q for each:

  [1,1,1,1]  Q = e                     (narrow on wires 0, 3)
  [2,2]      Q = CX0>1                 (narrow on wires 0, 1, 3)
  [2,1,1]    Q = CCX20>1               (searched: BC211)
  [3,1]      Q = CCX20>1 CCX10>2       (searched: BC31)
  [4]        Q = CX0>1 CCX10>2         (searched: BC4)

Run as `python bc_targets.py [pg_search options]`: adds the targets to
pg_search's table and runs its scheduler, the lemma library resumed from
pg_results.json.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import pg_search as P  # noqa: E402

GBAR = P.parse('X3 CX3>0 X3')
G = P.parse('CX3>0')

QS = {
    'BC11': P.parse(''),
    'BC22': P.parse('CX0>1'),
    'BC211': P.parse('CCX20>1'),
    'BC31': P.parse('CCX20>1 CCX10>2'),
    'BC4': P.parse('CX0>1 CCX10>2'),
}


def state_perm(word):
    return P.func(word)


def union_type(q):
    """The union type of mu0 and q mu0 q^-1 on the states with wire 3 = 1."""
    f = P.func(q + G + P.inv(q))
    nu = {x: f[8 | x] & 7 for x in range(8)}
    mu = {x: x ^ 1 for x in range(8)}
    seen, t = set(), []
    for s in range(8):
        if s in seen:
            continue
        x, L, use_mu = s, 0, True
        while True:
            seen.add(x)
            x = mu[x] if use_mu else nu[x]
            use_mu = not use_mu
            L += 1
            if x == s and use_mu:
                break
        t.append(L // 2)
    return tuple(sorted(t, reverse=True))


def targets():
    out = {}
    for nm, q in QS.items():
        xnu = q + G + P.inv(q)
        out[nm] = (GBAR + xnu, xnu + GBAR)
    return out


if __name__ == '__main__':
    for nm, q in QS.items():
        print(nm, union_type(q))
    T = targets()
    for nm, (l, r) in T.items():
        assert P.func(l) == P.func(r), nm
    P.TARGETS.update(T)
    argv = sys.argv[1:]
    if argv:
        P.main(argv)
