"""Check the data of Alt16-RevCir numerically: what the Agda modules prove.

Run: python3 check.py
"""
from common import (N, ENC, GATES, K, BASE, compose, omega, word_perm,
                    circ_perm, from_cycles, cycles_of, corner, omega_circuit,
                    phi, inversions)


def main():
    print('states along the Gray code (wire 3 first):')
    print(' ', ' '.join(format(s, '04b') for s in ENC))
    print('the gates as permutations of the positions:')
    for name, p in GATES.items():
        print('  %-5s' % name, cycles_of(p))

    # the cycles
    assert circ_perm(K) == from_cycles([(9, 10, 11)])
    cyc = [omega_circuit(i) for i in range(N - 2)]
    print('the cycles:')
    for i, c in enumerate(cyc):
        assert circ_perm(c) == omega(i), i
        a, b, wires = corner(i)
        print('  Omega %-2d face %d%d, NOT on wires %s, %d gates' %
              (i, a, b, wires or '-', len(c)))

    # Lafont's relations between the cycles
    om = [circ_perm(c) for c in cyc]
    e = tuple(range(N))

    def prod(*ps):
        r = e
        for p in ps:
            r = compose(r, p)
        return r
    for i in range(14):
        assert prod(om[i], om[i], om[i]) == e
    for i in range(13):
        assert prod(om[i], om[i + 1], om[i]) == prod(om[i + 1], om[i + 1])
    for i in range(12):
        assert (prod(om[i], om[i + 2], om[i]) ==
                prod(om[i + 2], om[i], om[i + 1]))
    for i in range(14):
        for j in range(i + 3, 14):
            assert prod(om[j], om[i]) == prod(om[i], om[j])
    print('order, near, far, apart: 14 + 13 + 12 + 66 instances hold')

    # the gates as words in the cycles
    f = phi()
    for name, p in GATES.items():
        assert word_perm(f[name]) == p, name
        circ = [g for i in f[name] for g in cyc[i]]
        assert circ_perm(circ) == p, name
    print('the base gates as words in the cycles:')
    for name, w in BASE.items():
        print('  %-5s %2d letters, %2d inversions:' %
              (name, len(w), inversions(GATES[name])), w)

    # the swap's naturality, as Translation.agda uses it
    assert circ_perm(['Ex0', 'X0', 'Ex0']) == GATES['X1']
    assert circ_perm(['Ex0', 'Ex1', 'CX0', 'Ex1', 'Ex0']) == GATES['CX1']
    assert (circ_perm(['Ex0', 'Ex1', 'Ex2', 'CCX0', 'Ex2', 'Ex1', 'Ex0'])
            == GATES['CCX1'])

    # a cycle, read back through the gates' words
    for i in range(14):
        assert word_perm([j for g in cyc[i] for j in f[g]]) == omega(i)
    print('all checks pass')


if __name__ == '__main__':
    main()
