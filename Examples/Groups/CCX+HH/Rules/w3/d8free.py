"""W(D8) = <Aff, CCX0, Z1> over S8: which relations are needed beyond
the free ones (affine, two-wire with Z1 = HH0 X1 HH0 on the wires 0, 1)
and the classical rules?

    python3 -B d8free.py
"""
import sys
sys.path.insert(0, '..')
import classfree as F

F.E['Z1'] = tuple(F.L[t] for t in 'HH0 X1 HH0'.split())
F.NAMES.append('Z1')
F.IX['Z1'] = len(F.NAMES) - 1
F.PERM['Z1'] = F.rep.evaluate(F.E['Z1'])

W = F.AFF + ['CCX0', 'Z1']
P01Z = ['X0', 'X1', 'CX0', 'SW0', 'Z1']
S8 = F.AFF + ['CCX0']

EXTRA = {
    'Z1-X2': 'Z1 X2 Z1 X2',
    'Z1-CCX': 'Z1 CCX0 Z1 CCX0',
    'Z1-Z2': 'Z1 SW1 Z1 SW1 Z1 SW1 Z1 SW1',
    'Z1-CX1': 'CX1 Z1 CX1 SW1 Z1 SW1 Z1',
}

def run(extra):
    rels = [r for r in F.free_relators([F.AFF, P01Z, F.P12]) if all(F.NAMES[x] in W for x in r)]
    rels += [F.rel(n) for n in ['CCX-sym', 'CCX-neg', 'CCX-XC']]
    rels += [F.w(EXTRA[e]) for e in extra]
    loc = {F.IX[n]: k for k, n in enumerate(W)}
    rels = [tuple(loc[x] for x in r) for r in rels]
    sub = [(loc[F.IX[n]],) for n in S8]
    got = F.C.index(len(W), rels, sub, limit=2_000_000)
    print(extra, '->', got, flush=True)

if __name__ == '__main__':
    pass
    for n, t in EXTRA.items():
        assert F.rep.is_identity(tuple(x for tok in t.split() for x in F.E[tok])), n
    run([])
    run(['Z1-X2'])
    run(['Z1-X2', 'Z1-CCX'])
    run(['Z1-X2', 'Z1-CCX', 'Z1-Z2'])
    run(['Z1-X2', 'Z1-CCX', 'Z1-Z2', 'Z1-CX1'])
