"""Is AGL(3,2) = <X i, CX i, SW i> on three wires presented by the
two-wire relations (completeness on two wires), the commutations of
gates on disjoint wires, the braid SW0 SW1 SW0 = SW1 SW0 SW1 and
CX-up SW0 SW1 CX0 SW1 SW0 = CX1?

    python3 -B afffree.py
"""
import sys
sys.path.insert(0, '..')
import classfree as F

AFF = F.AFF
A01 = ['X0', 'X1', 'CX0', 'SW0']
A12 = ['X1', 'X2', 'CX1', 'SW1']

def rels_for(extra):
    rels = [r for r in F.free_relators([A01, A12]) if all(F.NAMES[x] in AFF for x in r)]
    # disjoint commutations
    for a in ['X2']:
        for b in ['X0', 'X1', 'CX0', 'SW0']:
            if not (a == 'X2' and b == 'X1'):
                rels.append(F.w(f'{a} {b} {a} {b}'))
    for b in ['X1', 'X2', 'CX1', 'SW1']:
        if b != 'X1':
            rels.append(F.w(f'X0 {b} X0 {b}'))
    rels += [F.w(t) for t in extra]
    loc = {F.IX[n]: k for k, n in enumerate(AFF)}
    return [tuple(loc[x] for x in r) for r in rels]

if __name__ == '__main__':
    print('|AGL(3,2)| =', len(F.bfs(AFF)))
    braid = 'SW0 SW1 SW0 SW1 SW0 SW1'
    cxup = 'SW0 SW1 CX0 SW1 SW0 CX1'
    for extra in ([], [braid], [braid, cxup]):
        got = F.C.index(len(AFF), rels_for(extra), [], limit=2_000_000)
        print(len(extra), 'extra ->', got, flush=True)
