# Transport classes of the hybrid's shift facts l_c l_{c+1} k_c = k_{c+1} l_c l_{c+1}
# and of the top-pair facts (k_14 against the far letters, the scalar).
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import facts4 as F
import hyb_classes as HC

def sem(b):
    bits, mid = b
    if len(mid) == 80: return (bits, 'K', HC.hyb_roles(mid))
    return F.sem(b)

def classify(insts):
    G = F.group(); cl = {}
    for (name, blocks) in insts:
        best = None
        for ops in G:
            bt = F.TF(ops, blocks)
            k = tuple(sem(b) for b in bt)
            if best is None or k < best[0]: best = (k, ops, bt)
        cl.setdefault(best[0], []).append((name, best[1], best[2]))
    return cl

if __name__ == '__main__':
    insts = []
    for c in range(14):
        insts.append((f'sh{c}', [F.decoded(c, 'l'), F.decoded(c + 1, 'l'), F.decoded(c, 'k'), F.decoded(c + 1, 'k')]))
    cl = classify(insts)
    print('shift classes', len(cl))
    for k, v in cl.items():
        print(len(v), [x[0] for x in v])
        for b in k: print('   ', b)
