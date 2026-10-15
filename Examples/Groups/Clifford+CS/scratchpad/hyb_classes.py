# The far facts of the hybrid letter at n = 4 under the transports: its
# commutation with the phase gadget, the rotation and another hybrid at a
# position two or more away, by class, and the role the separating wires
# play in the hybrid's spelling [Bar(V^2; pair -> t), CK(single -> t)].
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import facts4 as F

def kind_of(mid):
    return {4: 'PP', 8: 'R', 80: 'K'}[len(mid)]

def sem(b):
    bits, mid = b
    return (bits, kind_of(mid), F.tgt_of(mid) if kind_of(mid) != 'K' else hyb_roles(mid)[0])

def hyb_roles(mid):
    """(target, single, pair) of a hybrid middle word."""
    t = [g for g in mid if g[0] == 'CK' and len(g) == 3]
    # the CK letters of Barenco's word are CK(pair -> t); the single's is the one
    # whose control is not a control of a CX letter
    cx = {w for g in mid if g[0] == 'CX' for w in g[1:]}
    ks = [g for g in mid if g[0] in ('CK', 'CKd') and g[1] not in cx]
    single, tgt = ks[0][1], ks[0][2]
    pair = tuple(sorted(cx))
    return tgt, single, pair

def key(bs): return tuple(sem(b) for b in bs)

def instances():
    out = []
    for c in range(15):
        for j in range(15):
            if abs(j - c) < 2: continue
            out.append(('kp', c, j)); out.append(('kl', c, j))
            if j > c: out.append(('kk', c, j))
    return out

KIND2 = {'kp': 'p', 'kl': 'l', 'kk': 'k'}

def classify():
    G = F.group()
    classes = {}
    for (name, c, j) in instances():
        A, B = F.decoded(c, 'k'), F.decoded(j, KIND2[name])
        best = None
        for ops in G:
            At, Bt = F.TF(ops, [A, B])
            k = (name, key([At, Bt]))
            if name == 'kk':
                k2 = (name, key([Bt, At]))
                if k2 < k: k = k2
            if best is None or k < best[0]: best = (k, ops, At, Bt)
        classes.setdefault(best[0], []).append((c, j, best[2], best[3]))
    return classes

if __name__ == '__main__':
    cl = classify()
    from collections import Counter
    print('classes', len(cl), Counter(k[0] for k in cl))
    for k, insts in sorted(cl.items()):
        c, j, A, B = insts[0]
        tA, sA, pA = hyb_roles(A[1])
        bA, bB = A[0], B[0]
        tB = sem(B)[2]
        seps = [w for w in range(4) if w not in (tA, tB) and bA[w] != bB[w]]
        roles = ['single' if w == sA else 'pair' for w in seps]
        print(k[0], len(insts), 'hyb t', tA, 'single', sA, 'bits', bA, '| other', sem(B), '| seps', seps, roles)
