import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
os.environ.setdefault('DERIV_QUIET', '1')
import hyb_classes as HC
cl = HC.classify()
for k, insts in sorted(cl.items()):
    if k[0] != 'kk': continue
    c, j, A, B = insts[0]
    tA, sA, pA = HC.hyb_roles(A[1]); tB, sB, pB = HC.hyb_roles(B[1])
    seps = [w for w in range(4) if w not in (tA, tB) and A[0][w] != B[0][w]]
    print(len(insts), 'A t', tA, 's', sA, 'p', pA, 'bits', A[0], '| B t', tB, 's', sB, 'p', pB, 'bits', B[0],
          '| seps', [(w, 'P' if w in pA else 'S', 'P' if w in pB else 'S') for w in seps])
