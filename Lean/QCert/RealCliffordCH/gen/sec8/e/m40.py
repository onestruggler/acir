import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
from mc import *
import numpy as np
def ctlOf(s,t): return lambda j: None if j==t else bool((s>>j)&1)
def D(*ms):
    M = np.eye(ms[0].shape[0])
    for m in ms: M = m @ M
    return M
for N in [3,4,5,6]:
    W = lambda j: False if 2<=j<N else None
    Hg = mc_sem(N,'hg',[1,0], W)
    Bw = mc_sem(N,'box',[2], ctlOf(2,2)); Bb = mc_sem(N,'box',[2], ctlOf(3,2))
    ci = lambda j: True if j==1 else (False if 3<=j<N else None)
    Bi = mc_sem(N,'box',[2], ci); Bi0 = mc_sem(N,'box',[0], ci)
    Z = mc_sem(N,'zx',[0], ctlOf(3,0))
    print(N, 'F1', np.allclose(Z, D(Hg,Bb,Hg,Bb)), 'F2', np.allclose(D(Bb,Bw), Bi),
      'F5', np.allclose(Bi@Hg, Hg@Bi), 'move', np.allclose(Bi, Bi0),
      'rule', np.allclose(D(Hg,Bw), D(Z,Bw,Hg)))
    # also check the actual decoding model if available
