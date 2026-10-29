import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
from mc import *
import numpy as np
def D(*ms):  # drawn order: first applied first
    M = np.eye(ms[0].shape[0])
    for m in ms: M = m @ M
    return M
for N in [2,3,4,5]:
    a = mc_sem(N,'xz',[0],blackOn(1,N))
    b = mc_sem(N,'zx',[1],ctlOr(ctlAt(0,True),blackOn(2,N)))
    print(N, 'braid', np.allclose(D(a,b,a), D(b,a,b)))
    SW = mat(N, swAt(N,0)); CZ = mat(N, czAt(N,0,1))
    G = D(SW, CZ)   # first swap then CZ
    print('  G a = b G', np.allclose(G@a, b@G))
    a2 = mc_sem(N,'xz',[0],ctlAt(1,True)); b2 = mc_sem(N,'zx',[1],ctlAt(0,True))
    print('  a2b2a2 == G', np.allclose(D(a2,b2,a2), G), np.allclose(D(a2,b2,a2), D(CZ,SW)))
    print(np.round(D(a2,b2,a2)[:4,:4],3) if N==2 else '')
