import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
from mc import *
import numpy as np
for N in [3,4,5]:
    a = mc_sem(N,'zx',[1],blackOn(2,N)); ai = mc_sem(N,'xz',[1],blackOn(2,N))
    Bx = mc_sem(N,'box',[0],blackOn(1,N)); Hg = mc_sem(N,'hg',[0,1],blackOn(2,N))
    PP = mat(N, ppAt(N,0,1))
    print(N, 'Hg=PP Bx PP', np.allclose(Hg, PP@Bx@PP),
      'a=(Bx Hg)^2', np.allclose(a, Bx@Hg@Bx@Hg), np.allclose(a, Hg@Bx@Hg@Bx),
      '360', np.allclose(PP@a@PP, ai))
