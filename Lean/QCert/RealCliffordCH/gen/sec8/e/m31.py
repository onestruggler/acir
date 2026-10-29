import sys
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__file__), '..'))
from mc import *
import numpy as np
def gray(k): return k ^ (k >> 1)
def tOf(n,a):
    for j in range(n):
        if ((gray(a)>>j)&1) != ((gray(a+1)>>j)&1): return j
def ctlOf(s,t): return lambda j: None if j==t else bool((s>>j)&1)
def kind(n,a,which):
    t=tOf(n,a); b=(gray(a)>>t)&1
    return 'xz' if ((which==0)==(b==0)) else 'zx'
def R(n,a,which=0): return mc_sem(n,kind(n,a,which),[tOf(n,a)],ctlOf(gray(a),tOf(n,a)))
def B(n,k): return mc_sem(n,'box',[tOf(n,k)],ctlOf(gray(k),tOf(n,k)))
def prod(ms, N):
    M=np.eye(2**N)
    for m in ms: M = M @ m   # monoid order: product left to right
    return M
ok=True
for n in [3,4]:
    for a in range(2**n-1):
        r=R(n,a); ri=R(n,a,1); ba=B(n,a)
        assert np.allclose(r@r, ba) and np.allclose(ri@r, np.eye(2**n))
        if a+2 < 2**n:
            b1=B(n,a+1); ok &= np.allclose(b1@r@b1, ri)
        if a>=1:
            bm=B(n,a-1); ok &= np.allclose(bm@r@bm, ri)
        for c in range(2**n):
            if c in (a,a+1): continue
            def dZZ(x,y):
                lo,hi=min(x,y),max(x,y)
                return prod([B(n,k) for k in range(lo,hi)][::-1], n) if hi>lo else np.eye(2**n)
            # dZZ = drawn [B_lo, ..., B_{hi-1}] = B_{hi-1} * ... * B_lo
            lhs = dZZ(a+1,c) @ r; rhs = r @ dZZ(a,c)
            ok &= np.allclose(lhs, rhs)
print('rule31 ok', ok)
