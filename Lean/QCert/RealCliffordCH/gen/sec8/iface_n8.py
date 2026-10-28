"""Numerical check of the statements (269), (290)-(292), (295), (300)-(302) of
Sec8/D/N8.lean (and (293), (294), used on the way), as transcribed in Lean, at
widths 3-6: `python iface_n8.py`."""
import sys
sys.path.insert(0, '.')
from mc import *
def setCtl(c, w, v): return lambda j: v if j == w else c(j)
def U(*cs):
    def f(j):
        for c in cs:
            if c(j) is not None: return c(j)
        return None
    return f
def D(N, *gs): return drawn(*gs)
B = lambda N: mc(N, 'box', [0], blackOn(1, N))
def ctls(d): return ctlDict(d)
E = {}
def e269(N):
    W = mc(N,'zx',[0],U(ctlAt(1,True),ctlAt(2,True))); V = mc(N,'xz',[0],U(ctlAt(1,True),ctlAt(2,True)))
    Bp = mc(N,'box',[1],U(ctlAt(0,True),blackOn(3,N)))
    return B(N), D(N, W, Bp, V, Bp)
E['269']=(3,e269)
def e290(N):
    b = mc(N,'box',[0],U(ctlAt(1,True),blackOn(4,N))); z = mc(N,'zx',[0],blackOn(1,4))
    return D(N,b,z), D(N,z,b)
E['290']=(4,e290)
def e291(N):
    b = mc(N,'box',[0],U(ctlAt(1,True),blackOn(3,N))); z = mc(N,'zx',[0],blackOn(1,4))
    return D(N,b,z), D(N,z,b)
E['291']=(4,e291)
def e292(N):
    z = mc(N,'zx',[0],blackOn(1,3)); b = mc(N,'box',[1],U(ctlAt(0,True),ctlAt(2,False),blackOn(3,N)))
    return D(N,z,b), D(N,b,z)
E['292']=(3,e292)
def e293(N):
    z = mc(N,'zx',[1],U(ctlAt(0,True),ctlAt(2,False),ctlAt(3,True)))
    return D(N,z,B(N)), D(N,B(N),z)
E['293']=(4,e293)
def e294(N):
    a = mc(N,'zx',[0],blackOn(1,3)); a2 = mc(N,'xz',[0],blackOn(1,3))
    c = mc(N,'zx',[1],U(ctlAt(0,True),ctlAt(3,True))); c2 = mc(N,'xz',[1],U(ctlAt(0,True),ctlAt(3,True)))
    b = mc(N,'box',[0],U(ctlAt(1,True),blackOn(4,N)))
    return B(N), D(N,a,c,b,c2,a2,c,b,c2)
E['294']=(4,e294)
def e295(N):
    a = mc(N,'zx',[0],blackOn(1,4)); a2 = mc(N,'xz',[0],blackOn(1,4))
    c = mc(N,'zx',[1],U(ctlAt(0,True),blackOn(2,4))); c2 = mc(N,'xz',[1],U(ctlAt(0,True),blackOn(2,4)))
    b = mc(N,'box',[0],U(ctlAt(1,True),blackOn(4,N)))
    return B(N), D(N,a,c,b,c2,a2,c,b,c2)
E['295']=(4,e295)
def e300(N):
    W = mc(N,'zx',[0],blackOn(1,3)); V = mc(N,'xz',[0],blackOn(1,3))
    Bp = mc(N,'box',[1],U(ctlAt(0,True),blackOn(3,N)))
    return B(N), D(N, Bp, W, Bp, V)
E['300']=(3,e300)
def e301(N):
    return D(N,B(N),mc(N,'box',[0],setCtl(blackOn(1,N),2,False))), mc(N,'box',[0],setCtl(blackOn(1,N),2,None))
E['301']=(3,e301)
def e302(N):
    return D(N,mc(N,'box',[0],setCtl(blackOn(1,N),2,False)),B(N)), mc(N,'box',[0],setCtl(blackOn(1,N),2,None))
E['302']=(3,e302)
if __name__=='__main__':
    for k,(lo,f) in E.items():
        res=[]
        for N in range(lo,7):
            l,r=f(N); res.append((N, bool(np.allclose(mat(N,l),mat(N,r)))))
        print(k,res)
