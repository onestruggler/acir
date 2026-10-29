import sys
sys.path.insert(0, r'D:\work2\acir\Lean\QCert\RealCliffordCH\gen\sec8\w4')
sys.path.insert(0, r'D:\work2\acir\Lean\QCert\RealCliffordCH\gen\sec8')
import tok
from tok import G, P, S
N=4
def g(K,tg,cs): return ('g',K,tuple(tg),tuple(cs))   # keep given order (Lean lists)
bx0=g('box',[0],[(3,True),(2,True),(1,True)])
wW=g('zx',[0],[(2,True),(1,True)]); wV=g('xz',[0],[(2,True),(1,True)])
cC=g('box',[1],[(3,True),(0,True)])
Abz=g('zx',[1],[(3,True),(2,False),(0,True)]); Abx=g('xz',[1],[(3,True),(2,False),(0,True)])
A2z=g('zx',[1],[(3,True),(2,True),(0,True)]); A2x=g('xz',[1],[(3,True),(2,True),(0,True)])
A1z=g('zx',[1],[(3,True),(0,True)]); A1x=g('xz',[1],[(3,True),(0,True)])
D4=g('box',[0],[(1,True)])
Z123=g('zx',[0],[(3,True),(2,True),(1,True)]); X123=g('xz',[0],[(3,True),(2,True),(1,True)])
Zw=g('zx',[0],[(3,False),(2,True),(1,True)]); Xw=g('xz',[0],[(3,False),(2,True),(1,True)])
B31=g('box',[0],[(3,True),(1,True)])
def chk(name,a,b):
    ok=tok.weq(N,a,b); print(name, ok); assert ok
# table entries numerically
E269=([bx0],[wW,cC,wV,cC]); chk('269',*E269)
E291c=([cC,A2z],[A2z,cC]); chk('291c',*E291c)
E208f0r=([A2z,A2x],[]); chk('208f0r',*E208f0r)
E208r=([A2x,A2z],[]); chk('208r',*E208r)
E216=([Abz,wW],[wW,Abz]); chk('216',*E216)
E217=([Abz,wV],[wV,Abz]); chk('217',*E217)
E218=([Abx,wW],[wW,Abx]); chk('218',*E218)
E209=([Abx,Abz],[]); chk('209',*E209)
E221=([Abz,A2z],[A1z]); chk('221',*E221)
E222=([A2x,Abx],[A1x]); chk('222',*E222)
E223=([Z123,Zw],[wW]); chk('223',*E223)
E224=([Xw,X123],[wV]); chk('224',*E224)
E225=([Abx,A1z],[A2z]); chk('225',*E225)
E226=([A1x,Abz],[A2x]); chk('226',*E226)
E290=([D4,Z123],[Z123,D4]); chk('290',*E290)
E240a=([A2z,Zw],[Zw,A2z]); chk('240a',*E240a)
E240b=([A2x,Zw],[Zw,A2x]); chk('240b',*E240b)
E208f0f3=([Zw,Xw],[]); chk('208f0f3',*E208f0f3)
x3=('p',1,(('H',0),('Z',0),('H',0)),(3,))
EX=([x3,Z123,x3],[Zw]); chk('x81',*EX)

def run(name,T,w,v,ss):
    e=tok.Engine(3,T)
    r,bad=e.run(w,ss)
    print(name, 'OK' if r==v else ('FAIL',bad,r))
    assert r==v
# L4: [cC, A2x] = [A2x, cC]
run('L4',[E291c,E208f0r,E208r],[cC,A2x],[A2x,cC],
    [('rw',0,2,True),('rw',1,0,True),('rw',2,1,False)])
E291cx=([cC,A2x],[A2x,cC])
# L5: [Abz,cC]=[cC,Abz]
run('L5',[E226,E291cx],[Abz,cC],[cC,Abz],
    [('sem',0,0,[A1z,A1x],2),('rw',1,0,False),('rw',1,1,True),('sem',0,2,[cC,A1z],2),('rw',2,0,True),('sem',1,2,[],2)])
EAbC=([Abz,cC],[cC,Abz])
# L6: 293
run('L6',[E269,E216,EAbC,E217],[Abz,bx0],[bx0,Abz],
    [('rw',1,0,False),('rw',0,1,False),('rw',1,2,False),('rw',2,3,False),('rw',3,2,False),('rw',0,0,True)])
E293=([Abz,bx0],[bx0,Abz])
F295=[wW,A2z,D4,A2x,wV,A2z,D4,A2x]
run('L7',[E209,E293,E269,E218,E225,E226,E221,E222,E217],[bx0],F295,
    [('rw',0,0,True),     # insert Abx Abz
     ('rw',1,1,False),    # Abz bx0 -> bx0 Abz
     ('rw',1,2,False),    # bx0 -> W C V C
     ('sem',2,1,[A1z,D4,A1x,D4],2),
     ('sem',7,1,[A1z,D4,A1x,D4],2),
     ('sem',5,2,[wV,D4],3),
     ('sem',6,5,[A1z,D4,A1x],2),
     ('rw',0,3,False),    # 218
     ('rw',1,4,False),    # 225
     ('rw',7,5,False),    # 226
     ('rw',3,7,True),     # A1x -> A2x Abx
     ('rw',6,6,True),     # A1z -> Abz A2z   (positions shift)
     ('rw',5,8,True),('rw',4,0,False)])
E295a=([bx0],F295)
F295i=[Z123,A2z,D4,A2x,X123,A2z,D4,A2x]
# L9 [D4,Zw]=[Zw,D4]
run('L9',[E290,EX],[D4,Zw],[Zw,D4],
   [('rw',1,1,True),('sem',0,2,[x3,D4],2),('rw',1,0,False),('sem',2,2,[x3,D4],2),('rw',0,1,False)])
E290w=([D4,Zw],[Zw,D4])
run('L12',[E295a,E223,E240a,E290w,E240b,E224,E208f0f3],[bx0],F295i,
   [('rw',0,0,False),('rw',0,1,True),('rw',1,2,True),('rw',2,3,True),('rw',3,4,True),('rw',5,5,True),('rw',4,6,False)])

