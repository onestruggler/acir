"""Runs of D/N8 (S274, S277, S275) in the Python model se.py, checked step by step:
`python se_runs.py` (from this folder).  New runs are developed here first."""
from se import *
# ---- runs1 ----
T_=True; F_=False
def tau(j,q): return j+1 if q==j else (j if q==j+1 else q)
def swapG(j,x):
    _,Kd,tg,cs,b = x
    return ('g',Kd,tuple(tau(j,t) for t in tg),tuple((tau(j,p),v) for p,v in cs),b)
Z = lambda j: S('Z',j); H_ = lambda j: S('H',j); C_ = lambda j: S('C',j); SW = lambda j: S('S',j)
bx0 = G('box',[0],[(1,T_),(2,T_),(3,T_),(4,T_)],True)
wW = G('zx',[0],[(1,T_),(2,T_)],False); wV = G('xz',[0],[(1,T_),(2,T_)],False)
cC = G('box',[1],[(0,T_),(3,T_),(4,T_)],True)
bx1p = swapG(0,bx0); bx2 = swapG(1,bx1p)
W1 = swapG(0,wW); ZX2 = swapG(1,W1); V1 = swapG(0,wV); XZ2 = swapG(1,V1)
C1 = swapG(0,cC); B0 = swapG(1,C1)
B1 = swapG(0,B0)
print('bx2',bx2,'ZX2',ZX2,'B0',B0,'B1',B1)
def sw(j,x): return ([SW(j),x,SW(j)],[swapG(j,x)])
k=4
# table for R19b
T = [([Z(0),bx0],[bx0,Z(0)]), sw(0,bx0), sw(1,bx1p)]
r19 = [('rw',1,2,True),('rw',2,1,True),('sem',0,3,[SW(1),SW(0),Z(0)],4),('rw',2,0,False),
       ('sem',3,3,[SW(0),SW(1),Z(2)],4),('rw',1,1,False),('rw',0,2,False)]
print('R19b', run(k,T,[Z(2),bx2],r19) == [bx2,Z(2)])
# table for R269b
T2 = [([bx0],[wW,cC,wV,cC]), sw(0,bx0), sw(1,bx1p), sw(0,wW), sw(1,W1), sw(0,cC), sw(1,C1), sw(0,wV), sw(1,V1)]
ins = [SW(0),SW(1),SW(1),SW(0)]
r269 = [('rw',0,2,True),('rw',1,1,True),('rw',2,0,False),
        # [S1,S0,W,C,V,C,S0,S1]
        ('sem',3,0,ins,4),('sem',8,0,ins,4),('sem',13,0,ins,4),
        # [S1,S0,W,S0,S1,S1,S0,C,S0,S1,S1,S0,V,S0,S1,S1,S0,C,S0,S1]
        ('rw',16,5,False),('rw',15,6,False),
        ('rw',11,7,False),('rw',10,8,False),
        ('rw',6,5,False),('rw',5,6,False),
        ('rw',1,3,False),('rw',0,4,False)]
print('R269b', run(k,T2,[bx2],r269) == [ZX2,B0,XZ2,B0])
# (272'): [C0, B0] -> [B0, C0]
T3 = [([Z(2),bx2],[bx2,Z(2)]), ([bx2],[ZX2,B0,XZ2,B0])]
r272 = [('sem',0,1,[Z(2),XZ2,ZX2,Z(2),C_(0)],4),
        ('sem',6,0,[XZ2,ZX2],4),
        ('sem',7,0,[B0,B0],1),
        ('sem',2,3,[Z(2),ZX2],4),
        ('rw',3,1,True),
        ('rw',2,0,False),
        ('rw',2,1,False),
        ('sem',5,3,[Z(2)],1),
        ('sem',0,3,[Z(2)],4),
        ('sem',2,3,[Z(2),C_(0)],4),
        ('sem',0,3,[B0],1)]
w = run(k,T3,[C_(0),B0],r272, verbose=False)
print('272p', w == [B0,C_(0)], w)
# (274): [B1] -> [B0]
sw9 = [C_(0),H_(1),H_(0),C_(0),H_(1),H_(0),C_(0),H_(1),H_(0)]
T4 = [([C_(0),B0],[B0,C_(0)]), ([B0,H_(1)],[H_(1),B0]), sw(0,B0)]
r274 = [('rw',0,2,True), ('sem',2,1,sw9,2)]
pos = 1
for g in sw9:
    if g == C_(0): r274.append(('rw',pos,0,True))
    elif g == H_(1): r274.append(('rw',pos,1,False))
    else: r274.append(('sem',pos,2,[H_(0),B0],1))
    pos += 1
r274 += [('sem',1,9,[SW(0)],2), ('sem',0,2,[],2)]
w = run(k,T4,[B1],r274)
print('274', w == [B0], w)
# ---- runs2 ----
T_=True
K_ = lambda j: S('K',j); Z = lambda j: S('Z',j); H_ = lambda j: S('H',j); SW = lambda j: S('S',j)
def ppL(i): return [K_(i),H_(i+1),Z(i),K_(i),H_(i+1),Z(i),K_(i),H_(i+1),Z(i),SW(i)]
B1 = G('box',[1],[(2,T_),(3,T_),(4,T_)],True); B0 = G('box',[0],[(2,T_),(3,T_),(4,T_)],True)
ZXa = G('zx',[1],[(2,T_),(3,T_)],False); XZa = G('xz',[1],[(2,T_),(3,T_)],False)
Hg = G('hg',[2,1],[(4,T_)],True); Bq = G('box',[2],[(1,T_),(4,T_)],True)
PP = ppL(0)
k=4
r276 = [('sem',10,1,[ZXa,Hg,XZa,Hg],0),
        ('sem',0,11,[XZa]+PP,4), ('sem',1,11,[Bq]+PP,3), ('sem',2,11,[ZXa]+PP,4), ('sem',3,11,[Bq]+PP,3),
        ('sem',4,20,[],4), ('sem',0,4,[B1],0)]
w = run(k,[],PP+[B1]+PP,r276)
print('276', w == [B1])
# (277)
Hg12 = G('hg',[1,2],[(3,T_),(4,T_)],True); Hg02 = G('hg',[0,2],[(3,T_),(4,T_)],True)
PP12 = ppL(1); PP02 = [SW(1)]+ppL(0)+[SW(1)]
def tau(j,q): return j+1 if q==j else (j if q==j+1 else q)
def swapG(j,x):
    _,Kd,tg,cs,b = x
    return ('g',Kd,tuple(tau(j,t) for t in tg),tuple((tau(j,p),v) for p,v in cs),b)
B0p = swapG(1,B0); Hg01p = G('hg',[0,1],[(3,T_),(4,T_)],True)
print('B0p',B0p,'swap Hg01p',swapG(1,Hg01p))
T = [(PP+[B1]+PP,[B1]), ([B1],[B0]), ([SW(1),B0,SW(1)],[B0p]), ([SW(1),Hg01p,SW(1)],[swapG(1,Hg01p)])]
r277 = [('sem',0,1,PP12+[B1]+PP12,0),
        ('rw',10,0,True),
        ('sem',0,20,PP02,3),
        ('sem',13,20,PP02,3),
        ('rw',12,1,False),
        ('rw',11,2,False),
        ('sem',1,21,[Hg01p],2),
        ('rw',0,3,False)]
w = run(k,T,[Hg12],r277)
print('277', w == [Hg02], w)
# ---- runs3 ----
T_=True
Z = lambda j: S('Z',j); C_ = lambda j: S('C',j); SW = lambda j: S('S',j)
def tau(j,q): return j+1 if q==j else (j if q==j+1 else q)
def swapG(j,x):
    _,Kd,tg,cs,b = x
    return ('g',Kd,tuple(tau(j,t) for t in tg),tuple((tau(j,p),v) for p,v in cs),b)
def sw(j,x): return ([SW(j),x,SW(j)],[swapG(j,x)])
bx0 = G('box',[0],[(1,T_),(2,T_),(3,T_),(4,T_)],True)
wW = G('zx',[0],[(1,T_),(2,T_)],False); wV = G('xz',[0],[(1,T_),(2,T_)],False)
cC = G('box',[1],[(0,T_),(3,T_),(4,T_)],True)
k=4
# (286)
T = [([Z(0),bx0],[bx0,Z(0)]), ([bx0],[wW,cC,wV,cC])]
r286 = [('sem',0,0,[Z(0),Z(0)],4),('rw',1,0,False),('rw',1,1,False),
        ('sem',0,2,[wV,Z(0)],4),('sem',1,2,[cC,Z(0)],2),('sem',2,2,[wW,Z(0)],4),('sem',3,3,[cC],2)]
print('286', run(k,T,[bx0],r286) == [wV,cC,wW,cC])
# (271'): cz02 commutes with cC
cz02 = [SW(1),C_(0),SW(1)]
zxB = G('zx',[1],[(0,T_),(3,T_)],False); xzB = G('xz',[1],[(0,T_),(3,T_)],False)
bB = G('box',[0],[(1,T_),(4,T_)],True)
r271p = [('sem',3,1,[zxB,bB,xzB,bB],2),
         ('sem',0,4,[zxB]+cz02,4),('sem',1,4,[bB]+cz02,3),('sem',2,4,[xzB]+cz02,4),('sem',3,4,[bB]+cz02,3),
         ('sem',0,4,[cC],2)]
print("271'", run(k,[],cz02+[cC],r271p) == [cC]+cz02)
# (273)
T = [([bx0],[wW,cC,wV,cC]), (cz02+[cC],[cC]+cz02), ([bx0],[wV,cC,wW,cC])]
r273 = [('rw',3,0,False),('sem',0,4,[wV]+cz02,4),('rw',1,1,False),('sem',2,4,[wW]+cz02,4),
        ('rw',3,1,False),('rw',0,2,True)]
print('273', run(k,T,cz02+[bx0],r273) == [bx0]+cz02)
# relabeled (274): box[2|0,3,4] = box[1|0,3,4]
B0 = G('box',[0],[(2,T_),(3,T_),(4,T_)],True); B1 = G('box',[1],[(2,T_),(3,T_),(4,T_)],True)
a1 = swapG(1,B1); a2 = swapG(0,a1); b1 = swapG(1,B0); b2 = swapG(0,b1)
print('a2',a2,'b2',b2)
T = [([B1],[B0]), sw(1,B1), sw(0,a1), sw(1,B0), sw(0,b1)]
r274r = [('rw',0,2,True),('rw',1,1,True),('rw',2,0,False),('rw',1,3,False),('rw',0,4,False)]
print('274r', run(k,T,[a2],r274r) == [b2])
# (275): bx0 commutes with S1
C2 = swapG(1,cC)
T = [([bx0],[wW,cC,wV,cC]), ([a2],[b2]), sw(1,cC)]
r275 = [('rw',0,0,False),
        ('sem',3,0,[SW(1),SW(1)],4), ('rw',4,2,False), ('rw',4,1,False),
        ('sem',2,2,[SW(1),wV],4),
        ('sem',1,0,[SW(1),SW(1)],4), ('rw',2,2,False), ('rw',2,1,False),
        ('sem',0,2,[SW(1),wW],4),
        ('rw',1,0,True)]
print('275', run(k,T,[bx0,SW(1)],r275) == [SW(1),bx0])
