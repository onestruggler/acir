# Two-qubit Clifford+T words, semantics, axioms and the 46 RS equations.
# Letters: w = omega, H = H0, h = H1, S = S0, s = S1, T = T0, t = T1, Z = CZ.
import numpy as np, itertools, functools

LET = 'wHhSsTtZ'
w8 = np.exp(1j*np.pi/4)
I2 = np.eye(2)
Hm = np.array([[1,1],[1,-1]])/np.sqrt(2)
Sm = np.diag([1,1j]); Tm = np.diag([1,w8])
MAT = {
 'w': w8*np.eye(4), 'H': np.kron(Hm,I2), 'h': np.kron(I2,Hm),
 'S': np.kron(Sm,I2), 's': np.kron(I2,Sm), 'T': np.kron(Tm,I2), 't': np.kron(I2,Tm),
 'Z': np.diag([1,1,1,-1]),
}
def mat(word):
    M = np.eye(4, dtype=complex)
    for c in word: M = M @ MAT[c]
    return M
def eq(u, v): return np.allclose(mat(u), mat(v))

# abbreviations (Syntax.lean)
def X(i): return ('H' if i==0 else 'h') + ('SS' if i==0 else 'ss') + ('H' if i==0 else 'h')
def H_(i): return 'H' if i==0 else 'h'
def S_(i): return 'S' if i==0 else 's'
def T_(i): return 'T' if i==0 else 't'
def Tdg(i): return T_(i)*7
def Sdg(i): return S_(i)*3
def CX(i): return H_(i)+'Z'+H_(i)
def CXw(i): return CX(i)+X(i)
def CH(i): return S_(i)+H_(i)+T_(i)+CX(i)+Tdg(i)+H_(i)+Sdg(i)
def CHw(i): return CH(i)+H_(i)
OMINV = 'w'*7
SWAP = CX(0)+CX(1)+CX(0)

# axioms (Rel), as (lhs, rhs, name)
AX = []
for A in 'HhSsTtZ': AX.append(('w'+A, A+'w', 'c1_'+A))
for A in 'HST':
    for B in 'hst': AX.append((A+B, B+A, 'c2_'+A+B))
AX.append(('w'*8, '', 'c3'))
for i in (0,1): AX.append((H_(i)*2, '', 'c4_%d'%i))
for i in (0,1): AX.append((S_(i)*4, '', 'c5_%d'%i))
for i in (0,1): AX.append(((S_(i)+H_(i))*3, 'w', 'c6_%d'%i))
AX.append(('ZZ', '', 'c7'))
AX.append(('SZ', 'ZS', 'c8'))
AX.append(('sZ', 'Zs', 'c9'))
AX.append((X(0)+'Z', 'Z'+'ss'+X(0), 'c10'))
AX.append((X(1)+'Z', 'Z'+'SS'+X(1), 'c11'))
AX.append(('ZHZ', 'SHZSHSs'+OMINV, 'c12'))
AX.append(('ZhZ', 'shZshsS'+OMINV, 'c13'))
for i in (0,1): AX.append((T_(i)*2, S_(i), 'c14_%d'%i))
for i in (0,1): AX.append(((T_(i)+X(i))*2, 'w', 'c15_%d'%i))
AX.append(('TZ', 'ZT', 'c16'))
AX.append(('h'+'Z'+'H'+'h'+'Z'+'H'+'T', 't'+'h'+'Z'+'H'+'h'+'Z'+'H', 'c17'))
AX.append((CX(1)+'t'+'h'+Tdg(1)+CXw(1)+'t'+'h'+Tdg(1), 't'+'h'+Tdg(1)+CXw(1)+'t'+'h'+Tdg(1)+CX(1), 'c18'))
AX.append((CX(1)+'tht'+'h'+Tdg(1)+CXw(1)+'th'+Tdg(1)+'h'+Tdg(1), 'tht'+'h'+Tdg(1)+CXw(1)+'th'+Tdg(1)+'h'+Tdg(1)+CX(1), 'c19'))
AX.append((CHw(1)+'t'+CH(1)+CHw(0)+'T'+CH(0), CHw(0)+'T'+CH(0)+CHw(1)+'t'+CH(1), 'c20'))
for l,r,n in AX: assert eq(l,r), n

# simplified Greylyn (letters: o = omega0, a = X01, b = X12, c = X23, k = H01)
om = {0:'o'}; om[1]='aoa'; om[2]='b'+om[1]+'b'; om[3]='c'+om[2]+'c'
XG = {(0,1):'a',(1,2):'b',(2,3):'c',(0,2):'bab'}; XG[(0,3)]='c'+XG[(0,2)]+'c'; XG[(1,3)]='cbc'
HG = {(0,1):'k',(0,2):'bkb'}; HG[(0,3)]='c'+HG[(0,2)]+'c'; HG[(1,2)]='abkba'; HG[(1,3)]='c'+HG[(1,2)]+'c'; HG[(2,3)]='bc'+HG[(1,2)]+'cb'
FS = {  # f' = simple o f
 'w': om[0]+om[1]+om[2]+om[3], 'H': HG[(1,3)]+HG[(0,2)], 'h': HG[(2,3)]+HG[(0,1)],
 'S': om[2]*2+om[3]*2, 's': om[1]*2+om[3]*2, 'T': om[2]+om[3], 't': om[1]+om[3], 'Z': om[3]*4,
}
HT = {
 ('I','o'): (Tdg(0)+Tdg(1)+'w', 'O'), ('I','a'): (X(1)+CX(1), 'I'), ('I','b'): (SWAP,'I'),
 ('I','c'): (CX(1),'I'), ('I','k'): (X(0)+CH(1)+X(0),'I'),
 ('O','o'): (X(0)+CX(0)+'T'+CX(0)+X(0),'I'), ('O','a'): (X(1)+CX(1),'O'), ('O','b'): (SWAP,'O'),
 ('O','c'): ('t'+CX(1)+Tdg(1),'O'), ('O','k'): (X(0)+CH(1)+X(0),'O'),
}
def hstar(c, word):
    out=''
    for y in word:
        v, c = HT[(c,y)]
        out += v
    return out, c
SREL = {
 1:('o'*8,''),2:('kk',''),3:('aa',''),4:('bb',''),5:('cc',''),
 6:('o'+om[1], om[1]+'o'),7:(om[2]+'k','k'+om[2]),8:('ob','bo'),9:('oc','co'),
 10:('k'+HG[(2,3)],HG[(2,3)]+'k'),11:('kc','ck'),12:('ac','ca'),13:('aba','bab'),14:('bcb','cbc'),
 15:('o'+om[1]+'a','a'+'o'+om[1]),16:('o'+om[1]+'k','k'+'o'+om[1]),17:('ka',om[1]*4+'k'),
 18:('koo'+'k','o'*6+'k'+'ooo'+om[1]*5),19:('k'+HG[(2,3)]+HG[(0,2)]+HG[(1,3)],HG[(0,2)]+HG[(1,3)]+'k'+HG[(2,3)]),
}
EQN = {}
for i,x in enumerate('wHhSsTtZ'):
    v,c = hstar('I', FS[x]); assert c=='I'
    EQN[i+1] = (v, x)
for k in range(1,20):
    for ci,c in enumerate('IO'):
        l,r = SREL[k]
        (vl,cl),(vr,cr) = hstar(c,l), hstar(c,r)
        assert cl==cr
        EQN[9+2*(k-1)+ci] = (vl, vr)
if __name__ == '__main__':
    for n,(l,r) in EQN.items():
        print(n, len(l), len(r), eq(l,r))
