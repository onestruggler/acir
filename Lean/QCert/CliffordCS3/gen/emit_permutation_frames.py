"""Checked permutation identities used by the remaining local frames."""
from permutation_normalize import *
def fl(l):return '['+', '.join(map(str,l))+']'
def chunks(st):
    out=[]
    for start in range(0,len(st),32):
        ss=st[start:start+32];c=0
        for i,k,rev in reversed(ss):c=c*33554432+2*(4096*i+k)+(0 if rev else 1)
        out.append(f'({len(ss)}, {c})')
    return '['+', '.join(out)+']'
data=json.loads((Path(__file__).parent/'data/permutation_natural.json').read_text())
tn=data['tokens']; gn=data['gates'];GRAY=[5,1,0,4,6,2,3,7]
def expand(w):return sum((tn[i] for i in w),[])
def gray_word(p):
    a=list(range(8));w=[]
    for k in range(7):
        j=next(j for j in range(k,8) if a[GRAY[j]]==p[GRAY[k]])
        for z in range(j-1,k-1,-1):
            x,y=GRAY[z:z+2];a[x],a[y]=a[y],a[x];w.append(z)
    assert a==list(p)
    return w
F=[4,5,6,4,5]
sw=gray_word(permutation(expand(F[::-1])+gn['X2']))
assert all(i<5 for i in sw),sw
l=expand(F+sw);r=gn['X2'];nl,sl=normalize(l);nr,sr=normalize(r);assert nl==nr
st=sl+[(p,k,not rev)for p,k,rev in reversed(sr)]
out=f'''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# A wire flip and the canonical four-point frame
-/
import QCert.CliffordCS3.Three.PermutationRoutes

set_option maxRecDepth 100000

namespace QCert.CliffordCS3.Three.PermutationFrames
open PermutationRoutes PermutationNatural

def frame : List (Fin 7) := {fl(F)}
def stabilizer : List (Fin 7) := {fl(sw)}

theorem stabilizer_bound : ∀ d ∈ stabilizer, d.val < 5 := by decide

theorem frame_stabilizer : Derivable Rel (tokens (frame ++ stabilizer)) (W.X 2) :=
  (tokens_eq (frame ++ stabilizer)).trans
    ((derive {fl(l)} natural_X2 {chunks(st)} (by decide +kernel)).trans gate_X2.symm)

end QCert.CliffordCS3.Three.PermutationFrames
'''
path=ROOT/'CliffordCS3/Three/PermutationFrames.lean';path.write_text(out,encoding='utf8')
print('stabilizer',sw)
