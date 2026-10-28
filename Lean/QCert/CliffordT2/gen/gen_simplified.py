# Generate QCert/CliffordT2/SimplifiedGreylyn.lean: the 123 instances of
# Greylyn's relations, translated to the five-generator presentation.
import itertools, sys
sys.path.insert(0, __import__('os').path.dirname(__file__))

rules = [
 ('bw','wb'), ('cw','wc'), ('ch','hc'), ('ca','ac'),
 ('aa',''), ('bb',''), ('cc',''),
 ('aba','bab'), ('bcb','cbc'),
 ('acba','cbab'),
 ('wwwwwwww',''), ('hh',''),
]
def rewrite1(w):
    for i in range(len(w)):
        for l,r in rules:
            if w.startswith(l, i):
                return w[:i]+r+w[i+len(l):]
    return None
def normalize(w, n=10000):
    for _ in range(n):
        w2 = rewrite1(w)
        if w2 is None: return w
        w = w2
    return w
def nsteps(w):
    k=0
    while True:
        w2=rewrite1(w)
        if w2 is None: return k
        w=w2; k+=1
inv = {'w':'wwwwwww','a':'a','b':'b','c':'c','h':'h'}
def winv(w): return ''.join(inv[x] for x in reversed(w))
X = {(0,1):'a',(1,2):'b',(2,3):'c'}
X[(0,2)]='bab'; X[(0,3)]='c'+X[(0,2)]+'c'; X[(1,3)]='cbc'
om = {0:'w'}; om[1]='awa'; om[2]='b'+om[1]+'b'; om[3]='c'+om[2]+'c'
H = {(0,1):'h'}
H[(0,2)]='bhb'; H[(0,3)]='c'+H[(0,2)]+'c'
H[(1,2)]='abhba'; H[(1,3)]='c'+H[(1,2)]+'c'; H[(2,3)]='bc'+H[(1,2)]+'cb'
S = {
 1:('w'*8,''), 2:('hh',''), 3:('aa',''), 4:('bb',''), 5:('cc',''),
 6:(om[0]+om[1], om[1]+om[0]), 7:(om[2]+'h','h'+om[2]), 8:('wb','bw'), 9:('wc','cw'),
 10:('h'+H[(2,3)], H[(2,3)]+'h'), 11:('hc','ch'), 12:('ac','ca'),
 13:('aba','bab'), 14:('bcb','cbc'),
 15:(om[0]+om[1]+'a', 'a'+om[0]+om[1]), 16:(om[0]+om[1]+'h','h'+om[0]+om[1]),
 17:('ha', om[1]*4+'h'), 18:('hwwh', 'w'*6+'h'+'www'+om[1]*5),
 19:('h'+H[(2,3)]+H[(0,2)]+H[(1,3)], H[(0,2)]+H[(1,3)]+'h'+H[(2,3)]),
}
gs2 = [''.join(t) for n in range(0,6) for t in itertools.product('abc',repeat=n)]
FUEL = 200
def solve(l,r):
    assert nsteps(l) < FUEL and nsteps(r) < FUEL, (l, r)
    if normalize(l)==normalize(r): return 'nf'
    for sn in [6,7,10,15,16,17,18,19]:
        su,sv = S[sn]
        for g in gs2:
            for (u,v,d) in [(su,sv,True),(sv,su,False)]:
                gu = g+u+winv(g); gv = g+v+winv(g)
                if normalize(l)==normalize(gu) and normalize(r)==normalize(gv):
                    assert nsteps(gu)<FUEL and nsteps(gv)<FUEL
                    return ('bc',sn,g,d)
    raise Exception('unsolved %s %s' % (l, r))
leanword = {'w':'ω₀','a':'X₀₁','b':'X₁₂','c':'X₂₃','h':'H₀₁'}
def lw(g):
    if g=='': return '1'
    return '(' + ' * '.join(leanword[c] for c in g) + ')'
stats = {'nf':0,'bc':0}
def tac(sol):
    if sol=='nf':
        stats['nf']+=1
        return 'exact by_nf _ _ (by decide +kernel +revert)'
    stats['bc']+=1
    _,sn,g,d = sol
    huv = f'(Derivable.of SRel.s{sn})' + ('' if d else '.symm')
    return f'exact by_bc {lw(g)} {lw(winv(g))} {huv} (by decide +kernel +revert) (by decide +kernel +revert)'
out=[]
R=range(4)
out.append('  | r1 j => fin_cases j <;> exact by_nf _ _ (by decide +kernel +revert)')
for fam,word in [('2',H),('3',X)]:
    out.append(f'  | r{fam} j k hjk =>')
    out.append('    fin_cases j <;> fin_cases k')
    for j in R:
        for k in R:
            if not j<k: out.append('    · exact absurd hjk (by decide)')
            else: out.append('    · '+tac(solve(word[(j,k)]*2,'')))
out.append('  | r4 j k hjk =>')
out.append('    fin_cases j <;> fin_cases k')
for j in R:
    for k in R:
        if j==k: out.append('    · exact absurd rfl hjk')
        else: out.append('    · '+tac(solve(om[j]+om[k],om[k]+om[j])))
for fam,word in [('5',H),('6',X)]:
    out.append(f'  | r{fam} j k l hjk hlj hlk =>')
    out.append('    fin_cases j <;> fin_cases k <;> fin_cases l')
    for j in R:
        for k in R:
            for l in R:
                if not j<k: out.append('    · exact absurd hjk (by decide)')
                elif l==j: out.append('    · exact absurd rfl hlj')
                elif l==k: out.append('    · exact absurd rfl hlk')
                else: out.append('    · '+tac(solve(om[l]+word[(j,k)],word[(j,k)]+om[l])))
for fam,(A,B) in [('7',(H,H)),('8',(H,X)),('9',(X,X))]:
    out.append(f'  | r{fam} j k l t hjk hlt hlj hlk htj htk =>')
    out.append('    fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases t')
    for j in R:
        for k in R:
            for l in R:
                for t in R:
                    if not j<k: out.append('    · exact absurd hjk (by decide)')
                    elif not l<t: out.append('    · exact absurd hlt (by decide)')
                    elif l==j: out.append('    · exact absurd rfl hlj')
                    elif l==k: out.append('    · exact absurd rfl hlk')
                    elif t==j: out.append('    · exact absurd rfl htj')
                    elif t==k: out.append('    · exact absurd rfl htk')
                    else: out.append('    · '+tac(solve(A[(j,k)]+B[(l,t)],B[(l,t)]+A[(j,k)])))
for fam in ['10','11']:
    out.append(f'  | r{fam} j k hjk =>')
    out.append('    fin_cases j <;> fin_cases k')
    for j in R:
        for k in R:
            if not j<k: out.append('    · exact absurd hjk (by decide)')
            elif fam=='10': out.append('    · '+tac(solve(X[(j,k)]+om[k],om[j]+X[(j,k)])))
            else: out.append('    · '+tac(solve(X[(j,k)]+om[j],om[k]+X[(j,k)])))
for fam,word in [('12',X),('14',H)]:
    out.append(f'  | r{fam} j k l hjk hkl =>')
    out.append('    fin_cases j <;> fin_cases k <;> fin_cases l')
    for j in R:
        for k in R:
            for l in R:
                if not j<k: out.append('    · exact absurd hjk (by decide)')
                elif not k<l: out.append('    · exact absurd hkl (by decide)')
                else: out.append('    · '+tac(solve(X[(j,k)]+word[(j,l)],word[(k,l)]+X[(j,k)])))
for fam,word in [('13',X),('15',H)]:
    out.append(f'  | r{fam} j k l hlj hjk =>')
    out.append('    fin_cases j <;> fin_cases k <;> fin_cases l')
    for j in R:
        for k in R:
            for l in R:
                if not l<j: out.append('    · exact absurd hlj (by decide)')
                elif not j<k: out.append('    · exact absurd hjk (by decide)')
                else: out.append('    · '+tac(solve(X[(j,k)]+word[(l,j)],word[(l,k)]+X[(j,k)])))
for fam in ['16','17','18','19']:
    out.append(f'  | r{fam} j k hjk =>')
    out.append('    fin_cases j <;> fin_cases k')
    for j in R:
        for k in R:
            if not j<k: out.append('    · exact absurd hjk (by decide)'); continue
            p=(j,k)
            if fam=='16': l_,r_ = om[j]+om[k]+X[p], X[p]+om[j]+om[k]
            if fam=='17': l_,r_ = om[j]+om[k]+H[p], H[p]+om[j]+om[k]
            if fam=='18': l_,r_ = H[p]+X[p], om[k]*4+H[p]
            if fam=='19': l_,r_ = H[p]+om[j]*2+H[p], om[j]*6+H[p]+om[j]*3+om[k]*5
            out.append('    · '+tac(solve(l_,r_)))
out.append('  | r20 j k l t hjk hkl hlt =>')
out.append('    fin_cases j <;> fin_cases k <;> fin_cases l <;> fin_cases t')
for j in R:
    for k in R:
        for l in R:
            for t in R:
                if not j<k: out.append('    · exact absurd hjk (by decide)')
                elif not k<l: out.append('    · exact absurd hkl (by decide)')
                elif not l<t: out.append('    · exact absurd hlt (by decide)')
                else: out.append('    · '+tac(solve(H[(j,k)]+H[(l,t)]+H[(j,l)]+H[(k,t)],H[(j,l)]+H[(k,t)]+H[(j,k)]+H[(l,t)])))
body='\n'.join(out)
lean = '''/-
Copyright (c) 2026 QCert contributors. All rights reserved.

# Greylyn's relations from the five-generator presentation

Each of the 123 instances of Greylyn's relations (`QCert.Greylyn.Rel 4`),
translated by `simple`, is derivable from (S1)–(S19): both sides are
normalized by the rewriting system `rules`, after conjugating one of
(S1)–(S19) by a permutation where needed (the authors' basis change).
Hence every derivation from Greylyn's relations is carried to one from
(S1)–(S19) (`derivable_simple`; `theorem-simple-of-greylyn` of the
authors' code).

Generated by `QCert/CliffordT2/gen/gen_simplified.py`.
-/
import QCert.CliffordT2.Simplified
import Mathlib.Tactic.FinCases

namespace QCert.CliffordT2.Simplified

open SW

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
/-- Every axiom of Greylyn's presentation holds, translated. -/
theorem simple_axiom : ∀ (w v : Word (Greylyn.Gen 4)), Greylyn.Rel 4 w v →
    Derivable SRel (FreeMonoid.lift simple w) (FreeMonoid.lift simple v) := by
  intro w v h
  cases h with
''' + body + '''

/-- Derivations from Greylyn's relations are carried to derivations from
(S1)–(S19). -/
theorem derivable_simple {w v : Word (Greylyn.Gen 4)} (h : Derivable (Greylyn.Rel 4) w v) :
    Derivable SRel (FreeMonoid.lift simple w) (FreeMonoid.lift simple v) :=
  Derivable.map (FreeMonoid.lift simple) simple_axiom h

end QCert.CliffordT2.Simplified
'''
import os
here = os.path.dirname(os.path.abspath(__file__))
import sys
sys.path.insert(0, here)
from paths import OUT
dst = os.path.join(OUT, 'SimplifiedGreylyn.lean')
open(dst,'w',encoding='utf-8',newline='\n').write(lean)
print(len(out), stats)
