"""Check the retained K definition in the intended exact semantics."""
import generate as g
ROOT=g.ROOT;P=g.PREFIX
E={};mats={}
def collect(t):
    if t not in E:
        if isinstance(t,tuple) and t:collect(t[0]);collect(t[1])
        E[t]=len(E)
    return E[t]
for w in ['K12','NK X0 NK X0']:collect(g.tree(w))
def tab(v):
    if len(v)==1:return v[0]
    k=len(v)//2;return '('+tab(v[:k])+', '+tab(v[k:])+')'
def literal(m):
    def z(a):return '(+ '+str(a)+')' if a>=0 else '(-[1+ '+str(-a-1)+' ])'
    return 'mat '+tab(['('+z(a)+' +√2 (+ 0))' for row in m for a in row])
s=g.header('Repaired.KMatrix')
s+=f'''open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Product.Base using (_,_ )
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import {P}.Syntactics
open import {P}.GateMatrices
open import {P}.Interpretation
'''
for t,i in E.items():
    if isinstance(t,str):
        m=g.matrix(t)[1];w=t;proof=f'Eq.trans (readM-gen {t}-gen) Eq.refl'
    else:
        a,b=E[t[0]],E[t[1]];m=g.mul(mats[t[0]],mats[t[1]]);w=f'w{a} • w{b}'
        proof=f'Eq.trans (readM-• w{a} w{b}) (Eq.trans (Eq.cong₂ mulM e{a} e{b}) step{i})'
    mats[t]=m
    s+=f'\nw{i} : Word Gen\nw{i} = {w}\nmatrix{i} : Mat 3\nmatrix{i} = {literal(m)}\n'
    if isinstance(t,tuple):s+=f'step{i} : mulM matrix{a} matrix{b} ≡ matrix{i}\nstep{i} = Eq.refl\n'
    s+=f'e{i} : readM w{i} ≡ matrix{i}\ne{i} = {proof}\n'
i,j=[E[g.tree(w)] for w in ['K12','NK X0 NK X0']]
s+=f'''
checked : scaledM K12 (NK • X0 • NK • X0) ≡ scaledM (NK • X0 • NK • X0) K12
checked = Eq.trans (Eq.cong (scaleM (√2^ len (NK • X0 • NK • X0))) e{i})
  (Eq.trans Eq.refl (Eq.sym (Eq.cong (scaleM (√2^ len K12)) e{j})))
'''
(ROOT/'Repaired'/'KMatrix.agda').write_text(s,encoding='utf-8')
