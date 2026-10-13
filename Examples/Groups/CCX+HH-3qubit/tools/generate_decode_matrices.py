"""Check the matrix meaning of every finite two-level decoding frame."""
import generate as g
import generate_frames as f
from pathlib import Path
ROOT=g.ROOT;P=g.PREFIX
def pt(q):return g.tree(' '.join('t'+str(i)+str(i+1) for i in q))
def at(atom):
    if atom[0]=='X':return pt(f.transposition(*atom[1:]))
    q=f.afr(atom)
    return (pt(q),(g.tree(f.center(atom)),pt(tuple(reversed(q)))))
E={};mats={}
def collect(t):
    if t not in E:
        if isinstance(t,tuple) and t:collect(t[0]);collect(t[1])
        E[t]=len(E)
    return E[t]
for atom in f.atoms:collect(at(atom))
def tab(v):
    if len(v)==1:return v[0]
    k=len(v)//2;return '('+tab(v[:k])+' , '+tab(v[k:])+')'
def literal(m):
    def z(a):return '(+ '+str(a)+')' if a>=0 else '(-[1+ '+str(-a-1)+' ])'
    return 'mat '+tab(['('+z(a)+' +√2 (+ 0))' for row in m for a in row])
imports=f'''open import Data.Integer.Base using (+_ ; -[1+_])
open import Data.Product.Base using (_,_ )
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import {P}.Syntactics
open import {P}.GateMatrices
open import {P}.Interpretation

'''
folder=ROOT/'FrameEvaluation';folder.mkdir(exist_ok=True)
blocks=[]
for t,i in E.items():
    if isinstance(t,str):
        m=g.matrix(t)[1];w=t;pr=f'Eq.trans (readM-gen {t}-gen) Eq.refl'
    elif not t:
        m=[[int(i==j) for j in range(8)] for i in range(8)];w='ε';pr='Eq.trans readM-ε Eq.refl'
    else:
        a,b=E[t[0]],E[t[1]];m=g.mul(mats[t[0]],mats[t[1]]);w=f'w{a} • w{b}'
        pr=f'Eq.trans (readM-• w{a} w{b}) (Eq.trans (Eq.cong₂ mulM e{a} e{b}) step{i})'
    mats[t]=m
    block=f'w{i} : Word Gen\nw{i} = {w}\nmatrix{i} : Mat 3\nmatrix{i} = {literal(m)}\n'
    if isinstance(t,tuple) and t:block+=f'step{i} : mulM matrix{a} matrix{b} ≡ matrix{i}\nstep{i} = Eq.refl\n'
    block+=f'e{i} : readM w{i} ≡ matrix{i}\ne{i} = {pr}\n\n'
    blocks.append(block)
for chunk,offset in enumerate(range(0,len(blocks),24)):
    s=g.header(f'FrameEvaluation.E{chunk:02d}')+imports
    if chunk:s+=f'open import {P}.FrameEvaluation.E{chunk-1:02d} public\n\n'
    s+=''.join(blocks[offset:offset+24])
    (folder/f'E{chunk:02d}.agda').write_text(s,encoding='utf-8')
s=g.header('FrameEvaluation')+f'open import {P}.FrameEvaluation.E{chunk:02d} public\n'
(ROOT/'FrameEvaluation.agda').write_text(s,encoding='utf-8')

def bound(a):
    r='z≤n'
    for _ in range(a+1):r='(s≤s '+r+')'
    return r
def gen(atom):
    k,*xs=atom
    if k=='M':return 'T.M-gen '+f.finpat(xs[0])
    return 'T.'+k+'-gen '+' '.join(f.finpat(i) for i in xs)+' '+' '.join(bound(i) for i in xs[:-1])
folder=ROOT/'DecodeMatrices';folder.mkdir(exist_ok=True)
for atom in f.atoms:
    name=f.name(atom);i=E[at(atom)];degree=2 if atom[0]=='K' else 0
    s=g.header('DecodeMatrices.'+name)
    s+=f'''open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (s≤s ; z≤n)
open import Data.Product.Base using (_,_ )
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import {P}.Syntactics
open import {P}.GateMatrices
open import {P}.Interpretation
import {P}.FrameWords as F
open import {P}.Matrix using (module BM ; ⟦_⟧ᴹ)
open import {P}.FrameEvaluation using (matrix{i} ; e{i})
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
module Dim = SS.Dim 4

letter : T.Gen 8
letter = {gen(atom)}

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_ SS.actV SS.set₁ SS.set₂
  calculation : Dim.⟦ [ L.⌊ letter ⌋ ]ʷ ⟧ᴸ ≡ BM.Φ ({degree} , ix matrix{i})
  calculation = SS.mat-ext (λ {{ '''
    s+='\n    ; '.join(f.finpat(r)+' '+f.finpat(c)+' → Eq.refl' for r in range(8) for c in range(8))
    s+='\n    ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _\n    ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })\n'
    s+=f'''
proved : Dim.⟦ [ L.⌊ letter ⌋ ]ʷ ⟧ᴸ ≡ ⟦ F.{name} ⟧ᴹ
proved = Eq.trans calculation (Eq.sym
  (BM.Φ-≐ {{ℓ = {degree}}} {{M = ix (readM F.{name})}} {{M′ = ix matrix{i}}}
    (λ x y → Eq.cong (λ M → ix M x y) e{i})))
'''
    (folder/(name+'.agda')).write_text(s,encoding='utf-8')

s=g.header('Repaired.DecodingMatrices')
s+=f'''open import Data.Empty.Irrelevant using (⊥-elim)
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Nat.Base using (s≤s ; z≤n)
import Data.Nat.Properties as NP
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import {P}.Repaired.Syntactics
open import {P}.Matrix using (⟦_⟧ᴹ ; matrix-• ; matrix-ε)
open import {P}.Repaired.Encoding using (decode)
import {P}.Repaired.EncodingMatrices as EM
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
module Dim = SS.Dim 4
'''
for atom in f.atoms:s+=f'import {P}.DecodeMatrices.{f.name(atom)} as C{f.name(atom)}\n'
s+='\ndyadic-letter : ∀ g → Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ decode (L.⌊ g ⌋) ⟧ᴹ\n'
from itertools import combinations
for kind,arity in [('M',1),('X',2),('K',4)]:
    vs=list('abcd')[:arity];ps=['p'+str(i) for i in range(arity-1)]
    def clause(vals):
        global s
        pats=[f.finpat(i) for i in vals]+vs[len(vals):]
        lhs='dyadic-letter (T.'+kind+'-gen '+' '.join(pats+ps)+')'
        for j in range(len(vals)-1):
            if vals[j]>=vals[j+1]:
                b='z≤n'
                for _ in range(vals[j+1]):b='(s≤s '+b+')'
                s+=lhs+f' = ⊥-elim (NP.≤⇒≯ {b} p{j})\n';return
        if len(vals)==arity:
            s+=lhs+' = C'+kind+''.join(str(i) for i in vals)+'.proved\n';return
        for i in range(8):clause(vals+[i])
    clause([])
s+='''
letter-matrix : ∀ g → Dim.⟦ [ g ]ʷ ⟧ᴸ ≡ ⟦ decode g ⟧ᴹ
letter-matrix (L.⌊ g ⌋) = dyadic-letter g
letter-matrix L.IH = EM.gen-matrix H2-gen

-- Decoding every word preserves its matrix, including I ⊗ H.
decode-matrix : ∀ w → Dim.⟦ w ⟧ᴸ ≡ ⟦ (decode ʷ) w ⟧ᴹ
decode-matrix [ g ]ʷ = letter-matrix g
decode-matrix ε = Eq.sym matrix-ε
decode-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ w v)
  (Eq.trans (Eq.cong₂ _·*·_ (decode-matrix w) (decode-matrix v))
    (Eq.sym (matrix-• ((decode ʷ) w) ((decode ʷ) v))))
'''
(ROOT/'Repaired'/'DecodingMatrices.agda').write_text(s,encoding='utf-8')
print('Decoding matrix certificates:',len(f.atoms),'letters;',len(E),'shared evaluations')
