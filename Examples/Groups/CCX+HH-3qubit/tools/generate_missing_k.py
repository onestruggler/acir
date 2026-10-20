"""Generate a checked F17 countermodel for the dyadic rules.

Conjugate the Figure 4 gates by I-J/4, retaining the intended CCZ and
negatively controlled K matrices. Agda checks every arithmetic step.
"""
import generate as g
import re
from pathlib import Path

ROOT=g.ROOT; P=g.PREFIX
OUT=ROOT/'MissingK'; OUT.mkdir(exist_ok=True)
I=[[int(i==j) for j in range(8)] for i in range(8)]
T=[[(I[i][j]-13)%17 for j in range(8)] for i in range(8)]
def mul(a,b):return [[x%17 for x in row] for row in g.mul(a,b)]
def gate(x):
    d,a=g.matrix(x)
    assert d%2==0
    a=[[v*pow(pow(2,d//2,17),-1,17)%17 for v in row] for row in a]
    return a if x in ('CCZ','NK') else mul(mul(T,a),T)
def tab(v):
    if len(v)==1:return str(v[0])
    k=len(v)//2;return '('+tab(v[:k])+' , '+tab(v[k:])+')'
def literal(m):return 'mat '+tab([x for row in m for x in row])

s=g.header('MissingK.Model')
s+=f'''open import Algebra.Bundles using (Monoid)
open import Data.Bool.Base using (true ; false)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Unit using (⊤)
open import Data.Vec.Base using ([] ; _∷_)
open import Level using (0ℓ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Examples.Groups.Clifford.Qubit.Model.Algebra public
open import {P}.Syntactics
import Presentation.Base as PB
open import Presentation.Independence using (Select ; _∣_)
import Normalization.StarInterp as SI

dyadic-rules : Select _===_
'''
for n in g.RELATIONS:s+=f'dyadic-rules r{n:03d} = '+('⊤' if n<102 else '⊥')+'\n'
s+='''
_===ᴰ_ : WRel Gen
_===ᴰ_ = _===_ ∣ dyadic-rules

monoid : Monoid 0ℓ 0ℓ
monoid = record
  { Carrier = Op 3
  ; _≈_ = _≐_
  ; _∙_ = _⊙_
  ; ε = Idₒ
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = record
          { refl = λ {M} → ≐-refl M ; sym = ≐-sym ; trans = ≐-trans }
        ; ∙-cong = ⊙-cong }
      ; assoc = ⊙-assoc }
    ; identity = ⊙-identityˡ , ⊙-identityʳ }
  }

gateM : Gen → Mat 3
'''
for x in g.GATES:
    if x!='H2':s+=f'gateM {x}-gen = {literal(gate(x))}\n'
s+='gateM H2-gen = idM\n'
s+='''
abstract
  readM : Word Gen → Mat 3
  readM [ x ]ʷ = gateM x
  readM ε = idM
  readM (w • v) = mulM (readM w) (readM v)

  readM-gen : ∀ x → readM [ x ]ʷ ≡ gateM x
  readM-gen x = Eq.refl
  readM-ε : readM ε ≡ idM
  readM-ε = Eq.refl
  readM-• : ∀ w v → readM (w • v) ≡ mulM (readM w) (readM v)
  readM-• w v = Eq.refl

module Ext = SI.Extend _===ᴰ_ monoid (λ x → ix (gateM x))

read-Ext : ∀ w → ix (readM w) ≐ Ext.⟦ w ⟧
read-Ext [ x ]ʷ a b = Eq.cong (λ M → ix M a b) (readM-gen x)
read-Ext ε a b = Eq.trans (Eq.cong (λ M → ix M a b) readM-ε) (ix-id a b)
read-Ext (w • v) a b = Eq.trans
  (Eq.cong (λ M → ix M a b) (readM-• w v))
  (Eq.trans (ix-mul (readM w) (readM v) a b)
    (⊙-cong (read-Ext w) (read-Ext v) a b))

by-matrix : ∀ {w v} → readM w ≡ readM v → Ext.⟦ w ⟧ ≐ Ext.⟦ v ⟧
by-matrix {w} {v} e a b = Eq.trans (Eq.sym (read-Ext w a b))
  (Eq.trans (Eq.cong (λ M → ix M a b) e) (read-Ext v a b))
'''
(OUT/'Model.agda').write_text(s,encoding='utf-8')

E={}
def collect(t):
    if t not in E:
        if isinstance(t,tuple) and t:collect(t[0]);collect(t[1])
        E[t]=len(E)
    return E[t]
rels={n:lr for n,lr in g.RELATIONS.items() if n<102}
for l,r in rels.values():collect(g.tree(l));collect(g.tree(r))
glue=('K12','NK X0 NK X0')
for w in glue:collect(g.tree(w))
s=g.header('MissingK.Evaluation')
s+=f'open import Data.Product.Base using (_,_ )\nopen import {P}.Syntactics\nopen import {P}.MissingK.Model\nopen import Relation.Binary.PropositionalEquality as Eq using (_≡_)\n\n'
matrices={}
for t,i in E.items():
    if isinstance(t,str):
        m=gate(t); w=t; proof=f'Eq.trans (readM-gen {t}-gen) Eq.refl'
    elif not t:
        m=I;w='ε';proof='Eq.trans readM-ε Eq.refl'
    else:
        a,b=E[t[0]],E[t[1]];m=mul(matrices[t[0]],matrices[t[1]]);w=f'w{a} • w{b}'
        proof=f'Eq.trans (readM-• w{a} w{b}) (Eq.trans (Eq.cong₂ mulM {{x = readM w{a}}} {{y = matrix{a}}} {{u = readM w{b}}} {{v = matrix{b}}} e{a} e{b}) step{i})'
    matrices[t]=m
    s+=f'w{i} : Word Gen\nw{i} = {w}\nmatrix{i} : Mat 3\nmatrix{i} = {literal(m)}\n'
    if isinstance(t,tuple) and t:s+=f'step{i} : mulM matrix{a} matrix{b} ≡ matrix{i}\nstep{i} = Eq.refl\n'
    s+=f'e{i} : readM w{i} ≡ matrix{i}\ne{i} = {proof}\n\n'
start=s.index('w0 : Word Gen')
imports=s[len(g.header('MissingK.Evaluation')):start]
blocks=re.split(r'(?=^w[0-9]+ : Word Gen)',s[start:],flags=re.M)
blocks=[block for block in blocks if block]
g.evaluation_chunks('MissingK.Evaluations','MissingK.Evaluation',lambda body:imports.rstrip('\n')+'\n',blocks,16)
s=g.header('MissingK')
s+=f'''open import Data.Bool.Base using (true ; false)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Vec.Base using ([] ; _∷_)
import Relation.Binary.PropositionalEquality as Eq
open import {P}.Syntactics
open import {P}.MissingK.Model
open import {P}.MissingK.Evaluation
import Presentation.Base as PB

axiom-sound : ∀ {{w v}} → w ===ᴰ v → Ext.⟦ w ⟧ ≐ Ext.⟦ v ⟧
'''
for n,(l,r) in g.RELATIONS.items():
    if n<102:
        il,ir=E[g.tree(l)],E[g.tree(r)]
        assert matrices[g.tree(l)]==matrices[g.tree(r)],n
        s+=f'axiom-sound (r{n:03d} , _) = by-matrix {{w = {g.word(l)}}} {{v = {g.word(r)}}} (Eq.trans e{il} (Eq.trans Eq.refl (Eq.sym e{ir})))\n'
    else:s+=f'axiom-sound (r{n:03d} , ())\n'
s+='''
module Sound = Ext.Cong axiom-sound

-- This theorem is about Figures 4 and 7 only. It makes no claim about
-- independence in the extension by the seven H₂ relations.
K-definition-underivable :
  PB._≈_ _===ᴰ_ K12 (NK • X0 • NK • X0) → ⊥
K-definition-underivable e = bad (Eq.trans (read-Ext K12 x y)
  (Eq.trans (Sound.fʷ-cong e x y) (Eq.sym (read-Ext (NK • X0 • NK • X0) x y))))
  where
'''
il,ir=[E[g.tree(w)] for w in glue];a,b=[matrices[g.tree(w)] for w in glue]
i,j=next((i,j) for i in range(8) for j in range(8) if a[i][j]!=b[i][j])
def bits(i):return '('+' ∷ '.join('true' if i&(1<<(2-j)) else 'false' for j in range(3))+' ∷ [])'
s+=f'  x y : Bits 3\n  x = {bits(i)}\n  y = {bits(j)}\n'
s+=f'''  unequal : Eq._≢_ {{A = 𝔽}} {a[i][j]} {b[i][j]}
  unequal ()
  bad : ix (readM K12) x y Eq.≢ ix (readM (NK • X0 • NK • X0)) x y
  bad eq = unequal (Eq.trans
    (Eq.sym (Eq.cong (λ M → ix M x y) e{il}))
    (Eq.trans eq (Eq.cong (λ M → ix M x y) e{ir})))
'''
(ROOT/'MissingK.agda').write_text(s,encoding='utf-8')
print('F17 countermodel:',len(rels),'relations;',len(E),'evaluations; witness',i,j,a[i][j],b[i][j])
