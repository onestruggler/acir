"""Check the matrix meaning of the basic two-level decoding frames.

Only the basic generators of Li, Ross and Selinger — (-1)_[0], the
X_[x,x+1] and K_[0,1,2,3] — get a matrix certificate (DecodeMatrices):
every other generator is conjugate to a basic one by adjacent X's
(CCX+HH-TwoLevel's Conjugation.decompose), both readings respect that
conjugation, and Repaired/DecodingMatrices carries the certificates
along it."""
import generate as g
import generate_frames as f
from pathlib import Path
ROOT=g.ROOT;P=g.PREFIX
BASIC=[('M',0)]+[('X',i,i+1) for i in range(7)]+[('K',0,1,2,3)]
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
for atom in BASIC:collect(at(atom))
def tab(v):
    if len(v)==1:return v[0]
    k=len(v)//2;return '('+tab(v[:k])+' , '+tab(v[k:])+')'
def literal(m):
    def z(a):return '(+ '+str(a)+')' if a>=0 else '(-[1+ '+str(-a-1)+' ])'
    return 'mat '+tab(['('+z(a)+' +√2 (+ 0))' for row in m for a in row])
folder=ROOT/'FrameEvaluation';folder.mkdir(exist_ok=True)
for old in folder.glob('E*.agda'):old.unlink()
blocks=[]
for t,i in E.items():
    if isinstance(t,str):
        m=g.matrix(t)[1];w=t;pr=f'Eq.trans (readM-gen {t}-gen) Eq.refl'
    elif not t:
        m=[[int(i==j) for j in range(8)] for i in range(8)];w='ε';pr='Eq.trans readM-ε Eq.refl'
    else:
        a,b=E[t[0]],E[t[1]];m=g.mul(mats[t[0]],mats[t[1]]);w=f'w{a} • w{b}'
        pr=f'Eq.trans (readM-• w{a} w{b}) (Eq.trans (Eq.cong₂ mulM {{x = readM w{a}}} {{y = matrix{a}}} {{u = readM w{b}}} {{v = matrix{b}}} e{a} e{b}) step{i})'
    mats[t]=m
    block=f'w{i} : Word Gen\nw{i} = {w}\nmatrix{i} : Mat 3\nmatrix{i} = {literal(m)}\n'
    if isinstance(t,tuple) and t:block+=g.matrix_step(i,a,b)
    block+=f'e{i} : readM w{i} ≡ matrix{i}\ne{i} = {pr}\n\n'
    blocks.append(block)
g.evaluation_chunks('FrameEvaluation','FrameEvaluation',g.matrix_imports,blocks,24)

def bound(a):
    r='z≤n'
    for _ in range(a+1):r='(s≤s '+r+')'
    return r
def gen(atom):
    k,*xs=atom
    if k=='M':return 'T.M-gen '+f.finpat(xs[0])
    return 'T.'+k+'-gen '+' '.join(f.finpat(i) for i in xs)+' '+' '.join(bound(i) for i in xs[:-1])
folder=ROOT/'DecodeMatrices';folder.mkdir(exist_ok=True)
for old in folder.glob('*.agda'):old.unlink()
for atom in BASIC:
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

# The basic letters, read off their certificates; the other index
# choices contradict Conj.Basic.
fp=f.finpat
def suc_(k,inner):return '('+'suc ('*k+inner+')'*k+')' if k else inner
NONE='(suc (suc (suc (suc (suc (suc (suc (suc ()))))))))'
basic=['basic (T.M-gen (zero)) _ = CM0.proved','basic (T.M-gen (suc _)) ()']
for a in range(8):
    for b in range(8):
        if a<7 and b==a+1:basic.append(f'basic (T.X-gen {fp(a)} {fp(b)} _) _ = CX{a}{b}.proved')
        else:basic.append(f'basic (T.X-gen {fp(a)} {fp(b)} _) ()')
    basic.append(f'basic (T.X-gen {fp(a)} {NONE} _) _')
basic.append(f'basic (T.X-gen {NONE} _ _) _')
basic+=['basic (T.K-gen (suc _) _ _ _ _ _ _) (() , _)',
        'basic (T.K-gen (zero) (zero) _ _ _ _ _) (_ , () , _)',
        'basic (T.K-gen (zero) (suc (suc _)) _ _ _ _ _) (_ , () , _)',
        f'basic (T.K-gen (zero) {fp(1)} (zero) _ _ _ _) (_ , _ , () , _)',
        f'basic (T.K-gen (zero) {fp(1)} {fp(1)} _ _ _ _) (_ , _ , () , _)',
        f'basic (T.K-gen (zero) {fp(1)} (suc (suc (suc _))) _ _ _ _) (_ , _ , () , _)']
for d in range(3):basic.append(f'basic (T.K-gen (zero) {fp(1)} {fp(2)} {fp(d)} _ _ _) (_ , _ , _ , ())')
basic.append(f'basic (T.K-gen (zero) {fp(1)} {fp(2)} {fp(3)} _ _ _) _ = CK0123.proved')
basic.append(f'basic (T.K-gen (zero) {fp(1)} {fp(2)} (suc (suc (suc (suc _)))) _ _ _) (_ , _ , _ , ())')

s=g.header('Repaired.DecodingMatrices')
s+=f'''open import Data.Nat.Base as ℕ using (ℕ ; suc ; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Fin.Base using (Fin ; zero ; suc ; _<_)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_ ; inj₁ ; inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import {P}.Repaired.Syntactics
open import {P}.Matrix using (⟦_⟧ᴹ ; matrix-• ; matrix-ε ; matrix-sound)
open import {P}.Repaired.Encoding using (decode)
import {P}.Repaired.EncodingMatrices as EM
import {P}.FrameWords as F
import {P}.TwoLevel as TwoLevel
import Presentation.Base as PB
import Examples.Groups.CCX+HH-TwoLevel.Syntactics as T
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S1
open import Examples.Groups.CCX+HH-TwoLevel.Reduction {{8}} using () renaming (sound-act to sound-act₁)
import Examples.Groups.CCX+HH-TwoLevel.Conjugation {{8}} as Conj
  using (Basic ; size ; decompose ; Step ; module Step)
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Syntactics as L
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
module Dim = SS.Dim 4
'''
for atom in BASIC:s+=f'import {P}.DecodeMatrices.{f.name(atom)} as C{f.name(atom)}\n'
s+='''
-- The basic letters, from their matrix certificates.
basic : ∀ g → Conj.Basic g → Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ F.decode g ⟧ᴹ
'''+'\n'.join(basic)+'''

-- Every other letter is a basic one conjugated by adjacent X's, and both
-- readings respect that conjugation: the two-level one by the soundness
-- of Table 1 (two-level), the circuit one by TwoLevel.decode-cong and
-- soundness (circuit).
private
  module _ (g g′ : T.Gen 8) (x y : Fin 8) .(xy : x < y)
           (rel : PB._≈_ (T._===_ {8}) [ g ]ʷ ([ T.X-gen x y xy ]ʷ • ([ g′ ]ʷ • [ T.X-gen x y xy ]ʷ))) where

    -- The words are written out in the types, not abbreviated: two
    -- spellings of one reading are compared by unfolding it.
    two-level : Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ _·*·_ {{R.RingD}} Dim.⟦ [ L.⌊ T.X-gen x y xy ⌋ ]ʷ ⟧ᴸ
                  (_·*·_ {{R.RingD}} Dim.⟦ [ L.⌊ g′ ⌋ ]ʷ ⟧ᴸ Dim.⟦ [ L.⌊ T.X-gen x y xy ⌋ ]ʷ ⟧ᴸ)
    two-level = Eq.trans (SS.⟦⌊⌋⟧ 4 [ g ]ʷ)
      (Eq.trans (Eq.cong SS.mapM (sound-act₁ rel S1.𝕀))
        (Eq.trans (Eq.sym (SS.⟦⌊⌋⟧ 4 w))
          (Eq.trans (Dim.⟦•⟧ᴸ [ ⌊X⌋ ]ʷ ([ L.⌊ g′ ⌋ ]ʷ • [ ⌊X⌋ ]ʷ))
            (Eq.cong (_·*·_ {{R.RingD}} Dim.⟦ [ ⌊X⌋ ]ʷ ⟧ᴸ) (Dim.⟦•⟧ᴸ [ L.⌊ g′ ⌋ ]ʷ [ ⌊X⌋ ]ʷ)))))
      where
      ⌊X⌋ = L.⌊ T.X-gen x y xy ⌋
      w = [ T.X-gen x y xy ]ʷ • ([ g′ ]ʷ • [ T.X-gen x y xy ]ʷ)

    circuit : _·*·_ {{R.RingD}} ⟦ F.decode (T.X-gen x y xy) ⟧ᴹ
                (_·*·_ {{R.RingD}} ⟦ F.decode g′ ⟧ᴹ ⟦ F.decode (T.X-gen x y xy) ⟧ᴹ) ≡ ⟦ F.decode g ⟧ᴹ
    circuit = Eq.trans (Eq.cong (_·*·_ {{R.RingD}} ⟦ F.decode (T.X-gen x y xy) ⟧ᴹ)
                          (Eq.sym (matrix-• (F.decode g′) (F.decode (T.X-gen x y xy)))))
      (Eq.trans (Eq.sym (matrix-• (F.decode (T.X-gen x y xy)) (F.decode g′ • F.decode (T.X-gen x y xy))))
        (matrix-sound {F.decode (T.X-gen x y xy) • (F.decode g′ • F.decode (T.X-gen x y xy))} {F.decode g}
          (TwoLevel.decode-cong (PB.sym rel))))

mutual
  dyadic-letter′ : (k : ℕ) (g : T.Gen 8) → Conj.size g ℕ.< k → Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ F.decode g ⟧ᴹ
  dyadic-letter′ (suc k) g (s≤s lt) = by k g lt (Conj.decompose g)

  by : (k : ℕ) (g : T.Gen 8) → Conj.size g ℕ.≤ k → Conj.Basic g ⊎ Conj.Step g →
       Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ F.decode g ⟧ᴹ
  by k g lt (inj₁ b) = basic g b
  by k g lt (inj₂ s) =
    Eq.trans (two-level g g′ x y xy rel)
      (Eq.trans (Eq.cong₂ (_·*·_ {{R.RingD}}) bX (Eq.cong₂ (_·*·_ {{R.RingD}}) ih bX))
        (circuit g g′ x y xy rel))
    where
    open Conj.Step s using (x ; y ; xy ; g′ ; rel)
    bX = basic (T.X-gen x y xy) (Conj.Step.adj s)
    ih = dyadic-letter′ k g′ (ℕP.<-≤-trans (Conj.Step.small s) lt)

dyadic-letter : ∀ g → Dim.⟦ [ L.⌊ g ⌋ ]ʷ ⟧ᴸ ≡ ⟦ decode (L.⌊ g ⌋) ⟧ᴹ
dyadic-letter g = dyadic-letter′ (suc (Conj.size g)) g ℕP.≤-refl

letter-matrix : ∀ g → Dim.⟦ [ g ]ʷ ⟧ᴸ ≡ ⟦ decode g ⟧ᴹ
letter-matrix (L.⌊ g ⌋) = dyadic-letter g
letter-matrix L.IH = EM.gen-matrix H2-gen

-- Decoding every word preserves its matrix, including I ⊗ H.
decode-matrix : ∀ w → Dim.⟦ w ⟧ᴸ ≡ ⟦ (decode ʷ) w ⟧ᴹ
decode-matrix [ g ]ʷ = letter-matrix g
decode-matrix ε = Eq.sym matrix-ε
decode-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ w v)
  (Eq.trans (Eq.cong₂ (_·*·_ {{R.RingD}})
    (decode-matrix w) (decode-matrix v))
    (Eq.sym (matrix-• ((decode ʷ) w) ((decode ʷ) v))))
'''
(ROOT/'Repaired'/'DecodingMatrices.agda').write_text(s,encoding='utf-8')
letters=ROOT/'Repaired'/'DecodingLetters'
if letters.exists():
    for old in letters.glob('*.agda'):old.unlink()
    letters.rmdir()
print('Decoding matrix certificates:',len(BASIC),'basic letters;',len(E),'shared evaluations')
