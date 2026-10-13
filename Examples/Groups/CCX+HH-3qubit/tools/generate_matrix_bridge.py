"""Finite primitive matrix checks for the two-level encoding."""
import generate as g
ROOT=g.ROOT;P=g.PREFIX
def fin(i):return '('+'suc ('*i+'zero'+')'*i+')'
s=g.header('Repaired.EncodingMatrices')
s+=f'''open import Data.Fin.Base using (zero ; suc)
open import Data.Product.Base using (_,_ )
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Quantum.Synthesis.Matrix using (_·*·_)
open import {P}.Repaired.Syntactics
open import {P}.GateMatrices
open import {P}.Core
open import {P}.Matrix using (module BM ; ⟦_⟧ᴹ ; matrix-gen ; matrix-ε ; matrix-• ; matrix-sound)
open import {P}.Repaired.Encoding using (encode ; e)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
import Examples.Groups.CCX+HH-TwoLevel.Scaled.Semantics as SS

module Dim = SS.Dim 4

opaque
  unfolding R._+ᴰ_ R._*ᴰ_ R.-ᴰ_ SS.actV SS.set₁ SS.set₂

  primitive-matrix : ∀ g → Dim.⟦ encode g ⟧ᴸ ≡ BM.Φ (degree (embed g) , ix (gateM (embed g)))
'''
for x in ['X0','CX01','CCX12','K12','CCZ','NK','H2']:
    s+=f'  primitive-matrix c{x} = SS.mat-ext\n    (λ {{ '
    s+='\n       ; '.join(fin(i)+' '+fin(j)+' → Eq.refl' for i in range(8) for j in range(8))
    s+='\n       ; (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) _\n       ; _ (suc (suc (suc (suc (suc (suc (suc (suc ())))))))) })\n'
s+='''
core-matrix : ∀ w → Dim.⟦ (encode ʷ) w ⟧ᴸ ≡ ⟦ ⌞ w ⌟ ⟧ᴹ
core-matrix [ g ]ʷ = Eq.trans (primitive-matrix g) (Eq.sym (matrix-gen (embed g)))
core-matrix ε = Eq.sym matrix-ε
core-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ ((encode ʷ) w) ((encode ʷ) v))
  (Eq.trans (Eq.cong₂ _·*·_ (core-matrix w) (core-matrix v))
    (Eq.sym (matrix-• ⌞ w ⌟ ⌞ v ⌟)))

gen-matrix : ∀ g → Dim.⟦ e g ⟧ᴸ ≡ ⟦ [ g ]ʷ ⟧ᴹ
gen-matrix g = Eq.trans (core-matrix (core g)) (Eq.sym (matrix-sound (gen-expand g)))

-- The encoding denotes exactly the same matrix as the circuit.
encode-matrix : ∀ w → Dim.⟦ (e ʷ) w ⟧ᴸ ≡ ⟦ w ⟧ᴹ
encode-matrix [ g ]ʷ = gen-matrix g
encode-matrix ε = Eq.sym matrix-ε
encode-matrix (w • v) = Eq.trans (Dim.⟦•⟧ᴸ ((e ʷ) w) ((e ʷ) v))
  (Eq.trans (Eq.cong₂ _·*·_ (encode-matrix w) (encode-matrix v))
    (Eq.sym (matrix-• w v)))
'''
(ROOT/'Repaired'/'EncodingMatrices.agda').write_text(s,encoding='utf-8')
