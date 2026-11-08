------------------------------------------------------------------------
-- Presentations of groups
--
-- Read the exact scaled operators as ordinary 8 × 8 matrices over
-- ℤ[1/√2], using the shared matrix bridge and binary basis numbering.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.Matrix where

open import Data.Product.Base using (_,_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open import Quantum.Synthesis.Matrix using (Matrix ; _·*·_)
open import Examples.Groups.CCX+HH-3qubit.Syntactics
open import Examples.Groups.CCX+HH-3qubit.GateMatrices
open import Examples.Groups.CCX+HH-3qubit.Interpretation
import Examples.Groups.CCX+HH-3qubit.Soundness as Sound
import Examples.Groups.Real-Clifford+CH.Semantics.Scaled as S
import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring as R
import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics as RMat
import Examples.Groups.Real-Clifford.Semantics.Matrix as RM₀
import Examples.Groups.Real-Clifford+CH.Auxiliary.Bridge.Matrix as BM₀

module RM = RM₀ {A = R.D} {{R.RingD}} {{R.AdjointD}}
  R.isCommutativeRing-D R.adj-D
module BM = BM₀ 3 (RM.bits 3) (RM.idx {3})
  (RM.bits-idx {3}) (RM.idx-bits 3)

⟦_⟧ᴹ : Word Gen → Matrix 8 8 R.D
⟦ w ⟧ᴹ = BM.Φ ⟦ w ⟧

matrix-~ : ∀ {s t} → s ~ t → BM.Φ s ≡ BM.Φ t
matrix-~ {s} {t} = BM.Φ-~ {s} {t}

matrix-sound : ∀ {w v} → w ≈ v → ⟦ w ⟧ᴹ ≡ ⟦ v ⟧ᴹ
matrix-sound {w} {v} e = BM.Φ-~ {⟦ w ⟧} {⟦ v ⟧} (Sound.sound e)

matrix-gen : ∀ g → ⟦ [ g ]ʷ ⟧ᴹ ≡ BM.Φ (degree g , ix (gateM g))
matrix-gen g = BM.Φ-≐ {ℓ = degree g}
  {M = ix (readM [ g ]ʷ)} {M′ = ix (gateM g)}
  (λ x y → Eq.cong (λ M → ix M x y) (readM-gen g))

matrix-ε : ⟦ ε ⟧ᴹ ≡ RMat.𝕀
matrix-ε = Eq.trans
  (BM.Φ-≐ {ℓ = 0} {M = ix (readM ε)} {M′ = Idₒ {3}}
    (λ x y → Eq.trans (Eq.cong (λ M → ix M x y) readM-ε) (ix-id x y)))
  BM.Φ-ε

matrix-• : ∀ w v → ⟦ w • v ⟧ᴹ ≡ ⟦ w ⟧ᴹ ·*· ⟦ v ⟧ᴹ
matrix-• w v = Eq.trans
  (BM.Φ-~ {⟦ w • v ⟧} {⟦ w ⟧ S.∙ ⟦ v ⟧}
    (S.~-reflexive {l = len (w • v)} {l' = len (w • v)}
      {M = ix (readM (w • v))} {M' = ix (readM w) ⊙ ix (readM v)}
      Eq.refl (λ x y → Eq.trans
        (Eq.cong (λ M → ix M x y) (readM-• w v))
        (ix-mul (readM w) (readM v) x y))))
  (BM.Φ-∙ ⟦ w ⟧ ⟦ v ⟧)
