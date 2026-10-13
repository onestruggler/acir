------------------------------------------------------------------------
-- Presentations of groups
--
-- Ordinary two-qubit gate matrices, independently of the auxiliary
-- encoding.  Matrices list columns in binary order 00, 01, 10, 11,
-- with wire 0 the least significant bit.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH.TwoQubit.Semantics where

open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Quantum.Synthesis.Matrix using (Matrix ; Matrix' ; _·*·_)
open import Word.Base using ([_]ʷ ; ε ; _•_)
open import Examples.Groups.CCX+HH.Syntactics
open import Examples.Groups.CCX+HH.Encoding using (e ; encode)
open import Examples.Groups.CCX+HH-TwoLevel.Ring
  using (D ; 0ᴰ ; 1ᴰ ; ½ᴰ ; -ᴰ_ ; _+ᴰ_ ; _*ᴰ_ ; SemiRingD ; RingD)
import Examples.Groups.CCX+HH-TwoLevel.Semantics as S
open S using (actV ; set₁ ; set₂)

X₀ X₁ CX₁₀ HH₀₁ : Matrix 4 4 D
X₀ = Matrix'
  ((0ᴰ ∷ 1ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ []) ∷
   (1ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ []) ∷
   (0ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ 1ᴰ ∷ []) ∷
   (0ᴰ ∷ 0ᴰ ∷ 1ᴰ ∷ 0ᴰ ∷ []) ∷ [])
X₁ = Matrix'
  ((0ᴰ ∷ 0ᴰ ∷ 1ᴰ ∷ 0ᴰ ∷ []) ∷
   (0ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ 1ᴰ ∷ []) ∷
   (1ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ []) ∷
   (0ᴰ ∷ 1ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ []) ∷ [])
CX₁₀ = Matrix'
  ((1ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ []) ∷
   (0ᴰ ∷ 1ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ []) ∷
   (0ᴰ ∷ 0ᴰ ∷ 0ᴰ ∷ 1ᴰ ∷ []) ∷
   (0ᴰ ∷ 0ᴰ ∷ 1ᴰ ∷ 0ᴰ ∷ []) ∷ [])
HH₀₁ = Matrix'
  ((½ᴰ ∷ ½ᴰ ∷ ½ᴰ ∷ ½ᴰ ∷ []) ∷
   (½ᴰ ∷ -ᴰ ½ᴰ ∷ ½ᴰ ∷ -ᴰ ½ᴰ ∷ []) ∷
   (½ᴰ ∷ ½ᴰ ∷ -ᴰ ½ᴰ ∷ -ᴰ ½ᴰ ∷ []) ∷
   (½ᴰ ∷ -ᴰ ½ᴰ ∷ -ᴰ ½ᴰ ∷ ½ᴰ ∷ []) ∷ [])

gate-matrix : Gen 2 → Matrix 4 4 D
gate-matrix (gate₀ ())
gate-matrix X-gen = X₀
gate-matrix CX-gen = CX₁₀
gate-matrix HH-gen = HH₀₁
gate-matrix ((gate₀ ()) ↥)
gate-matrix (X-gen ↥) = X₁
gate-matrix (((gate₀ ()) ↥) ↥)

⟦_⟧ : Circuit 2 → Matrix 4 4 D
⟦ [ g ]ʷ ⟧ = gate-matrix g
⟦ ε ⟧ = S.𝕀
⟦ u • v ⟧ = ⟦ u ⟧ ·*· ⟦ v ⟧

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  encoding-correct-gate : ∀ g → S.⟦ e g ⟧ᵐ ≡ gate-matrix g
  encoding-correct-gate (gate₀ ())
  encoding-correct-gate X-gen = refl
  encoding-correct-gate CX-gen = refl
  encoding-correct-gate HH-gen = refl
  encoding-correct-gate ((gate₀ ()) ↥)
  encoding-correct-gate (X-gen ↥) = refl
  encoding-correct-gate (((gate₀ ()) ↥) ↥)

encoding-correct : ∀ w → S.⟦ encode w ⟧ᵐ ≡ ⟦ w ⟧
encoding-correct [ g ]ʷ = encoding-correct-gate g
encoding-correct ε = refl
encoding-correct (u • v) = Eq.trans (S.⟦•⟧ᵐ (encode u) (encode v))
  (Eq.cong₂ _·*·_ (encoding-correct u) (encoding-correct v))
