------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian and Selinger's presentation of Uₙ(𝔻[i]), read in Uₙ(𝔻[ω])
--
-- 𝔻[i] = ℤ[½, i] is a subring of 𝔻[ω] = ℤ[1/√2, i]: x + yi is
-- yω² + x (EucDomain's cplx→ω), an injective ring homomorphism that
-- commutes with conjugation.  So Uₙ(𝔻[i]) is a subgroup of Uₙ(𝔻[ω])
-- (Embed), and the two-level relations, which present Uₙ(𝔻[i])
-- (Presentation), are a sub-presentation of Uₙ(𝔻[ω]): a word's matrix
-- over 𝔻[ω] is its matrix over 𝔻[i] with the entries included
-- (⟦⟧-matrix), and two words are equal by the relations exactly when
-- those matrices are equal (sound, complete).  Clifford+CS-3qubit reads
-- its group in U₈(𝔻[ω]) through Embed.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS-TwoLevel.DOmega where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (proj₁ ; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import Instances using (adj)
open import Quantum.Synthesis.Matrix using (matrix-map)
open import Quantum.Synthesis.Ring
  using (SemiRingDyadic ; RingDyadic ; AdjointDyadic ; SemiRingCplx ; RingCplx ; AdjointCplx)
open import Quantum.Synthesis.Ring.Properties using (isCommutativeRing-DComplex ; adj-DComplex)
import Quantum.Synthesis.Ring.Properties.Embedding as E

open import Word.Base using (Word)
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Clifford+CS-TwoLevel.Syntactics using (Gen ; _===_)
import Examples.Groups.Clifford+CS-TwoLevel.Ring as CSR
import Examples.Groups.Clifford+CS-TwoLevel.Semantics as S
import Examples.Groups.Clifford+CS-TwoLevel.Presentation as P
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring as Ω
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U ; UMat)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Subring as Subring

------------------------------------------------------------------------
-- 𝔻[i] in 𝔻[ω], with the (opaque) operations of Uₙ(𝔻[ω])

ι : CSR.D → Ω.D
ι = E.cplx→ω

opaque
  unfolding Ω._+ᴰ_ Ω._*ᴰ_ Ω.adjᴰ

  ι-+ : ∀ x y → ι (x CSR.DR.+ y) ≡ ι x Ω.DR.+ ι y
  ι-+ = E.At-𝔻.cplx→ω-+

  ι-* : ∀ x y → ι (x CSR.DR.* y) ≡ ι x Ω.DR.* ι y
  ι-* = E.At-𝔻.cplx→ω-*

  ι-adj : ∀ x → ι (adj x) ≡ Ω.adjᴰ (ι x)
  ι-adj = E.At-𝔻.cplx→ω-adj

-- Matrices over 𝔻[i] as matrices over 𝔻[ω].
module Emb = Subring {A = CSR.D} isCommutativeRing-DComplex adj-DComplex
               ι ι-+ ι-* refl refl ι-adj E.cplx→ω-injective

------------------------------------------------------------------------
-- Uₙ(𝔻[i]) in Uₙ(𝔻[ω])

module Embed (n : ℕ) =
  Emb.Group-Embedding (S.U n) n proj₁ proj₂ (λ e → e) (λ e → e) (λ _ _ → refl) refl

------------------------------------------------------------------------
-- The presentation, read in Uₙ(𝔻[ω])

module _ {n : ℕ} where

  presentation : (_===_ {n}) IsSubPresentationOf U n
  presentation = Embed.along-presentation n (P.presentation {n})

  open PE.Sub presentation public using (⟦_⟧ ; sound ; complete)

  -- A word's matrix over 𝔻[ω] is its matrix over 𝔻[i], included.
  ⟦⟧-matrix : (w : Word (Gen n)) → proj₁ ⟦ w ⟧ ≡ matrix-map ι S.⟦ w ⟧ᵐ
  ⟦⟧-matrix w = refl
