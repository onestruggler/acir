------------------------------------------------------------------------
-- Presentations of groups
--
-- C1–C15 present the Clifford group inside U_{2ⁿ}(𝔻[ω])
--
-- Presentation at 𝔻[ω] = ℤ[1/√2,i], with s = 1/√2 = (ω − ω³)/2, which
-- complex conjugation fixes, and i = ω², which it negates, into the
-- unitary group that the other developments over 𝔻[ω] use
-- (Clifford+T-2qubit-TwoLevel.Semantics.U); and the order of the
-- Clifford group there (Corollary 5.6).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Presentation.DOmega where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Fin.Base using (Fin)
open import Data.Nat.Base using (ℕ ; _^_)
open import Function.Bundles using (Inverse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Instances using (adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Definitions using (_IsSubPresentationOf_)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; adjᴰ ; _*ᴰ_ ; -ᴰ_ ; ωᴰ ; √½ ; SemiRingD ; RingD ; AdjointD)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U ; √½-half)

open import Examples.Groups.Qubit-Clifford.Syntactics using (_VRel,_===_ ; grouplike)
open import Examples.Groups.Qubit-Clifford.Count using (order)
import Examples.Groups.Qubit-Clifford.Presentation
import Examples.Groups.Qubit-Clifford.Semantics.Completeness
import Examples.Groups.Qubit-Clifford.Semantics.Interpretation
import Examples.Groups.Qubit-Clifford.Semantics.Order
import Examples.Groups.Qubit-Clifford.Semantics.Soundness
import Examples.Groups.Real-Clifford.Semantics.Matrix

------------------------------------------------------------------------
-- 1/√2 is real, its square is ½, i = ω² squares to −1 and is
-- imaginary, and 𝔻[ω] is nontrivial

iᴰ : D
iᴰ = ωᴰ * ωᴰ

opaque
  unfolding adjᴰ

  adj-√½ : adj √½ ≡ √½
  adj-√½ = refl

opaque
  unfolding _*ᴰ_ -ᴰ_

  iᴰ² : iᴰ * iᴰ ≡ - 1#
  iᴰ² = refl

opaque
  unfolding _*ᴰ_ -ᴰ_ adjᴰ

  adj-iᴰ : adj iᴰ ≡ - iᴰ
  adj-iᴰ = refl

√½-sq : √½ * √½ + √½ * √½ ≡ 1#
√½-sq = Eq.subst (λ a → a * √½ + a * √½ ≡ 1#) adj-√½ √½-half

1≢0 : _≢_ {A = D} 1# 0#
1≢0 ()

------------------------------------------------------------------------
-- The presentation

private
  module P = Examples.Groups.Qubit-Clifford.Presentation {A = D}
    isCommutativeRing-D adj-D √½ √½-sq adj-√½ iᴰ iᴰ² adj-iᴰ 1≢0
  module Sound = Examples.Groups.Qubit-Clifford.Semantics.Soundness {A = D} isCommutativeRing-D √½ √½-sq iᴰ iᴰ²
  module Compl = Examples.Groups.Qubit-Clifford.Semantics.Completeness {A = D}
    isCommutativeRing-D √½ √½-sq iᴰ iᴰ² 1≢0
  module Mat = Examples.Groups.Real-Clifford.Semantics.Matrix {A = D} isCommutativeRing-D adj-D
  module Int = Examples.Groups.Qubit-Clifford.Semantics.Interpretation {A = D} isCommutativeRing-D √½ √½-sq iᴰ iᴰ²
  module Ord = Examples.Groups.Qubit-Clifford.Semantics.Order {A = D} isCommutativeRing-D √½ √½-sq iᴰ iᴰ² 1≢0

presentation : {n : ℕ} → (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
presentation {n} = record
  { gl = grouplike
  ; ⟦_⟧ = P.⟦_⟧ᵘ
  ; mono = record
    { isGroupHomomorphism =
        isMonoidHomomorphism⇒isGroupHomomorphism GL.•-ε-group (U (2 ^ n)) isMonoidHomomorphism
    ; injective = λ {w} {v} e → Compl.completeness (Mat.mat-injective {M = Int.⟦ w ⟧ᴬ} {N = Int.⟦ v ⟧ᴬ} e)
    }
  }
  where
  module GL = Group-Lemmas (n VRel,_===_) grouplike
  open MonoidMorphisms (Group.rawMonoid GL.•-ε-group) (Group.rawMonoid (U (2 ^ n)))
  isMonoidHomomorphism : IsMonoidHomomorphism P.⟦_⟧ᵘ
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → Mat.mat-≐ (Sound.sound e) }
      ; homo = λ w v → Mat.mat-⊙ Int.⟦ w ⟧ᴬ Int.⟦ v ⟧ᴬ
      }
    ; ε-homo = Mat.mat-Id {n}
    }

-- There are exactly 8 · ∏ᵢ₌₁ⁿ 2 (4ⁱ − 1) 4ⁱ Clifford operators on n
-- qubits.
corollary-5-6 : {n : ℕ} → Inverse (Ord.Clifford-setoid n) (Eq.setoid (Fin (order n)))
corollary-5-6 = Ord.corollary-5-6
