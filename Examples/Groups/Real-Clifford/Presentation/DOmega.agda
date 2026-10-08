------------------------------------------------------------------------
-- Presentations of groups
--
-- R1–R16 present the real Clifford group inside U_{2ⁿ}(𝔻[ω])
--
-- Presentation at 𝔻[ω] = ℤ[1/√2,i], with s = 1/√2 = (ω − ω³)/2, which
-- complex conjugation fixes, into the unitary group that the other
-- developments over 𝔻[ω] use (Clifford+T-2qubit-TwoLevel.Semantics.U,
-- as in CNOT+Dihedral.Presentation): its carrier is the same type of
-- unitary matrices, and its operations agree on the matrices.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Presentation.DOmega where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Nat.Base using (ℕ ; _^_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Instances using (adj ; _+_ ; _*_ ; 0# ; 1#)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Definitions using (_IsSubPresentationOf_)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; adjᴰ ; √½ ; _≟ᴰ_ ; SemiRingD ; RingD ; AdjointD)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U ; √½-half)

open import Examples.Groups.Real-Clifford.Syntactics using (_VRel,_===_ ; grouplike)
import Examples.Groups.Real-Clifford.Presentation
import Examples.Groups.Real-Clifford.Semantics.Completeness
import Examples.Groups.Real-Clifford.Semantics.Interpretation
import Examples.Groups.Real-Clifford.Semantics.Matrix
import Examples.Groups.Real-Clifford.Semantics.Soundness

------------------------------------------------------------------------
-- 1/√2 is real, its square is ½, and 𝔻[ω] is nontrivial

opaque
  unfolding adjᴰ

  adj-√½ : adj √½ ≡ √½
  adj-√½ = refl

√½-sq : √½ * √½ + √½ * √½ ≡ 1#
√½-sq = Eq.subst (λ a → a * √½ + a * √½ ≡ 1#) adj-√½ √½-half

1≢0 : _≢_ {A = D} 1# 0#
1≢0 ()

------------------------------------------------------------------------
-- The presentation

private
  module P = Examples.Groups.Real-Clifford.Presentation {A = D} isCommutativeRing-D adj-D √½ √½-sq adj-√½ 1≢0
  module Sound = Examples.Groups.Real-Clifford.Semantics.Soundness {A = D} isCommutativeRing-D √½ √½-sq
  module Compl = Examples.Groups.Real-Clifford.Semantics.Completeness {A = D} isCommutativeRing-D √½ √½-sq 1≢0
  module Mat = Examples.Groups.Real-Clifford.Semantics.Matrix {A = D} isCommutativeRing-D adj-D
  module Int = Examples.Groups.Real-Clifford.Semantics.Interpretation {A = D} isCommutativeRing-D √½ √½-sq

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
