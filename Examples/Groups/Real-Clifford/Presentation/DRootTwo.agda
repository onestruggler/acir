------------------------------------------------------------------------
-- Presentations of groups
--
-- R1–R16 present the real Clifford group inside O_{2ⁿ}(ℤ[1/√2]), and
-- real Clifford circuits translate into two-level words
--
-- Presentation at 𝔻[√2] = ℤ[1/√2], with s = 1/√2 and the identity as
-- the involution, into the orthogonal group of Real-Clifford+CH-
-- TwoLevel (Semantics.O): its carrier is the same type of orthogonal
-- matrices, and its operations agree on the matrices.
--
-- That group is presented by the two-level generators Z_[a], X_[a,b],
-- H_[a,b] with the relations of Figure 6 of Fang, Heunen and
-- Kaarsgaard, or with Clément's (Real-Clifford+CH-TwoLevel-Clement.
-- Presentation).  So every real Clifford circuit on n qubits has a
-- two-level word on 2ⁿ indices with the same matrix (`translate`), and
-- two circuits are equal by R1–R16 exactly when their translations are
-- equal by Figure 6 (`translate-≈`), or by Clément's relations
-- (`translate-≈ᶜ`).
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Presentation.DRootTwo where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Nat.Base using (ℕ ; _^_)
open import Function.Bundles using (_⇔_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; _≢_ ; refl)

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Instances using (adj ; _+_ ; _*_ ; 0# ; 1#)
open import Word.Base using (Word)
import Presentation.Base as PB
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Translation as Translation

open import Examples.Groups.Real-Clifford+CH-TwoLevel.Ring
  using (D ; isCommutativeRing-D ; adj-D ; adjᴰ ; adjᴰ-id ; √½ ; SemiRingD ; RingD ; AdjointD)
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Semantics using (O ; √½-half ; ⟦_⟧ᵐ)
import Examples.Groups.Real-Clifford+CH-TwoLevel.Syntactics as TL
open import Examples.Groups.Real-Clifford+CH-TwoLevel.Clement using (_===ᶜ_)
import Examples.Groups.Real-Clifford+CH-TwoLevel-Clement.Presentation as TLP

open import Examples.Groups.Real-Clifford.Syntactics using (_VRel,_===_ ; Circuit ; grouplike)
import Examples.Groups.Real-Clifford.Presentation
import Examples.Groups.Real-Clifford.Semantics.Completeness
import Examples.Groups.Real-Clifford.Semantics.Interpretation
import Examples.Groups.Real-Clifford.Semantics.Matrix
import Examples.Groups.Real-Clifford.Semantics.Soundness

------------------------------------------------------------------------
-- 1/√2 is real, its square is ½, and 𝔻[√2] is nontrivial

adj-√½ : adj √½ ≡ √½
adj-√½ = adjᴰ-id √½

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

presentation : {n : ℕ} → (n VRel,_===_) IsSubPresentationOf O (2 ^ n)
presentation {n} = record
  { gl = grouplike
  ; ⟦_⟧ = P.⟦_⟧ᵘ
  ; mono = record
    { isGroupHomomorphism =
        isMonoidHomomorphism⇒isGroupHomomorphism GL.•-ε-group (O (2 ^ n)) isMonoidHomomorphism
    ; injective = λ {w} {v} e → Compl.completeness (Mat.mat-injective {M = Int.⟦ w ⟧ᴬ} {N = Int.⟦ v ⟧ᴬ} e)
    }
  }
  where
  module GL = Group-Lemmas (n VRel,_===_) grouplike
  open MonoidMorphisms (Group.rawMonoid GL.•-ε-group) (Group.rawMonoid (O (2 ^ n)))
  isMonoidHomomorphism : IsMonoidHomomorphism P.⟦_⟧ᵘ
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → Mat.mat-≐ (Sound.sound e) }
      ; homo = λ w v → Mat.mat-⊙ Int.⟦ w ⟧ᴬ Int.⟦ v ⟧ᴬ
      }
    ; ε-homo = Mat.mat-Id {n}
    }

------------------------------------------------------------------------
-- Real Clifford circuits as two-level words

module _ {n : ℕ} where

  private
    module T = Translation (presentation {n}) (TLP.presentation {2 ^ n})
    module Tᶜ = Translation (presentation {n}) (TLP.presentationᶜ {2 ^ n})

  -- A two-level word with the matrix of the circuit: the inverse of
  -- the output of Algorithm 1 on that matrix.
  translate : Circuit n → Word (TL.Gen (2 ^ n))
  translate = T.translate

  translate-correct : ∀ w → ⟦ translate w ⟧ᵐ ≡ Mat.mat Int.⟦ w ⟧ᴬ
  translate-correct = T.translate-correct

  -- Equal by R1–R16 exactly when equal by Figure 6, or by Clément's
  -- relations.
  translate-≈ : ∀ {u v} → PB._≈_ (n VRel,_===_) u v ⇔ PB._≈_ (TL._===_ {2 ^ n}) (translate u) (translate v)
  translate-≈ = T.translate-≈

  translate-≈ᶜ : ∀ {u v} → PB._≈_ (n VRel,_===_) u v ⇔ PB._≈_ (_===ᶜ_ {2 ^ n}) (translate u) (translate v)
  translate-≈ᶜ = Tᶜ.translate-≈

  -- And the translation is a group monomorphism.
  open T public using (translate-mono)
