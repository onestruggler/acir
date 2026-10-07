------------------------------------------------------------------------
-- Presentations of groups
--
-- The main theorem of Amy, Chen and Ross, "A finite presentation of
-- CNOT-dihedral operators" (arXiv:1701.00140): the relations of
-- Syntactics present the group of n-qubit CNOT-dihedral operators.
--
-- A circuit denotes a unitary 2ⁿ × 2ⁿ matrix over 𝔻[ω] (Matrix), a
-- monomial matrix with entries powers of ω.  Then
--
-- * sound: related circuits have the same operator (Soundness), hence
--   the same matrix;
-- * complete: circuits with the same matrix have the same operator
--   (Matrix.mat-injective), hence are related (Completeness);
--
-- so the relations present the subgroup of U_{2ⁿ}(𝔻[ω]) that the gates
-- ω, X, T, CNOT and SWAP generate.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CNOT+Dihedral.Presentation where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Nat using (ℕ ; _^_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Definitions using (_IsSubPresentationOf_)
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (U)

open import Examples.Groups.CNOT+Dihedral.Syntactics using (_VRel,_===_ ; grouplike)
open import Examples.Groups.CNOT+Dihedral.Interpretation using (⟦_⟧ ; ⟦⟧-• ; ⟦⟧-ε)
open import Examples.Groups.CNOT+Dihedral.Soundness using (sound)
open import Examples.Groups.CNOT+Dihedral.Completeness using (complete)
open import Examples.Groups.CNOT+Dihedral.Matrix
  using (⟦_⟧ᵘ ; mat-≐ ; mat-⊙ ; mat-Id ; mat-injective)

------------------------------------------------------------------------
-- The presentation

-- ⟦_⟧ᵘ is a group monomorphism from the circuits modulo the relations
-- to U_{2ⁿ}(𝔻[ω]).
presentation : {n : ℕ} → (n VRel,_===_) IsSubPresentationOf U (2 ^ n)
presentation {n} = record
  { gl = grouplike
  ; ⟦_⟧ = ⟦_⟧ᵘ
  ; mono = record
    { isGroupHomomorphism =
        isMonoidHomomorphism⇒isGroupHomomorphism GL.•-ε-group (U (2 ^ n)) isMonoidHomomorphism
    ; injective = λ {w} {v} e → complete (mat-injective {M = ⟦ w ⟧} {N = ⟦ v ⟧} e)
    }
  }
  where
  module GL = Group-Lemmas (n VRel,_===_) grouplike
  open MonoidMorphisms (Group.rawMonoid GL.•-ε-group) (Group.rawMonoid (U (2 ^ n)))
  isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧ᵘ
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → mat-≐ (sound e) }
      ; homo = λ w v → Eq.trans (mat-≐ (⟦⟧-• w v)) (mat-⊙ ⟦ w ⟧ ⟦ v ⟧)
      }
    ; ε-homo = Eq.trans (mat-≐ (⟦⟧-ε {n})) (mat-Id {n})
    }
