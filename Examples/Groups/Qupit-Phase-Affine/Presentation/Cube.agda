------------------------------------------------------------------------
-- Presentations of groups
--
-- CubicPhase_d presents its group (p > 3)
--
-- Over any coefficient ring A with a primitive p-th root of unity (see
-- Matrix), a circuit of CubicPhase_d on n wires denotes a unitary
-- pⁿ × pⁿ matrix, monomial with entries powers of the root: an affine
-- map of F_pⁿ and a phase of degree at most 3.  Then
--
-- * sound: related circuits have the same operator (Soundness, which
--   needs p > 3 at level 3), hence the same matrix;
-- * complete: circuits with the same matrix have the same operator
--   (Matrix.mat-injective), hence are related (Completeness.Cube);
--
-- so the rules of CubicPhase_d present the subgroup of U_{pⁿ}(A) that
-- ω, X, Z, S, T, the multipliers, CX and SWAP generate.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Nat.Base using (ℕ ; _≤_)
open import Data.Nat.Primality using (Prime)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)
open import Notations using (₂₊)

import Examples.Groups.Qupit-Phase-Affine.Field as Field

module Examples.Groups.Qupit-Phase-Affine.Presentation.Cube
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2)) (gt3 : 2 ≤ p-2)
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (phase : Field.F p-2 p-prime → A)
  (phase-+ : ∀ a b → phase (Field._+_ p-2 p-prime a b) ≡ phase a * phase b)
  (phase-unit : ∀ a → adj (phase a) * phase a ≡ 1#)
  (phase-injective : ∀ a b → phase a ≡ phase b → a ≡ b)
  where

open import Algebra.Bundles using (Group)
open import Algebra.Morphism.Structures using (module MonoidMorphisms)
open import Data.Nat.Base using (_^_)
open import Data.Product.Base using (_,_)
import Relation.Binary.PropositionalEquality as Eq

open import ForStdlib.Algebra.Morphism.Consequences using (isMonoidHomomorphism⇒isGroupHomomorphism)
open import Presentation.GroupLike using (module Group-Lemmas)
open import Presentation.Definitions using (_IsSubPresentationOf_)

import Examples.Groups.Qupit-Phase-Affine.Semantics as Sem
open Sem p-2 p-prime using (p ; ≐-trans ; ≐-sym)
open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 3 using (Circuit ; _VRel,_===_)
open import Examples.Groups.Qupit-Phase-Affine.Interpretation p-2 p-prime 3 using (⟦_⟧ ; ⟦⟧-• ; ⟦⟧-ε)
open import Examples.Groups.Qupit-Phase-Affine.Basic p-2 p-prime 3 using (grouplike ; module Inv ; _⁻¹)
open import Examples.Groups.Qupit-Phase-Affine.Completeness.Cube p-2 p-prime gt3 using (adm ; completeness)
open import Examples.Groups.Qupit-Phase-Affine.Evaluation p-2 p-prime 3 adm using (sound)
open import Examples.Groups.Qupit-Phase-Affine.Matrix p-2 p-prime isCR adjI phase phase-+ phase-unit phase-injective
  using (UMat ; U ; mat ; mat-≐ ; mat-⊙ ; mat-Id ; mat-injective ; Unitary-mat)

------------------------------------------------------------------------
-- The matrix of a circuit

-- It is unitary, its inverse being the matrix of the inverse circuit.
⟦_⟧ᵘ : {n : ℕ} → Circuit n → UMat (p ^ n)
⟦_⟧ᵘ {n} w = mat ⟦ w ⟧ , Unitary-mat ⟦ w ⟧ ⟦ w ⁻¹ ⟧
  (≐-trans (≐-sym (⟦⟧-• (w ⁻¹) w)) (≐-trans (sound (Inv.inverseˡ n {w})) ⟦⟧-ε))
  (≐-trans (≐-sym (⟦⟧-• w (w ⁻¹))) (≐-trans (sound (Inv.inverseʳ n {w})) ⟦⟧-ε))

------------------------------------------------------------------------
-- The presentation

-- ⟦_⟧ᵘ is a group monomorphism from the circuits modulo the rules of
-- CubicPhase_d to U_{pⁿ}(A).
presentation : {n : ℕ} → (n VRel,_===_) IsSubPresentationOf U (p ^ n)
presentation {n} = record
  { gl = grouplike
  ; ⟦_⟧ = ⟦_⟧ᵘ
  ; mono = record
    { isGroupHomomorphism =
        isMonoidHomomorphism⇒isGroupHomomorphism GL.•-ε-group (U (p ^ n)) isMonoidHomomorphism
    ; injective = λ {w} {v} e → completeness n (mat-injective {M = ⟦ w ⟧} {N = ⟦ v ⟧} e)
    }
  }
  where
  module GL = Group-Lemmas (n VRel,_===_) grouplike
  open MonoidMorphisms (Group.rawMonoid GL.•-ε-group) (Group.rawMonoid (U (p ^ n)))
  isMonoidHomomorphism : IsMonoidHomomorphism ⟦_⟧ᵘ
  isMonoidHomomorphism = record
    { isMagmaHomomorphism = record
      { isRelHomomorphism = record { cong = λ e → mat-≐ (sound e) }
      ; homo = λ w v → Eq.trans (mat-≐ (⟦⟧-• w v)) (mat-⊙ ⟦ w ⟧ ⟦ v ⟧)
      }
    ; ε-homo = Eq.trans (mat-≐ (⟦⟧-ε {n})) (mat-Id {n})
    }
