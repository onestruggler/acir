------------------------------------------------------------------------
-- Presentations of groups
--
-- Blake (2026): the main theorems, for MainTheorems
--
-- The four levels — affine circuits, then phases, then S (p odd), then
-- T (p > 3) — each present the group their circuits generate in
-- U_{pⁿ}, over any commutative ring A with an involution and an
-- injective character of 𝔽_p: Theorem 1 (Presentation.Aff) and its
-- three extensions (.Lin, .Quad, .Cube).  This module collects what
-- MainTheorems states, behind one import: the group, matrix equality
-- _≈ᴬ_, and for each level a module (Affine, Linear-Phase, Quadratic,
-- Cubic) with the circuits, the relations at each width
-- (_CRel,_===_), a circuit's matrix ⟦_⟧, derivability ⊢_≈_, the
-- sub-presentation, and its completeness and soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Algebra.Structures using (IsCommutativeRing)
open import Data.Nat.Base using (ℕ ; _≤_ ; _^_)
open import Data.Nat.Primality using (Prime)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Instances using (Ring ; Adjoint ; adj ; _+_ ; _*_ ; -_ ; 0# ; 1#)
open import Notations using (₂₊)
open import Quantum.Synthesis.Ring.Properties.Hom using (IsInvolutiveRingEndo)
import Examples.Groups.Qupit-Phase-Affine.Field as Field

module Examples.Groups.Qupit-Phase-Affine.MainTheorem
  (p-2 : ℕ) (p-prime : Prime (₂₊ p-2))
  {A : Set} {{RA : Ring A}} {{AA : Adjoint A}}
  (isCR : IsCommutativeRing (_≡_ {A = A}) _+_ _*_ -_ 0# 1#)
  (adjI : IsInvolutiveRingEndo {A} adj)
  (phase : Field.F p-2 p-prime → A)
  (phase-+ : ∀ a b → phase (Field._+_ p-2 p-prime a b) ≡ phase a * phase b)
  (phase-unit : ∀ a → adj (phase a) * phase a ≡ 1#)
  (phase-injective : ∀ a b → phase a ≡ phase b → a ≡ b)
  where

open import Algebra.Bundles using (Group)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsSubPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Qupit-Phase-Affine.Semantics p-2 p-prime public using (p)
open import Examples.Groups.Qupit-Phase-Affine.Matrix p-2 p-prime isCR adjI phase phase-+ phase-unit phase-injective public
  using (U)

-- Matrices in U_N over A, equal when their entries are.
infix 4 _≈ᴬ_
_≈ᴬ_ : ∀ {N} → Group.Carrier (U N) → Group.Carrier (U N) → Set
_≈ᴬ_ {N} = Group._≈_ (U N)

------------------------------------------------------------------------
-- Level 0: affine circuits (Theorem 1)

module Affine where

  open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 0 public
    using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
  import Examples.Groups.Qupit-Phase-Affine.Presentation.Aff p-2 p-prime isCR adjI phase phase-+ phase-unit phase-injective as Aff

  infix 4 ⊢_≈_
  ⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
  ⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

  presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (p ^ n)
  presentation n = Aff.presentation {n}

  ⟦_⟧ : ∀ {n} → Circuit n → Group.Carrier (U (p ^ n))
  ⟦_⟧ {n} = PE.Sub.⟦_⟧ (presentation n)

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → ⊢ w ≈ v
  complete {n} = PE.Sub.complete (presentation n)

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
  sound {n} = PE.Sub.sound (presentation n)

------------------------------------------------------------------------
-- Level 1: with phases

module Linear-Phase where

  open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 1 public
    using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
  import Examples.Groups.Qupit-Phase-Affine.Presentation.Lin p-2 p-prime isCR adjI phase phase-+ phase-unit phase-injective as Lin

  infix 4 ⊢_≈_
  ⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
  ⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

  presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (p ^ n)
  presentation n = Lin.presentation {n}

  ⟦_⟧ : ∀ {n} → Circuit n → Group.Carrier (U (p ^ n))
  ⟦_⟧ {n} = PE.Sub.⟦_⟧ (presentation n)

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → ⊢ w ≈ v
  complete {n} = PE.Sub.complete (presentation n)

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
  sound {n} = PE.Sub.sound (presentation n)

------------------------------------------------------------------------
-- Level 2: with S, for p odd

module Quadratic (odd : 1 ≤ p-2) where

  open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 2 public
    using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
  import Examples.Groups.Qupit-Phase-Affine.Presentation.Quad p-2 p-prime odd isCR adjI phase phase-+ phase-unit phase-injective as Quad

  infix 4 ⊢_≈_
  ⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
  ⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

  presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (p ^ n)
  presentation n = Quad.presentation {n}

  ⟦_⟧ : ∀ {n} → Circuit n → Group.Carrier (U (p ^ n))
  ⟦_⟧ {n} = PE.Sub.⟦_⟧ (presentation n)

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → ⊢ w ≈ v
  complete {n} = PE.Sub.complete (presentation n)

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
  sound {n} = PE.Sub.sound (presentation n)

------------------------------------------------------------------------
-- Level 3: with T, for p > 3

module Cubic (gt3 : 2 ≤ p-2) where

  open import Examples.Groups.Qupit-Phase-Affine.Syntactics p-2 p-prime 3 public
    using (Circuit) renaming (_VRel,_===_ to _CRel,_===_)
  import Examples.Groups.Qupit-Phase-Affine.Presentation.Cube p-2 p-prime gt3 isCR adjI phase phase-+ phase-unit phase-injective as Cube

  infix 4 ⊢_≈_
  ⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
  ⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

  presentation : ∀ n → (n CRel,_===_) IsSubPresentationOf U (p ^ n)
  presentation n = Cube.presentation {n}

  ⟦_⟧ : ∀ {n} → Circuit n → Group.Carrier (U (p ^ n))
  ⟦_⟧ {n} = PE.Sub.⟦_⟧ (presentation n)

  complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧ → ⊢ w ≈ v
  complete {n} = PE.Sub.complete (presentation n)

  sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
  sound {n} = PE.Sub.sound (presentation n)
