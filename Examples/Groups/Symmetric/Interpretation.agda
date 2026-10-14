------------------------------------------------------------------------
-- Presentations of groups
--
-- The interpretation of circuits as permutations: ⟦_⟧ : Circuit n →
-- Perm n.
--
-- A generator denotes a permutation (⟦_⟧ᵍ) and a word denotes the
-- composite, read left to right, which is what StarInterp's Extend
-- builds out of the target monoid.  ⟦↑⟧ is the one computation law the
-- rest of the development needs: shifting a circuit shifts its
-- denotation.
--
-- This says nothing about the RELATIONS.  That ⟦_⟧ respects them --
-- that congruent circuits denote the same permutation -- is Soundness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Symmetric.Interpretation where

open import Algebra.Bundles using (Group)
open import Data.Fin using (Fin ; zero ; suc ; inject₁ ; fromℕ)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_ ; lift₀-id ; lift₀-comp)
open import Notations using (₁₊ ; ₂₊)
open import Word.Base using (Word ; ε ; [_]ʷ ; _•_)

import Relation.Binary.PropositionalEquality as Eq

open Eq using (_≡_ ; refl)

open import Examples.Groups.Symmetric.Semantics
open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : ∀ {n} → Gen n → Perm n
⟦ gate₂ σ-gate ⟧ᵍ = swap01
⟦ g ↥ ⟧ᵍ          = shift ⟦ g ⟧ᵍ

-- Words are read left-to-right: w • v applies w first, then v.
⟦_⟧ : ∀ {n} → Word (Gen n) → Perm n
⟦_⟧ {n} = E.⟦_⟧
  where
  open import Normalization.StarInterp (n VRel,_===_)
  module E = Extend (Group.monoid (Permutation′-group n)) ⟦_⟧ᵍ

------------------------------------------------------------------------
-- Lemmas about shift (= lift₀)

-- ⟦ w ↑ ⟧ agrees with shift ⟦ w ⟧ pointwise.
⟦↑⟧ : ∀ {n} (w : Word (Gen n)) (k : Fin (₁₊ n)) →
      ⟦ w ↑ ⟧ ⟨$⟩ʳ k ≡ shift ⟦ w ⟧ ⟨$⟩ʳ k
⟦↑⟧ ε       k = Eq.sym (lift₀-id k)
⟦↑⟧ [ g ]ʷ  k = refl
⟦↑⟧ (w • v) k =
  Eq.trans (Eq.cong (⟦ v ↑ ⟧ ⟨$⟩ʳ_) (⟦↑⟧ w k))
  (Eq.trans (⟦↑⟧ v _) (lift₀-comp ⟦ w ⟧ ⟦ v ⟧ k))

------------------------------------------------------------------------
-- An idle wire on top

-- ⟦ w ⇓ ⟧ acts as ⟦ w ⟧ on the wires below the new one ...
⟦⇓⟧ᵍ : ∀ {n} (g : Gen n) (k : Fin n) →
       ⟦ g ↧ ⟧ᵍ ⟨$⟩ʳ inject₁ k ≡ inject₁ (⟦ g ⟧ᵍ ⟨$⟩ʳ k)
⟦⇓⟧ᵍ (gate₂ σ-gate) zero      = refl
⟦⇓⟧ᵍ (gate₂ σ-gate) (₁₊ zero) = refl
⟦⇓⟧ᵍ (gate₂ σ-gate) (₂₊ k)    = refl
⟦⇓⟧ᵍ (g ↥)          zero      = refl
⟦⇓⟧ᵍ (g ↥)          (suc k)   = Eq.cong suc (⟦⇓⟧ᵍ g k)

⟦⇓⟧ : ∀ {n} (w : Word (Gen n)) (k : Fin n) →
      ⟦ w ⇓ ⟧ ⟨$⟩ʳ inject₁ k ≡ inject₁ (⟦ w ⟧ ⟨$⟩ʳ k)
⟦⇓⟧ ε       k = refl
⟦⇓⟧ [ g ]ʷ  k = ⟦⇓⟧ᵍ g k
⟦⇓⟧ (w • v) k = Eq.trans (Eq.cong (⟦ v ⇓ ⟧ ⟨$⟩ʳ_) (⟦⇓⟧ w k)) (⟦⇓⟧ v _)

-- ... and fixes it.
⟦⇓⟧ᵍ-top : ∀ {n} (g : Gen n) → ⟦ g ↧ ⟧ᵍ ⟨$⟩ʳ fromℕ n ≡ fromℕ n
⟦⇓⟧ᵍ-top (gate₂ σ-gate) = refl
⟦⇓⟧ᵍ-top (g ↥)          = Eq.cong suc (⟦⇓⟧ᵍ-top g)

⟦⇓⟧-top : ∀ {n} (w : Word (Gen n)) → ⟦ w ⇓ ⟧ ⟨$⟩ʳ fromℕ n ≡ fromℕ n
⟦⇓⟧-top ε       = refl
⟦⇓⟧-top [ g ]ʷ  = ⟦⇓⟧ᵍ-top g
⟦⇓⟧-top (w • v) =
  Eq.trans (Eq.cong (⟦ v ⇓ ⟧ ⟨$⟩ʳ_) (⟦⇓⟧-top w)) (⟦⇓⟧-top v)
