------------------------------------------------------------------------
-- Presentations of groups
--
-- Bian et al. (2026): the main theorem, for MainTheorems
--
-- The gates −ω, H, S, CZ and the rules C0–C15 of Figure 1 present the
-- qudit Clifford group at every width, for an odd prime p: the paper's
-- Theorem 4.10 (Figure1.Presentation), against the algebraic model, the
-- central extension of Pauli ⋊ Sp(2n, ℤ/pℤ) by ⟨ω⟩ (the Weyl cocycle)
-- times ⟨−1⟩.  The rules name a primitive root g of ℤ/pℤ.  This module
-- collects what MainTheorems states, behind one import: the circuits,
-- the rules at each width (_CRel,_===_), the group, a circuit's value
-- ⟦_⟧ in it and their equality _≈ᶜ_, derivability ⊢_≈_, the
-- presentation, and its completeness and soundness for ⟦_⟧.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

open import Data.Fin.Base using (toℕ)
open import Data.Nat.Base using (ℕ ; 2+)
open import Data.Nat.Primality using (Prime)
open import Data.Product.Base using (_,_ ; ∃)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Notations using (₁₊)
open import ForStdlib.Data.Fin.Mod using (ℤ ; ℤ* ; _^′_)
open import ForStdlib.Data.Fin.Mod.Prime.Fermat using (module PrimeModulus')

module Examples.Groups.Clifford+MinusOne.Qupit.MainTheorem
  (p-3 : ℕ)
  (let p-2 = ₁₊ p-3)
  (p-prime : Prime (2+ p-2))
  (let open PrimeModulus' p-2 p-prime)
  (g*@(g , g≠0) : ℤ* ₚ)
  (g-gen : ∀ ((x , _) : ℤ* ₚ) → ∃ λ (k : ℤ ₚ-₁) → x ≡ g ^′ toℕ k)
  where

open import Algebra.Bundles using (Group)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)
import Presentation.Embedding as PE

open import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Syntactics p-3 p-prime g* g-gen public
  using (Circuit) renaming (_F,_===_ to _CRel,_===_)
open import Examples.Groups.Clifford+MinusOne.Qupit.Semantics p-3 p-prime g* g-gen public
  using (Clifford±)
import Examples.Groups.Clifford+MinusOne.Qupit.Figure1.Presentation p-3 p-prime g* g-gen as P

-- Equality by the rules.
infix 4 ⊢_≈_
⊢_≈_ : ∀ {n} → Circuit n → Circuit n → Set
⊢_≈_ {n} = PB._≈_ (n CRel,_===_)

-- Equality in the model.
infix 4 _≈ᶜ_
_≈ᶜ_ : ∀ {n} → Group.Carrier (Clifford± n) → Group.Carrier (Clifford± n) → Set
_≈ᶜ_ {n} = Group._≈_ (Clifford± n)

------------------------------------------------------------------------
-- The theorem

presentation : ∀ n → (n CRel,_===_) IsPresentationOf (Clifford± n)
presentation = P.presentation-Figure1

-- A circuit's value in the model.
⟦_⟧ : ∀ {n} → Circuit n → Group.Carrier (Clifford± n)
⟦_⟧ {n} = PE.Pres.⟦_⟧ (presentation n)

complete : ∀ {n} {w v : Circuit n} → ⟦ w ⟧ ≈ᶜ ⟦ v ⟧ → ⊢ w ≈ v
complete {n} = PE.Pres.complete (presentation n)

sound : ∀ {n} {w v : Circuit n} → ⊢ w ≈ v → ⟦ w ⟧ ≈ᶜ ⟦ v ⟧
sound {n} = PE.Pres.sound (presentation n)
