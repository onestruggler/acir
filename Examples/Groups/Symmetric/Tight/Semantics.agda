------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the symmetric group: bijections on Fin n via
-- Data.Fin.Permutation.Permutation′.
-- Re-exports the group structure on Permutation′ n (whose generic
-- definition lives in ForStdlib.Data.Fin.Permutation.Properties).
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat using (ℕ ; zero ; suc)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Permutation
  using ( Permutation′ ; permutation ; _⟨$⟩ʳ_ ; _∘ₚ_
        ; lift₀ ; lift₀-id ; lift₀-comp )
  renaming (id to idP)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; cong ; sym ; trans)

open import Word.Base
open import Notations

module Examples.Groups.Symmetric.Tight.Semantics where

open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Permutation type

Perm : ℕ → Set
Perm n = Permutation′ n

------------------------------------------------------------------------
-- Semantic building blocks

-- The underlying function for swap01 (used to build the Permutation′).
private
  swap01-fun : ∀ {n} → Fin (₂₊ n) → Fin (₂₊ n)
  swap01-fun zero      = ₁₊ zero
  swap01-fun (₁₊ zero) = zero
  swap01-fun (₂₊ k)    = ₂₊ k

-- Swap positions 0 and 1: the denotation of σ-gate.
swap01 : ∀ {n} → Perm (₂₊ n)
swap01 = permutation swap01-fun swap01-fun
  (λ { zero → refl ; (₁₊ zero) → refl ; (₂₊ _) → refl })
  (λ { zero → refl ; (₁₊ zero) → refl ; (₂₊ _) → refl })

-- Shift a permutation up by one wire: the action of _↥.
shift : ∀ {n} → Perm n → Perm (₁₊ n)
shift = lift₀

------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : ∀ {n} → Gen n → Perm n
⟦ gate₁ () ⟧ᵍ
⟦ gate₂ σ-gate ⟧ᵍ = swap01
⟦ g ↥ ⟧ᵍ          = shift ⟦ g ⟧ᵍ

-- Words are read left-to-right: w • v applies w first, then v.
⟦_⟧ : ∀ {n} → Word (Gen n) → Perm n
⟦ ε ⟧      = idP
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
⟦ w • v ⟧  = ⟦ w ⟧ ∘ₚ ⟦ v ⟧

------------------------------------------------------------------------
-- Lemmas about shift (= lift₀)

-- ⟦ w ↑ ⟧ agrees with shift ⟦ w ⟧ pointwise.
⟦↑⟧ : ∀ {n} (w : Word (Gen n)) (k : Fin (₁₊ n))
     → ⟦ w ↑ ⟧ ⟨$⟩ʳ k ≡ shift ⟦ w ⟧ ⟨$⟩ʳ k
⟦↑⟧ ε       k = Eq.sym (lift₀-id k)
⟦↑⟧ [ g ]ʷ  k = refl
⟦↑⟧ (w • v) k =
  Eq.trans (Eq.cong (⟦ v ↑ ⟧ ⟨$⟩ʳ_) (⟦↑⟧ w k))
  (Eq.trans (⟦↑⟧ v _) (lift₀-comp ⟦ w ⟧ ⟦ v ⟧ k))

------------------------------------------------------------------------
-- Group structure on Permutation′ n

-- The symmetric group Sₙ is a generic carrier: its construction lives
-- in the standard-library supplement (under the idiomatic name
-- ∘ₚ-id-group).  Re-exported here as Permutation′-group so that the
-- tight semantics keeps a single, readable home for "the meaning of
-- the syntax".
open import ForStdlib.Data.Fin.Permutation.Properties
  using () renaming (∘ₚ-id-group to Permutation′-group) public
