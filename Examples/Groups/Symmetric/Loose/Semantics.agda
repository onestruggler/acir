------------------------------------------------------------------------
-- Presentations of groups
--
-- Semantics of the symmetric group: permutations of Fin n.
------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ ; zero ; suc)
open import Function using (_∘_ ; id)
open import Relation.Binary.Bundles using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl ; _≗_)

open import Notations using (₁₊ ; ₂₊)
open import Word.Base using (Word ; ε ; [_]ʷ ; _•_)

module Examples.Groups.Symmetric.Loose.Semantics where

open import Examples.Groups.Symmetric.Syntactics

------------------------------------------------------------------------
-- Endofunctions on Fin n

-- Endofunctions on Fin n: the loose semantic domain.
Endo : ℕ → Set
Endo n = Fin n → Fin n

-- Endofunctions up to pointwise propositional equality.
Endo-setoid : ℕ → Setoid _ _
Endo-setoid n = record
  { Carrier       = Endo n
  ; _≈_           = _≗_
  ; isEquivalence = record
    { refl  = λ _   → refl
    ; sym   = λ p k → Eq.sym (p k)
    ; trans = λ p q k → Eq.trans (p k) (q k)
    }
  }

------------------------------------------------------------------------
-- Semantic building blocks

-- Swap positions 0 and 1: the denotation of σ-gate.
swap01 : ∀ {n} → Endo (₂₊ n)
swap01 zero      = ₁₊ zero
swap01 (₁₊ zero) = zero
swap01 (₂₊ k)    = ₂₊ k

-- Shift a permutation up by one wire: the action of _↥.
shift : ∀ {n} → Endo n → Endo (₁₊ n)
shift f zero   = zero
shift f (₁₊ k) = suc (f k)

------------------------------------------------------------------------
-- Denotation of generators and words

-- Denotation of a single generator.
⟦_⟧ᵍ : ∀ {n} → Gen n → Endo n
⟦ gate₁ () ⟧ᵍ
⟦ gate₂ σ-gate ⟧ᵍ = swap01
⟦ g ↥ ⟧ᵍ          = shift ⟦ g ⟧ᵍ

-- Words are read left-to-right: w • v applies w first, then v.
⟦_⟧ : ∀ {n} → Word (Gen n) → Endo n
⟦ ε ⟧      = id
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
⟦ w • v ⟧  = ⟦ v ⟧ ∘ ⟦ w ⟧

------------------------------------------------------------------------
-- Lemmas about shift

-- shift preserves the identity.
shift-id : ∀ {n} (k : Fin (₁₊ n)) → shift id k ≡ k
shift-id zero   = refl
shift-id (₁₊ k) = refl

-- shift distributes over composition.
shift-hom : ∀ {n} (f g : Endo n) (k : Fin (₁₊ n))
          → shift (f ∘ g) k ≡ (shift f ∘ shift g) k
shift-hom f g zero   = refl
shift-hom f g (₁₊ k) = refl

-- shift respects pointwise equality.
shift-cong : ∀ {n} {f g : Endo n} → f ≗ g → shift f ≗ shift g
shift-cong eq zero   = refl
shift-cong eq (₁₊ k) = Eq.cong suc (eq k)

-- ⟦ w ↑ ⟧ agrees with shift ⟦ w ⟧ pointwise.
⟦↑⟧ : ∀ {n} (w : Word (Gen n)) → ⟦ w ↑ ⟧ ≗ shift ⟦ w ⟧
⟦↑⟧ ε       k = Eq.sym (shift-id k)
⟦↑⟧ [ g ]ʷ  k = refl
⟦↑⟧ (w • v) k =
  Eq.trans (Eq.cong (⟦ v ↑ ⟧) (⟦↑⟧ w k))
  (Eq.trans (⟦↑⟧ v _) (Eq.sym (shift-hom _ _ k)))

