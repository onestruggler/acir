------------------------------------------------------------------------
-- Presentations of groups
--
-- The interpretation of circuits as even permutations:
-- ⟦_⟧ : Circuit n → Alt n.
--
-- A generator denotes an even permutation (⟦_⟧ᵍ) and a word the
-- composite, read left to right.  ⟦_⟧ is defined by recursion on words
-- rather than through StarInterp, whose extension is indexed by one
-- relation: here the same reading serves the three theories that
-- present 𝔄ₙ.  ⟦↑⟧ is the one computation law the rest of the
-- development needs: shifting a circuit shifts its denotation.
--
-- This says nothing about the RELATIONS.  That ⟦_⟧ respects them is
-- Soundness.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Interpretation where

open import Data.Fin using (Fin)
open import Data.Fin.Permutation
  using (_⟨$⟩ʳ_ ; lift₀ ; lift₀-id ; lift₀-comp)
open import Data.Nat using (ℕ)
open import Notations using (₁₊)
open import Relation.Binary.PropositionalEquality
  using (_≡_ ; refl ; sym ; trans ; cong)
open import Word.Base using (ε ; [_]ʷ ; _•_)

open import Examples.Groups.Alternating.Semantics
open import Examples.Groups.Alternating.Syntactics
  using (Gen ; Circuit ; ω-gen ; _↥ ; _↑)

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- Denotation of generators and words

⟦_⟧ᵍ : Gen n → Alt n
⟦ ω-gen ⟧ᵍ = cycleᴬ
⟦ g ↥ ⟧ᵍ   = shiftᴬ ⟦ g ⟧ᵍ

-- Words are read left to right: w • v applies w first, then v.
⟦_⟧ : Circuit n → Alt n
⟦ [ g ]ʷ ⟧ = ⟦ g ⟧ᵍ
⟦ ε ⟧      = εᴬ
⟦ w • v ⟧  = ⟦ w ⟧ ∙ᴬ ⟦ v ⟧

------------------------------------------------------------------------
-- Shifting

-- ⟦ w ↑ ⟧ agrees with lift₀ ⟦ w ⟧ pointwise.
⟦↑⟧ : (w : Circuit n) (k : Fin (₁₊ n)) →
      perm ⟦ w ↑ ⟧ ⟨$⟩ʳ k ≡ lift₀ (perm ⟦ w ⟧) ⟨$⟩ʳ k
⟦↑⟧ ε       k = sym (lift₀-id k)
⟦↑⟧ [ g ]ʷ  k = refl
⟦↑⟧ (w • v) k =
  trans (cong (perm ⟦ v ↑ ⟧ ⟨$⟩ʳ_) (⟦↑⟧ w k))
  (trans (⟦↑⟧ v _) (lift₀-comp (perm ⟦ w ⟧) (perm ⟦ v ⟧) k))
