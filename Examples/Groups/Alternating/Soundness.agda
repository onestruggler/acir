------------------------------------------------------------------------
-- Presentations of groups
--
-- Soundness: congruent circuits denote the same even permutation.
--
-- Two steps, as for Sₙ, but for any theory.  sound-ax handles the raw
-- relation given soundness of the theory's own rules: cong↑ by ⟦↑⟧
-- and the induction hypothesis, comm₃ by case analysis on Fin; sound
-- then closes it under the monoid congruence, every constructor of _≈_
-- mapping to the corresponding fact about permutations.  The rules of
-- the three theories (Theorem 4's relations, the rules of Fig. 10 and
-- Alternative's relations) are checked one by one, each by case
-- analysis on the at most five wires it touches.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alternating.Soundness where

open import Data.Fin.Permutation
  using (Permutation′ ; _⟨$⟩ʳ_ ; _∘ₚ_ ; lift₀ ; lift₀-cong)
  renaming (_≈_ to _≈ₚ_)
open import Data.Nat using (ℕ)
open import Notations using (₀ ; ₁ ; ₂ ; ₃ ; ₄ ; ₃₊ ; ₄₊)
open import Relation.Binary.PropositionalEquality
  using (refl ; sym ; trans ; cong)

import Presentation.Base as PB

open import Examples.Groups.Alternating.Interpretation
open import Examples.Groups.Alternating.Semantics
open import Examples.Groups.Alternating.Syntactics
  hiding (_VRel,_===_ ; srel ; cong↑ ; comm₁ ; comm₂ ; comm₃ ; ω↑=ω
         ; lemma-cong↑ ; comm-gate₃-w↑↑↑)

import Examples.Groups.Alternating.Alternative as A
import Examples.Groups.Alternating.Rules as R

private
  variable
    n : ℕ


------------------------------------------------------------------------
-- The structural rules

-- A cycle commutes with any permutation of the wires above it.
sound-comm₃ : (π : Permutation′ n) →
              (lift₀ (lift₀ (lift₀ π)) ∘ₚ cycle) ≈ₚ
              (cycle ∘ₚ lift₀ (lift₀ (lift₀ π)))
sound-comm₃ π ₀      = refl
sound-comm₃ π ₁      = refl
sound-comm₃ π ₂      = refl
sound-comm₃ π (₃₊ _) = refl

module _ (T : Theory)
         (sound-T : ∀ {n} {w v : Circuit n} → T n w v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧)
  where

  open Lift-Relation T using (_VRel,_===_ ; srel ; cong↑ ; comm₃)

  -- Soundness of the raw relation.
  sound-ax : ∀ {w v : Circuit n} → n VRel, w === v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
  sound-ax (srel r)              k = sound-T r k
  sound-ax (cong↑ {_} {w} {v} p) k =
    trans (⟦↑⟧ w k)
    (trans (lift₀-cong (perm ⟦ w ⟧) (perm ⟦ v ⟧) (sound-ax p) k)
           (sym (⟦↑⟧ v k)))
  sound-ax (comm₃ ω-gate g)      k = sound-comm₃ (perm ⟦ g ⟧ᵍ) k

  -- Soundness of the congruence.
  sound : ∀ {w v : Circuit n} → T ∣ n ⊢ w ≈ v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
  sound PB.refl                           k = refl
  sound (PB.sym p)                        k = sym (sound p k)
  sound (PB.trans p q)                    k = trans (sound p k) (sound q k)
  sound (PB.cong {w₀} {_} {_} {v₁} p q)   k =
    trans (sound q (perm ⟦ w₀ ⟧ ⟨$⟩ʳ k))
          (cong (perm ⟦ v₁ ⟧ ⟨$⟩ʳ_) (sound p k))
  sound PB.assoc                          k = refl
  sound PB.left-unit                      k = refl
  sound PB.right-unit                     k = refl
  sound (PB.axiom a)                      k = sound-ax a k

------------------------------------------------------------------------
-- Theorem 4's relations

sound-S : ∀ {w v : Circuit n} → n SRel, w === v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
sound-S order = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; (₃₊ _) → refl }
sound-S near  = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl
                  ; (₄₊ _) → refl }
sound-S far   = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl ; ₄ → refl
                  ; (₅₊ _) → refl }

------------------------------------------------------------------------
-- The rules of Fig. 10

sound-R : ∀ {w v : Circuit n} → R._RRel,_===_ n w v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
sound-R R.rule₁ = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl ; ₄ → refl
                    ; (₅₊ _) → refl }
sound-R R.rule₂ = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl ; ₄ → refl
                    ; (₅₊ _) → refl }
sound-R R.rule₃ = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl
                    ; (₄₊ _) → refl }
sound-R R.rule₄ = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl
                    ; (₄₊ _) → refl }
sound-R R.rule₅ = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl ; ₄ → refl
                    ; (₅₊ _) → refl }
sound-R R.rule₆ = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl
                    ; (₄₊ _) → refl }
sound-R R.rule₇ = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; (₃₊ _) → refl }

------------------------------------------------------------------------
-- Alternative's relations

sound-A : ∀ {w v : Circuit n} → A._SRel′,_===_ n w v → ⟦ w ⟧ ≈ᴬ ⟦ v ⟧
sound-A A.order  = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; (₃₊ _) → refl }
sound-A A.square = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl
                     ; (₄₊ _) → refl }
sound-A A.far    = λ { ₀ → refl ; ₁ → refl ; ₂ → refl ; ₃ → refl ; ₄ → refl
                     ; (₅₊ _) → refl }
