------------------------------------------------------------------------
-- Presentations of groups
--
-- One wire: the rules are complete, and the circuits present S₂
--
-- The instance of BySymmetric at one wire and two states.  The one
-- transposition is NOT itself, the one Coxeter relation is rule (1),
-- and nothing is left to derive.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Alt16-RevCir.Width1 where

open import Data.Bool.Base using (true ; false)
open import Data.Empty using (⊥-elim)
open import Data.Fin using (Fin ; zero ; suc)
open import Data.Fin.Permutation using (_⟨$⟩ʳ_)
open import Data.Nat using (ℕ ; suc ; _+_ ; _≤_ ; s≤s)
open import Data.Vec.Base using ([] ; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Word.Base using ([_]ʷ ; ε ; _•_ ; _ʷ)

import Presentation.Base as PB
open import Presentation.Definitions using (_IsPresentationOf_)

import Examples.Groups.Symmetric.Interpretation as SI
open import Examples.Groups.Symmetric.Semantics using (Permutation′-group)
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Alt16-RevCir.BySymmetric
  using (gᵈ ; no-gen₁ ; module Step)
open import Examples.Groups.Alt16-RevCir.Semantics
  using (Bits ; ⟦_⟧ᵍ ; ⟦_⟧ ; _≐_)
open import Examples.Groups.Alt16-RevCir.Syntactics
  using (Gen ; Circuit ; X ; X-gen ; gate₀ ; _↥)
open import Examples.Groups.Alt16-RevCir.Theory using (r1 ; module T)

------------------------------------------------------------------------
-- The translations

Θ : ℕ → Circuit 1
Θ 0 = X
Θ _ = ε

f : Gen 1 → S.Circuit 2
f X-gen = S.σ
f (gate₀ ())
f (gate₀ () ↥)

------------------------------------------------------------------------
-- The two states

enc : Fin 2 → Bits 1
enc zero       = false ∷ []
enc (suc zero) = true ∷ []

dec : Bits 1 → Fin 2
dec (false ∷ []) = zero
dec (true ∷ [])  = suc zero

dec-enc : ∀ i → dec (enc i) ≡ i
dec-enc zero       = refl
dec-enc (suc zero) = refl

enc-dec : ∀ x → enc (dec x) ≡ x
enc-dec (false ∷ []) = refl
enc-dec (true ∷ [])  = refl

------------------------------------------------------------------------
-- The hypotheses of the step

private
  order : ∀ d → 2 + d ≤ 2 → 1 T.⊢ Θ d • Θ d ≈ ε
  order 0       _               = PB.axiom (T.srel (T.srel r1))
  order (suc d) (s≤s (s≤s ()))

  braid : ∀ d → 3 + d ≤ 2 →
          1 T.⊢ Θ d • Θ (suc d) • Θ d ≈ Θ (suc d) • Θ d • Θ (suc d)
  braid d (s≤s (s≤s ()))

  far : ∀ d e → 2 + d ≤ e → 2 + e ≤ 2 → 1 T.⊢ Θ e • Θ d ≈ Θ d • Θ e
  far d 0       () _
  far d (suc e) _  (s≤s (s≤s ()))

  gate : (x : Gen 1) → 1 T.⊢ [ x ]ʷ ≈ (gᵈ Θ 0 ʷ) (f x)
  gate X-gen = PB.refl
  gate (gate₀ ())
  gate (gate₀ () ↥)

  f-sem-gen : (x : Gen 1) (i : Fin 2) →
              SI.⟦ f x ⟧ ⟨$⟩ʳ i ≡ dec (⟦ x ⟧ᵍ (enc i))
  f-sem-gen X-gen zero       = refl
  f-sem-gen X-gen (suc zero) = refl
  f-sem-gen (gate₀ ())
  f-sem-gen (gate₀ () ↥)

  g-sem-gen : (y : S.Gen 2) (i : Fin 2) →
              dec (⟦ gᵈ Θ 0 y ⟧ (enc i)) ≡ SI.⟦ [ y ]ʷ ⟧ ⟨$⟩ʳ i
  g-sem-gen S.σ-gen zero       = refl
  g-sem-gen S.σ-gen (suc zero) = refl
  g-sem-gen (y S.↥) i          = ⊥-elim (no-gen₁ y)

------------------------------------------------------------------------
-- The step

module Step₁ = Step Θ f enc dec dec-enc enc-dec
                    order braid far gate f-sem-gen g-sem-gen

-- Two one-wire circuits with the same function are equal by the rules.
complete₁ : {w v : Circuit 1} → ⟦ w ⟧ ≐ ⟦ v ⟧ → 1 T.⊢ w ≈ v
complete₁ = Step₁.complete

presentation₁ : (T._VRel,_===_ 1) IsPresentationOf (Permutation′-group 2)
presentation₁ = Step₁.presentation
