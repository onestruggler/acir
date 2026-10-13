------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations C1 … C18 as equations of letter lists (Engine.Eqn),
-- with short names for the letters on the bottom three wires
--
-- Generated from Syntactics by gen_axioms.py: each list is the rule's
-- word with its derived generators unfolded, which by-assoc checks.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qutrit-Clifford.Axioms where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
import Relation.Binary.PropositionalEquality as Eq

import Presentation.Base as PB
import Presentation.Properties as PP

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Qutrit-Clifford.Syntactics
open import Examples.Groups.Qutrit-Clifford.Engine using (Eqn ; eqn ; ⟪_⟫)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Letters: the scalar, and H, S, CZ on the bottom wires

pattern 𝕟  = gate₀ ν-gate
pattern h₀ = gate₁ H-gate
pattern h₁ = gate₁ H-gate ↥
pattern h₂ = gate₁ H-gate ↥ ↥
pattern s₀ = gate₁ S-gate
pattern s₁ = gate₁ S-gate ↥
pattern s₂ = gate₁ S-gate ↥ ↥
pattern c₀ = gate₂ CZ-gate
pattern c₁ = gate₂ CZ-gate ↥

------------------------------------------------------------------------
-- The relations, read up to associativity

private
  ax : ∀ {m} {w v : Circuit m} (l r : List (Gen m)) → m QRel, w === v →
       m ⊢ ⟪ l ⟫ ≈ w → m ⊢ v ≈ ⟪ r ⟫ → Eqn m
  ax l r a p q = eqn l r (PB.trans p (PB.trans (PB.axiom (srel a)) q))

  as : ∀ {m} {w v : Circuit m} → PP.to-list (m VRel,_===_) w Eq.≡ PP.to-list (m VRel,_===_) v →
       m ⊢ w ≈ v
  as {m} = PP.by-assoc (m VRel,_===_)

C₁ᵉ : Eqn n
C₁ᵉ = ax (𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ [])
  [] C₁ (as Eq.refl) (as Eq.refl)

C₂ᵉ : Eqn (₁₊ n)
C₂ᵉ = ax (h₀ ∷ h₀ ∷ h₀ ∷ h₀ ∷ [])
  [] C₂ (as Eq.refl) (as Eq.refl)

C₃ᵉ : Eqn (₁₊ n)
C₃ᵉ = ax (s₀ ∷ s₀ ∷ s₀ ∷ [])
  [] C₃ (as Eq.refl) (as Eq.refl)

C₄ᵉ : Eqn (₁₊ n)
C₄ᵉ = ax (h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ [])
  (𝕟 ∷ []) C₄ (as Eq.refl) (as Eq.refl)

C₅ᵉ : Eqn (₁₊ n)
C₅ᵉ = ax (h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ s₀ ∷ [])
  (s₀ ∷ h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ []) C₅ (as Eq.refl) (as Eq.refl)

C₆ᵉ : Eqn (₂₊ n)
C₆ᵉ = ax (c₀ ∷ c₀ ∷ c₀ ∷ [])
  [] C₆ (as Eq.refl) (as Eq.refl)

C₇ᵉ : Eqn (₂₊ n)
C₇ᵉ = ax (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ [])
  [] C₇ (as Eq.refl) (as Eq.refl)

C₈ᵉ : Eqn (₂₊ n)
C₈ᵉ = ax (c₀ ∷ s₁ ∷ [])
  (s₁ ∷ c₀ ∷ []) C₈ (as Eq.refl) (as Eq.refl)

C₉ᵉ : Eqn (₂₊ n)
C₉ᵉ = ax (c₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ [])
  (h₁ ∷ h₁ ∷ c₀ ∷ []) C₉ (as Eq.refl) (as Eq.refl)

C₁₀ᵉ : Eqn (₂₊ n)
C₁₀ᵉ = ax (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ s₁ ∷ [])
  (s₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ []) C₁₀ (as Eq.refl) (as Eq.refl)

C₁₁ᵉ : Eqn (₂₊ n)
C₁₁ᵉ = ax (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ h₁ ∷ [])
  (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ []) C₁₁ (as Eq.refl) (as Eq.refl)

C₁₂ᵉ : Eqn (₂₊ n)
C₁₂ᵉ = ax (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
  (c₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ []) C₁₂ (as Eq.refl) (as Eq.refl)

C₁₃ᵉ : Eqn (₂₊ n)
C₁₃ᵉ = ax (h₁ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ s₁ ∷ [])
  (𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ s₁ ∷ c₀ ∷ h₁ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ []) C₁₃ (as Eq.refl) (as Eq.refl)

C₁₄ᵉ : Eqn (₂₊ n)
C₁₄ᵉ = ax (h₁ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ [])
  (𝕟 ∷ 𝕟 ∷ 𝕟 ∷ 𝕟 ∷ s₀ ∷ h₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ []) C₁₄ (as Eq.refl) (as Eq.refl)

C₁₅ᵉ : Eqn (₃₊ n)
C₁₅ᵉ = ax (c₁ ∷ c₀ ∷ [])
  (c₀ ∷ c₁ ∷ []) C₁₅ (as Eq.refl) (as Eq.refl)

C₁₆ᵉ : Eqn (₃₊ n)
C₁₆ᵉ = ax (c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ [])
  (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ []) C₁₆ (as Eq.refl) (as Eq.refl)

C₁₇ᵉ : Eqn (₃₊ n)
C₁₇ᵉ = ax (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₀ ∷ [])
  (c₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ []) C₁₇ (as Eq.refl) (as Eq.refl)

C₁₈ᵉ : Eqn (₃₊ n)
C₁₈ᵉ = ax (c₀ ∷ h₁ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ [])
  (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ h₁ ∷ h₁ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ []) C₁₈ (as Eq.refl) (as Eq.refl)
