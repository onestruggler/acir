------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations C1 … C15 as equations of letter lists (Engine.Eqn),
-- with short names for the letters on the bottom three wires
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Qubit-Clifford.Axioms where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
import Relation.Binary.PropositionalEquality as Eq

import Presentation.Base as PB
import Presentation.Properties as PP

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Qubit-Clifford.Syntactics
open import Examples.Groups.Qubit-Clifford.Engine using (Eqn ; eqn ; ⟪_⟫)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Letters: the scalar, and H, S, CZ on the bottom wires

pattern 𝕨  = gate₀ ω-gate
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
  ax : ∀ {m} {w v : Circuit m} (l r : List (Gen m)) → m SRel, w === v →
       m ⊢ ⟪ l ⟫ ≈ w → m ⊢ v ≈ ⟪ r ⟫ → Eqn m
  ax l r a p q = eqn l r (PB.trans p (PB.trans (PB.axiom (srel a)) q))

  as : ∀ {m} {w v : Circuit m} → PP.to-list (m VRel,_===_) w Eq.≡ PP.to-list (m VRel,_===_) v →
       m ⊢ w ≈ v
  as {m} = PP.by-assoc (m VRel,_===_)

C₁ᵉ : Eqn n
C₁ᵉ = ax (𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ [])
  ([]) C₁ (as Eq.refl) (as Eq.refl)

C₂ᵉ : Eqn (₁₊ n)
C₂ᵉ = ax (h₀ ∷ h₀ ∷ [])
  ([]) C₂ (as Eq.refl) (as Eq.refl)

C₃ᵉ : Eqn (₁₊ n)
C₃ᵉ = ax (s₀ ∷ s₀ ∷ s₀ ∷ s₀ ∷ [])
  ([]) C₃ (as Eq.refl) (as Eq.refl)

C₄ᵉ : Eqn (₁₊ n)
C₄ᵉ = ax (h₀ ∷ s₀ ∷ h₀ ∷ s₀ ∷ h₀ ∷ s₀ ∷ [])
  (𝕨 ∷ []) C₄ (as Eq.refl) (as Eq.refl)

C₅ᵉ : Eqn (₂₊ n)
C₅ᵉ = ax (c₀ ∷ c₀ ∷ [])
  ([]) C₅ (as Eq.refl) (as Eq.refl)

C₆ᵉ : Eqn (₂₊ n)
C₆ᵉ = ax (c₀ ∷ s₁ ∷ [])
  (s₁ ∷ c₀ ∷ []) C₆ (as Eq.refl) (as Eq.refl)

C₇ᵉ : Eqn (₂₊ n)
C₇ᵉ = ax (c₀ ∷ s₀ ∷ [])
  (s₀ ∷ c₀ ∷ []) C₇ (as Eq.refl) (as Eq.refl)

C₈ᵉ : Eqn (₂₊ n)
C₈ᵉ = ax (c₀ ∷ h₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ [])
  (h₁ ∷ s₁ ∷ s₁ ∷ h₁ ∷ s₀ ∷ s₀ ∷ c₀ ∷ []) C₈ (as Eq.refl) (as Eq.refl)

C₉ᵉ : Eqn (₂₊ n)
C₉ᵉ = ax (c₀ ∷ h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ [])
  (h₀ ∷ s₀ ∷ s₀ ∷ h₀ ∷ s₁ ∷ s₁ ∷ c₀ ∷ []) C₉ (as Eq.refl) (as Eq.refl)

C₁₀ᵉ : Eqn (₂₊ n)
C₁₀ᵉ = ax (c₀ ∷ h₁ ∷ c₀ ∷ [])
  (𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ s₁ ∷ h₁ ∷ s₁ ∷ s₀ ∷ c₀ ∷ h₁ ∷ s₁ ∷ []) C₁₀ (as Eq.refl) (as Eq.refl)

C₁₁ᵉ : Eqn (₂₊ n)
C₁₁ᵉ = ax (c₀ ∷ h₀ ∷ c₀ ∷ [])
  (𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ 𝕨 ∷ s₀ ∷ h₀ ∷ s₀ ∷ s₁ ∷ c₀ ∷ h₀ ∷ s₀ ∷ []) C₁₁ (as Eq.refl) (as Eq.refl)

C₁₂ᵉ : Eqn (₃₊ n)
C₁₂ᵉ = ax (c₀ ∷ c₁ ∷ [])
  (c₁ ∷ c₀ ∷ []) C₁₂ (as Eq.refl) (as Eq.refl)

C₁₃ᵉ : Eqn (₃₊ n)
C₁₃ᵉ = ax (c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ [])
  (c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₂ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ []) C₁₃ (as Eq.refl) (as Eq.refl)

C₁₄ᵉ : Eqn (₃₊ n)
C₁₄ᵉ = ax (c₀ ∷ h₂ ∷ h₁ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ [])
  ([]) C₁₄ (as Eq.refl) (as Eq.refl)

C₁₅ᵉ : Eqn (₃₊ n)
C₁₅ᵉ = ax (c₁ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ c₁ ∷ h₁ ∷ h₀ ∷ c₀ ∷ h₁ ∷ h₀ ∷ c₀ ∷ [])
  ([]) C₁₅ (as Eq.refl) (as Eq.refl)
