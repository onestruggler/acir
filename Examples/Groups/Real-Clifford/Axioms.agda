------------------------------------------------------------------------
-- Presentations of groups
--
-- The relations R1 … R16 as equations of letter lists (Engine.Eqn),
-- with short names for the letters on the bottom three wires
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Real-Clifford.Axioms where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Nat.Base using (ℕ)
import Relation.Binary.PropositionalEquality as Eq

import Presentation.Base as PB
import Presentation.Properties as PP

open import Notations using (₁₊ ; ₂₊ ; ₃₊)
open import Examples.Groups.Real-Clifford.Syntactics
open import Examples.Groups.Real-Clifford.Engine using (Eqn ; eqn ; ⟪_⟫)

private
  variable
    n : ℕ

------------------------------------------------------------------------
-- Letters: the scalar, and H, Z, CZ on the bottom wires

pattern 𝕞  = gate₀ neg-gate
pattern h₀ = gate₁ H-gate
pattern h₁ = gate₁ H-gate ↥
pattern h₂ = gate₁ H-gate ↥ ↥
pattern z₀ = gate₁ Z-gate
pattern z₁ = gate₁ Z-gate ↥
pattern z₂ = gate₁ Z-gate ↥ ↥
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

R₁ᵉ : Eqn n
R₁ᵉ = ax (𝕞 ∷ 𝕞 ∷ []) [] R₁ (as Eq.refl) (as Eq.refl)

R₂ᵉ : Eqn (₁₊ n)
R₂ᵉ = ax (z₀ ∷ z₀ ∷ []) [] R₂ (as Eq.refl) (as Eq.refl)

R₃ᵉ : Eqn (₁₊ n)
R₃ᵉ = ax (h₀ ∷ h₀ ∷ []) [] R₃ (as Eq.refl) (as Eq.refl)

R₄ᵉ : Eqn (₁₊ n)
R₄ᵉ = ax (h₀ ∷ z₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ z₀ ∷ []) (𝕞 ∷ []) R₄ (as Eq.refl) (as Eq.refl)

R₅ᵉ : Eqn (₂₊ n)
R₅ᵉ = ax (c₀ ∷ c₀ ∷ []) [] R₅ (as Eq.refl) (as Eq.refl)

R₆ᵉ : Eqn (₂₊ n)
R₆ᵉ = ax (c₀ ∷ z₁ ∷ []) (z₁ ∷ c₀ ∷ []) R₆ (as Eq.refl) (as Eq.refl)

R₇ᵉ : Eqn (₂₊ n)
R₇ᵉ = ax (c₀ ∷ z₀ ∷ []) (z₀ ∷ c₀ ∷ []) R₇ (as Eq.refl) (as Eq.refl)

R₈ᵉ : Eqn (₂₊ n)
R₈ᵉ = ax (c₀ ∷ h₁ ∷ z₁ ∷ h₁ ∷ []) (h₁ ∷ z₀ ∷ z₁ ∷ h₁ ∷ c₀ ∷ []) R₈ (as Eq.refl) (as Eq.refl)

R₉ᵉ : Eqn (₂₊ n)
R₉ᵉ = ax (c₀ ∷ h₀ ∷ z₀ ∷ h₀ ∷ []) (h₀ ∷ z₀ ∷ z₁ ∷ h₀ ∷ c₀ ∷ []) R₉ (as Eq.refl) (as Eq.refl)

R₁₀ᵉ : Eqn (₂₊ n)
R₁₀ᵉ = ax (c₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ []) (z₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₀ ∷ []) R₁₀ (as Eq.refl) (as Eq.refl)

R₁₁ᵉ : Eqn (₂₊ n)
R₁₁ᵉ = ax (c₀ ∷ h₀ ∷ c₀ ∷ h₀ ∷ []) (h₀ ∷ z₁ ∷ c₀ ∷ h₀ ∷ c₀ ∷ []) R₁₁ (as Eq.refl) (as Eq.refl)

R₁₂ᵉ : Eqn (₂₊ n)
R₁₂ᵉ = ax (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ [])
          (h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ []) R₁₂ (as Eq.refl) (as Eq.refl)

R₁₃ᵉ : Eqn (₃₊ n)
R₁₃ᵉ = ax (c₀ ∷ c₁ ∷ []) (c₁ ∷ c₀ ∷ []) R₁₃ (as Eq.refl) (as Eq.refl)

R₁₄ᵉ : Eqn (₃₊ n)
R₁₄ᵉ = ax (h₀ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ [])
          (h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ c₀ ∷ h₁ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₂ ∷ [])
          R₁₄ (as Eq.refl) (as Eq.refl)

R₁₅ᵉ : Eqn (₃₊ n)
R₁₅ᵉ = ax (c₀ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ c₀ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ [])
          (c₁ ∷ h₁ ∷ h₂ ∷ c₁ ∷ h₁ ∷ h₂ ∷ c₀ ∷ [])
          R₁₅ (as Eq.refl) (as Eq.refl)

R₁₆ᵉ : Eqn (₃₊ n)
R₁₆ᵉ = ax (c₁ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ c₁ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ [])
          (c₀ ∷ h₀ ∷ h₁ ∷ c₀ ∷ h₀ ∷ h₁ ∷ c₁ ∷ [])
          R₁₆ (as Eq.refl) (as Eq.refl)
