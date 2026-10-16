------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled functor λ¹₄ on generators
--
-- The joint paper's controlled functor with control wire 4 and domain
-- wires 0 1 2 3: the scalar goes to S on wire 4, S and K on a wire v to
-- CS(v, 4) and the K on v controlled by wire 4, and CS on the wires v,
-- v + 1 to the doubly controlled S Σ(v; 4, v + 1 | u, A), whose borrowed
-- wires u < A are the other two domain wires (an S-box of Five.Letters).
-- `λ₁` gives the letter, `λc` the circuit; Five.Transport carries it to
-- lines and derivations.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Lambda where

open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.Five.Letters

λ₁ : Gen 4 → Mac
λ₁ (gate₀ h)                = S4
λ₁ (gate₁ S-gate)           = CS04
λ₁ (gate₁ K-gate)           = CK40
λ₁ (gate₂ CS-gate)          = Sb2-0-41-3
λ₁ (gate₀ h ↥)              = S4
λ₁ (gate₁ S-gate ↥)         = CS14
λ₁ (gate₁ K-gate ↥)         = CK41
λ₁ (gate₂ CS-gate ↥)        = Sb0-1-42-3
λ₁ (gate₀ h ↥ ↥)            = S4
λ₁ (gate₁ S-gate ↥ ↥)       = CS24
λ₁ (gate₁ K-gate ↥ ↥)       = CK42
λ₁ (gate₂ CS-gate ↥ ↥)      = Sb0-2-43-1
λ₁ (gate₀ h ↥ ↥ ↥)          = S4
λ₁ (gate₁ S-gate ↥ ↥ ↥)     = CS34
λ₁ (gate₁ K-gate ↥ ↥ ↥)     = CK43
λ₁ (gate₀ h ↥ ↥ ↥ ↥)        = S4

λc : Circuit 4 → Circuit 5
λc [ g ]ʷ  = ⟪ λ₁ g ⟫
λc ε       = ε
λc (u • v) = λc u • λc v

-- The generator itself, on the domain wires 0 .. 3 of five.
λᵈ : Gen 4 → Mac
λᵈ (gate₀ h)                = ι
λᵈ (gate₁ S-gate)           = S0
λᵈ (gate₁ K-gate)           = K0
λᵈ (gate₂ CS-gate)          = CS01
λᵈ (gate₀ h ↥)              = ι1
λᵈ (gate₁ S-gate ↥)         = S1
λᵈ (gate₁ K-gate ↥)         = K1
λᵈ (gate₂ CS-gate ↥)        = CS12
λᵈ (gate₀ h ↥ ↥)            = ι2
λᵈ (gate₁ S-gate ↥ ↥)       = S2
λᵈ (gate₁ K-gate ↥ ↥)       = K2
λᵈ (gate₂ CS-gate ↥ ↥)      = CS23
λᵈ (gate₀ h ↥ ↥ ↥)          = ι3
λᵈ (gate₁ S-gate ↥ ↥ ↥)     = S3
λᵈ (gate₁ K-gate ↥ ↥ ↥)     = K3
λᵈ (gate₀ h ↥ ↥ ↥ ↥)        = ι4

λᵈ-sp : ∀ g → ⟪ λᵈ g ⟫ ≡ [ g ]ʷ ↓ᵏ 1
λᵈ-sp (gate₀ I-gate)                = Eq.refl
λᵈ-sp (gate₁ S-gate)                = Eq.refl
λᵈ-sp (gate₁ K-gate)                = Eq.refl
λᵈ-sp (gate₂ CS-gate)               = Eq.refl
λᵈ-sp (gate₀ I-gate ↥)              = Eq.refl
λᵈ-sp (gate₁ S-gate ↥)              = Eq.refl
λᵈ-sp (gate₁ K-gate ↥)              = Eq.refl
λᵈ-sp (gate₂ CS-gate ↥)             = Eq.refl
λᵈ-sp (gate₀ I-gate ↥ ↥)            = Eq.refl
λᵈ-sp (gate₁ S-gate ↥ ↥)            = Eq.refl
λᵈ-sp (gate₁ K-gate ↥ ↥)            = Eq.refl
λᵈ-sp (gate₂ CS-gate ↥ ↥)           = Eq.refl
λᵈ-sp (gate₀ I-gate ↥ ↥ ↥)          = Eq.refl
λᵈ-sp (gate₁ S-gate ↥ ↥ ↥)          = Eq.refl
λᵈ-sp (gate₁ K-gate ↥ ↥ ↥)          = Eq.refl
λᵈ-sp (gate₀ I-gate ↥ ↥ ↥ ↥)        = Eq.refl
