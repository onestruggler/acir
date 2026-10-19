------------------------------------------------------------------------
-- Presentations of groups
--
-- CliffT₂'s matrices against two-level and Bian–Selinger semantics:
-- the encodings
--
-- Completeness of CliffT₂ (Theorem 22) is transferred from three
-- presentations over 𝔻[ω] = ℤ[1/√2,i], one for each width:
--
-- * on two wires, Bian and Selinger's (Examples.Groups.Clifford+T-
--   2qubit), whose words over ω, H₀, H₁, S₀, S₁, T₀, T₁ and CZ are
--   read, in operator order, as 4 × 4 matrices through their
--   translation into two-level matrices (tl); qubit 0 is wire 0;
-- * on one wire and on none, the two-level presentation of
--   U₂(𝔻[ω]) and U₁(𝔻[ω]) (Examples.Groups.Clifford+T-2qubit-
--   TwoLevel, complete in dimensions up to 4), by ω_[a], X_[a,b] and
--   H_[a,b]: a T is ω_[1], ω is ω_[0] ω_[1] (or ω_[0]), H is H_[0,1].
--
-- Each encoding sends a gate to a word with the gate's matrix, read
-- in 𝔻[ω] (Semantics.Reading); the gates are compared as closed
-- matrices, and Reading.Transfer does the rest.  Into the two-level
-- words a circuit is encoded backwards (Via), their words being read
-- in operator order; into Bian and Selinger's it is encoded forwards
-- (ViaT), as the paper does, its matrix being then the transpose of
-- the circuit's — every gate's matrix is symmetric — so that each of
-- their relations decodes to the paper's own reading of it.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Independence.Clifford+T.Bridge where

open import Data.Fin.Base using (zero ; suc)
open import Data.Nat.Base using (z≤n ; s≤s)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_ ; refl)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_ ; _ʷ)

open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Ring using (_+ᴰ_ ; _*ᴰ_ ; -ᴰ_)
import Examples.Groups.Clifford+T-2qubit-TwoLevel.Syntactics as TL
open import Examples.Groups.Clifford+T-2qubit-TwoLevel.Semantics using (⟦_⟧ᵐ ; ⟦•⟧ᵐ ; actV ; set₁ ; set₂)
open import Examples.Groups.Clifford+T-2qubit.Generator using (module Clifford+T)
open import Examples.Groups.Clifford+T-2qubit.Presentation using (tl)

open import Examples.Independence.Clifford+T.Syntactics
import Examples.Independence.Clifford+T.Semantics as Sem
open import Examples.Independence.Semantics.Reading using (⟪_⟫ ; _ᵀ ; module Mat ; module Transfer)

module BS = Clifford+T

open Transfer Sem.val public using (exact)
open Transfer Sem.val using (module Via ; module ViaT)

------------------------------------------------------------------------
-- The encodings

-- On two wires, into Bian and Selinger's words: CNOT is H CZ H on its
-- target, the swap three such CNOTs (their Swap).
ℰ₂ : Gen 2 → Word BS.Generator
ℰ₂ (gate₀ ⌈ ω-gate ⌉)     = BS.W
ℰ₂ (gate₁ ⌈ H-gate ⌉)     = BS.H0
ℰ₂ (gate₁ ⌈ T-gate ⌉)     = BS.T0
ℰ₂ (gate₂ ⌈ CX-gate ⌉)    = BS.CX0
ℰ₂ (gate₂ swap)           = BS.Swap
ℰ₂ (gate₀ ⌈ ω-gate ⌉ ↥)   = BS.W
ℰ₂ (gate₁ ⌈ H-gate ⌉ ↥)   = BS.H1
ℰ₂ (gate₁ ⌈ T-gate ⌉ ↥)   = BS.T1
ℰ₂ (gate₀ ⌈ ω-gate ⌉ ↥ ↥) = BS.W

-- On one wire, into two-level words on two indices.
ℰ₁ : Gen 1 → Word (TL.Gen 2)
ℰ₁ (gate₀ ⌈ ω-gate ⌉)   = TL.ω zero • TL.ω (suc zero)
ℰ₁ (gate₁ ⌈ H-gate ⌉)   = TL.H zero (suc zero) (s≤s z≤n)
ℰ₁ (gate₁ ⌈ T-gate ⌉)   = TL.ω (suc zero)
ℰ₁ (gate₀ ⌈ ω-gate ⌉ ↥) = TL.ω zero • TL.ω (suc zero)

-- On no wire, into two-level words on one index.
ℰ₀ : Gen 0 → Word (TL.Gen 1)
ℰ₀ (gate₀ ⌈ ω-gate ⌉) = TL.ω zero

------------------------------------------------------------------------
-- The gates, as closed matrices

-- Bian and Selinger's matrices.
⟦_⟧ᴮ : Word BS.Generator → _
⟦ u ⟧ᴮ = ⟦ (tl ʷ) u ⟧ᵐ

opaque
  unfolding actV set₁ set₂ _+ᴰ_ _*ᴰ_ -ᴰ_

  gen₂ : (g : Gen 2) → ⟦ ℰ₂ g ⟧ᴮ ≡ Mat.mat (⟪ Sem.⟦ g ⟧₀ ⟫ ᵀ)
  gen₂ (gate₀ ⌈ ω-gate ⌉)     = refl
  gen₂ (gate₁ ⌈ H-gate ⌉)     = refl
  gen₂ (gate₁ ⌈ T-gate ⌉)     = refl
  gen₂ (gate₂ ⌈ CX-gate ⌉)    = refl
  gen₂ (gate₂ swap)           = refl
  gen₂ (gate₀ ⌈ ω-gate ⌉ ↥)   = refl
  gen₂ (gate₁ ⌈ H-gate ⌉ ↥)   = refl
  gen₂ (gate₁ ⌈ T-gate ⌉ ↥)   = refl
  gen₂ (gate₀ ⌈ ω-gate ⌉ ↥ ↥) = refl

  gen₁ : (g : Gen 1) → ⟦ ℰ₁ g ⟧ᵐ ≡ Mat.mat ⟪ Sem.⟦ g ⟧₀ ⟫
  gen₁ (gate₀ ⌈ ω-gate ⌉)   = refl
  gen₁ (gate₁ ⌈ H-gate ⌉)   = refl
  gen₁ (gate₁ ⌈ T-gate ⌉)   = refl
  gen₁ (gate₀ ⌈ ω-gate ⌉ ↥) = refl

  gen₀ : (g : Gen 0) → ⟦ ℰ₀ g ⟧ᵐ ≡ Mat.mat ⟪ Sem.⟦ g ⟧₀ ⟫
  gen₀ (gate₀ ⌈ ω-gate ⌉) = refl

------------------------------------------------------------------------
-- Every circuit

module V₂ = ViaT ⟦_⟧ᴮ refl (λ u v → ⟦•⟧ᵐ ((tl ʷ) u) ((tl ʷ) v)) ℰ₂ gen₂
module V₁ = Via ⟦_⟧ᵐ refl ⟦•⟧ᵐ ℰ₁ gen₁
module V₀ = Via ⟦_⟧ᵐ refl ⟦•⟧ᵐ ℰ₀ gen₀
