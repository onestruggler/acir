------------------------------------------------------------------------
-- Presentations of groups
--
-- The controlled forms of the general-width gates, and the semantics
-- of Equation (284) at every width
--
-- The gates of Lemma D.8 all have the box's controls 3 … on top and a
-- local part on the wires 0, 1, 2, so each has a controlled form with a
-- three-wire payload (CForm).  `B□` and `E□` are GeneralN.Box's and
-- GeneralN.EForm's gates, restated here without those modules'
-- completeness parameters (the two spellings agree by definition).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.Sem where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals

------------------------------------------------------------------------
-- The gates

-- The smaller box with its box wire on wire 1, a control on wire 0 and
-- wire 2 idle; the multi-controlled H it makes between P ⊗ P.
B□ E□ : ∀ k → Circuit (₄₊ k)
B□ k = τ₀₂-conj (Λ□ (₂₊ k) ↑)
E□ k = PP ↓ • B□ k • PP ↓

------------------------------------------------------------------------
-- Their forms, with the payload on the wires 0, 1, 2

cf-Λ : ∀ k → CF {3} {₁₊ k} (Λ□ (₃₊ k))
cf-Λ k = cf-box 2 (₁₊ k)

cf-Λ↑ : ∀ k → CF {3} {₁₊ k} (Λ□ (₂₊ k) ↑)
cf-Λ↑ k = cf-↑ (cf-box 1 (₁₊ k))

cf-B : ∀ k → CF {3} {₁₊ k} (B□ k)
cf-B k = cf-• (cf-loc′ τ₀₂ τᴸ τᴸ-def) (cf-• (cf-Λ↑ k) (cf-loc′ τ₀₂ τᴸ τᴸ-def))

cf-E : ∀ k → CF {3} {₁₊ k} (E□ k)
cf-E k = cf-• (cf-loc′ PP PP₀₁ᴸ PP₀₁ᴸ-def) (cf-• (cf-B k) (cf-loc′ PP PP₀₁ᴸ PP₀₁ᴸ-def))

cf-W : ∀ k → CF {3} {₁₊ k} CCZX
cf-W k = cf-loc′ CCZX Wᴸ Wᴸ-def

cf-V : ∀ k → CF {3} {₁₊ k} CCXZ
cf-V k = cf-loc′ CCXZ Vᴸ Vᴸ-def

------------------------------------------------------------------------
-- (284) holds semantically at every width

sem284 : ∀ k → ⟦ Λ□ (₃₊ k) ⟧ ~ ⟦ CCZX • E□ k • CCXZ • E□ k ⟧
sem284 k = cf-~ (cf-Λ k) (cf-• (cf-W k) (cf-• (cf-E k) (cf-• (cf-V k) (cf-E k)))) Eq.refl Eq.refl

------------------------------------------------------------------------
-- (285) holds semantically at every width: on its box wire alone the
-- box's payload is a scalar

sem285 : ∀ k → ⟦ H ↓ • Λ□ (₃₊ k) ⟧ ~ ⟦ Λ□ (₃₊ k) • H ↓ ⟧
sem285 k = cf-~ (cf-• (cf-loc H) (cf-box 0 (₃₊ k))) (cf-• (cf-box 0 (₃₊ k)) (cf-loc H)) Eq.refl Eq.refl
