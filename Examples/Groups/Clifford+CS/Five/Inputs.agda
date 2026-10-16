------------------------------------------------------------------------
-- Presentations of groups
--
-- The generated five-wire lemmas the generic modules take
--
-- Five.Calc, Five.F6 and what is built on them are generic in a few
-- five-wire equations between lines of macro letters, so that they can
-- be checked without the derivations; Five.CalcAx, Five.F6Ax and
-- Five.TransportAx supply them, as lemmas of Five.D (the joint paper's
-- items lowered to primitive steps, and windows).  This record collects
-- them.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Inputs where

open import Data.List using (List ; [] ; _∷_)
open import Word.Base using (ε)

open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lambda using (λ₁ ; λᵈ)
open import Examples.Groups.Clifford+CS.Five.Transport using (AxOk)

record Inputs : Set where
  field
    -- The λ-calculus at control wire 4 for generators.
    F4ᵍ : ∀ g h → ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ h ∷ [] ⟫ʷ ≈ ⟪ λ₁ h ∷ X4 ∷ λ₁ g ∷ X4 ∷ [] ⟫ʷ
    F5ᵍ : ∀ g → ⟪ λᵈ g ∷ [] ⟫ʷ ≈ ⟪ X4 ∷ λ₁ g ∷ X4 ∷ λ₁ g ∷ [] ⟫ʷ
    x4x4 : ⟪ X4 ∷ X4 ∷ [] ⟫ʷ ≈ ε
    -- Transport.
    ok : AxOk
    -- (F6).
    cx14ˡ : ⟪ CX14 ∷ [] ⟫ʷ ≈ ⟪ K4 ∷ CS14 ∷ CS14 ∷ K4 ∷ ι ∷ [] ⟫ʷ
    w1ˡ : ⟪ CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ [] ⟫ʷ ≈ ⟪ CS01⁻ ∷ CCZ014 ∷ X4 ∷ CS04 ∷ X4 ∷ [] ⟫ʷ
    w2ˡ : ⟪ CX14 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CX14 ∷ [] ⟫ʷ ≈
          ⟪ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ X4 ∷ CS04 ∷ X4 ∷ CS01 ∷ CCZ014 ∷ [] ⟫ʷ
    aaˡ : ⟪ CX14 ∷ CX14 ∷ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
    eeˡ : ⟪ CS01 ∷ CCZ014 ∷ CS01⁻ ∷ CCZ014 ∷ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
    sb2ˡ : ⟪ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ [] ⟫ʷ ≈ ⟪ CCZ014 ∷ [] ⟫ʷ
    -- The letters touching wire 4 for the independence.
    cx43ˡ : ⟪ CX43 ∷ [] ⟫ʷ ≈ ⟪ CK43 ∷ CS34 ∷ CS34 ∷ CK43 ∷ S4 ∷ [] ⟫ʷ
    cx34ˡ : ⟪ CX34 ∷ [] ⟫ʷ ≈ ⟪ Sw23 ∷ Sw12 ∷ CX14 ∷ Sw12 ∷ Sw23 ∷ [] ⟫ʷ
    sw34ˡ : ⟪ Sw34 ∷ [] ⟫ʷ ≈ ⟪ CX34 ∷ CX43 ∷ CX34 ∷ [] ⟫ʷ
