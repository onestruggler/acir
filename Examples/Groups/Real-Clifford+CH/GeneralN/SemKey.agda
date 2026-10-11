------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic steps of Equations (283)–(284), one width down
--
-- One width down, with the wire 2 of the full width removed, the
-- multi-controlled H and the box of (284) are HG₀₁ and B₁₀ (SemZX):
-- the H on wire 0 and the box, both with their box wire on wire 1.
-- Their product passes the CH and CZ from wire 1 onto wire 0 in either
-- order, and H on their box wire; and the box is an involution.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.SemKey where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (B₁₀ ; HG₀₁ ; module Forms)

module _ (k : ℕ) where
  open Forms k

  private
    eb : CF {3} {k} (HG₀₁ k • B₁₀ k)
    eb = cf-• hg₀₁ b₁₀

    h₁ : CF {3} {k} (H ↑)
    h₁ = cf-loc (H ↑)

  sem-EB-P₁ : ⟦ (HG₀₁ k • B₁₀ k) • (CH • CZ) ⟧ ~ ⟦ (CH • CZ) • (HG₀₁ k • B₁₀ k) ⟧
  sem-EB-P₁ = cf-~ (cf-• eb (cf-• ch cz)) (cf-• (cf-• ch cz) eb) Eq.refl Eq.refl

  sem-EB-P₂ : ⟦ (HG₀₁ k • B₁₀ k) • (CZ • CH) ⟧ ~ ⟦ (CZ • CH) • (HG₀₁ k • B₁₀ k) ⟧
  sem-EB-P₂ = cf-~ (cf-• eb (cf-• cz ch)) (cf-• (cf-• cz ch) eb) Eq.refl Eq.refl

  sem-EB-H₁ : ⟦ (HG₀₁ k • B₁₀ k) • H ↑ ⟧ ~ ⟦ H ↑ • (HG₀₁ k • B₁₀ k) ⟧
  sem-EB-H₁ = cf-~ (cf-• eb h₁) (cf-• h₁ eb) Eq.refl Eq.refl

  -- (299) one width down: the box is an involution.
  sem-box² : ⟦ Λ□ (₂₊ k) • Λ□ (₂₊ k) ⟧ ~ ⟦ ε ⟧
  sem-box² = cf-~ (cf-• box box) eps Eq.refl Eq.refl

  -- (298) one width down, the step (287) takes: the box passes the CH
  -- from its first control onto its box wire.
  sem-box-CH : ⟦ Λ□ (₂₊ k) • CH ⟧ ~ ⟦ CH • Λ□ (₂₊ k) ⟧
  sem-box-CH = cf-~ (cf-• box ch) (cf-• ch box) Eq.refl Eq.refl
