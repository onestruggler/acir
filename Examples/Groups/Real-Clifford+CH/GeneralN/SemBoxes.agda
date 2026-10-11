------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic steps of Equations (288)–(291), one width down
--
-- At width 4 + k, each an identity of controlled forms decided on the
-- stored payloads: the boxes B□ k and B₁₀ (1 + k) square to the
-- identity; the latter generates the box with the doubly controlled ZX
-- as in (269); and the CZ and CH of the wires 0 1 pass the box on wire
-- 2 with its first control on wire 1 (GeneralN.Idle.yB).  And for
-- (294)/(295): the box C₀ on wire 0 controlled by the wires 1 3 … (wire 2
-- idle) generates B₁₀ (1 + k) with the singly controlled ZX on wire 1,
-- as (269) there in either order, passes CCXZ (once squared away), and
-- is yB k.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.SemBoxes where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□ ; cf-Λ ; cf-B ; cf-W ; cf-V)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (B₁₀ ; module Forms)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals using (Ex₁₂ᴸ ; Ex₁₂ᴸ-def)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (cf-Λ↑)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place ; cyc ; cyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (yB ; cf-yB)

-- The box on wire 0 controlled by the wires 1 3 …, wire 2 idle.
C₀ : ∀ k → Circuit (₄₊ k)
C₀ k = place 2 (Λ□ (₂₊ k))

module _ (k : ℕ) where
  open Forms (₁₊ k)

  sem-B□² : ⟦ B□ k • B□ k ⟧ ~ ⟦ ε ⟧
  sem-B□² = cf-~ (cf-• (cf-B k) (cf-B k)) eps Eq.refl Eq.refl

  sem-B₁₀² : ⟦ B₁₀ (₁₊ k) • B₁₀ (₁₊ k) ⟧ ~ ⟦ ε ⟧
  sem-B₁₀² = cf-~ (cf-• b₁₀ b₁₀) eps Eq.refl Eq.refl

  sem-B₁₀-form : ⟦ CCZX • B₁₀ (₁₊ k) • CCXZ • B₁₀ (₁₊ k) ⟧ ~ ⟦ Λ□ (₃₊ k) ⟧
  sem-B₁₀-form = cf-~ (cf-• (cf-W k) (cf-• b₁₀ (cf-• (cf-V k) b₁₀))) (cf-Λ k) Eq.refl Eq.refl

  sem-yB-CZ : ⟦ CZ • yB k ⟧ ~ ⟦ yB k • CZ ⟧
  sem-yB-CZ = cf-~ (cf-• cz (cf-yB k)) (cf-• (cf-yB k) cz) Eq.refl Eq.refl

  sem-yB-CH : ⟦ CH • yB k ⟧ ~ ⟦ yB k • CH ⟧
  sem-yB-CH = cf-~ (cf-• ch (cf-yB k)) (cf-• (cf-yB k) ch) Eq.refl Eq.refl

  private
    ex₁₂ : CF {3} {₁₊ k} (Ex ↑)
    ex₁₂ = cf-loc′ (Ex ↑) Ex₁₂ᴸ Ex₁₂ᴸ-def

    cf-C₀ : CF {3} {₁₊ k} (C₀ k)
    cf-C₀ = cf-• (cf-• (cf-• eps ex₁₂) ex) (cf-• (cf-Λ↑ k) (cf-• ex (cf-• ex₁₂ eps)))

    a₀ : CF {3} {₁₊ k} (Ex ↓ • CCZX • Ex ↓)
    a₀ = cf-• ex (cf-• (cf-W k) ex)

    ā₀ : CF {3} {₁₊ k} (Ex ↓ • CCXZ • Ex ↓)
    ā₀ = cf-• ex (cf-• (cf-V k) ex)

  sem-294a : ⟦ (Ex ↓ • CCZX • Ex ↓) • C₀ k • (Ex ↓ • CCXZ • Ex ↓) • C₀ k ⟧ ~ ⟦ B₁₀ (₁₊ k) ⟧
  sem-294a = cf-~ (cf-• a₀ (cf-• cf-C₀ (cf-• ā₀ cf-C₀))) b₁₀ Eq.refl Eq.refl

  sem-294b : ⟦ C₀ k • (Ex ↓ • CCZX • Ex ↓) • C₀ k • (Ex ↓ • CCXZ • Ex ↓) ⟧ ~ ⟦ B₁₀ (₁₊ k) ⟧
  sem-294b = cf-~ (cf-• cf-C₀ (cf-• a₀ (cf-• cf-C₀ ā₀))) b₁₀ Eq.refl Eq.refl

  sem-294c : ⟦ C₀ k • CCXZ • C₀ k ⟧ ~ ⟦ CCXZ ⟧
  sem-294c = cf-~ (cf-• cf-C₀ (cf-• (cf-V k) cf-C₀)) (cf-V k) Eq.refl Eq.refl

  sem-C₀-yB : ⟦ C₀ k ⟧ ~ ⟦ yB k ⟧
  sem-C₀-yB = cf-~ cf-C₀ (cf-yB k) Eq.refl Eq.refl

  sem-C₀² : ⟦ C₀ k • C₀ k ⟧ ~ ⟦ ε ⟧
  sem-C₀² = cf-~ (cf-• cf-C₀ cf-C₀) eps Eq.refl Eq.refl
