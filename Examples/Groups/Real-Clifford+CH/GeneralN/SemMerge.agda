------------------------------------------------------------------------
-- Presentations of groups
--
-- The semantic steps of Equation (301), one width down
--
-- With the wire 2 of the full width removed: (305) there — the box on
-- wire 1 controlled by wire 0, between the singly controlled ZX and XZ
-- on wire 0, makes the box on wire 0 — and (304) there — that box
-- passes the singly controlled ZX.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.Real-Clifford+CH.GeneralN.SemMerge where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊)

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm
open import Examples.Groups.Real-Clifford+CH.GeneralN.Locals2
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (B₁₀ ; module Forms)

-- The singly controlled ZX and XZ on wire 0 from wire 1, at width 3 + k.
ZX₀ XZ₀ : ∀ k → Circuit (₃₊ k)
ZX₀ k = ΛZX 1 ↓ᵏ (₁₊ k)
XZ₀ k = ΛXZ 1 ↓ᵏ (₁₊ k)

module _ (k : ℕ) where
  open Forms k

  private
    zx : CF {3} {k} (ZX₀ k)
    zx = cf-loc′ (ΛZX 1 ↓ᵏ 1) ZX₀₁ᴸ ZX₀₁ᴸ-def

    xz : CF {3} {k} (XZ₀ k)
    xz = cf-loc′ (ΛXZ 1 ↓ᵏ 1) XZ₀₁ᴸ XZ₀₁ᴸ-def

  sem-305 : ⟦ XZ₀ k • B₁₀ k • ZX₀ k • B₁₀ k ⟧ ~ ⟦ Λ□ (₂₊ k) ⟧
  sem-305 = cf-~ (cf-• xz (cf-• b₁₀ (cf-• zx b₁₀))) box Eq.refl Eq.refl

  sem-304 : ⟦ Λ□ (₂₊ k) • ZX₀ k ⟧ ~ ⟦ ZX₀ k • Λ□ (₂₊ k) ⟧
  sem-304 = cf-~ (cf-• box zx) (cf-• zx box) Eq.refl Eq.refl
