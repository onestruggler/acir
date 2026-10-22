------------------------------------------------------------------------
-- Presentations of groups
--
-- Closed equations on a few wires, widened and placed
--
-- For each small width k: an equation of Five.Rules' theory between
-- circuits on k wires holds with r idle wires on top (`wkᵏ`, from
-- Five.Weakening's one wire at a time: `top (w ↓ᵏ r)` is `w ↓ᵏ suc r`),
-- so it holds placed by any network (`placedᵏ`); and an equation of
-- closed circuits on k wires with the same matrix holds given
-- completeness on k wires (`closedᵏ`).  The widths are numerals because
-- the two sides of `top (w ↓ᵏ r) ≡ w ↓ᵏ suc r` have one type only when k
-- is one.  Written by scratchpad/wide/gen_weaken.py.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Wide.Weaken where

open import Data.Nat using (ℕ ; zero ; suc) renaming (_+_ to _+ℕ_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; [_]ʷ ; ε ; _•_)

import Presentation.Base as PB
import Examples.Groups.Symmetric.Syntactics as S

open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (_↧ ; top)
open import Examples.Groups.Clifford+CS.SemanticSteps using (Complete ; Same ; same-sem)
open import Examples.Groups.Clifford+CS.LocalPlace using (pl)
open import Examples.Groups.Clifford+CS.Five.Rules using (_⊢ₓ_≈_ ; embed)
open import Examples.Groups.Clifford+CS.Five.Weakening using (top-congₓ)

------------------------------------------------------------------------
-- 0 wires

private
  tg₀ : ∀ r (g : Gen 0) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r
  tg₀ r (gate₀ h) = Eq.refl

  zg₀ : (g : Gen 0) → g ↧ᵏ 0 ≡ g
  zg₀ (gate₀ h) = Eq.refl

  tw₀ : ∀ r (w : Circuit 0) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r
  tw₀ r [ g ]ʷ  = Eq.cong [_]ʷ (tg₀ r g)
  tw₀ r ε       = Eq.refl
  tw₀ r (u • v) = Eq.cong₂ _•_ (tw₀ r u) (tw₀ r v)

  zw₀ : (w : Circuit 0) → w ↓ᵏ 0 ≡ w
  zw₀ [ g ]ʷ  = Eq.cong [_]ʷ (zg₀ g)
  zw₀ ε       = Eq.refl
  zw₀ (u • v) = Eq.cong₂ _•_ (zw₀ u) (zw₀ v)

wk₀ : ∀ r {u v : Circuit 0} → 0 ⊢ₓ u ≈ v → (0 +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r
wk₀ zero    {u} {v} e = Eq.subst₂ (0 ⊢ₓ_≈_) (Eq.sym (zw₀ u)) (Eq.sym (zw₀ v)) e
wk₀ (suc r) {u} {v} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw₀ r u) (tw₀ r v) (top-congₓ (wk₀ r e))

placed₀ : ∀ r (τ : Word (S.Gen (0 +ℕ r))) {u v : Circuit 0} → 0 ⊢ₓ u ≈ v →
          (0 +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)
placed₀ r τ e = PB.cong PB.refl (PB.cong (wk₀ r e) PB.refl)

closed₀ : Complete 0 → (u v : Circuit 0) → Same u v → 0 ⊢ₓ u ≈ v
closed₀ c u v e = embed (c (same-sem u v e))

------------------------------------------------------------------------
-- 1 wire

private
  tg₁ : ∀ r (g : Gen 1) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r
  tg₁ r (gate₀ h) = Eq.refl
  tg₁ r (gate₁ h) = Eq.refl
  tg₁ r (g ↥) = Eq.cong _↥ (tg₀ r g)

  zg₁ : (g : Gen 1) → g ↧ᵏ 0 ≡ g
  zg₁ (gate₀ h) = Eq.refl
  zg₁ (gate₁ h) = Eq.refl
  zg₁ (g ↥) = Eq.cong _↥ (zg₀ g)

  tw₁ : ∀ r (w : Circuit 1) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r
  tw₁ r [ g ]ʷ  = Eq.cong [_]ʷ (tg₁ r g)
  tw₁ r ε       = Eq.refl
  tw₁ r (u • v) = Eq.cong₂ _•_ (tw₁ r u) (tw₁ r v)

  zw₁ : (w : Circuit 1) → w ↓ᵏ 0 ≡ w
  zw₁ [ g ]ʷ  = Eq.cong [_]ʷ (zg₁ g)
  zw₁ ε       = Eq.refl
  zw₁ (u • v) = Eq.cong₂ _•_ (zw₁ u) (zw₁ v)

wk₁ : ∀ r {u v : Circuit 1} → 1 ⊢ₓ u ≈ v → (1 +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r
wk₁ zero    {u} {v} e = Eq.subst₂ (1 ⊢ₓ_≈_) (Eq.sym (zw₁ u)) (Eq.sym (zw₁ v)) e
wk₁ (suc r) {u} {v} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw₁ r u) (tw₁ r v) (top-congₓ (wk₁ r e))

placed₁ : ∀ r (τ : Word (S.Gen (1 +ℕ r))) {u v : Circuit 1} → 1 ⊢ₓ u ≈ v →
          (1 +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)
placed₁ r τ e = PB.cong PB.refl (PB.cong (wk₁ r e) PB.refl)

closed₁ : Complete 1 → (u v : Circuit 1) → Same u v → 1 ⊢ₓ u ≈ v
closed₁ c u v e = embed (c (same-sem u v e))

------------------------------------------------------------------------
-- 2 wires

private
  tg₂ : ∀ r (g : Gen 2) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r
  tg₂ r (gate₀ h) = Eq.refl
  tg₂ r (gate₁ h) = Eq.refl
  tg₂ r (gate₂ h) = Eq.refl
  tg₂ r (g ↥) = Eq.cong _↥ (tg₁ r g)

  zg₂ : (g : Gen 2) → g ↧ᵏ 0 ≡ g
  zg₂ (gate₀ h) = Eq.refl
  zg₂ (gate₁ h) = Eq.refl
  zg₂ (gate₂ h) = Eq.refl
  zg₂ (g ↥) = Eq.cong _↥ (zg₁ g)

  tw₂ : ∀ r (w : Circuit 2) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r
  tw₂ r [ g ]ʷ  = Eq.cong [_]ʷ (tg₂ r g)
  tw₂ r ε       = Eq.refl
  tw₂ r (u • v) = Eq.cong₂ _•_ (tw₂ r u) (tw₂ r v)

  zw₂ : (w : Circuit 2) → w ↓ᵏ 0 ≡ w
  zw₂ [ g ]ʷ  = Eq.cong [_]ʷ (zg₂ g)
  zw₂ ε       = Eq.refl
  zw₂ (u • v) = Eq.cong₂ _•_ (zw₂ u) (zw₂ v)

wk₂ : ∀ r {u v : Circuit 2} → 2 ⊢ₓ u ≈ v → (2 +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r
wk₂ zero    {u} {v} e = Eq.subst₂ (2 ⊢ₓ_≈_) (Eq.sym (zw₂ u)) (Eq.sym (zw₂ v)) e
wk₂ (suc r) {u} {v} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw₂ r u) (tw₂ r v) (top-congₓ (wk₂ r e))

placed₂ : ∀ r (τ : Word (S.Gen (2 +ℕ r))) {u v : Circuit 2} → 2 ⊢ₓ u ≈ v →
          (2 +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)
placed₂ r τ e = PB.cong PB.refl (PB.cong (wk₂ r e) PB.refl)

closed₂ : Complete 2 → (u v : Circuit 2) → Same u v → 2 ⊢ₓ u ≈ v
closed₂ c u v e = embed (c (same-sem u v e))

------------------------------------------------------------------------
-- 3 wires

private
  tg₃ : ∀ r (g : Gen 3) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r
  tg₃ r (gate₀ h) = Eq.refl
  tg₃ r (gate₁ h) = Eq.refl
  tg₃ r (gate₂ h) = Eq.refl
  tg₃ r (g ↥) = Eq.cong _↥ (tg₂ r g)

  zg₃ : (g : Gen 3) → g ↧ᵏ 0 ≡ g
  zg₃ (gate₀ h) = Eq.refl
  zg₃ (gate₁ h) = Eq.refl
  zg₃ (gate₂ h) = Eq.refl
  zg₃ (g ↥) = Eq.cong _↥ (zg₂ g)

  tw₃ : ∀ r (w : Circuit 3) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r
  tw₃ r [ g ]ʷ  = Eq.cong [_]ʷ (tg₃ r g)
  tw₃ r ε       = Eq.refl
  tw₃ r (u • v) = Eq.cong₂ _•_ (tw₃ r u) (tw₃ r v)

  zw₃ : (w : Circuit 3) → w ↓ᵏ 0 ≡ w
  zw₃ [ g ]ʷ  = Eq.cong [_]ʷ (zg₃ g)
  zw₃ ε       = Eq.refl
  zw₃ (u • v) = Eq.cong₂ _•_ (zw₃ u) (zw₃ v)

wk₃ : ∀ r {u v : Circuit 3} → 3 ⊢ₓ u ≈ v → (3 +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r
wk₃ zero    {u} {v} e = Eq.subst₂ (3 ⊢ₓ_≈_) (Eq.sym (zw₃ u)) (Eq.sym (zw₃ v)) e
wk₃ (suc r) {u} {v} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw₃ r u) (tw₃ r v) (top-congₓ (wk₃ r e))

placed₃ : ∀ r (τ : Word (S.Gen (3 +ℕ r))) {u v : Circuit 3} → 3 ⊢ₓ u ≈ v →
          (3 +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)
placed₃ r τ e = PB.cong PB.refl (PB.cong (wk₃ r e) PB.refl)

closed₃ : Complete 3 → (u v : Circuit 3) → Same u v → 3 ⊢ₓ u ≈ v
closed₃ c u v e = embed (c (same-sem u v e))

------------------------------------------------------------------------
-- 4 wires

private
  tg₄ : ∀ r (g : Gen 4) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r
  tg₄ r (gate₀ h) = Eq.refl
  tg₄ r (gate₁ h) = Eq.refl
  tg₄ r (gate₂ h) = Eq.refl
  tg₄ r (g ↥) = Eq.cong _↥ (tg₃ r g)

  zg₄ : (g : Gen 4) → g ↧ᵏ 0 ≡ g
  zg₄ (gate₀ h) = Eq.refl
  zg₄ (gate₁ h) = Eq.refl
  zg₄ (gate₂ h) = Eq.refl
  zg₄ (g ↥) = Eq.cong _↥ (zg₃ g)

  tw₄ : ∀ r (w : Circuit 4) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r
  tw₄ r [ g ]ʷ  = Eq.cong [_]ʷ (tg₄ r g)
  tw₄ r ε       = Eq.refl
  tw₄ r (u • v) = Eq.cong₂ _•_ (tw₄ r u) (tw₄ r v)

  zw₄ : (w : Circuit 4) → w ↓ᵏ 0 ≡ w
  zw₄ [ g ]ʷ  = Eq.cong [_]ʷ (zg₄ g)
  zw₄ ε       = Eq.refl
  zw₄ (u • v) = Eq.cong₂ _•_ (zw₄ u) (zw₄ v)

wk₄ : ∀ r {u v : Circuit 4} → 4 ⊢ₓ u ≈ v → (4 +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r
wk₄ zero    {u} {v} e = Eq.subst₂ (4 ⊢ₓ_≈_) (Eq.sym (zw₄ u)) (Eq.sym (zw₄ v)) e
wk₄ (suc r) {u} {v} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw₄ r u) (tw₄ r v) (top-congₓ (wk₄ r e))

placed₄ : ∀ r (τ : Word (S.Gen (4 +ℕ r))) {u v : Circuit 4} → 4 ⊢ₓ u ≈ v →
          (4 +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)
placed₄ r τ e = PB.cong PB.refl (PB.cong (wk₄ r e) PB.refl)

closed₄ : Complete 4 → (u v : Circuit 4) → Same u v → 4 ⊢ₓ u ≈ v
closed₄ c u v e = embed (c (same-sem u v e))

------------------------------------------------------------------------
-- 5 wires

private
  tg₅ : ∀ r (g : Gen 5) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r
  tg₅ r (gate₀ h) = Eq.refl
  tg₅ r (gate₁ h) = Eq.refl
  tg₅ r (gate₂ h) = Eq.refl
  tg₅ r (g ↥) = Eq.cong _↥ (tg₄ r g)

  zg₅ : (g : Gen 5) → g ↧ᵏ 0 ≡ g
  zg₅ (gate₀ h) = Eq.refl
  zg₅ (gate₁ h) = Eq.refl
  zg₅ (gate₂ h) = Eq.refl
  zg₅ (g ↥) = Eq.cong _↥ (zg₄ g)

  tw₅ : ∀ r (w : Circuit 5) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r
  tw₅ r [ g ]ʷ  = Eq.cong [_]ʷ (tg₅ r g)
  tw₅ r ε       = Eq.refl
  tw₅ r (u • v) = Eq.cong₂ _•_ (tw₅ r u) (tw₅ r v)

  zw₅ : (w : Circuit 5) → w ↓ᵏ 0 ≡ w
  zw₅ [ g ]ʷ  = Eq.cong [_]ʷ (zg₅ g)
  zw₅ ε       = Eq.refl
  zw₅ (u • v) = Eq.cong₂ _•_ (zw₅ u) (zw₅ v)

wk₅ : ∀ r {u v : Circuit 5} → 5 ⊢ₓ u ≈ v → (5 +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r
wk₅ zero    {u} {v} e = Eq.subst₂ (5 ⊢ₓ_≈_) (Eq.sym (zw₅ u)) (Eq.sym (zw₅ v)) e
wk₅ (suc r) {u} {v} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw₅ r u) (tw₅ r v) (top-congₓ (wk₅ r e))

placed₅ : ∀ r (τ : Word (S.Gen (5 +ℕ r))) {u v : Circuit 5} → 5 ⊢ₓ u ≈ v →
          (5 +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)
placed₅ r τ e = PB.cong PB.refl (PB.cong (wk₅ r e) PB.refl)

closed₅ : Complete 5 → (u v : Circuit 5) → Same u v → 5 ⊢ₓ u ≈ v
closed₅ c u v e = embed (c (same-sem u v e))

------------------------------------------------------------------------
-- 6 wires

private
  tg₆ : ∀ r (g : Gen 6) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r
  tg₆ r (gate₀ h) = Eq.refl
  tg₆ r (gate₁ h) = Eq.refl
  tg₆ r (gate₂ h) = Eq.refl
  tg₆ r (g ↥) = Eq.cong _↥ (tg₅ r g)

  zg₆ : (g : Gen 6) → g ↧ᵏ 0 ≡ g
  zg₆ (gate₀ h) = Eq.refl
  zg₆ (gate₁ h) = Eq.refl
  zg₆ (gate₂ h) = Eq.refl
  zg₆ (g ↥) = Eq.cong _↥ (zg₅ g)

  tw₆ : ∀ r (w : Circuit 6) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r
  tw₆ r [ g ]ʷ  = Eq.cong [_]ʷ (tg₆ r g)
  tw₆ r ε       = Eq.refl
  tw₆ r (u • v) = Eq.cong₂ _•_ (tw₆ r u) (tw₆ r v)

  zw₆ : (w : Circuit 6) → w ↓ᵏ 0 ≡ w
  zw₆ [ g ]ʷ  = Eq.cong [_]ʷ (zg₆ g)
  zw₆ ε       = Eq.refl
  zw₆ (u • v) = Eq.cong₂ _•_ (zw₆ u) (zw₆ v)

wk₆ : ∀ r {u v : Circuit 6} → 6 ⊢ₓ u ≈ v → (6 +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r
wk₆ zero    {u} {v} e = Eq.subst₂ (6 ⊢ₓ_≈_) (Eq.sym (zw₆ u)) (Eq.sym (zw₆ v)) e
wk₆ (suc r) {u} {v} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw₆ r u) (tw₆ r v) (top-congₓ (wk₆ r e))

placed₆ : ∀ r (τ : Word (S.Gen (6 +ℕ r))) {u v : Circuit 6} → 6 ⊢ₓ u ≈ v →
          (6 +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)
placed₆ r τ e = PB.cong PB.refl (PB.cong (wk₆ r e) PB.refl)

closed₆ : Complete 6 → (u v : Circuit 6) → Same u v → 6 ⊢ₓ u ≈ v
closed₆ c u v e = embed (c (same-sem u v e))

------------------------------------------------------------------------
-- 7 wires

private
  tg₇ : ∀ r (g : Gen 7) → (g ↧ᵏ r) ↧ ≡ g ↧ᵏ suc r
  tg₇ r (gate₀ h) = Eq.refl
  tg₇ r (gate₁ h) = Eq.refl
  tg₇ r (gate₂ h) = Eq.refl
  tg₇ r (g ↥) = Eq.cong _↥ (tg₆ r g)

  zg₇ : (g : Gen 7) → g ↧ᵏ 0 ≡ g
  zg₇ (gate₀ h) = Eq.refl
  zg₇ (gate₁ h) = Eq.refl
  zg₇ (gate₂ h) = Eq.refl
  zg₇ (g ↥) = Eq.cong _↥ (zg₆ g)

  tw₇ : ∀ r (w : Circuit 7) → top (w ↓ᵏ r) ≡ w ↓ᵏ suc r
  tw₇ r [ g ]ʷ  = Eq.cong [_]ʷ (tg₇ r g)
  tw₇ r ε       = Eq.refl
  tw₇ r (u • v) = Eq.cong₂ _•_ (tw₇ r u) (tw₇ r v)

  zw₇ : (w : Circuit 7) → w ↓ᵏ 0 ≡ w
  zw₇ [ g ]ʷ  = Eq.cong [_]ʷ (zg₇ g)
  zw₇ ε       = Eq.refl
  zw₇ (u • v) = Eq.cong₂ _•_ (zw₇ u) (zw₇ v)

wk₇ : ∀ r {u v : Circuit 7} → 7 ⊢ₓ u ≈ v → (7 +ℕ r) ⊢ₓ u ↓ᵏ r ≈ v ↓ᵏ r
wk₇ zero    {u} {v} e = Eq.subst₂ (7 ⊢ₓ_≈_) (Eq.sym (zw₇ u)) (Eq.sym (zw₇ v)) e
wk₇ (suc r) {u} {v} e = Eq.subst₂ (_ ⊢ₓ_≈_) (tw₇ r u) (tw₇ r v) (top-congₓ (wk₇ r e))

placed₇ : ∀ r (τ : Word (S.Gen (7 +ℕ r))) {u v : Circuit 7} → 7 ⊢ₓ u ≈ v →
          (7 +ℕ r) ⊢ₓ pl τ (u ↓ᵏ r) ≈ pl τ (v ↓ᵏ r)
placed₇ r τ e = PB.cong PB.refl (PB.cong (wk₇ r e) PB.refl)

closed₇ : Complete 7 → (u v : Circuit 7) → Same u v → 7 ⊢ₓ u ≈ v
closed₇ c u v e = embed (c (same-sem u v e))
