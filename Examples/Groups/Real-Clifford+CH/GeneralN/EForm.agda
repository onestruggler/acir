------------------------------------------------------------------------
-- Presentations of groups
--
-- The box with a multi-controlled H in place of its inner letter
-- (Clément, Lemma D.8, Equation (284)), and what follows from it
--
-- (269) writes the box on k + 4 wires as W B V B, with W and V the
-- doubly controlled ZX and XZ on wire 0 and B the smaller box, met on
-- wire 1 between the transposition of the wires 0 2.  (284) is the same
-- with B replaced by
--
--     E□ k  =  PP ↓ • B□ k • PP ↓,
--
-- the multi-controlled H with its H on wire 0, its box wire on wire 1
-- and its controls on the wires 3 … k + 3 — the general form of the
-- four-qubit (153), where E□ 0 is the CH from wire 3.
--
-- (284) is the keystone of Lemma D.8, and the paper reaches it only
-- through (283).  It is stated here in its two halves, `Eq284` and its
-- mirror `Eq284′`, because everything below it needs exactly those:
--
--   * (285), H on the box wire passes the box, is `box-pass` — H ↓
--     exchanges W and V, and passes E because between P ⊗ P it is Z on
--     a control of B, (270).  Its flip hypothesis V E W ≈ W E V is the
--     two halves with one E cancelled on the right.
--   * (274) and (275) then follow, in `BoxWire`.
--
-- So the whole of this part of Lemma D.8 rests on the two halves of
-- (284), and on nothing else that is not already proved.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.EForm
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Fin using (zero)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (WRel ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Presentation.GroupLike using (module Basis-Change)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (H↓-CCZX ; H↓-CCXZ)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
  using (L-sem ; L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃
  using (B□ ; eq270)
open import Examples.Groups.Real-Clifford+CH.GeneralN.HGate complete₂ complete₃
  using (through)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxWire complete₂ complete₃
  using (Eq285)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The multi-controlled H that replaces the box's inner letter

-- Its H is on wire 0, its box wire is wire 1 and its controls are the
-- wires 3 … k + 3: the letter B between P ⊗ P on the wires 0 1, which
-- turns B's control on wire 0 into an H there.
E□ : ∀ k → Circuit (₄₊ k)
E□ k = PP ↓ • B□ k • PP ↓

-- (284) and its mirror.
Eq284 Eq284′ : ℕ → Set
Eq284  k = (₄₊ k) ⊢ Λ□ (₃₊ k) ≈ CCZX • E□ k • CCXZ • E□ k
Eq284′ k = (₄₊ k) ⊢ Λ□ (₃₊ k) ≈ CCXZ • E□ k • CCZX • E□ k

------------------------------------------------------------------------
-- H on the box wire passes E

private
  -- Between P ⊗ P, H is Z: (113).
  H₀-PP : (₃₊ n) ⊢ H ↓ • PP ↓ ≈ PP ↓ • Z ↓
  H₀-PP = L-sem (H ↓ • PP) (PP • Z ↓) Eq.refl

  Z₀-PP : (₃₊ n) ⊢ Z ↓ • PP ↓ ≈ PP ↓ • H ↓
  Z₀-PP = L-sem (Z ↓ • PP) (PP • H ↓) Eq.refl

  τ₀₂² : (₄₊ n) ⊢ τ₀₂ • τ₀₂ ≈ ε
  τ₀₂² {n} = conj-invol Ex² (lemma-cong↑ (Ex • Ex) ε Ex²)
    where open Tools ((₄₊ n) VRel,_===_)

  module T {n : ℕ} = Conj {₄₊ n} τ₀₂ τ₀₂²

  T-Z₂ : (₄₊ n) ⊢ T.⟪ Z ↑ ↑ ⟫ ≈ Z ↓
  T-Z₂ = L₃-sem (τ₀₂ • Z ↑ ↑ • τ₀₂) (Z ↓) Eq.refl

-- Z on wire 0 is, under the transposition, Z on the first control of
-- the smaller box: (270).
Z↓-B□ : ∀ k → (₄₊ k) ⊢ Z ↓ • B□ k ≈ B□ k • Z ↓
Z↓-B□ k = T.⟪⟫-≈ (lemma-cong↑ (Z ↑ • Λ□ (₂₊ k)) (Λ□ (₂₊ k) • Z ↑) (eq270 (₂₊ k) zero))
                 (T.⟪⟫-•₂ T-Z₂ refl) (T.⟪⟫-•₂ refl T-Z₂)
  where open Tools ((₄₊ k) VRel,_===_)

H↓-E□ : ∀ k → (₄₊ k) ⊢ H ↓ • E□ k ≈ E□ k • H ↓
H↓-E□ k = through ((₄₊ k) VRel,_===_) H₀-PP Z₀-PP (Z↓-B□ k)

------------------------------------------------------------------------
-- (285), from the two halves of (284)

-- The two halves with one E cancelled on the right.
flipE : ∀ k → Eq284 k → Eq284′ k →
        (₄₊ k) ⊢ CCXZ • E□ k • CCZX ≈ CCZX • E□ k • CCXZ
flipE k e e′ = bbc ε (E□ k) (back ε (begin
  (CCXZ • E□ k • CCZX) • E□ k     ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  CCXZ • E□ k • CCZX • E□ k       ≈⟨ sym e′ ⟩
  Λ□ (₃₊ k)                       ≈⟨ e ⟩
  CCZX • E□ k • CCXZ • E□ k       ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
  (CCZX • E□ k • CCXZ) • E□ k ∎))
  where
  Γ = (₄₊ k) VRel,_===_
  open Tools Γ
  open Basis-Change (Gen (₄₊ k)) Γ grouplike using (bbc)

eq285 : ∀ k → Eq284 k → Eq284′ k → Eq285 k
eq285 k e e′ = begin
  H ↓ • Λ□ (₃₊ k)
    ≈⟨ back _ e ⟩
  H ↓ • (CCZX • E□ k • CCXZ • E□ k)
    ≈⟨ box-pass H↓-CCZX H↓-CCXZ (H↓-E□ k) (flipE k e e′) ⟩
  (CCZX • E□ k • CCXZ • E□ k) • H ↓
    ≈⟨ front _ (sym e) ⟩
  Λ□ (₃₊ k) • H ↓ ∎
  where
  open Tools ((₄₊ k) VRel,_===_)
  open Alg ((₄₊ k) VRel,_===_)
