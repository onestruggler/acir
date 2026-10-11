------------------------------------------------------------------------
-- Presentations of groups
--
-- More gates against the triply controlled rotations (Clément, Lemma
-- D.5, Equations (234)–(238))
--
--   (234), (235)   the CH onto wire 0 from wire 2, negated there, passes
--                  the triply controlled ZX and XZ on wire 1
--   (236)   H on the target exchanges ZX and XZ
--   (237)   so does Z
--   (238)   and X
--
-- (234): the rotation in the form of (212), whose H gate the CH passes as
-- in (216).  (236): H is the CH from wire 1 times the same negated; the
-- first is a letter of the definition a B a B, which it turns over, and
-- the second passes, (232) under the symmetry (215).  (237): likewise Z is
-- the CZ from wire 3 times the same negated, a letter of (213) and (231).
-- (238): X = H Z H.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Rotations5
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; CH² ; S-Z↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (CZ₃₀ ; CZ₃₀² ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃
  using (CH₂₀-S₀₁°ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃
  using (Kᵇ ; Kᵇ′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations4 complete₂ complete₃
  using (eq231 ; eq232 ; °CH₂₀-as-O)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; °CH₂₀)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    a B G c t₀ : Circuit (₄₊ n)
    a  = CH ↓
    B  = box₃′
    G  = ΛH₂′
    c  = CZ₃₀
    t₀ = °CH₂₀

  ----------------------------------------------------------------------
  -- (234), (235)

  private
    G′ c′ : Circuit (₄₊ n)
    G′ = S₀₁.⟪ ΛH₂′ ⟫
    c′ = P₁₃ CZ

    S₀₁-c : S₀₁.⟪ c ⟫ ≈ c′
    S₀₁-c = trans (S₀₁.⟪⟫-cong CZ₃₀-P) (S₀₁.⟪⟫-⟪⟫ c′)

    Kᵇ-form : Kᵇ ≈ G′ • c′ • G′ • c′
    Kᵇ-form = trans (S₀₁.⟪⟫-cong eq212) (S₀₁.⟪⟫-•₄ refl S₀₁-c refl S₀₁-c)

    N₂-Ex : N₂.⟪ Ex ↓ ⟫ ≈ Ex ↓
    N₂-Ex = N₂.⟪⟫-fix (sym (L-comm Ex X))

    -- As in (216), with the colours on wire 2 exchanged.
    t₀-G′ : t₀ • G′ ≈ G′ • t₀
    t₀-G′ = N₂.⟪⟫-≈ CH₂₀-S₀₁°ΛH₂′ (N₂.⟪⟫-•₂ refl m) (N₂.⟪⟫-•₂ m refl)
      where
      m : N₂.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ≈ G′
      m = trans (N₂.⟪⟫-•₃ N₂-Ex refl N₂-Ex) (S₀₁.⟪⟫-cong (N₂.⟪⟫-⟪⟫ ΛH₂′))

    t₀-c′ : t₀ • c′ ≈ c′ • t₀
    t₀-c′ = begin
      t₀ • c′          ≈⟨ front _ °CH₂₀-as-O ⟩
      O °CH • c′       ≈⟨ sym (P₁₃-O CZ °CH) ⟩
      c′ • O °CH       ≈⟨ back _ (sym °CH₂₀-as-O) ⟩
      c′ • t₀ ∎

    KᵇKᵇ′ : Kᵇ • Kᵇ′ ≈ ε
    KᵇKᵇ′ = trans (sym (S₀₁.⟪⟫-• ZX₃ XZ₃)) (trans (S₀₁.⟪⟫-cong eq208′) S₀₁.⟪⟫-ε)

    Kᵇ′Kᵇ : Kᵇ′ • Kᵇ ≈ ε
    Kᵇ′Kᵇ = trans (sym (S₀₁.⟪⟫-• XZ₃ ZX₃)) (trans (S₀₁.⟪⟫-cong eq208) S₀₁.⟪⟫-ε)

  eq234 : t₀ • Kᵇ ≈ Kᵇ • t₀
  eq234 = begin
    t₀ • Kᵇ                        ≈⟨ back _ Kᵇ-form ⟩
    t₀ • (G′ • c′ • G′ • c′)       ≈⟨ comm-abab t₀-G′ t₀-c′ ⟩
    (G′ • c′ • G′ • c′) • t₀       ≈⟨ front _ (sym Kᵇ-form) ⟩
    Kᵇ • t₀ ∎

  eq235 : t₀ • Kᵇ′ ≈ Kᵇ′ • t₀
  eq235 = comm-inv KᵇKᵇ′ Kᵇ′Kᵇ eq234

  ----------------------------------------------------------------------
  -- (236)

  private
    °a : Circuit (₄₊ n)
    °a = L °CH

    -- H on wire 0 is the CH from wire 1 in both colours.
    h-form : H ↓ ≈ °a • a
    h-form = L-sem (H ↓) (°CH • CH) Eq.refl

    h-form′ : H ↓ ≈ a • °a
    h-form′ = L-sem (H ↓) (CH • °CH) Eq.refl

    -- (232) under the middle swap: the white CH from wire 1.
    °a-ZX₃ : °a • ZX₃ ≈ ZX₃ • °a
    °a-ZX₃ = S₁₂.⟪⟫-≈ eq232 (S₁₂.⟪⟫-•₂ m S₁₂-ZX₃) (S₁₂.⟪⟫-•₂ S₁₂-ZX₃ m)
      where
      m : S₁₂.⟪ °CH₂₀ ⟫ ≈ °a
      m = S₁₂.⟪⟫-•₃ S₁₂-X₂ (trans (S₁₂.⟪⟫-cong (sym (O-L CH))) (S₁₂.⟪⟫-⟪⟫ (L CH))) S₁₂-X₂

    °a-XZ₃ : °a • XZ₃ ≈ XZ₃ • °a
    °a-XZ₃ = comm-inv eq208′ eq208 °a-ZX₃

    -- The black one is a letter of the definition.
    a-ZX₃ : a • ZX₃ ≈ XZ₃ • a
    a-ZX₃ = begin
      a • (a • B • a • B)       ≈⟨ sym assoc ⟩
      (a • a) • B • a • B       ≈⟨ trans (front _ CH²) left-unit ⟩
      B • a • B                 ≈⟨ sym (trans (back _ (back _ (trans (back _ CH²) right-unit))) refl) ⟩
      B • a • B • a • a         ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □ • □) • □) Eq.refl ⟩
      (B • a • B • a) • a ∎

  eq236 : H ↓ • ZX₃ ≈ XZ₃ • H ↓
  eq236 = begin
    H ↓ • ZX₃               ≈⟨ front _ h-form ⟩
    (°a • a) • ZX₃          ≈⟨ assoc ⟩
    °a • a • ZX₃            ≈⟨ back _ a-ZX₃ ⟩
    °a • XZ₃ • a            ≈⟨ sym assoc ⟩
    (°a • XZ₃) • a          ≈⟨ front _ °a-XZ₃ ⟩
    (XZ₃ • °a) • a          ≈⟨ assoc ⟩
    XZ₃ • °a • a            ≈⟨ back _ (sym h-form) ⟩
    XZ₃ • H ↓ ∎

  ----------------------------------------------------------------------
  -- (237)

  private
    °c : Circuit (₄₊ n)
    °c = P₀₃ °CZ

    -- A gate on the lower wire of the pair 0 3 is the gate on wire 0.
    P₀₃-Z↓ : P₀₃ (Z ↓) ≈ Z ↓
    P₀₃-Z↓ = trans (S₀₁.⟪⟫-cong (lemma-cong↑ (Ex • Z ↑ • Ex) (Z ↓) S-Z↑)) S-Z↑

    -- Z on wire 0 is the CZ from wire 3 in both colours.
    z-form : Z ↓ ≈ °c • c
    z-form = sym (begin
      °c • c                ≈⟨ back _ CZ₃₀-P ⟩
      P₀₃ °CZ • P₀₃ CZ      ≈⟨ sym (P₀₃-• °CZ CZ) ⟩
      P₀₃ (°CZ • CZ)        ≈⟨ P₀₃-sem (°CZ • CZ) (Z ↓) Eq.refl ⟩
      P₀₃ (Z ↓)             ≈⟨ P₀₃-Z↓ ⟩
      Z ↓ ∎)

    °c-ZX₃ : °c • ZX₃ ≈ ZX₃ • °c
    °c-ZX₃ = comm-inv eq208 eq208′ eq231

    -- The black one is a letter of (213).
    c-XZ₃ : c • XZ₃ ≈ ZX₃ • c
    c-XZ₃ = begin
      c • XZ₃                   ≈⟨ back _ eq213 ⟩
      c • (c • G • c • G)       ≈⟨ sym assoc ⟩
      (c • c) • G • c • G       ≈⟨ trans (front _ CZ₃₀²) left-unit ⟩
      G • c • G                 ≈⟨ sym (trans (back _ (back _ (trans (back _ CZ₃₀²) right-unit))) refl) ⟩
      G • c • G • c • c         ≈⟨ by-passoc (□ • □ • □ • □ • □) ((□ • □ • □ • □) • □) Eq.refl ⟩
      (G • c • G • c) • c       ≈⟨ front _ (sym eq212) ⟩
      ZX₃ • c ∎

  eq237 : Z ↓ • XZ₃ ≈ ZX₃ • Z ↓
  eq237 = begin
    Z ↓ • XZ₃               ≈⟨ front _ z-form ⟩
    (°c • c) • XZ₃          ≈⟨ assoc ⟩
    °c • c • XZ₃            ≈⟨ back _ c-XZ₃ ⟩
    °c • ZX₃ • c            ≈⟨ sym assoc ⟩
    (°c • ZX₃) • c          ≈⟨ front _ °c-ZX₃ ⟩
    (ZX₃ • °c) • c          ≈⟨ assoc ⟩
    ZX₃ • °c • c            ≈⟨ back _ (sym z-form) ⟩
    ZX₃ • Z ↓ ∎

  ----------------------------------------------------------------------
  -- (238)

  private
    eq236′ : H ↓ • XZ₃ ≈ ZX₃ • H ↓
    eq236′ = begin
      H ↓ • XZ₃               ≈⟨ front _ h-form′ ⟩
      (a • °a) • XZ₃          ≈⟨ assoc ⟩
      a • °a • XZ₃            ≈⟨ back _ °a-XZ₃ ⟩
      a • XZ₃ • °a            ≈⟨ sym assoc ⟩
      (a • XZ₃) • °a          ≈⟨ front _ a-XZ₃ ⟩
      (ZX₃ • a) • °a          ≈⟨ assoc ⟩
      ZX₃ • a • °a            ≈⟨ back _ (sym h-form′) ⟩
      ZX₃ • H ↓ ∎
      where
      a-XZ₃ : a • XZ₃ ≈ ZX₃ • a
      a-XZ₃ = begin
        a • (B • a • B • a)       ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
        (a • B • a • B) • a ∎

  -- X = H Z H.
  eq238 : X ↓ • ZX₃ ≈ XZ₃ • X ↓
  eq238 = begin
    (H ↓ • Z ↓ • H ↓) • ZX₃
      ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    H ↓ • Z ↓ • (H ↓ • ZX₃)
      ≈⟨ back _ (back _ eq236) ⟩
    H ↓ • Z ↓ • (XZ₃ • H ↓)
      ≈⟨ by-passoc (□ • □ • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
    H ↓ • (Z ↓ • XZ₃) • H ↓
      ≈⟨ back _ (front _ eq237) ⟩
    H ↓ • (ZX₃ • Z ↓) • H ↓
      ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
    (H ↓ • ZX₃) • Z ↓ • H ↓
      ≈⟨ front _ eq236 ⟩
    (XZ₃ • H ↓) • Z ↓ • H ↓
      ≈⟨ assoc ⟩
    XZ₃ • (H ↓ • Z ↓ • H ↓) ∎
