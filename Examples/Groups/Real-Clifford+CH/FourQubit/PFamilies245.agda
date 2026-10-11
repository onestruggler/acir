------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation between P ⊗ P on two of its controls
-- against one white on wire 3, on the same target (Clément, Lemma D.5,
-- Equation (245))
--
-- The first gate rotates wire 0 from the wires 1, 3 and, in either
-- colour, 2, and stands between P ⊗ P on the wires 1 2; the second
-- rotates wire 0 from wire 2, from wire 3 negatively, and from wire 1 in
-- either colour.
--
--   both black: the rotation is G₂ B G₂ B with the box wire of its H gate
--     on wire 2, (210) and (214).  Between P ⊗ P the box B becomes the
--     H gate H(2, 1; 0, 3) and G₂ the black version of the gate of (227);
--     the second gate is °G₂ °B °G₂ °B, white on wire 3; and the letters
--     pass each other — (205), (199), and the two facts behind (227)
--     with the colours on wire 3 exchanged.
--   the second gate white on wire 1: by the merge on wire 1 it is the
--     doubly controlled ZX from the wires 2 3, white on wire 3, times a
--     gate of the first kind; the first gate passes the former by (228),
--     under the middle swap.
--   the first gate white on wire 2: by the merge on wire 2 it is the
--     doubly controlled ZX from the wires 1 3 between P ⊗ P times a gate
--     of the first kind, and the second gate passes the former by (228).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies245
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; CCZX₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (eq199)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (S₀₁-N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (PP₁₂ ; PP₁₂² ; N₃-PP₁₂ ; G-PP ; eq205)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃
  using (CCZX₁₃ ; merge₀)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PConjugates complete₂ complete₃
  using (Y ; Y₁ ; Y₀ ; Y-B ; Y-G₂ ; eq228₁ ; eq228₀)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; rot)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
  using (merge₁ ; S₁₂-CCZX₁₃)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

module Pj {n : ℕ} = Conj {₄₊ n} PP₁₂ PP₁₂²

N₂ᵇ : Bool → Circuit (₄₊ n) → Circuit (₄₊ n)
N₂ᵇ true  w = w
N₂ᵇ false w = N₂.⟪ w ⟫

-- The first gate: the rotation of wire 0, its control on wire 2 of
-- either colour, between P ⊗ P on the wires 1 2.
F₂₄₅ : Bool → Bool → Circuit (₄₊ n)
F₂₄₅ α a = Pj.⟪ N₂ᵇ α (rot a) ⟫

-- The second gate: white on wire 3, either colour on wire 1.
S₂₄₅ : Bool → Bool → Circuit (₄₊ n)
S₂₄₅ β b = N₃.⟪ N₁ᵇ β (rot b) ⟫

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    B G₂ °B₃ °G₂ Yᵇ Jᵇ : Circuit (₄₊ n)
    B   = box₃′
    G₂  = S₁₂.⟪ ΛH₀₁ ⟫
    °B₃ = N₃.⟪ B ⟫
    °G₂ = N₃.⟪ G₂ ⟫
    Yᵇ  = Pj.⟪ G₂ ⟫
    Jᵇ  = S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫

    inv-row : ∀ {w v y : Circuit (₄₊ n)} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    conj-swap : ∀ {x y : Circuit (₄₊ n)} → x • y ≈ y • x → (w : Circuit (₄₊ n)) →
                x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎

    words : ∀ {x₁ x₂ y₁ y₂ : Circuit (₄₊ n)} →
            x₁ • y₁ ≈ y₁ • x₁ → x₁ • y₂ ≈ y₂ • x₁ → x₂ • y₁ ≈ y₁ • x₂ → x₂ • y₂ ≈ y₂ • x₂ →
            (x₁ • x₂ • x₁ • x₂) • (y₁ • y₂ • y₁ • y₂) ≈ (y₁ • y₂ • y₁ • y₂) • (x₁ • x₂ • x₁ • x₂)
    words e₁₁ e₁₂ e₂₁ e₂₂ =
      sym (comm-abab (sym (comm-abab e₁₁ e₁₂)) (sym (comm-abab e₂₁ e₂₂)))

    -- X on wire 3 and P ⊗ P on the wires 1 2.
    X₃-PP : X ↑ ↑ ↑ • PP₁₂ ≈ PP₁₂ • X ↑ ↑ ↑
    X₃-PP = N₃.⟪⟫-comm N₃-PP₁₂

    N₃-Pj : (w : Circuit (₄₊ n)) → N₃.⟪ Pj.⟪ w ⟫ ⟫ ≈ Pj.⟪ N₃.⟪ w ⟫ ⟫
    N₃-Pj = conj-swap X₃-PP

    --------------------------------------------------------------------
    -- Both gates black on the wires 2 and 1

    F-form : F₂₄₅ true true ≈ Yᵇ • Jᵇ • Yᵇ • Jᵇ
    F-form = trans (Pj.⟪⟫-cong ZX₃-form₄) (Pj.⟪⟫-•₄ refl (sym G-PP) refl (sym G-PP))

    S-form : S₂₄₅ true true ≈ °G₂ • °B₃ • °G₂ • °B₃
    S-form = trans (N₃.⟪⟫-cong ZX₃-form₄) (N₃.⟪⟫-•₄ refl refl refl refl)

    -- The letters.  The gate of (227) with the colours on wire 3
    -- exchanged …
    N₃-Y : N₃.⟪ Y ⟫ ≈ Yᵇ
    N₃-Y = trans (N₃-Pj (N₃.⟪ G₂ ⟫)) (Pj.⟪⟫-cong (N₃.⟪⟫-⟪⟫ G₂))

    Yᵇ-°G₂ : Yᵇ • °G₂ ≈ °G₂ • Yᵇ
    Yᵇ-°G₂ = N₃.⟪⟫-≈ Y-G₂ (N₃.⟪⟫-•₂ N₃-Y refl) (N₃.⟪⟫-•₂ refl N₃-Y)

    Yᵇ-°B₃ : Yᵇ • °B₃ ≈ °B₃ • Yᵇ
    Yᵇ-°B₃ = N₃.⟪⟫-≈ Y-B (N₃.⟪⟫-•₂ N₃-Y refl) (N₃.⟪⟫-•₂ refl N₃-Y)

    -- … and (205), (199).
    Jᵇ-°B₃ : Jᵇ • °B₃ ≈ °B₃ • Jᵇ
    Jᵇ-°B₃ = trans (back _ (sym (S₀₁-N₃ box₃))) (trans eq199 (front _ (S₀₁-N₃ box₃)))

    base : F₂₄₅ true true • S₂₄₅ true true ≈ S₂₄₅ true true • F₂₄₅ true true
    base = begin
      F₂₄₅ true true • S₂₄₅ true true
        ≈⟨ cong F-form S-form ⟩
      (Yᵇ • Jᵇ • Yᵇ • Jᵇ) • (°G₂ • °B₃ • °G₂ • °B₃)
        ≈⟨ words Yᵇ-°G₂ Yᵇ-°B₃ eq205 Jᵇ-°B₃ ⟩
      (°G₂ • °B₃ • °G₂ • °B₃) • (Yᵇ • Jᵇ • Yᵇ • Jᵇ)
        ≈⟨ sym (cong S-form F-form) ⟩
      S₂₄₅ true true • F₂₄₅ true true ∎

    --------------------------------------------------------------------
    -- Inverses

    N₁ᵇ-inv : ∀ β {u v : Circuit (₄₊ n)} → u • v ≈ ε → N₁ᵇ β u • N₁ᵇ β v ≈ ε
    N₁ᵇ-inv true  e = e
    N₁ᵇ-inv false {u} {v} e = trans (sym (N₁.⟪⟫-• u v)) (trans (N₁.⟪⟫-cong e) N₁.⟪⟫-ε)

    N₂ᵇ-inv : ∀ α {u v : Circuit (₄₊ n)} → u • v ≈ ε → N₂ᵇ α u • N₂ᵇ α v ≈ ε
    N₂ᵇ-inv true  e = e
    N₂ᵇ-inv false {u} {v} e = trans (sym (N₂.⟪⟫-• u v)) (trans (N₂.⟪⟫-cong e) N₂.⟪⟫-ε)

    S-inv : ∀ β → S₂₄₅ β true • S₂₄₅ β false ≈ ε
    S-inv β = trans (sym (N₃.⟪⟫-• _ _)) (trans (N₃.⟪⟫-cong (N₁ᵇ-inv β eq208′)) N₃.⟪⟫-ε)

    S-inv′ : ∀ β → S₂₄₅ β false • S₂₄₅ β true ≈ ε
    S-inv′ β = trans (sym (N₃.⟪⟫-• _ _)) (trans (N₃.⟪⟫-cong (N₁ᵇ-inv β eq208)) N₃.⟪⟫-ε)

    F-inv : ∀ α → F₂₄₅ α true • F₂₄₅ α false ≈ ε
    F-inv α = trans (sym (Pj.⟪⟫-• _ _)) (trans (Pj.⟪⟫-cong (N₂ᵇ-inv α eq208′)) Pj.⟪⟫-ε)

    F-inv′ : ∀ α → F₂₄₅ α false • F₂₄₅ α true ≈ ε
    F-inv′ α = trans (sym (Pj.⟪⟫-• _ _)) (trans (Pj.⟪⟫-cong (N₂ᵇ-inv α eq208)) Pj.⟪⟫-ε)

    --------------------------------------------------------------------
    -- The second gate white on wire 1

    N₁ZX₃-form : N₁.⟪ ZX₃ ⟫ ≈ CCZX₂₃ • XZ₃
    N₁ZX₃-form = begin
      N₁.⟪ ZX₃ ⟫                    ≈⟨ sym right-unit ⟩
      N₁.⟪ ZX₃ ⟫ • ε                ≈⟨ back _ (sym eq208′) ⟩
      N₁.⟪ ZX₃ ⟫ • ZX₃ • XZ₃        ≈⟨ sym assoc ⟩
      (N₁.⟪ ZX₃ ⟫ • ZX₃) • XZ₃      ≈⟨ front _ merge₁ ⟩
      CCZX₂₃ • XZ₃ ∎

    S-white : S₂₄₅ false true ≈ N₃.⟪ CCZX₂₃ ⟫ • S₂₄₅ true false
    S-white = trans (N₃.⟪⟫-cong N₁ZX₃-form) (N₃.⟪⟫-• CCZX₂₃ XZ₃)

    -- (228) under the middle swap, then with the colours on wire 3
    -- exchanged.
    S₁₂-PP : S₁₂.⟪ PP₁₂ ⟫ ≈ PP₁₂
    S₁₂-PP = U-sem (Ex • PP • Ex) PP Eq.refl

    S₁₂-Y₁ : S₁₂.⟪ Y₁ ⟫ ≈ Y₁
    S₁₂-Y₁ = S₁₂.⟪⟫-•₃ S₁₂-PP (S₁₂.⟪⟫-•₃ S₁₂-X₃ S₁₂-ZX₃ S₁₂-X₃) S₁₂-PP

    Y₁-W₂₃ : Y₁ • CCZX₂₃ ≈ CCZX₂₃ • Y₁
    Y₁-W₂₃ = S₁₂.⟪⟫-≈ eq228₁ (S₁₂.⟪⟫-•₂ S₁₂-Y₁ S₁₂-CCZX₁₃) (S₁₂.⟪⟫-•₂ S₁₂-CCZX₁₃ S₁₂-Y₁)

    N₃-Y₁ : N₃.⟪ Y₁ ⟫ ≈ F₂₄₅ true true
    N₃-Y₁ = trans (N₃-Pj (N₃.⟪ ZX₃ ⟫)) (Pj.⟪⟫-cong (N₃.⟪⟫-⟪⟫ ZX₃))

    F-°W₂₃ : F₂₄₅ true true • N₃.⟪ CCZX₂₃ ⟫ ≈ N₃.⟪ CCZX₂₃ ⟫ • F₂₄₅ true true
    F-°W₂₃ = N₃.⟪⟫-≈ Y₁-W₂₃ (N₃.⟪⟫-•₂ N₃-Y₁ refl) (N₃.⟪⟫-•₂ refl N₃-Y₁)

    black-ZX : ∀ β → F₂₄₅ true true • S₂₄₅ β true ≈ S₂₄₅ β true • F₂₄₅ true true
    black-ZX true  = base
    black-ZX false = begin
      F₂₄₅ true true • S₂₄₅ false true
        ≈⟨ back _ S-white ⟩
      F₂₄₅ true true • (N₃.⟪ CCZX₂₃ ⟫ • S₂₄₅ true false)
        ≈⟨ comm-• F-°W₂₃ (comm-inv (S-inv true) (S-inv′ true) base) ⟩
      (N₃.⟪ CCZX₂₃ ⟫ • S₂₄₅ true false) • F₂₄₅ true true
        ≈⟨ front _ (sym S-white) ⟩
      S₂₄₅ false true • F₂₄₅ true true ∎

    black₁ : ∀ β b → F₂₄₅ true true • S₂₄₅ β b ≈ S₂₄₅ β b • F₂₄₅ true true
    black₁ β true  = black-ZX β
    black₁ β false = comm-inv (S-inv β) (S-inv′ β) (black-ZX β)

    black : ∀ β a b → F₂₄₅ true a • S₂₄₅ β b ≈ S₂₄₅ β b • F₂₄₅ true a
    black β true  b = black₁ β b
    black β false b = inv-row (F-inv true) (F-inv′ true) (black₁ β b)

    --------------------------------------------------------------------
    -- The first gate white on wire 2

    N₂ZX₃-form : N₂.⟪ ZX₃ ⟫ ≈ CCZX₁₃ • XZ₃
    N₂ZX₃-form = begin
      N₂.⟪ ZX₃ ⟫                    ≈⟨ sym right-unit ⟩
      N₂.⟪ ZX₃ ⟫ • ε                ≈⟨ back _ (sym eq208′) ⟩
      N₂.⟪ ZX₃ ⟫ • ZX₃ • XZ₃        ≈⟨ sym assoc ⟩
      (N₂.⟪ ZX₃ ⟫ • ZX₃) • XZ₃      ≈⟨ front _ merge₀ ⟩
      CCZX₁₃ • XZ₃ ∎

    F-white : F₂₄₅ false true ≈ Pj.⟪ CCZX₁₃ ⟫ • F₂₄₅ true false
    F-white = trans (Pj.⟪⟫-cong N₂ZX₃-form) (Pj.⟪⟫-• CCZX₁₃ XZ₃)

    -- (228) between P ⊗ P.
    PN-S : ∀ β → Pj.⟪ CCZX₁₃ ⟫ • S₂₄₅ β true ≈ S₂₄₅ β true • Pj.⟪ CCZX₁₃ ⟫
    PN-S true  = sym (Pj.⟪⟫-≈ eq228₁ (Pj.⟪⟫-•₂ (Pj.⟪⟫-⟪⟫ _) refl) (Pj.⟪⟫-•₂ refl (Pj.⟪⟫-⟪⟫ _)))
    PN-S false = sym (Pj.⟪⟫-≈ eq228₀ (Pj.⟪⟫-•₂ (Pj.⟪⟫-⟪⟫ _) refl) (Pj.⟪⟫-•₂ refl (Pj.⟪⟫-⟪⟫ _)))

    PN-S′ : ∀ β b → Pj.⟪ CCZX₁₃ ⟫ • S₂₄₅ β b ≈ S₂₄₅ β b • Pj.⟪ CCZX₁₃ ⟫
    PN-S′ β true  = PN-S β
    PN-S′ β false = comm-inv (S-inv β) (S-inv′ β) (PN-S β)

    white-ZX : ∀ β b → F₂₄₅ false true • S₂₄₅ β b ≈ S₂₄₅ β b • F₂₄₅ false true
    white-ZX β b = begin
      F₂₄₅ false true • S₂₄₅ β b
        ≈⟨ front _ F-white ⟩
      (Pj.⟪ CCZX₁₃ ⟫ • F₂₄₅ true false) • S₂₄₅ β b
        ≈⟨ sym (comm-• (sym (PN-S′ β b)) (sym (black β false b))) ⟩
      S₂₄₅ β b • (Pj.⟪ CCZX₁₃ ⟫ • F₂₄₅ true false)
        ≈⟨ back _ (sym F-white) ⟩
      S₂₄₅ β b • F₂₄₅ false true ∎

  -- The second gate and its inverse, for (244).
  S₂₄₅-inv : ∀ β → S₂₄₅ β true • S₂₄₅ β false ≈ ε
  S₂₄₅-inv = S-inv

  S₂₄₅-inv′ : ∀ β → S₂₄₅ β false • S₂₄₅ β true ≈ ε
  S₂₄₅-inv′ = S-inv′

  N₂ᵇ-cancel : ∀ α {u v : Circuit (₄₊ n)} → u • v ≈ ε → N₂ᵇ α u • N₂ᵇ α v ≈ ε
  N₂ᵇ-cancel = N₂ᵇ-inv

  -- The merge on wire 2, solved for the white rotation.
  N₂-ZX₃-split : N₂.⟪ ZX₃ ⟫ ≈ CCZX₁₃ • XZ₃
  N₂-ZX₃-split = N₂ZX₃-form

  -- (245)
  eq245 : ∀ α β a b → F₂₄₅ α a • S₂₄₅ β b ≈ S₂₄₅ β b • F₂₄₅ α a
  eq245 true  β a     b = black β a b
  eq245 false β true  b = white-ZX β b
  eq245 false β false b = inv-row (F-inv false) (F-inv′ false) (white-ZX β b)
