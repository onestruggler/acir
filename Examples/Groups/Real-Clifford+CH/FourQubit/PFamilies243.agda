------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation between P ⊗ P against one of the other
-- colour on the same target (Clément, Lemma D.5, Equation (243))
--
-- The first gate is that of (241) between P ⊗ P on the wires 0 1, the
-- second that of (241).  X on wire 3 passes P ⊗ P and exchanges the
-- colours of both gates there; ZX and XZ are inverse.  A white control
-- of the first gate on wire 1 adds a doubly controlled XZ from the wires
-- 2 3 (`Aᴾ-white`), which is the merge of two gates of (241) and so
-- passes the second gate.  With the first gate black, G′ P G′ P:
--
--   the second gate black on wire 1: it is °G °B °G °B, (210), or with
--     the box white on wire 3 as well, and every letter of the first
--     passes every letter of the second — (203), (192), (202), (196),
--     (197);
--   white on wire 1: by the merge on wire 1 it is the doubly controlled
--     ZX from the wires 2 3, white on wire 2, times a gate of the first
--     kind; between P ⊗ P that doubly controlled ZX is turned over,
--     (174), and the rotation passes it by (239).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies243
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; S-X↓ ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; CCZX₂₃ ; CCXZ₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; °°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (N₂-box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (eq192 ; eq196 ; eq197)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; N₂-PP₀₁ ; S₀₁-N₃ ; eq202)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (eq203 ; eq207)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families complete₂ complete₃
  using (R₁ ; R₁′ ; R₀ ; R₀′ ; eq239₁′ ; eq239₀′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; N₃ᵇ ; rot ; A₂₄₁ ; C₂₄₁ ; C₂₄₁-inv ; C₂₄₁-inv′ ; eq241)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂ ; eq117 ; eq118)
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
    G °G G′ P B °B °°B °Z °Z′ : Circuit (₄₊ n)
    G   = ΛH₂′
    °G  = °ΛH₂′
    G′  = S₀₁.⟪ ΛH₂′ ⟫
    P   = ΛH₀₁
    B   = box₃′
    °B  = S₀₁.⟪ °box₃ ⟫
    °°B = S₀₁.⟪ °°box₃ ⟫
    °Z  = N₂.⟪ ZX₃ ⟫
    °Z′ = N₂.⟪ XZ₃ ⟫

    inv-row : ∀ {w v y : Circuit (₄₊ n)} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    conj-swap : ∀ {x y : Circuit (₄₊ n)} → x • y ≈ y • x → (w : Circuit (₄₊ n)) →
                x • (y • w • y) • x ≈ y • (x • w • x) • y
    conj-swap {x} {y} xy w = begin
      x • (y • w • y) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • y) • w • (y • x)     ≈⟨ cong xy (back _ (sym xy)) ⟩
      (y • x) • w • (x • y)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      y • (x • w • x) • y ∎

    -- Two words x₁ x₂ x₁ x₂ and y₁ y₂ y₁ y₂ whose letters pass each other.
    words : ∀ {x₁ x₂ y₁ y₂ : Circuit (₄₊ n)} →
            x₁ • y₁ ≈ y₁ • x₁ → x₁ • y₂ ≈ y₂ • x₁ → x₂ • y₁ ≈ y₁ • x₂ → x₂ • y₂ ≈ y₂ • x₂ →
            (x₁ • x₂ • x₁ • x₂) • (y₁ • y₂ • y₁ • y₂) ≈ (y₁ • y₂ • y₁ • y₂) • (x₁ • x₂ • x₁ • x₂)
    words e₁₁ e₁₂ e₂₁ e₂₂ =
      sym (comm-abab (sym (comm-abab e₁₁ e₁₂)) (sym (comm-abab e₂₁ e₂₂)))

    --------------------------------------------------------------------
    -- X on wire 3 and the letters

    -- It passes the H gate whose box wire it is on: (207) under the cycle.
    X₃-G : X ↑ ↑ ↑ • G ≈ G • X ↑ ↑ ↑
    X₃-G = S₂₃.⟪⟫-≈
      (S₁₂.⟪⟫-≈
        (S₀₁.⟪⟫-≈ eq207 (S₀₁.⟪⟫-•₂ S-X↓ refl) (S₀₁.⟪⟫-•₂ refl S-X↓))
        (S₁₂.⟪⟫-•₂ S₁₂-X₁ refl) (S₁₂.⟪⟫-•₂ refl S₁₂-X₁))
      (S₂₃.⟪⟫-•₂ S₂₃-X₂ refl) (S₂₃.⟪⟫-•₂ refl S₂₃-X₂)

    N₃-G : N₃.⟪ G ⟫ ≈ G
    N₃-G = N₃.⟪⟫-fix X₃-G

    N₃-°G : N₃.⟪ °G ⟫ ≈ °G
    N₃-°G = trans (sym (N₂-N₃ G)) (N₂.⟪⟫-cong N₃-G)

    N₃-G′ : N₃.⟪ G′ ⟫ ≈ G′
    N₃-G′ = trans (sym (S₀₁-N₃ G)) (S₀₁.⟪⟫-cong N₃-G)

    N₃-°B : N₃.⟪ °B ⟫ ≈ °°B
    N₃-°B = sym (S₀₁-N₃ °box₃)

    --------------------------------------------------------------------
    -- The second gate black on wire 1

    °Z-form : °Z ≈ °G • °B • °G • °B
    °Z-form = trans (N₂.⟪⟫-cong eq210) (N₂.⟪⟫-•₄ refl N₂-box₃′ refl N₂-box₃′)

    N₃°Z-form : N₃.⟪ °Z ⟫ ≈ °G • °°B • °G • °°B
    N₃°Z-form = trans (N₃.⟪⟫-cong °Z-form) (N₃.⟪⟫-•₄ N₃-°G N₃-°B N₃-°G N₃-°B)

    G′-°°B : G′ • °°B ≈ °°B • G′
    G′-°°B = N₃.⟪⟫-≈ eq192 (N₃.⟪⟫-•₂ N₃-G′ N₃-°B) (N₃.⟪⟫-•₂ N₃-°B N₃-G′)

    base₁ : ∀ γ → Aᴾ true true true • C₂₄₁ γ true true ≈ C₂₄₁ γ true true • Aᴾ true true true
    base₁ true = begin
      Aᴾ true true true • °Z
        ≈⟨ cong Aᴾ-form °Z-form ⟩
      (G′ • P • G′ • P) • (°G • °B • °G • °B)
        ≈⟨ words eq203 eq192 eq202 eq196 ⟩
      (°G • °B • °G • °B) • (G′ • P • G′ • P)
        ≈⟨ sym (cong °Z-form Aᴾ-form) ⟩
      °Z • Aᴾ true true true ∎
    base₁ false = begin
      Aᴾ true true true • N₃.⟪ °Z ⟫
        ≈⟨ cong Aᴾ-form N₃°Z-form ⟩
      (G′ • P • G′ • P) • (°G • °°B • °G • °°B)
        ≈⟨ words eq203 G′-°°B eq202 eq197 ⟩
      (°G • °°B • °G • °°B) • (G′ • P • G′ • P)
        ≈⟨ sym (cong N₃°Z-form Aᴾ-form) ⟩
      N₃.⟪ °Z ⟫ • Aᴾ true true true ∎

    base₁′ : ∀ γ → Aᴾ true true true • C₂₄₁ γ true false ≈ C₂₄₁ γ true false • Aᴾ true true true
    base₁′ γ = comm-inv (C₂₄₁-inv γ true) (C₂₄₁-inv′ γ true) (base₁ γ)

    --------------------------------------------------------------------
    -- The second gate white on wire 1

    X₁-X₂ : X ↑ • X ↑ ↑ ≈ X ↑ ↑ • X ↑
    X₁-X₂ = lemma-cong↑ (X ↓ • X ↑) (X ↑ • X ↓) (comm-↓↑ X X)

    -- The merge on wire 1, white on wire 2.
    °merge₁ : N₁.⟪ °Z ⟫ • °Z ≈ R₁
    °merge₁ = trans (front _ (conj-swap X₁-X₂ ZX₃))
                    (N₂.⟪⟫-≈ merge₁ (N₂.⟪⟫-• (N₁.⟪ ZX₃ ⟫) ZX₃) refl)

    °Z°Z′ : °Z • °Z′ ≈ ε
    °Z°Z′ = C₂₄₁-inv true true

    N₁°Z-form : N₁.⟪ °Z ⟫ ≈ R₁ • °Z′
    N₁°Z-form = begin
      N₁.⟪ °Z ⟫                   ≈⟨ sym right-unit ⟩
      N₁.⟪ °Z ⟫ • ε               ≈⟨ back _ (sym °Z°Z′) ⟩
      N₁.⟪ °Z ⟫ • °Z • °Z′        ≈⟨ sym assoc ⟩
      (N₁.⟪ °Z ⟫ • °Z) • °Z′      ≈⟨ front _ °merge₁ ⟩
      R₁ • °Z′ ∎

    C-white : ∀ γ → C₂₄₁ γ false true ≈ N₃ᵇ γ R₁ • C₂₄₁ γ true false
    C-white true  = N₁°Z-form
    C-white false = trans (N₃.⟪⟫-cong N₁°Z-form) (N₃.⟪⟫-• R₁ °Z′)

    -- Between P ⊗ P the doubly controlled ZX, white on wire 2, is turned
    -- over; so the rotation between P ⊗ P passes it, (239).
    X₂-PP : X ↑ ↑ • PP₀₁ ≈ PP₀₁ • X ↑ ↑
    X₂-PP = N₂.⟪⟫-comm N₂-PP₀₁

    X₃-PP : X ↑ ↑ ↑ • PP₀₁ ≈ PP₀₁ • X ↑ ↑ ↑
    X₃-PP = N₃.⟪⟫-comm N₃-PP₀₁

    Aj-R₁′ : Aj.⟪ R₁′ ⟫ ≈ R₁
    Aj-R₁′ = trans (conj-swap (sym X₂-PP) CCXZ₂₃)
                   (N₂.⟪⟫-cong (trans (Aj.⟪⟫-cong (sym Aj-CCZX₂₃)) (Aj.⟪⟫-⟪⟫ CCZX₂₃)))

    Aj-R₀′ : Aj.⟪ R₀′ ⟫ ≈ R₀
    Aj-R₀′ = trans (conj-swap (sym X₃-PP) R₁′) (N₃.⟪⟫-cong Aj-R₁′)

    Aᴾ-R : ∀ γ → Aᴾ true true true • N₃ᵇ γ R₁ ≈ N₃ᵇ γ R₁ • Aᴾ true true true
    Aᴾ-R true  = Aj.⟪⟫-≈ eq239₁′ (Aj.⟪⟫-•₂ refl Aj-R₁′) (Aj.⟪⟫-•₂ Aj-R₁′ refl)
    Aᴾ-R false = Aj.⟪⟫-≈ eq239₀′ (Aj.⟪⟫-•₂ refl Aj-R₀′) (Aj.⟪⟫-•₂ Aj-R₀′ refl)

    base₀ : ∀ γ → Aᴾ true true true • C₂₄₁ γ false true ≈ C₂₄₁ γ false true • Aᴾ true true true
    base₀ γ = begin
      Aᴾ true true true • C₂₄₁ γ false true
        ≈⟨ back _ (C-white γ) ⟩
      Aᴾ true true true • (N₃ᵇ γ R₁ • C₂₄₁ γ true false)
        ≈⟨ comm-• (Aᴾ-R γ) (base₁′ γ) ⟩
      (N₃ᵇ γ R₁ • C₂₄₁ γ true false) • Aᴾ true true true
        ≈⟨ front _ (sym (C-white γ)) ⟩
      C₂₄₁ γ false true • Aᴾ true true true ∎

    --------------------------------------------------------------------
    -- The first gate black on the wires 1 and 3

    core-ZX : ∀ γ δ → Aᴾ true true true • C₂₄₁ γ δ true ≈ C₂₄₁ γ δ true • Aᴾ true true true
    core-ZX γ true  = base₁ γ
    core-ZX γ false = base₀ γ

    all-a : ∀ {g : Circuit (₄₊ n)} → Aᴾ true true true • g ≈ g • Aᴾ true true true →
            ∀ a → Aᴾ true true a • g ≈ g • Aᴾ true true a
    all-a e true  = e
    all-a e false = inv-row (Aᴾ-inv true true) (Aᴾ-inv′ true true) e

    black : ∀ γ δ a b → Aᴾ true true a • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • Aᴾ true true a
    black γ δ a true  = all-a (core-ZX γ δ) a
    black γ δ a false = all-a (comm-inv (C₂₄₁-inv γ δ) (C₂₄₁-inv′ γ δ) (core-ZX γ δ)) a

    --------------------------------------------------------------------
    -- The first gate white on wire 1

    -- The doubly controlled ZX from the wires 2 3 is the merge of two
    -- gates of (241).
    W₂₃-C : ∀ γ δ b → CCZX₂₃ • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • CCZX₂₃
    W₂₃-C γ δ b = begin
      CCZX₂₃ • C₂₄₁ γ δ b
        ≈⟨ front _ (sym merge₁) ⟩
      (N₁.⟪ ZX₃ ⟫ • ZX₃) • C₂₄₁ γ δ b
        ≈⟨ sym (comm-• (sym (eq241 true false γ δ true b)) (sym (eq241 true true γ δ true b))) ⟩
      C₂₄₁ γ δ b • (N₁.⟪ ZX₃ ⟫ • ZX₃)
        ≈⟨ back _ merge₁ ⟩
      C₂₄₁ γ δ b • CCZX₂₃ ∎

    W₂₃V₂₃ : CCZX₂₃ • CCXZ₂₃ ≈ ε
    W₂₃V₂₃ = trans (sym (S₀₁.⟪⟫-• (U₃ CCZX) (U₃ CCXZ)))
            (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCZX • CCXZ) ε eq117)) S₀₁.⟪⟫-ε)

    V₂₃W₂₃ : CCXZ₂₃ • CCZX₂₃ ≈ ε
    V₂₃W₂₃ = trans (sym (S₀₁.⟪⟫-• (U₃ CCXZ) (U₃ CCZX)))
            (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCXZ • CCZX) ε eq118)) S₀₁.⟪⟫-ε)

    V₂₃-C : ∀ γ δ b → CCXZ₂₃ • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • CCXZ₂₃
    V₂₃-C γ δ b = inv-row W₂₃V₂₃ V₂₃W₂₃ (W₂₃-C γ δ b)

    white-ZX : ∀ γ δ b → Aᴾ true false true • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • Aᴾ true false true
    white-ZX γ δ b = begin
      Aᴾ true false true • C₂₄₁ γ δ b
        ≈⟨ front _ Aᴾ-white ⟩
      (CCXZ₂₃ • Aᴾ true true false) • C₂₄₁ γ δ b
        ≈⟨ sym (comm-• (sym (V₂₃-C γ δ b)) (sym (black γ δ false b))) ⟩
      C₂₄₁ γ δ b • (CCXZ₂₃ • Aᴾ true true false)
        ≈⟨ back _ (sym Aᴾ-white) ⟩
      C₂₄₁ γ δ b • Aᴾ true false true ∎

    white : ∀ γ δ a b → Aᴾ true false a • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • Aᴾ true false a
    white γ δ true  b = white-ZX γ δ b
    white γ δ false b = inv-row (Aᴾ-inv true false) (Aᴾ-inv′ true false) (white-ZX γ δ b)

    stage-β : ∀ β γ δ a b → Aᴾ true β a • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • Aᴾ true β a
    stage-β true  = black
    stage-β false = white

    flip₃ : ∀ γ (w : Circuit (₄₊ n)) → N₃.⟪ N₃ᵇ (not γ) w ⟫ ≈ N₃ᵇ γ w
    flip₃ true  w = N₃.⟪⟫-⟪⟫ w
    flip₃ false w = refl

  -- For (242): X on wire 3 and the H gates, the second gate's form, the
  -- merge on wire 1, and the white doubly controlled rotation between
  -- P ⊗ P.
  N₃-S₀₁ΛH₂′ : N₃.⟪ S₀₁.⟪ ΛH₂′ ⟫ ⟫ ≈ S₀₁.⟪ ΛH₂′ ⟫
  N₃-S₀₁ΛH₂′ = N₃-G′

  N₃-S₀₁°ΛH₂′ : N₃.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ≈ S₀₁.⟪ °ΛH₂′ ⟫
  N₃-S₀₁°ΛH₂′ = trans (sym (S₀₁-N₃ °G)) (S₀₁.⟪⟫-cong N₃-°G)

  °ZX₃-as-GBGB : N₂.⟪ ZX₃ ⟫ ≈ °ΛH₂′ • S₀₁.⟪ °box₃ ⟫ • °ΛH₂′ • S₀₁.⟪ °box₃ ⟫
  °ZX₃-as-GBGB = °Z-form

  °merge-on-1 : N₁.⟪ N₂.⟪ ZX₃ ⟫ ⟫ • N₂.⟪ ZX₃ ⟫ ≈ R₁
  °merge-on-1 = °merge₁

  PP-R₁′ : Aj.⟪ R₁′ ⟫ ≈ R₁
  PP-R₁′ = Aj-R₁′

  -- (243)
  eq243 : ∀ α β γ δ a b → Aᴾ α β a • C₂₄₁ γ δ b ≈ C₂₄₁ γ δ b • Aᴾ α β a
  eq243 true  β γ δ a b = stage-β β γ δ a b
  eq243 false β γ δ a b = N₃.⟪⟫-≈ (stage-β β (not γ) δ a b)
    (N₃.⟪⟫-•₂ (N₃-Aᴾ β a) (flip₃ γ (N₁ᵇ δ (N₂.⟪ rot b ⟫))))
    (N₃.⟪⟫-•₂ (flip₃ γ (N₁ᵇ δ (N₂.⟪ rot b ⟫))) (N₃-Aᴾ β a))
