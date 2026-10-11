------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation between P ⊗ P on its target and a control
-- against one white on wire 3 (Clément, Lemma D.5, Equation (244))
--
-- The first gate rotates wire 1 from the wires 0, 3 and, in either
-- colour, 2, and stands between P ⊗ P on the wires 1 2; the second
-- rotates wire 0 from wire 2, from wire 3 negatively, and from wire 1 in
-- either colour — the second gate of (245).
--
--   both black: the first gate is G₃ B₀ G₃ B₀ between P ⊗ P, (210) and
--     (214) under the lower swap — the H gate H(1, 2; 0, 3) and the box
--     on wire 0 —, and between the same P ⊗ P the second gate is
--     Y J′ Y J′, the letters of (227) and (220).  The letters pass each
--     other: (206), (184), and for Y — the white box on wire 2 between
--     P ⊗ P on the wires 0 1 — the Klein four-group with (198), and
--     (183).
--   the first gate white on wire 2: by the merge on wire 2, (221), it is
--     the doubly controlled ZX on wire 1 from the wires 0 3 between P ⊗ P
--     times a gate of the first kind.  Between P ⊗ P that ZX is its
--     inverse, (174), and the second gate passes it: this is the crossed
--     statement (216) under the lower and the upper swap.
--   the second gate white on wire 1: X on wire 1 exchanges its two
--     colours, and between P ⊗ P it is Z H Z on the target of the first
--     gate, which exchanges ZX and XZ there, (236) and (237).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies244
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; H² ; Z²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; CCZX₂₃ ; CCXZ₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (eq184)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁ ; S₁₂-N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (PP₁₂ ; PP₀₂ ; PP₁₂² ; eq206)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃
  using (K ; eq216)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃
  using (J′ ; CCZX₁₃ ; CCXZ₁₃ ; Kᵇ)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations5 complete₂ complete₃
  using (eq236 ; eq237)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PConjugates complete₂ complete₃
  using (Y ; Y₁ ; Y₁-form ; Y-G₃ ; Y-box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (rot ; N₁-N₃-swap)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
  using (S₁₂-CCZX₁₃ ; Aj-CCZX₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies245 complete₂ complete₃
  using (module Pj ; N₂ᵇ ; S₂₄₅ ; S₂₄₅-inv ; S₂₄₅-inv′ ; N₂ᵇ-cancel ; N₂-ZX₃-split)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂ ; eq117 ; eq118)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

-- The first gate: the rotation of wire 1, its control on wire 2 of
-- either colour, between P ⊗ P on the wires 1 2.
F₂₄₄ : Bool → Bool → Circuit (₄₊ n)
F₂₄₄ α a = Pj.⟪ S₀₁.⟪ N₂ᵇ α (rot a) ⟫ ⟫

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    G₃ M M′ zhz₀ zhz₁ : Circuit (₄₊ n)
    G₃   = S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫
    M    = S₀₁.⟪ CCZX₁₃ ⟫
    M′   = S₀₁.⟪ CCXZ₁₃ ⟫
    zhz₀ = Z ↓ • H ↓ • Z ↓
    zhz₁ = Z ↑ • H ↑ • Z ↑

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

    --------------------------------------------------------------------
    -- Both gates black on the wires 2 and 1

    Kᵇ-form : Kᵇ ≈ G₃ • box₃ • G₃ • box₃
    Kᵇ-form = trans (S₀₁.⟪⟫-cong ZX₃-form₄)
                    (S₀₁.⟪⟫-•₄ refl (S₀₁.⟪⟫-⟪⟫ box₃) refl (S₀₁.⟪⟫-⟪⟫ box₃))

    -- The H gate of (184) is J′: the wires of (0 1)(1 2) against those of
    -- the six swaps.
    S₀₁-N₂ : (w : Circuit (₄₊ n)) → S₀₁.⟪ N₂.⟪ w ⟫ ⟫ ≈ N₂.⟪ S₀₁.⟪ w ⟫ ⟫
    S₀₁-N₂ w = S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ X) refl (P₂₃-S₀₁ X)

    S₂₃-N₂ : (w : Circuit (₄₊ n)) → S₂₃.⟪ N₂.⟪ w ⟫ ⟫ ≈ N₃.⟪ S₂₃.⟪ w ⟫ ⟫
    S₂₃-N₂ w = S₂₃.⟪⟫-•₃ S₂₃-X₂ refl S₂₃-X₂

    perm : S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ ΛH₂′ ⟫ ⟫ ⟫ ≈ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫
    perm = begin
      S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ S₂₃.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (conj-swap far (S₁₂.⟪ ΛH₀₁ ⟫))) ⟩
      S₁₂.⟪ S₂₃.⟪ S₂₃.⟪ G₃ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-⟪⟫ G₃) ⟩
      S₁₂.⟪ S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ ⟫
        ≈⟨ braid-conj ΛH₀₁ ⟩
      S₀₁.⟪ S₁₂.⟪ S₀₁.⟪ ΛH₀₁ ⟫ ⟫ ⟫
        ≈⟨ S₀₁.⟪⟫-cong (S₁₂.⟪⟫-cong (S₀₁.⟪⟫-⟪⟫ (ΛH 2 ↓ᵏ n))) ⟩
      S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ∎

    J′-bridge : S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫ ⟫ ≈ J′
    J′-bridge = begin
      S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ N₂.⟪ ΛH₂′ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (S₀₁-N₂ ΛH₂′)) ⟩
      S₁₂.⟪ S₂₃.⟪ N₂.⟪ S₀₁.⟪ ΛH₂′ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃-N₂ (S₀₁.⟪ ΛH₂′ ⟫)) ⟩
      S₁₂.⟪ N₃.⟪ S₂₃.⟪ S₀₁.⟪ ΛH₂′ ⟫ ⟫ ⟫ ⟫
        ≈⟨ S₁₂-N₃ (S₂₃.⟪ S₀₁.⟪ ΛH₂′ ⟫ ⟫) ⟩
      N₃.⟪ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ ΛH₂′ ⟫ ⟫ ⟫ ⟫
        ≈⟨ N₃.⟪⟫-cong perm ⟩
      J′ ∎

    -- The letters.
    box₃-J′ : box₃ • J′ ≈ J′ • box₃
    box₃-J′ = trans (back _ (sym J′-bridge)) (trans eq184 (front _ J′-bridge))

    base₀ : Kᵇ • Y₁ ≈ Y₁ • Kᵇ
    base₀ = begin
      Kᵇ • Y₁
        ≈⟨ cong Kᵇ-form Y₁-form ⟩
      (G₃ • box₃ • G₃ • box₃) • (Y • J′ • Y • J′)
        ≈⟨ words (sym Y-G₃) eq206 (sym Y-box₃) box₃-J′ ⟩
      (Y • J′ • Y • J′) • (G₃ • box₃ • G₃ • box₃)
        ≈⟨ sym (cong Y₁-form Kᵇ-form) ⟩
      Y₁ • Kᵇ ∎

    base : F₂₄₄ true true • S₂₄₅ true true ≈ S₂₄₅ true true • F₂₄₄ true true
    base = Pj.⟪⟫-≈ base₀
      (Pj.⟪⟫-•₂ refl (Pj.⟪⟫-⟪⟫ (N₃.⟪ ZX₃ ⟫)))
      (Pj.⟪⟫-•₂ (Pj.⟪⟫-⟪⟫ (N₃.⟪ ZX₃ ⟫)) refl)

    --------------------------------------------------------------------
    -- Inverses

    F-inv : ∀ α → F₂₄₄ α true • F₂₄₄ α false ≈ ε
    F-inv α = trans (sym (Pj.⟪⟫-• _ _)) (trans (Pj.⟪⟫-cong
              (trans (sym (S₀₁.⟪⟫-• _ _)) (trans (S₀₁.⟪⟫-cong (N₂ᵇ-cancel α eq208′)) S₀₁.⟪⟫-ε)))
              Pj.⟪⟫-ε)

    F-inv′ : ∀ α → F₂₄₄ α false • F₂₄₄ α true ≈ ε
    F-inv′ α = trans (sym (Pj.⟪⟫-• _ _)) (trans (Pj.⟪⟫-cong
               (trans (sym (S₀₁.⟪⟫-• _ _)) (trans (S₀₁.⟪⟫-cong (N₂ᵇ-cancel α eq208)) S₀₁.⟪⟫-ε)))
               Pj.⟪⟫-ε)

    bb₁ : ∀ b → F₂₄₄ true true • S₂₄₅ true b ≈ S₂₄₅ true b • F₂₄₄ true true
    bb₁ true  = base
    bb₁ false = comm-inv (S₂₄₅-inv true) (S₂₄₅-inv′ true) base

    bb : ∀ a b → F₂₄₄ true a • S₂₄₅ true b ≈ S₂₄₅ true b • F₂₄₄ true a
    bb true  b = bb₁ b
    bb false b = inv-row (F-inv true) (F-inv′ true) (bb₁ b)

    --------------------------------------------------------------------
    -- The first gate white on wire 2

    MM′ : M • M′ ≈ ε
    MM′ = trans (sym (S₀₁.⟪⟫-• CCZX₁₃ CCXZ₁₃)) (trans (S₀₁.⟪⟫-cong
          (trans (sym (S₂₃.⟪⟫-• (L₃ CCZX) (L₃ CCXZ))) (trans (S₂₃.⟪⟫-cong eq117) S₂₃.⟪⟫-ε)))
          S₀₁.⟪⟫-ε)

    M′M : M′ • M ≈ ε
    M′M = trans (sym (S₀₁.⟪⟫-• CCXZ₁₃ CCZX₁₃)) (trans (S₀₁.⟪⟫-cong
          (trans (sym (S₂₃.⟪⟫-• (L₃ CCXZ) (L₃ CCZX))) (trans (S₂₃.⟪⟫-cong eq118) S₂₃.⟪⟫-ε)))
          S₀₁.⟪⟫-ε)

    F-white : F₂₄₄ false true ≈ Pj.⟪ M ⟫ • F₂₄₄ true false
    F-white = trans (Pj.⟪⟫-cong (trans (S₀₁.⟪⟫-cong N₂-ZX₃-split) (S₀₁.⟪⟫-• CCZX₁₃ XZ₃)))
                    (Pj.⟪⟫-• M (S₀₁.⟪ XZ₃ ⟫))

    -- Between P ⊗ P the doubly controlled ZX is its inverse: (174) under
    -- the middle and the lower swap.
    S₁₂-CCXZ₁₃ : S₁₂.⟪ CCXZ₁₃ ⟫ ≈ CCXZ₂₃
    S₁₂-CCXZ₁₃ = begin
      S₁₂.⟪ CCXZ₁₃ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-•₄ (O-S₂₃ CZ) (L-S₂₃ CH) (O-S₂₃ CZ) (L-S₂₃ CH)) ⟩
      S₁₂.⟪ P₀₃ CZ • CH ↓ • P₀₃ CZ • CH ↓ ⟫
        ≈⟨ S₁₂.⟪⟫-•₄ (S₁₂-P₀₃ CZ) (O-L CH) (S₁₂-P₀₃ CZ) (O-L CH) ⟩
      P₀₃ CZ • CH₂₀ • P₀₃ CZ • CH₂₀
        ≈⟨ sym (S₀₁.⟪⟫-•₄ refl refl refl refl) ⟩
      CCXZ₂₃ ∎

    P₀₂-N : PP₀₂ • CCZX₁₃ • PP₀₂ ≈ CCXZ₁₃
    P₀₂-N = S₁₂.⟪⟫-≈ Aj-CCZX₂₃
      (S₁₂.⟪⟫-•₃ (O-L PP) (trans (S₁₂.⟪⟫-cong (sym S₁₂-CCZX₁₃)) (S₁₂.⟪⟫-⟪⟫ CCZX₁₃)) (O-L PP))
      (trans (S₁₂.⟪⟫-cong (sym S₁₂-CCXZ₁₃)) (S₁₂.⟪⟫-⟪⟫ CCXZ₁₃))

    Pj-M : Pj.⟪ M ⟫ ≈ M′
    Pj-M = S₀₁.⟪⟫-≈ P₀₂-N
      (S₀₁.⟪⟫-•₃ (S₀₁.⟪⟫-⟪⟫ (U PP)) refl (S₀₁.⟪⟫-⟪⟫ (U PP)))
      refl

    -- (216) under the lower and the upper swap.
    S₂₃-°ZX₃ : S₂₃.⟪ N₂.⟪ ZX₃ ⟫ ⟫ ≈ N₃.⟪ ZX₃ ⟫
    S₂₃-°ZX₃ = trans (S₂₃-N₂ ZX₃) (N₃.⟪⟫-cong S₂₃-ZX₃)

    e216 : N₃.⟪ ZX₃ ⟫ • M ≈ M • N₃.⟪ ZX₃ ⟫
    e216 = S₂₃.⟪⟫-≈
      (S₀₁.⟪⟫-≈ eq216
        (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ (N₂.⟪ ZX₃ ⟫)) refl)
        (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ (N₂.⟪ ZX₃ ⟫))))
      (S₂₃.⟪⟫-•₂ S₂₃-°ZX₃ sw) (S₂₃.⟪⟫-•₂ sw S₂₃-°ZX₃)
      where
      sw : S₂₃.⟪ S₀₁.⟪ CCZX ⟫ ⟫ ≈ M
      sw = sym (conj-swap far CCZX)

    PM-S₁ : Pj.⟪ M ⟫ • S₂₄₅ true true ≈ S₂₄₅ true true • Pj.⟪ M ⟫
    PM-S₁ = trans (front _ Pj-M) (trans (inv-row MM′ M′M (sym e216)) (back _ (sym Pj-M)))

    PM-S : ∀ b → Pj.⟪ M ⟫ • S₂₄₅ true b ≈ S₂₄₅ true b • Pj.⟪ M ⟫
    PM-S true  = PM-S₁
    PM-S false = comm-inv (S₂₄₅-inv true) (S₂₄₅-inv′ true) PM-S₁

    wb₁ : ∀ b → F₂₄₄ false true • S₂₄₅ true b ≈ S₂₄₅ true b • F₂₄₄ false true
    wb₁ b = begin
      F₂₄₄ false true • S₂₄₅ true b
        ≈⟨ front _ F-white ⟩
      (Pj.⟪ M ⟫ • F₂₄₄ true false) • S₂₄₅ true b
        ≈⟨ sym (comm-• (sym (PM-S b)) (sym (bb false b))) ⟩
      S₂₄₅ true b • (Pj.⟪ M ⟫ • F₂₄₄ true false)
        ≈⟨ back _ (sym F-white) ⟩
      S₂₄₅ true b • F₂₄₄ false true ∎

    black-β : ∀ α a b → F₂₄₄ α a • S₂₄₅ true b ≈ S₂₄₅ true b • F₂₄₄ α a
    black-β true  a     b = bb a b
    black-β false true  b = wb₁ b
    black-β false false b = inv-row (F-inv false) (F-inv′ false) (wb₁ b)

    --------------------------------------------------------------------
    -- The second gate white on wire 1: X on wire 1

    -- Between P ⊗ P, X on wire 1 is Z H Z …
    Pj-zhz : Pj.⟪ zhz₁ ⟫ ≈ X ↑
    Pj-zhz = U-sem (PP • (Z ↓ • H ↓ • Z ↓) • PP) (X ↓) Eq.refl

    S₀₁-zhz : S₀₁.⟪ zhz₀ ⟫ ≈ zhz₁
    S₀₁-zhz = L-sem (Ex • (Z ↓ • H ↓ • Z ↓) • Ex) (Z ↑ • H ↑ • Z ↑) Eq.refl

    zhz₀² : zhz₀ • zhz₀ ≈ ε
    zhz₀² = L-sem ((Z ↓ • H ↓ • Z ↓) • (Z ↓ • H ↓ • Z ↓)) ε Eq.refl

    module Zh = Conj {₄₊ n} zhz₀ zhz₀²

    N₁-Pj-S₀₁ : (w : Circuit (₄₊ n)) → N₁.⟪ Pj.⟪ S₀₁.⟪ w ⟫ ⟫ ⟫ ≈ Pj.⟪ S₀₁.⟪ Zh.⟪ w ⟫ ⟫ ⟫
    N₁-Pj-S₀₁ w = begin
      X ↑ • Pj.⟪ S₀₁.⟪ w ⟫ ⟫ • X ↑
        ≈⟨ cong (sym Pj-zhz) (back _ (sym Pj-zhz)) ⟩
      Pj.⟪ zhz₁ ⟫ • Pj.⟪ S₀₁.⟪ w ⟫ ⟫ • Pj.⟪ zhz₁ ⟫
        ≈⟨ sym (Pj.⟪⟫-•₃ refl refl refl) ⟩
      Pj.⟪ zhz₁ • S₀₁.⟪ w ⟫ • zhz₁ ⟫
        ≈⟨ Pj.⟪⟫-cong (sym (S₀₁.⟪⟫-•₃ S₀₁-zhz refl S₀₁-zhz)) ⟩
      Pj.⟪ S₀₁.⟪ zhz₀ • w • zhz₀ ⟫ ⟫ ∎

    -- … which exchanges ZX and XZ on the target, (236) and (237).
    flip-pass : ∀ {x w w′ : Circuit (₄₊ n)} → x • x ≈ ε → x • w ≈ w′ • x → x • w′ ≈ w • x
    flip-pass xx e = sym (conj-comm xx (trans (sym assoc) (trans (front _ e) (cancelʳ _ xx))))

    pass₃ : ∀ {x y w w′ : Circuit (₄₊ n)} → x • w ≈ w′ • x → y • w′ ≈ w • y →
            (x • y • x) • w ≈ w′ • (x • y • x)
    pass₃ {x} {y} {w} {w′} xw yw′ = begin
      (x • y • x) • w       ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
      x • y • (x • w)       ≈⟨ back _ (back _ xw) ⟩
      x • y • (w′ • x)      ≈⟨ by-passoc (□ • □ • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
      x • (y • w′) • x      ≈⟨ back _ (front _ yw′) ⟩
      x • (w • y) • x       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
      (x • w) • y • x       ≈⟨ front _ xw ⟩
      (w′ • x) • y • x      ≈⟨ assoc ⟩
      w′ • (x • y • x) ∎

    unpass : ∀ {w w′ : Circuit (₄₊ n)} → zhz₀ • w ≈ w′ • zhz₀ → Zh.⟪ w ⟫ ≈ w′
    unpass e = trans (sym assoc) (trans (front _ e) (cancelʳ _ zhz₀²))

    Zh-rot : ∀ a → Zh.⟪ rot (not a) ⟫ ≈ rot a
    Zh-rot true  = unpass (pass₃ eq237 eq236)
    Zh-rot false = unpass (pass₃ (flip-pass Z² eq237) (flip-pass H² eq236))

    zhz-X₂ : zhz₀ • X ↑ ↑ ≈ X ↑ ↑ • zhz₀
    zhz-X₂ = L-comm (Z ↓ • H ↓ • Z ↓) X

    Zh-N₂ᵇ : ∀ α a → Zh.⟪ N₂ᵇ α (rot (not a)) ⟫ ≈ N₂ᵇ α (rot a)
    Zh-N₂ᵇ true  a = Zh-rot a
    Zh-N₂ᵇ false a = trans (conj-swap zhz-X₂ (rot (not a))) (N₂.⟪⟫-cong (Zh-rot a))

    flipF : ∀ α a → N₁.⟪ F₂₄₄ α (not a) ⟫ ≈ F₂₄₄ α a
    flipF α a = trans (N₁-Pj-S₀₁ (N₂ᵇ α (rot (not a))))
                      (Pj.⟪⟫-cong (S₀₁.⟪⟫-cong (Zh-N₂ᵇ α a)))

    flipS : ∀ b → N₁.⟪ S₂₄₅ true b ⟫ ≈ S₂₄₅ false b
    flipS b = N₁-N₃-swap (rot b)

    white-β : ∀ α a b → F₂₄₄ α a • S₂₄₅ false b ≈ S₂₄₅ false b • F₂₄₄ α a
    white-β α a b = N₁.⟪⟫-≈ (black-β α (not a) b)
      (N₁.⟪⟫-•₂ (flipF α a) (flipS b))
      (N₁.⟪⟫-•₂ (flipS b) (flipF α a))

  -- (244)
  eq244 : ∀ α β a b → F₂₄₄ α a • S₂₄₅ β b ≈ S₂₄₅ β b • F₂₄₄ α a
  eq244 α true  a b = black-β α a b
  eq244 α false a b = white-β α a b
