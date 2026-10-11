------------------------------------------------------------------------
-- Presentations of groups
--
-- A triply controlled rotation between P ⊗ P against one of the other
-- colour with a control on wire 4 (Clément, Lemma D.7, Equation (268))
--
-- The first gate is that of (243), the rotation of wire 0 between P ⊗ P
-- on the wires 0 1, with controls of any colour on the wires 1 and 3.
-- The second rotates wire 0 from wire 4, from wire 2 negatively, and
-- from wire 1 in either colour: the second gate of (243) with wire 4 in
-- the place of wire 3.  As for (243):
--
--   all black: the first gate is G′ P G′ P, H gates, and the second
--     °G₄ °B₄ °G₄ °B₄ — the first and second gates of (253)–(260) — and
--     the letters pass each other: (258), (253), (260), (255);
--   the second gate white on wire 1: by the merge on wire 1 it is the
--     doubly controlled ZX from the wires 2 4, white on wire 2, times a
--     gate of the first kind; between P ⊗ P that ZX is turned over, (174),
--     and the rotation passes it: (261) under the swap of the wires 3 4,
--     negated on wire 2;
--   the first gate white on wire 1: it is the doubly controlled XZ from
--     the wires 2 3 times a black one (`Aᴾ-white`), and the XZ passes the
--     second gate by (261), X on wire 1 giving its other colour;
--   the first gate white on wire 3: X on wire 3, which the second gate
--     does not see.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FiveQubit.PFamilies268
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; comm-↓↑ ; X² ; S-X↓ ; S-X↑)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (CCXZ₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (ΛH₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (PP₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
  using (ZX₃ ; XZ₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families complete₂ complete₃
  using (R₁ ; R₁′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; rot ; C₂₄₁ ; C₂₄₁-inv ; C₂₄₁-inv′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PForms complete₂ complete₃
  using (module Aj ; Aᴾ ; Aᴾ-form ; Aᴾ-white ; Aᴾ-inv ; Aᴾ-inv′ ; N₃-Aᴾ)
open import Examples.Groups.Real-Clifford+CH.FourQubit.PFamilies243 complete₂ complete₃
  using (°ZX₃-as-GBGB ; °merge-on-1 ; PP-R₁′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Shift complete₂ complete₃
  using (module S₃₄ ; conj-swap ; L₄-top)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Colours complete₂ complete₃
  using (eq253 ; eq255 ; eq258 ; eq260)
open import Examples.Groups.Real-Clifford+CH.FiveQubit.Rotations2 complete₂ complete₃
  using (F₂₆₁ ; eq261)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The second gate

-- The rotation of wire 0 from wire 4, from wire 2 negatively, and from
-- wire 1 in either colour.
G₂₆₈ : Bool → Bool → Circuit (₁₊ (₄₊ n))
G₂₆₈ γ b = S₃₄.⟪ C₂₄₁ true γ b ⟫

module _ {n : ℕ} where
  private
    Γ = (₁₊ (₄₊ n)) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    W₅ = Circuit (₁₊ (₄₊ n))

    Ex₃₄ X₄ °Z °Z′ °G₄ °B₄ : W₅
    Ex₃₄ = Ex ↑ ↑ ↑
    X₄   = X ↑ ↑ ↑ ↑
    °Z   = N₂.⟪ ZX₃ ⟫
    °Z′  = N₂.⟪ XZ₃ ⟫
    °G₄  = S₃₄.⟪ °ΛH₂′ ⟫
    °B₄  = S₃₄.⟪ S₀₁.⟪ °box₃ ⟫ ⟫

    inv-row : ∀ {w v y : W₅} → w • v ≈ ε → v • w ≈ ε → w • y ≈ y • w → v • y ≈ y • v
    inv-row wv vw h = sym (comm-inv wv vw (sym h))

    words : ∀ {x₁ x₂ y₁ y₂ : W₅} →
            x₁ • y₁ ≈ y₁ • x₁ → x₁ • y₂ ≈ y₂ • x₁ → x₂ • y₁ ≈ y₁ • x₂ → x₂ • y₂ ≈ y₂ • x₂ →
            (x₁ • x₂ • x₁ • x₂) • (y₁ • y₂ • y₁ • y₂) ≈ (y₁ • y₂ • y₁ • y₂) • (x₁ • x₂ • x₁ • x₂)
    words e₁₁ e₁₂ e₂₁ e₂₂ =
      sym (comm-abab (sym (comm-abab e₁₁ e₁₂)) (sym (comm-abab e₂₁ e₂₂)))

    --------------------------------------------------------------------
    -- What passes the swap of the wires 3 4

    X₁-Ex₃₄ : X ↑ • Ex₃₄ ≈ Ex₃₄ • X ↑
    X₁-Ex₃₄ = lemma-cong↑ (X ↓ • Ex ↑ ↑) (Ex ↑ ↑ • X ↓) (comm-↓↑ X (Ex ↑))

    X₂-Ex₃₄ : X ↑ ↑ • Ex₃₄ ≈ Ex₃₄ • X ↑ ↑
    X₂-Ex₃₄ = lemma-cong↑ (X ↑ • Ex ↑ ↑) (Ex ↑ ↑ • X ↑)
                (lemma-cong↑ (X ↓ • Ex ↑) (Ex ↑ • X ↓) (comm-↓↑ X Ex))

    PP-Ex₃₄ : PP₀₁ • Ex₃₄ ≈ Ex₃₄ • PP₀₁
    PP-Ex₃₄ = L-comm PP (Ex ↑)

    --------------------------------------------------------------------
    -- All black

    G-form : G₂₆₈ true true ≈ °G₄ • °B₄ • °G₄ • °B₄
    G-form = trans (S₃₄.⟪⟫-cong °ZX₃-as-GBGB) (S₃₄.⟪⟫-•₄ refl refl refl refl)

    base₁ : Aᴾ true true true • G₂₆₈ true true ≈ G₂₆₈ true true • Aᴾ true true true
    base₁ = begin
      Aᴾ true true true • G₂₆₈ true true
        ≈⟨ cong Aᴾ-form G-form ⟩
      (S₀₁.⟪ ΛH₂′ ⟫ • ΛH₀₁ • S₀₁.⟪ ΛH₂′ ⟫ • ΛH₀₁) • (°G₄ • °B₄ • °G₄ • °B₄)
        ≈⟨ words eq258 eq253 eq260 eq255 ⟩
      (°G₄ • °B₄ • °G₄ • °B₄) • (S₀₁.⟪ ΛH₂′ ⟫ • ΛH₀₁ • S₀₁.⟪ ΛH₂′ ⟫ • ΛH₀₁)
        ≈⟨ sym (cong G-form Aᴾ-form) ⟩
      G₂₆₈ true true • Aᴾ true true true ∎

    --------------------------------------------------------------------
    -- Inverses

    G-inv : ∀ γ → G₂₆₈ γ true • G₂₆₈ γ false ≈ ε
    G-inv γ = trans (sym (S₃₄.⟪⟫-• _ _)) (trans (S₃₄.⟪⟫-cong (C₂₄₁-inv true γ)) S₃₄.⟪⟫-ε)

    G-inv′ : ∀ γ → G₂₆₈ γ false • G₂₆₈ γ true ≈ ε
    G-inv′ γ = trans (sym (S₃₄.⟪⟫-• _ _)) (trans (S₃₄.⟪⟫-cong (C₂₄₁-inv′ true γ)) S₃₄.⟪⟫-ε)

    --------------------------------------------------------------------
    -- The second gate white on wire 1

    N₁°Z-form : N₁.⟪ °Z ⟫ ≈ R₁ • °Z′
    N₁°Z-form = begin
      N₁.⟪ °Z ⟫                   ≈⟨ sym right-unit ⟩
      N₁.⟪ °Z ⟫ • ε               ≈⟨ back _ (sym (C₂₄₁-inv true true)) ⟩
      N₁.⟪ °Z ⟫ • °Z • °Z′        ≈⟨ sym assoc ⟩
      (N₁.⟪ °Z ⟫ • °Z) • °Z′      ≈⟨ front _ °merge-on-1 ⟩
      R₁ • °Z′ ∎

    G-white : G₂₆₈ false true ≈ S₃₄.⟪ R₁ ⟫ • G₂₆₈ true false
    G-white = trans (S₃₄.⟪⟫-cong N₁°Z-form) (S₃₄.⟪⟫-• R₁ °Z′)

    -- (261) under the swap of the wires 3 4, negated on wire 2 …
    ZX₃-SR′ : ZX₃ • S₃₄.⟪ R₁′ ⟫ ≈ S₃₄.⟪ R₁′ ⟫ • ZX₃
    ZX₃-SR′ = N₂.⟪⟫-≈ e₁ (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ ZX₃) N₂-S) (N₂.⟪⟫-•₂ N₂-S (N₂.⟪⟫-⟪⟫ ZX₃))
      where
      e₁ : °Z • S₃₄.⟪ CCXZ₂₃ ⟫ ≈ S₃₄.⟪ CCXZ₂₃ ⟫ • °Z
      e₁ = S₃₄.⟪⟫-≈ eq261 (S₃₄.⟪⟫-•₂ (S₃₄.⟪⟫-⟪⟫ °Z) refl) (S₃₄.⟪⟫-•₂ refl (S₃₄.⟪⟫-⟪⟫ °Z))
      N₂-S : N₂.⟪ S₃₄.⟪ CCXZ₂₃ ⟫ ⟫ ≈ S₃₄.⟪ R₁′ ⟫
      N₂-S = conj-swap X₂-Ex₃₄ CCXZ₂₃

    -- … and between P ⊗ P.
    Aᴾ-SR : Aᴾ true true true • S₃₄.⟪ R₁ ⟫ ≈ S₃₄.⟪ R₁ ⟫ • Aᴾ true true true
    Aᴾ-SR = Aj.⟪⟫-≈ ZX₃-SR′ (Aj.⟪⟫-•₂ refl Aj-S) (Aj.⟪⟫-•₂ Aj-S refl)
      where
      Aj-S : Aj.⟪ S₃₄.⟪ R₁′ ⟫ ⟫ ≈ S₃₄.⟪ R₁ ⟫
      Aj-S = trans (conj-swap PP-Ex₃₄ R₁′) (S₃₄.⟪⟫-cong PP-R₁′)

    base₀ : Aᴾ true true true • G₂₆₈ false true ≈ G₂₆₈ false true • Aᴾ true true true
    base₀ = begin
      Aᴾ true true true • G₂₆₈ false true
        ≈⟨ back _ G-white ⟩
      Aᴾ true true true • (S₃₄.⟪ R₁ ⟫ • G₂₆₈ true false)
        ≈⟨ comm-• Aᴾ-SR (comm-inv (G-inv true) (G-inv′ true) base₁) ⟩
      (S₃₄.⟪ R₁ ⟫ • G₂₆₈ true false) • Aᴾ true true true
        ≈⟨ front _ (sym G-white) ⟩
      G₂₆₈ false true • Aᴾ true true true ∎

    core-ZX : ∀ γ → Aᴾ true true true • G₂₆₈ γ true ≈ G₂₆₈ γ true • Aᴾ true true true
    core-ZX true  = base₁
    core-ZX false = base₀

    core : ∀ γ b → Aᴾ true true true • G₂₆₈ γ b ≈ G₂₆₈ γ b • Aᴾ true true true
    core γ true  = core-ZX γ
    core γ false = comm-inv (G-inv γ) (G-inv′ γ) (core-ZX γ)

    black : ∀ γ a b → Aᴾ true true a • G₂₆₈ γ b ≈ G₂₆₈ γ b • Aᴾ true true a
    black γ true  b = core γ b
    black γ false b = inv-row (Aᴾ-inv true true) (Aᴾ-inv′ true true) (core γ b)

    --------------------------------------------------------------------
    -- The first gate white on wire 1

    -- X on wire 1 does not see the doubly controlled XZ from the wires
    -- 2 3.
    N₁-V₂₃ : N₁.⟪ CCXZ₂₃ ⟫ ≈ CCXZ₂₃
    N₁-V₂₃ = N₁.⟪⟫-fix (S₀₁.⟪⟫-≈ (comm-↓↑ X CCXZ) (S₀₁.⟪⟫-•₂ S-X↓ refl) (S₀₁.⟪⟫-•₂ refl S-X↓))

    V-G₁ : ∀ γ → CCXZ₂₃ • G₂₆₈ γ true ≈ G₂₆₈ γ true • CCXZ₂₃
    V-G₁ true  = sym eq261
    V-G₁ false = N₁.⟪⟫-≈ (sym eq261) (N₁.⟪⟫-•₂ N₁-V₂₃ N₁-G) (N₁.⟪⟫-•₂ N₁-G N₁-V₂₃)
      where
      N₁-G : N₁.⟪ F₂₆₁ ⟫ ≈ G₂₆₈ false true
      N₁-G = conj-swap X₁-Ex₃₄ °Z

    V-G : ∀ γ b → CCXZ₂₃ • G₂₆₈ γ b ≈ G₂₆₈ γ b • CCXZ₂₃
    V-G γ true  = V-G₁ γ
    V-G γ false = comm-inv (G-inv γ) (G-inv′ γ) (V-G₁ γ)

    white-ZX : ∀ γ b → Aᴾ true false true • G₂₆₈ γ b ≈ G₂₆₈ γ b • Aᴾ true false true
    white-ZX γ b = begin
      Aᴾ true false true • G₂₆₈ γ b
        ≈⟨ front _ Aᴾ-white ⟩
      (CCXZ₂₃ • Aᴾ true true false) • G₂₆₈ γ b
        ≈⟨ sym (comm-• (sym (V-G γ b)) (sym (black γ false b))) ⟩
      G₂₆₈ γ b • (CCXZ₂₃ • Aᴾ true true false)
        ≈⟨ back _ (sym Aᴾ-white) ⟩
      G₂₆₈ γ b • Aᴾ true false true ∎

    white : ∀ γ a b → Aᴾ true false a • G₂₆₈ γ b ≈ G₂₆₈ γ b • Aᴾ true false a
    white γ true  b = white-ZX γ b
    white γ false b = inv-row (Aᴾ-inv true false) (Aᴾ-inv′ true false) (white-ZX γ b)

    stage-β : ∀ β γ a b → Aᴾ true β a • G₂₆₈ γ b ≈ G₂₆₈ γ b • Aᴾ true β a
    stage-β true  = black
    stage-β false = white

    --------------------------------------------------------------------
    -- The first gate white on wire 3: the second gate does not see X there

    X₄² : X₄ • X₄ ≈ ε
    X₄² = lemma-cong↑ (X ↑ ↑ ↑ • X ↑ ↑ ↑) ε (lemma-cong↑ (X ↑ ↑ • X ↑ ↑) ε
            (lemma-cong↑ (X ↑ • X ↑) ε (lemma-cong↑ (X • X) ε X²)))

    module N₄ = Conj {₁₊ (₄₊ n)} X₄ X₄²

    S₃₄-X₄ : S₃₄.⟪ X₄ ⟫ ≈ X ↑ ↑ ↑
    S₃₄-X₄ = lemma-cong↑ (Ex ↑ ↑ • X ↑ ↑ ↑ • Ex ↑ ↑) (X ↑ ↑)
               (lemma-cong↑ (Ex ↑ • X ↑ ↑ • Ex ↑) (X ↑)
                 (lemma-cong↑ (Ex • X ↑ • Ex) (X ↓) S-X↑))

    N₄-rot : ∀ b → N₄.⟪ rot b ⟫ ≈ rot b
    N₄-rot true  = N₄.⟪⟫-fix (sym (L₄-top (ΛZX 3) X))
    N₄-rot false = N₄.⟪⟫-fix (sym (L₄-top (ΛXZ 3) X))

    X₄-X₂ : X₄ • X ↑ ↑ ≈ X ↑ ↑ • X₄
    X₄-X₂ = sym (lemma-cong↑ (X ↑ • X ↑ ↑ ↑) (X ↑ ↑ ↑ • X ↑)
                  (lemma-cong↑ (X ↓ • X ↑ ↑) (X ↑ ↑ • X ↓) (comm-↓↑ X (X ↑))))

    X₄-X₁ : X₄ • X ↑ ≈ X ↑ • X₄
    X₄-X₁ = sym (lemma-cong↑ (X ↓ • X ↑ ↑ ↑) (X ↑ ↑ ↑ • X ↓) (comm-↓↑ X (X ↑ ↑)))

    N₄-C : ∀ γ b → N₄.⟪ C₂₄₁ true γ b ⟫ ≈ C₂₄₁ true γ b
    N₄-C true  b = trans (conj-swap X₄-X₂ (rot b)) (N₂.⟪⟫-cong (N₄-rot b))
    N₄-C false b = trans (conj-swap X₄-X₁ (N₂.⟪ rot b ⟫))
                         (N₁.⟪⟫-cong (trans (conj-swap X₄-X₂ (rot b)) (N₂.⟪⟫-cong (N₄-rot b))))

    N₃-G : ∀ γ b → N₃.⟪ G₂₆₈ γ b ⟫ ≈ G₂₆₈ γ b
    N₃-G γ b = begin
      X ↑ ↑ ↑ • S₃₄.⟪ C₂₄₁ true γ b ⟫ • X ↑ ↑ ↑
        ≈⟨ cong (sym S₃₄-X₄) (back _ (sym S₃₄-X₄)) ⟩
      S₃₄.⟪ X₄ ⟫ • S₃₄.⟪ C₂₄₁ true γ b ⟫ • S₃₄.⟪ X₄ ⟫
        ≈⟨ sym (S₃₄.⟪⟫-•₃ refl refl refl) ⟩
      S₃₄.⟪ N₄.⟪ C₂₄₁ true γ b ⟫ ⟫
        ≈⟨ S₃₄.⟪⟫-cong (N₄-C γ b) ⟩
      S₃₄.⟪ C₂₄₁ true γ b ⟫ ∎

  -- (268)
  eq268 : ∀ α β γ a b → Aᴾ α β a • G₂₆₈ γ b ≈ G₂₆₈ γ b • Aᴾ α β a
  eq268 true  β γ a b = stage-β β γ a b
  eq268 false β γ a b = N₃.⟪⟫-≈ (stage-β β γ a b)
    (N₃.⟪⟫-•₂ (N₃-Aᴾ β a) (N₃-G γ b)) (N₃.⟪⟫-•₂ (N₃-G γ b) (N₃-Aᴾ β a))
