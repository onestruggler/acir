------------------------------------------------------------------------
-- Presentations of groups
--
-- The triply controlled ZX against a doubly controlled rotation of the
-- other colour on the same target (Clément, Lemma D.5, Equation (239))
--
-- The second gate is the ZX or XZ on wire 0 from wire 2, negatively, and
-- from wire 3 in either colour: t c t c with t the CH from wire 2 negated
-- there and c the CZ from wire 3, black or white.  t passes the triply
-- controlled ZX and XZ, (232) and (233).  The white c passes them too,
-- (231); the black one exchanges them — it is a letter of (212) — and
-- then `pass-pqpq` applies.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Families
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (CZ₃₀ ; CZ₃₀² ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (CCZX₂₃ ; CCXZ₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (S₀₁-N₃ ; S₁₂-N₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations4 complete₂ complete₃
  using (eq231 ; eq232 ; eq233)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; °CH₂₀ ; eq117 ; eq118)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

-- The ZX and XZ on wire 0 from wire 2, negatively, and wire 3 …
R₁ R₁′ : Circuit (₄₊ n)
R₁  = N₂.⟪ CCZX₂₃ ⟫
R₁′ = N₂.⟪ CCXZ₂₃ ⟫

-- … and from both negatively.
R₀ R₀′ : Circuit (₄₊ n)
R₀  = N₃.⟪ R₁ ⟫
R₀′ = N₃.⟪ R₁′ ⟫

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    t c °c G : Circuit (₄₊ n)
    t  = °CH₂₀
    c  = CZ₃₀
    °c = P₀₃ °CZ
    G  = ΛH₂′

    N₂-c : N₂.⟪ P₀₃ CZ ⟫ ≈ c
    N₂-c = trans (N₂.⟪⟫-fix (sym (P₀₃-U CZ (X ↑)))) (sym CZ₃₀-P)

    R₁-form : R₁ ≈ t • c • t • c
    R₁-form = trans (N₂.⟪⟫-cong (S₀₁.⟪⟫-•₄ refl refl refl refl)) (N₂.⟪⟫-•₄ refl N₂-c refl N₂-c)

    N₃-t : N₃.⟪ t ⟫ ≈ t
    N₃-t = N₃.⟪⟫-fix (sym (L₃-top °CH₂₀ X))

    N₃-c : N₃.⟪ c ⟫ ≈ °c
    N₃-c = trans (N₃.⟪⟫-cong CZ₃₀-P)
                 (sym (trans (S₀₁.⟪⟫-cong (S₁₂-N₃ (P₂₃ CZ))) (S₀₁-N₃ (P₁₃ CZ))))

    R₀-form : R₀ ≈ t • °c • t • °c
    R₀-form = trans (N₃.⟪⟫-cong R₁-form) (N₃.⟪⟫-•₄ N₃-t N₃-c N₃-t N₃-c)

    -- The black CZ from wire 3 is a letter of (212) and (213).
    c-ZX₃ : c • ZX₃ ≈ XZ₃ • c
    c-ZX₃ = begin
      c • ZX₃                   ≈⟨ back _ eq212 ⟩
      c • (G • c • G • c)       ≈⟨ by-passoc (□ • (□ • □ • □ • □)) ((□ • □ • □ • □) • □) Eq.refl ⟩
      (c • G • c • G) • c       ≈⟨ front _ (sym eq213) ⟩
      XZ₃ • c ∎

    c-XZ₃ : c • XZ₃ ≈ ZX₃ • c
    c-XZ₃ = sym (conj-comm CZ₃₀² (trans (sym assoc) (trans (front _ c-ZX₃) (cancelʳ _ CZ₃₀²))))

    °c-ZX₃ : °c • ZX₃ ≈ ZX₃ • °c
    °c-ZX₃ = comm-inv eq208 eq208′ eq231

    -- Inverses.
    R₁R₁′ : R₁ • R₁′ ≈ ε
    R₁R₁′ = trans (sym (N₂.⟪⟫-• CCZX₂₃ CCXZ₂₃)) (trans (N₂.⟪⟫-cong W₂₃V₂₃) N₂.⟪⟫-ε)
      where
      W₂₃V₂₃ : CCZX₂₃ • CCXZ₂₃ ≈ ε
      W₂₃V₂₃ = trans (sym (S₀₁.⟪⟫-• (U₃ CCZX) (U₃ CCXZ)))
              (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCZX • CCXZ) ε eq117)) S₀₁.⟪⟫-ε)

    R₁′R₁ : R₁′ • R₁ ≈ ε
    R₁′R₁ = trans (sym (N₂.⟪⟫-• CCXZ₂₃ CCZX₂₃)) (trans (N₂.⟪⟫-cong V₂₃W₂₃) N₂.⟪⟫-ε)
      where
      V₂₃W₂₃ : CCXZ₂₃ • CCZX₂₃ ≈ ε
      V₂₃W₂₃ = trans (sym (S₀₁.⟪⟫-• (U₃ CCXZ) (U₃ CCZX)))
              (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCXZ • CCZX) ε eq118)) S₀₁.⟪⟫-ε)

    R₀R₀′ : R₀ • R₀′ ≈ ε
    R₀R₀′ = trans (sym (N₃.⟪⟫-• R₁ R₁′)) (trans (N₃.⟪⟫-cong R₁R₁′) N₃.⟪⟫-ε)

    R₀′R₀ : R₀′ • R₀ ≈ ε
    R₀′R₀ = trans (sym (N₃.⟪⟫-• R₁′ R₁)) (trans (N₃.⟪⟫-cong R₁′R₁) N₃.⟪⟫-ε)

  -- The inverses, for later use.
  R₁-inv : R₁ • R₁′ ≈ ε
  R₁-inv = R₁R₁′

  R₁-inv′ : R₁′ • R₁ ≈ ε
  R₁-inv′ = R₁′R₁

  -- (239), the control on wire 3 black: the ZX …
  eq239₁ : ZX₃ • R₁ ≈ R₁ • ZX₃
  eq239₁ = sym (begin
    R₁ • ZX₃                  ≈⟨ front _ R₁-form ⟩
    (t • c • t • c) • ZX₃     ≈⟨ pass-pqpq eq232 eq233 c-ZX₃ c-XZ₃ ⟩
    ZX₃ • (t • c • t • c)     ≈⟨ back _ (sym R₁-form) ⟩
    ZX₃ • R₁ ∎)

  -- … and the XZ.
  eq239₁′ : ZX₃ • R₁′ ≈ R₁′ • ZX₃
  eq239₁′ = comm-inv R₁R₁′ R₁′R₁ eq239₁

  -- (239), the control on wire 3 white.
  eq239₀ : ZX₃ • R₀ ≈ R₀ • ZX₃
  eq239₀ = sym (begin
    R₀ • ZX₃                    ≈⟨ front _ R₀-form ⟩
    (t • °c • t • °c) • ZX₃     ≈⟨ sym (comm-abab (sym eq232) (sym °c-ZX₃)) ⟩
    ZX₃ • (t • °c • t • °c)     ≈⟨ back _ (sym R₀-form) ⟩
    ZX₃ • R₀ ∎)

  eq239₀′ : ZX₃ • R₀′ ≈ R₀′ • ZX₃
  eq239₀′ = comm-inv R₀R₀′ R₀′R₀ eq239₀
