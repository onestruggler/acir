------------------------------------------------------------------------
-- Presentations of groups
--
-- Gates that pass a controlled rotation (Clément, Lemma D.5, Equations
-- (229)–(233))
--
--   (229)   −Z on a control           the triply controlled ZX, XZ
--   (230)   the CH onto wire 1 from wire 2, negated there
--                                     the ZX on wire 0 from wires 2, 3
--   (231)   the CZ of wires 0 3, negated on wire 3
--                                     the triply controlled XZ
--   (232)   the CH onto wire 0 from wire 2, negated there
--                                     the triply controlled ZX
--   (233)   the same                  the triply controlled XZ
--
-- Each passes the rotation letter by letter, in the right form of the
-- rotation: the definition a B a B for (229) and (232) — the box B by
-- (164) in (232) —, the form (213) with the box wire of the H gate on
-- wire 2 for (231), where the H gate is passed as in (190).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Rotations4
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
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals229 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (eq164)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; CCZX₂₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (°CZ₂₀-ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
  using (ΛH₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; °CH₂₀ ; °CZ₂₀-O ; eq134)
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
    a b c B : Circuit (₄₊ n)
    a = CH ↓
    b = CZ₂₀
    c = CZ₃₀
    B = box₃′

    -- The CH from wire 2, negated there, as a two-wire circuit on the
    -- wires 0 2.
    °CH₂₀-O : °CH₂₀ ≈ O °CH
    °CH₂₀-O = sym (S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ X) refl (P₂₃-S₀₁ X))

  ----------------------------------------------------------------------
  -- (229)

  private
    z° : Circuit (₄₊ n)
    z° = Z° ↑ ↑

    z°-a : z° • a ≈ a • z°
    z°-a = sym (L-comm CH Z°)

    z°-b : z° • b ≈ b • z°
    z°-b = comm-12-02 (Z° ↑) CZ ev-Z°-CZ

    z°-c : z° • c ≈ c • z°
    z°-c = begin
      z° • c                ≈⟨ back _ CZ₃₀-P ⟩
      U (Z° ↑) • P₀₃ CZ     ≈⟨ sym (P₀₃-U CZ (Z° ↑)) ⟩
      P₀₃ CZ • U (Z° ↑)     ≈⟨ front _ (sym CZ₃₀-P) ⟩
      c • z° ∎

    z°-box₃ : z° • box₃ ≈ box₃ • z°
    z°-box₃ = comm-• (comm-abab z°-a z°-b) (comm-• z°-c (comm-• (comm-abab z°-b z°-a) z°-c))

    z°-B : z° • B ≈ B • z°
    z°-B = S₀₁.⟪⟫-≈ z°-box₃ (S₀₁.⟪⟫-•₂ (P₂₃-S₀₁ Z°) refl) (S₀₁.⟪⟫-•₂ refl (P₂₃-S₀₁ Z°))

  eq229 : z° • ZX₃ ≈ ZX₃ • z°
  eq229 = comm-abab z°-a z°-B

  eq229′ : z° • XZ₃ ≈ XZ₃ • z°
  eq229′ = comm-abab z°-B z°-a

  ----------------------------------------------------------------------
  -- (230)

  private
    t₁ : Circuit (₄₊ n)
    t₁ = U °CH

    -- (134) under the lower swap.
    t₁-p : t₁ • CH₂₀ ≈ CH₂₀ • t₁
    t₁-p = sym (S₀₁.⟪⟫-≈ eq134 (S₀₁.⟪⟫-•₂ refl m) (S₀₁.⟪⟫-•₂ m refl))
      where
      m : S₀₁.⟪ °CH₂₀ ⟫ ≈ t₁
      m = S₀₁.⟪⟫-•₃ (P₂₃-S₀₁ X) (S₀₁.⟪⟫-⟪⟫ (U CH)) (P₂₃-S₀₁ X)

    t₁-c : t₁ • P₀₃ CZ ≈ P₀₃ CZ • t₁
    t₁-c = sym (P₀₃-U CZ °CH)

    CCZX₂₃-form : CCZX₂₃ ≈ CH₂₀ • P₀₃ CZ • CH₂₀ • P₀₃ CZ
    CCZX₂₃-form = S₀₁.⟪⟫-•₄ refl refl refl refl

  eq230 : t₁ • CCZX₂₃ ≈ CCZX₂₃ • t₁
  eq230 = begin
    t₁ • CCZX₂₃                                     ≈⟨ back _ CCZX₂₃-form ⟩
    t₁ • (CH₂₀ • P₀₃ CZ • CH₂₀ • P₀₃ CZ)            ≈⟨ comm-abab t₁-p t₁-c ⟩
    (CH₂₀ • P₀₃ CZ • CH₂₀ • P₀₃ CZ) • t₁            ≈⟨ front _ (sym CCZX₂₃-form) ⟩
    CCZX₂₃ • t₁ ∎

  ----------------------------------------------------------------------
  -- (231)

  private
    °c G₂ : Circuit (₄₊ n)
    °c = P₀₃ °CZ
    G₂ = S₁₂.⟪ ΛH₀₁ ⟫

    °c-b : °c • b ≈ b • °c
    °c-b = comm-03-02 °CZ CZ ev-°CZ-CZ

    -- The H gate as in (190), under the upper swap.
    °c-G₂ : °c • G₂ ≈ G₂ • °c
    °c-G₂ = S₂₃.⟪⟫-≈ °CZ₂₀-ΛH₂′ (S₂₃.⟪⟫-•₂ m₁ m₂) (S₂₃.⟪⟫-•₂ m₂ m₁)
      where
      m₁ : S₂₃.⟪ °CZ₂₀ ⟫ ≈ °c
      m₁ = trans (S₂₃.⟪⟫-cong °CZ₂₀-O) (O-S₂₃ °CZ)
      m₂ : S₂₃.⟪ ΛH₂′ ⟫ ≈ G₂
      m₂ = S₂₃.⟪⟫-⟪⟫ G₂

  eq231 : °c • XZ₃ ≈ XZ₃ • °c
  eq231 = begin
    °c • XZ₃                      ≈⟨ back _ XZ₃-form₃ ⟩
    °c • (b • G₂ • b • G₂)        ≈⟨ comm-abab °c-b °c-G₂ ⟩
    (b • G₂ • b • G₂) • °c        ≈⟨ front _ (sym XZ₃-form₃) ⟩
    XZ₃ • °c ∎

  ----------------------------------------------------------------------
  -- (232)

  private
    t₀ : Circuit (₄₊ n)
    t₀ = °CH₂₀

    t₀-a : t₀ • a ≈ a • t₀
    t₀-a = begin
      t₀ • a          ≈⟨ front _ °CH₂₀-O ⟩
      O °CH • a       ≈⟨ sym (comm-01-02 CH °CH ev-CH-°CH) ⟩
      a • O °CH       ≈⟨ back _ (sym °CH₂₀-O) ⟩
      a • t₀ ∎

    -- (164) under the lower swap.
    t₀-B : t₀ • B ≈ B • t₀
    t₀-B = begin
      t₀ • B          ≈⟨ front _ °CH₂₀-O ⟩
      O °CH • B       ≈⟨ S₀₁.⟪⟫-≈ eq164 (S₀₁.⟪⟫-• (U °CH) box₃) (S₀₁.⟪⟫-• box₃ (U °CH)) ⟩
      B • O °CH       ≈⟨ back _ (sym °CH₂₀-O) ⟩
      B • t₀ ∎

  eq232 : t₀ • ZX₃ ≈ ZX₃ • t₀
  eq232 = comm-abab t₀-a t₀-B

  -- (233)
  eq233 : t₀ • XZ₃ ≈ XZ₃ • t₀
  eq233 = comm-abab t₀-B t₀-a

  -- The spelling of the gate as a two-wire circuit, for later use.
  °CH₂₀-as-O : °CH₂₀ ≈ O °CH
  °CH₂₀-as-O = °CH₂₀-O
