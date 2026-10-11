------------------------------------------------------------------------
-- Presentations of groups
--
-- White gates between P ⊗ P against a doubly controlled rotation
-- (Clément, Lemma D.5, Equations (227), (228))
--
-- N is the ZX on wire 0 from the wires 1 and 3.  Between P ⊗ P on the
-- wires 1 2:
--
--   (227)   the H gate H(0, 2; 1, °3) passes N
--   (228)   so does the triply controlled ZX on wire 0 from wire 2, from
--           wire 3 negatively, and from wire 1 in either colour
--
-- (227): by the Klein four-group on the wires 0 1 2 the gate Y is the box
-- on wire 2, white on wire 3, between P ⊗ P on the wires 0 1 — two
-- controls of the box.  N is the merge of the two colours of the triply
-- controlled ZX, (221), each of the form G₂ B G₂ B with the box wire of
-- its H gate on wire 2, and Y passes every letter: the box B on wire 1 —
-- between P ⊗ P on 0 1 this is (189) —, its white version, and the H
-- gate G₂ by the Klein four-group and (198).  (228): the rotation is
-- °G₂ °B °G₂ °B, and between P ⊗ P the first letter is the gate of (227)
-- and the second that of (220); a white control on wire 1 adds, by
-- (171), the CH from wire 3 negated there, which passes N letter by
-- letter.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.PConjugates
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; S-X↓)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals229 complete₂ complete₃
  using (ev-CH-°CH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq156)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq167)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (N₂-box₃′ ; eq183)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (τ₀₂-box₃ ; eq198 ; S₂₃-°box₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (PP₁₂ ; PP₀₂ ; PP₁₂² ; PP₀₂² ; PP-triangle₂ ; box₃″° ; G′-PP ; G₆-PP ; G₆′-PP ; e189)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃
  using (X₂-S₁₂ΛH₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃
  using (J′ ; CCZX₁₃ ; merge₀ ; eq220)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

private
  module Pj {n : ℕ} = Conj {₄₊ n} PP₁₂ PP₁₂²

-- H(0, 2; 1, °3) between P ⊗ P on the wires 1 2.
Y : Circuit (₄₊ n)
Y = Pj.⟪ N₃.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ ⟫

-- The triply controlled ZX on wire 0, white on wire 3 and black or white
-- on wire 1, between the same.
Y₁ Y₀ : Circuit (₄₊ n)
Y₁ = Pj.⟪ N₃.⟪ ZX₃ ⟫ ⟫
Y₀ = Pj.⟪ N₃.⟪ N₁.⟪ ZX₃ ⟫ ⟫ ⟫

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    N B °B G₂ °G₂ G₃ β β° Yᶠ : Circuit (₄₊ n)
    N   = CCZX₁₃
    B   = box₃′
    °B  = S₀₁.⟪ °box₃ ⟫
    G₂  = S₁₂.⟪ ΛH₀₁ ⟫
    °G₂ = N₃.⟪ G₂ ⟫
    G₃  = S₀₁.⟪ G₂ ⟫
    β   = S₁₂.⟪ box₃′ ⟫
    β°  = box₃″°
    Yᶠ  = PP₀₁ • β° • PP₀₁

    module Aj = Conj {₄₊ n} PP₀₁ PP₀₁²

    --------------------------------------------------------------------
    -- Y is the white box on wire 2 between P ⊗ P on the wires 0 1

    -- The Klein four-group on the wires 0 1 2.
    cb : PP₁₂ • PP₀₂ ≈ PP₀₁
    cb = begin
      PP₁₂ • PP₀₂           ≈⟨ back _ (sym (klein-ca Γ PP₀₁² PP₀₂² PP₁₂² PP-triangle₂)) ⟩
      PP₁₂ • PP₁₂ • PP₀₁    ≈⟨ sym assoc ⟩
      (PP₁₂ • PP₁₂) • PP₀₁  ≈⟨ trans (front _ PP₁₂²) left-unit ⟩
      PP₀₁ ∎

    bc : PP₀₂ • PP₁₂ ≈ PP₀₁
    bc = begin
      PP₀₂ • PP₁₂           ≈⟨ front _ (sym PP-triangle₂) ⟩
      (PP₀₁ • PP₁₂) • PP₁₂  ≈⟨ assoc ⟩
      PP₀₁ • PP₁₂ • PP₁₂    ≈⟨ trans (back _ PP₁₂²) right-unit ⟩
      PP₀₁ ∎

    Y-form : Y ≈ Yᶠ
    Y-form = begin
      PP₁₂ • °G₂ • PP₁₂
        ≈⟨ back _ (front _ G′-PP) ⟩
      PP₁₂ • (PP₀₂ • β° • PP₀₂) • PP₁₂
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (PP₁₂ • PP₀₂) • β° • (PP₀₂ • PP₁₂)
        ≈⟨ cong cb (back _ bc) ⟩
      PP₀₁ • β° • PP₀₁ ∎

    --------------------------------------------------------------------
    -- It passes the box on wire 1, black …

    Yᶠ-B : Yᶠ • B ≈ B • Yᶠ
    Yᶠ-B = Aj.⟪⟫-≈ e189 (Aj.⟪⟫-•₂ refl (Aj.⟪⟫-⟪⟫ B)) (Aj.⟪⟫-•₂ (Aj.⟪⟫-⟪⟫ B) refl)

    -- … and white on wire 2: X there is on the box wire of the white box.
    X₂-β : X ↑ ↑ • β ≈ β • X ↑ ↑
    X₂-β = S₁₂.⟪⟫-≈
      (S₀₁.⟪⟫-≈ eq156 (S₀₁.⟪⟫-•₂ S-X↓ refl) (S₀₁.⟪⟫-•₂ refl S-X↓))
      (S₁₂.⟪⟫-•₂ S₁₂-X₁ refl) (S₁₂.⟪⟫-•₂ refl S₁₂-X₁)

    X₂-β° : X ↑ ↑ • β° ≈ β° • X ↑ ↑
    X₂-β° = N₃.⟪⟫-≈ X₂-β (N₃.⟪⟫-•₂ N₃-X₂ refl) (N₃.⟪⟫-•₂ refl N₃-X₂)
      where
      N₃-X₂ : N₃.⟪ X ↑ ↑ ⟫ ≈ X ↑ ↑
      N₃-X₂ = N₃.⟪⟫-fix (sym X₂-X₃)

    N₂-Yᶠ : N₂.⟪ Yᶠ ⟫ ≈ Yᶠ
    N₂-Yᶠ = N₂.⟪⟫-•₃ N₂-PP₀₁ (N₂.⟪⟫-fix X₂-β°) N₂-PP₀₁

    Yᶠ-°B : Yᶠ • °B ≈ °B • Yᶠ
    Yᶠ-°B = N₂.⟪⟫-≈ Yᶠ-B (N₂.⟪⟫-•₂ N₂-Yᶠ N₂-box₃′) (N₂.⟪⟫-•₂ N₂-box₃′ N₂-Yᶠ)

    --------------------------------------------------------------------
    -- … and the H gate with its box wire on wire 2

    G₂-PP : G₂ ≈ PP₀₂ • β • PP₀₂
    G₂-PP = trans (S₁₂.⟪⟫-cong ΛH₀₁-PP) (S₁₂.⟪⟫-•₃ (O-L PP) refl (O-L PP))

    G₃-PP : G₃ ≈ PP₁₂ • β • PP₁₂
    G₃-PP = trans G₆-PP (back _ (front _ τ₀₂-box₃))

    -- (198), and then under the lower swap.
    G₂-β° : G₂ • β° ≈ β° • G₂
    G₂-β° = trans (back _ (sym m)) (trans eq198 (front _ m))
      where
      m : S₁₂.⟪ S₀₁.⟪ N₃.⟪ box₃ ⟫ ⟫ ⟫ ≈ β°
      m = trans (S₁₂.⟪⟫-cong (S₀₁-N₃ box₃)) (S₁₂-N₃ box₃′)

    S₀₁-β° : S₀₁.⟪ β° ⟫ ≈ β°
    S₀₁-β° = trans (S₀₁-N₃ β) (N₃.⟪⟫-cong τ₀₂-box₃)

    G₃-β° : G₃ • β° ≈ β° • G₃
    G₃-β° = S₀₁.⟪⟫-≈ G₂-β° (S₀₁.⟪⟫-•₂ refl S₀₁-β°) (S₀₁.⟪⟫-•₂ S₀₁-β° refl)

    Yᶠ-G₂ : Yᶠ • G₂ ≈ G₂ • Yᶠ
    Yᶠ-G₂ = begin
      Yᶠ • G₂
        ≈⟨ back _ G₂-PP ⟩
      (PP₀₁ • β° • PP₀₁) • (PP₀₂ • β • PP₀₂)
        ≈⟨ klein Γ PP₀₁² PP₀₂² PP₁₂² PP-triangle₂ h ⟩
      (PP₀₂ • β • PP₀₂) • (PP₀₁ • β° • PP₀₁)
        ≈⟨ front _ (sym G₂-PP) ⟩
      G₂ • Yᶠ ∎
      where
      h : β° • (PP₁₂ • β • PP₁₂) ≈ (PP₁₂ • β • PP₁₂) • β°
      h = trans (back _ (sym G₃-PP)) (trans (sym G₃-β°) (front _ G₃-PP))

    --------------------------------------------------------------------
    -- … the H gate H(1, 2; 0, 3): the Klein four-group again, and (198)
    -- with the colours on wire 3 exchanged …

    β-°G₂ : β • °G₂ ≈ °G₂ • β
    β-°G₂ = sym (N₃.⟪⟫-≈ G₂-β° (N₃.⟪⟫-•₂ refl (N₃.⟪⟫-⟪⟫ β)) (N₃.⟪⟫-•₂ (N₃.⟪⟫-⟪⟫ β) refl))

    Yᶠ-G₃ : Yᶠ • G₃ ≈ G₃ • Yᶠ
    Yᶠ-G₃ = begin
      Yᶠ • G₃
        ≈⟨ back _ G₃-PP ⟩
      (PP₀₁ • β° • PP₀₁) • (PP₁₂ • β • PP₁₂)
        ≈⟨ sym (klein Γ PP₁₂² PP₀₁² PP₀₂² cb h) ⟩
      (PP₁₂ • β • PP₁₂) • (PP₀₁ • β° • PP₀₁)
        ≈⟨ front _ (sym G₃-PP) ⟩
      G₃ • Yᶠ ∎
      where
      h : β • (PP₀₂ • β° • PP₀₂) ≈ (PP₀₂ • β° • PP₀₂) • β
      h = trans (back _ (sym G′-PP)) (trans β-°G₂ (front _ G′-PP))

    -- … and the box on wire 0, which between P ⊗ P on the wires 0 1 is
    -- the H gate of (183).
    e183 : (ΛH 2 ↓ᵏ n) • β° ≈ β° • (ΛH 2 ↓ᵏ n)
    e183 = trans (back _ (sym bridge)) (trans eq183 (front _ bridge))
      where
      bridge : S₀₁.⟪ S₁₂.⟪ S₂₃.⟪ S₀₁.⟪ °box₃ ⟫ ⟫ ⟫ ⟫ ≈ β°
      bridge = trans
        (S₀₁.⟪⟫-cong (trans
          (S₁₂.⟪⟫-cong (trans (S₂₃.⟪⟫-•₃ (L-S₂₃ Ex) S₂₃-°box₃ (L-S₂₃ Ex)) (S₀₁-N₃ box₃)))
          (S₁₂-N₃ box₃′)))
        S₀₁-β°

    Yᶠ-box₃ : Yᶠ • box₃ ≈ box₃ • Yᶠ
    Yᶠ-box₃ = sym (Aj.⟪⟫-≈ e183 (Aj.⟪⟫-•₂ (Aj.⟪⟫-⟪⟫ box₃) refl) (Aj.⟪⟫-•₂ refl (Aj.⟪⟫-⟪⟫ box₃)))

    --------------------------------------------------------------------
    -- So it passes both colours of the triply controlled ZX

    °ZX₃-form₄ : N₂.⟪ ZX₃ ⟫ ≈ G₂ • °B • G₂ • °B
    °ZX₃-form₄ = trans (N₂.⟪⟫-cong ZX₃-form₄) (N₂.⟪⟫-•₄ N-G N₂-box₃′ N-G N₂-box₃′)
      where
      N-G : N₂.⟪ G₂ ⟫ ≈ G₂
      N-G = N₂.⟪⟫-fix X₂-S₁₂ΛH₀₁

    Yᶠ-N : Yᶠ • N ≈ N • Yᶠ
    Yᶠ-N = begin
      Yᶠ • N
        ≈⟨ back _ (sym merge₀) ⟩
      Yᶠ • (N₂.⟪ ZX₃ ⟫ • ZX₃)
        ≈⟨ back _ (cong °ZX₃-form₄ ZX₃-form₄) ⟩
      Yᶠ • ((G₂ • °B • G₂ • °B) • (G₂ • B • G₂ • B))
        ≈⟨ comm-• (comm-abab Yᶠ-G₂ Yᶠ-°B) (comm-abab Yᶠ-G₂ Yᶠ-B) ⟩
      ((G₂ • °B • G₂ • °B) • (G₂ • B • G₂ • B)) • Yᶠ
        ≈⟨ front _ (sym (cong °ZX₃-form₄ ZX₃-form₄)) ⟩
      (N₂.⟪ ZX₃ ⟫ • ZX₃) • Yᶠ
        ≈⟨ front _ merge₀ ⟩
      N • Yᶠ ∎

  -- The letters the gate passes, for (245).
  Y-B : Y • box₃′ ≈ box₃′ • Y
  Y-B = trans (front _ Y-form) (trans Yᶠ-B (back _ (sym Y-form)))

  Y-G₂ : Y • S₁₂.⟪ ΛH₀₁ ⟫ ≈ S₁₂.⟪ ΛH₀₁ ⟫ • Y
  Y-G₂ = trans (front _ Y-form) (trans Yᶠ-G₂ (back _ (sym Y-form)))

  -- … and those for (244).
  Y-G₃ : Y • S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ ≈ S₀₁.⟪ S₁₂.⟪ ΛH₀₁ ⟫ ⟫ • Y
  Y-G₃ = trans (front _ Y-form) (trans Yᶠ-G₃ (back _ (sym Y-form)))

  Y-box₃ : Y • box₃ ≈ box₃ • Y
  Y-box₃ = trans (front _ Y-form) (trans Yᶠ-box₃ (back _ (sym Y-form)))

  -- (227)
  eq227 : Y • CCZX₁₃ ≈ CCZX₁₃ • Y
  eq227 = trans (front _ Y-form) (trans Yᶠ-N (back _ (sym Y-form)))

  ----------------------------------------------------------------------
  -- (228)

  private
    °B₁ p″ : Circuit (₄₊ n)
    °B₁ = N₃.⟪ box₃′ ⟫
    p″  = P₀₃ °CH

    N-Y : N • Y ≈ Y • N
    N-Y = sym eq227

    N-J′ : N • J′ ≈ J′ • N
    N-J′ = sym eq220

    P-°B₁ : Pj.⟪ °B₁ ⟫ ≈ J′
    P-°B₁ = sym G₆′-PP

  -- The rotation, black on wire 1, in the two letters of (227) and (220).
  Y₁-form : Y₁ ≈ Y • J′ • Y • J′
  Y₁-form = trans (Pj.⟪⟫-cong (trans (N₃.⟪⟫-cong ZX₃-form₄) (N₃.⟪⟫-•₄ refl refl refl refl)))
                  (Pj.⟪⟫-•₄ refl P-°B₁ refl P-°B₁)

  eq228₁ : Y₁ • CCZX₁₃ ≈ CCZX₁₃ • Y₁
  eq228₁ = begin
    Y₁ • N                      ≈⟨ front _ Y₁-form ⟩
    (Y • J′ • Y • J′) • N       ≈⟨ sym (comm-abab N-Y N-J′) ⟩
    N • (Y • J′ • Y • J′)       ≈⟨ back _ (sym Y₁-form) ⟩
    N • Y₁ ∎

  private
    -- White on wire 1.  The box on wire 1 does not see X there …
    X₁-B : X ↑ • B ≈ B • X ↑
    X₁-B = S₀₁.⟪⟫-≈ eq156 (S₀₁.⟪⟫-•₂ S-X↓ refl) (S₀₁.⟪⟫-•₂ refl S-X↓)

    -- … and the H gate gains the CH from wire 3: (171) under the cycle
    -- 1 → 3 → 2 → 1.
    G₂² : G₂ • G₂ ≈ ε
    G₂² = S₁₂.⟪⟫-invol (S₀₁.⟪⟫-invol eq167)

    e171₁ : G₂ • N₁.⟪ G₂ ⟫ ≈ P₀₃ CH
    e171₁ = S₂₃.⟪⟫-≈
      (S₁₂.⟪⟫-≈ eq171ᶜ (S₁₂.⟪⟫-•₂ S₁₂-ΛH₂′ mA) (O-L CH))
      (S₂₃.⟪⟫-•₂ mG mB) (O-S₂₃ CH)
      where
      mA : S₁₂.⟪ °ΛH₂′ ⟫ ≈ N₁.⟪ ΛH₂′ ⟫
      mA = S₁₂.⟪⟫-•₃ S₁₂-X₂ S₁₂-ΛH₂′ S₁₂-X₂
      mG : S₂₃.⟪ ΛH₂′ ⟫ ≈ G₂
      mG = S₂₃.⟪⟫-⟪⟫ G₂
      mB : S₂₃.⟪ N₁.⟪ ΛH₂′ ⟫ ⟫ ≈ N₁.⟪ G₂ ⟫
      mB = S₂₃.⟪⟫-•₃ S₂₃-X₁ mG S₂₃-X₁

    N₁-G₂ : N₁.⟪ G₂ ⟫ ≈ G₂ • P₀₃ CH
    N₁-G₂ = begin
      N₁.⟪ G₂ ⟫                 ≈⟨ sym left-unit ⟩
      ε • N₁.⟪ G₂ ⟫             ≈⟨ front _ (sym G₂²) ⟩
      (G₂ • G₂) • N₁.⟪ G₂ ⟫     ≈⟨ assoc ⟩
      G₂ • G₂ • N₁.⟪ G₂ ⟫       ≈⟨ back _ e171₁ ⟩
      G₂ • P₀₃ CH ∎

    -- The CH from wire 3 under X on wire 3.
    N₃-P₀₃ : N₃.⟪ P₀₃ CH ⟫ ≈ p″
    N₃-P₀₃ = sym (trans (S₀₁.⟪⟫-cong (S₁₂-N₃ (P₂₃ CH))) (S₀₁-N₃ (P₁₃ CH)))

    -- It passes N letter by letter.
    Pj-p″ : Pj.⟪ p″ ⟫ ≈ p″
    Pj-p″ = Pj.⟪⟫-fix (sym (P₀₃-U °CH PP))

    N-form : N ≈ CH ↓ • CZ₃₀ • CH ↓ • CZ₃₀
    N-form = S₂₃.⟪⟫-•₄ (L-S₂₃ CH) m (L-S₂₃ CH) m
      where
      m : S₂₃.⟪ CZ₂₀ ⟫ ≈ CZ₃₀
      m = trans (O-S₂₃ CZ) (sym CZ₃₀-P)

    p″-a : p″ • CH ↓ ≈ CH ↓ • p″
    p″-a = sym (comm-01-03 CH °CH ev-CH-°CH)

    p″-c : p″ • CZ₃₀ ≈ CZ₃₀ • p″
    p″-c = begin
      p″ • CZ₃₀             ≈⟨ back _ CZ₃₀-P ⟩
      P₀₃ °CH • P₀₃ CZ      ≈⟨ sym (P₀₃-• °CH CZ) ⟩
      P₀₃ (°CH • CZ)        ≈⟨ P₀₃-sem (°CH • CZ) (CZ • °CH) Eq.refl ⟩
      P₀₃ (CZ • °CH)        ≈⟨ P₀₃-• CZ °CH ⟩
      P₀₃ CZ • P₀₃ °CH      ≈⟨ front _ (sym CZ₃₀-P) ⟩
      CZ₃₀ • p″ ∎

    N-p″ : N • p″ ≈ p″ • N
    N-p″ = sym (trans (back _ N-form) (trans (comm-abab p″-a p″-c) (front _ (sym N-form))))

  eq228₀ : Y₀ • CCZX₁₃ ≈ CCZX₁₃ • Y₀
  eq228₀ = begin
    Y₀ • N                                      ≈⟨ front _ Y₀-form ⟩
    ((Y • p″) • J′ • (Y • p″) • J′) • N         ≈⟨ sym (comm-abab (comm-• N-Y N-p″) N-J′) ⟩
    N • ((Y • p″) • J′ • (Y • p″) • J′)         ≈⟨ back _ (sym Y₀-form) ⟩
    N • Y₀ ∎
    where
    N₁-form : N₁.⟪ ZX₃ ⟫ ≈ (G₂ • P₀₃ CH) • B • (G₂ • P₀₃ CH) • B
    N₁-form = trans (N₁.⟪⟫-cong ZX₃-form₄)
      (N₁.⟪⟫-•₄ N₁-G₂ (N₁.⟪⟫-fix X₁-B) N₁-G₂ (N₁.⟪⟫-fix X₁-B))

    N₃-GP : N₃.⟪ G₂ • P₀₃ CH ⟫ ≈ °G₂ • p″
    N₃-GP = N₃.⟪⟫-•₂ refl N₃-P₀₃

    P-GP : Pj.⟪ °G₂ • p″ ⟫ ≈ Y • p″
    P-GP = Pj.⟪⟫-•₂ refl Pj-p″

    Y₀-form : Y₀ ≈ (Y • p″) • J′ • (Y • p″) • J′
    Y₀-form = trans (Pj.⟪⟫-cong (trans (N₃.⟪⟫-cong N₁-form) (N₃.⟪⟫-•₄ N₃-GP refl N₃-GP refl)))
                    (Pj.⟪⟫-•₄ P-GP P-°B₁ P-GP P-°B₁)
