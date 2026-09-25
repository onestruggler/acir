------------------------------------------------------------------------
-- Presentations of groups
--
-- A four-wire gadget against a box with the opposite colour on a shared
-- control (Clément, Lemma D.12, Equation (318), the all-black case)
--
-- At width 5 + k, with the wires numbered from the bottom as D = 0,
-- C = 1, B = 2, A = 3 and the top wires 4 …: the triply controlled ZX
-- on C from D, B and A, `G₁ = S₀₁⟪ ZX₃ ⟫`, and the box on D controlled
-- by C, by B white and by the top wires, wire A idle,
-- `G₂ = N₂⟪ place 3 (Λ□ (3 + k)) ⟫`, commute.  The paper's proof: the
-- box is W B′ V B′ by (269), negated on B — W, V the doubly controlled
-- ZX and XZ on D from C and B white, B′ the box on C controlled by D and
-- the top wires, B and A idle — and G₁ passes each factor: the doubly
-- controlled gates by (216), (217) under X on B, and B′ by (290) under
-- the swap of the wires D C, where (290)'s box has its box wire on C as
-- B′ does, up to moving it along an idle wire (274).  That last
-- identification is one semantic step one width down, with wire A idle.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Gadget318
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂ using (module N₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (module S₀₁)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃ using (ZX₃)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃ using (K ; eq216 ; eq217)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.TwoBoxes complete₂ complete₃ using (eq290)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□ ; cf-B)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm using (cf-• ; cf-loc ; cf-~)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Idle using (yB ; cf-yB ; place-yB)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
  using (place ; place-• ; place-low ; place-cong ; lemma-5-1 ; low-comm)

------------------------------------------------------------------------
-- The gates

-- The triply controlled ZX on wire 1 from the wires 0 2 3.
G₁ : ∀ {k} → Circuit (₁₊ (₄₊ k))
G₁ = S₀₁.⟪ ZX₃ ⟫

-- The box on wire 0 controlled by the wires 1, 2 and 4 …, wire 3 idle;
-- and the same with the control on wire 2 white.
Box₃ G₂ : ∀ k → Circuit (₁₊ (₄₊ k))
Box₃ k = place 3 (Λ□ (₃₊ k))
G₂   k = N₂.⟪ Box₃ k ⟫

module _ (k : ℕ) (complete : Complete (₁₊ k)) where
  open Tools ((₁₊ (₄₊ k)) VRel,_===_)

  private
    -- The smaller box on wire 1, controlled by wire 0 and the wires
    -- 4 …; the wires 2 3 idle.
    B′ : Circuit (₁₊ (₄₊ k))
    B′ = place 3 (B□ k)

    ------------------------------------------------------------------
    -- The box, factor by factor ((269))

    Box₃-form : Box₃ k ≈ CCZX • B′ • CCXZ • B′
    Box₃-form = begin
      place 3 (CCZX • B□ k • CCXZ • B□ k)
        ≈⟨ place-• 3 CCZX (B□ k • CCXZ • B□ k) ⟩
      place 3 CCZX • place 3 (B□ k • CCXZ • B□ k)
        ≈⟨ back _ (place-• 3 (B□ k) (CCXZ • B□ k)) ⟩
      place 3 CCZX • place 3 (B□ k) • place 3 (CCXZ • B□ k)
        ≈⟨ back _ (back _ (place-• 3 CCXZ (B□ k))) ⟩
      place 3 CCZX • B′ • place 3 CCXZ • B′
        ≈⟨ cong (place-low 3 (CCZX {0})) (back _ (front _ (place-low 3 (CCXZ {0})))) ⟩
      CCZX • B′ • CCXZ • B′ ∎

    -- X on wire 2, which B′ leaves idle, passes it: one width down.
    X₂-B′ : X ↑ ↑ • B′ ≈ B′ • X ↑ ↑
    X₂-B′ = begin
      X ↑ ↑ • B′
        ≈⟨ front _ (sym (place-low 3 (X {0} ↑ ↑))) ⟩
      place 3 (X ↑ ↑) • place 3 (B□ k)
        ≈⟨ sym (place-• 3 (X ↑ ↑) (B□ k)) ⟩
      place 3 (X ↑ ↑ • B□ k)
        ≈⟨ lemma-5-1 3 complete
             (cf-~ (cf-• (cf-loc (X {0} ↑ ↑)) (cf-B k)) (cf-• (cf-B k) (cf-loc (X {0} ↑ ↑))) Eq.refl Eq.refl) ⟩
      place 3 (B□ k • X ↑ ↑)
        ≈⟨ place-• 3 (B□ k) (X ↑ ↑) ⟩
      place 3 (B□ k) • place 3 (X ↑ ↑)
        ≈⟨ back _ (place-low 3 (X {0} ↑ ↑)) ⟩
      B′ • X ↑ ↑ ∎

    G₂-form : G₂ k ≈ N₂.⟪ CCZX ⟫ • B′ • N₂.⟪ CCXZ ⟫ • B′
    G₂-form = trans (N₂.⟪⟫-cong Box₃-form)
                    (N₂.⟪⟫-•₄ refl (N₂.⟪⟫-fix X₂-B′) refl (N₂.⟪⟫-fix X₂-B′))

    ------------------------------------------------------------------
    -- G₁ passes each factor

    -- X on wire 2 and the swap of the wires 0 1 commute.
    N₂-S₀₁ : X ↑ ↑ • Ex ↓ ≈ Ex ↓ • X ↑ ↑
    N₂-S₀₁ = sym (low-comm (Ex {0}) (X {₂₊ k}))

    N₂-K : N₂.⟪ K ⟫ ≈ G₁
    N₂-K = begin
      N₂.⟪ S₀₁.⟪ N₂.⟪ ZX₃ ⟫ ⟫ ⟫
        ≈⟨ swapped ⟩
      S₀₁.⟪ N₂.⟪ N₂.⟪ ZX₃ ⟫ ⟫ ⟫
        ≈⟨ S₀₁.⟪⟫-cong (N₂.⟪⟫-⟪⟫ ZX₃) ⟩
      S₀₁.⟪ ZX₃ ⟫ ∎
      where
      M : Circuit (₁₊ (₄₊ k))
      M = N₂.⟪ ZX₃ ⟫
      swapped : N₂.⟪ S₀₁.⟪ M ⟫ ⟫ ≈ S₀₁.⟪ N₂.⟪ M ⟫ ⟫
      swapped = begin
        X ↑ ↑ • (Ex ↓ • M • Ex ↓) • X ↑ ↑
          ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
        (X ↑ ↑ • Ex ↓) • M • (Ex ↓ • X ↑ ↑)
          ≈⟨ cong N₂-S₀₁ (back _ (sym N₂-S₀₁)) ⟩
        (Ex ↓ • X ↑ ↑) • M • (X ↑ ↑ • Ex ↓)
          ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
        Ex ↓ • (X ↑ ↑ • M • X ↑ ↑) • Ex ↓ ∎

    G₁-W : G₁ • N₂.⟪ CCZX ⟫ ≈ N₂.⟪ CCZX ⟫ • G₁
    G₁-W = N₂.⟪⟫-≈ (eq216 {₁₊ k}) (N₂.⟪⟫-•₂ N₂-K refl) (N₂.⟪⟫-•₂ refl N₂-K)

    G₁-V : G₁ • N₂.⟪ CCXZ ⟫ ≈ N₂.⟪ CCXZ ⟫ • G₁
    G₁-V = N₂.⟪⟫-≈ (eq217 {₁₊ k}) (N₂.⟪⟫-•₂ N₂-K refl) (N₂.⟪⟫-•₂ refl N₂-K)

    -- (290)'s box under the swap of the wires 0 1 is B′, with its box
    -- wire moved along the idle wire 2: one width down, wire 3 idle.
    S₀₁-B : S₀₁.⟪ B□ k ↑ ⟫ ≈ B′
    S₀₁-B = begin
      Ex ↓ • B□ k ↑ • Ex ↓
        ≈⟨ back _ (front _ (sym (place-yB k))) ⟩
      Ex ↓ • place 3 (yB k) • Ex ↓
        ≈⟨ cong (sym (place-low 3 (Ex {1}))) (back _ (sym (place-low 3 (Ex {1})))) ⟩
      place 3 Ex • place 3 (yB k) • place 3 Ex
        ≈⟨ trans (back _ (sym (place-• 3 (yB k) Ex))) (sym (place-• 3 Ex (yB k • Ex))) ⟩
      place 3 (Ex • yB k • Ex)
        ≈⟨ lemma-5-1 3 complete
             (cf-~ (cf-• (cf-loc (Ex {1})) (cf-• (cf-yB k) (cf-loc (Ex {1})))) (cf-B k) Eq.refl Eq.refl) ⟩
      place 3 (B□ k) ∎

    G₁-B′ : G₁ • B′ ≈ B′ • G₁
    G₁-B′ = S₀₁.⟪⟫-≈ (sym (eq290 k complete)) (S₀₁.⟪⟫-•₂ refl S₀₁-B) (S₀₁.⟪⟫-•₂ S₀₁-B refl)

    pass : ∀ {a x y} → a • x ≈ x • a → a • y ≈ y • a → a • (x • y) ≈ (x • y) • a
    pass {a} {x} {y} ex ey = begin
      a • (x • y)   ≈⟨ sym assoc ⟩
      (a • x) • y   ≈⟨ front _ ex ⟩
      (x • a) • y   ≈⟨ assoc ⟩
      x • (a • y)   ≈⟨ back _ ey ⟩
      x • (y • a)   ≈⟨ sym assoc ⟩
      (x • y) • a ∎

  ----------------------------------------------------------------------
  -- (318), all controls black but B's

  eq318₀ : G₁ • G₂ k ≈ G₂ k • G₁
  eq318₀ = begin
    G₁ • G₂ k
      ≈⟨ back _ G₂-form ⟩
    G₁ • (N₂.⟪ CCZX ⟫ • B′ • N₂.⟪ CCXZ ⟫ • B′)
      ≈⟨ pass G₁-W (pass G₁-B′ (pass G₁-V G₁-B′)) ⟩
    (N₂.⟪ CCZX ⟫ • B′ • N₂.⟪ CCXZ ⟫ • B′) • G₁
      ≈⟨ front _ (sym G₂-form) ⟩
    G₂ k • G₁ ∎
