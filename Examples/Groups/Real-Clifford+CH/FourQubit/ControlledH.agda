------------------------------------------------------------------------
-- Presentations of groups
--
-- The doubly controlled H against the box, a white control against a
-- black one (Clément, Lemma D.5, Equation (181))
--
-- The gate is Definition 2.4's doubly controlled H with its H on wire 0,
-- its box wire on wire 3 and its controls on wires 1 and 2, the second
-- negated; the box has its box wire on wire 1 and controls 0, 2, 3.
-- They share wire 2, in opposite colours, and commute.
--
-- Following the paper: the H gate is a rotation R on its box wire 3,
-- controlled by wires 1 and 2, around the CH e from wire 3 —
-- R e R⁻¹ e (`°ΛH₂′-form`; R = d s d s with s the CH from wire 1 onto
-- wire 3 and d the CZ of wires 2 and 3).  The box is V₁ °q W₁ °q with
-- W₁ the doubly controlled ZX one wire up and °q the CZ of the lower
-- pair negated on wire 1 (`box₃′-form`).  R and e pass W₁; °q passes R
-- and, by the rule (17) on the wires 0 ← 3 ← 1, the conjugate e s e.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; X² ; Z² ; CZ² ; CH² ; Ex² ; comm-↓↑)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (eq169)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; CCZX₂₃ ; CCXZ₂₃ ; eq172)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals181 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Ev complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (eq117 ; eq118 ; CZ₂₀² ; module N₂ ; S↑-CH↓ ; S↑-CH₂₀ ; S↑-CZ↓ ; S↑-CZ₂₀)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gate

-- Definition 2.4's doubly controlled H, its H on wire 0 and its box wire
-- on wire 3: ΛH 2 under the cycle that takes wire 0 to wire 3.
ΛH₂′ : ∀ {n} → Circuit (₄₊ n)
ΛH₂′ {n} = S₂₃.⟪ S₁₂.⟪ S₀₁.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫

-- With the control on wire 2 negated.
°ΛH₂′ : ∀ {n} → Circuit (₄₊ n)
°ΛH₂′ = N₂.⟪ ΛH₂′ ⟫

module _ {n : ℕ} where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

  private
    a b p e q °q z W₁ V₁ s₃ d₃ °d₃ h₃ d′ e′ : Circuit (₄₊ n)
    a   = CH ↓
    b   = CZ₂₀
    p   = CH₂₀
    e   = CH₃₀
    q   = CZ ↓
    °q  = °CZ ↓
    z   = Z ↓
    W₁  = CCZX ↑
    V₁  = CCXZ ↑
    s₃  = P₁₃ HC
    d₃  = P₂₃ CZ
    °d₃ = P₂₃ CZ°
    h₃  = P₂₃ HC
    d′  = P₁₃ CZ
    e′  = P₀₃ CH

    Ex₁² : Ex ↑ • Ex ↑ ≈ ε
    Ex₁² = lemma-cong↑ (Ex • Ex) ε Ex²

    Ex₂² : Ex ↑ ↑ • Ex ↑ ↑ ≈ ε
    Ex₂² = lemma-cong↑ (Ex ↑ • Ex ↑) ε (lemma-cong↑ (Ex • Ex) ε Ex²)

    X₂² : X ↑ ↑ • X ↑ ↑ ≈ ε
    X₂² = lemma-cong↑ (X ↑ • X ↑) ε (lemma-cong↑ (X • X) ε X²)

    -- Conjugating a word of the box's shape, letter by letter.
    shape : ∀ {c r t u r′ t′ u′ : Circuit (₄₊ n)} → c • c ≈ ε →
            c • r • c ≈ r′ → c • t • c ≈ t′ → c • u • c ≈ u′ →
            c • ((r • t • r • t) • u • (t • r • t • r) • u) • c
              ≈ (r′ • t′ • r′ • t′) • u′ • (t′ • r′ • t′ • r′) • u′
    shape {c} cc er et eu = C.⟪⟫-•₄ (C.⟪⟫-•₄ er et er et) eu (C.⟪⟫-•₄ et er et er) eu
      where module C = Conj c cc

    ------------------------------------------------------------------
    -- (153) with the controls on wires 1 and 3 exchanged: the box with
    -- the CH from wire 1 outside

    S12-e : S₁₂.⟪ e ⟫ ≈ e
    S12-e = trans (S₁₂.⟪⟫-cong CH₃₀-P)
      (trans (S₁₂.⟪⟫-fix (sym (P₀₃-U CH Ex))) (sym CH₃₀-P))

    S23-p : S₂₃.⟪ p ⟫ ≈ e
    S23-p = trans (O-S₂₃ CH) (sym CH₃₀-P)

    S23-e : S₂₃.⟪ e ⟫ ≈ p
    S23-e = conj-sym Ex₂² S23-p

    boxA : box₃ ≈ (e • b • e • b) • a • (b • e • b • e) • a
    boxA = begin
      box₃
        ≈⟨ sym eq157 ⟩
      S₁₂.⟪ box₃ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (sym eq161) ⟩
      S₁₂.⟪ S₂₃.⟪ box₃ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong (sym eq157)) ⟩
      S₁₂.⟪ S₂₃.⟪ S₁₂.⟪ box₃ ⟫ ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-cong
             (trans (S₁₂.⟪⟫-cong eq153) (shape Ex₁² S↑-CH↓ S↑-CZ₂₀ S12-e))) ⟩
      S₁₂.⟪ S₂₃.⟪ (p • q • p • q) • e • (q • p • q • p) • e ⟫ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (shape Ex₂² S23-p (L-S₂₃ CZ) S23-e) ⟩
      S₁₂.⟪ (e • q • e • q) • p • (q • e • q • e) • p ⟫
        ≈⟨ shape Ex₁² S12-e S↑-CZ↓ S↑-CH₂₀ ⟩
      (e • b • e • b) • a • (b • e • b • e) • a ∎

    ------------------------------------------------------------------
    -- The gate, through the three swaps

    S01-e : S₀₁.⟪ e ⟫ ≈ P₁₃ CH
    S01-e = trans (S₀₁.⟪⟫-cong CH₃₀-P) (S₀₁.⟪⟫-⟪⟫ (P₁₃ CH))

    -- ΛH 2 one swap at a time.
    step₀ : S₀₁.⟪ ΛH 2 ↓ᵏ n ⟫
              ≈ PP ↓ • ((P₁₃ CH • CZ ↑ • P₁₃ CH • CZ ↑) • HC ↓ •
                        (CZ ↑ • P₁₃ CH • CZ ↑ • P₁₃ CH) • HC ↓) • PP ↓
    step₀ = trans (S₀₁.⟪⟫-cong (back _ (front _ boxA)))
      (S₀₁.⟪⟫-•₃ (L-sem (Ex • PP • Ex) PP Eq.refl)
                 (shape Ex² S01-e (S₀₁.⟪⟫-⟪⟫ (CZ ↑)) refl)
                 (L-sem (Ex • PP • Ex) PP Eq.refl))

    step₁ : S₁₂.⟪ S₀₁.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫
              ≈ O PP • ((P₂₃ CH • CZ ↑ • P₂₃ CH • CZ ↑) • O HC •
                        (CZ ↑ • P₂₃ CH • CZ ↑ • P₂₃ CH) • O HC) • O PP
    step₁ = trans (S₁₂.⟪⟫-cong step₀)
      (S₁₂.⟪⟫-•₃ (O-L PP)
                 (shape Ex₁² (S₁₂.⟪⟫-⟪⟫ (P₂₃ CH)) (U-sem (Ex • CZ • Ex) CZ Eq.refl) (O-L HC))
                 (O-L PP))

    step₂ : ΛH₂′ ≈ P₀₃ PP • ((h₃ • d′ • h₃ • d′) • P₀₃ HC • (d′ • h₃ • d′ • h₃) • P₀₃ HC) • P₀₃ PP
    step₂ = trans (S₂₃.⟪⟫-cong step₁)
      (S₂₃.⟪⟫-•₃ (O-S₂₃ PP)
                 (shape Ex₂² refl (U-S₂₃ CZ) (O-S₂₃ HC))
                 (O-S₂₃ PP))

    ------------------------------------------------------------------
    -- P ⊗ P on the pair 0 3

    PP₀₃² : P₀₃ PP • P₀₃ PP ≈ ε
    PP₀₃² = conj-invol Ex² (conj-invol Ex₁²
      (lemma-cong↑ (PP ↑ • PP ↑) ε (lemma-cong↑ (PP • PP) ε (by-sem (PP • PP) ε Eq.refl))))

    -- It turns the CH from wire 2 onto wire 3 into their CZ: on the
    -- triple 0 2 3.
    C-h : P₀₃ PP • h₃ • P₀₃ PP ≈ d₃
    C-h = begin
      P₀₃ PP • h₃ • P₀₃ PP
        ≈⟨ back _ (front _ (sym (P₂₃-S₀₁ HC))) ⟩
      O₃ (O₀ PP) • O₃ (U₀ HC) • O₃ (O₀ PP)
        ≈⟨ sym (S₀₁.⟪⟫-•₃ refl refl refl) ⟩
      O₃ (O₀ PP • U₀ HC • O₀ PP)
        ≈⟨ O₃-ev ev-PP-HC ⟩
      O₃ (U₀ CZ)
        ≈⟨ P₂₃-S₀₁ CZ ⟩
      d₃ ∎

    -- And the CZ of wires 1 and 3 into the CH from wire 1 onto wire 3:
    -- the same evaluation on the triple 0 1 3, read backwards.
    C-s : P₀₃ PP • s₃ • P₀₃ PP ≈ d′
    C-s = begin
      P₀₃ PP • s₃ • P₀₃ PP
        ≈⟨ sym (cong (M₃-O PP) (cong (M₃-U HC) (M₃-O PP))) ⟩
      M₃ (O₀ PP) • M₃ (U₀ HC) • M₃ (O₀ PP)
        ≈⟨ sym (S₂₃.⟪⟫-•₃ refl refl refl) ⟩
      M₃ (O₀ PP • U₀ HC • O₀ PP)
        ≈⟨ M₃-ev ev-PP-HC ⟩
      M₃ (U₀ CZ)
        ≈⟨ M₃-U CZ ⟩
      d′ ∎

    C-d : P₀₃ PP • d′ • P₀₃ PP ≈ s₃
    C-d = conj-sym PP₀₃² C-s

    C-a : P₀₃ PP • P₀₃ HC • P₀₃ PP ≈ e′
    C-a = trans (sym (trans (P₀₃-• PP (HC • PP)) (back _ (P₀₃-• HC PP))))
                (P₀₃-sem (PP • HC • PP) CH Eq.refl)

    -- The gate with black controls: a rotation on wire 3 around e.
    ΛH₂′-form : ΛH₂′ ≈ (d₃ • s₃ • d₃ • s₃) • e′ • (s₃ • d₃ • s₃ • d₃) • e′
    ΛH₂′-form = trans step₂ (shape PP₀₃² C-h C-d C-a)

    -- And with the control on wire 2 negated.
    N-s : N₂.⟪ s₃ ⟫ ≈ s₃
    N-s = N₂.⟪⟫-fix (comm-12-13 (X ↑) HC (evaluated Eq.refl))

    N-e : N₂.⟪ e′ ⟫ ≈ e′
    N-e = N₂.⟪⟫-fix (sym (P₀₃-U CH (X ↑)))

    °M : Circuit (₄₊ n)
    °M = (°d₃ • s₃ • °d₃ • s₃) • e′ • (s₃ • °d₃ • s₃ • °d₃) • e′

    °ΛH₂′-form : °ΛH₂′ ≈ °M
    °ΛH₂′-form = trans (N₂.⟪⟫-cong ΛH₂′-form) (shape X₂² refl N-s N-e)

    ------------------------------------------------------------------
    -- The gate again, with the two controls of its rotation in the
    -- other roles: the CZ from wire 1 and the CH from wire 2

    -- (14) on the triple 0 2 3.
    sym14 : p • CZ₃₀ • p • CZ₃₀ ≈ e • b • e • b
    sym14 = begin
      p • CZ₃₀ • p • CZ₃₀
        ≈⟨ back _ (cong CZ₃₀-P (back _ CZ₃₀-P)) ⟩
      p • P₀₃ CZ • p • P₀₃ CZ
        ≈⟨ sym (S₀₁.⟪⟫-•₄ refl refl refl refl) ⟩
      S₀₁.⟪ (CH ↓ • CZ₂₀ • CH ↓ • CZ₂₀) ↑ ⟫
        ≈⟨ S₀₁.⟪⟫-cong (lemma-cong↑ (CH ↓ • CZ₂₀ • CH ↓ • CZ₂₀) (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓)
                                      (ax symm-controls)) ⟩
      S₀₁.⟪ (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓) ↑ ⟫
        ≈⟨ S₀₁.⟪⟫-•₄ refl refl refl refl ⟩
      P₀₃ CH • b • P₀₃ CH • b
        ≈⟨ cong (sym CH₃₀-P) (back _ (front _ (sym CH₃₀-P))) ⟩
      e • b • e • b ∎

    p² : p • p ≈ ε
    p² = O-invol CH CH²

    sym14⁻ : CZ₃₀ • p • CZ₃₀ • p ≈ b • e • b • e
    sym14⁻ = inv-unique (invol-abab p² CZ₃₀²) (invol-abab CZ₂₀² CH₃₀²) sym14

    boxA′ : box₃ ≈ (p • CZ₃₀ • p • CZ₃₀) • a • (CZ₃₀ • p • CZ₃₀ • p) • a
    boxA′ = trans boxA (sym (cong sym14 (back _ (front _ sym14⁻))))

    S01-c : S₀₁.⟪ CZ₃₀ ⟫ ≈ d′
    S01-c = trans (S₀₁.⟪⟫-cong CZ₃₀-P) (S₀₁.⟪⟫-⟪⟫ d′)

    step₀′ : S₀₁.⟪ ΛH 2 ↓ᵏ n ⟫
               ≈ PP ↓ • ((CH ↑ • d′ • CH ↑ • d′) • HC ↓ • (d′ • CH ↑ • d′ • CH ↑) • HC ↓) • PP ↓
    step₀′ = trans (S₀₁.⟪⟫-cong (back _ (front _ boxA′)))
      (S₀₁.⟪⟫-•₃ (L-sem (Ex • PP • Ex) PP Eq.refl)
                 (shape Ex² (S₀₁.⟪⟫-⟪⟫ (CH ↑)) S01-c refl)
                 (L-sem (Ex • PP • Ex) PP Eq.refl))

    step₁′ : S₁₂.⟪ S₀₁.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫
               ≈ O PP • ((U HC • d₃ • U HC • d₃) • O HC • (d₃ • U HC • d₃ • U HC) • O HC) • O PP
    step₁′ = trans (S₁₂.⟪⟫-cong step₀′)
      (S₁₂.⟪⟫-•₃ (O-L PP)
                 (shape Ex₁² refl (S₁₂.⟪⟫-⟪⟫ d₃) (O-L HC))
                 (O-L PP))

    step₂′ : ΛH₂′ ≈ P₀₃ PP • ((s₃ • d₃ • s₃ • d₃) • P₀₃ HC • (d₃ • s₃ • d₃ • s₃) • P₀₃ HC) • P₀₃ PP
    step₂′ = trans (S₂₃.⟪⟫-cong step₁′)
      (S₂₃.⟪⟫-•₃ (O-S₂₃ PP)
                 (shape Ex₂² (U-S₂₃ HC)
                        (lemma-cong↑ ((Ex • CZ • Ex) ↑) (CZ ↑)
                          (lemma-cong↑ (Ex • CZ • Ex) CZ (by-sem (Ex • CZ • Ex) CZ Eq.refl)))
                        (O-S₂₃ HC))
                 (O-S₂₃ PP))

    ΛH₂′-form′ : ΛH₂′ ≈ (d′ • h₃ • d′ • h₃) • e′ • (h₃ • d′ • h₃ • d′) • e′
    ΛH₂′-form′ = trans step₂′ (shape PP₀₃² C-s (conj-sym PP₀₃² C-h) C-a)

    ------------------------------------------------------------------
    -- The box on wire 1, with a white CZ

    V₂₃W₂₃ : CCXZ₂₃ • CCZX₂₃ ≈ ε
    V₂₃W₂₃ = trans (sym (S₀₁.⟪⟫-• (CCXZ ↑) (CCZX ↑)))
      (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCXZ • CCZX) ε eq118)) S₀₁.⟪⟫-ε)

    box-q : box₃ ≈ CCXZ₂₃ • q • CCZX₂₃ • q
    box-q = sym (begin
      CCXZ₂₃ • q • CCZX₂₃ • q
        ≈⟨ by-passoc (□ • □ • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
      CCXZ₂₃ • (q • CCZX₂₃) • q
        ≈⟨ back _ (front _ eq172) ⟩
      CCXZ₂₃ • (CCZX₂₃ • box₃ • q) • q
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (CCXZ₂₃ • CCZX₂₃) • box₃ • (q • q)
        ≈⟨ trans (front _ V₂₃W₂₃) left-unit ⟩
      box₃ • (q • q)
        ≈⟨ cancelᵉ _ CZ² ⟩
      box₃ ∎)

    q-form : q ≈ °q • z
    q-form = L-sem CZ (°CZ • Z ↓) Eq.refl

    z-°q : z • °q ≈ °q • z
    z-°q = L-sem (Z ↓ • °CZ) (°CZ • Z ↓) Eq.refl

    z-W₁ : z • W₁ ≈ W₁ • z
    z-W₁ = comm-↓↑ Z CCZX

    box₃′-form : box₃′ ≈ V₁ • °q • W₁ • °q
    box₃′-form = begin
      box₃′
        ≈⟨ S₀₁.⟪⟫-cong box-q ⟩
      S₀₁.⟪ CCXZ₂₃ • q • CCZX₂₃ • q ⟫
        ≈⟨ S₀₁.⟪⟫-•₄ (S₀₁.⟪⟫-⟪⟫ V₁) S-q (S₀₁.⟪⟫-⟪⟫ W₁) S-q ⟩
      V₁ • q • W₁ • q
        ≈⟨ back _ (cong q-form (back _ q-form)) ⟩
      V₁ • (°q • z) • W₁ • (°q • z)
        ≈⟨ by-passoc (□ • (□ • □) • □ • (□ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      V₁ • °q • (z • W₁) • °q • z
        ≈⟨ back _ (back _ (front _ z-W₁)) ⟩
      V₁ • °q • (W₁ • z) • °q • z
        ≈⟨ by-passoc (□ • □ • (□ • □) • □ • □) (□ • □ • □ • (□ • □) • □) Eq.refl ⟩
      V₁ • °q • W₁ • (z • °q) • z
        ≈⟨ back _ (back _ (back _ (front _ z-°q))) ⟩
      V₁ • °q • W₁ • (°q • z) • z
        ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
      V₁ • °q • W₁ • °q • (z • z)
        ≈⟨ back _ (back _ (back _ (cancelᵉ _ Z²))) ⟩
      V₁ • °q • W₁ • °q ∎
      where
      S-q : S₀₁.⟪ q ⟫ ≈ q
      S-q = L-sem (Ex • CZ • Ex) CZ Eq.refl

    ------------------------------------------------------------------
    -- What passes what

    °R °R⁻ : Circuit (₄₊ n)
    °R  = °d₃ • s₃ • °d₃ • s₃
    °R⁻ = s₃ • °d₃ • s₃ • °d₃

    °d₃² : °d₃ • °d₃ ≈ ε
    °d₃² = lemma-cong↑ (CZ° ↑ • CZ° ↑) ε (lemma-cong↑ (CZ° • CZ°) ε (by-sem (CZ° • CZ°) ε Eq.refl))

    s₃² : s₃ • s₃ ≈ ε
    s₃² = lemma-cong↑ (O HC • O HC) ε (O-invol HC (by-sem₀ (HC • HC) ε Eq.refl))

    e′² : e′ • e′ ≈ ε
    e′² = trans (cong (sym CH₃₀-P) (sym CH₃₀-P)) CH₃₀²

    W₁V₁ : W₁ • V₁ ≈ ε
    W₁V₁ = lemma-cong↑ (CCZX • CCXZ) ε eq117

    V₁W₁ : V₁ • W₁ ≈ ε
    V₁W₁ = lemma-cong↑ (CCXZ • CCZX) ε eq118

    -- W₁ passes the rotation, its inverse and e: so it passes the gate.
    W-°R : W₁ • °R ≈ °R • W₁
    W-°R = sym (U₃-comm-ev ev-°R-CCZX)

    W-°R⁻ : W₁ • °R⁻ ≈ °R⁻ • W₁
    W-°R⁻ = comm-inv (invol-abab °d₃² s₃²) (invol-abab s₃² °d₃²) W-°R

    W-e : W₁ • e′ ≈ e′ • W₁
    W-e = begin
      W₁ • e′     ≈⟨ back _ (sym CH₃₀-P) ⟩
      W₁ • e      ≈⟨ sym eq169 ⟩
      e • W₁      ≈⟨ front _ CH₃₀-P ⟩
      e′ • W₁ ∎

    M-W : °M • W₁ ≈ W₁ • °M
    M-W = sym (comm-• W-°R (comm-• W-e (comm-• W-°R⁻ W-e)))

    M-V : °M • V₁ ≈ V₁ • °M
    M-V = comm-inv W₁V₁ V₁W₁ M-W

    -- °q passes the rotation, and e °R⁻ e: the rule (17).
    °q-°d₃ : °q • °d₃ ≈ °d₃ • °q
    °q-°d₃ = sym (P₂₃-L CZ° °CZ)

    °q-s₃ : °q • s₃ ≈ s₃ • °q
    °q-s₃ = comm-01-13 °CZ HC (evaluated Eq.refl)

  private module E = Conj {₄₊ n} e′ e′²

  private
    ŝ : Circuit (₄₊ n)
    ŝ = E.⟪ s₃ ⟫

    E-°d₃ : E.⟪ °d₃ ⟫ ≈ °d₃
    E-°d₃ = E.⟪⟫-fix (sym (comm-23-03 CZ° CH (evaluated Eq.refl)))

    tail-form : e′ • °R⁻ • e′ ≈ ŝ • °d₃ • ŝ • °d₃
    tail-form = E.⟪⟫-•₄ refl E-°d₃ refl E-°d₃

    °q-ŝ : °q • ŝ ≈ ŝ • °q
    °q-ŝ = begin
      °q • (e′ • s₃ • e′)
        ≈⟨ sym (cong (M₃-L °CZ) (S₂₃.⟪⟫-•₃ (M₃-O CH) (M₃-U HC) (M₃-O CH))) ⟩
      M₃ (L₀ °CZ) • M₃ (O₀ CH • U₀ HC • O₀ CH)
        ≈⟨ M₃-comm-ev ev-17 ⟩
      M₃ (O₀ CH • U₀ HC • O₀ CH) • M₃ (L₀ °CZ)
        ≈⟨ cong (S₂₃.⟪⟫-•₃ (M₃-O CH) (M₃-U HC) (M₃-O CH)) (M₃-L °CZ) ⟩
      (e′ • s₃ • e′) • °q ∎

    °q-tail : °q • (e′ • °R⁻ • e′) ≈ (e′ • °R⁻ • e′) • °q
    °q-tail = begin
      °q • (e′ • °R⁻ • e′)          ≈⟨ back _ tail-form ⟩
      °q • (ŝ • °d₃ • ŝ • °d₃)      ≈⟨ comm-abab °q-ŝ °q-°d₃ ⟩
      (ŝ • °d₃ • ŝ • °d₃) • °q      ≈⟨ front _ (sym tail-form) ⟩
      (e′ • °R⁻ • e′) • °q ∎

    M-°q : °M • °q ≈ °q • °M
    M-°q = sym (comm-• (comm-abab °q-°d₃ °q-s₃) °q-tail)

  -- The gate as a rotation on its box wire around the CH from that
  -- wire, in both spellings of the rotation.
  ΛH₂′-rot : (₄₊ n) ⊢ ΛH₂′ ≈ (P₂₃ CZ • P₁₃ HC • P₂₃ CZ • P₁₃ HC) • P₀₃ CH •
                            (P₁₃ HC • P₂₃ CZ • P₁₃ HC • P₂₃ CZ) • P₀₃ CH
  ΛH₂′-rot = ΛH₂′-form

  ΛH₂′-rot′ : (₄₊ n) ⊢ ΛH₂′ ≈ (P₁₃ CZ • P₂₃ HC • P₁₃ CZ • P₂₃ HC) • P₀₃ CH •
                             (P₂₃ HC • P₁₃ CZ • P₂₃ HC • P₁₃ CZ) • P₀₃ CH
  ΛH₂′-rot′ = ΛH₂′-form′

  -- (181)
  eq181 : (₄₊ n) ⊢ box₃′ • °ΛH₂′ ≈ °ΛH₂′ • box₃′
  eq181 = begin
    box₃′ • °ΛH₂′
      ≈⟨ cong box₃′-form °ΛH₂′-form ⟩
    (V₁ • °q • W₁ • °q) • °M
      ≈⟨ sym (comm-• M-V (comm-• M-°q (comm-• M-W M-°q))) ⟩
    °M • (V₁ • °q • W₁ • °q)
      ≈⟨ sym (cong °ΛH₂′-form box₃′-form) ⟩
    °ΛH₂′ • box₃′ ∎
