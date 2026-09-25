------------------------------------------------------------------------
-- Presentations of groups
--
-- The keystone of Lemma D.8: the box in its E-form, and H on its box
-- wire (Clément, Equations (283)–(285))
--
-- At width 4 + k let B = B□ k be the smaller box on wire 1, with a
-- control on wire 0, and E = E□ k the multi-controlled H it makes
-- between P ⊗ P on the wires 0 1.  (283) says that E • B passes the
-- doubly controlled ZX W = CCZX; with E and B involutions that is (284),
-- the box in its E-form, and with the mirror (286) its mirror; and the
-- two halves of (284) give (285) (GeneralN.EForm).
--
-- The proof of (283) uses the paper's ingredients but not its order.
-- On three wires, W is P₁ • CX • P₂ • CX • P₃ (one evaluation): P₁ and
-- P₂ are the CH and CZ from wire 1 onto wire 0 in the two orders, CX
-- the CNOT from wire 2 onto wire 1, and P₃ is P₁ with its control moved
-- to wire 2 by the swap of the wires 1 2.  E • B passes
--
--   * P₁ and P₂, and H on wire 1: steps one width down with wire 2 idle
--     (Lemma 5.1), where E • B is H on wire 0 times the box on wire 1,
--     both controlled by the wires 3 …, and those are the same rotation;
--   * CZ on the wires 1 2, hence the CX: for B, under the transposition
--     of the wires 0 2 it is the CZ from wire 0 onto the box wire, (272);
--     for E, P ⊗ P turns it into the CH from wire 2 (the axiom (18)),
--     which under the transposition is (280);
--   * the swap of the wires 1 2, hence P₃: under the transposition it is
--     the swap of the box wire and the idle wire below, (274), and for E
--     the Klein four-group of the P ⊗ P on the wires 0 1 2 reduces it to
--     P ⊗ P on the box wire and that wire, (276).
--
-- (272), (274), (276) and (280) at width 4 + k are GeneralN.ZXPass's;
-- every step one width down uses completeness at 3 + k.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.Keystone
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (eq286)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxWire complete₂ complete₃ using (Eq285)
open import Examples.Groups.Real-Clifford+CH.GeneralN.EForm complete₂ complete₃
  using (Eq284 ; Eq284′ ; eq285)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□ ; E□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX using (B₁₀ ; HG₀₁)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemKey
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place
  using (place ; place-• ; place-low ; lemma-5-1 ; cyc ; cyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃
  using (Complete ; box272 ; box274 ; box276 ; eq280)

-- (283): E • B passes the doubly controlled ZX.
Eq283 : ℕ → Set
Eq283 k = (₄₊ k) ⊢ (E□ k • B□ k) • CCZX ≈ CCZX • (E□ k • B□ k)

module _ (k : ℕ) (complete : Complete k) where

  private
    open Tools ((₄₊ k) VRel,_===_)

    B E EB Λ↑ PP₀₂ P₁ P₂ P₃ : Circuit (₄₊ k)
    B    = B□ k
    E    = E□ k
    EB   = E • B
    Λ↑   = Λ□ (₂₊ k) ↑
    PP₀₂ = Ex ↑ • PP ↓ • Ex ↑
    P₁   = CH • CZ
    P₂   = CZ • CH
    P₃   = CH₂₀ • CZ₂₀

    ------------------------------------------------------------------
    -- Facts on three wires

    τ² : (₄₊ k) ⊢ τ₀₂ • τ₀₂ ≈ ε
    τ² = L₃-sem (τ₀₂ • τ₀₂) ε Eq.refl

    PP² : (₄₊ k) ⊢ PP ↓ • PP ↓ ≈ ε
    PP² = L₃-sem (PP • PP) ε Eq.refl

    Ex↑² : (₄₊ k) ⊢ Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ (Ex • Ex) ε Ex²

    τ-CZ↑ : (₄₊ k) ⊢ τ₀₂ • CZ ↑ ≈ CZ ↓ • τ₀₂
    τ-CZ↑ = L₃-sem (τ₀₂ • CZ ↑) (CZ • τ₀₂) Eq.refl

    τ-CZ↓ : (₄₊ k) ⊢ τ₀₂ • CZ ↓ ≈ CZ ↑ • τ₀₂
    τ-CZ↓ = L₃-sem (τ₀₂ • CZ) (CZ ↑ • τ₀₂) Eq.refl

    τ-CH↑ : (₄₊ k) ⊢ τ₀₂ • CH ↑ ≈ HC • τ₀₂
    τ-CH↑ = L₃-sem (τ₀₂ • CH ↑) (HC • τ₀₂) Eq.refl

    τ-HC : (₄₊ k) ⊢ τ₀₂ • HC ≈ CH ↑ • τ₀₂
    τ-HC = L₃-sem (τ₀₂ • HC) (CH ↑ • τ₀₂) Eq.refl

    Ex-τ : (₄₊ k) ⊢ Ex ↑ • τ₀₂ ≈ τ₀₂ • Ex ↓
    Ex-τ = L₃-sem (Ex ↑ • τ₀₂) (τ₀₂ • Ex) Eq.refl

    τ-Ex : (₄₊ k) ⊢ τ₀₂ • Ex ↑ ≈ Ex ↓ • τ₀₂
    τ-Ex = L₃-sem (τ₀₂ • Ex ↑) (Ex • τ₀₂) Eq.refl

    PP-τ : (₄₊ k) ⊢ PP ↑ • τ₀₂ ≈ τ₀₂ • PP ↓
    PP-τ = L₃-sem (PP ↑ • τ₀₂) (τ₀₂ • PP) Eq.refl

    τ-PP : (₄₊ k) ⊢ τ₀₂ • PP ↑ ≈ PP ↓ • τ₀₂
    τ-PP = L₃-sem (τ₀₂ • PP ↑) (PP • τ₀₂) Eq.refl

    PP-CZ : (₄₊ k) ⊢ PP ↓ • CZ ↑ ≈ CH ↑ • PP ↓
    PP-CZ = L₃-sem (PP • CZ ↑) (CH ↑ • PP) Eq.refl

    PP-CH : (₄₊ k) ⊢ PP ↓ • CH ↑ ≈ CZ ↑ • PP ↓
    PP-CH = L₃-sem (PP • CH ↑) (CZ ↑ • PP) Eq.refl

    klein-a : (₄₊ k) ⊢ PP₀₂ ≈ PP ↓ • PP ↑
    klein-a = L₃-sem (Ex ↑ • PP • Ex ↑) (PP • PP ↑) Eq.refl

    klein-b : (₄₊ k) ⊢ PP₀₂ ≈ PP ↑ • PP ↓
    klein-b = L₃-sem (Ex ↑ • PP • Ex ↑) (PP ↑ • PP) Eq.refl

    W-V : (₄₊ k) ⊢ CCZX • CCXZ ≈ ε
    W-V = L₃-sem (CCZX • CCXZ) ε Eq.refl

    V-W : (₄₊ k) ⊢ CCXZ • CCZX ≈ ε
    V-W = L₃-sem (CCXZ • CCZX) ε Eq.refl

    W-dec : (₄₊ k) ⊢ CCZX ≈ P₁ • CX ↑ • P₂ • CX ↑ • P₃
    W-dec = L₃-sem CCZX ((CH • CZ) • CX ↑ • (CZ • CH) • CX ↑ • (CH₂₀ • CZ₂₀)) Eq.refl

    P₃-P₁ : (₄₊ k) ⊢ P₃ ≈ Ex ↑ • P₁ • Ex ↑
    P₃-P₁ = L₃-sem (CH₂₀ • CZ₂₀) (Ex ↑ • (CH • CZ) • Ex ↑) Eq.refl

    net₁ : (₄₊ k) ⊢ cyc⁻¹ 2 • Ex ↑ ≈ τ₀₂
    net₁ = L₃-sem (cyc⁻¹ 2 • Ex ↑) τ₀₂ Eq.refl

    net₂ : (₄₊ k) ⊢ Ex ↑ • cyc 2 ≈ τ₀₂
    net₂ = L₃-sem (Ex ↑ • cyc 2) τ₀₂ Eq.refl

    ------------------------------------------------------------------
    -- Word algebra

    -- A word passing x and y passes x • y.
    pass : ∀ {a x y : Circuit (₄₊ k)} → (₄₊ k) ⊢ a • x ≈ x • a → (₄₊ k) ⊢ a • y ≈ y • a →
           (₄₊ k) ⊢ a • (x • y) ≈ (x • y) • a
    pass {a} {x} {y} hx hy = begin
      a • (x • y)     ≈⟨ sym assoc ⟩
      (a • x) • y     ≈⟨ front _ hx ⟩
      (x • a) • y     ≈⟨ assoc ⟩
      x • (a • y)     ≈⟨ back _ hy ⟩
      x • (y • a)     ≈⟨ sym assoc ⟩
      (x • y) • a ∎

    -- A product passing y passes it.
    pass′ : ∀ {a b y : Circuit (₄₊ k)} → (₄₊ k) ⊢ a • y ≈ y • a → (₄₊ k) ⊢ b • y ≈ y • b →
            (₄₊ k) ⊢ (a • b) • y ≈ y • (a • b)
    pass′ {a} {b} {y} ha hb = begin
      (a • b) • y     ≈⟨ assoc ⟩
      a • (b • y)     ≈⟨ back _ hb ⟩
      a • (y • b)     ≈⟨ sym assoc ⟩
      (a • y) • b     ≈⟨ front _ ha ⟩
      (y • a) • b     ≈⟨ assoc ⟩
      y • (a • b) ∎

    -- Passing w and a conjugation: passing c • w • c for an involution c.
    pass-conj : ∀ {a c w : Circuit (₄₊ k)} → (₄₊ k) ⊢ c • c ≈ ε → (₄₊ k) ⊢ a • c ≈ c • a →
                (₄₊ k) ⊢ a • w ≈ w • a → (₄₊ k) ⊢ a • (c • w • c) ≈ (c • w • c) • a
    pass-conj {a} {c} {w} _ hc hw = begin
      a • (c • w • c)       ≈⟨ pass hc (pass hw hc) ⟩
      (c • w • c) • a ∎

    -- Passing w, and w inverse to v: passing v.
    pass-inv : ∀ {a w v : Circuit (₄₊ k)} → (₄₊ k) ⊢ a • w ≈ w • a →
               (₄₊ k) ⊢ w • v ≈ ε → (₄₊ k) ⊢ v • w ≈ ε → (₄₊ k) ⊢ a • v ≈ v • a
    pass-inv {a} {w} {v} h wv vw = begin
      a • v                   ≈⟨ sym left-unit ⟩
      ε • a • v               ≈⟨ front _ (sym vw) ⟩
      (v • w) • a • v         ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
      v • (w • a) • v         ≈⟨ back _ (front _ (sym h)) ⟩
      v • (a • w) • v         ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
      v • a • (w • v)         ≈⟨ back _ (back _ wv) ⟩
      v • a • ε               ≈⟨ back _ right-unit ⟩
      v • a ∎

    -- A word fixed by conjugation with an involution passes it.
    conj-pass : ∀ {c w : Circuit (₄₊ k)} → (₄₊ k) ⊢ c • c ≈ ε → (₄₊ k) ⊢ c • w • c ≈ w →
                (₄₊ k) ⊢ w • c ≈ c • w
    conj-pass e h = conj-comm e h

    ------------------------------------------------------------------
    -- The box through the transposition of the wires 0 2

    -- τ • x ≈ y • τ, y passes Λ↑, and τ • y ≈ x • τ: x passes B.
    through : ∀ {x y : Circuit (₄₊ k)} → (₄₊ k) ⊢ τ₀₂ • x ≈ y • τ₀₂ → (₄₊ k) ⊢ τ₀₂ • y ≈ x • τ₀₂ →
              (₄₊ k) ⊢ y • Λ↑ ≈ Λ↑ • y → (₄₊ k) ⊢ B • x ≈ x • B
    through {x} {y} tx ty h = begin
      (τ₀₂ • Λ↑ • τ₀₂) • x          ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
      τ₀₂ • Λ↑ • (τ₀₂ • x)          ≈⟨ back _ (back _ tx) ⟩
      τ₀₂ • Λ↑ • (y • τ₀₂)          ≈⟨ back _ (by-passoc (□ • (□ • □)) ((□ • □) • □) Eq.refl) ⟩
      τ₀₂ • (Λ↑ • y) • τ₀₂          ≈⟨ back _ (front _ (sym h)) ⟩
      τ₀₂ • (y • Λ↑) • τ₀₂          ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
      (τ₀₂ • y) • Λ↑ • τ₀₂          ≈⟨ front _ ty ⟩
      (x • τ₀₂) • Λ↑ • τ₀₂          ≈⟨ assoc ⟩
      x • τ₀₂ • Λ↑ • τ₀₂ ∎

    -- The same for a conjugation: τ • x ≈ y • τ, y fixes Λ↑, and x an
    -- involution with τ • τ = ε: x fixes B.
    through-conj : ∀ {x y : Circuit (₄₊ k)} → (₄₊ k) ⊢ x • τ₀₂ ≈ τ₀₂ • y → (₄₊ k) ⊢ τ₀₂ • x ≈ y • τ₀₂ →
                   (₄₊ k) ⊢ y • Λ↑ • y ≈ Λ↑ → (₄₊ k) ⊢ x • B • x ≈ B
    through-conj {x} {y} xt tx h = begin
      x • (τ₀₂ • Λ↑ • τ₀₂) • x       ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (x • τ₀₂) • Λ↑ • (τ₀₂ • x)     ≈⟨ cong xt (back _ tx) ⟩
      (τ₀₂ • y) • Λ↑ • (y • τ₀₂)     ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      τ₀₂ • (y • Λ↑ • y) • τ₀₂       ≈⟨ back _ (front _ h) ⟩
      τ₀₂ • Λ↑ • τ₀₂ ∎

    B-CZ : (₄₊ k) ⊢ B • CZ ↑ ≈ CZ ↑ • B
    B-CZ = through τ-CZ↑ τ-CZ↓ (box272 k)

    B-CH : (₄₊ k) ⊢ B • CH ↑ ≈ CH ↑ • B
    B-CH = through τ-CH↑ τ-HC (eq280 k complete)

    B-Ex : (₄₊ k) ⊢ Ex ↑ • B • Ex ↑ ≈ B
    B-Ex = through-conj Ex-τ τ-Ex (box274 k complete)

    B-PP : (₄₊ k) ⊢ PP ↑ • B • PP ↑ ≈ B
    B-PP = through-conj PP-τ τ-PP (box276 k complete)

    B² : (₄₊ k) ⊢ B • B ≈ ε
    B² = begin
      (τ₀₂ • Λ↑ • τ₀₂) • (τ₀₂ • Λ↑ • τ₀₂)   ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      τ₀₂ • Λ↑ • (τ₀₂ • τ₀₂) • Λ↑ • τ₀₂     ≈⟨ back _ (back _ (front _ τ²)) ⟩
      τ₀₂ • Λ↑ • ε • Λ↑ • τ₀₂               ≈⟨ back _ (back _ left-unit) ⟩
      τ₀₂ • Λ↑ • Λ↑ • τ₀₂                   ≈⟨ back _ (sym assoc) ⟩
      τ₀₂ • (Λ↑ • Λ↑) • τ₀₂                 ≈⟨ back _ (front _ (lemma-cong↑ _ ε (complete (sem-box² k)))) ⟩
      τ₀₂ • ε • τ₀₂                         ≈⟨ back _ left-unit ⟩
      τ₀₂ • τ₀₂                             ≈⟨ τ² ⟩
      ε ∎

    ------------------------------------------------------------------
    -- The multi-controlled H

    E² : (₄₊ k) ⊢ E • E ≈ ε
    E² = begin
      (PP ↓ • B • PP ↓) • (PP ↓ • B • PP ↓)   ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □)) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
      PP ↓ • B • (PP ↓ • PP ↓) • B • PP ↓     ≈⟨ back _ (back _ (front _ PP²)) ⟩
      PP ↓ • B • ε • B • PP ↓                 ≈⟨ back _ (back _ left-unit) ⟩
      PP ↓ • B • B • PP ↓                     ≈⟨ back _ (sym assoc) ⟩
      PP ↓ • (B • B) • PP ↓                   ≈⟨ back _ (front _ B²) ⟩
      PP ↓ • ε • PP ↓                         ≈⟨ back _ left-unit ⟩
      PP ↓ • PP ↓                             ≈⟨ PP² ⟩
      ε ∎

    E-CZ : (₄₊ k) ⊢ E • CZ ↑ ≈ CZ ↑ • E
    E-CZ = begin
      (PP ↓ • B • PP ↓) • CZ ↑       ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
      PP ↓ • B • (PP ↓ • CZ ↑)       ≈⟨ back _ (back _ PP-CZ) ⟩
      PP ↓ • B • (CH ↑ • PP ↓)       ≈⟨ back _ (by-passoc (□ • (□ • □)) ((□ • □) • □) Eq.refl) ⟩
      PP ↓ • (B • CH ↑) • PP ↓       ≈⟨ back _ (front _ B-CH) ⟩
      PP ↓ • (CH ↑ • B) • PP ↓       ≈⟨ by-passoc (□ • (□ • □) • □) ((□ • □) • □ • □) Eq.refl ⟩
      (PP ↓ • CH ↑) • B • PP ↓       ≈⟨ front _ PP-CH ⟩
      (CZ ↑ • PP ↓) • B • PP ↓       ≈⟨ assoc ⟩
      CZ ↑ • PP ↓ • B • PP ↓ ∎

    E-Ex : (₄₊ k) ⊢ Ex ↑ • E • Ex ↑ ≈ E
    E-Ex = begin
      Ex ↑ • (PP ↓ • B • PP ↓) • Ex ↑      ≈⟨ X.⟪⟫-•₃ refl B-Ex refl ⟩
      PP₀₂ • B • PP₀₂                     ≈⟨ cong klein-a (back _ klein-b) ⟩
      (PP ↓ • PP ↑) • B • (PP ↑ • PP ↓)   ≈⟨ by-passoc ((□ • □) • □ • (□ • □)) (□ • (□ • □ • □) • □) Eq.refl ⟩
      PP ↓ • (PP ↑ • B • PP ↑) • PP ↓     ≈⟨ back _ (front _ B-PP) ⟩
      PP ↓ • B • PP ↓ ∎
      where module X = Conj (Ex ↑) Ex↑²

    ------------------------------------------------------------------
    -- Steps one width down with wire 2 idle

    place-B : (₄₊ k) ⊢ place 2 (B₁₀ k) ≈ B
    place-B = begin
      cyc⁻¹ 2 • (Ex ↑ • Λ↑ • Ex ↑) • cyc 2
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (cyc⁻¹ 2 • Ex ↑) • Λ↑ • (Ex ↑ • cyc 2)
        ≈⟨ cong net₁ (back _ net₂) ⟩
      τ₀₂ • Λ↑ • τ₀₂ ∎

    place-E : (₄₊ k) ⊢ place 2 (HG₀₁ k) ≈ E
    place-E = begin
      place 2 (PP ↓ • B₁₀ k • PP ↓)
        ≈⟨ place-• 2 (PP ↓) (B₁₀ k • PP ↓) ⟩
      place 2 (PP ↓) • place 2 (B₁₀ k • PP ↓)
        ≈⟨ back _ (place-• 2 (B₁₀ k) (PP ↓)) ⟩
      place 2 (PP ↓) • place 2 (B₁₀ k) • place 2 (PP ↓)
        ≈⟨ cong (place-low 2 PP) (cong place-B (place-low 2 PP)) ⟩
      PP ↓ • B • PP ↓ ∎

    place-EB : (₄₊ k) ⊢ place 2 (HG₀₁ k • B₁₀ k) ≈ EB
    place-EB = trans (place-• 2 (HG₀₁ k) (B₁₀ k)) (cong place-E place-B)

    via-place : ∀ {X Y : Circuit (₃₊ k)} {a b : Circuit (₄₊ k)} →
                (₄₊ k) ⊢ place 2 X ≈ a → (₄₊ k) ⊢ place 2 Y ≈ b → ⟦ X • Y ⟧ ~ ⟦ Y • X ⟧ →
                (₄₊ k) ⊢ a • b ≈ b • a
    via-place {X} {Y} {a} {b} ea eb e = begin
      a • b                      ≈⟨ cong (sym ea) (sym eb) ⟩
      place 2 X • place 2 Y      ≈⟨ sym (place-• 2 X Y) ⟩
      place 2 (X • Y)            ≈⟨ lemma-5-1 2 complete e ⟩
      place 2 (Y • X)            ≈⟨ place-• 2 Y X ⟩
      place 2 Y • place 2 X      ≈⟨ cong eb ea ⟩
      b • a ∎

    EB-P₁ : (₄₊ k) ⊢ EB • P₁ ≈ P₁ • EB
    EB-P₁ = via-place place-EB (place-low 2 (CH • CZ)) (sem-EB-P₁ k)

    EB-P₂ : (₄₊ k) ⊢ EB • P₂ ≈ P₂ • EB
    EB-P₂ = via-place place-EB (place-low 2 (CZ • CH)) (sem-EB-P₂ k)

    EB-H₁ : (₄₊ k) ⊢ EB • H ↑ ≈ H ↑ • EB
    EB-H₁ = via-place place-EB (place-low 2 (H ↑)) (sem-EB-H₁ k)

    ------------------------------------------------------------------
    -- E • B passes the pieces of W

    EB-CZ : (₄₊ k) ⊢ EB • CZ ↑ ≈ CZ ↑ • EB
    EB-CZ = pass′ E-CZ B-CZ

    EB-CX : (₄₊ k) ⊢ EB • CX ↑ ≈ CX ↑ • EB
    EB-CX = pass EB-H₁ (pass EB-CZ EB-H₁)

    EB-Ex : (₄₊ k) ⊢ EB • Ex ↑ ≈ Ex ↑ • EB
    EB-Ex = conj-pass Ex↑² (X.⟪⟫-•₂ E-Ex B-Ex)
      where module X = Conj (Ex ↑) Ex↑²

    EB-P₃ : (₄₊ k) ⊢ EB • P₃ ≈ P₃ • EB
    EB-P₃ = begin
      EB • P₃                        ≈⟨ back _ P₃-P₁ ⟩
      EB • (Ex ↑ • P₁ • Ex ↑)        ≈⟨ pass EB-Ex (pass EB-P₁ EB-Ex) ⟩
      (Ex ↑ • P₁ • Ex ↑) • EB        ≈⟨ front _ (sym P₃-P₁) ⟩
      P₃ • EB ∎

  ----------------------------------------------------------------------
  -- (283)

  eq283 : Eq283 k
  eq283 = begin
    EB • CCZX
      ≈⟨ back _ W-dec ⟩
    EB • (P₁ • CX ↑ • P₂ • CX ↑ • P₃)
      ≈⟨ pass EB-P₁ (pass EB-CX (pass EB-P₂ (pass EB-CX EB-P₃))) ⟩
    (P₁ • CX ↑ • P₂ • CX ↑ • P₃) • EB
      ≈⟨ front _ (sym W-dec) ⟩
    CCZX • EB ∎

  ----------------------------------------------------------------------
  -- (284) and its mirror: B • x • B ≈ E • x • E for x = W, V

  private
    swap-BE : ∀ {x : Circuit (₄₊ k)} → (₄₊ k) ⊢ EB • x ≈ x • EB → (₄₊ k) ⊢ B • x • B ≈ E • x • E
    swap-BE {x} h = begin
      B • x • B                    ≈⟨ sym left-unit ⟩
      ε • B • x • B                ≈⟨ front _ (sym E²) ⟩
      (E • E) • B • x • B          ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • ((□ • □) • □) • □) Eq.refl ⟩
      E • ((E • B) • x) • B        ≈⟨ back _ (front _ h) ⟩
      E • (x • (E • B)) • B        ≈⟨ by-passoc (□ • (□ • (□ • □)) • □) (□ • □ • □ • (□ • □)) Eq.refl ⟩
      E • x • E • (B • B)          ≈⟨ back _ (back _ (back _ B²)) ⟩
      E • x • E • ε                ≈⟨ back _ (back _ right-unit) ⟩
      E • x • E ∎

    EB-V : (₄₊ k) ⊢ EB • CCXZ ≈ CCXZ • EB
    EB-V = pass-inv eq283 W-V V-W

  -- (269): Λ□ (₃₊ k) is CCZX • B • CCXZ • B by definition.
  eq284 : Eq284 k
  eq284 = back CCZX (swap-BE EB-V)

  -- (286): Λ□ (₃₊ k) is also CCXZ • B • CCZX • B.
  eq284′ : Eq284′ k
  eq284′ = trans (eq286 k) (back CCXZ (swap-BE eq283))

  ----------------------------------------------------------------------
  -- (285): H on the box wire passes the box

  eq285ₙ : Eq285 k
  eq285ₙ = eq285 k eq284 eq284′

  ----------------------------------------------------------------------
  -- What the later equations use: the box B and the H gate E, and their
  -- product, against the gates on the wires 0 1 2

  B□-CZ↑ : (₄₊ k) ⊢ B□ k • CZ ↑ ≈ CZ ↑ • B□ k
  B□-CZ↑ = B-CZ

  B□-CH↑ : (₄₊ k) ⊢ B□ k • CH ↑ ≈ CH ↑ • B□ k
  B□-CH↑ = B-CH

  B□-Ex↑ : (₄₊ k) ⊢ Ex ↑ • B□ k • Ex ↑ ≈ B□ k
  B□-Ex↑ = B-Ex

  B□-PP↑ : (₄₊ k) ⊢ PP ↑ • B□ k • PP ↑ ≈ B□ k
  B□-PP↑ = B-PP

  B□² : (₄₊ k) ⊢ B□ k • B□ k ≈ ε
  B□² = B²

  E□² : (₄₊ k) ⊢ E□ k • E□ k ≈ ε
  E□² = E²

  E□-CZ↑ : (₄₊ k) ⊢ E□ k • CZ ↑ ≈ CZ ↑ • E□ k
  E□-CZ↑ = E-CZ

  E□-Ex↑ : (₄₊ k) ⊢ Ex ↑ • E□ k • Ex ↑ ≈ E□ k
  E□-Ex↑ = E-Ex

  EB-CX↑ : (₄₊ k) ⊢ (E□ k • B□ k) • CX ↑ ≈ CX ↑ • (E□ k • B□ k)
  EB-CX↑ = EB-CX

  -- The box and the H gate one width down, placed with wire 2 idle.
  place-B□ : (₄₊ k) ⊢ place 2 (B₁₀ k) ≈ B□ k
  place-B□ = place-B

  place-E□ : (₄₊ k) ⊢ place 2 (HG₀₁ k) ≈ E□ k
  place-E□ = place-E

  -- Two circuits placed with wire 2 idle commute when their unplaced
  -- versions do semantically.
  commute-placed : ∀ {X Y : Circuit (₃₊ k)} {a b : Circuit (₄₊ k)} →
                   (₄₊ k) ⊢ place 2 X ≈ a → (₄₊ k) ⊢ place 2 Y ≈ b → ⟦ X • Y ⟧ ~ ⟦ Y • X ⟧ →
                   (₄₊ k) ⊢ a • b ≈ b • a
  commute-placed = via-place
