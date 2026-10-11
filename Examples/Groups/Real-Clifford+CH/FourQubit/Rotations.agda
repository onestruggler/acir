------------------------------------------------------------------------
-- Presentations of groups
--
-- Controlled rotations and boxes on four qubits (Clément, Lemma D.5,
-- Equations (172)–(178))
--
-- The doubly controlled ZX from wires 2 and 3 meets the CZ of the lower
-- pair at the price of a box, (172), (173); P ⊗ P below turns the doubly
-- controlled ZX one wire up into the XZ, (174); the box with its box
-- wire on wire 1 lets a controlled ZX on that wire through, (175), and
-- a doubly controlled XZ negated on a wire it controls, (176); and the
-- three-controlled box is built from that box and the controlled
-- rotations from wires 1 and 2, or from wire 1 alone, (177), (178).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Rotations
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; CZ² ; CH²)
open import Examples.Groups.Real-Clifford+CH.SemanticSteps using (Evaluated ; evaluated)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq170 ; eq170′)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using ( eq117 ; eq118 ; eq127 ; eq124 ; eq137 ; eq139 ; eq140 ; K-W ; CZ₂₀²
        ; °CCZX ; °CCXZ ; °CZXC ; °CXZC ; module N₂ ; S↑-CH↓
        ; CH↓-CCZX ; PP-CH↑ )
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- (172), (173): the lower CZ and the doubly controlled ZX from wires 2, 3

-- The doubly controlled ZX and XZ on wire 0 from wires 2 and 3.
CCZX₂₃ CCXZ₂₃ : Circuit (₄₊ n)
CCZX₂₃ = O₃ CCZX
CCXZ₂₃ = O₃ CCXZ

private
  CH₂₀² : (₄₊ n) ⊢ CH₂₀ • CH₂₀ ≈ ε
  CH₂₀² = O-invol CH CH²

  CCZX₂₃-form : (₄₊ n) ⊢ CCZX₂₃ ≈ CH₂₀ • CZ₃₀ • CH₂₀ • CZ₃₀
  CCZX₂₃-form {n} = begin
    S₀₁.⟪ CH ↑ • P₁₃ CZ • CH ↑ • P₁₃ CZ ⟫
      ≈⟨ S₀₁.⟪⟫-•₄ refl refl refl refl ⟩
    CH₂₀ • P₀₃ CZ • CH₂₀ • P₀₃ CZ
      ≈⟨ back _ (cong (sym CZ₃₀-P) (back _ (sym CZ₃₀-P))) ⟩
    CH₂₀ • CZ₃₀ • CH₂₀ • CZ₃₀ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  CCXZ₂₃-form : (₄₊ n) ⊢ CCXZ₂₃ ≈ CZ₃₀ • CH₂₀ • CZ₃₀ • CH₂₀
  CCXZ₂₃-form {n} = begin
    S₀₁.⟪ P₁₃ CZ • CH ↑ • P₁₃ CZ • CH ↑ ⟫
      ≈⟨ S₀₁.⟪⟫-•₄ refl refl refl refl ⟩
    P₀₃ CZ • CH₂₀ • P₀₃ CZ • CH₂₀
      ≈⟨ cong (sym CZ₃₀-P) (back _ (front _ (sym CZ₃₀-P))) ⟩
    CZ₃₀ • CH₂₀ • CZ₃₀ • CH₂₀ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  -- The upper swap of the lower triple fixes CCZX and CCXZ, and the box.
  S-W : (₄₊ n) ⊢ S₁₂.⟪ CCZX ⟫ ≈ CCZX
  S-W {n} = S₁₂.⟪⟫-fix (sym eq127)
    where open Tools ((₄₊ n) VRel,_===_)

  S-V : (₄₊ n) ⊢ S₁₂.⟪ CCXZ ⟫ ≈ CCXZ
  S-V {n} = begin
    S₁₂.⟪ CCXZ ⟫           ≈⟨ S₁₂.⟪⟫-cong (sym eq124) ⟩
    S₁₂.⟪ CCZX • CZ ↑ ⟫    ≈⟨ S₁₂.⟪⟫-•₂ S-W (U-sem (Ex • CZ • Ex) CZ Eq.refl) ⟩
    CCZX • CZ ↑            ≈⟨ eq124 ⟩
    CCXZ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  -- The outer CH exchanges CCZX and CCXZ, and passes the box: the lower
  -- CH, through the swap.
  p-W : (₄₊ n) ⊢ CH₂₀ • CCZX ≈ CCXZ • CH₂₀
  p-W = S₁₂.⟪⟫-≈ CH↓-CCZX (S₁₂.⟪⟫-•₂ S↑-CH↓ S-W) (S₁₂.⟪⟫-•₂ S-V S↑-CH↓)

  p-box : (₄₊ n) ⊢ CH₂₀ • box₃ ≈ box₃ • CH₂₀
  p-box = S₁₂.⟪⟫-≈ eq163 (S₁₂.⟪⟫-•₂ S↑-CH↓ eq157) (S₁₂.⟪⟫-•₂ eq157 S↑-CH↓)

module Q {n : ℕ} = Conj {₄₊ n} (CZ ↓) CZ²

private
  -- The lower CZ turns the outer CH into itself times CCZX: (14).
  Q-p : (₄₊ n) ⊢ Q.⟪ CH₂₀ ⟫ ≈ CH₂₀ • CCZX
  Q-p {n} = sym (trans (back _ (ax symm-controls)) (cancelˡ _ CH₂₀²))
    where open Tools ((₄₊ n) VRel,_===_)

  Q-c : (₄₊ n) ⊢ Q.⟪ CZ₃₀ ⟫ ≈ CZ₃₀
  Q-c {n} = Q.⟪⟫-fix (begin
    CZ ↓ • CZ₃₀       ≈⟨ back _ CZ₃₀-P ⟩
    L CZ • P₀₃ CZ     ≈⟨ comm-01-03 CZ CZ (evaluated Eq.refl) ⟩
    P₀₃ CZ • L CZ     ≈⟨ front _ (sym CZ₃₀-P) ⟩
    CZ₃₀ • CZ ↓ ∎)
    where open Tools ((₄₊ n) VRel,_===_)

  Q-W₂₃ : (₄₊ n) ⊢ Q.⟪ CCZX₂₃ ⟫ ≈ CCZX₂₃ • box₃
  Q-W₂₃ {n} = begin
    Q.⟪ CCZX₂₃ ⟫
      ≈⟨ Q.⟪⟫-cong CCZX₂₃-form ⟩
    Q.⟪ CH₂₀ • CZ₃₀ • CH₂₀ • CZ₃₀ ⟫
      ≈⟨ Q.⟪⟫-•₄ Q-p Q-c Q-p Q-c ⟩
    (CH₂₀ • CCZX) • CZ₃₀ • (CH₂₀ • CCZX) • CZ₃₀
      ≈⟨ back _ (back _ (front _ p-W)) ⟩
    (CH₂₀ • CCZX) • CZ₃₀ • (CCXZ • CH₂₀) • CZ₃₀
      ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
    CH₂₀ • CCZX • CZ₃₀ • CCXZ • (CH₂₀ • CZ₃₀)
      ≈⟨ back _ (back _ (back _ (back _ (insertˡ _ CZ₃₀²)))) ⟩
    CH₂₀ • CCZX • CZ₃₀ • CCXZ • (CZ₃₀ • CZ₃₀ • CH₂₀ • CZ₃₀)
      ≈⟨ by-passoc (□ • □ • □ • □ • (□ • □ • □ • □)) (□ • (□ • □ • □ • □) • (□ • □ • □)) Eq.refl ⟩
    CH₂₀ • box₃ • (CZ₃₀ • CH₂₀ • CZ₃₀)
      ≈⟨ back _ (comm-• (sym CZ₃₀-box) (comm-• (sym p-box) (sym CZ₃₀-box))) ⟩
    CH₂₀ • (CZ₃₀ • CH₂₀ • CZ₃₀) • box₃
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □ • □ • □) • □) Eq.refl ⟩
    (CH₂₀ • CZ₃₀ • CH₂₀ • CZ₃₀) • box₃
      ≈⟨ front _ (sym CCZX₂₃-form) ⟩
    CCZX₂₃ • box₃ ∎
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)

-- (172)
eq172 : (₄₊ n) ⊢ CZ ↓ • CCZX₂₃ ≈ CCZX₂₃ • box₃ • CZ ↓
eq172 {n} = trans (sym (conj-comm CZ² (conj-sym CZ² Q-W₂₃))) assoc
  where open Tools ((₄₊ n) VRel,_===_)

private
  W₂₃V₂₃ : (₄₊ n) ⊢ CCZX₂₃ • CCXZ₂₃ ≈ ε
  W₂₃V₂₃ {n} = trans (sym (S₀₁.⟪⟫-• (CCZX ↑) (CCXZ ↑)))
    (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCZX • CCXZ) ε eq117)) S₀₁.⟪⟫-ε)
    where open Tools ((₄₊ n) VRel,_===_)

  V₂₃W₂₃ : (₄₊ n) ⊢ CCXZ₂₃ • CCZX₂₃ ≈ ε
  V₂₃W₂₃ {n} = trans (sym (S₀₁.⟪⟫-• (CCXZ ↑) (CCZX ↑)))
    (trans (S₀₁.⟪⟫-cong (lemma-cong↑ (CCXZ • CCZX) ε eq118)) S₀₁.⟪⟫-ε)
    where open Tools ((₄₊ n) VRel,_===_)

-- (173): the same read backwards.
eq173 : (₄₊ n) ⊢ CCXZ₂₃ • CZ ↓ ≈ CZ ↓ • box₃ • CCXZ₂₃
eq173 {n} = begin
  CCXZ₂₃ • CZ ↓
    ≈⟨ sym right-unit ⟩
  (CCXZ₂₃ • CZ ↓) • ε
    ≈⟨ back _ (sym W₂₃V₂₃) ⟩
  (CCXZ₂₃ • CZ ↓) • (CCZX₂₃ • CCXZ₂₃)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  CCXZ₂₃ • (CZ ↓ • CCZX₂₃) • CCXZ₂₃
    ≈⟨ back _ (front _ eq172) ⟩
  CCXZ₂₃ • (CCZX₂₃ • box₃ • CZ ↓) • CCXZ₂₃
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • (□ • □) • □) Eq.refl ⟩
  (CCXZ₂₃ • CCZX₂₃) • (box₃ • CZ ↓) • CCXZ₂₃
    ≈⟨ trans (front _ V₂₃W₂₃) left-unit ⟩
  (box₃ • CZ ↓) • CCXZ₂₃
    ≈⟨ front _ (sym eq160) ⟩
  (CZ ↓ • box₃) • CCXZ₂₃
    ≈⟨ assoc ⟩
  CZ ↓ • box₃ • CCXZ₂₃ ∎
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (174): P ⊗ P below the doubly controlled ZX one wire up

private
  PP↓² : (₄₊ n) ⊢ PP ↓ • PP ↓ ≈ ε
  PP↓² = L-sem (PP • PP) ε Eq.refl

module PP₄ {n : ℕ} = Conj {₄₊ n} (PP ↓) PP↓²

private
  -- P ⊗ P below turns the CZ of wires 1 and 3 into the CH: (18) on the
  -- triple 0 1 3.
  PP-d′ : (₄₊ n) ⊢ PP₄.⟪ P₁₃ CZ ⟫ ≈ P₁₃ CH
  PP-d′ {n} = begin
    PP ↓ • P₁₃ CZ • PP ↓
      ≈⟨ sym (cong (M₃-L PP) (cong (M₃-U CZ) (M₃-L PP))) ⟩
    M₃ (L₀ PP) • M₃ (U₀ CZ) • M₃ (L₀ PP)
      ≈⟨ sym (S₂₃.⟪⟫-•₃ refl refl refl) ⟩
    M₃ (L₀ PP • U₀ CZ • L₀ PP)
      ≈⟨ M₃-sem (L₀ PP • U₀ CZ • L₀ PP) (U₀ CH) Eq.refl ⟩
    M₃ (U₀ CH)
      ≈⟨ M₃-U CH ⟩
    P₁₃ CH ∎
    where open Tools ((₄₊ n) VRel,_===_)

  -- CCXZ with the roles of its controls exchanged, one wire up.
  V↑-form : (₄₊ n) ⊢ CCXZ ↑ ≈ CZ ↑ • P₁₃ CH • CZ ↑ • P₁₃ CH
  V↑-form {n} = lemma-cong↑ CCXZ (CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀) alt
    where
    open Tools ((₃₊ n) VRel,_===_)
    alt : (₃₊ n) ⊢ CCXZ ≈ CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀
    alt = begin
      CCXZ
        ≈⟨ sym K-W ⟩
      CZ ↓ • CCZX • CZ ↓
        ≈⟨ back _ (front _ (ax symm-controls)) ⟩
      CZ ↓ • (CH₂₀ • CZ ↓ • CH₂₀ • CZ ↓) • CZ ↓
        ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) (□ • □ • □ • □ • (□ • □)) Eq.refl ⟩
      CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀ • (CZ ↓ • CZ ↓)
        ≈⟨ back _ (back _ (back _ (cancelᵉ _ CZ²))) ⟩
      CZ ↓ • CH₂₀ • CZ ↓ • CH₂₀ ∎

eq174 : (₄₊ n) ⊢ PP ↓ • CCZX ↑ ≈ CCXZ ↑ • PP ↓
eq174 {n} = sym (conj-comm PP↓² (conj-sym PP↓² e))
  where
  open Tools ((₄₊ n) VRel,_===_)
  e : (₄₊ n) ⊢ PP₄.⟪ CCZX ↑ ⟫ ≈ CCXZ ↑
  e = trans (PP₄.⟪⟫-•₄ PP-CH↑ PP-d′ PP-CH↑ PP-d′) (sym V↑-form)

------------------------------------------------------------------------
-- (175): a controlled ZX on the box wire passes the doubly controlled H

-- The gate is the doubly controlled H with its target on wire 0 and its
-- box wire on wire 1: ΛH 2 under the lower swap.
private
  zx : Circuit 2
  zx = CH • Z ↓ • CH • Z ↓

  P₀₃-H↓ : (₄₊ n) ⊢ P₀₃ (H ↓) ≈ H ↓
  P₀₃-H↓ {n} = begin
    Ex ↓ • (Ex ↑ • H ↑ ↑ • Ex ↑) • Ex ↓
      ≈⟨ back _ (front _ (U-sem (Ex • H ↑ • Ex) (H ↓) Eq.refl)) ⟩
    Ex ↓ • H ↑ • Ex ↓
      ≈⟨ L-sem (Ex • H ↑ • Ex) (H ↓) Eq.refl ⟩
    H ↓ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  -- P ⊗ P below turns the controlled ZX from wire 3 into CZ H CZ H.
  PP-zx : (₄₊ n) ⊢ PP₄.⟪ P₀₃ zx ⟫ ≈ CZ₃₀ • H ↓ • CZ₃₀ • H ↓
  PP-zx {n} = begin
    PP ↓ • P₀₃ zx • PP ↓
      ≈⟨ sym (cong (M₃-L PP) (cong (M₃-O zx) (M₃-L PP))) ⟩
    M₃ (L₀ PP) • M₃ (O₀ zx) • M₃ (L₀ PP)
      ≈⟨ sym (S₂₃.⟪⟫-•₃ refl refl refl) ⟩
    M₃ (L₀ PP • O₀ zx • L₀ PP)
      ≈⟨ M₃-sem (L₀ PP • O₀ zx • L₀ PP) (O₀ (CZ • H ↓ • CZ • H ↓)) Eq.refl ⟩
    M₃ (O₀ (CZ • H ↓ • CZ • H ↓))
      ≈⟨ M₃-O (CZ • H ↓ • CZ • H ↓) ⟩
    P₀₃ (CZ • H ↓ • CZ • H ↓)
      ≈⟨ trans (P₀₃-• CZ (H ↓ • CZ • H ↓)) (back _ (trans (P₀₃-• (H ↓) (CZ • H ↓)) (back _ (P₀₃-• CZ (H ↓))))) ⟩
    P₀₃ CZ • P₀₃ (H ↓) • P₀₃ CZ • P₀₃ (H ↓)
      ≈⟨ cong (sym CZ₃₀-P) (cong P₀₃-H↓ (cong (sym CZ₃₀-P) P₀₃-H↓)) ⟩
    CZ₃₀ • H ↓ • CZ₃₀ • H ↓ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  ch-box : (₄₊ n) ⊢ (CZ₃₀ • H ↓ • CZ₃₀ • H ↓) • box₃ ≈ box₃ • (CZ₃₀ • H ↓ • CZ₃₀ • H ↓)
  ch-box {n} = sym (comm-• (sym CZ₃₀-box) (comm-• (sym eq155) (comm-• (sym CZ₃₀-box) (sym eq155))))
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)

  zx-ΛH : (₄₊ n) ⊢ P₀₃ (ΛZX 1) • (ΛH 2 ↓ᵏ n) ≈ (ΛH 2 ↓ᵏ n) • P₀₃ (ΛZX 1)
  zx-ΛH {n} = begin
    P₀₃ (ΛZX 1) • (ΛH 2 ↓ᵏ n)   ≈⟨ front _ form ⟩
    P₀₃ zx • PP₄.⟪ box₃ ⟫        ≈⟨ PP₄.⟪⟫-≈ ch-box (PP₄.⟪⟫-•₂ PP-Y refl) (PP₄.⟪⟫-•₂ refl PP-Y) ⟩
    PP₄.⟪ box₃ ⟫ • P₀₃ zx        ≈⟨ back _ (sym form) ⟩
    (ΛH 2 ↓ᵏ n) • P₀₃ (ΛZX 1) ∎
    where
    open Tools ((₄₊ n) VRel,_===_)
    form : (₄₊ n) ⊢ P₀₃ (ΛZX 1) ≈ P₀₃ zx
    form = P₀₃-sem (ΛZX 1) zx Eq.refl
    PP-Y : (₄₊ n) ⊢ PP₄.⟪ CZ₃₀ • H ↓ • CZ₃₀ • H ↓ ⟫ ≈ P₀₃ zx
    PP-Y = conj-sym PP↓² PP-zx

eq175 : (₄₊ n) ⊢ P₁₃ (ΛZX 1) • S₀₁.⟪ ΛH 2 ↓ᵏ n ⟫ ≈ S₀₁.⟪ ΛH 2 ↓ᵏ n ⟫ • P₁₃ (ΛZX 1)
eq175 {n} = S₀₁.⟪⟫-≈ zx-ΛH
  (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ (P₁₃ (ΛZX 1))) refl)
  (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ (P₁₃ (ΛZX 1))))
  where open Tools ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (176): a white control against a black one

-- The box with its box wire on wire 1: controls on wires 0, 2, 3.
box₃′ : Circuit (₄₊ n)
box₃′ = S₀₁.⟪ box₃ ⟫

private
  box₃′-form : (₄₊ n) ⊢ box₃′ ≈ S₀₁.⟪ CCZX ⟫ • P₁₃ CZ • S₀₁.⟪ CCXZ ⟫ • P₁₃ CZ
  box₃′-form {n} = S₀₁.⟪⟫-•₄ refl S-c refl S-c
    where
    open Tools ((₄₊ n) VRel,_===_)
    S-c : (₄₊ n) ⊢ S₀₁.⟪ CZ₃₀ ⟫ ≈ P₁₃ CZ
    S-c = trans (S₀₁.⟪⟫-cong CZ₃₀-P) (S₀₁.⟪⟫-⟪⟫ (P₁₃ CZ))

  -- (140), through the lower swap: the negated CCXZ passes the doubly
  -- controlled ZX with its target on wire 1; and so its inverse.
  °V-W′ : (₄₊ n) ⊢ °CCXZ • S₀₁.⟪ CCZX ⟫ ≈ S₀₁.⟪ CCZX ⟫ • °CCXZ
  °V-W′ {n} = sym (S₀₁.⟪⟫-≈ eq140
    (S₀₁.⟪⟫-•₂ refl (S₀₁.⟪⟫-⟪⟫ °CCXZ)) (S₀₁.⟪⟫-•₂ (S₀₁.⟪⟫-⟪⟫ °CCXZ) refl))
    where open Tools ((₄₊ n) VRel,_===_)

  °V-V′ : (₄₊ n) ⊢ °CCXZ • S₀₁.⟪ CCXZ ⟫ ≈ S₀₁.⟪ CCXZ ⟫ • °CCXZ
  °V-V′ {n} = comm-inv W′V′ V′W′ °V-W′
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    W′V′ : (₄₊ n) ⊢ S₀₁.⟪ CCZX ⟫ • S₀₁.⟪ CCXZ ⟫ ≈ ε
    W′V′ = trans (sym (S₀₁.⟪⟫-• CCZX CCXZ)) (trans (S₀₁.⟪⟫-cong eq117) S₀₁.⟪⟫-ε)
    V′W′ : (₄₊ n) ⊢ S₀₁.⟪ CCXZ ⟫ • S₀₁.⟪ CCZX ⟫ ≈ ε
    V′W′ = trans (sym (S₀₁.⟪⟫-• CCXZ CCZX)) (trans (S₀₁.⟪⟫-cong eq118) S₀₁.⟪⟫-ε)

  -- The CZ of wires 1 and 3 passes it too.
  °V-d′ : (₄₊ n) ⊢ °CCXZ • P₁₃ CZ ≈ P₁₃ CZ • °CCXZ
  °V-d′ {n} = sym (comm-• d′-X (comm-• (comm-abab (P₁₃-O CZ CZ) d′-a) d′-X))
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    d′-X : (₄₊ n) ⊢ P₁₃ CZ • X ↑ ↑ ≈ X ↑ ↑ • P₁₃ CZ
    d′-X = sym (comm-12-13 (X ↑) CZ (evaluated Eq.refl))
    d′-a : (₄₊ n) ⊢ P₁₃ CZ • CH ↓ ≈ CH ↓ • P₁₃ CZ
    d′-a = sym (comm-01-13 CH CZ (evaluated Eq.refl))

eq176 : (₄₊ n) ⊢ °CCXZ • box₃′ ≈ box₃′ • °CCXZ
eq176 {n} = begin
  °CCXZ • box₃′
    ≈⟨ back _ box₃′-form ⟩
  °CCXZ • (S₀₁.⟪ CCZX ⟫ • P₁₃ CZ • S₀₁.⟪ CCXZ ⟫ • P₁₃ CZ)
    ≈⟨ comm-• °V-W′ (comm-• °V-d′ (comm-• °V-V′ °V-d′)) ⟩
  (S₀₁.⟪ CCZX ⟫ • P₁₃ CZ • S₀₁.⟪ CCXZ ⟫ • P₁₃ CZ) • °CCXZ
    ≈⟨ front _ (sym box₃′-form) ⟩
  box₃′ • °CCXZ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

------------------------------------------------------------------------
-- (177), (178): the box from the box one wire over

private
  °box₃′ : Circuit (₄₊ n)
  °box₃′ = S₀₁.⟪ °box₃ ⟫

  -- The CZ from wire 3 is the two boxes, black and white on wire 2:
  -- (170) through the lower swap.
  c-BB : (₄₊ n) ⊢ CZ₃₀ ≈ box₃′ • °box₃′
  c-BB {n} = sym (trans (sym (S₀₁.⟪⟫-• box₃ °box₃)) (trans (S₀₁.⟪⟫-cong eq170) (sym CZ₃₀-P)))
    where open Tools ((₄₊ n) VRel,_===_)

  c-B′B : (₄₊ n) ⊢ CZ₃₀ ≈ °box₃′ • box₃′
  c-B′B {n} = sym (trans (sym (S₀₁.⟪⟫-• °box₃ box₃)) (trans (S₀₁.⟪⟫-cong eq170′) (sym CZ₃₀-P)))
    where open Tools ((₄₊ n) VRel,_===_)

  °B² : (₄₊ n) ⊢ °box₃′ • °box₃′ ≈ ε
  °B² = S₀₁.⟪⟫-invol (N₂.⟪⟫-invol eq166)

  -- (176) with the colours exchanged.
  V-°B : (₄₊ n) ⊢ CCXZ • °box₃′ ≈ °box₃′ • CCXZ
  V-°B {n} = N₂.⟪⟫-≈ eq176 (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ CCXZ) N₂-B) (N₂.⟪⟫-•₂ N₂-B (N₂.⟪⟫-⟪⟫ CCXZ))
    where
    open Tools ((₄₊ n) VRel,_===_)
    N₂-Ex : (₄₊ n) ⊢ N₂.⟪ Ex ↓ ⟫ ≈ Ex ↓
    N₂-Ex = N₂.⟪⟫-fix (sym (L-comm Ex X))
    N₂-B : (₄₊ n) ⊢ N₂.⟪ box₃′ ⟫ ≈ °box₃′
    N₂-B = N₂.⟪⟫-•₃ N₂-Ex refl N₂-Ex

-- (177)
eq177 : (₄₊ n) ⊢ box₃ ≈ CCZX • box₃′ • CCXZ • box₃′
eq177 {n} = begin
  CCZX • CZ₃₀ • CCXZ • CZ₃₀
    ≈⟨ back _ (cong c-BB (back _ c-B′B)) ⟩
  CCZX • (box₃′ • °box₃′) • CCXZ • (°box₃′ • box₃′)
    ≈⟨ by-passoc (□ • (□ • □) • □ • (□ • □)) (□ • □ • (□ • □ • □) • □) Eq.refl ⟩
  CCZX • box₃′ • (°box₃′ • CCXZ • °box₃′) • box₃′
    ≈⟨ back _ (back _ (front _ (bzb °B² V-°B))) ⟩
  CCZX • box₃′ • CCXZ • box₃′ ∎
  where
  open Tools ((₄₊ n) VRel,_===_)
  open Alg ((₄₊ n) VRel,_===_)

private
  °W°V : (₄₊ n) ⊢ °CCZX • °CCXZ ≈ ε
  °W°V {n} = trans (sym (N₂.⟪⟫-• CCZX CCXZ)) (trans (N₂.⟪⟫-cong eq117) N₂.⟪⟫-ε)
    where open Tools ((₄₊ n) VRel,_===_)

  °V°W : (₄₊ n) ⊢ °CCXZ • °CCZX ≈ ε
  °V°W {n} = trans (sym (N₂.⟪⟫-• CCXZ CCZX)) (trans (N₂.⟪⟫-cong eq118) N₂.⟪⟫-ε)
    where open Tools ((₄₊ n) VRel,_===_)

  -- CCZX and CCXZ from the controlled rotation of wire 1 and the negated
  -- doubly controlled one: (137) and its inverse.
  W-C : (₄₊ n) ⊢ CCZX ≈ L (ΛZX 1) • °CCXZ
  W-C {n} = begin
    CCZX                        ≈⟨ sym right-unit ⟩
    CCZX • ε                    ≈⟨ back _ (sym °W°V) ⟩
    CCZX • °CCZX • °CCXZ        ≈⟨ sym assoc ⟩
    (CCZX • °CCZX) • °CCXZ      ≈⟨ front _ eq137 ⟩
    L (ΛZX 1) • °CCXZ ∎
    where open Tools ((₄₊ n) VRel,_===_)

  V-C : (₄₊ n) ⊢ CCXZ ≈ °CCZX • L (ΛXZ 1)
  V-C {n} = begin
    CCXZ                        ≈⟨ sym left-unit ⟩
    ε • CCXZ                    ≈⟨ front _ (sym °W°V) ⟩
    (°CCZX • °CCXZ) • CCXZ      ≈⟨ assoc ⟩
    °CCZX • °CCXZ • CCXZ        ≈⟨ back _ °VV ⟩
    °CCZX • L (ΛXZ 1) ∎
    where
    open Tools ((₄₊ n) VRel,_===_)
    open Alg ((₄₊ n) VRel,_===_)
    °VV : (₄₊ n) ⊢ °CCXZ • CCXZ ≈ L (ΛXZ 1)
    °VV = inv-unique (unwrap′ °W°V eq117) (L-sem (ΛXZ 1 • ΛZX 1) ε Eq.refl) eq137

-- (178)
eq178 : (₄₊ n) ⊢ box₃ ≈ L (ΛZX 1) • box₃′ • L (ΛXZ 1) • box₃′
eq178 {n} = begin
  box₃
    ≈⟨ eq177 ⟩
  CCZX • box₃′ • CCXZ • box₃′
    ≈⟨ cong W-C (back _ (front _ V-C)) ⟩
  (L (ΛZX 1) • °CCXZ) • box₃′ • (°CCZX • L (ΛXZ 1)) • box₃′
    ≈⟨ by-passoc ((□ • □) • □ • (□ • □) • □) (□ • (□ • □) • □ • □ • □) Eq.refl ⟩
  L (ΛZX 1) • (°CCXZ • box₃′) • °CCZX • L (ΛXZ 1) • box₃′
    ≈⟨ back _ (front _ eq176) ⟩
  L (ΛZX 1) • (box₃′ • °CCXZ) • °CCZX • L (ΛXZ 1) • box₃′
    ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □) (□ • □ • (□ • □) • □ • □) Eq.refl ⟩
  L (ΛZX 1) • box₃′ • (°CCXZ • °CCZX) • L (ΛXZ 1) • box₃′
    ≈⟨ back _ (back _ (trans (front _ °V°W) left-unit)) ⟩
  L (ΛZX 1) • box₃′ • L (ΛXZ 1) • box₃′ ∎
  where open Tools ((₄₊ n) VRel,_===_)
