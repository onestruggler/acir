------------------------------------------------------------------------
-- Presentations of groups
--
-- A white H gate against a controlled rotation, and two triply
-- controlled rotations of different colours merged (Clément, Lemma D.5,
-- Equations (219)–(226))
--
--   (219)   H(1, 2; 0, °3)  against the triply controlled XZ on wire 0
--   (220)   H(2, 1; 0, °3)  against the ZX on wire 0 from the wires 1, 3
--   (221)–(226)   the triply controlled ZX (XZ) with a white control
--                 times the black one is the ZX (XZ) without that control
--
-- (219): the XZ in its form B G B G, (211), with the control on wire 2 in
-- the role of wire 3, (214); the H gate passes the box B by (193) and the
-- black H gate G by (203).  (220): the rotation in its other form
-- p q p q, (14), with p the CH from wire 3 and q the lower CZ; between
-- the P ⊗ P of the H gate, p meets a box of the other colour, (164), and
-- q becomes a CH onto the box wire, (163).  The merges: in the forms
-- G B G B and °G °B °G °B of (210) every black letter passes every white
-- one — (181) twice, (201), (170) — so the product shuffles into
-- (°G G)(°B B)(°G G)(°B B), and °G G is the CH, (171), °B B the CZ, (170).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.Merges
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Ev complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Evals219 complete₂ complete₃
  using (ev-PP-CZ↓)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (box₃ ; CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Box complete₂ complete₃
  using (eq163)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Controlled complete₂ complete₃
  using (°box₃ ; eq164)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′ ; °ΛH₂′ ; eq181)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours2 complete₂ complete₃
  using (N₂-box₃′ ; eq181ᵇ)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours3 complete₂ complete₃
  using (S₂₃-°box₃ ; eq193)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
  using (S₀₁-N₃ ; eq171ᶜ ; eq171ᶜ′ ; ΛH₂′-°ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (PP₁₂ ; PP₁₂² ; G₆′-PP ; eq203)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Crossed complete₂ complete₃
  using (K ; K′)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₂ ; eq117 ; eq118)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- The gates

-- The doubly controlled H gates H(1, 2; 0, °3) and H(2, 1; 0, °3).
J J′ : Circuit (₄₊ n)
J      = S₂₃.⟪ S₀₁.⟪ °ΛH₂′ ⟫ ⟫
J′ {n} = N₃.⟪ S₀₁.⟪ S₁₂.⟪ ΛH 2 ↓ᵏ n ⟫ ⟫ ⟫

-- The doubly controlled ZX and XZ on wire 0 from the wires 1 and 3.
CCZX₁₃ CCXZ₁₃ : Circuit (₄₊ n)
CCZX₁₃ = M₃ CCZX
CCXZ₁₃ = M₃ CCXZ

-- The triply controlled ZX and XZ on wire 1, all controls black.
Kᵇ Kᵇ′ : Circuit (₄₊ n)
Kᵇ  = S₀₁.⟪ ZX₃ ⟫
Kᵇ′ = S₀₁.⟪ XZ₃ ⟫

------------------------------------------------------------------------
-- Words

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ
  open Alg Γ

  -- If every x passes every y, the product of the pairs y x is the
  -- product of the y's times the product of the x's.
  shuffle : ∀ {x₁ x₂ y₁ y₂ : Word X} →
            x₁ • y₁ ≈ y₁ • x₁ → x₁ • y₂ ≈ y₂ • x₁ → x₂ • y₁ ≈ y₁ • x₂ → x₂ • y₂ ≈ y₂ • x₂ →
            (y₁ • x₁) • (y₂ • x₂) • (y₁ • x₁) • (y₂ • x₂) ≈ (y₁ • y₂ • y₁ • y₂) • (x₁ • x₂ • x₁ • x₂)
  shuffle {x₁} {x₂} {y₁} {y₂} e₁₁ e₁₂ e₂₁ e₂₂ = begin
    (y₁ • x₁) • (y₂ • x₂) • (y₁ • x₁) • (y₂ • x₂)
      ≈⟨ by-passoc ((□ • □) • (□ • □) • (□ • □) • (□ • □)) (□ • (□ • □) • □ • □ • □ • □ • □) Eq.refl ⟩
    y₁ • (x₁ • y₂) • x₂ • y₁ • x₁ • y₂ • x₂
      ≈⟨ back _ (front _ e₁₂) ⟩
    y₁ • (y₂ • x₁) • x₂ • y₁ • x₁ • y₂ • x₂
      ≈⟨ by-passoc (□ • (□ • □) • □ • □ • □ • □ • □) (□ • □ • ((□ • □) • □) • □ • □ • □) Eq.refl ⟩
    y₁ • y₂ • ((x₁ • x₂) • y₁) • x₁ • y₂ • x₂
      ≈⟨ back _ (back _ (front _ (sym (comm-• (sym e₁₁) (sym e₂₁))))) ⟩
    y₁ • y₂ • (y₁ • (x₁ • x₂)) • x₁ • y₂ • x₂
      ≈⟨ by-passoc (□ • □ • (□ • (□ • □)) • □ • □ • □) (□ • □ • □ • ((□ • □ • □) • □) • □) Eq.refl ⟩
    y₁ • y₂ • y₁ • ((x₁ • x₂ • x₁) • y₂) • x₂
      ≈⟨ back _ (back _ (back _ (front _
           (sym (comm-• (sym e₁₂) (comm-• (sym e₂₂) (sym e₁₂))))))) ⟩
    y₁ • y₂ • y₁ • (y₂ • (x₁ • x₂ • x₁)) • x₂
      ≈⟨ by-passoc (□ • □ • □ • (□ • (□ • □ • □)) • □) ((□ • □ • □ • □) • (□ • □ • □ • □)) Eq.refl ⟩
    (y₁ • y₂ • y₁ • y₂) • (x₁ • x₂ • x₁ • x₂) ∎

------------------------------------------------------------------------
-- (219)

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    G₂ : Circuit (₄₊ n)
    G₂ = S₁₂.⟪ ΛH₀₁ ⟫

    N₂-Ex : N₂.⟪ Ex ↓ ⟫ ≈ Ex ↓
    N₂-Ex = N₂.⟪⟫-fix (sym (L-comm Ex X))

    -- (203) with the colours exchanged.
    e203ᵇ : S₀₁.⟪ °ΛH₂′ ⟫ • ΛH₂′ ≈ ΛH₂′ • S₀₁.⟪ °ΛH₂′ ⟫
    e203ᵇ = N₂.⟪⟫-≈ eq203 (N₂.⟪⟫-•₂ m (N₂.⟪⟫-⟪⟫ ΛH₂′)) (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ ΛH₂′) m)
      where
      m : N₂.⟪ S₀₁.⟪ ΛH₂′ ⟫ ⟫ ≈ S₀₁.⟪ °ΛH₂′ ⟫
      m = N₂.⟪⟫-•₃ N₂-Ex refl N₂-Ex

    -- Under the upper swap: the box wires on wire 2.
    J-G₂ : J • G₂ ≈ G₂ • J
    J-G₂ = S₂₃.⟪⟫-≈ e203ᵇ (S₂₃.⟪⟫-•₂ refl (S₂₃.⟪⟫-⟪⟫ G₂)) (S₂₃.⟪⟫-•₂ (S₂₃.⟪⟫-⟪⟫ G₂) refl)

    J-B : J • box₃′ ≈ box₃′ • J
    J-B = sym eq193

  eq219 : J • XZ₃ ≈ XZ₃ • J
  eq219 = begin
    J • XZ₃                               ≈⟨ back _ XZ₃-form₄ ⟩
    J • (box₃′ • G₂ • box₃′ • G₂)         ≈⟨ comm-abab J-B J-G₂ ⟩
    (box₃′ • G₂ • box₃′ • G₂) • J         ≈⟨ front _ (sym XZ₃-form₄) ⟩
    XZ₃ • J ∎

  ----------------------------------------------------------------------
  -- (220)

  private
    p′ q′ °B₁ : Circuit (₄₊ n)
    p′  = P₀₃ CH
    q′  = CZ ↓
    °B₁ = N₃.⟪ box₃′ ⟫

    -- (14) on the wires 0 1 3.
    N-form : CCZX₁₃ ≈ p′ • q′ • p′ • q′
    N-form = trans (S₂₃.⟪⟫-cong (ax symm-controls))
                   (S₂₃.⟪⟫-•₄ (O-S₂₃ CH) (L-S₂₃ CZ) (O-S₂₃ CH) (L-S₂₃ CZ))

    -- (164) with the colours exchanged, then on the wires of °B₁.
    e164° : U CH • °box₃ ≈ °box₃ • U CH
    e164° = N₂.⟪⟫-≈ eq164 (N₂.⟪⟫-•₂ (N₂.⟪⟫-⟪⟫ (U CH)) refl) (N₂.⟪⟫-•₂ refl (N₂.⟪⟫-⟪⟫ (U CH)))

    p′-°B₁ : p′ • °B₁ ≈ °B₁ • p′
    p′-°B₁ = S₀₁.⟪⟫-≈
      (S₂₃.⟪⟫-≈ e164° (S₂₃.⟪⟫-•₂ (U-S₂₃ CH) S₂₃-°box₃) (S₂₃.⟪⟫-•₂ S₂₃-°box₃ (U-S₂₃ CH)))
      (S₀₁.⟪⟫-•₂ refl (S₀₁-N₃ box₃)) (S₀₁.⟪⟫-•₂ (S₀₁-N₃ box₃) refl)

    p′-PP : p′ • PP₁₂ ≈ PP₁₂ • p′
    p′-PP = P₀₃-U CH PP

    p′-J′ : p′ • J′ ≈ J′ • p′
    p′-J′ = begin
      p′ • J′                        ≈⟨ back _ G₆′-PP ⟩
      p′ • (PP₁₂ • °B₁ • PP₁₂)       ≈⟨ comm-• p′-PP (comm-• p′-°B₁ p′-PP) ⟩
      (PP₁₂ • °B₁ • PP₁₂) • p′       ≈⟨ front _ (sym G₆′-PP) ⟩
      J′ • p′ ∎

    -- (163) with a white control on wire 3, under the lower swap: the CH
    -- from wire 0 onto the box wire.
    e163₃ : CH ↓ • N₃.⟪ box₃ ⟫ ≈ N₃.⟪ box₃ ⟫ • CH ↓
    e163₃ = N₃.⟪⟫-≈ eq163 (N₃.⟪⟫-•₂ N₃-a refl) (N₃.⟪⟫-•₂ refl N₃-a)
      where
      N₃-a : N₃.⟪ CH ↓ ⟫ ≈ CH ↓
      N₃-a = N₃.⟪⟫-fix (sym (L₃-top (L₀ CH) X))

    hc-°B₁ : HC ↓ • °B₁ ≈ °B₁ • HC ↓
    hc-°B₁ = S₀₁.⟪⟫-≈ e163₃ (S₀₁.⟪⟫-•₂ refl (S₀₁-N₃ box₃)) (S₀₁.⟪⟫-•₂ (S₀₁-N₃ box₃) refl)

    module Pj = Conj {₄₊ n} PP₁₂ PP₁₂²

    P-q′ : Pj.⟪ q′ ⟫ ≈ HC ↓
    P-q′ = L₃-ev ev-PP-CZ↓

    q′-J′ : q′ • J′ ≈ J′ • q′
    q′-J′ = Pj.⟪⟫-≈ hc-°B₁ (Pj.⟪⟫-•₂ back-q back-J) (Pj.⟪⟫-•₂ back-J back-q)
      where
      back-q : Pj.⟪ HC ↓ ⟫ ≈ q′
      back-q = trans (Pj.⟪⟫-cong (sym P-q′)) (Pj.⟪⟫-⟪⟫ q′)
      back-J : Pj.⟪ °B₁ ⟫ ≈ J′
      back-J = sym G₆′-PP

  eq220 : J′ • CCZX₁₃ ≈ CCZX₁₃ • J′
  eq220 = begin
    J′ • CCZX₁₃                   ≈⟨ back _ N-form ⟩
    J′ • (p′ • q′ • p′ • q′)      ≈⟨ comm-abab (sym p′-J′) (sym q′-J′) ⟩
    (p′ • q′ • p′ • q′) • J′      ≈⟨ front _ (sym N-form) ⟩
    CCZX₁₃ • J′ ∎

  ----------------------------------------------------------------------
  -- The merge on wire 0

  private
    a B °B G °G c : Circuit (₄₊ n)
    a  = CH ↓
    B  = box₃′
    °B = S₀₁.⟪ °box₃ ⟫
    G  = ΛH₂′
    °G = °ΛH₂′
    c  = CZ₃₀

    °ZX₃-form : N₂.⟪ ZX₃ ⟫ ≈ °G • °B • °G • °B
    °ZX₃-form = trans (N₂.⟪⟫-cong eq210) (N₂.⟪⟫-•₄ refl N₂-box₃′ refl N₂-box₃′)

    acac : CCZX₁₃ ≈ a • c • a • c
    acac = S₂₃.⟪⟫-•₄ (L-S₂₃ CH) m (L-S₂₃ CH) m
      where
      m : S₂₃.⟪ CZ₂₀ ⟫ ≈ c
      m = trans (O-S₂₃ CZ) (sym CZ₃₀-P)

    -- Black passes white.
    G-°G : G • °G ≈ °G • G
    G-°G = ΛH₂′-°ΛH₂′

    G-°B : G • °B ≈ °B • G
    G-°B = sym eq181ᵇ

    B-°G : B • °G ≈ °G • B
    B-°G = eq181

    B-°B : B • °B ≈ °B • B
    B-°B = trans eq170ᵇ (sym eq170ᵇ′)

  -- White first …
  merge₀ : N₂.⟪ ZX₃ ⟫ • ZX₃ ≈ CCZX₁₃
  merge₀ = sym (begin
    CCZX₁₃
      ≈⟨ acac ⟩
    a • c • a • c
      ≈⟨ cong (sym eq171ᶜ′) (cong (sym eq170ᵇ′) (cong (sym eq171ᶜ′) (sym eq170ᵇ′))) ⟩
    (°G • G) • (°B • B) • (°G • G) • (°B • B)
      ≈⟨ shuffle Γ G-°G G-°B B-°G B-°B ⟩
    (°G • °B • °G • °B) • (G • B • G • B)
      ≈⟨ sym (cong °ZX₃-form eq210) ⟩
    N₂.⟪ ZX₃ ⟫ • ZX₃ ∎)

  -- … and black first.
  merge₀′ : ZX₃ • N₂.⟪ ZX₃ ⟫ ≈ CCZX₁₃
  merge₀′ = sym (begin
    CCZX₁₃
      ≈⟨ acac ⟩
    a • c • a • c
      ≈⟨ cong (sym eq171ᶜ) (cong (sym eq170ᵇ) (cong (sym eq171ᶜ) (sym eq170ᵇ))) ⟩
    (G • °G) • (B • °B) • (G • °G) • (B • °B)
      ≈⟨ shuffle Γ (sym G-°G) (sym B-°G) (sym G-°B) (sym B-°B) ⟩
    (G • B • G • B) • (°G • °B • °G • °B)
      ≈⟨ sym (cong eq210 °ZX₃-form) ⟩
    ZX₃ • N₂.⟪ ZX₃ ⟫ ∎)

  ----------------------------------------------------------------------
  -- Inverses

  private
    °ZX°XZ : N₂.⟪ ZX₃ ⟫ • N₂.⟪ XZ₃ ⟫ ≈ ε
    °ZX°XZ = trans (sym (N₂.⟪⟫-• ZX₃ XZ₃)) (trans (N₂.⟪⟫-cong eq208′) N₂.⟪⟫-ε)

    KK′ : K • K′ ≈ ε
    KK′ = trans (sym (S₀₁.⟪⟫-• (N₂.⟪ ZX₃ ⟫) (N₂.⟪ XZ₃ ⟫))) (trans (S₀₁.⟪⟫-cong °ZX°XZ) S₀₁.⟪⟫-ε)

    K′K : K′ • K ≈ ε
    K′K = eq209

    KᵇKᵇ′ : Kᵇ • Kᵇ′ ≈ ε
    KᵇKᵇ′ = trans (sym (S₀₁.⟪⟫-• ZX₃ XZ₃)) (trans (S₀₁.⟪⟫-cong eq208′) S₀₁.⟪⟫-ε)

    N′N₀ : CCXZ₁₃ • CCZX₁₃ ≈ ε
    N′N₀ = trans (sym (S₂₃.⟪⟫-• (L₃ CCXZ) (L₃ CCZX))) (trans (S₂₃.⟪⟫-cong eq118) S₂₃.⟪⟫-ε)

    N′N : S₀₁.⟪ CCXZ₁₃ ⟫ • S₀₁.⟪ CCZX₁₃ ⟫ ≈ ε
    N′N = trans (sym (S₀₁.⟪⟫-• CCXZ₁₃ CCZX₁₃)) (trans (S₀₁.⟪⟫-cong N′N₀) S₀₁.⟪⟫-ε)

  ----------------------------------------------------------------------
  -- (221)–(226)

  -- (221): on wire 1, the white control on wire 2.
  eq221 : K • Kᵇ ≈ S₀₁.⟪ CCZX₁₃ ⟫
  eq221 = trans (sym (S₀₁.⟪⟫-• (N₂.⟪ ZX₃ ⟫) ZX₃)) (S₀₁.⟪⟫-cong merge₀)

  eq221′ : Kᵇ • K ≈ S₀₁.⟪ CCZX₁₃ ⟫
  eq221′ = trans (sym (S₀₁.⟪⟫-• ZX₃ (N₂.⟪ ZX₃ ⟫))) (S₀₁.⟪⟫-cong merge₀′)

  -- (222): the inverses, in the other order.
  eq222 : Kᵇ′ • K′ ≈ S₀₁.⟪ CCXZ₁₃ ⟫
  eq222 = inv-unique (unwrap′ KᵇKᵇ′ KK′) N′N eq221

  -- (223): on wire 0, the white control on wire 3.
  private
    S₂₃-°ZX₃ : S₂₃.⟪ N₂.⟪ ZX₃ ⟫ ⟫ ≈ N₃.⟪ ZX₃ ⟫
    S₂₃-°ZX₃ = S₂₃.⟪⟫-•₃ S₂₃-X₂ S₂₃-ZX₃ S₂₃-X₂

  eq223 : N₃.⟪ ZX₃ ⟫ • ZX₃ ≈ CCZX
  eq223 = S₂₃.⟪⟫-≈ merge₀ (S₂₃.⟪⟫-•₂ S₂₃-°ZX₃ S₂₃-ZX₃) (S₂₃.⟪⟫-⟪⟫ (L₃ CCZX))

  eq223′ : ZX₃ • N₃.⟪ ZX₃ ⟫ ≈ CCZX
  eq223′ = S₂₃.⟪⟫-≈ merge₀′ (S₂₃.⟪⟫-•₂ S₂₃-ZX₃ S₂₃-°ZX₃) (S₂₃.⟪⟫-⟪⟫ (L₃ CCZX))

  -- (224)
  eq224 : N₃.⟪ XZ₃ ⟫ • XZ₃ ≈ CCXZ
  eq224 = inv-unique (unwrap′ N₃-inv eq208′) eq118 eq223′
    where
    N₃-inv : N₃.⟪ ZX₃ ⟫ • N₃.⟪ XZ₃ ⟫ ≈ ε
    N₃-inv = trans (sym (N₃.⟪⟫-• ZX₃ XZ₃)) (trans (N₃.⟪⟫-cong eq208′) N₃.⟪⟫-ε)

  -- (225)
  eq225 : K′ • S₀₁.⟪ CCZX₁₃ ⟫ ≈ Kᵇ
  eq225 = begin
    K′ • S₀₁.⟪ CCZX₁₃ ⟫     ≈⟨ back _ (sym eq221) ⟩
    K′ • K • Kᵇ             ≈⟨ sym assoc ⟩
    (K′ • K) • Kᵇ           ≈⟨ trans (front _ K′K) left-unit ⟩
    Kᵇ ∎

  -- (226)
  eq226 : S₀₁.⟪ CCXZ₁₃ ⟫ • K ≈ Kᵇ′
  eq226 = begin
    S₀₁.⟪ CCXZ₁₃ ⟫ • K      ≈⟨ front _ (sym eq222) ⟩
    (Kᵇ′ • K′) • K          ≈⟨ assoc ⟩
    Kᵇ′ • K′ • K            ≈⟨ trans (back _ K′K) right-unit ⟩
    Kᵇ′ ∎
