------------------------------------------------------------------------
-- Presentations of groups
--
-- P ⊗ P on four wires, and the triply controlled rotation between P ⊗ P
-- (Clément, Lemma D.5, Equation (246), and the forms behind (242)–(245))
--
-- (246): P ⊗ P on the pairs 2 3 and 0 1 is P ⊗ P on the pairs 1 3 and
-- 0 2 — two Klein four-groups, on the wires 1 2 3 and 0 1 2, sharing
-- P ⊗ P on 1 2.
--
-- The triply controlled ZX on wire 0 is G B G B, (210), with G the H gate
-- H(0, 3; 1, 2) and B the box on wire 1.  Between P ⊗ P on the wires 0 1
-- the box becomes the H gate H(0, 1; 2, 3), (112), and the H gate, itself
-- a box between P ⊗ P on the wires 0 3, becomes the H gate H(1, 3; 0, 2)
-- by the Klein four-group on the wires 0 1 3: the rotation between P ⊗ P
-- is again a word of two H gates (`Aᴾ-form`).  With a white control on
-- wire 1 the rotation is, by the merge on wire 1, the doubly controlled
-- ZX from the wires 2 3 times the inverse of the black one, and between
-- P ⊗ P the former is turned over, (174) (`Aᴾ-white`).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.FourQubit.PForms
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Bool using (Bool ; true ; false ; not)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Auxiliary complete₂ complete₃
  using (CZ₃₀ ; CZ₃₀-P)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations complete₂ complete₃
  using (box₃′ ; CCZX₂₃ ; CCXZ₂₃ ; eq174)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Colours complete₂ complete₃
  using (module N₃ ; L₃-top)
open import Examples.Groups.Real-Clifford+CH.FourQubit.ControlledH complete₂ complete₃
  using (ΛH₂′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Permutations complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.HGates2 complete₂ complete₃
  using (PP₁₂ ; PP₀₂ ; PP₁₂² ; PP₀₂² ; PP-triangle₂)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Rotations3 complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.FourQubit.Merges complete₂ complete₃
  using (CCZX₁₃ ; merge₀ ; merge₀′)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Families2 complete₂ complete₃
  using (N₁ᵇ ; N₃ᵇ ; rot ; A₂₄₁)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (module N₁ ; module N₂ ; eq117 ; eq118 ; eq130)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- (246)

PP₂₃ : Circuit (₄₊ n)
PP₂₃ = P₂₃ PP

PP₂₃² : (₄₊ n) ⊢ PP₂₃ • PP₂₃ ≈ ε
PP₂₃² = lemma-cong↑ (U (PP • PP)) ε (U-sem (PP • PP) ε Eq.refl)

-- (130) one wire up.
PP-triangle₃ : (₄₊ n) ⊢ PP₁₂ • PP₂₃ ≈ PP₁₃
PP-triangle₃ {n} = trans (lemma-cong↑ (PP ↓ • PP ↑) (Ex ↑ • PP ↓ • Ex ↑) eq130) (U-S₂₃ PP)
  where open Tools ((₄₊ n) VRel,_===_)

eq246 : (₄₊ n) ⊢ PP₂₃ • PP₀₁ ≈ PP₁₃ • PP₀₂
eq246 {n} = begin
  PP₂₃ • PP₀₁
    ≈⟨ cong (sym (klein-ba Γ PP₁₂² PP₁₃² PP₂₃² PP-triangle₃)) m ⟩
  (PP₁₃ • PP₁₂) • (PP₁₂ • PP₀₂)
    ≈⟨ by-passoc ((□ • □) • (□ • □)) (□ • (□ • □) • □) Eq.refl ⟩
  PP₁₃ • (PP₁₂ • PP₁₂) • PP₀₂
    ≈⟨ back _ (trans (front _ PP₁₂²) left-unit) ⟩
  PP₁₃ • PP₀₂ ∎
  where
  Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  m : (₄₊ n) ⊢ PP₀₁ ≈ PP₁₂ • PP₀₂
  m = begin
    PP₀₁                      ≈⟨ sym left-unit ⟩
    ε • PP₀₁                  ≈⟨ front _ (sym PP₁₂²) ⟩
    (PP₁₂ • PP₁₂) • PP₀₁      ≈⟨ assoc ⟩
    PP₁₂ • PP₁₂ • PP₀₁        ≈⟨ back _ (klein-ca Γ PP₀₁² PP₀₂² PP₁₂² PP-triangle₂) ⟩
    PP₁₂ • PP₀₂ ∎

------------------------------------------------------------------------
-- The triply controlled rotation between P ⊗ P on the wires 0 1

module Aj {n : ℕ} = Conj {₄₊ n} PP₀₁ PP₀₁²

-- The first gate of (242) and (243).
Aᴾ : Bool → Bool → Bool → Circuit (₄₊ n)
Aᴾ α β a = Aj.⟪ A₂₄₁ α β a ⟫

module _ {n : ℕ} where
  private
    Γ = (₄₊ n) VRel,_===_
  open Tools Γ
  open Alg Γ

  private
    G G′ P B : Circuit (₄₊ n)
    G  = ΛH₂′
    G′ = S₀₁.⟪ ΛH₂′ ⟫
    P  = ΛH₀₁
    B  = box₃′

  -- The H gate with its box wire on wire 3: its H moves to wire 1.
  Aj-G : Aj.⟪ G ⟫ ≈ G′
  Aj-G = begin
    PP₀₁ • G • PP₀₁
      ≈⟨ back _ (front _ ΛH₂′-PP) ⟩
    PP₀₁ • (PP₀₃ • box₃‴ • PP₀₃) • PP₀₁
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
    (PP₀₁ • PP₀₃) • box₃‴ • (PP₀₃ • PP₀₁)
      ≈⟨ cong (klein-ab Γ PP₀₁² PP-triangle)
              (back _ (klein-ba Γ PP₀₁² PP₀₃² PP₁₃² PP-triangle)) ⟩
    PP₁₃ • box₃‴ • PP₁₃
      ≈⟨ sym S₀₁-ΛH₂′-PP ⟩
    G′ ∎

  -- The box on wire 1 becomes the H gate on the wires 0 1.
  Aj-B : Aj.⟪ B ⟫ ≈ P
  Aj-B = sym ΛH₀₁-PP

  -- All black.
  Aᴾ-form : Aᴾ true true true ≈ G′ • P • G′ • P
  Aᴾ-form = trans (Aj.⟪⟫-cong eq210) (Aj.⟪⟫-•₄ Aj-G Aj-B Aj-G Aj-B)

  ----------------------------------------------------------------------
  -- A white control on wire 1

  private
    -- The merge (221) under the middle swap: on wire 1.
    S₁₂-°ZX₃ : S₁₂.⟪ N₂.⟪ ZX₃ ⟫ ⟫ ≈ N₁.⟪ ZX₃ ⟫
    S₁₂-°ZX₃ = S₁₂.⟪⟫-•₃ S₁₂-X₂ S₁₂-ZX₃ S₁₂-X₂

    S₁₂-N : S₁₂.⟪ CCZX₁₃ ⟫ ≈ CCZX₂₃
    S₁₂-N = begin
      S₁₂.⟪ CCZX₁₃ ⟫
        ≈⟨ S₁₂.⟪⟫-cong (S₂₃.⟪⟫-•₄ (L-S₂₃ CH) (O-S₂₃ CZ) (L-S₂₃ CH) (O-S₂₃ CZ)) ⟩
      S₁₂.⟪ CH ↓ • P₀₃ CZ • CH ↓ • P₀₃ CZ ⟫
        ≈⟨ S₁₂.⟪⟫-•₄ (O-L CH) (S₁₂-P₀₃ CZ) (O-L CH) (S₁₂-P₀₃ CZ) ⟩
      CH₂₀ • P₀₃ CZ • CH₂₀ • P₀₃ CZ
        ≈⟨ sym (S₀₁.⟪⟫-•₄ refl refl refl refl) ⟩
      CCZX₂₃ ∎

  -- The middle swap on the doubly controlled ZX from the wires 1 3.
  S₁₂-CCZX₁₃ : S₁₂.⟪ CCZX₁₃ ⟫ ≈ CCZX₂₃
  S₁₂-CCZX₁₃ = S₁₂-N

  merge₁ : N₁.⟪ ZX₃ ⟫ • ZX₃ ≈ CCZX₂₃
  merge₁ = S₁₂.⟪⟫-≈ merge₀ (S₁₂.⟪⟫-•₂ S₁₂-°ZX₃ S₁₂-ZX₃) S₁₂-N

  merge₁′ : ZX₃ • N₁.⟪ ZX₃ ⟫ ≈ CCZX₂₃
  merge₁′ = S₁₂.⟪⟫-≈ merge₀′ (S₁₂.⟪⟫-•₂ S₁₂-ZX₃ S₁₂-°ZX₃) S₁₂-N

  -- The doubly controlled ZX from the wires 2 3 between P ⊗ P: (174)
  -- under the lower swap.
  Aj-CCZX₂₃ : Aj.⟪ CCZX₂₃ ⟫ ≈ CCXZ₂₃
  Aj-CCZX₂₃ = trans (sym assoc) (trans (front _ e) (cancelʳ _ PP₀₁²))
    where
    S-PP : S₀₁.⟪ PP ↓ ⟫ ≈ PP ↓
    S-PP = L-sem (Ex • PP • Ex) PP Eq.refl
    e : PP₀₁ • CCZX₂₃ ≈ CCXZ₂₃ • PP₀₁
    e = S₀₁.⟪⟫-≈ eq174 (S₀₁.⟪⟫-•₂ S-PP refl) (S₀₁.⟪⟫-•₂ refl S-PP)

  -- White on wire 1: the doubly controlled XZ times the black XZ.
  Aᴾ-white : Aᴾ true false true ≈ CCXZ₂₃ • Aᴾ true true false
  Aᴾ-white = begin
    Aj.⟪ N₁.⟪ ZX₃ ⟫ ⟫
      ≈⟨ Aj.⟪⟫-cong N₁ZX₃-form ⟩
    Aj.⟪ CCZX₂₃ • XZ₃ ⟫
      ≈⟨ Aj.⟪⟫-•₂ Aj-CCZX₂₃ refl ⟩
    CCXZ₂₃ • Aj.⟪ XZ₃ ⟫ ∎
    where
    N₁ZX₃-form : N₁.⟪ ZX₃ ⟫ ≈ CCZX₂₃ • XZ₃
    N₁ZX₃-form = begin
      N₁.⟪ ZX₃ ⟫                    ≈⟨ sym right-unit ⟩
      N₁.⟪ ZX₃ ⟫ • ε                ≈⟨ back _ (sym eq208′) ⟩
      N₁.⟪ ZX₃ ⟫ • ZX₃ • XZ₃        ≈⟨ sym assoc ⟩
      (N₁.⟪ ZX₃ ⟫ • ZX₃) • XZ₃      ≈⟨ front _ merge₁ ⟩
      CCZX₂₃ • XZ₃ ∎

  ----------------------------------------------------------------------
  -- Inverses, and X on wire 3

  Aᴾ-inv : ∀ α β → Aᴾ α β true • Aᴾ α β false ≈ ε
  Aᴾ-inv α β = trans (sym (Aj.⟪⟫-• (A₂₄₁ α β true) (A₂₄₁ α β false)))
                     (trans (Aj.⟪⟫-cong (A-inv α β)) Aj.⟪⟫-ε)
    where
    A-inv₁ : ∀ β → A₂₄₁ true β true • A₂₄₁ true β false ≈ ε
    A-inv₁ true  = eq208′
    A-inv₁ false = trans (sym (N₁.⟪⟫-• ZX₃ XZ₃)) (trans (N₁.⟪⟫-cong eq208′) N₁.⟪⟫-ε)
    A-inv : ∀ α β → A₂₄₁ α β true • A₂₄₁ α β false ≈ ε
    A-inv true  β = A-inv₁ β
    A-inv false β = trans (sym (N₃.⟪⟫-• _ _)) (trans (N₃.⟪⟫-cong (A-inv₁ β)) N₃.⟪⟫-ε)

  Aᴾ-inv′ : ∀ α β → Aᴾ α β false • Aᴾ α β true ≈ ε
  Aᴾ-inv′ α β = trans (sym (Aj.⟪⟫-• (A₂₄₁ α β false) (A₂₄₁ α β true)))
                      (trans (Aj.⟪⟫-cong (A-inv′ α β)) Aj.⟪⟫-ε)
    where
    A-inv₁′ : ∀ β → A₂₄₁ true β false • A₂₄₁ true β true ≈ ε
    A-inv₁′ true  = eq208
    A-inv₁′ false = trans (sym (N₁.⟪⟫-• XZ₃ ZX₃)) (trans (N₁.⟪⟫-cong eq208) N₁.⟪⟫-ε)
    A-inv′ : ∀ α β → A₂₄₁ α β false • A₂₄₁ α β true ≈ ε
    A-inv′ true  β = A-inv₁′ β
    A-inv′ false β = trans (sym (N₃.⟪⟫-• _ _)) (trans (N₃.⟪⟫-cong (A-inv₁′ β)) N₃.⟪⟫-ε)

  N₃-PP₀₁ : N₃.⟪ PP₀₁ ⟫ ≈ PP₀₁
  N₃-PP₀₁ = N₃.⟪⟫-fix (sym (L₃-top (L₀ PP) X))

  -- X on wire 3 makes the control there white.
  N₃-Aᴾ : ∀ β a → N₃.⟪ Aᴾ true β a ⟫ ≈ Aᴾ false β a
  N₃-Aᴾ β a = N₃.⟪⟫-•₃ N₃-PP₀₁ refl N₃-PP₀₁
