------------------------------------------------------------------------
-- Presentations of groups
--
-- P ⊗ P on the target of a rotation and its idle wire turns it over
-- (Clément, Lemma D.15, Equation (360))
--
-- At width 4 + k, with the ZX and XZ one wire up (target 1, wire 0
-- idle):  PP ↓ • ΛXZ (2 + k) ↑ • PP ↓ ≈ ΛZX (2 + k) ↑  (`eq360`).
--
-- In ZXPass's frame.  One width down the XZ is, by a step decided on
-- the controlled forms of CForm (`sem-d′`, the mirror of SemZX.sem-d),
-- a word CZ CH ZX CH CZ XZ B HG in the CZ and CH on the wires 1 2, the
-- ZX and XZ on wire 2 and the box and H gate with their box wire on
-- wire 2.  P ⊗ P on the wires 0 1 exchanges the CZ and the CH (three
-- wires), passes the rotations on wire 2, and, once the box wire is
-- moved to wire 0 ((274), (276): ZXPass's moves), exchanges the box
-- and the H gate — which is SemZX.sem-d, the ZX.  Checked numerically
-- first (scratchpad t360.py).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.ZX360
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Figure13 complete₂ using (eq111)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.CForm using (CF ; cf-• ; cf-~)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemZX
  using (B₁₀ ; HG₀₁ ; ZX₁ ; XZ₁ ; module Forms ; sem-d)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place ; low-comm)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete ; box274 ; box276)

------------------------------------------------------------------------
-- The step one width down: the XZ as a word, the mirror of sem-d

module _ (k : ℕ) where
  open Forms k

  private
    xz₀ : CF {3} {k} (ΛXZ (₂₊ k))
    xz₀ = cf-• b₁₀ (cf-• ch (cf-• b₁₀ ch))

  sem-d′ : ⟦ CZ • CH • ZX₁ k • CH • CZ • XZ₁ k • B₁₀ k • HG₀₁ k ⟧ ~ ⟦ ΛXZ (₂₊ k) ⟧
  sem-d′ = cf-~ (cf-• cz (cf-• ch (cf-• zx₁ (cf-• ch (cf-• cz (cf-• xz₁ (cf-• b₁₀ hg₀₁)))))))
                xz₀ Eq.refl Eq.refl

  -- The ZX and XZ on wire 0 are inverse.
  sem-zx-xz : ⟦ ΛZX (₂₊ k) • ΛXZ (₂₊ k) ⟧ ~ ⟦ ε ⟧
  sem-zx-xz = cf-~ (cf-• zx₀ xz₀) eps Eq.refl Eq.refl

  sem-xz-zx : ⟦ ΛXZ (₂₊ k) • ΛZX (₂₊ k) ⟧ ~ ⟦ ε ⟧
  sem-xz-zx = cf-~ (cf-• xz₀ zx₀) eps Eq.refl Eq.refl

------------------------------------------------------------------------
-- (360)

module _ (k : ℕ) (complete : Complete k) where

  private
    open Tools ((₄₊ k) VRel,_===_)

    up : ∀ {u v : Circuit (₃₊ k)} → ⟦ u ⟧ ~ ⟦ v ⟧ → (₄₊ k) ⊢ u ↑ ≈ v ↑
    up {u} {v} e = lemma-cong↑ u v (complete e)

    Λ↑ B₂₁ HG₁₂ ZX₂ XZ₂ B₀₁ HG₁₀ PP₀₂ : Circuit (₄₊ k)
    Λ↑   = Λ□ (₂₊ k) ↑
    B₂₁  = B₁₀ k ↑
    HG₁₂ = HG₀₁ k ↑
    ZX₂  = ZX₁ k ↑
    XZ₂  = XZ₁ k ↑
    B₀₁  = place 2 (Λ□ (₂₊ k))
    HG₁₀ = PP ↓ • B₀₁ • PP ↓
    PP₀₂ = Ex ↑ • PP ↓ • Ex ↑

    Ex↑² : (₄₊ k) ⊢ Ex ↑ • Ex ↑ ≈ ε
    Ex↑² = lemma-cong↑ (Ex • Ex) ε Ex²

    -- Moving the box wire of B₂₁ and HG₁₂ from wire 2 to wire 0
    -- (ZXPass's moves).
    move-B : (₄₊ k) ⊢ B₂₁ ≈ B₀₁
    move-B = begin
      Ex ↑ • Λ↑ • Ex ↑
        ≈⟨ back _ (front _ (sym (box274 k complete))) ⟩
      Ex ↑ • (Ex ↓ • Λ↑ • Ex ↓) • Ex ↑
        ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (Ex ↑ • Ex ↓) • Λ↑ • (Ex ↓ • Ex ↑)
        ≈⟨ cong (front _ (sym left-unit)) (back _ (back _ (sym right-unit))) ⟩
      ((ε • Ex ↑) • Ex ↓) • Λ↑ • (Ex ↓ • (Ex ↑ • ε)) ∎

    pp-B : (₄₊ k) ⊢ PP₀₂ • B₂₁ • PP₀₂ ≈ B₂₁
    pp-B = begin
      (Ex ↑ • PP ↓ • Ex ↑) • (Ex ↑ • Λ↑ • Ex ↑) • (Ex ↑ • PP ↓ • Ex ↑)
        ≈⟨ by-passoc ((□ • □ • □) • (□ • □ • □) • (□ • □ • □))
                     (□ • □ • (□ • □) • □ • (□ • □) • □ • □) Eq.refl ⟩
      Ex ↑ • PP ↓ • (Ex ↑ • Ex ↑) • Λ↑ • (Ex ↑ • Ex ↑) • PP ↓ • Ex ↑
        ≈⟨ back _ (back _ (cong Ex↑² (back _ (front _ Ex↑²)))) ⟩
      Ex ↑ • PP ↓ • ε • Λ↑ • ε • PP ↓ • Ex ↑
        ≈⟨ back _ (back _ (trans left-unit (back _ left-unit))) ⟩
      Ex ↑ • PP ↓ • Λ↑ • PP ↓ • Ex ↑
        ≈⟨ back _ (by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl) ⟩
      Ex ↑ • (PP ↓ • Λ↑ • PP ↓) • Ex ↑
        ≈⟨ back _ (front _ (box276 k complete)) ⟩
      Ex ↑ • Λ↑ • Ex ↑ ∎

    klein₁ : (₄₊ k) ⊢ PP ↑ • PP₀₂ ≈ PP ↓
    klein₁ = L₃-sem (PP ↑ • Ex ↑ • PP ↓ • Ex ↑) PP Eq.refl

    klein₂ : (₄₊ k) ⊢ PP₀₂ • PP ↑ ≈ PP ↓
    klein₂ = L₃-sem ((Ex ↑ • PP ↓ • Ex ↑) • PP ↑) PP Eq.refl

    move-HG : (₄₊ k) ⊢ HG₁₂ ≈ HG₁₀
    move-HG = begin
      PP ↑ • B₂₁ • PP ↑                          ≈⟨ back _ (front _ (sym pp-B)) ⟩
      PP ↑ • (PP₀₂ • B₂₁ • PP₀₂) • PP ↑          ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (PP ↑ • PP₀₂) • B₂₁ • (PP₀₂ • PP ↑)        ≈⟨ cong klein₁ (back _ klein₂) ⟩
      PP ↓ • B₂₁ • PP ↓                          ≈⟨ back _ (front _ move-B) ⟩
      PP ↓ • B₀₁ • PP ↓ ∎

    -- P ⊗ P on the wires 0 1: the conjugation, and what it does to the
    -- letters.
    module P = Conj {₄₊ k} (PP ↓) eq111

    P-CZ↑ : P.⟪ CZ ↑ ⟫ ≈ CH ↑
    P-CZ↑ = L₃-sem (PP • CZ ↑ • PP) (CH ↑) Eq.refl

    P-CH↑ : P.⟪ CH ↑ ⟫ ≈ CZ ↑
    P-CH↑ = L₃-sem (PP • CH ↑ • PP) (CZ ↑) Eq.refl

    P-ZX₂ : P.⟪ ZX₂ ⟫ ≈ ZX₂
    P-ZX₂ = P.⟪⟫-fix (low-comm PP (ΛZX (₁₊ k)))

    P-XZ₂ : P.⟪ XZ₂ ⟫ ≈ XZ₂
    P-XZ₂ = P.⟪⟫-fix (low-comm PP (ΛXZ (₁₊ k)))

    P-B : P.⟪ B₂₁ ⟫ ≈ HG₁₂
    P-B = trans (P.⟪⟫-cong move-B) (sym move-HG)

    P-HG : P.⟪ HG₁₂ ⟫ ≈ B₂₁
    P-HG = trans (P.⟪⟫-cong move-HG) (trans (P.⟪⟫-⟪⟫ B₀₁) (sym move-B))

  eq360 : PP ↓ • ΛXZ (₂₊ k) ↑ • PP ↓ ≈ ΛZX (₂₊ k) ↑
  eq360 = begin
    P.⟪ ΛXZ (₂₊ k) ↑ ⟫
      ≈⟨ P.⟪⟫-cong (sym (up (sem-d′ k))) ⟩
    P.⟪ CZ ↑ • CH ↑ • ZX₂ • CH ↑ • CZ ↑ • XZ₂ • B₂₁ • HG₁₂ ⟫
      ≈⟨ P.⟪⟫-•₄ P-CZ↑ P-CH↑ P-ZX₂ (P.⟪⟫-•₅ P-CH↑ P-CZ↑ P-XZ₂ P-B P-HG) ⟩
    CH ↑ • CZ ↑ • ZX₂ • CZ ↑ • CH ↑ • XZ₂ • HG₁₂ • B₂₁
      ≈⟨ up (sem-d k) ⟩
    ΛZX (₂₊ k) ↑ ∎

  eq360′ : PP ↓ • ΛZX (₂₊ k) ↑ • PP ↓ ≈ ΛXZ (₂₊ k) ↑
  eq360′ = conj-sym eq111 eq360
