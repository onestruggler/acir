------------------------------------------------------------------------
-- Presentations of groups
--
-- The multi-controlled H on any number of wires (Clément, Lemma D.8,
-- Equations (281), (303)), and the box against the lower CZ
--
-- ΛH (k + 2) is the box on k + 4 wires between P ⊗ P on the wires 0 1:
-- its H on wire 1, its box wire on wire 0, its controls on the wires
-- 2 … k + 3.  Between P ⊗ P, H on either of the wires 0 1 is Z there,
-- (113), so:
--
--   (281)  H on the H wire passes the gate: Z on the control on wire 1
--          passes the box, (270);
--   (303)  H on the box wire passes the gate: Z on the box wire passes
--          the box, the schema (19).
--
-- The box also passes the CZ of its box wire and the control on wire 1 —
-- (273) for the other of the two lowest controls: that CZ turns W and V
-- into each other, (12) in the form `K-W`, and passes B, by induction
-- under the transposition that places B; then `box-pass` with the flip
-- V B W = W B V, which is (286) with one B cancelled.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.HGate
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Fin using (Fin ; zero ; suc)
open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; WRel ; [_]ʷ ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Presentation.GroupLike using (module Basis-Change)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation
  using (module Tools ; module Conj ; ax ; CZ² ; Ex²)
open import Examples.Groups.Real-Clifford+CH.MultiControlled using (ΛH)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Auxiliary complete₂
  using (K-W ; K-V)
import Examples.Groups.Real-Clifford+CH.WordAlgebra as WordAlgebra

private
  variable
    n : ℕ

  module Alg {X : Set} (Γ : WRel X) = WordAlgebra Γ

------------------------------------------------------------------------
-- (281), (303)

private
  -- Between P ⊗ P, H is Z: (113).
  H₀-PP : (₃₊ n) ⊢ H ↓ • PP ↓ ≈ PP ↓ • Z ↓
  H₀-PP = L-sem (H ↓ • PP) (PP • Z ↓) Eq.refl

  Z₀-PP : (₃₊ n) ⊢ Z ↓ • PP ↓ ≈ PP ↓ • H ↓
  Z₀-PP = L-sem (Z ↓ • PP) (PP • H ↓) Eq.refl

  H₁-PP : (₃₊ n) ⊢ H ↑ • PP ↓ ≈ PP ↓ • Z ↑
  H₁-PP = L-sem (H ↑ • PP) (PP • Z ↑) Eq.refl

  Z₁-PP : (₃₊ n) ⊢ Z ↑ • PP ↓ ≈ PP ↓ • H ↑
  Z₁-PP = L-sem (Z ↑ • PP) (PP • H ↑) Eq.refl

module _ {X : Set} (Γ : WRel X) where
  open Tools Γ

  -- h is z between p, and z passes q: h passes p q p.
  through : ∀ {h z p q : Word X} → h • p ≈ p • z → z • p ≈ p • h → z • q ≈ q • z →
            h • (p • q • p) ≈ (p • q • p) • h
  through {h} {z} {p} {q} hp zp zq = begin
    h • (p • q • p)     ≈⟨ sym assoc ⟩
    (h • p) • q • p     ≈⟨ front _ hp ⟩
    (p • z) • q • p     ≈⟨ by-passoc ((□ • □) • □ • □) (□ • (□ • □) • □) Eq.refl ⟩
    p • (z • q) • p     ≈⟨ back _ (front _ zq) ⟩
    p • (q • z) • p     ≈⟨ by-passoc (□ • (□ • □) • □) (□ • □ • (□ • □)) Eq.refl ⟩
    p • q • (z • p)     ≈⟨ back _ (back _ zp) ⟩
    p • q • (p • h)     ≈⟨ by-passoc (□ • □ • (□ • □)) ((□ • □ • □) • □) Eq.refl ⟩
    (p • q • p) • h ∎

-- (281): H on the H wire.
eq281 : ∀ k → (₄₊ k) ⊢ H ↑ • ΛH (₂₊ k) ≈ ΛH (₂₊ k) • H ↑
eq281 k = through ((₄₊ k) VRel,_===_) H₁-PP Z₁-PP (eq270 (₃₊ k) zero)

-- (303): H on the box wire.
eq303 : ∀ k → (₄₊ k) ⊢ H ↓ • ΛH (₂₊ k) ≈ ΛH (₂₊ k) • H ↓
eq303 k = through ((₄₊ k) VRel,_===_) H₀-PP Z₀-PP (box-Z₀ (₁₊ k))

------------------------------------------------------------------------
-- The box and the CZ of its box wire and the control on wire 1

private
  τ₀₂² : (₄₊ n) ⊢ τ₀₂ • τ₀₂ ≈ ε
  τ₀₂² {n} = conj-invol Ex² (lemma-cong↑ (Ex • Ex) ε Ex²)
    where open Tools ((₄₊ n) VRel,_===_)

  module T {n : ℕ} = Conj {₄₊ n} τ₀₂ τ₀₂²

  T-CZ↓ : (₄₊ n) ⊢ T.⟪ CZ ↓ ⟫ ≈ CZ ↑
  T-CZ↓ = L₃-sem (τ₀₂ • CZ ↓ • τ₀₂) (CZ ↑) Eq.refl

-- (286) with one B cancelled.
flip□ : ∀ k → (₄₊ k) ⊢ CCXZ • B□ k • CCZX ≈ CCZX • B□ k • CCXZ
flip□ k = bbc ε (B□ k) (back ε (begin
  (CCXZ • B□ k • CCZX) • B□ k     ≈⟨ by-passoc ((□ • □ • □) • □) (□ • □ • □ • □) Eq.refl ⟩
  CCXZ • B□ k • CCZX • B□ k       ≈⟨ sym (eq286 k) ⟩
  CCZX • B□ k • CCXZ • B□ k       ≈⟨ by-passoc (□ • □ • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
  (CCZX • B□ k • CCXZ) • B□ k ∎))
  where
  Γ = (₄₊ k) VRel,_===_
  open Tools Γ
  open Basis-Change (Gen (₄₊ k)) Γ grouplike using (bbc)

box-CZ↓ : ∀ k → (₃₊ k) ⊢ CZ ↓ • Λ□ (₂₊ k) ≈ Λ□ (₂₊ k) • CZ ↓
box-CZ↓ 0 = sym (ax comm-CZ↑-CZ↓)
  where open Tools (3 VRel,_===_)
box-CZ↓ (₁₊ k) = box-pass q-W q-V q-B (flip□ k)
  where
  Γ = (₄₊ k) VRel,_===_
  open Tools Γ
  open Alg Γ

  conj-pass : ∀ {x w w′ : Circuit (₄₊ k)} → x • x ≈ ε → x • w • x ≈ w′ → x • w ≈ w′ • x
  conj-pass {x} {w} {w′} xx e = begin
    x • w                 ≈⟨ sym right-unit ⟩
    (x • w) • ε           ≈⟨ back _ (sym xx) ⟩
    (x • w) • x • x       ≈⟨ by-passoc ((□ • □) • □ • □) ((□ • □ • □) • □) Eq.refl ⟩
    (x • w • x) • x       ≈⟨ front _ e ⟩
    w′ • x ∎

  q-W : CZ ↓ • CCZX ≈ CCXZ • CZ ↓
  q-W = conj-pass CZ² K-W

  q-V : CZ ↓ • CCXZ ≈ CCZX • CZ ↓
  q-V = conj-pass CZ² K-V

  q-B : CZ ↓ • B□ k ≈ B□ k • CZ ↓
  q-B = T.⟪⟫-≈ (lemma-cong↑ (CZ ↓ • Λ□ (₂₊ k)) (Λ□ (₂₊ k) • CZ ↓) (box-CZ↓ k))
               (T.⟪⟫-•₂ (trans (T.⟪⟫-cong (sym T-CZ↓)) (T.⟪⟫-⟪⟫ (CZ ↓))) refl)
               (T.⟪⟫-•₂ refl (trans (T.⟪⟫-cong (sym T-CZ↓)) (T.⟪⟫-⟪⟫ (CZ ↓))))
