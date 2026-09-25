------------------------------------------------------------------------
-- Presentations of groups
--
-- The box passes the doubly controlled ZX on its box wire from its
-- first control and an idle wire (Clément, Lemma D.8, Equation (287))
--
-- At width 4 + k the box B₀₁ has its box wire on wire 0, controls on
-- wire 1 and the wires 3 …, and wire 2 idle; the ZX is CCZX, on wire 0
-- from the wires 1 2.  The paper's proof, factor by factor:
-- CCZX = CH • CZ₂₀ • CH • CZ₂₀, the box passes the CH from its control
-- onto its box wire — (298) one width down, here completeness one width
-- down with wire 2 idle — and the CZ between its box wire and the idle
-- wire, (272), which is Keystone's B□-CZ↑ under the swap of the wires
-- 0 1.
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxZX
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools ; module Conj ; Ex²)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.SemKey using (sem-box-CH)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Place using (place ; place-low ; cyc ; cyc⁻¹)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃
  using (B□-CZ↑ ; commute-placed)

-- The box on wire 0 with controls on wire 1 and the wires 3 …, wire 2
-- idle.
B₀₁ : ∀ k → Circuit (₄₊ k)
B₀₁ k = place 2 (Λ□ (₂₊ k))

-- (287)
Eq287 : ℕ → Set
Eq287 k = (₄₊ k) ⊢ B₀₁ k • CCZX ≈ CCZX • B₀₁ k

module _ (k : ℕ) (complete : Complete k) where

  private
    open Tools ((₄₊ k) VRel,_===_)
    module X = Conj {₄₊ k} (Ex ↓) Ex²

    Λ↑ : Circuit (₄₊ k)
    Λ↑ = Λ□ (₂₊ k) ↑

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

    -- The swap of the wires 0 1 carries B□ k to B₀₁ k.
    net₁ : (₄₊ k) ⊢ Ex ↓ • τ₀₂ ≈ cyc⁻¹ 2
    net₁ = L₃-sem (Ex • τ₀₂) (cyc⁻¹ 2) Eq.refl

    net₂ : (₄₊ k) ⊢ τ₀₂ • Ex ↓ ≈ cyc 2
    net₂ = L₃-sem (τ₀₂ • Ex) (cyc 2) Eq.refl

    conj-B : (₄₊ k) ⊢ X.⟪ B□ k ⟫ ≈ B₀₁ k
    conj-B = begin
      Ex ↓ • (τ₀₂ • Λ↑ • τ₀₂) • Ex ↓     ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • (□ • □)) Eq.refl ⟩
      (Ex ↓ • τ₀₂) • Λ↑ • (τ₀₂ • Ex ↓)   ≈⟨ cong net₁ (back _ net₂) ⟩
      cyc⁻¹ 2 • Λ↑ • cyc 2 ∎

    box-CH : (₄₊ k) ⊢ B₀₁ k • CH ≈ CH • B₀₁ k
    box-CH = commute-placed k complete {X = Λ□ (₂₊ k)} {Y = CH} refl (place-low 2 CH) (sem-box-CH k)

    box-CZ₂₀ : (₄₊ k) ⊢ B₀₁ k • CZ₂₀ ≈ CZ₂₀ • B₀₁ k
    box-CZ₂₀ = X.⟪⟫-≈ (B□-CZ↑ k complete) (X.⟪⟫-•₂ conj-B refl) (X.⟪⟫-•₂ refl conj-B)

  eq287 : Eq287 k
  eq287 = pass box-CH (pass box-CZ₂₀ (pass box-CH box-CZ₂₀))
