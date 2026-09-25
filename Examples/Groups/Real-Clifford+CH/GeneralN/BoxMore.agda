------------------------------------------------------------------------
-- Presentations of groups
--
-- The box in its last B-form, and the box passing the singly controlled
-- ZX on its box wire (Clément, Lemma D.8, Equations (300) and (304))
--
-- (300), the box is B • W • B • V: that word is the inverse of the
-- B-form W • B • V • B, (269), B and the pair W, V being involutions
-- and inverse; and the box is its own inverse, (299).
--
-- (304), the box passes the ZX on its box wire from its first control:
-- that ZX is CH • Z • CH • Z on the wires 0 1 (two wires), the box
-- passes the CH by (298) and Z on its box wire by (19).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

open import Examples.Groups.Real-Clifford+CH.Semantics using (_~_)
open import Examples.Groups.Real-Clifford+CH.Syntactics
open import Examples.Groups.Real-Clifford+CH.Interpretation using (⟦_⟧)

module Examples.Groups.Real-Clifford+CH.GeneralN.BoxMore
  (complete₂ : ∀ {u v : Circuit 2} → ⟦ u ⟧ ~ ⟦ v ⟧ → 2 ⊢ u ≈ v)
  (complete₃ : ∀ {u v : Circuit 3} → ⟦ u ⟧ ~ ⟦ v ⟧ → 3 ⊢ u ≈ v)
  where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (Word ; ε ; _•_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.Real-Clifford+CH.TwoQubit.Conjugation using (module Tools)
open import Examples.Groups.Real-Clifford+CH.ThreeQubit.Blocks complete₂ using (L-sem)
open import Examples.Groups.Real-Clifford+CH.FourQubit.Blocks complete₂ complete₃ using (L₃-sem)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Box complete₂ complete₃ using (box-Z₀)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Sem using (B□)
open import Examples.Groups.Real-Clifford+CH.GeneralN.ZXPass complete₂ complete₃ using (Complete)
open import Examples.Groups.Real-Clifford+CH.GeneralN.Keystone complete₂ complete₃ using (B□²)
open import Examples.Groups.Real-Clifford+CH.GeneralN.BoxFull complete₂ complete₃ using (eq298 ; eq299)

Eq300 Eq304 : ℕ → Set
Eq300 k = (₄₊ k) ⊢ Λ□ (₃₊ k) ≈ B□ k • CCZX • B□ k • CCXZ
Eq304 k = (₄₊ k) ⊢ Λ□ (₃₊ k) • (ΛZX 1 ↓ᵏ (₂₊ k)) ≈ (ΛZX 1 ↓ᵏ (₂₊ k)) • Λ□ (₃₊ k)

module _ (k : ℕ) (complete : Complete k) where

  private
    open Tools ((₄₊ k) VRel,_===_)

    Λ W V B : Circuit (₄₊ k)
    Λ = Λ□ (₃₊ k)
    W = CCZX
    V = CCXZ
    B = B□ k

    V-W : (₄₊ k) ⊢ V • W ≈ ε
    V-W = L₃-sem (CCXZ • CCZX) ε Eq.refl

    W-V : (₄₊ k) ⊢ W • V ≈ ε
    W-V = L₃-sem (CCZX • CCXZ) ε Eq.refl

  eq300 : Eq300 k
  eq300 = sym (begin
    B • W • B • V                                   ≈⟨ sym right-unit ⟩
    (B • W • B • V) • ε                             ≈⟨ back _ (sym (eq299 k complete)) ⟩
    (B • W • B • V) • (W • B • V • B) • Λ           ≈⟨ by-passoc ((□ • □ • □ • □) • (□ • □ • □ • □) • □)
                                                                (□ • □ • □ • (□ • □) • □ • □ • □ • □) Eq.refl ⟩
    B • W • B • (V • W) • B • V • B • Λ             ≈⟨ back _ (back _ (back _ (front _ V-W))) ⟩
    B • W • B • ε • B • V • B • Λ                   ≈⟨ back _ (back _ (back _ left-unit)) ⟩
    B • W • B • B • V • B • Λ                       ≈⟨ back _ (back _ (sym assoc)) ⟩
    B • W • (B • B) • V • B • Λ                     ≈⟨ back _ (back _ (front _ (B□² k complete))) ⟩
    B • W • ε • V • B • Λ                           ≈⟨ back _ (back _ left-unit) ⟩
    B • W • V • B • Λ                               ≈⟨ back _ (sym assoc) ⟩
    B • (W • V) • B • Λ                             ≈⟨ back _ (front _ W-V) ⟩
    B • ε • B • Λ                                   ≈⟨ back _ left-unit ⟩
    B • B • Λ                                       ≈⟨ sym assoc ⟩
    (B • B) • Λ                                     ≈⟨ front _ (B□² k complete) ⟩
    ε • Λ                                           ≈⟨ left-unit ⟩
    Λ ∎)

  private
    -- The Z-part of the ZX: Z on the box wire, on two wires.
    ZZ : (₄₊ k) ⊢ Ex • Z ↑ • Ex ≈ Z ↓
    ZZ = L-sem (Ex • Z ↑ • Ex) Z Eq.refl

    Z-Λ : (₄₊ k) ⊢ (Ex • Z ↑ • Ex) • Λ ≈ Λ • (Ex • Z ↑ • Ex)
    Z-Λ = begin
      (Ex • Z ↑ • Ex) • Λ   ≈⟨ front _ ZZ ⟩
      Z ↓ • Λ               ≈⟨ box-Z₀ (₁₊ k) ⟩
      Λ • Z ↓               ≈⟨ back _ (sym ZZ) ⟩
      Λ • (Ex • Z ↑ • Ex) ∎

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

  eq304 : Eq304 k
  eq304 = sym (pass′ (eq298 k complete) (pass′ Z-Λ (pass′ (eq298 k complete) Z-Λ)))
