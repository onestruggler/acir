------------------------------------------------------------------------
-- Presentations of groups
--
-- Splitting a phase gate along wire 0
--
-- On ₁₊ m wires, write x = (x₀ , x').  A parity not involving x₀ is a
-- parity one wire up (split-sw), and one involving it splits as
--
--     ω^(x₀ ⊕ ℓ·x') = ω^(ℓ·x') · ω^(x₀) · ω^(−2 x₀ (ℓ·x')),
--
-- that is P (cx ℓ) ≈ (P ℓ) ↑ • T • C₂ ℓ ⁷ (split-cx), where
-- C₂ ℓ = ω^(2 x₀ (ℓ·x')) is CS conjugated by the representative of ℓ
-- one wire up.  Expanding the parity one wire at a time,
--
--     2 x₀ (x₁ ⊕ y) = 2 x₀ x₁ + 2 x₀ y + 4 x₀ x₁ y        (mod 8),
--     4 x₀ x₁ (x₂ ⊕ y) = 4 x₀ x₁ x₂ + 4 x₀ x₁ y            (mod 8),
--
-- C₂ reduces to CS on (0, 1), C₂ of the rest moved past wire 1, and
-- C₃ ℓ = ω^(4 x₀ x₁ (ℓ·x'')), which reduces the same way to CCZ.  Each
-- step is one conjugation by the representative's gadget, and the
-- local identities of Diagonal.Gates (R₉ and R₁₃ in disguise).
------------------------------------------------------------------------

{-# OPTIONS --cubical-compatible --safe #-}

module Examples.Groups.CNOT+Dihedral.Diagonal.Split where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (ε ; _•_ ; _^_)

open import Notations using (₁₊ ; ₂₊ ; ₃₊ ; ₄₊)

open import Examples.Groups.CNOT+Dihedral.Syntactics
open import Examples.Groups.CNOT+Dihedral.Reasoning
open import Examples.Groups.CNOT+Dihedral.Powers
open import Examples.Groups.CNOT+Dihedral.Evaluation using (_⁻¹ ; module Inv)
open import Examples.Groups.CNOT+Dihedral.Linear.Base using (NZ ; e₀ ; cx ; sw ; r)
open import Examples.Groups.CNOT+Dihedral.Diagonal.Phase
open import Examples.Groups.CNOT+Dihedral.Diagonal.Gates

private
  variable
    n k : ℕ

------------------------------------------------------------------------
-- The controlled phases on a parity

C₂ : NZ (₁₊ k) → Circuit (₂₊ k)
C₂ ℓ = (r ℓ ⁻¹) ↑ • CS • r ℓ ↑

C₃ : NZ (₁₊ k) → Circuit (₃₊ k)
C₃ ℓ = (r ℓ ⁻¹) ↑ ↑ • CCZ • r ℓ ↑ ↑

------------------------------------------------------------------------
-- The gates on the bottom wires commute with what lies above them

module _ (w : Circuit n) where

  private
    τ₂ : Circuit (₂₊ n)
    τ₂ = w ↑ ↑

    τT : (₂₊ n) ⊢ τ₂ • T ≈ T • τ₂
    τT = comm-gate₁-w↑ T-gate (w ↑)

    τT↑ : (₂₊ n) ⊢ τ₂ • T ↑ ≈ T ↑ • τ₂
    τT↑ = lift (comm-gate₁-w↑ T-gate w)

    τCNOT : (₂₊ n) ⊢ τ₂ • CNOT ≈ CNOT • τ₂
    τCNOT = comm-gate₂-w↑↑ CNOT-gate w

    τSWAP : (₂₊ n) ⊢ τ₂ • SWAP ≈ SWAP • τ₂
    τSWAP = comm-gate₂-w↑↑ SWAP-gate w

  τ₂-U : (₂₊ n) ⊢ w ↑ ↑ • U ≈ U • w ↑ ↑
  τ₂-U = Width.slide (₂₊ n) τCNOT (Width.slide (₂₊ n) τT τCNOT)

  τ₂-CS : (₂₊ n) ⊢ w ↑ ↑ • CS ≈ CS • w ↑ ↑
  τ₂-CS = Width.slide (₂₊ n) τT (Width.slide (₂₊ n) τT↑
            (Width.sym (Pow.pow-comm (₂₊ n) 7 (Width.sym τ₂-U))))

module _ (w : Circuit n) where

  private
    τ₃ : Circuit (₃₊ n)
    τ₃ = w ↑ ↑ ↑

    sl = Width.slide (₃₊ n)

    τT : (₃₊ n) ⊢ τ₃ • T ≈ T • τ₃
    τT = comm-gate₁-w↑ T-gate (w ↑ ↑)

    τT↑ : (₃₊ n) ⊢ τ₃ • T ↑ ≈ T ↑ • τ₃
    τT↑ = lift (comm-gate₁-w↑ T-gate (w ↑))

    τT↑↑ : (₃₊ n) ⊢ τ₃ • T ↑ ↑ ≈ T ↑ ↑ • τ₃
    τT↑↑ = lift (lift (comm-gate₁-w↑ T-gate w))

    τCNOT : (₃₊ n) ⊢ τ₃ • CNOT ≈ CNOT • τ₃
    τCNOT = comm-gate₂-w↑↑ CNOT-gate (w ↑)

    τCNOT↑ : (₃₊ n) ⊢ τ₃ • CNOT ↑ ≈ CNOT ↑ • τ₃
    τCNOT↑ = lift (comm-gate₂-w↑↑ CNOT-gate w)

    τSWAP : (₃₊ n) ⊢ τ₃ • SWAP ≈ SWAP • τ₃
    τSWAP = comm-gate₂-w↑↑ SWAP-gate (w ↑)

    τU : (₃₊ n) ⊢ τ₃ • U ≈ U • τ₃
    τU = τ₂-U (w ↑)

    τU↑ : (₃₊ n) ⊢ τ₃ • U ↑ ≈ U ↑ • τ₃
    τU↑ = lift (τ₂-U w)

    pw : ∀ {a : Circuit (₃₊ n)} (i : ℕ) → (₃₊ n) ⊢ τ₃ • a ≈ a • τ₃ →
         (₃₊ n) ⊢ τ₃ • a ^ i ≈ a ^ i • τ₃
    pw i e = Width.sym (Pow.pow-comm (₃₊ n) i (Width.sym e))

  τ₃-CCZ : (₃₊ n) ⊢ w ↑ ↑ ↑ • CCZ ≈ CCZ • w ↑ ↑ ↑
  τ₃-CCZ =
    sl (sl τCNOT↑ (sl (sl τCNOT (sl τT τCNOT)) τCNOT↑))
    (sl τT (sl τT↑ (sl τT↑↑ (sl (pw 7 τU)
      (sl (pw 7 (sl τSWAP (sl τU↑ τSWAP))) (pw 7 τU↑))))))

------------------------------------------------------------------------
-- Splitting a phase gate

private
  -- A word that commutes with ρ survives conjugation by it.
  conj-id : ∀ {m} (A ρ X : Circuit m) → m ⊢ A • ρ ≈ ε → m ⊢ ρ • X ≈ X • ρ →
            m ⊢ A • X • ρ ≈ X
  conj-id {m} A ρ X i c = begin
    A • X • ρ        ≈⟨ back A (Width.sym c) ⟩
    A • ρ • X        ≈⟨ sym assoc ⟩
    (A • ρ) • X      ≈⟨ front X i ⟩
    ε • X            ≈⟨ left-unit ⟩
    X                ∎
    where open Width m

  -- (r ℓ ⁻¹) ↑ is the inverse of r ℓ ↑, on either side.
  inv↑ˡ : (ℓ : NZ (₁₊ k)) → (₂₊ k) ⊢ (r ℓ ⁻¹) ↑ • r ℓ ↑ ≈ ε
  inv↑ˡ ℓ = lift (Inv.inverseˡ _)

  inv↑ʳ : (ℓ : NZ (₁₊ k)) → (₂₊ k) ⊢ r ℓ ↑ • (r ℓ ⁻¹) ↑ ≈ ε
  inv↑ʳ ℓ = lift (Inv.inverseʳ _)

split-sw : (ℓ : NZ (₁₊ k)) → (₂₊ k) ⊢ P (sw ℓ) ≈ (P ℓ) ↑
split-sw ℓ = P-sw ℓ

split-cx : (ℓ : NZ (₁₊ k)) → (₂₊ k) ⊢ P (cx ℓ) ≈ (P ℓ) ↑ • T • C₂ ℓ ^ 7
split-cx {k} ℓ = begin
  P (cx ℓ)
    ≈⟨ P-cx ℓ ⟩
  A • U • R
    ≈⟨ back A (front R U-CS) ⟩
  A • (T ↑ • T • CS ^ 7) • R
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
  A • T ↑ • T • CS ^ 7 • R
    ≈⟨ back A (back (T ↑) (sym (cancel (T • CS ^ 7 • R)))) ⟩
  A • T ↑ • R • A • T • CS ^ 7 • R
    ≈⟨ back A (back (T ↑) (back R (by-passoc (□ • □ • □ • □) ((□ • □) • □ • □) Eq.refl))) ⟩
  A • T ↑ • R • (A • T) • CS ^ 7 • R
    ≈⟨ back A (back (T ↑) (back R (front _ (sym (T-↑ (r ℓ ⁻¹)))))) ⟩
  A • T ↑ • R • (T • A) • CS ^ 7 • R
    ≈⟨ by-passoc (□ • □ • □ • (□ • □) • □ • □) ((□ • □ • □) • □ • (□ • □ • □)) Eq.refl ⟩
  (A • T ↑ • R) • T • (A • CS ^ 7 • R)
    ≈⟨ back _ (back T (sym C₂⁷)) ⟩
  (A • T ↑ • R) • T • C₂ ℓ ^ 7 ∎
  where
  open Width (₂₊ k)
  A = (r ℓ ⁻¹) ↑
  R = r ℓ ↑
  cancel : (X : Circuit (₂₊ k)) → (₂₊ k) ⊢ R • A • X ≈ X
  cancel X = trans (sym assoc) (trans (front X (inv↑ʳ ℓ)) left-unit)
  -- C₂ ℓ ⁷ is CS⁷ conjugated.
  C₂⁷ : (₂₊ k) ⊢ C₂ ℓ ^ 7 ≈ A • CS ^ 7 • R
  C₂⁷ = trans (Pow.pow-cong (₂₊ k) 7 (front _ (refl' (Eq.sym (⁻¹-↑ (r ℓ))))))
          (trans (Pow.pow-conj (₂₊ k) R CS 7) (front _ (refl' (⁻¹-↑ (r ℓ)))))

------------------------------------------------------------------------
-- The controlled phases, one wire at a time

C₂-e₀ : (₂₊ k) ⊢ C₂ {k} e₀ ≈ CS
C₂-e₀ {k} = trans left-unit right-unit
  where open Width (₂₊ k)

C₂-sw : (ℓ : NZ (₁₊ k)) → (₃₊ k) ⊢ C₂ (sw ℓ) ≈ SWAP • (C₂ ℓ) ↑ • SWAP
C₂-sw {k} ℓ = begin
  ((r ℓ ↑) ⁻¹ • SWAP) ↑ • CS • (SWAP • r ℓ ↑) ↑
    ≈⟨ front _ (refl' (Eq.cong (λ z → (z • SWAP) ↑) (⁻¹-↑ (r ℓ)))) ⟩
  (A • SWAP ↑) • CS • SWAP ↑ • ρ
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  A • (SWAP ↑ • CS • SWAP ↑) • ρ
    ≈⟨ back A (front ρ CS₀₂) ⟩
  A • (SWAP • CS ↑ • SWAP) • ρ
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
  (A • SWAP) • CS ↑ • SWAP • ρ
    ≈⟨ cong (comm-gate₂-w↑↑ SWAP-gate (r ℓ ⁻¹)) (back _ (sym (comm-gate₂-w↑↑ SWAP-gate (r ℓ)))) ⟩
  (SWAP • A) • CS ↑ • ρ • SWAP
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  SWAP • (A • CS ↑ • ρ) • SWAP ∎
  where
  open Width (₃₊ k)
  A = (r ℓ ⁻¹) ↑ ↑
  ρ = r ℓ ↑ ↑

C₂-cx : (ℓ : NZ (₁₊ k)) → (₃₊ k) ⊢ C₂ (cx ℓ) ≈ CS • (SWAP • (C₂ ℓ) ↑ • SWAP) • C₃ ℓ
C₂-cx {k} ℓ = begin
  ((r ℓ ↑) ⁻¹ • CNOT) ↑ • CS • (CNOT • r ℓ ↑) ↑
    ≈⟨ front _ (refl' (Eq.cong (λ z → (z • CNOT) ↑) (⁻¹-↑ (r ℓ)))) ⟩
  (A • CNOT ↑) • CS • CNOT ↑ • ρ
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  A • (CNOT ↑ • CS • CNOT ↑) • ρ
    ≈⟨ back A (front ρ CNOT-CS) ⟩
  A • (CS • (SWAP • CS ↑ • SWAP) • CCZ) • ρ
    ≈⟨ by-passoc (□ • (□ • □ • □) • □) (□ • □ • □ • □ • □) Eq.refl ⟩
  A • CS • S • CCZ • ρ
    ≈⟨ back A (back CS (back S (sym (cancel (CCZ • ρ))))) ⟩
  A • CS • S • ρ • A • CCZ • ρ
    ≈⟨ back A (back CS (sym (cancel (S • ρ • A • CCZ • ρ)))) ⟩
  A • CS • ρ • A • S • ρ • A • CCZ • ρ
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □ • □ • □ • □) ((□ • □ • □) • (□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (A • CS • ρ) • (A • S • ρ) • (A • CCZ • ρ)
    ≈⟨ cong (conj-id A ρ CS (lift (lift (Inv.inverseˡ _))) (τ₂-CS (r ℓ)))
            (front _ (C₂-sw-core ℓ)) ⟩
  CS • (SWAP • (C₂ ℓ) ↑ • SWAP) • C₃ ℓ ∎
  where
  open Width (₃₊ k)
  A = (r ℓ ⁻¹) ↑ ↑
  ρ = r ℓ ↑ ↑
  S = SWAP • CS ↑ • SWAP
  cancel : (X : Circuit (₃₊ k)) → (₃₊ k) ⊢ ρ • A • X ≈ X
  cancel X = trans (sym assoc) (trans (front X (lift (lift (Inv.inverseʳ _)))) left-unit)
  C₂-sw-core : (ℓ : NZ (₁₊ k)) → (₃₊ k) ⊢ (r ℓ ⁻¹) ↑ ↑ • (SWAP • CS ↑ • SWAP) • r ℓ ↑ ↑ ≈ SWAP • (C₂ ℓ) ↑ • SWAP
  C₂-sw-core ℓ = begin
    A' • (SWAP • CS ↑ • SWAP) • ρ'
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
    (A' • SWAP) • CS ↑ • SWAP • ρ'
      ≈⟨ cong (comm-gate₂-w↑↑ SWAP-gate (r ℓ ⁻¹)) (back _ (sym (comm-gate₂-w↑↑ SWAP-gate (r ℓ)))) ⟩
    (SWAP • A') • CS ↑ • ρ' • SWAP
      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    SWAP • (A' • CS ↑ • ρ') • SWAP ∎
    where
    A' = (r ℓ ⁻¹) ↑ ↑
    ρ' = r ℓ ↑ ↑

C₃-e₀ : (₃₊ k) ⊢ C₃ {k} e₀ ≈ CCZ
C₃-e₀ {k} = trans left-unit right-unit
  where open Width (₃₊ k)

private
  -- The rotations commute with what lies three wires up.
  πL-comm : (w : Circuit n) → (₃₊ n) ⊢ w ↑ ↑ ↑ • πL ≈ πL • w ↑ ↑ ↑
  πL-comm {n} w = Width.slide (₃₊ n) (lift (comm-gate₂-w↑↑ SWAP-gate w)) (comm-gate₂-w↑↑ SWAP-gate (w ↑))

  πR-comm : (w : Circuit n) → (₃₊ n) ⊢ w ↑ ↑ ↑ • πR ≈ πR • w ↑ ↑ ↑
  πR-comm {n} w = Width.slide (₃₊ n) (comm-gate₂-w↑↑ SWAP-gate (w ↑)) (lift (comm-gate₂-w↑↑ SWAP-gate w))

  -- Conjugating π-rotated words by an upper circuit.
  π-core : (ℓ : NZ (₁₊ k)) (X : Circuit (₃₊ k)) →
           (₄₊ k) ⊢ (r ℓ ⁻¹) ↑ ↑ ↑ • (πL • X ↑ • πR) • r ℓ ↑ ↑ ↑ ≈
                    πL • ((r ℓ ⁻¹) ↑ ↑ • X • r ℓ ↑ ↑) ↑ • πR
  π-core {k} ℓ X = begin
    A • (πL • X ↑ • πR) • ρ
      ≈⟨ by-passoc (□ • (□ • □ • □) • □) ((□ • □) • □ • □ • □) Eq.refl ⟩
    (A • πL) • X ↑ • πR • ρ
      ≈⟨ cong (πL-comm (r ℓ ⁻¹)) (back _ (sym (πR-comm (r ℓ)))) ⟩
    (πL • A) • X ↑ • ρ • πR
      ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
    πL • (A • X ↑ • ρ) • πR ∎
    where
    open Width (₄₊ k)
    A = (r ℓ ⁻¹) ↑ ↑ ↑
    ρ = r ℓ ↑ ↑ ↑

C₃-sw : (ℓ : NZ (₁₊ k)) → (₄₊ k) ⊢ C₃ (sw ℓ) ≈ πL • (C₃ ℓ) ↑ • πR
C₃-sw {k} ℓ = begin
  ((r ℓ ↑) ⁻¹ • SWAP) ↑ ↑ • CCZ • (SWAP • r ℓ ↑) ↑ ↑
    ≈⟨ front _ (refl' (Eq.cong (λ z → (z • SWAP) ↑ ↑) (⁻¹-↑ (r ℓ)))) ⟩
  (A • SWAP ↑ ↑) • CCZ • SWAP ↑ ↑ • ρ
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  A • (SWAP ↑ ↑ • CCZ • SWAP ↑ ↑) • ρ
    ≈⟨ back A (front ρ CCZ₀₁₃) ⟩
  A • (πL • CCZ ↑ • πR) • ρ
    ≈⟨ π-core ℓ CCZ ⟩
  πL • (C₃ ℓ) ↑ • πR ∎
  where
  open Width (₄₊ k)
  A = (r ℓ ⁻¹) ↑ ↑ ↑
  ρ = r ℓ ↑ ↑ ↑

C₃-cx : (ℓ : NZ (₁₊ k)) → (₄₊ k) ⊢ C₃ (cx ℓ) ≈ CCZ • πL • (C₃ ℓ) ↑ • πR
C₃-cx {k} ℓ = begin
  ((r ℓ ↑) ⁻¹ • CNOT) ↑ ↑ • CCZ • (CNOT • r ℓ ↑) ↑ ↑
    ≈⟨ front _ (refl' (Eq.cong (λ z → (z • CNOT) ↑ ↑) (⁻¹-↑ (r ℓ)))) ⟩
  (A • CNOT ↑ ↑) • CCZ • CNOT ↑ ↑ • ρ
    ≈⟨ by-passoc ((□ • □) • □ • □ • □) (□ • (□ • □ • □) • □) Eq.refl ⟩
  A • (CNOT ↑ ↑ • CCZ • CNOT ↑ ↑) • ρ
    ≈⟨ back A (front ρ CNOT-CCZ) ⟩
  A • (CCZ • πL • CCZ ↑ • πR) • ρ
    ≈⟨ by-passoc (□ • (□ • □ • □ • □) • □) (□ • □ • (□ • □ • □) • □) Eq.refl ⟩
  A • CCZ • (πL • CCZ ↑ • πR) • ρ
    ≈⟨ back A (back CCZ (sym (cancel ((πL • CCZ ↑ • πR) • ρ)))) ⟩
  A • CCZ • ρ • A • (πL • CCZ ↑ • πR) • ρ
    ≈⟨ by-passoc (□ • □ • □ • □ • □ • □) ((□ • □ • □) • (□ • □ • □)) Eq.refl ⟩
  (A • CCZ • ρ) • (A • (πL • CCZ ↑ • πR) • ρ)
    ≈⟨ cong (conj-id A ρ CCZ (lift (lift (lift (Inv.inverseˡ _)))) (τ₃-CCZ (r ℓ))) (π-core ℓ CCZ) ⟩
  CCZ • πL • (C₃ ℓ) ↑ • πR ∎
  where
  open Width (₄₊ k)
  A = (r ℓ ⁻¹) ↑ ↑ ↑
  ρ = r ℓ ↑ ↑ ↑
  cancel : (X : Circuit (₄₊ k)) → (₄₊ k) ⊢ ρ • A • X ≈ X
  cancel X = trans (sym assoc) (trans (front X (lift (lift (lift (Inv.inverseʳ _))))) left-unit)
