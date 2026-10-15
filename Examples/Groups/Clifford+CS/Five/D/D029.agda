{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D029 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Completeness using (Complete)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.Lits using (lw0 ; lw1 ; lw2 ; lw3 ; lw4)
open import Examples.Groups.Clifford+CS.Five.Resps using (pw0 ; pw1 ; pw2 ; pw3 ; pw4)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441 ; lem-box-tQ-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D028 using (lem-CSu-box-2-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CX40-CCZ123)
-- Ku-box @122441: 6 steps
lem-Ku-box-at122441 : Complete 4 → ⟪ (K0 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box-at122441 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ K0 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ K0 ∷ []) (pw1 c4 (K0 ∷ Toff024 ∷ []) (CCZ024 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ []) (Toff013 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ K0 ∷ []) (pw1 c4 (K0 ∷ Toff024 ∷ []) (CCZ024 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ []) (Toff013 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- Kdu-box @122441: 6 steps
lem-Kdu-box-at122441 : Complete 4 → ⟪ (K0⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at122441 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (K0⁻ ∷ Toff024 ∷ []) (CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff013 ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ CCZ013 ∷ []) (Toff013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (K0⁻ ∷ Toff024 ∷ []) (CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ CCZ013 ∷ []) (Toff013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- CKdu-box-2 @122441: 7 steps
lem-CKdu-box-2-at122441 : Complete 4 → ⟪ (CK40⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at122441 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (pw1 c4 (CK40⁻ ∷ []) (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 3 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 2 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 2 (Bx0-2431 ∷ K0⁻ ∷ []) (lem-Kdu-box-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (pw1 c4 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (CK40⁻ ∷ []) tt tt Eq.refl) ▸ done


-- XCKX-box-2 @122441: 4 steps
lem-XCKX-box-2-at122441 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at122441 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 3 (K0 ∷ CK40⁻ ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ []) (K0 ∷ CK40⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ CK40⁻ ∷ []) (lem-CKdu-box-2-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ K0 ∷ []) (lem-Ku-box-at122441 c4) ▸
       at 1 2 (X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (K0 ∷ CK40⁻ ∷ []) (X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-CS2: 11 steps
lem-F4-K0-CS2 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-XCKX-box-2-at122441 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CK40 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CK40 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F4-K1-I: 1 steps
lem-F4-K1-I : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K1-S0: 1 steps
lem-F4-K1-S0 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K1-S1: 1 steps
lem-F4-K1-S1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K1-S2: 1 steps
lem-F4-K1-S2 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K1-S3: 1 steps
lem-F4-K1-S3 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K1-K0: 1 steps
lem-F4-K1-K0 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK41 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K1-K1: 1 steps
lem-F4-K1-K1 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K1-K2: 1 steps
lem-F4-K1-K2 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K1-K3: 1 steps
lem-F4-K1-K3 : Complete 4 → ⟪ (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK41 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- sym-ab @0210243143: 18 steps
lem-sym-ab-at0210243143 : Complete 4 → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym-ab-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (lw0 c4 (CCZ123 ∷ []) (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-43 ∷ []) (refl) ▸
       at 7 1 (Bx2-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ [])
  b1 = at 2 6 (Bx4-213 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (lw4 c4 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (lw0 c4 (CCZ123 ∷ []) (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-43 ∷ []) (refl) ▸
       at 10 1 (Bx2-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (Bx2-4013 ∷ [])
  b2 = at 5 6 (Bx4-213 ∷ []) (refl) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done


-- cQ @0214203143: 7 steps
lem-cQ-at0214203143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at0214203143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (pw3 c4 (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CS24 ∷ []) (lw0 c4 (CS24 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 c4) ▸
       at 2 2 (CCZ123 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 c4) ▸
       at 0 2 (CCZ123 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ024 ∷ []) (pw3 c4 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done

