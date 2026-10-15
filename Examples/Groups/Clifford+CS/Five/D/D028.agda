{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D028 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243 ; lem-box-tQ-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-tQ-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS24-CCZ013 ; lem-comm-CSd24-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CK40-TOFF213 ; lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023)
-- F4-K0-S0: 1 steps
lem-F4-K0-S0 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-S1: 1 steps
lem-F4-K0-S1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-S2: 1 steps
lem-F4-K0-S2 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-S3: 1 steps
lem-F4-K0-S3 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-K0: 1 steps
lem-F4-K0-K0 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-K1: 1 steps
lem-F4-K0-K1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-K2: 1 steps
lem-F4-K0-K2 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-K3: 1 steps
lem-F4-K0-K3 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-CS0: 17 steps
lem-F4-K0-CS0 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 2 (Toff213 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF213 c4) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 2 4 (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 2 (Toff213 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF213 c4) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- CSu-box-2 @243243: 17 steps
lem-CSu-box-2-at243243 : Complete 4 → ⟪ (CS04 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-2-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04 ∷ Bx0-1423 ∷ []) (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) (pw2 c4 (CS04 ∷ Toff014 ∷ []) (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ023 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 4 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸ done

  b1 : Chain (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CS04 ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff014 ∷ []) (Toff014 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) (pw2 c4 (CS04 ∷ Toff014 ∷ []) (Toff014 ∷ CS04 ∷ CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS04 ∷ []) (pw2 c4 (CS04 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CS04 ∷ []) (Bx0-1423 ∷ CS04 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done


-- Ku-box @243243: 6 steps
lem-Ku-box-at243243 : Complete 4 → ⟪ (K0 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ K0 ∷ []) ⟫ʷ
lem-Ku-box-at243243 c4 = run b0
  where
  b0 : Chain (K0 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ K0 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ K0 ∷ []) (pw2 c4 (K0 ∷ Toff014 ∷ []) (CCZ014 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ []) (Toff023 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ K0 ∷ []) (pw2 c4 (K0 ∷ Toff014 ∷ []) (CCZ014 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ K0 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ []) (Toff023 ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


-- Kdu-box @243243: 6 steps
lem-Kdu-box-at243243 : Complete 4 → ⟪ (K0⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ K0⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at243243 c4 = run b0
  where
  b0 : Chain (K0⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ K0⁻ ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ Toff014 ∷ []) (CCZ014 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ CCZ023 ∷ []) (Toff023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ K0⁻ ∷ []) (pw2 c4 (K0⁻ ∷ Toff014 ∷ []) (CCZ014 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ K0⁻ ∷ []) (lw4 c4 (K0⁻ ∷ CCZ023 ∷ []) (Toff023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


-- CKdu-box-2 @243243: 7 steps
lem-CKdu-box-2-at243243 : Complete 4 → ⟪ (CK40⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at243243 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (pw1 c4 (CK40⁻ ∷ []) (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 3 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 2 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 2 (Bx0-1423 ∷ K0⁻ ∷ []) (lem-Kdu-box-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (pw1 c4 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (CK40⁻ ∷ []) tt tt Eq.refl) ▸ done


-- XCKX-box-2 @243243: 4 steps
lem-XCKX-box-2-at243243 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at243243 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 3 (K0 ∷ CK40⁻ ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ []) (K0 ∷ CK40⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ CK40⁻ ∷ []) (lem-CKdu-box-2-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ K0 ∷ []) (lem-Ku-box-at243243 c4) ▸
       at 1 2 (X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (K0 ∷ CK40⁻ ∷ []) (X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-CS1: 11 steps
lem-F4-K0-CS1 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (lem-XCKX-box-2-at243243 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CK40 ∷ X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CK40 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- CSu-box-2 @122441: 17 steps
lem-CSu-box-2-at122441 : Complete 4 → ⟪ (CS04 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS04 ∷ []) ⟫ʷ
lem-CSu-box-2-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04 ∷ Bx0-2431 ∷ []) (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) (pw1 c4 (CS04 ∷ Toff024 ∷ []) (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 4 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸ done

  b1 : Chain (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CS04 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff024 ∷ []) (Toff024 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) (pw1 c4 (CS04 ∷ Toff024 ∷ []) (Toff024 ∷ CS04 ∷ CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS04 ∷ []) (pw1 c4 (CS04 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CS04 ∷ []) (Bx0-2431 ∷ CS04 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done

