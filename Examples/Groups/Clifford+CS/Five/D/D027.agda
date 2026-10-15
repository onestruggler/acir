{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D027 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-cP-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-XCSX-box-2-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CSd24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS24-TOFF013)
-- F4-S2-CS0: 13 steps
lem-F4-S2-CS0 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 4 (Bx2-0413 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lem-XCSX-box-2-at0210243143 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS24 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS24 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ []) (S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-CS1: 15 steps
lem-F4-S2-CS1 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS24 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff023 ∷ []) (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS24 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff023 ∷ []) (Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (S2 ∷ CS24⁻ ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ []) (S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S2-CS2: 18 steps
lem-F4-S2-CS2 : Complete 4 → ⟪ (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S2-CS2 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS24 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS24 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 c4) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CS24 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ S2 ∷ CS24⁻ ∷ [])
  b1 = at 2 3 (S2 ∷ CS24⁻ ∷ []) (lw0 c4 (X4 ∷ CS24 ∷ X4 ∷ []) (S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 3 (CCZ024 ∷ S2 ∷ CS24⁻ ∷ []) (pw1 c4 (S2 ∷ CS24⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 c4) ▸
       at 3 2 (Toff013 ∷ S2 ∷ []) (lw4 c4 (S2 ∷ Toff013 ∷ []) (Toff013 ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 6 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S2 ∷ CS24⁻ ∷ []) (lw0 c4 (S2 ∷ CS24⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S2 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ S2 ∷ CS24⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS24 ∷ X4 ∷ [])
  b2 = at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 2 (X4 ∷ CS24 ∷ X4 ∷ []) (lw0 c4 (S2 ∷ CS24⁻ ∷ []) (X4 ∷ CS24 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-I: 1 steps
lem-F4-S3-I : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-S0: 1 steps
lem-F4-S3-S0 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-S1: 1 steps
lem-F4-S3-S1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-S2: 1 steps
lem-F4-S3-S2 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-S3: 1 steps
lem-F4-S3-S3 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-K0: 1 steps
lem-F4-S3-K0 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-K1: 1 steps
lem-F4-S3-K1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-K2: 1 steps
lem-F4-S3-K2 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-K3: 1 steps
lem-F4-S3-K3 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-K3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b0 = at 0 4 (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-CS0: 15 steps
lem-F4-S3-CS0 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff213 ∷ []) (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff213 ∷ []) (Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ []) (S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (S3 ∷ CS34⁻ ∷ []) (X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-CS1: 15 steps
lem-F4-S3-CS1 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 4 (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS34 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff023 ∷ []) (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS34 ∷ X4 ∷ CCZ014 ∷ []) (CCZ014 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff023 ∷ []) (Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ []) (S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (S3 ∷ CS34⁻ ∷ []) (X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S3-CS2: 15 steps
lem-F4-S3-CS2 : Complete 4 → ⟪ (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S3-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS34 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff013 ∷ []) (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS34 ∷ X4 ∷ CCZ024 ∷ []) (CCZ024 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff013 ∷ []) (Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS34 ∷ X4 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (S3 ∷ CS34⁻ ∷ []) (lw0 c4 (X4 ∷ CS34 ∷ X4 ∷ []) (S3 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS34 ∷ X4 ∷ []) (lw0 c4 (S3 ∷ CS34⁻ ∷ []) (X4 ∷ CS34 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-K0-I: 1 steps
lem-F4-K0-I : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K0-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

