{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D025 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-tQ-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-tQ-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS24-CCZ013 ; lem-comm-CSd24-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023)
-- CSdu-box-2 @243243: 17 steps
lem-CSdu-box-2-at243243 : Complete 4 → ⟪ (CS04⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx0-1423 ∷ []) (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CS04⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ023 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 4 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸ done

  b1 : Chain (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CS04⁻ ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) (pw2 c4 (CS04⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS04⁻ ∷ []) (pw2 c4 (CS04⁻ ∷ CS14⁻ ∷ CCZ014 ∷ CS14⁻ ∷ CZ14 ∷ CCZ014 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CS04⁻ ∷ []) (Bx0-1423 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done


-- Su-box @243243: 17 steps
lem-Su-box-at243243 : Complete 4 → ⟪ (S0 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S0 ∷ Bx0-1423 ∷ []) (Toff014 ∷ S0 ∷ CS14 ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) (pw2 c4 (S0 ∷ Toff014 ∷ []) (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ023 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 4 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸ done

  b1 : Chain (Toff014 ∷ S0 ∷ CS14 ∷ CCZ023 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff014 ∷ CCZ023 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ S0 ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ CCZ023 ∷ []) (CCZ023 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff014 ∷ []) (Toff014 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) (pw2 c4 (S0 ∷ Toff014 ∷ []) (Toff014 ∷ S0 ∷ CS14 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (S0 ∷ []) (pw2 c4 (S0 ∷ CS14 ∷ CCZ014 ∷ CS14 ∷ CZ14 ∷ CCZ014 ∷ []) (S0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ CCZ023 ∷ []) (CCZ023 ∷ S0 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ S0 ∷ []) (Bx0-1423 ∷ S0 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done


-- XCSX-box-2 @243243: 4 steps
lem-XCSX-box-2-at243243 : Complete 4 → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at243243 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ []) (S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1423 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at243243 c4) ▸
       at 0 2 (Bx0-1423 ∷ S0 ∷ []) (lem-Su-box-at243243 c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S0-CS1: 13 steps
lem-F4-S0-CS1 : Complete 4 → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-1423 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-XCSX-box-2-at243243 c4) ▸
       at 1 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS04 ∷ X4 ∷ CS13 ∷ []) (CS13 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff324 ∷ []) (Toff324 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS04 ∷ X4 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ []) (S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- CSdu-box-2 @122441: 17 steps
lem-CSdu-box-2-at122441 : Complete 4 → ⟪ (CS04⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx0-2431 ∷ []) (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CS04⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 4 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸ done

  b1 : Chain (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CS04⁻ ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ CS04⁻ ∷ []) (pw2 c4 (CS04⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) (pw1 c4 (CS04⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CS24⁻ ∷ CCZ024 ∷ CS24⁻ ∷ CZ24 ∷ CCZ024 ∷ []) (CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CS04⁻ ∷ []) (pw2 c4 (CS04⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CS04⁻ ∷ []) (Bx0-2431 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done


-- Su-box @122441: 17 steps
lem-Su-box-at122441 : Complete 4 → ⟪ (S0 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ S0 ∷ []) ⟫ʷ
lem-Su-box-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S0 ∷ Bx0-2431 ∷ []) (Toff024 ∷ S0 ∷ CS24 ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at122441 c4) ▸
       at 0 2 (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) (pw1 c4 (S0 ∷ Toff024 ∷ []) (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 c4) ▸
       at 4 2 (CCZ013 ∷ CX02 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸ done

  b1 : Chain (Toff024 ∷ S0 ∷ CS24 ∷ CCZ013 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff024 ∷ CCZ013 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ S0 ∷ [])
  b1 = at 4 5 (CCZ024 ∷ []) (pw1 c4 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ CCZ013 ∷ []) (CCZ013 ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CZ24 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff024 ∷ []) (Toff024 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) (pw1 c4 (S0 ∷ Toff024 ∷ []) (Toff024 ∷ S0 ∷ CS24 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 6 (S0 ∷ []) (pw1 c4 (S0 ∷ CS24 ∷ CCZ024 ∷ CS24 ∷ CZ24 ∷ CCZ024 ∷ []) (S0 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ S0 ∷ []) (lw4 c4 (S0 ∷ CCZ013 ∷ []) (CCZ013 ∷ S0 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ S0 ∷ []) (Bx0-2431 ∷ S0 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done


-- XCSX-box-2 @122441: 4 steps
lem-XCSX-box-2-at122441 : Complete 4 → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-2-at122441 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ []) (S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-2431 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at122441 c4) ▸
       at 0 2 (Bx0-2431 ∷ S0 ∷ []) (lem-Su-box-at122441 c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S0-CS2: 13 steps
lem-F4-S0-CS2 : Complete 4 → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 4 (Bx0-2431 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (lem-XCSX-box-2-at122441 c4) ▸
       at 1 4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS04 ∷ X4 ∷ CS12 ∷ []) (CS12 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS04 ∷ X4 ∷ Toff134 ∷ []) (Toff134 ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (pw3 c4 (X4 ∷ CS04 ∷ X4 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS04 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (S0 ∷ CS04⁻ ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ []) (S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-I: 1 steps
lem-F4-S1-I : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-I c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-S0: 1 steps
lem-F4-S1-S0 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS14 ∷ X4 ∷ CS04 ∷ []) (CS04 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-S1: 1 steps
lem-F4-S1-S1 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ CS14 ∷ []) (CS14 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-S2: 1 steps
lem-F4-S1-S2 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ CS24 ∷ []) (CS24 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-S3: 1 steps
lem-F4-S1-S3 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-S3 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ CS34 ∷ []) (CS34 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-K0: 1 steps
lem-F4-S1-K0 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K0 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (pw2 c4 (X4 ∷ CS14 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-K1: 1 steps
lem-F4-S1-K1 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K1 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- F4-S1-K2: 1 steps
lem-F4-S1-K2 : Complete 4 → ⟪ (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) ⟫ʷ
lem-F4-S1-K2 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ [])
  b0 = at 0 4 (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CS14 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ CS14 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

