{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D010 where

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
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-pairs)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-sym-bc-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-sym-ab-at13213442)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CZ14-TOFF023 ; lem-comm-CZ24-CCZ013 ; lem-comm-CZ24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CSd13-TOFF024 ; lem-comm-CZ13-CCZ024 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CZ23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-CX31-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-CX32-CCZ014 ; lem-comm-CX42-CCZ013)
-- box-perm-1342: 3 steps
lem-box-perm-1342 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1342 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸
       at 0 1 (Bx0-1342 ∷ []) (lem-sym-ab-at13213442 c4) ▸ done


-- cQ @13213442: 7 steps
lem-cQ-at13213442 : Complete 4 → ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-cQ-at13213442 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (pw1 c4 (CS03 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 2 2 (CCZ024 ∷ CS01⁻ ∷ []) (pw3 c4 (CS01⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 c4) ▸
       at 0 2 (CCZ024 ∷ CS01 ∷ []) (pw3 c4 (CS01 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ013 ∷ []) (lw4 c4 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @13213442: 13 steps
lem-box-tQ-at13213442 : Complete 4 → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3142 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw1 c4 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw1 c4 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) (lw4 c4 (CCZ013 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 c4) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at13213442 c4) ▸
       at 2 4 (Toff013 ∷ []) (lw4 c4 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- tP @13213442: 7 steps
lem-tP-at13213442 : Complete 4 → ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ
lem-tP-at13213442 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (Toff024 ∷ []) (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ024 ∷ CCZ013 ∷ []) (lem-cQ-at13213442 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff024 ∷ []) (pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @13213442: 8 steps
lem-P-box-at13213442 : Complete 4 → ⟪ (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-P-box-at13213442 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4) ▸
       at 0 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at13213442 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at13213442 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ24 ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) (CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 c4) ▸
       at 3 3 (CCZ024 ∷ []) (pw1 c4 (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸ done


-- VPQ @13213442: 14 steps
lem-VPQ-at13213442 : Complete 4 → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸
       at 1 2 (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS24⁻ ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at13213442 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS13⁻ ∷ []) (sym (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 c4) ▸
       at 3 2 (S0⁻ ∷ CS13⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 0 4 (Toff024 ∷ CCZ024 ∷ []) (pw1 c4 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff013 ∷ CCZ013 ∷ []) (lw4 c4 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @13213442: 3 steps
lem-QVQ-at13213442 : Complete 4 → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at13213442 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at13213442 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @13213442: 12 steps
lem-box-cP-at13213442 : Complete 4 → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at13213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3142 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-042 ∷ Toff013 ∷ CCZ013 ∷ Bx3-042 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw1 c4 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx0-32 ∷ Toff304 ∷ CCZ034 ∷ Bx0-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw1 c4 (CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at13213442 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at13213442 c4) ▸
       at 2 2 [] (lw4 c4 (Toff013 ∷ Toff013 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @1441: 7 steps
lem-cQ-at1441 : Complete 4 → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at1441 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 c4) ▸
       at 2 2 (CCZ013 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 c4) ▸
       at 0 2 (CCZ013 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ024 ∷ []) (pw1 c4 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @1441: 13 steps
lem-box-tQ-at1441 : Complete 4 → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4231 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (pw2 c4 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (pw2 c4 (CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at1441 c4) ▸
       at 2 4 (Toff024 ∷ []) (pw1 c4 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @13213442: 4 steps
lem-pairs-at13213442 : Complete 4 → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-pairs-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-3142 ∷ Toff024 ∷ []) (sym (lem-P-box-at13213442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4) ▸
       at 4 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸ done


-- box-perm-4231: 3 steps
lem-box-perm-4231 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-box-perm-4231 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-pairs c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸
       at 0 1 (Bx0-4231 ∷ []) (lem-pairs-at13213442 c4) ▸ done


-- cQ @1331: 7 steps
lem-cQ-at1331 : Complete 4 → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at1331 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 c4) ▸
       at 0 2 (CCZ014 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @1331: 13 steps
lem-box-tQ-at1331 : Complete 4 → ⟪ (Bx0-3214 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at1331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3214 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx3-014 ∷ Toff023 ∷ CCZ023 ∷ Bx3-014 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw2 c4 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff301 ∷ Bx0-34 ∷ Toff301 ∷ CCZ013 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (pw2 c4 (CCZ013 ∷ Toff301 ∷ CZ34 ∷ Toff301 ∷ CCZ013 ∷ CZ34 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) (lw4 c4 (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 c4) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at1331 c4) ▸
       at 2 4 (Toff023 ∷ []) (lw4 c4 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- tP @1331: 7 steps
lem-tP-at1331 : Complete 4 → ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ
lem-tP-at1331 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Toff014 ∷ []) (Toff014 ∷ Toff023 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (lw4 c4 (Toff023 ∷ []) (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (pw2 c4 (Toff014 ∷ []) (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at1331 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff014 ∷ []) (pw2 c4 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff023 ∷ []) (lw4 c4 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @1331: 8 steps
lem-P-box-at1331 : Complete 4 → ⟪ (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-P-box-at1331 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Bx0-3214 ∷ Toff014 ∷ []) (Bx0-3214 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4) ▸
       at 0 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at1331 c4)) ▸
       at 1 2 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ14 ∷ Toff014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (sym (lem-tP-at1331 c4)) ▸
       at 4 3 (CCZ014 ∷ CZ14 ∷ []) (pw2 c4 (Toff014 ∷ CCZ014 ∷ Toff014 ∷ []) (CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 c4) ▸
       at 3 3 (CCZ014 ∷ []) (pw2 c4 (CZ14 ∷ CCZ014 ∷ CZ14 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3214 ∷ []) (sym (lem-box-tQ-at1331 c4)) ▸ done

