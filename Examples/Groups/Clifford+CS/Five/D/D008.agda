{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D008 where

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
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-tQ-at122441 ; lem-sym-bc)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at12243143 ; lem-sym-ab-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-pairs-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at132132 ; lem-tP-at132132)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX24-CCZ013 ; lem-comm-CZ24-TOFF013)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-CSd13-TOFF024 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R008 using (lem-comm-CS13-TOFF024)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-SWAP14-BOX⟨0·23⟩)
-- P-box @132132: 8 steps
lem-P-box-at132132 : Complete 4 → ⟪ (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-P-box-at132132 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) (Bx0-3124 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at132132 c4) ▸
       at 0 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at132132 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at132132 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ24 ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) (CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 c4) ▸
       at 3 3 (CCZ024 ∷ []) (pw1 c4 (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-3124 ∷ []) (sym (lem-box-tQ-at132132 c4)) ▸ done


-- VPQ @132132: 14 steps
lem-VPQ-at132132 : Complete 4 → ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 2 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 c4) ▸
       at 1 2 (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑)) ▸
       at 0 2 (CS24⁻ ∷ CS13⁻ ∷ []) (lw0 c4 (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at132132 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS13⁻ ∷ S0 ∷ Toff024 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS13⁻ ∷ []) (sym (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 2 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 c4) ▸
       at 3 2 (S0⁻ ∷ CS13⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 0 4 (Toff024 ∷ CCZ024 ∷ []) (pw1 c4 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff013 ∷ CCZ013 ∷ []) (lw4 c4 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @132132: 3 steps
lem-QVQ-at132132 : Complete 4 → ⟪ (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-QVQ-at132132 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ [])
  b0 = at 0 0 (Toff024 ∷ Toff024 ∷ []) (pw1 c4 [] (Toff024 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at132132 c4)) ▸
       at 4 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @132132: 12 steps
lem-box-cP-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) ⟫ʷ
lem-box-cP-at132132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-3124 ∷ []) (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff013 ∷ Bx3-024 ∷ Toff013 ∷ CCZ013 ∷ Bx3-024 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (pw1 c4 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx0-34 ∷ Toff302 ∷ CCZ023 ∷ Bx0-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (pw1 c4 (CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff024 ∷ Toff013 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-QVQ-at132132 c4) ▸
       at 1 2 (Toff024 ∷ Toff013 ∷ []) (lem-tP-at132132 c4) ▸
       at 2 2 [] (lw4 c4 (Toff013 ∷ Toff013 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @132132: 4 steps
lem-pairs-at132132 : Complete 4 → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-pairs-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Toff024 ∷ Bx0-3124 ∷ Toff024 ∷ []) (sym (lem-P-box-at132132 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at132132 c4) ▸
       at 4 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-tQ-at122441 c4)) ▸ done


-- box-perm-2431: 3 steps
lem-box-perm-2431 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-2431 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-pairs-at132132 c4) ▸ done


-- sym-ab @12243143: 18 steps
lem-sym-ab-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym-ab-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2413 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (lw4 c4 (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (pw2 c4 (CCZ013 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-43 ∷ []) (refl) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ [])
  b1 = at 2 6 (Bx4-013 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (lw4 c4 (CCZ012 ∷ Toff201 ∷ CZ23 ∷ Toff201 ∷ CCZ012 ∷ CZ23 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (pw2 c4 (CCZ013 ∷ []) (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-43 ∷ []) (refl) ▸
       at 10 1 (Bx0-43 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (Bx0-4213 ∷ [])
  b2 = at 5 6 (Bx4-013 ∷ []) (refl) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- box-perm-4213: 3 steps
lem-box-perm-4213 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-4213 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-sym-ab-at12243143 c4) ▸ done


-- CXbc-box @12243143: 17 steps
lem-CXbc-box-at12243143 : Complete 4 → ⟪ (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx0-2413 ∷ CX41 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX41 ∷ CCZ034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CCZ013 ∷ CX24 ∷ CS23 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at12243143 c4) ▸
       at 0 2 (Toff024 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ Toff024 ∷ []) (Toff024 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (pw2 c4 (CX41 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ034 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ Toff024 ∷ []) (Toff024 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ013 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX41 ∷ CCZ034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CCZ013 ∷ CX24 ∷ CS23 ∷ CX41 ∷ []) (Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS34⁻ ∷ []) (pw2 c4 (CS34⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 c4) ▸
       at 5 2 (CCZ013 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ234 ∷ []) (lw0 c4 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) (pw2 c4 (CX41 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX41 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX41 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-tQ-at12243143 c4)) ▸ done

  b2 : Chain (Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ []) (Bx0-2413 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX41 ∷ CCZ234 ∷ CX41 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @12243143: 18 steps
lem-CXcb-box-at12243143 : Complete 4 → ⟪ (CX14 ∷ Bx0-2413 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx0-2413 ∷ CX14 ∷ []) (Toff024 ∷ CCZ013 ∷ CX14 ∷ Toff012 ∷ CS13 ∷ CX21 ∷ Toff024 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ CCZ013 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at12243143 c4) ▸
       at 0 2 (Toff024 ∷ CX14 ∷ Toff012 ∷ []) (pw3 c4 (CX14 ∷ Toff024 ∷ []) (Toff024 ∷ CX14 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (lw4 c4 (Toff012 ∷ CCZ013 ∷ []) (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX14 ∷ []) (pw2 c4 (CX14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff024 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ Toff024 ∷ []) (Toff024 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff024 ∷ CX21 ∷ []) (pw3 c4 (CX21 ∷ Toff024 ∷ []) (Toff024 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 c4) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX14 ∷ Toff012 ∷ CS13 ∷ CX21 ∷ Toff024 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ CCZ013 ∷ CX14 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX21 ∷ []) (pw3 c4 (CX21 ∷ Toff024 ∷ []) (Toff024 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 c4) ▸
       at 5 5 (CCZ123 ∷ []) (lw4 c4 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff012 ∷ []) (pw3 c4 (Toff012 ∷ Toff024 ∷ []) (Toff024 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CX14 ∷ Toff012 ∷ []) (pw3 c4 (CX14 ∷ Toff024 ∷ []) (Toff024 ∷ CX14 ∷ Toff012 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX14 ∷ []) (pw3 c4 (CX14 ∷ Toff012 ∷ Toff012 ∷ []) (CX14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX14 ∷ []) (pw2 c4 (CX14 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX14 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ []) (Bx0-2413 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-2413 ∷ []) (sym (lem-box-tQ-at12243143 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (lw0 c4 (CX14 ∷ CCZ123 ∷ CX14 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @12243143: 11 steps
lem-SWbc-box-at12243143 : Complete 4 → ⟪ (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-SWbc-box-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (CX41 ∷ Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (lw0 c4 (Sw14 ∷ []) (CX41 ∷ CX14 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-CXbc-box-at12243143 c4) ▸
       at 3 2 (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-2413 ∷ CCZ123 ∷ []) (lem-CXcb-box-at12243143 c4) ▸
       at 4 2 (CX41 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ123 ∷ CX41 ∷ []) (CX41 ∷ CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX41 ∷ Bx0-2413 ∷ CX41 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (Bx0-2413 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-2413 ∷ CCZ234 ∷ []) (lem-CXbc-box-at12243143 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @12243143: 23 steps
lem-nat-SWbc-at12243143 : Complete 4 → ⟪ (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-nat-SWbc-at12243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ Sw14 ∷ CCZ012 ∷ Bx0-23 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff024 ∷ Bx2-013 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ024 ∷ []) (CCZ012 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff012 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff024 ∷ []) (Toff012 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ012 ∷ []) (CCZ024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff201 ∷ []) (Toff204 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ c4) ▸
       at 5 2 (Toff204 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff201 ∷ []) (Toff204 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ Sw14 ∷ CCZ012 ∷ Bx0-23 ∷ Toff024 ∷ CCZ024 ∷ Bx2-013 ∷ Sw14 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Sw14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ012 ∷ []) (CCZ024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ c4) ▸
       at 8 2 (Toff012 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff024 ∷ []) (Toff012 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ012 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ024 ∷ []) (CCZ012 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ012 ∷ Toff201 ∷ Bx0-23 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ012 ∷ []) (CCZ024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff204 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff201 ∷ []) (Toff204 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ c4) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Toff204 ∷ CCZ024 ∷ Bx0-23 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx0-23 ∷ Sw14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-23 ∷ Sw14 ∷ []) (Bx0-2143 ∷ [])
  b2 = at 13 2 (Toff204 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ Toff201 ∷ []) (Toff204 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ024 ∷ Sw14 ∷ []) (pw3 c4 (Sw14 ∷ CCZ012 ∷ []) (CCZ024 ∷ Sw14 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-23 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨0·23⟩ c4) ▸
       at 16 2 [] (lw0 c4 (Sw14 ∷ Sw14 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx2-043 ∷ []) (refl) ▸
       at 5 6 (Bx2-043 ∷ []) (refl) ▸
       at 0 6 (Bx0-2143 ∷ []) (refl) ▸ done


-- sym-bc @12243143: 2 steps
lem-sym-bc-at12243143 : Complete 4 → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-sym-bc-at12243143 c4 = run b0
  where
  b0 : Chain (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx0-2413 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at12243143 c4)) ▸
       at 0 3 (Bx0-2143 ∷ []) (lem-nat-SWbc-at12243143 c4) ▸ done


-- box-perm-2143: 3 steps
lem-box-perm-2143 : Complete 4 → ⟪ (Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-2143 c4 = run b0
  where
  b0 : Chain (Bx0-1234 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-pairs-at2332 c4) ▸
       at 0 1 (Bx0-2143 ∷ []) (lem-sym-bc-at12243143 c4) ▸ done


-- cQ @14233142: 7 steps
lem-cQ-at14233142 : Complete 4 → ⟪ (CCZ034 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ034 ∷ []) ⟫ʷ
lem-cQ-at14233142 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ012 ∷ CS04 ∷ []) (pw3 c4 (CS04 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 2 2 (CCZ012 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 0 2 (CCZ012 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ012 ∷ []) (CCZ012 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ034 ∷ []) (pw1 c4 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @14233142: 13 steps
lem-box-tQ-at14233142 : Complete 4 → ⟪ (Bx0-4312 ∷ []) ⟫ʷ ≈ ⟪ (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at14233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4312 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-012 ∷ Toff034 ∷ CCZ034 ∷ Bx4-012 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (pw3 c4 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-42 ∷ Toff401 ∷ CCZ014 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ034 ∷ CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (pw3 c4 (CCZ014 ∷ Toff401 ∷ CZ24 ∷ Toff401 ∷ CCZ014 ∷ CZ24 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) (pw1 c4 (CCZ034 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ CZ34 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ034 ∷ []) (lem-cQ-at14233142 c4) ▸
       at 2 4 (Toff034 ∷ []) (pw1 c4 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ CCZ034 ∷ []) (Toff034 ∷ []) tt tt Eq.refl) ▸ done

