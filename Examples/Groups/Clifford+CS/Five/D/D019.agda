{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D019 where

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
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box-tQ-at043043)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CS03-TOFF412 ; lem-comm-TOFF401-CSd23)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CSd03-TOFF412 ; lem-comm-SWAP02-BOX⟨4·13⟩)
-- cQ @0330: 7 steps
lem-cQ-at0330 : Complete 4 → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0330: 13 steps
lem-box-tQ-at0330 : Complete 4 → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1204 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-304 ∷ Toff312 ∷ CCZ123 ∷ Bx1-304 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-14 ∷ Toff103 ∷ CCZ013 ∷ Bx3-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (pw2 c4 (CCZ013 ∷ Toff103 ∷ CZ14 ∷ Toff103 ∷ CCZ013 ∷ CZ14 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (lw4 c4 (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 c4) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at0330 c4) ▸
       at 2 4 (Toff312 ∷ []) (lw4 c4 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @043043: 17 steps
lem-CXbc-box-at043043 : Complete 4 → ⟪ (CX20 ∷ Bx4-1203 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx4-1203 ∷ CX20 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX20 ∷ CCZ234 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 0 2 (Toff412 ∷ CX20 ∷ []) (pw3 c4 (CX20 ∷ Toff412 ∷ []) (Toff412 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (pw1 c4 (CX20 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff412 ∷ CCZ234 ∷ CCZ123 ∷ []) (lw0 c4 (CCZ234 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ234 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff412 ∷ CX20 ∷ []) (pw3 c4 (CX20 ∷ Toff412 ∷ []) (Toff412 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ034 ∷ CS13 ∷ []) (pw2 c4 (CS13 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX20 ∷ CCZ234 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CX20 ∷ []) (Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CX20 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS23⁻ ∷ []) (pw1 c4 (CS23⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 c4) ▸
       at 5 2 (CCZ034 ∷ CS23 ∷ []) (pw1 c4 (CS23 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ123 ∷ []) (lw4 c4 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) (pw1 c4 (CX20 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX20 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX20 ∷ []) (pw1 c4 (CX20 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX20 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸ done

  b2 : Chain (Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CX20 ∷ []) (Bx4-1203 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (lw4 c4 (CX20 ∷ CCZ123 ∷ CX20 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @043043: 18 steps
lem-CXcb-box-at043043 : Complete 4 → ⟪ (CX02 ∷ Bx4-1203 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx4-1203 ∷ CX02 ∷ []) (Toff412 ∷ CCZ034 ∷ CX02 ∷ Toff401 ∷ CS03 ∷ CX10 ∷ Toff412 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ CCZ034 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 0 2 (Toff412 ∷ CX02 ∷ Toff401 ∷ []) (pw3 c4 (CX02 ∷ Toff412 ∷ []) (Toff412 ∷ CX02 ∷ Toff401 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) (pw2 c4 (Toff401 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff401 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CX02 ∷ []) (pw1 c4 (CX02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (lw4 c4 (CCZ013 ∷ []) (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff412 ∷ CS13 ∷ []) (lw0 c4 (CS13 ∷ Toff412 ∷ []) (Toff412 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff412 ∷ CX10 ∷ []) (pw3 c4 (CX10 ∷ Toff412 ∷ []) (Toff412 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 c4) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ CX02 ∷ Toff401 ∷ CS03 ∷ CX10 ∷ Toff412 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ CCZ034 ∷ CX02 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX02 ∷ CCZ013 ∷ CX02 ∷ [])
  b1 = at 5 2 (Toff412 ∷ CX10 ∷ []) (pw3 c4 (CX10 ∷ Toff412 ∷ []) (Toff412 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 c4) ▸
       at 5 5 (CCZ013 ∷ []) (lw4 c4 (CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff412 ∷ Toff401 ∷ []) (pw3 c4 (Toff401 ∷ Toff412 ∷ []) (Toff412 ∷ Toff401 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff412 ∷ CX02 ∷ Toff401 ∷ []) (pw3 c4 (CX02 ∷ Toff412 ∷ []) (Toff412 ∷ CX02 ∷ Toff401 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX02 ∷ []) (pw3 c4 (CX02 ∷ Toff401 ∷ Toff401 ∷ []) (CX02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (pw2 c4 (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CX02 ∷ []) (pw1 c4 (CX02 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX02 ∷ CCZ013 ∷ CX02 ∷ []) (Bx4-1203 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (lw4 c4 (CX02 ∷ CCZ013 ∷ CX02 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @043043: 11 steps
lem-SWbc-box-at043043 : Complete 4 → ⟪ (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-SWbc-box-at043043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (CX20 ∷ Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (lw4 c4 (Sw02 ∷ []) (CX20 ∷ CX02 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX20 ∷ CX02 ∷ CX20 ∷ []) (lw4 c4 (Sw02 ∷ []) (CX20 ∷ CX02 ∷ CX20 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx4-1203 ∷ CCZ123 ∷ []) (lem-CXbc-box-at043043 c4) ▸
       at 3 2 (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx4-1203 ∷ CCZ013 ∷ []) (lem-CXcb-box-at043043 c4) ▸
       at 4 2 (CX20 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX20 ∷ Bx4-1203 ∷ CX20 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ []) (Bx4-1203 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx4-1203 ∷ CCZ123 ∷ []) (lem-CXbc-box-at043043 c4) ▸
       at 1 2 [] (lw4 c4 (CCZ123 ∷ CCZ123 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @043043: 23 steps
lem-nat-SWbc-at043043 : Complete 4 → ⟪ (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-nat-SWbc-at043043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ Sw02 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ Sw02 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff412 ∷ Bx1-403 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ []) (refl) ▸
       at 0 2 (CCZ014 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ124 ∷ []) (CCZ014 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff401 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff412 ∷ []) (Toff401 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ014 ∷ []) (CCZ124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff104 ∷ []) (Toff124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ c4) ▸
       at 5 2 (Toff124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff104 ∷ []) (Toff124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ Sw02 ∷ CCZ014 ∷ Bx4-13 ∷ Toff412 ∷ CCZ124 ∷ Bx1-403 ∷ Sw02 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Sw02 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Sw02 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ014 ∷ []) (CCZ124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ c4) ▸
       at 8 2 (Toff401 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff412 ∷ []) (Toff401 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ014 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ124 ∷ []) (CCZ014 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ014 ∷ Toff104 ∷ Bx4-13 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ014 ∷ []) (CCZ124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff104 ∷ []) (Toff124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ c4) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Sw02 ∷ Toff104 ∷ CCZ014 ∷ Bx4-13 ∷ Sw02 ∷ []) (Bx4-1023 ∷ [])
  b2 = at 13 2 (Toff124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ Toff104 ∷ []) (Toff124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ124 ∷ Sw02 ∷ []) (pw3 c4 (Sw02 ∷ CCZ014 ∷ []) (CCZ124 ∷ Sw02 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx4-13 ∷ Sw02 ∷ []) (lem-comm-SWAP02-BOX⟨4·13⟩ c4) ▸
       at 16 2 [] (lw4 c4 (Sw02 ∷ Sw02 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx1-423 ∷ []) (refl) ▸
       at 5 6 (Bx1-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-1023 ∷ []) (refl) ▸ done


-- sym-bc @043043: 2 steps
lem-sym-bc-at043043 : Complete 4 → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-sym-bc-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Sw02 ∷ Bx4-1203 ∷ Sw02 ∷ []) (sym (lem-SWbc-box-at043043 c4)) ▸
       at 0 3 (Bx4-1023 ∷ []) (lem-nat-SWbc-at043043 c4) ▸ done


-- box-perm-1324 @043043: 1 steps
lem-box-perm-1324-at043043 : Complete 4 → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-1324-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-bc-at043043 c4) ▸ done


-- cQ @04203243: 7 steps
lem-cQ-at04203243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at04203243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ234 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS04⁻ ∷ []) (pw1 c4 (CS04⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ014 ∷ []) (pw2 c4 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- tP @04203243: 7 steps
lem-tP-at04203243 : Complete 4 → ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-tP-at04203243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Toff423 ∷ []) (Toff423 ∷ Toff401 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (pw2 c4 (Toff401 ∷ []) (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (lw0 c4 (Toff423 ∷ []) (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw0 c4 (K4⁻ ∷ K4 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ234 ∷ CCZ014 ∷ []) (lem-cQ-at04203243 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (lw0 c4 [] (K4⁻ ∷ K4 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff423 ∷ []) (lw0 c4 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff401 ∷ []) (pw2 c4 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (Toff401 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @04203243: 14 steps
lem-VPQ-at04203243 : Complete 4 → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (CS23⁻ ∷ CS01⁻ ∷ S4 ∷ Toff423 ∷ Toff401 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (pw2 c4 (Toff401 ∷ CCZ014 ∷ []) (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (lw0 c4 (Toff423 ∷ CCZ234 ∷ []) (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS23⁻ ∷ S4⁻ ∷ []) (sym (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS23⁻ ∷ Toff401 ∷ []) (lem-comm-TOFF401-CSd23 c4) ▸
       at 1 2 (CS23⁻ ∷ S4 ∷ []) (sym (c₄ ((CS • CS • CS) ↑ ↑) (S))) ▸
       at 0 2 (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS)) ▸
       at 4 2 [] (lw0 c4 (S4⁻ ∷ S4 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS01⁻ ∷ S4 ∷ Toff423 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (lw0 c4 [] (S4⁻ ∷ S4 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S4 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑ ↑)) ▸
       at 2 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸
       at 3 2 (S4⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑)) ▸
       at 0 4 (Toff423 ∷ CCZ234 ∷ []) (lw0 c4 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff401 ∷ CCZ014 ∷ []) (pw2 c4 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff401 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @04203243: 3 steps
lem-QVQ-at04203243 : Complete 4 → ⟪ (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-QVQ-at04203243 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ [])
  b0 = at 0 0 (Toff423 ∷ Toff423 ∷ []) (lw0 c4 [] (Toff423 ∷ Toff423 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at04203243 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ234 ∷ CCZ234 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @04203243: 12 steps
lem-box-cP-at04203243 : Complete 4 → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ
lem-box-cP-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1023 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff423 ∷ Toff401 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-QVQ-at04203243 c4) ▸
       at 1 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸
       at 2 2 [] (pw2 c4 (Toff401 ∷ Toff401 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym-ab @04203243: 18 steps
lem-sym-ab-at04203243 : Complete 4 → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-sym-ab-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx4-1023 ∷ []) (CCZ014 ∷ Toff401 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff401 ∷ Bx1-423 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (lw0 c4 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (pw1 c4 (CCZ234 ∷ []) (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx4-03 ∷ []) (refl) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff401 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx1-423 ∷ []) (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ [])
  b1 = at 2 6 (Bx0-423 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-13 ∷ Toff124 ∷ CCZ124 ∷ Bx4-13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (lw0 c4 (CCZ124 ∷ Toff124 ∷ CZ13 ∷ Toff124 ∷ CCZ124 ∷ CZ13 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (pw1 c4 (CCZ234 ∷ []) (CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx4-03 ∷ []) (refl) ▸
       at 10 1 (Bx4-03 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (Bx4-0123 ∷ [])
  b2 = at 5 6 (Bx0-423 ∷ []) (refl) ▸
       at 0 6 (Bx4-0123 ∷ []) (refl) ▸ done


-- box-perm-3124 @043043: 2 steps
lem-box-perm-3124-at043043 : Complete 4 → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-box-perm-3124-at043043 c4 = run b0
  where
  b0 : Chain (Bx4-1203 ∷ []) (Bx4-0123 ∷ [])
  b0 = at 0 1 (Bx4-1023 ∷ []) (lem-sym-bc-at043043 c4) ▸
       at 0 1 (Bx4-0123 ∷ []) (lem-sym-ab-at04203243 c4) ▸ done


-- tP @0330: 7 steps
lem-tP-at0330 : Complete 4 → ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-tP-at0330 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (lw4 c4 (Toff312 ∷ []) (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (pw1 c4 (Toff304 ∷ []) (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at0330 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff304 ∷ []) (pw1 c4 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (Toff304 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff312 ∷ []) (lw4 c4 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (Toff312 ∷ []) tt tt Eq.refl) ▸ done

