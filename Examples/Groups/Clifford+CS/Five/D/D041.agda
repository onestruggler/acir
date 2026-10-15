{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D041 where

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
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-box-cP-at0314203142 ; lem-sym-ab-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-box-tQ-at0214213043)
open import Examples.Groups.Clifford+CS.Five.D.D039 using (lem-box-tQ-at0314213042 ; lem-cQ-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.D040 using (lem-CXbc-box-at0314203142 ; lem-box-box-4-at0310243142 ; lem-box-perm-1324-at0314213042 ; lem-box-perm-3124-at0314213042 ; lem-box-perm-3421-at0213203441 ; lem-box-perm-4312-at0214213043 ; lem-box-tQ-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CSd12-TOFF304)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS14-CCZ023 ; lem-comm-CSd14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CX41-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R016 using (lem-comm-CS02-TOFF314 ; lem-comm-CZ02-TOFF314)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-CS02-CCZ134 ; lem-comm-CS12-TOFF304 ; lem-comm-CSd02-CCZ134 ; lem-comm-CSd14-TOFF302 ; lem-comm-CX04-TOFF312 ; lem-comm-CZ14-TOFF302 ; lem-comm-TOFF314-CSd02)
-- CXcb-box @0314203142: 18 steps
lem-CXcb-box-at0314203142 : Complete 4 → ⟪ (CX10 ∷ Bx3-4012 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx3-4012 ∷ CX10 ∷ []) (Toff304 ∷ CCZ123 ∷ CX10 ∷ Toff314 ∷ CS12 ∷ CX41 ∷ Toff304 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ123 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 0 2 (Toff304 ∷ CX10 ∷ Toff314 ∷ []) (pw2 c4 (CX10 ∷ Toff304 ∷ []) (Toff304 ∷ CX10 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ Toff314 ∷ CCZ124 ∷ []) (lw0 c4 (Toff314 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff314 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff304 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff304 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ Toff304 ∷ []) (Toff304 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 c4) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ CX10 ∷ Toff314 ∷ CS12 ∷ CX41 ∷ Toff304 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ CCZ123 ∷ CX10 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff304 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ Toff304 ∷ []) (Toff304 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 c4) ▸
       at 5 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff304 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ Toff304 ∷ []) (Toff304 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff304 ∷ CX10 ∷ Toff314 ∷ []) (pw2 c4 (CX10 ∷ Toff304 ∷ []) (Toff304 ∷ CX10 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX10 ∷ []) (pw2 c4 (CX10 ∷ Toff314 ∷ Toff314 ∷ []) (CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CCZ124 ∷ []) (lw0 c4 (CCZ124 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX10 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ []) (Bx3-4012 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (pw3 c4 (CX10 ∷ CCZ124 ∷ CX10 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0314203142: 11 steps
lem-SWbc-box-at0314203142 : Complete 4 → ⟪ (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-SWbc-box-at0314203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (CX01 ∷ Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (lw4 c4 (Sw01 ∷ []) (CX01 ∷ CX10 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (lw4 c4 (Sw01 ∷ []) (CX01 ∷ CX10 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0314203142 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx3-4012 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0314203142 c4) ▸
       at 4 2 (CX01 ∷ CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX01 ∷ Bx3-4012 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (Bx3-4012 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (pw3 c4 (CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx3-4012 ∷ CCZ024 ∷ []) (lem-CXbc-box-at0314203142 c4) ▸
       at 1 2 [] (pw1 c4 (CCZ024 ∷ CCZ024 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0314203142: 23 steps
lem-nat-SWbc-at0314203142 : Complete 4 → ⟪ (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-nat-SWbc-at0314203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ Sw01 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff304 ∷ Bx4-312 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff314 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 2 2 (CCZ034 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff403 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 5 2 (Toff403 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ Sw01 ∷ CCZ134 ∷ Bx3-42 ∷ Toff304 ∷ CCZ034 ∷ Bx4-312 ∷ Sw01 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Sw01 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ034 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 8 2 (Toff314 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff304 ∷ []) (Toff314 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ134 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ034 ∷ []) (CCZ134 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ134 ∷ Toff413 ∷ Bx3-42 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ []) (refl) ▸
       at 10 2 (CCZ034 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff403 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Sw01 ∷ Toff413 ∷ CCZ134 ∷ Bx3-42 ∷ Sw01 ∷ []) (Bx3-4102 ∷ [])
  b2 = at 13 2 (Toff403 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ Toff413 ∷ []) (Toff403 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ034 ∷ Sw01 ∷ []) (pw2 c4 (Sw01 ∷ CCZ134 ∷ []) (CCZ034 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx3-42 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 16 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx4-302 ∷ []) (refl) ▸
       at 5 6 (Bx4-302 ∷ []) (refl) ▸
       at 0 6 (Bx3-4102 ∷ []) (refl) ▸ done


-- sym-bc @0314203142: 2 steps
lem-sym-bc-at0314203142 : Complete 4 → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-sym-bc-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-4012 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0314203142 c4)) ▸
       at 0 3 (Bx3-4102 ∷ []) (lem-nat-SWbc-at0314203142 c4) ▸ done


-- box-perm-2314 @0310243142: 2 steps
lem-box-perm-2314-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-box-perm-2314-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸
       at 0 1 (Bx3-4102 ∷ []) (lem-sym-bc-at0314203142 c4) ▸ done


-- F0-B @14213243: 62 steps
lem-F0-B-at14213243 : Complete 4 → ⟪ (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Bx3-4102 ∷ []) ⟫ʷ
lem-F0-B-at14213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CZ02 ∷ CCZ014 ∷ CCZ023 ∷ CZ02 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ Toff314 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ Toff214 ∷ []) (Toff214 ∷ Toff314 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CZ02 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ02 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ Toff214 ∷ []) (Toff214 ∷ Toff314 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ023 ∷ CZ02 ∷ []) (lw4 c4 (CX23 ∷ CCZ023 ∷ CX23 ∷ []) (CCZ023 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ CZ02 ∷ CCZ014 ∷ []) (pw3 c4 (CZ02 ∷ Toff214 ∷ []) (Toff214 ∷ CZ02 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff314 ∷ CCZ014 ∷ []) (pw2 c4 (CCZ014 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 c4) ▸ done

  b1 : Chain (Toff214 ∷ Toff314 ∷ CCZ023 ∷ Toff214 ∷ Toff314 ∷ CZ02 ∷ CCZ014 ∷ CCZ023 ∷ CZ02 ∷ []) (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b1 = at 5 2 (CCZ014 ∷ CZ02 ∷ []) (pw3 c4 (CZ02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CZ02 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ023 ∷ []) (lw4 c4 (CZ02 ∷ CCZ023 ∷ CZ02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff314 ∷ Toff214 ∷ []) (lw0 c4 (Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 4 0 (CCZ023 ∷ CCZ023 ∷ []) (lw4 c4 [] (CCZ023 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 1 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff214 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b2 = at 6 2 (CCZ034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 0 2 (CCZ034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ CCZ034 ∷ []) (CCZ034 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 1 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ034 ∷ Toff214 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ K2 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b3 = at 1 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff214 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (pw2 c4 (Toff314 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ034 ∷ K2⁻ ∷ []) (pw1 c4 (K2⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 c4) ▸
       at 4 2 (CCZ034 ∷ CX41 ∷ []) (pw2 c4 (CX41 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX41 ∷ []) tt tt Eq.refl) ▸ done

  b4 : Chain (CCZ034 ∷ Toff312 ∷ K2 ∷ CS12 ∷ CCZ034 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b4 = at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 c4) ▸
       at 2 2 (CCZ034 ∷ K2 ∷ []) (pw1 c4 (K2 ∷ CCZ034 ∷ []) (CCZ034 ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 3 7 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff312 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 7 2 (Toff312 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸ done

  b5 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (Bx3-4102 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ [])
  b5 = at 5 2 (Toff312 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff312 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (lw0 c4 (Toff214 ∷ Toff312 ∷ []) (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (Toff214 ∷ []) (lw0 c4 (Toff214 ∷ Toff314 ∷ Toff314 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 0 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 2 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸ done

  b6 : Chain (Bx3-4102 ∷ Toff214 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ023 ∷ Toff214 ∷ CCZ014 ∷ CCZ023 ∷ []) (Bx3-4102 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b6 = at 6 2 (CCZ023 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CCZ023 ∷ CX04 ∷ []) (pw1 c4 (CX04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 c4) ▸
       at 3 2 (CCZ023 ∷ CX04 ∷ []) (pw1 c4 (CX04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 c4) ▸
       at 3 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ CCZ014 ∷ []) (pw3 c4 (CCZ014 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (pw2 c4 (CCZ014 ∷ CCZ014 ∷ []) [] tt tt Eq.refl) ▸ done

  b7 : Chain (Bx3-4102 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ [])
  b7 = at 1 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-box-perm-3124-at0314213042 c4) ▸
       at 1 1 (Bx2-3041 ∷ []) (lem-box-perm-4312-at0214213043 c4) ▸
       at 0 2 (Bx2-3041 ∷ Bx3-0412 ∷ []) (lem-box-box-4-at0310243142 c4) ▸
       at 0 1 (Bx2-4103 ∷ []) (lem-box-perm-3421-at0213203441 c4) ▸
       at 1 1 (Bx3-4102 ∷ []) (lem-box-perm-2314-at0310243142 c4) ▸ done


-- tP @0314213042: 7 steps
lem-tP-at0314213042 : Complete 4 → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (lw0 c4 (Toff314 ∷ []) (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (lw4 c4 (Toff302 ∷ []) (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K3⁻ ∷ K3 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213042 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (lw4 c4 [] (K3⁻ ∷ K3 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff302 ∷ []) (lw4 c4 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (Toff302 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff314 ∷ []) (lw0 c4 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (Toff314 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @0314213042: 14 steps
lem-VPQ-at0314213042 : Complete 4 → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (lw0 c4 (Toff314 ∷ CCZ134 ∷ []) (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (lw4 c4 (Toff302 ∷ CCZ023 ∷ []) (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS02⁻ ∷ S3⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))) ▸
       at 2 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 c4) ▸
       at 1 2 (CS02⁻ ∷ S3 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))) ▸
       at 0 2 (CS02⁻ ∷ CS14⁻ ∷ []) (pw3 c4 (CS14⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S3⁻ ∷ S3 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (lw4 c4 [] (S3⁻ ∷ S3 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S3 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ S3 ∷ []) (S3 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 c4) ▸
       at 3 2 (S3⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff302 ∷ CCZ023 ∷ []) (lw4 c4 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff314 ∷ CCZ134 ∷ []) (lw0 c4 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0314213042: 3 steps
lem-QVQ-at0314213042 : Complete 4 → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at0314213042 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (lw4 c4 [] (Toff302 ∷ Toff302 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at0314213042 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0314213042: 12 steps
lem-box-cP-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4102 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-302 ∷ Toff314 ∷ CCZ134 ∷ Bx4-302 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (pw1 c4 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-42 ∷ Toff403 ∷ CCZ034 ∷ Bx3-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (pw1 c4 (CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at0314213042 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸
       at 2 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸ done


-- CSdu-box-3 @0314213042: 17 steps
lem-CSdu-box-3-at0314213042 : Complete 4 → ⟪ (CS03⁻ ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03⁻ ∷ Bx3-4102 ∷ []) (CCZ134 ∷ Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CS02 ∷ CCZ134 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Toff302 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4) ▸
       at 0 2 (CCZ134 ∷ CS03⁻ ∷ []) (pw2 c4 (CS03⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CS03⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ134 ∷ CS23 ∷ []) (lw0 c4 (CS23 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ134 ∷ CX30 ∷ []) (pw2 c4 (CX30 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 c4) ▸
       at 5 2 (CCZ134 ∷ CX30 ∷ []) (pw2 c4 (CX30 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX30 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CS02 ∷ CCZ134 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS03⁻ ∷ [])
  b1 = at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 c4) ▸
       at 5 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 c4) ▸
       at 2 2 (CCZ134 ∷ CS03⁻ ∷ []) (pw2 c4 (CS03⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ Toff302 ∷ []) (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff302 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CS03⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CS02⁻ ∷ CZ02 ∷ CCZ023 ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS03⁻ ∷ []) (Bx3-4102 ∷ CS03⁻ ∷ [])
  b2 = at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-cP-at0314213042 c4)) ▸ done


-- F0-R @14213243: 11 steps
lem-F0-R-at14213243 : Complete 4 → ⟪ (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ []) ⟫ʷ
lem-F0-R-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ [])
  b0 = at 0 2 (Toff314 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ Toff314 ∷ []) (Toff314 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CS03 ∷ CS02 ∷ CCZ023 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CS03 ∷ []) (CS03 ∷ CS02 ∷ CCZ023 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff314 ∷ CX23 ∷ []) (lw0 c4 (CX23 ∷ Toff314 ∷ []) (Toff314 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CX23 ∷ []) (lw4 c4 (CX23 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS02⁻ ∷ CCZ023 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 c4) ▸
       at 4 3 (CS03⁻ ∷ []) (lw4 c4 (CS02 ∷ CS03⁻ ∷ CS02⁻ ∷ []) (CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Toff314 ∷ CS03 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CS03⁻ ∷ CCZ023 ∷ CX23 ∷ []) (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸
       at 3 2 (CS03⁻ ∷ Bx3-4102 ∷ []) (sym (lem-CSdu-box-3-at0314213042 c4)) ▸ done


-- CSu-box-3 @0314213042: 17 steps
lem-CSu-box-3-at0314213042 : Complete 4 → ⟪ (CS03 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3-at0314213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ Bx3-4102 ∷ []) (CCZ134 ∷ Toff302 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CCZ134 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Toff302 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4) ▸
       at 0 2 (CCZ134 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) (lw4 c4 (CS03 ∷ Toff302 ∷ []) (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ134 ∷ CS23 ∷ []) (lw0 c4 (CS23 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ134 ∷ CX30 ∷ []) (pw2 c4 (CX30 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX30 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 c4) ▸
       at 5 2 (CCZ134 ∷ CX30 ∷ []) (pw2 c4 (CX30 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX30 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff302 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CCZ134 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS03 ∷ [])
  b1 = at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 c4) ▸
       at 5 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 c4) ▸
       at 2 2 (CCZ134 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ Toff302 ∷ []) (Toff302 ∷ CZ02 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff302 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ Toff302 ∷ []) (Toff302 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) (lw4 c4 (CS03 ∷ Toff302 ∷ []) (Toff302 ∷ CS03 ∷ CS02 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS03 ∷ []) (lw4 c4 (CS03 ∷ CS02 ∷ CCZ023 ∷ CS02 ∷ CZ02 ∷ CCZ023 ∷ []) (CS03 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS03 ∷ []) (Bx3-4102 ∷ CS03 ∷ [])
  b2 = at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-cP-at0314213042 c4)) ▸ done


-- t-cP @0314213042: 5 steps
lem-t-cP-at0314213042 : Complete 4 → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-t-cP-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 2 (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) (lw0 c4 (Toff314 ∷ CCZ134 ∷ []) (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸
       at 2 3 (CCZ134 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ CZ14 ∷ CCZ134 ∷ []) (CCZ134 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4) ▸ done


-- box2 @0314213042: 11 steps
lem-box2-at0314213042 : Complete 4 → ⟪ (Bx3-4102 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0314213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4102 ∷ Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (lw0 c4 [] (Toff314 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) (lem-t-cP-at0314213042 c4) ▸
       at 5 4 (Bx3-4102 ∷ []) (sym (lem-box-cP-at0314213042 c4)) ▸
       at 5 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 4 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) []
  b1 = at 2 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸
       at 0 2 [] (lw0 c4 (Toff314 ∷ Toff314 ∷ []) [] tt tt Eq.refl) ▸ done


-- CXbc-box @0214213043: 17 steps
lem-CXbc-box-at0214213043 : Complete 4 → ⟪ (CX10 ∷ Bx2-4103 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at0214213043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx2-4103 ∷ CX10 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CX10 ∷ CCZ123 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ CX10 ∷ []) (pw3 c4 (CX10 ∷ Toff214 ∷ []) (Toff214 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (lw4 c4 (CX10 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ123 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ CX10 ∷ []) (pw3 c4 (CX10 ∷ Toff214 ∷ []) (Toff214 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸ done

  b1 : Chain (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CX10 ∷ CCZ123 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX10 ∷ []) (Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 5 2 (CCZ023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (lw4 c4 (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) (lw4 c4 (CX10 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX10 ∷ CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX10 ∷ []) (lw4 c4 (CX10 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX10 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸ done

  b2 : Chain (Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ []) (Bx2-4103 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (pw2 c4 (CX10 ∷ CCZ134 ∷ CX10 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done

