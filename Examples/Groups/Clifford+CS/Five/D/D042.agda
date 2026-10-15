{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D042 where

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
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at243243 ; lem-box-tQ-at243243 ; lem-tP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-box-cP-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-pairs-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-sym-ab-at032032 ; lem-sym-bc-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-box-tQ-at0214213043)
open import Examples.Groups.Clifford+CS.Five.D.D039 using (lem-box-perm-2314-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D040 using (lem-box-perm-1324-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.D041 using (lem-CSdu-box-3-at0314213042 ; lem-CSu-box-3-at0314213042 ; lem-CXbc-box-at0214213043 ; lem-F0-B-at14213243 ; lem-F0-R-at14213243 ; lem-box2-at0314213042)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX04-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CSd03-TOFF214)
open import Examples.Groups.Clifford+CS.Five.D.R017 using (lem-comm-CS03-TOFF214 ; lem-comm-CX04-TOFF312 ; lem-comm-CZ23-TOFF014 ; lem-comm-TOFF214-CS03)
-- CXcb-box @0214213043: 18 steps
lem-CXcb-box-at0214213043 : Complete 4 → ⟪ (CX01 ∷ Bx2-4103 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0214213043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx2-4103 ∷ CX01 ∷ []) (Toff214 ∷ CCZ023 ∷ CX01 ∷ Toff204 ∷ CS03 ∷ CX40 ∷ Toff214 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ023 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ CX01 ∷ Toff204 ∷ []) (pw3 c4 (CX01 ∷ Toff214 ∷ []) (Toff214 ∷ CX01 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) (pw1 c4 (Toff204 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff204 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff214 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff214 ∷ []) (Toff214 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff214 ∷ CX40 ∷ []) (pw3 c4 (CX40 ∷ Toff214 ∷ []) (Toff214 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 c4) ▸ done

  b1 : Chain (Toff214 ∷ CCZ023 ∷ CX01 ∷ Toff204 ∷ CS03 ∷ CX40 ∷ Toff214 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ CCZ023 ∷ CX01 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff214 ∷ CX40 ∷ []) (pw3 c4 (CX40 ∷ Toff214 ∷ []) (Toff214 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 c4) ▸
       at 5 5 (CCZ034 ∷ []) (pw1 c4 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ Toff204 ∷ []) (pw3 c4 (Toff204 ∷ Toff214 ∷ []) (Toff214 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ CX01 ∷ Toff204 ∷ []) (pw3 c4 (CX01 ∷ Toff214 ∷ []) (Toff214 ∷ CX01 ∷ Toff204 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX01 ∷ []) (pw3 c4 (CX01 ∷ Toff204 ∷ Toff204 ∷ []) (CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX01 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ []) (Bx2-4103 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ CX01 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0214213043: 11 steps
lem-SWbc-box-at0214213043 : Complete 4 → ⟪ (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-SWbc-box-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (CX10 ∷ Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (lw4 c4 (Sw01 ∷ []) (CX10 ∷ CX01 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (lw4 c4 (Sw01 ∷ []) (CX10 ∷ CX01 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx2-4103 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214213043 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx2-4103 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0214213043 c4) ▸
       at 4 2 (CX10 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX10 ∷ Bx2-4103 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (Bx2-4103 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-4103 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214213043 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0214213043: 23 steps
lem-nat-SWbc-at0214213043 : Complete 4 → ⟪ (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214213043 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ Sw01 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff204 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 2 2 (CCZ124 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff412 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff412 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ Sw01 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ Sw01 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Sw01 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ124 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff204 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff214 ∷ []) (Toff204 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 10 2 (CCZ124 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff412 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Sw01 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Sw01 ∷ []) (Bx2-4013 ∷ [])
  b2 = at 13 2 (Toff412 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff402 ∷ []) (Toff412 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ124 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx4-213 ∷ []) (refl) ▸
       at 5 6 (Bx4-213 ∷ []) (refl) ▸
       at 0 6 (Bx2-4013 ∷ []) (refl) ▸ done


-- sym-bc @0214213043: 2 steps
lem-sym-bc-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-sym-bc-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-4103 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0214213043 c4)) ▸
       at 0 3 (Bx2-4013 ∷ []) (lem-nat-SWbc-at0214213043 c4) ▸ done


-- sym-ab @0214203143: 18 steps
lem-sym-ab-at0214203143 : Complete 4 → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym-ab-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-4013 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw0 c4 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx2-03 ∷ []) (refl) ▸
       at 7 1 (Bx2-03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ [])
  b1 = at 2 6 (Bx0-213 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (lw0 c4 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (lw4 c4 (CCZ123 ∷ []) (CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx2-03 ∷ []) (refl) ▸
       at 10 1 (Bx2-03 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (Bx2-0413 ∷ [])
  b2 = at 5 6 (Bx0-213 ∷ []) (refl) ▸
       at 0 6 (Bx2-0413 ∷ []) (refl) ▸ done


-- box-perm-3124 @0214213043: 2 steps
lem-box-perm-3124-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-3124-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-bc-at0214213043 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸ done


-- CXuA-S @14213243: 44 steps
lem-CXuA-S-at14213243 : Complete 4 → ⟪ (CX23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CX23 ∷ []) ⟫ʷ
lem-CXuA-S-at14213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX23 ∷ Sb2-0-41-3 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Bx3-4102 ∷ CS03⁻ ∷ CX23 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (Bx2-4103 ∷ []) (lem-box-perm-2314-at0210243143 c4) ▸
       at 2 0 (CX23 ∷ CX23 ∷ []) (lw4 c4 [] (CX23 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-4103 ∷ Bx3-4102 ∷ []) (lem-F0-B-at14213243 c4) ▸
       at 2 5 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx3-4102 ∷ CX23 ∷ []) (lem-F0-R-at14213243 c4) ▸
       at 5 2 (Bx3-4102 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at0314213042 c4) ▸ done

  b1 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ Bx3-4102 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03⁻ ∷ CX23 ∷ [])
  b1 = at 5 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (pw2 c4 (Toff314 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 10 2 (Toff312 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 8 2 (Toff312 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸ done

  b2 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ CS03 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ Bx3-4102 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b2 = at 6 2 (Toff312 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 7 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 6 3 (CCZ034 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 4 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 3 2 (Bx3-4102 ∷ CS03 ∷ []) (lem-CSu-box-3-at0314213042 c4) ▸ done

  b3 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ Toff314 ∷ Bx3-4102 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b3 = at 3 1 (Bx3-4012 ∷ []) (lem-box-perm-1324-at0314213042 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (pw2 c4 (Toff314 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff312 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸
       at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 c4) ▸ done

  b4 : Chain (Bx2-4103 ∷ Bx3-4102 ∷ CCZ034 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ [])
  b4 = at 4 2 (Toff312 ∷ CS14 ∷ []) (lw0 c4 (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 5 5 (CCZ014 ∷ []) (pw2 c4 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff312 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CCZ034 ∷ Toff314 ∷ []) (pw2 c4 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff312 ∷ Toff314 ∷ []) (lw0 c4 (Toff314 ∷ Toff312 ∷ []) (Toff312 ∷ Toff314 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 2 1 (Bx3-4102 ∷ []) (sym (lem-box-perm-1324-at0314213042 c4)) ▸
       at 1 2 [] (lem-box2-at0314213042 c4) ▸ done

  b5 : Chain (Bx2-4103 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX23 ∷ []) (Sb2-0-41-3 ∷ CX23 ∷ [])
  b5 = at 0 1 (Bx2-0413 ∷ []) (lem-box-perm-3124-at0214213043 c4) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- CXu-box-4 @0210243143: 15 steps
lem-CXu-box-4-at0210243143 : Complete 4 → ⟪ (CX32 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CX32 ∷ []) ⟫ʷ
lem-CXu-box-4-at0210243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Bx2-0413 ∷ []) (CCZ024 ∷ CX32 ∷ Toff213 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (pw1 c4 (CX32 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff213 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 4 2 (Toff213 ∷ CS34⁻ ∷ []) (lw0 c4 (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 c4) ▸
       at 2 2 (Toff213 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ CX32 ∷ Toff213 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ []) (Bx2-0413 ∷ CX32 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (pw1 c4 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff213 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ024 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ034 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (pw1 c4 (CX32 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX32 ∷ []) (pw1 c4 (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff213 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- CXAu-S @14213243: 12 steps
lem-CXAu-S-at14213243 : Complete 4 → ⟪ (CX32 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CX32 ∷ []) ⟫ʷ
lem-CXAu-S-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX32 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CX32 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CX32 ∷ []) (lem-CXu-box-4-at0210243143 c4) ▸
       at 1 2 (Toff314 ∷ CX32 ∷ Toff214 ∷ []) (lw0 c4 (CX32 ∷ Toff314 ∷ []) (Toff314 ∷ CX32 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS03 ∷ Toff214 ∷ []) (lem-comm-TOFF214-CS03 c4) ▸
       at 2 2 (CS03 ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CS03 ∷ []) (CS03 ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (Toff314 ∷ CX32 ∷ []) (lw0 c4 (CX32 ∷ Toff214 ∷ Toff314 ∷ []) (Toff314 ∷ CX32 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CX32 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ CX32 ∷ [])
  b1 = at 4 2 (CS03⁻ ∷ CX32 ∷ []) (lw4 c4 (CX32 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CX32 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- SW-S @14213243: 5 steps
lem-SW-S-at14213243 : Complete 4 → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-SW-S-at14213243 c4 = run b0
  where
  b0 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ Sw23 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (lw4 c4 (Sw23 ∷ []) (CX23 ∷ CX32 ∷ CX23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Sb2-0-41-3 ∷ CX23 ∷ []) (lem-CXuA-S-at14213243 c4) ▸
       at 1 2 (Sb2-0-41-3 ∷ CX32 ∷ []) (lem-CXAu-S-at14213243 c4) ▸
       at 0 2 (Sb2-0-41-3 ∷ CX23 ∷ []) (lem-CXuA-S-at14213243 c4) ▸
       at 1 3 (Sw23 ∷ []) (lw4 c4 (CX23 ∷ CX32 ∷ CX23 ∷ []) (Sw23 ∷ []) tt tt Eq.refl) ▸ done


-- nat-S @14213243: 31 steps
lem-nat-S-at14213243 : Complete 4 → ⟪ (Sw23 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-nat-S-at14213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw23 ∷ Sb2-0-41-3 ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff304 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 5 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ [])
  b1 = at 8 1 (CZ03 ∷ []) (refl) ▸
       at 2 7 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx3-02 ∷ []) (refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 2 6 (Bx0-312 ∷ []) (refl) ▸
       at 3 2 (Toff304 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ Toff204 ∷ []) (Toff304 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ034 ∷ Sw23 ∷ []) (pw1 c4 (Sw23 ∷ CCZ024 ∷ []) (CCZ034 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 6 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Sw23 ∷ CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Toff214 ∷ CS02 ∷ Sw23 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ [])
  b2 = at 8 1 (CZ03 ∷ []) (refl) ▸
       at 11 1 (CZ03 ∷ []) (refl) ▸
       at 5 7 (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ []) (CCZ013 ∷ Toff013 ∷ CZ02 ∷ Toff013 ∷ CCZ013 ∷ CZ02 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx3-02 ∷ []) (refl) ▸
       at 10 1 (Bx3-02 ∷ []) (refl) ▸
       at 5 6 (Bx0-312 ∷ []) (refl) ▸
       at 6 2 (Toff214 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CS02 ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS03 ∷ []) (CS02 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸ done

  b3 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-312 ∷ Toff304 ∷ CCZ034 ∷ Bx0-312 ∷ Toff214 ∷ CS02 ∷ Sw23 ∷ Toff314 ∷ CS03⁻ ∷ Sw23 ∷ []) (Sb3-0-41-2 ∷ [])
  b3 = at 8 2 (Toff214 ∷ Sw23 ∷ []) (lw0 c4 (Sw23 ∷ Toff314 ∷ []) (Toff214 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CS02⁻ ∷ Sw23 ∷ []) (lw4 c4 (Sw23 ∷ CS03⁻ ∷ []) (CS02⁻ ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 10 2 [] (lw4 c4 (Sw23 ∷ Sw23 ∷ []) [] tt tt Eq.refl) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸
       at 2 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸ done


-- F0 @14213243: 3 steps
lem-F0-at14213243 : Complete 4 → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-41-2 ∷ []) ⟫ʷ
lem-F0-at14213243 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Sb3-0-41-2 ∷ [])
  b0 = at 0 0 (Sw23 ∷ Sw23 ∷ []) (lw4 c4 [] (Sw23 ∷ Sw23 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Sb2-0-41-3 ∷ Sw23 ∷ []) (lem-SW-S-at14213243 c4) ▸
       at 0 3 (Sb3-0-41-2 ∷ []) (lem-nat-S-at14213243 c4) ▸ done


-- CSdu-box-3 @243243: 17 steps
lem-CSdu-box-3-at243243 : Complete 4 → ⟪ (CS02⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02⁻ ∷ Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff023 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CS02⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS02⁻ ∷ [])
  b1 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS23⁻ ∷ []) (lw4 c4 (CS23⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) (lw4 c4 (CS02⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CS23⁻ ∷ CCZ023 ∷ CS23⁻ ∷ CZ23 ∷ CCZ023 ∷ []) (CS02⁻ ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS02⁻ ∷ []) (Bx0-1423 ∷ CS02⁻ ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


-- CSu-box-3 @243243: 17 steps
lem-CSu-box-3-at243243 : Complete 4 → ⟪ (CS02 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-3-at243243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS02 ∷ Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CS02 ∷ CS23 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff023 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) (lw4 c4 (CS02 ∷ Toff023 ∷ []) (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ014 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (CCZ014 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 c4) ▸
       at 5 2 (CCZ014 ∷ CX02 ∷ []) (pw3 c4 (CX02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX02 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CS02 ∷ CS23 ∷ CS23 ∷ CCZ014 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS02 ∷ [])
  b1 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 5 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CZ23 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff023 ∷ CS23 ∷ []) (lw4 c4 (CS23 ∷ Toff023 ∷ []) (Toff023 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) (lw4 c4 (CS02 ∷ Toff023 ∷ []) (Toff023 ∷ CS02 ∷ CS23 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 6 (CS02 ∷ []) (lw4 c4 (CS02 ∷ CS23 ∷ CCZ023 ∷ CS23 ∷ CZ23 ∷ CCZ023 ∷ []) (CS02 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS02 ∷ []) (Bx0-1423 ∷ CS02 ∷ [])
  b2 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


-- box-perm-1342 @0310243142: 3 steps
lem-box-perm-1342-at0310243142 : Complete 4 → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-1342-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-pairs-at0310243142 c4) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸ done


-- P-box @243243: 8 steps
lem-P-box-at243243 : Complete 4 → ⟪ (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-P-box-at243243 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx0-1423 ∷ Toff023 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at243243 c4) ▸
       at 0 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at243243 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at243243 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ23 ∷ []) (lw4 c4 (Toff023 ∷ CCZ023 ∷ Toff023 ∷ []) (CCZ023 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF014 c4) ▸
       at 3 3 (CCZ023 ∷ []) (lw4 c4 (CZ23 ∷ CCZ023 ∷ CZ23 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-tQ-at243243 c4)) ▸ done

