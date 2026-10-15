{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D030 where

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
open import Examples.Groups.Clifford+CS.Five.D.D029 using (lem-cQ-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CZ04-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CZ14-CCZ023)
open import Examples.Groups.Clifford+CS.Five.D.R013 using (lem-comm-CX40-CCZ123)
open import Examples.Groups.Clifford+CS.Five.D.R014 using (lem-comm-CS13-TOFF204 ; lem-comm-CSd13-TOFF204)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CSd14-TOFF203 ; lem-comm-CX03-CCZ124 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ03-TOFF214 ; lem-comm-TOFF214-CSd03)
-- box-tQ @0214203143: 13 steps
lem-box-tQ-at0214203143 : Complete 4 → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4013 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (lw0 c4 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (lw0 c4 (CCZ124 ∷ Toff412 ∷ CZ34 ∷ Toff412 ∷ CCZ124 ∷ CZ34 ∷ []) (CCZ123 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) (pw1 c4 (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 c4) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at0214203143 c4) ▸
       at 2 4 (Toff204 ∷ []) (pw1 c4 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @0214203143: 17 steps
lem-CXbc-box-at0214203143 : Complete 4 → ⟪ (CX01 ∷ Bx2-4013 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx2-4013 ∷ CX01 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX01 ∷ CCZ023 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CCZ123 ∷ CX40 ∷ CS34 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (Toff204 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (lw4 c4 (CX01 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ []) (pw1 c4 (CCZ023 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ023 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ CX01 ∷ []) (pw3 c4 (CX01 ∷ Toff204 ∷ []) (Toff204 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (pw1 c4 (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ123 ∷ CS34 ∷ []) (lw0 c4 (CS34 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 c4) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX01 ∷ CCZ023 ∷ CS03 ∷ CX40 ∷ CS03⁻ ∷ CCZ123 ∷ CX40 ∷ CS34 ∷ CX01 ∷ []) (Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS03⁻ ∷ []) (lw4 c4 (CS03⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 c4) ▸
       at 5 2 (CCZ123 ∷ CS03 ∷ []) (lw4 c4 (CS03 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ034 ∷ []) (pw1 c4 (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CCZ023 ∷ []) (lw4 c4 (CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) (lw4 c4 (CX01 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX01 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX01 ∷ []) (lw4 c4 (CX01 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX01 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸ done

  b2 : Chain (Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ []) (Bx2-4013 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (pw2 c4 (CX01 ∷ CCZ034 ∷ CX01 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @0214203143: 18 steps
lem-CXcb-box-at0214203143 : Complete 4 → ⟪ (CX10 ∷ Bx2-4013 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx2-4013 ∷ CX10 ∷ []) (Toff204 ∷ CCZ123 ∷ CX10 ∷ Toff214 ∷ CS13 ∷ CX41 ∷ Toff204 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ123 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4) ▸
       at 0 2 (Toff204 ∷ CX10 ∷ Toff214 ∷ []) (pw3 c4 (CX10 ∷ Toff204 ∷ []) (Toff204 ∷ CX10 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) (lw0 c4 (Toff214 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff214 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ123 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff204 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ Toff204 ∷ []) (Toff204 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff204 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 c4) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ CX10 ∷ Toff214 ∷ CS13 ∷ CX41 ∷ Toff204 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ123 ∷ CX10 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff204 ∷ CX41 ∷ []) (pw3 c4 (CX41 ∷ Toff204 ∷ []) (Toff204 ∷ CX41 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 c4) ▸
       at 5 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff204 ∷ Toff214 ∷ []) (pw3 c4 (Toff214 ∷ Toff204 ∷ []) (Toff204 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff204 ∷ CX10 ∷ Toff214 ∷ []) (pw3 c4 (CX10 ∷ Toff204 ∷ []) (Toff204 ∷ CX10 ∷ Toff214 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX10 ∷ []) (pw3 c4 (CX10 ∷ Toff214 ∷ Toff214 ∷ []) (CX10 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ123 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ123 ∷ CX10 ∷ []) (lw4 c4 (CX10 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX10 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ []) (Bx2-4013 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-4013 ∷ []) (sym (lem-box-tQ-at0214203143 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (pw2 c4 (CX10 ∷ CCZ134 ∷ CX10 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @0214203143: 11 steps
lem-SWbc-box-at0214203143 : Complete 4 → ⟪ (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-SWbc-box-at0214203143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (CX01 ∷ Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (lw4 c4 (Sw01 ∷ []) (CX01 ∷ CX10 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (lw4 c4 (Sw01 ∷ []) (CX01 ∷ CX10 ∷ CX01 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx2-4013 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0214203143 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx2-4013 ∷ CCZ134 ∷ []) (lem-CXcb-box-at0214203143 c4) ▸
       at 4 2 (CX01 ∷ CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ134 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX01 ∷ Bx2-4013 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (Bx2-4013 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (pw2 c4 (CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (CCZ034 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx2-4013 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0214203143 c4) ▸
       at 1 2 [] (pw1 c4 (CCZ034 ∷ CCZ034 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @0214203143: 23 steps
lem-nat-SWbc-at0214203143 : Complete 4 → ⟪ (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214203143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ Sw01 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-213 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ []) (refl) ▸
       at 0 2 (CCZ124 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff214 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff402 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff402 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ Sw01 ∷ CCZ124 ∷ Bx2-43 ∷ Toff204 ∷ CCZ024 ∷ Bx4-213 ∷ Sw01 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Sw01 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff214 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff204 ∷ []) (Toff214 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ124 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ024 ∷ []) (CCZ124 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ124 ∷ Toff412 ∷ Bx2-43 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff402 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ124 ∷ Toff214 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Sw01 ∷ Toff412 ∷ CCZ124 ∷ Bx2-43 ∷ Sw01 ∷ []) (Bx2-4103 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ Toff412 ∷ []) (Toff402 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ024 ∷ Sw01 ∷ []) (pw3 c4 (Sw01 ∷ CCZ124 ∷ []) (CCZ024 ∷ Sw01 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx2-43 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (lw4 c4 (Sw01 ∷ Sw01 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx4-203 ∷ []) (refl) ▸
       at 5 6 (Bx4-203 ∷ []) (refl) ▸
       at 0 6 (Bx2-4103 ∷ []) (refl) ▸ done


-- sym-bc @0214203143: 2 steps
lem-sym-bc-at0214203143 : Complete 4 → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-sym-bc-at0214203143 c4 = run b0
  where
  b0 : Chain (Bx2-4013 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-4013 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0214203143 c4)) ▸
       at 0 3 (Bx2-4103 ∷ []) (lem-nat-SWbc-at0214203143 c4) ▸ done


-- cQ @0214213043: 7 steps
lem-cQ-at0214213043 : Complete 4 → ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ
lem-cQ-at0214213043 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS24 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 2 2 (CCZ023 ∷ CS12⁻ ∷ []) (lw4 c4 (CS12⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ CS12 ∷ []) (lw4 c4 (CS12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ124 ∷ []) (lw0 c4 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0214213043: 13 steps
lem-box-tQ-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4103 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff214 ∷ CCZ124 ∷ CZ14 ∷ []) (lw0 c4 (CCZ124 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ124 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at0214213043 c4) ▸
       at 2 4 (Toff214 ∷ []) (lw0 c4 (CCZ124 ∷ CZ14 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸ done


-- tP @0214213043: 7 steps
lem-tP-at0214213043 : Complete 4 → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at0214213043 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (lw0 c4 (Toff214 ∷ []) (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (lw4 c4 (Toff203 ∷ []) (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K2⁻ ∷ K2 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at0214213043 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (lw4 c4 [] (K2⁻ ∷ K2 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff203 ∷ []) (lw4 c4 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff214 ∷ []) (lw0 c4 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (Toff214 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @0214213043: 8 steps
lem-P-box-at0214213043 : Complete 4 → ⟪ (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-P-box-at0214213043 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) (Bx2-4103 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at0214213043 c4) ▸
       at 0 2 (Toff214 ∷ Toff203 ∷ []) (sym (lem-tP-at0214213043 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ03 ∷ Toff203 ∷ []) (lw4 c4 (Toff203 ∷ CCZ023 ∷ []) (CCZ023 ∷ CZ03 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (sym (lem-tP-at0214213043 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ03 ∷ []) (lw4 c4 (Toff203 ∷ CCZ023 ∷ Toff203 ∷ []) (CCZ023 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff214 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF214 c4) ▸
       at 3 3 (CCZ023 ∷ []) (lw4 c4 (CZ03 ∷ CCZ023 ∷ CZ03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx2-4103 ∷ []) (sym (lem-box-tQ-at0214213043 c4)) ▸ done


-- VPQ @0214213043: 14 steps
lem-VPQ-at0214213043 : Complete 4 → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (lw0 c4 (Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (lw4 c4 (Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS03⁻ ∷ S2⁻ ∷ []) (lw4 c4 (S2⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S2⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 c4) ▸
       at 1 2 (CS03⁻ ∷ S2 ∷ []) (lw4 c4 (S2 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (CS03⁻ ∷ CS14⁻ ∷ []) (pw2 c4 (CS14⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S2⁻ ∷ S2 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (lw4 c4 [] (S2⁻ ∷ S2 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S2 ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ S2 ∷ []) (S2 ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 c4) ▸
       at 3 2 (S2⁻ ∷ CS14⁻ ∷ []) (lw0 c4 (CS14⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS14⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff203 ∷ CCZ023 ∷ []) (lw4 c4 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff214 ∷ CCZ124 ∷ []) (lw0 c4 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0214213043: 3 steps
lem-QVQ-at0214213043 : Complete 4 → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at0214213043 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  b0 = at 0 0 (Toff203 ∷ Toff203 ∷ []) (lw4 c4 [] (Toff203 ∷ Toff203 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at0214213043 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ023 ∷ CCZ023 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0214213043: 12 steps
lem-box-cP-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at0214213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4103 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-203 ∷ Toff214 ∷ CCZ124 ∷ Bx4-203 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-43 ∷ Toff402 ∷ CCZ024 ∷ Bx2-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at0214213043 c4) ▸
       at 1 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at0214213043 c4) ▸
       at 2 2 [] (lw0 c4 (Toff214 ∷ Toff214 ∷ []) [] tt tt Eq.refl) ▸ done


-- cQ @0210233441: 7 steps
lem-cQ-at0210233441 : Complete 4 → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0210233441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ124 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 c4) ▸
       at 2 2 (CCZ124 ∷ CS23⁻ ∷ []) (lw0 c4 (CS23⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS23⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 c4) ▸
       at 0 2 (CCZ124 ∷ CS23 ∷ []) (lw0 c4 (CS23 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS23 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ023 ∷ []) (lw4 c4 (CS23 ∷ CX03 ∷ CS23⁻ ∷ CX03 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @0210233441: 13 steps
lem-box-tQ-at0210233441 : Complete 4 → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0341 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (pw3 c4 (CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff203 ∷ CCZ023 ∷ CZ03 ∷ []) (lw4 c4 (CCZ023 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ023 ∷ CZ03 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at0210233441 c4) ▸
       at 2 4 (Toff203 ∷ []) (lw4 c4 (CCZ023 ∷ CZ03 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ []) tt tt Eq.refl) ▸ done


-- pairs @0214213043: 4 steps
lem-pairs-at0214213043 : Complete 4 → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-pairs-at0214213043 c4 = run b0
  where
  b0 : Chain (Bx2-4103 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Toff203 ∷ Bx2-4103 ∷ Toff203 ∷ []) (sym (lem-P-box-at0214213043 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at0214213043 c4) ▸
       at 4 2 [] (lw4 c4 (Toff203 ∷ Toff203 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done

