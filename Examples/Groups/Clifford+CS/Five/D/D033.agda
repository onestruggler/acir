{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D033 where

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
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-tQ-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D032 using (lem-XCKX-box-2-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CSd24-TOFF013 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ24-CCZ013 ; lem-comm-TOFF024-CSd13)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CSd23-TOFF014)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-CX42-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R015 using (lem-comm-CS23-TOFF014 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ13-TOFF024)
-- F4-K2-CS0: 11 steps
lem-F4-K2-CS0 : Complete 4 → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X4 ∷ CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 4 (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lem-XCKX-box-2-at0210243143 c4) ▸
       at 1 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CS03 ∷ []) (CS03 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 3 4 (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) (lw0 c4 (X4 ∷ CK42 ∷ X4 ∷ Toff314 ∷ []) (Toff314 ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸
       at 4 4 (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (pw1 c4 (X4 ∷ CK42 ∷ X4 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CK42 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- cQ @14213243: 7 steps
lem-cQ-at14213243 : Complete 4 → ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-cQ-at14213243 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CS04 ∷ []) (pw1 c4 (CS04 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 2 2 (CCZ023 ∷ CS01⁻ ∷ []) (lw4 c4 (CS01⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS01⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 0 2 (CCZ023 ∷ CS01 ∷ []) (lw4 c4 (CS01 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ014 ∷ []) (pw2 c4 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @14213243: 13 steps
lem-box-tQ-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4123 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (pw1 c4 (CCZ024 ∷ Toff402 ∷ CZ34 ∷ Toff402 ∷ CCZ024 ∷ CZ34 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) (pw2 c4 (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at14213243 c4) ▸
       at 2 4 (Toff014 ∷ []) (pw2 c4 (CCZ014 ∷ CZ14 ∷ Toff014 ∷ CCZ014 ∷ []) (Toff014 ∷ []) tt tt Eq.refl) ▸ done


-- CXbc-box @14213243: 17 steps
lem-CXbc-box-at14213243 : Complete 4 → ⟪ (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-4123 ∷ CX12 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX12 ∷ CCZ013 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ Toff014 ∷ []) (Toff014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (lw4 c4 (CX12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) (pw2 c4 (CCZ013 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ013 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ CX12 ∷ []) (pw3 c4 (CX12 ∷ Toff014 ∷ []) (Toff014 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (lw0 c4 (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ023 ∷ CS34 ∷ []) (pw1 c4 (CS34 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX12 ∷ CCZ013 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CCZ023 ∷ CX41 ∷ CS34 ∷ CX12 ∷ []) (Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS13⁻ ∷ []) (lw4 c4 (CS13⁻ ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13⁻ ∷ []) tt tt Eq.refl) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 c4) ▸
       at 5 2 (CCZ023 ∷ CS13 ∷ []) (lw4 c4 (CS13 ∷ CCZ023 ∷ []) (CCZ023 ∷ CS13 ∷ []) tt tt Eq.refl) ▸
       at 6 5 (CCZ134 ∷ []) (lw0 c4 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ013 ∷ []) (lw4 c4 (CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (lw4 c4 (CX12 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 4 3 (CX12 ∷ []) (lw4 c4 (CX12 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX12 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸ done

  b2 : Chain (Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-4123 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (lw0 c4 (CX12 ∷ CCZ134 ∷ CX12 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸ done


-- CXcb-box @14213243: 18 steps
lem-CXcb-box-at14213243 : Complete 4 → ⟪ (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-4123 ∷ CX21 ∷ []) (Toff014 ∷ CCZ023 ∷ CX21 ∷ Toff024 ∷ CS23 ∷ CX42 ∷ Toff014 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ CCZ023 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at14213243 c4) ▸
       at 0 2 (Toff014 ∷ CX21 ∷ Toff024 ∷ []) (pw3 c4 (CX21 ∷ Toff014 ∷ []) (Toff014 ∷ CX21 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) (pw1 c4 (Toff024 ∷ CCZ023 ∷ []) (CCZ023 ∷ Toff024 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ023 ∷ CX21 ∷ []) (lw4 c4 (CX21 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (lw0 c4 (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 8 2 (Toff014 ∷ CS34 ∷ []) (pw2 c4 (CS34 ∷ Toff014 ∷ []) (Toff014 ∷ CS34 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Toff014 ∷ CX42 ∷ []) (pw3 c4 (CX42 ∷ Toff014 ∷ []) (Toff014 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 c4) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX21 ∷ Toff024 ∷ CS23 ∷ CX42 ∷ Toff014 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ CCZ023 ∷ CX21 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX42 ∷ []) (pw3 c4 (CX42 ∷ Toff014 ∷ []) (Toff014 ∷ CX42 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 c4) ▸
       at 5 5 (CCZ234 ∷ []) (lw0 c4 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff014 ∷ Toff024 ∷ []) (pw3 c4 (Toff024 ∷ Toff014 ∷ []) (Toff014 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff014 ∷ CX21 ∷ Toff024 ∷ []) (pw3 c4 (CX21 ∷ Toff014 ∷ []) (Toff014 ∷ CX21 ∷ Toff024 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX21 ∷ []) (pw3 c4 (CX21 ∷ Toff024 ∷ Toff024 ∷ []) (CX21 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (pw1 c4 (CCZ234 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ023 ∷ CX21 ∷ []) (lw4 c4 (CX21 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX21 ∷ []) tt tt Eq.refl) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-4123 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-4123 ∷ []) (sym (lem-box-tQ-at14213243 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (lw0 c4 (CX21 ∷ CCZ234 ∷ CX21 ∷ []) (CCZ234 ∷ []) tt tt Eq.refl) ▸ done


-- SWbc-box @14213243: 11 steps
lem-SWbc-box-at14213243 : Complete 4 → ⟪ (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-SWbc-box-at14213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (CX12 ∷ Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (lw4 c4 (Sw12 ∷ []) (CX12 ∷ CX21 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (lw4 c4 (Sw12 ∷ []) (CX12 ∷ CX21 ∷ CX12 ∷ []) tt tt Eq.refl) ▸
       at 2 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14213243 c4) ▸
       at 3 2 (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX21 ∷ []) (CX21 ∷ CCZ234 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Bx0-4123 ∷ CCZ234 ∷ []) (lem-CXcb-box-at14213243 c4) ▸
       at 4 2 (CX12 ∷ CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) (lw0 c4 (CCZ234 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ CCZ234 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CX12 ∷ Bx0-4123 ∷ CX12 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (Bx0-4123 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (lw0 c4 (CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ CCZ234 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Bx0-4123 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14213243 c4) ▸
       at 1 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done


-- nat-SWbc @14213243: 23 steps
lem-nat-SWbc-at14213243 : Complete 4 → ⟪ (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-nat-SWbc-at14213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff014 ∷ Bx4-023 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff024 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff401 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 5 2 (Toff401 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ Sw12 ∷ CCZ024 ∷ Bx0-43 ∷ Toff014 ∷ CCZ014 ∷ Bx4-023 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Sw12 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 7 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 8 2 (Toff024 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ Toff014 ∷ []) (Toff024 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 9 2 (CCZ024 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ CCZ014 ∷ []) (CCZ024 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 1 (CCZ024 ∷ Toff402 ∷ Bx0-43 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 11 2 (Toff401 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 12 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Sw12 ∷ Toff402 ∷ CCZ024 ∷ Bx0-43 ∷ Sw12 ∷ []) (Bx0-4213 ∷ [])
  b2 = at 13 2 (Toff401 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ Toff402 ∷ []) (Toff401 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 14 2 (CCZ014 ∷ Sw12 ∷ []) (pw3 c4 (Sw12 ∷ CCZ024 ∷ []) (CCZ014 ∷ Sw12 ∷ []) tt tt Eq.refl) ▸
       at 15 2 (Bx0-43 ∷ Sw12 ∷ []) (c₃ (Swap ↑) (CZ)) ▸
       at 16 2 [] (lw4 c4 (Sw12 ∷ Sw12 ∷ []) [] tt tt Eq.refl) ▸
       at 2 6 (Bx4-013 ∷ []) (refl) ▸
       at 5 6 (Bx4-013 ∷ []) (refl) ▸
       at 0 6 (Bx0-4213 ∷ []) (refl) ▸ done


-- sym-bc @14213243: 2 steps
lem-sym-bc-at14213243 : Complete 4 → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-sym-bc-at14213243 c4 = run b0
  where
  b0 : Chain (Bx0-4123 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx0-4123 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at14213243 c4)) ▸
       at 0 3 (Bx0-4213 ∷ []) (lem-nat-SWbc-at14213243 c4) ▸ done


-- cQ @143143: 7 steps
lem-cQ-at143143 : Complete 4 → ⟪ (CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at143143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (pw1 c4 (CCZ024 ∷ []) (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ013 ∷ CS04 ∷ []) (pw2 c4 (CS04 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 c4) ▸
       at 2 2 (CCZ013 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 c4) ▸
       at 0 2 (CCZ013 ∷ CS02 ∷ []) (lw4 c4 (CS02 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ024 ∷ []) (pw1 c4 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @143143: 13 steps
lem-box-tQ-at143143 : Complete 4 → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4213 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (pw2 c4 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (pw2 c4 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) (pw1 c4 (CCZ024 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ CZ24 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 c4) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at143143 c4) ▸
       at 2 4 (Toff024 ∷ []) (pw1 c4 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ CCZ024 ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸ done


-- tP @143143: 7 steps
lem-tP-at143143 : Complete 4 → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at143143 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (pw1 c4 (Toff024 ∷ []) (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (lw4 c4 (Toff013 ∷ []) (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K0⁻ ∷ K0 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at143143 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (lw4 c4 [] (K0⁻ ∷ K0 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff013 ∷ []) (lw4 c4 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff024 ∷ []) (pw1 c4 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (Toff024 ∷ []) tt tt Eq.refl) ▸ done


-- P-box @143143: 8 steps
lem-P-box-at143143 : Complete 4 → ⟪ (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-P-box-at143143 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4) ▸
       at 0 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at143143 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ []) (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at143143 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ13 ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ Toff013 ∷ []) (CCZ013 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff024 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF024 c4) ▸
       at 3 3 (CCZ013 ∷ []) (lw4 c4 (CZ13 ∷ CCZ013 ∷ CZ13 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸ done


-- VPQ @143143: 14 steps
lem-VPQ-at143143 : Complete 4 → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (pw1 c4 (Toff024 ∷ CCZ024 ∷ []) (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (lw4 c4 (Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 2 2 (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 c4) ▸
       at 1 2 (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 2 (CS13⁻ ∷ CS24⁻ ∷ []) (lw0 c4 (CS24⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 [] (lw4 c4 (S0⁻ ∷ S0 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at143143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (lw4 c4 [] (S0⁻ ∷ S0 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S0 ∷ CS24⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 c4) ▸
       at 3 2 (S0⁻ ∷ CS24⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff013 ∷ CCZ013 ∷ []) (lw4 c4 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff024 ∷ CCZ024 ∷ []) (pw1 c4 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @143143: 3 steps
lem-QVQ-at143143 : Complete 4 → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at143143 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (lw4 c4 [] (Toff013 ∷ Toff013 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at143143 c4)) ▸
       at 4 2 [] (lw4 c4 (CCZ013 ∷ CCZ013 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @143143: 12 steps
lem-box-cP-at143143 : Complete 4 → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at143143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4213 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-013 ∷ Toff024 ∷ CCZ024 ∷ Bx4-013 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (pw2 c4 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ014 ∷ Toff401 ∷ Bx0-43 ∷ Toff401 ∷ CCZ014 ∷ Bx0-43 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (pw2 c4 (CCZ014 ∷ Toff401 ∷ CZ34 ∷ Toff401 ∷ CCZ014 ∷ CZ34 ∷ []) (CCZ013 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at143143 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at143143 c4) ▸
       at 2 2 [] (pw1 c4 (Toff024 ∷ Toff024 ∷ []) [] tt tt Eq.refl) ▸ done


-- pairs @143143: 4 steps
lem-pairs-at143143 : Complete 4 → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-pairs-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 0 1 (Toff013 ∷ Bx0-4213 ∷ Toff013 ∷ []) (sym (lem-P-box-at143143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at143143 c4) ▸
       at 4 2 [] (lw4 c4 (Toff013 ∷ Toff013 ∷ []) [] tt tt Eq.refl) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

