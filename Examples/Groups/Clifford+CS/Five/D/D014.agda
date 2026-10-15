{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D014 where

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
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-Kdu-box ; lem-Ku-box ; lem-Sdu-box ; lem-Su-box)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-CSdu-box-4 ; lem-CSu-box-4)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R007 using (lem-comm-CZ23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R010 using (lem-comm-CX32-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R011 using (lem-comm-CX02-CCZ134 ; lem-comm-CX12-TOFF034)
open import Examples.Groups.Clifford+CS.Five.D.R012 using (lem-comm-CSd02-TOFF134)
-- CXu-box-4: 15 steps
lem-CXu-box-4 : Complete 4 → ⟪ (CX40 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CX40 ∷ []) ⟫ʷ
lem-CXu-box-4 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX40 ∷ Bx0-1234 ∷ []) (CCZ012 ∷ CX40 ∷ Toff034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ012 ∷ Toff034 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP c4) ▸
       at 0 2 (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) (pw3 c4 (CX40 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (lw0 c4 (CCZ124 ∷ []) (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 6 2 (Toff034 ∷ CS14 ∷ []) (pw2 c4 (CS14 ∷ Toff034 ∷ []) (Toff034 ∷ CS14 ∷ []) tt tt Eq.refl) ▸
       at 5 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 4 2 (Toff034 ∷ CS24⁻ ∷ []) (pw1 c4 (CS24⁻ ∷ Toff034 ∷ []) (Toff034 ∷ CS24⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 c4) ▸
       at 2 2 (Toff034 ∷ CS24 ∷ []) (pw1 c4 (CS24 ∷ Toff034 ∷ []) (Toff034 ∷ CS24 ∷ []) tt tt Eq.refl) ▸ done

  b1 : Chain (CCZ012 ∷ CX40 ∷ Toff034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ012 ∷ Toff034 ∷ []) (Bx0-1234 ∷ CX40 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (lw0 c4 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Toff034 ∷ CX40 ∷ []) (pw1 c4 (CX40 ∷ Toff034 ∷ []) (Toff034 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ012 ∷ CCZ124 ∷ []) (pw3 c4 (CCZ124 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) (pw3 c4 (CX40 ∷ CCZ012 ∷ []) (CCZ012 ∷ CX40 ∷ CCZ124 ∷ []) tt tt Eq.refl) ▸
       at 3 3 (CX40 ∷ []) (pw3 c4 (CX40 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX40 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (Toff034 ∷ CX40 ∷ []) (pw1 c4 (CX40 ∷ Toff034 ∷ []) (Toff034 ∷ CX40 ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Bx0-1234 ∷ []) (sym (lem-box-cP c4)) ▸ done


-- CKu-box-4: 7 steps
lem-CKu-box-4 : Complete 4 → ⟪ (CK40 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK40 ∷ []) ⟫ʷ
lem-CKu-box-4 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK40 ∷ [])
  b0 = at 0 1 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (pw1 c4 (CK40 ∷ []) (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 1 5 (CK40 ∷ []) (pw1 c4 (CS04⁻ ∷ K0⁻ ∷ CS04⁻ ∷ K0 ∷ CS04⁻ ∷ []) (CK40 ∷ []) tt tt Eq.refl) ▸ done


-- CKdu-box-4: 7 steps
lem-CKdu-box-4 : Complete 4 → ⟪ (CK40⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CK40⁻ ∷ []) ⟫ʷ
lem-CKdu-box-4 c4 = run b0
  where
  b0 : Chain (CK40⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CK40⁻ ∷ [])
  b0 = at 0 1 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (pw1 c4 (CK40⁻ ∷ []) (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 3 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 2 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 1 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 0 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 1 5 (CK40⁻ ∷ []) (pw1 c4 (CS04 ∷ K0⁻ ∷ CS04 ∷ K0 ∷ CS04 ∷ []) (CK40⁻ ∷ []) tt tt Eq.refl) ▸ done


-- XCSX-box-4: 4 steps
lem-XCSX-box-4 : Complete 4 → ⟪ (X4 ∷ CS04 ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CS04 ∷ X4 ∷ []) ⟫ʷ
lem-XCSX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04 ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CS04 ∷ X4 ∷ [])
  b0 = at 0 3 (S0 ∷ CS04⁻ ∷ []) (pw1 c4 (X4 ∷ CS04 ∷ X4 ∷ []) (S0 ∷ CS04⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS04⁻ ∷ []) (lem-CSdu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0 ∷ []) (lem-Su-box c4) ▸
       at 1 2 (X4 ∷ CS04 ∷ X4 ∷ []) (pw1 c4 (S0 ∷ CS04⁻ ∷ []) (X4 ∷ CS04 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- XCSdX-box-4: 4 steps
lem-XCSdX-box-4 : Complete 4 → ⟪ (X4 ∷ CS04⁻ ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ []) ⟫ʷ
lem-XCSdX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CS04⁻ ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CS04⁻ ∷ X4 ∷ [])
  b0 = at 0 3 (S0⁻ ∷ CS04 ∷ []) (pw1 c4 (X4 ∷ CS04⁻ ∷ X4 ∷ []) (S0⁻ ∷ CS04 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CS04 ∷ []) (lem-CSu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ S0⁻ ∷ []) (lem-Sdu-box c4) ▸
       at 1 2 (X4 ∷ CS04⁻ ∷ X4 ∷ []) (pw1 c4 (S0⁻ ∷ CS04 ∷ []) (X4 ∷ CS04⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- XCKX-box-4: 4 steps
lem-XCKX-box-4 : Complete 4 → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40 ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  b0 = at 0 3 (K0 ∷ CK40⁻ ∷ []) (pw1 c4 (X4 ∷ CK40 ∷ X4 ∷ []) (K0 ∷ CK40⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CK40⁻ ∷ []) (lem-CKdu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0 ∷ []) (lem-Ku-box c4) ▸
       at 1 2 (X4 ∷ CK40 ∷ X4 ∷ []) (pw1 c4 (K0 ∷ CK40⁻ ∷ []) (X4 ∷ CK40 ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- XCKdX-box-4: 4 steps
lem-XCKdX-box-4 : Complete 4 → ⟪ (X4 ∷ CK40⁻ ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) ⟫ʷ
lem-XCKdX-box-4 c4 = run b0
  where
  b0 : Chain (X4 ∷ CK40⁻ ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ [])
  b0 = at 0 3 (K0⁻ ∷ CK40 ∷ []) (pw1 c4 (X4 ∷ CK40⁻ ∷ X4 ∷ []) (K0⁻ ∷ CK40 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (Bx0-1234 ∷ CK40 ∷ []) (lem-CKu-box-4 c4) ▸
       at 0 2 (Bx0-1234 ∷ K0⁻ ∷ []) (lem-Kdu-box c4) ▸
       at 1 2 (X4 ∷ CK40⁻ ∷ X4 ∷ []) (pw1 c4 (K0⁻ ∷ CK40 ∷ []) (X4 ∷ CK40⁻ ∷ X4 ∷ []) tt tt Eq.refl) ▸ done


-- cQ @12233441: 7 steps
lem-cQ-at12233441 : Complete 4 → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at12233441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CS03⁻ ∷ []) (pw2 c4 (CS03⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 c4) ▸
       at 0 2 (CCZ014 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ023 ∷ []) (lw4 c4 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done


-- box-tQ @12233441: 13 steps
lem-box-tQ-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at12233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-2341 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 0 2 (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) (lw4 c4 (CCZ023 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ CZ23 ∷ []) tt tt Eq.refl) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 c4) ▸
       at 1 2 (CCZ014 ∷ CCZ023 ∷ []) (lem-cQ-at12233441 c4) ▸
       at 2 4 (Toff023 ∷ []) (lw4 c4 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ []) tt tt Eq.refl) ▸ done


-- cQ @0110: 7 steps
lem-cQ-at0110 : Complete 4 → ⟪ (CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0110 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (lw4 c4 (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ134 ∷ CS01 ∷ []) (pw2 c4 (CS01 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS01 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 c4) ▸
       at 2 2 (CCZ134 ∷ CS12⁻ ∷ []) (lw0 c4 (CS12⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ CS12⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 c4) ▸
       at 0 2 (CCZ134 ∷ CS12 ∷ []) (lw0 c4 (CS12 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS12 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ012 ∷ []) (lw4 c4 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- tP @0110: 7 steps
lem-tP-at0110 : Complete 4 → ⟪ (Toff102 ∷ Toff134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff102 ∷ []) ⟫ʷ
lem-tP-at0110 c4 = run b0
  where
  b0 : Chain (Toff102 ∷ Toff134 ∷ []) (Toff134 ∷ Toff102 ∷ [])
  b0 = at 0 1 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (lw4 c4 (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 1 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (lw0 c4 (Toff134 ∷ []) (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 [] (lw4 c4 (K1⁻ ∷ K1 ∷ []) [] tt tt Eq.refl) ▸
       at 1 2 (CCZ134 ∷ CCZ012 ∷ []) (lem-cQ-at0110 c4) ▸
       at 2 0 (K1⁻ ∷ K1 ∷ []) (lw4 c4 [] (K1⁻ ∷ K1 ∷ []) tt tt Eq.refl) ▸
       at 0 3 (Toff134 ∷ []) (lw0 c4 (K1 ∷ CCZ134 ∷ K1⁻ ∷ []) (Toff134 ∷ []) tt tt Eq.refl) ▸
       at 1 3 (Toff102 ∷ []) (lw4 c4 (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) tt tt Eq.refl) ▸ done


-- VPQ @0110: 14 steps
lem-VPQ-at0110 : Complete 4 → ⟪ (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0110 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) (CS34⁻ ∷ CS02⁻ ∷ S1 ∷ Toff134 ∷ Toff102 ∷ S1⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) (lw4 c4 (Toff102 ∷ CCZ012 ∷ []) (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CS34⁻ ∷ S1 ∷ Toff134 ∷ S1⁻ ∷ []) (lw0 c4 (Toff134 ∷ CCZ134 ∷ []) (CS34⁻ ∷ S1 ∷ Toff134 ∷ S1⁻ ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CS34⁻ ∷ S1⁻ ∷ []) (c₂ ((S • S • S) ↑) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS34⁻ ∷ Toff102 ∷ []) (c₃ (K ↑ • CCZ • K ↑ • iI) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S1 ∷ []) (c₂ (S ↑) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS34⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (CS • CS • CS)) ▸
       at 4 2 [] (lw4 c4 (S1⁻ ∷ S1 ∷ []) [] tt tt Eq.refl) ▸
       at 3 2 (Toff134 ∷ Toff102 ∷ []) (lem-tP-at0110 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS02⁻ ∷ S1 ∷ Toff134 ∷ Toff102 ∷ S1⁻ ∷ []) (Toff134 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S1⁻ ∷ S1 ∷ []) (lw4 c4 [] (S1⁻ ∷ S1 ∷ []) tt tt Eq.refl) ▸
       at 1 2 (S1 ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ S1 ∷ []) (S1 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 2 2 (Toff134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF134 c4) ▸
       at 3 2 (S1⁻ ∷ CS02⁻ ∷ []) (lw4 c4 (CS02⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 0 4 (Toff134 ∷ CCZ134 ∷ []) (lw0 c4 (CS34⁻ ∷ S1 ∷ Toff134 ∷ S1⁻ ∷ []) (Toff134 ∷ CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff102 ∷ CCZ012 ∷ []) (lw4 c4 (CS02⁻ ∷ S1 ∷ Toff102 ∷ S1⁻ ∷ []) (Toff102 ∷ CCZ012 ∷ []) tt tt Eq.refl) ▸ done


-- QVQ @0110: 3 steps
lem-QVQ-at0110 : Complete 4 → ⟪ (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ []) ⟫ʷ
lem-QVQ-at0110 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ134 ∷ []) (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ [])
  b0 = at 0 0 (Toff134 ∷ Toff134 ∷ []) (lw0 c4 [] (Toff134 ∷ Toff134 ∷ []) tt tt Eq.refl) ▸
       at 1 4 (Toff102 ∷ CCZ012 ∷ Toff134 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at0110 c4)) ▸
       at 4 2 [] (lw0 c4 (CCZ134 ∷ CCZ134 ∷ []) [] tt tt Eq.refl) ▸ done


-- box-cP @0110: 12 steps
lem-box-cP-at0110 : Complete 4 → ⟪ (Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ []) ⟫ʷ
lem-box-cP-at0110 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx1-0234 ∷ []) (CCZ012 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff102 ∷ Bx0-134 ∷ Toff102 ∷ CCZ012 ∷ Bx0-134 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (pw2 c4 (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx1-04 ∷ Toff013 ∷ CCZ013 ∷ Bx1-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff102 ∷ CCZ134 ∷ Toff102 ∷ CCZ012 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ012 ∷ Toff134 ∷ CCZ012 ∷ Toff134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (pw2 c4 (CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (CCZ134 ∷ []) tt tt Eq.refl) ▸
       at 2 4 (Toff134 ∷ Toff102 ∷ CCZ012 ∷ Toff134 ∷ []) (lem-QVQ-at0110 c4) ▸
       at 1 2 (Toff134 ∷ Toff102 ∷ []) (lem-tP-at0110 c4) ▸
       at 2 2 [] (lw4 c4 (Toff102 ∷ Toff102 ∷ []) [] tt tt Eq.refl) ▸ done


-- sym-ab @12233441: 18 steps
lem-sym-ab-at12233441 : Complete 4 → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3241 ∷ []) ⟫ʷ
lem-sym-ab-at12233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-2341 ∷ []) (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff023 ∷ Bx2-041 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 4 1 (Bx0-31 ∷ []) (refl) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ Toff023 ∷ CCZ023 ∷ Bx2-041 ∷ []) (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ [])
  b1 = at 2 6 (Bx3-041 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx0-21 ∷ Toff204 ∷ CCZ024 ∷ Bx0-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸
       at 5 6 (CCZ014 ∷ []) (pw3 c4 (CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ014 ∷ []) tt tt Eq.refl) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) (pw2 c4 (CCZ014 ∷ []) (CCZ034 ∷ Toff304 ∷ CZ13 ∷ Toff304 ∷ CCZ034 ∷ CZ13 ∷ []) tt tt Eq.refl) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸
       at 10 1 (Bx0-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ023 ∷ Toff023 ∷ Bx3-041 ∷ Toff023 ∷ CCZ023 ∷ CCZ034 ∷ Toff304 ∷ Bx0-31 ∷ Toff304 ∷ CCZ034 ∷ Bx0-31 ∷ []) (Bx0-3241 ∷ [])
  b2 = at 5 6 (Bx3-041 ∷ []) (refl) ▸
       at 0 6 (Bx0-3241 ∷ []) (refl) ▸ done


-- cQ @133441: 7 steps
lem-cQ-at133441 : Complete 4 → ⟪ (CCZ023 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at133441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (lw4 c4 (CCZ023 ∷ []) (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 4 2 (CCZ014 ∷ CS03 ∷ []) (pw2 c4 (CS03 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS03 ∷ []) tt tt Eq.refl) ▸
       at 3 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 c4) ▸
       at 2 2 (CCZ014 ∷ CS02⁻ ∷ []) (pw3 c4 (CS02⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02⁻ ∷ []) tt tt Eq.refl) ▸
       at 1 2 (CCZ014 ∷ CX32 ∷ []) (lem-comm-CX32-CCZ014 c4) ▸
       at 0 2 (CCZ014 ∷ CS02 ∷ []) (pw3 c4 (CS02 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS02 ∷ []) tt tt Eq.refl) ▸
       at 1 5 (CCZ023 ∷ []) (lw4 c4 (CS02 ∷ CX32 ∷ CS02⁻ ∷ CX32 ∷ CS03 ∷ []) (CCZ023 ∷ []) tt tt Eq.refl) ▸ done

