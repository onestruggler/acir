{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D008 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0453 ; wl0454 ; wl1472 ; wl1485 ; wl1486 ; wl1491 ; wl1492 ; wl1493 ; wl1494 ; wl1495 ; wp0218 ; wp0303 ; wp1309 ; wp1310 ; wp1321 ; wl0465 ; wl0466 ; wl0467 ; wp0315 ; wp0516 ; wp0598 ; wp0733 ; wp0766 ; wp0767 ; wp1048 ; wp1391 ; wp1392 ; wl0175 ; wl0624 ; wl0625 ; wl1596 ; wp0211 ; wl1192 ; wl1370 ; wp0732 ; wp1436 ; wp1437 ; wp1456 ; wp1457 ; wl0302 ; wl0756 ; wl1263 ; wp0302 ; wp0342 ; wp0540 ; wp1494 ; wp1495 ; wp1496 ; wp1497 ; wp1498 ; wp1499 ; wp1503)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at0410213243 ; lem-box-tQ-at04203243 ; lem-tP-at0410213243 ; lem-tP-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-cQ-at02142140 ; lem-cQ-at0410233142 ; lem-cQ-at0410233241 ; lem-cQ-at041041 ; lem-cQ-at0412213043 ; lem-cQ-at04122140 ; lem-cQ-at0412233041 ; lem-cQ-at0412233140 ; lem-cQ-at0413203142 ; lem-cQ-at0413203241 ; lem-cQ-at0413213042 ; lem-cQ-at0413213240 ; lem-cQ-at04133140 ; lem-cQ-at04233240 ; lem-cQ-at0440 ; lem-tP-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CZ12-CCZ034 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CZ03-CCZ124)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CZ02-CCZ134 ; lem-comm-CZ23-TOFF401)

-- P-box @0410213243: 8 steps
lem-P-box-at0410213243 : Ws → ⟪ (Toff423 ∷ Bx4-0123 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-P-box-at0410213243 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-0123 ∷ Toff423 ∷ []) (Bx4-0123 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4) ▸
       at 0 2 (Toff401 ∷ Toff423 ∷ []) (sym (lem-tP-at0410213243 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ23 ∷ Toff423 ∷ []) (sym (wl1491 (lit c4))) ▸
       at 3 2 (Toff401 ∷ Toff423 ∷ []) (sym (lem-tP-at0410213243 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ23 ∷ []) (sym (wl1492 (lit c4))) ▸
       at 2 2 (Toff401 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF401 (lit c4)) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl1493 (lit c4))) ▸
       at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-tQ-at0410213243 c4)) ▸ done

-- box-tQ @0412233041: 13 steps
lem-box-tQ-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at0412233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2301 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-401 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 0 2 (Toff423 ∷ CCZ234 ∷ CZ23 ∷ []) (wl1494 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233041 c4) ▸
       at 2 4 (Toff423 ∷ []) (wl1495 (lit c4)) ▸ done

-- box-tQ @041041: 13 steps
lem-box-tQ-at041041 : Ws → ⟪ (Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at041041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0231 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-431 ∷ Toff402 ∷ CCZ024 ∷ Bx0-431 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx4-01 ∷ Toff034 ∷ CCZ034 ∷ Bx4-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 0 2 (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) (wp1309 c4) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at041041 c4) ▸
       at 2 4 (Toff402 ∷ []) (wp1310 c4) ▸ done

-- box-tQ @0410233241: 13 steps
lem-box-tQ-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0410233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0321 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 0 2 (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp1391 c4) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233241 c4) ▸
       at 2 4 (Toff403 ∷ []) (wp1392 c4) ▸ done

-- tP @0410233241: 7 steps
lem-tP-at0410233241 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0410233241 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 3 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233241 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸
       at 1 3 (Toff403 ∷ []) (wp0315 c4) ▸ done

-- box-tQ @0412213043: 13 steps
lem-box-tQ-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0412213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2103 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 5 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 0 2 (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (wl0465 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0412213043 c4) ▸
       at 2 4 (Toff412 ∷ []) (wl0466 (lit c4)) ▸ done

-- tP @0412213043: 7 steps
lem-tP-at0412213043 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at0412213043 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0412213043 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff403 ∷ []) (wp0315 c4) ▸
       at 1 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸ done

-- box-tQ @0413213240: 13 steps
lem-box-tQ-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0413213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3120 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 0 2 (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1485 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at0413213240 c4) ▸
       at 2 4 (Toff413 ∷ []) (wl1486 (lit c4)) ▸ done

-- box-tQ @04233240: 13 steps
lem-box-tQ-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at04233240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1320 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-420 ∷ Toff413 ∷ CCZ134 ∷ Bx1-420 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx4-10 ∷ Toff124 ∷ CCZ124 ∷ Bx4-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 0 2 (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1485 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at04233240 c4) ▸
       at 2 4 (Toff413 ∷ []) (wl1486 (lit c4)) ▸ done

-- box-tQ @0440: 13 steps
lem-box-tQ-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1230 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 0 2 (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (wl0465 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0440 c4) ▸
       at 2 4 (Toff412 ∷ []) (wl0466 (lit c4)) ▸ done

-- tP @0440: 7 steps
lem-tP-at0440 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at0440 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at0440 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff403 ∷ []) (wp0315 c4) ▸
       at 1 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸ done

-- box-tQ @0413203142: 13 steps
lem-box-tQ-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0413203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3012 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 0 2 (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp1391 c4) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203142 c4) ▸
       at 2 4 (Toff403 ∷ []) (wp1392 c4) ▸ done

-- tP @02142140: 7 steps
lem-tP-at02142140 : Ws → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at02142140 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at02142140 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸
       at 1 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸ done

-- box-tQ @0413213042: 13 steps
lem-box-tQ-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0413213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3102 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-402 ∷ Toff413 ∷ CCZ134 ∷ Bx3-402 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 4 1 (CZ23 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff304 ∷ Bx4-32 ∷ Toff304 ∷ CCZ034 ∷ Bx4-32 ∷ []) (refl) ▸
       at 7 1 (CZ23 ∷ []) (refl) ▸
       at 10 1 (CZ23 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ034 ∷ Toff304 ∷ CZ23 ∷ Toff304 ∷ CCZ034 ∷ CZ23 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0211 c4)) ▸
       at 0 2 (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1485 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at0413213042 c4) ▸
       at 2 4 (Toff413 ∷ []) (wl1486 (lit c4)) ▸ done

-- tP @0413203142: 7 steps
lem-tP-at0413203142 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0413203142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 3 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203142 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸
       at 1 3 (Toff403 ∷ []) (wp0315 c4) ▸ done

-- tP @0413213240: 7 steps
lem-tP-at0413213240 : Ws → ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ
lem-tP-at0413213240 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Toff402 ∷ []) (Toff402 ∷ Toff413 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (sym (wl1472 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (sym (wp1321 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at0413213240 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff402 ∷ []) (wp1321 c4) ▸
       at 1 3 (Toff413 ∷ []) (wl1472 (lit c4)) ▸ done

-- t-cP @0310213442: 5 steps
lem-t-cP-at0310213442 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-t-cP-at0310213442 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 2 (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) (sym (wl1370 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4) ▸
       at 2 3 (CCZ013 ∷ Toff301 ∷ []) (sym (wl1192 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4) ▸ done

-- P-box @04203243: 8 steps
lem-P-box-at04203243 : Ws → ⟪ (Toff423 ∷ Bx4-1023 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-P-box-at04203243 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Bx4-1023 ∷ Toff423 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ Toff423 ∷ []) (sym (lem-tP-at04203243 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ23 ∷ Toff423 ∷ []) (sym (wl1491 (lit c4))) ▸
       at 3 2 (Toff401 ∷ Toff423 ∷ []) (sym (lem-tP-at04203243 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ23 ∷ []) (sym (wl1492 (lit c4))) ▸
       at 2 2 (Toff401 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF401 (lit c4)) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl1493 (lit c4))) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done

-- box-tQ @0412233140: 13 steps
lem-box-tQ-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at0412233140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2310 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 0 2 (Toff423 ∷ CCZ234 ∷ CZ23 ∷ []) (wl1494 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233140 c4) ▸
       at 2 4 (Toff423 ∷ []) (wl1495 (lit c4)) ▸ done

-- box-tQ @0410233142: 13 steps
lem-box-tQ-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0410233142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0312 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 0 2 (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp1391 c4) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233142 c4) ▸
       at 2 4 (Toff403 ∷ []) (wp1392 c4) ▸ done

-- tP @0410233142: 7 steps
lem-tP-at0410233142 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0410233142 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 3 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0410233142 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸
       at 1 3 (Toff403 ∷ []) (wp0315 c4) ▸ done

-- box-tQ @04122140: 13 steps
lem-box-tQ-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at04122140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2130 ∷ []) (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 0 2 (Toff412 ∷ CCZ124 ∷ CZ12 ∷ []) (wl0465 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at04122140 c4) ▸
       at 2 4 (Toff412 ∷ []) (wl0466 (lit c4)) ▸ done

-- tP @0412233140: 7 steps
lem-tP-at0412233140 : Ws → ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ
lem-tP-at0412233140 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Toff401 ∷ []) (Toff401 ∷ Toff423 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0453 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (sym (wp0303 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233140 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff401 ∷ []) (wp0303 c4) ▸
       at 1 3 (Toff423 ∷ []) (wl0453 (lit c4)) ▸ done

-- t-cP @04203243: 5 steps
lem-t-cP-at04203243 : Ws → ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff401 ∷ []) ⟫ʷ
lem-t-cP-at04203243 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff401 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ Toff401 ∷ CZ01 ∷ []) (sym (wp1456 c4)) ▸
       at 2 2 (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ)) ▸
       at 1 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸
       at 2 3 (CCZ014 ∷ Toff401 ∷ []) (sym (wp1457 c4)) ▸
       at 3 2 (Toff423 ∷ Toff401 ∷ []) (lem-tP-at04203243 c4) ▸ done

-- box-tQ @0413203241: 13 steps
lem-box-tQ-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at0413203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3021 ∷ []) (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ Bx3-421 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 0 2 (Toff403 ∷ CCZ034 ∷ CZ03 ∷ []) (wp1391 c4) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203241 c4) ▸
       at 2 4 (Toff403 ∷ []) (wp1392 c4) ▸ done

-- tP @0413203241: 7 steps
lem-tP-at0413203241 : Ws → ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ
lem-tP-at0413203241 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 3 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ034 ∷ []) (lem-cQ-at0413203241 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸
       at 1 3 (Toff403 ∷ []) (wp0315 c4) ▸ done

-- tP @04122140: 7 steps
lem-tP-at04122140 : Ws → ⟪ (Toff412 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ []) ⟫ʷ
lem-tP-at04122140 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ124 ∷ K4⁻ ∷ []) (sym (wl0467 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ034 ∷ K4⁻ ∷ []) (sym (wp0315 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ124 ∷ []) (lem-cQ-at04122140 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff403 ∷ []) (wp0315 c4) ▸
       at 1 3 (Toff412 ∷ []) (wl0467 (lit c4)) ▸ done

-- CSdu-box-2 @04203243: 17 steps
lem-CSdu-box-2-at04203243 : Ws → ⟪ (CS04⁻ ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS04⁻ ∷ []) ⟫ʷ
lem-CSdu-box-2-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS04⁻ ∷ Bx4-1023 ∷ []) (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ234 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ Toff401 ∷ CCZ234 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) (wp1494 c4) ▸
       at 3 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 7 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 6 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸ done

  b1 : Chain (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ234 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ Toff401 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CS04⁻ ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸
       at 2 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 4 2 (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) (wp1457 c4) ▸
       at 3 2 (Toff401 ∷ CS01⁻ ∷ []) (wp1495 c4) ▸
       at 2 2 (Toff401 ∷ CS04⁻ ∷ CS01⁻ ∷ CCZ014 ∷ []) (wp1494 c4) ▸
       at 3 6 (CS04⁻ ∷ []) (wp1496 c4) ▸
       at 3 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CS04⁻ ∷ []) (Bx4-1023 ∷ CS04⁻ ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done

-- Su-box @04203243: 17 steps
lem-Su-box-at04203243 : Ws → ⟪ (S4 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ S4 ∷ []) ⟫ʷ
lem-Su-box-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (S4 ∷ Bx4-1023 ∷ []) (Toff401 ∷ S4 ∷ CS01 ∷ CCZ234 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ Toff401 ∷ CCZ234 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 0 2 (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) (wp1497 c4) ▸
       at 3 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 7 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 6 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸ done

  b1 : Chain (Toff401 ∷ S4 ∷ CS01 ∷ CCZ234 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ Toff401 ∷ CCZ234 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ S4 ∷ [])
  b1 = at 4 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸
       at 2 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ S4 ∷ []) (sym (wl1263 (lit c4))) ▸
       at 4 2 (Toff401 ∷ CZ01 ∷ CCZ014 ∷ []) (wp1457 c4) ▸
       at 3 2 (Toff401 ∷ CS01 ∷ []) (wp1498 c4) ▸
       at 2 2 (Toff401 ∷ S4 ∷ CS01 ∷ CCZ014 ∷ []) (wp1497 c4) ▸
       at 3 6 (S4 ∷ []) (wp1499 c4) ▸
       at 3 2 (CCZ234 ∷ S4 ∷ []) (sym (wl1263 (lit c4))) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ S4 ∷ []) (Bx4-1023 ∷ S4 ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-tQ-at04203243 c4)) ▸ done

-- box-tQ @04133140: 13 steps
lem-box-tQ-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) ⟫ʷ
lem-box-tQ-at04133140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-3210 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff423 ∷ Bx3-410 ∷ Toff423 ∷ CCZ234 ∷ Bx3-410 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ014 ∷ []) (sym (wp1503 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-30 ∷ Toff314 ∷ CCZ134 ∷ Bx4-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ134 ∷ Toff314 ∷ CZ03 ∷ Toff314 ∷ CCZ134 ∷ CZ03 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp1503 c4)) ▸
       at 0 2 (Toff423 ∷ CCZ234 ∷ CZ23 ∷ []) (wl1494 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CZ23 ∷ []) (lem-comm-CZ23-CCZ014 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at04133140 c4) ▸
       at 2 4 (Toff423 ∷ []) (wl1495 (lit c4)) ▸ done
