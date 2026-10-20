{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D015 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0180 ; wl0181 ; wl0230 ; wl0263 ; wl0288 ; wl0321 ; wl0341 ; wl0381 ; wl0420 ; wl0443 ; wl0509 ; wl0787 ; wl0788 ; wl0923 ; wl0961 ; wl1324 ; wp0022 ; wp0161 ; wp0162 ; wp0308 ; wp0381 ; wp0382 ; wp0383 ; wl0489 ; wl0560 ; wl0619 ; wl0635 ; wl0636 ; wl0755 ; wl1343 ; wp0007 ; wp0019 ; wp0135 ; wp0221 ; wp0506 ; wp0507 ; wp0508 ; wp0671 ; wp0672 ; wp0673 ; wp0674 ; wp0712 ; wp0713 ; wp1068 ; wl0674 ; wp0351 ; wp0694 ; wl0204 ; wl0278 ; wl0279 ; wl0280 ; wl0281 ; wl0282 ; wl0616 ; wp1229 ; wp1230 ; wl0203 ; wl0335 ; wl0448 ; wp0127 ; wp1252 ; wl0677 ; wl1468 ; wl1469 ; wl1470 ; wl1474 ; wl1479 ; wl1480 ; wl1481 ; wl1497 ; wp0306 ; wp1323 ; wl0258 ; wl0411 ; wl0470 ; wl0706 ; wl1020 ; wl1566 ; wl1567 ; wl1568 ; wl1591 ; wp0317 ; wl1600 ; wl1601 ; wl1602 ; wl1604 ; wl1666 ; wl1667 ; wl1668 ; wl0167 ; wl1679 ; wl0835 ; wl1729 ; wp1281 ; wp1500 ; wp1501 ; wp1502)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-nat-SWbc-at021021 ; lem-nat-SWbc-at0210213443 ; lem-nat-SWbc-at0410213243 ; lem-tP-at0213243041 ; lem-tP-at0214233041 ; lem-tP-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-nat-SWbc-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-CXbc-box-at02102331 ; lem-CXbc-box-at02132031 ; lem-CXbc-box-at02132130 ; lem-CXbc-box-at03122031 ; lem-CXbc-box-at03122130 ; lem-CXbc-box-at0314203241 ; lem-CXbc-box-at041041 ; lem-CXbc-box-at04122041 ; lem-CXbc-box-at0412233041 ; lem-CXbc-box-at0413203142 ; lem-CXbc-box-at0413213042 ; lem-CXbc-box-at04233240 ; lem-CXbc-box-at0440 ; lem-CXbc-box-at142142 ; lem-CXcb-box-at02102331 ; lem-CXcb-box-at02132031 ; lem-CXcb-box-at02132130 ; lem-CXcb-box-at03122031 ; lem-CXcb-box-at03122130 ; lem-CXcb-box-at0314203241 ; lem-CXcb-box-at041041 ; lem-CXcb-box-at04122041 ; lem-CXcb-box-at0412233041 ; lem-CXcb-box-at0413203142 ; lem-CXcb-box-at0413213042 ; lem-CXcb-box-at04233240 ; lem-CXcb-box-at0440 ; lem-CXcb-box-at142142 ; lem-QVQ-at0213243041 ; lem-QVQ-at0214233041 ; lem-QVQ-at0310213442 ; lem-SWbc-box-at021021 ; lem-SWbc-box-at0210213443 ; lem-SWbc-box-at0214233041 ; lem-SWbc-box-at0410213243 ; lem-VPQ-at02102331 ; lem-VPQ-at02132031 ; lem-VPQ-at02132130 ; lem-VPQ-at02142041 ; lem-VPQ-at02142140 ; lem-VPQ-at03122031 ; lem-VPQ-at03122130 ; lem-VPQ-at0314203241 ; lem-VPQ-at03143041 ; lem-VPQ-at03243042 ; lem-VPQ-at0410233241 ; lem-VPQ-at04103143 ; lem-VPQ-at04122041 ; lem-VPQ-at0412213043 ; lem-VPQ-at0412233041 ; lem-VPQ-at0413203142 ; lem-VPQ-at04233042 ; lem-VPQ-at0440 ; lem-VPQ-at142142)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-CSdu-box-2-at04122041 ; lem-CXbc-box-at04122140 ; lem-CXbc-box-at0412233140 ; lem-CXbc-box-at0413213240 ; lem-CXbc-box-at04133140 ; lem-CXcb-box-at04122140 ; lem-CXcb-box-at0412233140 ; lem-CXcb-box-at0413213240 ; lem-CXcb-box-at04133140 ; lem-Su-box-at04122041 ; lem-VPQ-at0410233142 ; lem-VPQ-at04122140 ; lem-VPQ-at0412233140 ; lem-VPQ-at0413203241 ; lem-VPQ-at0413213240 ; lem-XCSX-box-2-at04203243)

-- box-cP @0214233041: 12 steps
lem-box-cP-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0214233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4301 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ CZ14 ∷ Toff402 ∷ CCZ024 ∷ CZ14 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 2 4 (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0214233041 c4) ▸
       at 1 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0214233041 c4) ▸
       at 2 2 [] (wl0420 (lit c4)) ▸ done

-- SWbc-box @0314203241: 11 steps
lem-SWbc-box-at0314203241 : Ws → ⟪ (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-SWbc-box-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw02 ∷ Bx3-4021 ∷ Sw02 ∷ []) (CX02 ∷ Bx3-4021 ∷ CX02 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 4 1 (CX02 ∷ CX20 ∷ CX02 ∷ []) (sym (wl0509 (lit c4))) ▸
       at 2 3 (Bx3-4021 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314203241 c4) ▸
       at 3 2 (CX20 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0381 c4) ▸
       at 1 3 (Bx3-4021 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0314203241 c4) ▸
       at 4 2 (CX02 ∷ CCZ014 ∷ []) (wp0308 c4) ▸
       at 3 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸
       at 2 2 (CX02 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0382 c4) ▸ done

  b1 : Chain (CX02 ∷ Bx3-4021 ∷ CX02 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (Bx3-4021 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0383 c4) ▸
       at 0 3 (Bx3-4021 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0314203241 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- sym-bc @0210213443: 2 steps
lem-sym-bc-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-sym-bc-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0210213443 c4)) ▸
       at 0 3 (Bx2-0413 ∷ []) (lem-nat-SWbc-at0210213443 c4) ▸ done

-- sym-bc @0214233041: 2 steps
lem-sym-bc-at0214233041 : Ws → ⟪ (Bx2-4301 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym-bc-at0214233041 c4 = run b0
  where
  b0 : Chain (Bx2-4301 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at0214233041 c4)) ▸
       at 0 3 (Bx2-4031 ∷ []) (lem-nat-SWbc-at0214233041 c4) ▸ done

-- SWbc-box @02132130: 11 steps
lem-SWbc-box-at02132130 : Ws → ⟪ (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-SWbc-box-at02132130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (CX10 ∷ Bx2-3104 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx2-3104 ∷ CCZ134 ∷ []) (lem-CXbc-box-at02132130 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸
       at 1 3 (Bx2-3104 ∷ CCZ034 ∷ []) (lem-CXcb-box-at02132130 c4) ▸
       at 4 2 (CX10 ∷ CCZ134 ∷ []) (wp0712 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸
       at 2 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸ done

  b1 : Chain (CX10 ∷ Bx2-3104 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (Bx2-3104 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wp0713 c4) ▸
       at 0 3 (Bx2-3104 ∷ CCZ134 ∷ []) (lem-CXbc-box-at02132130 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- QVQ @03143041: 3 steps
lem-QVQ-at03143041 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at03143041 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at03143041 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done

-- QVQ @02132031: 3 steps
lem-QVQ-at02132031 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0636 (lit c4))) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at02132031 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

-- box-cP @0310213442: 12 steps
lem-box-cP-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at0310213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0142 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 2 4 (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at0310213442 c4) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4) ▸
       at 2 2 [] (wl0443 (lit c4)) ▸ done

-- SWbc-box @02132031: 11 steps
lem-SWbc-box-at02132031 : Ws → ⟪ (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-SWbc-box-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (CX01 ∷ Bx2-3014 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx2-3014 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02132031 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸
       at 1 3 (Bx2-3014 ∷ CCZ134 ∷ []) (lem-CXcb-box-at02132031 c4) ▸
       at 4 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸
       at 2 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸ done

  b1 : Chain (CX01 ∷ Bx2-3014 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (Bx2-3014 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp0508 c4) ▸
       at 0 3 (Bx2-3014 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02132031 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done

-- QVQ @02132130: 3 steps
lem-QVQ-at02132130 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at02132130 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 1 4 (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at02132130 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- box-cP @0213243041: 12 steps
lem-box-cP-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0213243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3401 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 2 4 (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0213243041 c4) ▸
       at 1 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243041 c4) ▸
       at 2 2 [] (wl0420 (lit c4)) ▸ done

-- SWbc-box @03122130: 11 steps
lem-SWbc-box-at03122130 : Ws → ⟪ (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-SWbc-box-at03122130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (CX10 ∷ Bx3-2104 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx3-2104 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03122130 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸
       at 1 3 (Bx3-2104 ∷ CCZ024 ∷ []) (lem-CXcb-box-at03122130 c4) ▸
       at 4 2 (CX10 ∷ CCZ124 ∷ []) (wp0672 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 2 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸ done

  b1 : Chain (CX10 ∷ Bx3-2104 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (Bx3-2104 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp0674 c4) ▸
       at 0 3 (Bx3-2104 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03122130 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- QVQ @03122031: 3 steps
lem-QVQ-at03122031 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at03122031 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 4 (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at03122031 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done

-- SWbc-box @03122031: 11 steps
lem-SWbc-box-at03122031 : Ws → ⟪ (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-SWbc-box-at03122031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (CX01 ∷ Bx3-2014 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx3-2014 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03122031 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 1 3 (Bx3-2014 ∷ CCZ124 ∷ []) (lem-CXcb-box-at03122031 c4) ▸
       at 4 2 (CX01 ∷ CCZ024 ∷ []) (wp0022 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸
       at 2 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸ done

  b1 : Chain (CX01 ∷ Bx3-2014 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (Bx3-2014 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0694 c4) ▸
       at 0 3 (Bx3-2014 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03122031 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done

-- QVQ @03122130: 3 steps
lem-QVQ-at03122130 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at03122130 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 1 4 (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at03122130 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- QVQ @02142041: 3 steps
lem-QVQ-at02142041 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at02142041 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at02142041 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

-- QVQ @0314203241: 3 steps
lem-QVQ-at0314203241 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0314203241 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0314203241 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done

-- sym-bc @021021: 2 steps
lem-sym-bc-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-sym-bc-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at021021 c4)) ▸
       at 0 3 (Bx2-0314 ∷ []) (lem-nat-SWbc-at021021 c4) ▸ done

-- QVQ @02102331: 3 steps
lem-QVQ-at02102331 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at02102331 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0636 (lit c4))) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at02102331 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

-- SWbc-box @142142: 11 steps
lem-SWbc-box-at142142 : Ws → ⟪ (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-SWbc-box-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) (CX13 ∷ Bx0-4132 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 2 3 (Bx0-4132 ∷ CCZ124 ∷ []) (lem-CXbc-box-at142142 c4) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸
       at 1 3 (Bx0-4132 ∷ CCZ234 ∷ []) (lem-CXcb-box-at142142 c4) ▸
       at 4 2 (CX13 ∷ CCZ124 ∷ []) (wl0280 (lit c4)) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸
       at 2 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸ done

  b1 : Chain (CX13 ∷ Bx0-4132 ∷ CX13 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ []) (Bx0-4132 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wl0282 (lit c4)) ▸
       at 0 3 (Bx0-4132 ∷ CCZ124 ∷ []) (lem-CXbc-box-at142142 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done

-- QVQ @03243042: 3 steps
lem-QVQ-at03243042 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at03243042 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (sym (wl0787 (lit c4))) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at03243042 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @02102331: 11 steps
lem-SWbc-box-at02102331 : Ws → ⟪ (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-SWbc-box-at02102331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) (CX31 ∷ Bx2-0314 ∷ CX31 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 2 3 (Bx2-0314 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02102331 c4) ▸
       at 3 2 (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp1230 c4) ▸
       at 1 3 (Bx2-0314 ∷ CCZ014 ∷ []) (lem-CXcb-box-at02102331 c4) ▸
       at 4 2 (CX31 ∷ CCZ034 ∷ []) (wp0127 c4) ▸
       at 3 2 (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1229 c4) ▸
       at 2 2 (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1229 c4) ▸ done

  b1 : Chain (CX31 ∷ Bx2-0314 ∷ CX31 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ []) (Bx2-0314 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp1252 c4) ▸
       at 0 3 (Bx2-0314 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02102331 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done

-- QVQ @142142: 3 steps
lem-QVQ-at142142 : Ws → ⟪ (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-QVQ-at142142 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ023 ∷ []) (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 0 0 (Toff023 ∷ Toff023 ∷ []) (sym (wl0203 (lit c4))) ▸
       at 1 4 (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at142142 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @04122041: 11 steps
lem-SWbc-box-at04122041 : Ws → ⟪ (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-SWbc-box-at04122041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) (CX03 ∷ Bx4-2031 ∷ CX03 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 4 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 2 3 (Bx4-2031 ∷ CCZ012 ∷ []) (lem-CXbc-box-at04122041 c4) ▸
       at 3 2 (CX30 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1468 (lit c4)) ▸
       at 1 3 (Bx4-2031 ∷ CCZ123 ∷ []) (lem-CXcb-box-at04122041 c4) ▸
       at 4 2 (CX03 ∷ CCZ012 ∷ []) (wl0381 (lit c4)) ▸
       at 3 2 (CX03 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl1469 (lit c4)) ▸
       at 2 2 (CX03 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl1469 (lit c4)) ▸ done

  b1 : Chain (CX03 ∷ Bx4-2031 ∷ CX03 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ []) (Bx4-2031 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wl1470 (lit c4)) ▸
       at 0 3 (Bx4-2031 ∷ CCZ012 ∷ []) (lem-CXbc-box-at04122041 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @0412233041: 3 steps
lem-QVQ-at0412233041 : Ws → ⟪ (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-QVQ-at0412233041 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Toff401 ∷ Toff401 ∷ []) (sym (wp0306 c4)) ▸
       at 1 4 (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at0412233041 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done

-- QVQ @04122041: 3 steps
lem-QVQ-at04122041 : Ws → ⟪ (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-QVQ-at04122041 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Toff413 ∷ Toff413 ∷ []) (sym (wl1474 (lit c4))) ▸
       at 1 4 (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at04122041 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done

-- sym-bc @0410213243: 2 steps
lem-sym-bc-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-sym-bc-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Bx4-0213 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at0410213243 c4)) ▸
       at 0 3 (Bx4-0213 ∷ []) (lem-nat-SWbc-at0410213243 c4) ▸ done

-- QVQ @04103143: 3 steps
lem-QVQ-at04103143 : Ws → ⟪ (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-QVQ-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Toff413 ∷ Toff413 ∷ []) (sym (wl1474 (lit c4))) ▸
       at 1 4 (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at04103143 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done

-- QVQ @04233042: 3 steps
lem-QVQ-at04233042 : Ws → ⟪ (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-QVQ-at04233042 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Toff402 ∷ Toff402 ∷ []) (sym (wp1323 c4)) ▸
       at 1 4 (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at04233042 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- SWbc-box @0412233041: 11 steps
lem-SWbc-box-at0412233041 : Ws → ⟪ (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-SWbc-box-at0412233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) (CX30 ∷ Bx4-2301 ∷ CX30 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 4 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 2 3 (Bx4-2301 ∷ CCZ123 ∷ []) (lem-CXbc-box-at0412233041 c4) ▸
       at 3 2 (CX03 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl1469 (lit c4)) ▸
       at 1 3 (Bx4-2301 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0412233041 c4) ▸
       at 4 2 (CX30 ∷ CCZ123 ∷ []) (wl1324 (lit c4)) ▸
       at 3 2 (CX30 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1468 (lit c4)) ▸
       at 2 2 (CX30 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1468 (lit c4)) ▸ done

  b1 : Chain (CX30 ∷ Bx4-2301 ∷ CX30 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ CCZ012 ∷ CCZ123 ∷ []) (Bx4-2301 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl1497 (lit c4)) ▸
       at 0 3 (Bx4-2301 ∷ CCZ123 ∷ []) (lem-CXbc-box-at0412233041 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- SWbc-box @041041: 11 steps
lem-SWbc-box-at041041 : Ws → ⟪ (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ []) ⟫ʷ
lem-SWbc-box-at041041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) (CX23 ∷ Bx4-0231 ∷ CX23 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 3 (Bx4-0231 ∷ CCZ012 ∷ []) (lem-CXbc-box-at041041 c4) ▸
       at 3 2 (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4)) ▸
       at 1 3 (Bx4-0231 ∷ CCZ013 ∷ []) (lem-CXcb-box-at041041 c4) ▸
       at 4 2 (CX23 ∷ CCZ012 ∷ []) (wl0411 (lit c4)) ▸
       at 3 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸ done

  b1 : Chain (CX23 ∷ Bx4-0231 ∷ CX23 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ []) (Bx4-0231 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wl1568 (lit c4)) ▸
       at 0 3 (Bx4-0231 ∷ CCZ012 ∷ []) (lem-CXbc-box-at041041 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @0410233241: 3 steps
lem-QVQ-at0410233241 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0410233241 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 1 4 (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0410233241 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

-- QVQ @0412213043: 3 steps
lem-QVQ-at0412213043 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at0412213043 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (sym (wp0317 c4)) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at0412213043 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- SWbc-box @04233240: 11 steps
lem-SWbc-box-at04233240 : Ws → ⟪ (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-SWbc-box-at04233240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) (CX32 ∷ Bx4-1320 ∷ CX32 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 4 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 2 3 (Bx4-1320 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04233240 c4) ▸
       at 3 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸
       at 1 3 (Bx4-1320 ∷ CCZ012 ∷ []) (lem-CXcb-box-at04233240 c4) ▸
       at 4 2 (CX32 ∷ CCZ013 ∷ []) (wl0706 (lit c4)) ▸
       at 3 2 (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4)) ▸
       at 2 2 (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4)) ▸ done

  b1 : Chain (CX32 ∷ Bx4-1320 ∷ CX32 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ []) (Bx4-1320 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wl1591 (lit c4)) ▸
       at 0 3 (Bx4-1320 ∷ CCZ013 ∷ []) (lem-CXbc-box-at04233240 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done

-- QVQ @0440: 3 steps
lem-QVQ-at0440 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at0440 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (sym (wp0317 c4)) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at0440 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- SWbc-box @0413203142: 11 steps
lem-SWbc-box-at0413203142 : Ws → ⟪ (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-SWbc-box-at0413203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) (CX01 ∷ Bx4-3012 ∷ CX01 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0413203142 c4) ▸
       at 3 2 (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) (wl1600 (lit c4)) ▸
       at 1 3 (Bx4-3012 ∷ CCZ123 ∷ []) (lem-CXcb-box-at0413203142 c4) ▸
       at 4 2 (CX01 ∷ CCZ023 ∷ []) (wl0560 (lit c4)) ▸
       at 3 2 (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1601 (lit c4)) ▸
       at 2 2 (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1601 (lit c4)) ▸ done

  b1 : Chain (CX01 ∷ Bx4-3012 ∷ CX01 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ []) (Bx4-3012 ∷ [])
  b1 = at 3 5 (CCZ023 ∷ []) (wl1602 (lit c4)) ▸
       at 0 3 (Bx4-3012 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0413203142 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸ done

-- QVQ @02142140: 3 steps
lem-QVQ-at02142140 : Ws → ⟪ (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-QVQ-at02142140 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ023 ∷ []) (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ [])
  b0 = at 0 0 (Toff203 ∷ Toff203 ∷ []) (sym (wl0635 (lit c4))) ▸
       at 1 4 (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at02142140 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @0413213042: 11 steps
lem-SWbc-box-at0413213042 : Ws → ⟪ (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-SWbc-box-at0413213042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) (CX10 ∷ Bx4-3102 ∷ CX10 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx4-3102 ∷ CCZ123 ∷ []) (lem-CXbc-box-at0413213042 c4) ▸
       at 3 2 (CX01 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1601 (lit c4)) ▸
       at 1 3 (Bx4-3102 ∷ CCZ023 ∷ []) (lem-CXcb-box-at0413213042 c4) ▸
       at 4 2 (CX10 ∷ CCZ123 ∷ []) (wl0616 (lit c4)) ▸
       at 3 2 (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) (wl1600 (lit c4)) ▸
       at 2 2 (CX10 ∷ CCZ123 ∷ CCZ023 ∷ []) (wl1600 (lit c4)) ▸ done

  b1 : Chain (CX10 ∷ Bx4-3102 ∷ CX10 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ CCZ023 ∷ CCZ123 ∷ []) (Bx4-3102 ∷ [])
  b1 = at 3 5 (CCZ123 ∷ []) (wl1604 (lit c4)) ▸
       at 0 3 (Bx4-3102 ∷ CCZ123 ∷ []) (lem-CXbc-box-at0413213042 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸ done

-- QVQ @0413203142: 3 steps
lem-QVQ-at0413203142 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0413203142 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 1 4 (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0413203142 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

-- SWbc-box @0440: 11 steps
lem-SWbc-box-at0440 : Ws → ⟪ (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-SWbc-box-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) (CX23 ∷ Bx4-1230 ∷ CX23 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 4 1 (CX23 ∷ CX32 ∷ CX23 ∷ []) (sym (wl0258 (lit c4))) ▸
       at 2 3 (Bx4-1230 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0440 c4) ▸
       at 3 2 (CX32 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1566 (lit c4)) ▸
       at 1 3 (Bx4-1230 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0440 c4) ▸
       at 4 2 (CX23 ∷ CCZ012 ∷ []) (wl0411 (lit c4)) ▸
       at 3 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl1567 (lit c4)) ▸ done

  b1 : Chain (CX23 ∷ Bx4-1230 ∷ CX23 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ CCZ013 ∷ CCZ012 ∷ []) (Bx4-1230 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wl1568 (lit c4)) ▸
       at 0 3 (Bx4-1230 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0440 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @0413213240: 3 steps
lem-QVQ-at0413213240 : Ws → ⟪ (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-QVQ-at0413213240 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Toff402 ∷ Toff402 ∷ []) (sym (wp1323 c4)) ▸
       at 1 4 (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at0413213240 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done

-- SWbc-box @0412233140: 11 steps
lem-SWbc-box-at0412233140 : Ws → ⟪ (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-SWbc-box-at0412233140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) (CX31 ∷ Bx4-2310 ∷ CX31 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 2 3 (Bx4-2310 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0412233140 c4) ▸
       at 3 2 (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) (wl1666 (lit c4)) ▸
       at 1 3 (Bx4-2310 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0412233140 c4) ▸
       at 4 2 (CX31 ∷ CCZ023 ∷ []) (wl1343 (lit c4)) ▸
       at 3 2 (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1667 (lit c4)) ▸
       at 2 2 (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1667 (lit c4)) ▸ done

  b1 : Chain (CX31 ∷ Bx4-2310 ∷ CX31 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ []) (Bx4-2310 ∷ [])
  b1 = at 3 5 (CCZ023 ∷ []) (wl1668 (lit c4)) ▸
       at 0 3 (Bx4-2310 ∷ CCZ023 ∷ []) (lem-CXbc-box-at0412233140 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸ done

-- QVQ @0410233142: 3 steps
lem-QVQ-at0410233142 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0410233142 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 1 4 (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0410233142 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

-- SWbc-box @04122140: 11 steps
lem-SWbc-box-at04122140 : Ws → ⟪ (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-SWbc-box-at04122140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) (CX13 ∷ Bx4-2130 ∷ CX13 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 2 3 (Bx4-2130 ∷ CCZ012 ∷ []) (lem-CXbc-box-at04122140 c4) ▸
       at 3 2 (CX31 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1667 (lit c4)) ▸
       at 1 3 (Bx4-2130 ∷ CCZ023 ∷ []) (lem-CXcb-box-at04122140 c4) ▸
       at 4 2 (CX13 ∷ CCZ012 ∷ []) (wl0167 (lit c4)) ▸
       at 3 2 (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) (wl1666 (lit c4)) ▸
       at 2 2 (CX13 ∷ CCZ012 ∷ CCZ023 ∷ []) (wl1666 (lit c4)) ▸ done

  b1 : Chain (CX13 ∷ Bx4-2130 ∷ CX13 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ CCZ023 ∷ CCZ012 ∷ []) (Bx4-2130 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wl1679 (lit c4)) ▸
       at 0 3 (Bx4-2130 ∷ CCZ012 ∷ []) (lem-CXbc-box-at04122140 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- QVQ @0412233140: 3 steps
lem-QVQ-at0412233140 : Ws → ⟪ (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-QVQ-at0412233140 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Toff401 ∷ Toff401 ∷ []) (sym (wp0306 c4)) ▸
       at 1 4 (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at0412233140 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done

-- XCSX-box-2 @04122041: 4 steps
lem-XCSX-box-2-at04122041 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-XCSX-box-2-at04122041 c4 = run b0
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 0 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 1 2 (Bx4-2031 ∷ CS04⁻ ∷ []) (lem-CSdu-box-2-at04122041 c4) ▸
       at 0 2 (Bx4-2031 ∷ S4 ∷ []) (lem-Su-box-at04122041 c4) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done

-- QVQ @0413203241: 3 steps
lem-QVQ-at0413203241 : Ws → ⟪ (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-QVQ-at0413203241 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ124 ∷ []) (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ [])
  b0 = at 0 0 (Toff412 ∷ Toff412 ∷ []) (sym (wl0470 (lit c4))) ▸
       at 1 4 (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at0413203241 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done

-- QVQ @04122140: 3 steps
lem-QVQ-at04122140 : Ws → ⟪ (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-QVQ-at04122140 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ [])
  b0 = at 0 0 (Toff403 ∷ Toff403 ∷ []) (sym (wp0317 c4)) ▸
       at 1 4 (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at04122140 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done

-- F4-S0-CS1 @0440: 13 steps
lem-F4-S0-CS1-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS1-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 4 (Bx4-1023 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-XCSX-box-2-at04203243 c4) ▸
       at 1 4 (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1500 c4)) ▸
       at 2 4 (CS13 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1501 c4)) ▸
       at 3 4 (Toff302 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1500 c4)) ▸
       at 4 4 (CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1502 c4)) ▸ done

  b1 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b1 = at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done

-- SWbc-box @04133140: 11 steps
lem-SWbc-box-at04133140 : Ws → ⟪ (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-SWbc-box-at04133140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) (CX21 ∷ Bx4-3210 ∷ CX21 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 4 1 (CX21 ∷ CX12 ∷ CX21 ∷ []) (sym (wl0835 (lit c4))) ▸
       at 2 3 (Bx4-3210 ∷ CCZ023 ∷ []) (lem-CXbc-box-at04133140 c4) ▸
       at 3 2 (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4)) ▸
       at 1 3 (Bx4-3210 ∷ CCZ013 ∷ []) (lem-CXcb-box-at04133140 c4) ▸
       at 4 2 (CX21 ∷ CCZ023 ∷ []) (wl0674 (lit c4)) ▸
       at 3 2 (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4)) ▸
       at 2 2 (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4)) ▸ done

  b1 : Chain (CX21 ∷ Bx4-3210 ∷ CX21 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ []) (Bx4-3210 ∷ [])
  b1 = at 3 5 (CCZ023 ∷ []) (wl1729 (lit c4)) ▸
       at 0 3 (Bx4-3210 ∷ CCZ023 ∷ []) (lem-CXbc-box-at04133140 c4) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸ done

-- SWbc-box @0413213240: 11 steps
lem-SWbc-box-at0413213240 : Ws → ⟪ (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-SWbc-box-at0413213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) (CX12 ∷ Bx4-3120 ∷ CX12 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx4-3120 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0413213240 c4) ▸
       at 3 2 (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4)) ▸
       at 1 3 (Bx4-3120 ∷ CCZ023 ∷ []) (lem-CXcb-box-at0413213240 c4) ▸
       at 4 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 3 2 (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4)) ▸
       at 2 2 (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4)) ▸ done

  b1 : Chain (CX12 ∷ Bx4-3120 ∷ CX12 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ []) (Bx4-3120 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wl1481 (lit c4)) ▸
       at 0 3 (Bx4-3120 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0413213240 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done
