{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D017 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0305 ; wl0443 ; wl0452 ; wl1319 ; wp0019 ; wp0161 ; wp0351 ; wp1189 ; wl0344 ; wl0433 ; wl0508 ; wl0635 ; wl0636 ; wl0765 ; wl0788 ; wp0661 ; wp0687 ; wp1187 ; wp1232 ; wp0051 ; wp0053 ; wp0054 ; wp0061 ; wp0065 ; wl0207 ; wl0341 ; wl0457 ; wl0461 ; wl0463 ; wl0929 ; wl1271 ; wl1441 ; wl1443 ; wl1474 ; wl1501 ; wl1509 ; wl1515 ; wp0060 ; wp0062 ; wp0064 ; wp0090 ; wp0212 ; wp0218 ; wp0306 ; wp1318 ; wp1323 ; wp1331 ; wp1335 ; wp1350 ; wl1431 ; wl1446 ; wl1448 ; wl1516 ; wl1517 ; wl1518 ; wl1519 ; wl1520 ; wl1521 ; wl1522 ; wl1523 ; wl1524 ; wl1525 ; wl1526 ; wl1527 ; wl1528 ; wl1529 ; wl1533 ; wl1534 ; wp0155 ; wp0156 ; wp0157 ; wp0311 ; wp1019 ; wp1023 ; wp1351 ; wp1352 ; wp1353 ; wp1354 ; wp1355 ; wp1356 ; wp1357 ; wp1358 ; wp1360 ; wl0470 ; wl1557 ; wl1558 ; wl1585 ; wp0317 ; wp0516 ; wp0598 ; wp0733 ; wp0766 ; wp0992 ; wp1383 ; wp1395 ; wl1596 ; wl0293 ; wl0324 ; wl0763 ; wl1204 ; wl1321 ; wl1329 ; wl1353 ; wl1635 ; wl1636 ; wl1643 ; wl1644 ; wl1645 ; wl1652 ; wl1653 ; wl1654 ; wp0184 ; wp0185 ; wp0523 ; wp0685 ; wp0732 ; wp0776 ; wp1071 ; wp1143 ; wp1171 ; wp1185 ; wp1186 ; wp1288 ; wp1436 ; wp1437 ; wl0675 ; wl1682 ; wl1683 ; wl1684 ; wl1685 ; wl1686 ; wl1687 ; wl1688 ; wp0269 ; wp0722 ; wl0756 ; wp1281 ; wp1476 ; wp1477 ; wp1478)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab-at0210243143 ; lem-sym-ab-at0310243142 ; lem-sym-ab-at032032 ; lem-sym-ab-at13243142)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at022330 ; lem-sym-ab-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-nat-SWbc-at041041 ; lem-nat-SWbc-at0413203142 ; lem-nat-SWbc-at0413213042 ; lem-nat-SWbc-at04233240 ; lem-nat-SWbc-at0440 ; lem-sym-ab-at02102331 ; lem-sym-ab-at031031)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at03102132 ; lem-box-tQ-at032032 ; lem-box-tQ-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at0310213442 ; lem-nat-SWbc-at02102331 ; lem-nat-SWbc-at04122041 ; lem-nat-SWbc-at04122140 ; lem-nat-SWbc-at0412233041 ; lem-nat-SWbc-at0412233140 ; lem-nat-SWbc-at0413213240 ; lem-nat-SWbc-at04133140 ; lem-nat-SWbc-at142142)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-t-cP-at03102132 ; lem-t-cP-at032032 ; lem-tP-at02102331 ; lem-tP-at02142041 ; lem-tP-at0314203241 ; lem-tP-at03243042 ; lem-tP-at04103143 ; lem-tP-at04122041 ; lem-tP-at0412233041 ; lem-tP-at04233042 ; lem-tP-at142142)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-P-box-at0410213243 ; lem-P-box-at04203243 ; lem-box-tQ-at0412233041 ; lem-box-tQ-at0412233140 ; lem-t-cP-at0310213442 ; lem-t-cP-at04203243 ; lem-tP-at02142140 ; lem-tP-at0410233142 ; lem-tP-at0410233241 ; lem-tP-at0412213043 ; lem-tP-at04122140 ; lem-tP-at0412233140 ; lem-tP-at0413203142 ; lem-tP-at0413203241 ; lem-tP-at0413213240 ; lem-tP-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at03102132 ; lem-box-cP-at032032 ; lem-box-cP-at0410213243 ; lem-box-cP-at04203243 ; lem-sym-bc-at0220 ; lem-sym-bc-at03102132 ; lem-sym-bc-at0310213442 ; lem-sym-bc-at032032 ; lem-sym-bc-at04203243 ; lem-sym-bc-at14233142)
open import Examples.Groups.Clifford+CS.Five.D.D015 using (lem-QVQ-at02102331 ; lem-QVQ-at02142041 ; lem-QVQ-at02142140 ; lem-QVQ-at0314203241 ; lem-QVQ-at03243042 ; lem-QVQ-at0410233142 ; lem-QVQ-at0410233241 ; lem-QVQ-at04103143 ; lem-QVQ-at04122041 ; lem-QVQ-at0412213043 ; lem-QVQ-at04122140 ; lem-QVQ-at0412233041 ; lem-QVQ-at0412233140 ; lem-QVQ-at0413203142 ; lem-QVQ-at0413203241 ; lem-QVQ-at0413213240 ; lem-QVQ-at04233042 ; lem-QVQ-at0440 ; lem-QVQ-at142142 ; lem-SWbc-box-at02102331 ; lem-SWbc-box-at041041 ; lem-SWbc-box-at04122041 ; lem-SWbc-box-at04122140 ; lem-SWbc-box-at0412233041 ; lem-SWbc-box-at0412233140 ; lem-SWbc-box-at0413203142 ; lem-SWbc-box-at0413213042 ; lem-SWbc-box-at0413213240 ; lem-SWbc-box-at04133140 ; lem-SWbc-box-at04233240 ; lem-SWbc-box-at0440 ; lem-SWbc-box-at142142 ; lem-XCSX-box-2-at04122041 ; lem-box-cP-at0213243041 ; lem-box-cP-at0310213442 ; lem-sym-bc-at021021 ; lem-sym-bc-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS23-CCZ014 ; lem-comm-CS24-CCZ013 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CX40-CCZ123)

-- box2 @03102132: 11 steps
lem-box2-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0124 ∷ Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 4 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 4 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 5 5 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) (lem-t-cP-at03102132 c4) ▸
       at 5 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸
       at 5 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) []
  b1 = at 2 2 [] (wl0443 (lit c4)) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸
       at 0 2 [] (wl0443 (lit c4)) ▸ done

-- box-cP @02142041: 12 steps
lem-box-cP-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4031 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at02142041 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4) ▸
       at 2 2 [] (wp0019 c4) ▸ done

-- box-cP @0314203241: 12 steps
lem-box-cP-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4021 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0314203241 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4) ▸
       at 2 2 [] (wp0351 c4) ▸ done

-- box-perm-1324 @032032: 1 steps
lem-box-perm-1324-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-1324-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸ done

-- box-perm-3124 @032032: 2 steps
lem-box-perm-3124-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-box-perm-3124-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 1 (Bx3-1204 ∷ []) (lem-sym-bc-at032032 c4) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-sym-ab-at0330 c4) ▸ done

-- box-perm-3124 @0220: 2 steps
lem-box-perm-3124-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-box-perm-3124-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 1 (Bx2-1304 ∷ []) (lem-sym-bc-at0220 c4) ▸
       at 0 1 (Bx2-3104 ∷ []) (lem-sym-ab-at022330 c4) ▸ done

-- box-perm-3214 @032032: 3 steps
lem-box-perm-3214-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-box-perm-3214-at032032 c4 = run b0
  where
  b0 : Chain (Bx3-1024 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ []) (lem-sym-ab-at032032 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-sym-bc-at03102132 c4) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-sym-ab-at031031 c4) ▸ done

-- box-perm-1324 @021021: 1 steps
lem-box-perm-1324-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-box-perm-1324-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  b0 = at 0 1 (Bx2-0314 ∷ []) (lem-sym-bc-at021021 c4) ▸ done

-- box-cP @02102331: 12 steps
lem-box-cP-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at02102331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0314 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at02102331 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02102331 c4) ▸
       at 2 2 [] (wl0635 (lit c4)) ▸ done

-- sym-bc @142142: 2 steps
lem-sym-bc-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-sym-bc-at142142 c4 = run b0
  where
  b0 : Chain (Bx0-4132 ∷ []) (Bx0-4312 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-4132 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at142142 c4)) ▸
       at 0 3 (Bx0-4312 ∷ []) (lem-nat-SWbc-at142142 c4) ▸ done

-- box-perm-2314 @13243142: 2 steps
lem-box-perm-2314-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-2314-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-4132 ∷ [])
  b0 = at 0 1 (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4) ▸
       at 0 1 (Bx0-4132 ∷ []) (lem-sym-bc-at14233142 c4) ▸ done

-- box-cP @03243042: 12 steps
lem-box-cP-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at03243042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1402 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at03243042 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243042 c4) ▸
       at 2 2 [] (wl0788 (lit c4)) ▸ done

-- box-perm-3124 @021021: 2 steps
lem-box-perm-3124-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-box-perm-3124-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 1 (Bx2-0314 ∷ []) (lem-sym-bc-at021021 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-sym-ab-at02102331 c4) ▸ done

-- sym-bc @02102331: 2 steps
lem-sym-bc-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym-bc-at02102331 c4 = run b0
  where
  b0 : Chain (Bx2-0314 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx2-0314 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at02102331 c4)) ▸
       at 0 3 (Bx2-0134 ∷ []) (lem-nat-SWbc-at02102331 c4) ▸ done

-- box-cP @142142: 12 steps
lem-box-cP-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4132 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 2 4 (Toff023 ∷ Toff014 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-QVQ-at142142 c4) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4) ▸
       at 2 2 [] (wp0051 c4) ▸ done

-- box2 @032032: 11 steps
lem-box2-at032032 : Ws → ⟪ (Bx3-1024 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at032032 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1024 ∷ Bx3-1024 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 4 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 4 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 5 5 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) (lem-t-cP-at032032 c4) ▸
       at 5 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 5 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at032032 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) []
  b1 = at 2 2 [] (wl0443 (lit c4)) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸
       at 0 2 [] (wl0443 (lit c4)) ▸ done

-- sym-bc @04122041: 2 steps
lem-sym-bc-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-sym-bc-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-2301 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at04122041 c4)) ▸
       at 0 3 (Bx4-2301 ∷ []) (lem-nat-SWbc-at04122041 c4) ▸ done

-- box-cP @0412233041: 12 steps
lem-box-cP-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-box-cP-at0412233041 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ024 ∷ Toff204 ∷ CZ12 ∷ Toff204 ∷ CCZ024 ∷ CZ12 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp0218 c4)) ▸
       at 2 4 (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-QVQ-at0412233041 c4) ▸
       at 1 2 (Toff401 ∷ Toff423 ∷ []) (lem-tP-at0412233041 c4) ▸
       at 2 2 [] (wl0457 (lit c4)) ▸ done

-- box-cP @04122041: 12 steps
lem-box-cP-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-box-cP-at04122041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2031 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 2 4 (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-QVQ-at04122041 c4) ▸
       at 1 2 (Toff413 ∷ Toff402 ∷ []) (lem-tP-at04122041 c4) ▸
       at 2 2 [] (wp1323 c4) ▸ done

-- box-cP @04103143: 12 steps
lem-box-cP-at04103143 : Ws → ⟪ (Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-box-cP-at04103143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0213 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ CZ03 ∷ Toff014 ∷ CCZ014 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp1331 c4) ▸
       at 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ CZ03 ∷ Toff014 ∷ CCZ014 ∷ CZ03 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1331 c4) ▸
       at 2 4 (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-QVQ-at04103143 c4) ▸
       at 1 2 (Toff413 ∷ Toff402 ∷ []) (lem-tP-at04103143 c4) ▸
       at 2 2 [] (wp1323 c4) ▸ done

-- box-cP @04233042: 12 steps
lem-box-cP-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-box-cP-at04233042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1302 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 2 4 (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-QVQ-at04233042 c4) ▸
       at 1 2 (Toff402 ∷ Toff413 ∷ []) (lem-tP-at04233042 c4) ▸
       at 2 2 [] (wl1474 (lit c4)) ▸ done

-- pairs @0410213243: 4 steps
lem-pairs-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-pairs-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Bx4-2301 ∷ [])
  b0 = at 0 1 (Toff423 ∷ Bx4-0123 ∷ Toff423 ∷ []) (sym (lem-P-box-at0410213243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 4 2 [] (wl0457 (lit c4)) ▸
       at 0 4 (Bx4-2301 ∷ []) (sym (lem-box-tQ-at0412233041 c4)) ▸ done

-- sym-bc @0412233041: 2 steps
lem-sym-bc-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-sym-bc-at0412233041 c4 = run b0
  where
  b0 : Chain (Bx4-2301 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at0412233041 c4)) ▸
       at 0 3 (Bx4-2031 ∷ []) (lem-nat-SWbc-at0412233041 c4) ▸ done

-- F4-CS1-K1 @0440: 19 steps
lem-F4-CS1-K1-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-K1-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ []) (X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K1 ∷ CK01 ∷ Toff423 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (sym (wl1441 (lit c4))) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK01 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1515 (lit c4))) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 5 2 (CK01 ∷ Toff423 ∷ []) (sym (c₂ (CK₀₁) (Toffᵗ))) ▸ done

  b1 : Chain (X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K1 ∷ CK01 ∷ Toff423 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b1 = at 6 2 (S0 ∷ Toff423 ∷ []) (sym (c₁ (S) (Toffᵗ ↑))) ▸
       at 3 4 (K1 ∷ CK01 ∷ S0 ∷ CCZ014 ∷ []) (wp1350 c4) ▸
       at 2 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 3 2 (CK01 ∷ Toff423 ∷ []) (sym (c₂ (CK₀₁) (Toffᵗ))) ▸
       at 4 2 (S0 ∷ Toff423 ∷ []) (sym (c₁ (S) (Toffᵗ ↑))) ▸
       at 1 4 (K1 ∷ CK01 ∷ S0 ∷ CCZ014 ∷ []) (wp1350 c4) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b2 = at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 0 4 (CK01 ∷ X0 ∷ []) (sym (wl1443 (lit c4))) ▸ done

-- F4-CS1-CS1 @0440: 286 steps
lem-F4-CS1-CS1-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS1-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 4 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸
       at 4 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CCZ014 ∷ CS13⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wp1353 c4) ▸
       at 6 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 5 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 5 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b3 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CCZ014 ∷ CS13⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b3 = at 6 2 (Toff423 ∷ CS13⁻ ∷ []) (wl1517 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 8 2 (Toff423 ∷ CS13⁻ ∷ []) (wl1517 (lit c4)) ▸
       at 5 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 5 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b5 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b5 = at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 12 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 7 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 8 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff402 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b6 = at 6 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸
       at 9 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 8 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 12 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 11 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 10 2 (Toff423 ∷ CS02⁻ ∷ []) (wp1355 c4) ▸
       at 9 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸ done

  b7 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff402 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b7 = at 9 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 7 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸
       at 8 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 3 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 4 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ014 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b8 = at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 3 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 8 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 7 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Bx4-1023 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ014 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ014 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b9 = at 5 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 4 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 2 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 3 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 3 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸ done

  b10 : Chain (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ014 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b10 = at 10 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 6 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸ done

  b11 : Chain (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CCZ012 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b11 = at 7 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 6 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 10 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 9 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS02⁻ ∷ []) (wp1355 c4) ▸
       at 7 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

  b12 : Chain (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CCZ012 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b12 = at 5 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸
       at 6 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 2 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸
       at 1 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b13 : Chain (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b13 = at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸ done

  b14 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b14 = at 3 3 (X0 ∷ []) (wp1353 c4) ▸
       at 4 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b15 : Chain (Bx4-1023 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b15 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b16 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b16 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 8 (CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) (sym (wl1518 (lit c4))) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b17 : Chain (Bx4-1023 ∷ X0 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b17 = at 3 3 (Toff302 ∷ CS13 ∷ CCZ012 ∷ []) (wl1519 (lit c4)) ▸
       at 5 2 [] (wl0341 (lit c4)) ▸
       at 4 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b18 : Chain (Bx4-1023 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b18 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX23 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1521 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 5 2 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (sym (wl1522 (lit c4))) ▸
       at 7 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 4 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1358 c4) ▸ done

  b19 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 10 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b20 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff423 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b20 = at 9 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 3 2 (CX24 ∷ Toff423 ∷ []) (sym (wl1523 (lit c4))) ▸
       at 5 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 4 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 5 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 6 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 7 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 8 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸ done

  b21 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff423 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ CX23 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Toff423 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b21 = at 4 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 5 2 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (sym (wl1522 (lit c4))) ▸
       at 7 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 9 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 8 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 9 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 10 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 11 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸ done

  b22 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ CX23 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Toff423 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b22 = at 12 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 8 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 9 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸
       at 5 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 3 4 (CX23 ∷ Toff302 ∷ []) (wl1524 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b23 : Chain (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CX23 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 4 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 3 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b24 : Chain (Bx4-1023 ∷ X0 ∷ CX23 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS13 ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b24 = at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸
       at 4 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS13 ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b25 = at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS13 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1527 (lit c4))) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 6 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done

  b26 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ [])
  b26 = at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b27 = at 5 6 (CX23 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1521 (lit c4))) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 7 2 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (sym (wl1522 (lit c4))) ▸
       at 9 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 6 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1358 c4) ▸
       at 12 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b28 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 12 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 16 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 11 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b29 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ Toff423 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b29 = at 5 2 (CX24 ∷ Toff423 ∷ []) (sym (wl1523 (lit c4))) ▸
       at 7 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 6 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 7 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 8 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 9 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 10 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

  b30 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ Toff423 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ CX23 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff423 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b30 = at 7 2 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (sym (wl1522 (lit c4))) ▸
       at 9 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 11 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 10 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 11 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 12 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 13 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 14 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸ done

  b31 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ CX23 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff423 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b31 = at 10 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 11 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 5 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸
       at 7 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 5 4 (CX23 ∷ Toff302 ∷ []) (wl1524 (lit c4)) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b32 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ Toff302 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 6 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done

  b33 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ Toff302 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸
       at 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13⁻ ∷ X0 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b34 = at 6 5 (CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1529 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff423 ∷ []) (sym (wl1517 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 2 (CS13⁻ ∷ Toff423 ∷ []) (sym (wl1517 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸ done

  b35 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b35 = at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸ done

-- F4-I-CS1 @0440: 15 steps
lem-F4-I-CS1-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS1-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 4 (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1360 c4)) ▸
       at 1 4 (Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1533 (lit c4))) ▸
       at 2 4 (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1360 c4)) ▸
       at 3 4 (Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1533 (lit c4))) ▸ done

  b1 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b1 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 7 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1534 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S0⁻ ∷ []) (wl1431 (lit c4)) ▸
       at 1 2 (X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1431 (lit c4))) ▸ done

-- F4-CS1-I @0440: 15 steps
lem-F4-CS1-I-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-I-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ S0 ∷ []) (X0 ∷ CCZ014 ∷ Toff423 ∷ ι ∷ S0⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (ι ∷ S0⁻ ∷ X0 ∷ []) (wl1446 (lit c4)) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 6 (ι ∷ S0⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (wl1557 (lit c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 3 (ι ∷ S0⁻ ∷ Toff423 ∷ []) (wl1558 (lit c4)) ▸
       at 3 3 (ι ∷ S0⁻ ∷ CCZ014 ∷ []) (wp1383 c4) ▸ done

  b1 : Chain (X0 ∷ CCZ014 ∷ Toff423 ∷ ι ∷ S0⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (S0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b1 = at 2 3 (ι ∷ S0⁻ ∷ Toff423 ∷ []) (wl1558 (lit c4)) ▸
       at 1 3 (ι ∷ S0⁻ ∷ CCZ014 ∷ []) (wp1383 c4) ▸
       at 3 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 5 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 7 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 0 3 (S0 ∷ X0 ∷ []) (sym (wl1448 (lit c4))) ▸ done

-- box-perm-1324 @04203243: 1 steps
lem-box-perm-1324-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-1324-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-1203 ∷ [])
  b0 = at 0 1 (Bx4-1203 ∷ []) (lem-sym-bc-at04203243 c4) ▸ done

-- sym-bc @041041: 2 steps
lem-sym-bc-at041041 : Ws → ⟪ (Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-sym-bc-at041041 c4 = run b0
  where
  b0 : Chain (Bx4-0231 ∷ []) (Bx4-0321 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx4-0231 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at041041 c4)) ▸
       at 0 3 (Bx4-0321 ∷ []) (lem-nat-SWbc-at041041 c4) ▸ done

-- box-cP @0410233241: 12 steps
lem-box-cP-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0410233241 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ024 ∷ Toff024 ∷ CZ01 ∷ Toff024 ∷ CCZ024 ∷ CZ01 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp0516 c4) ▸
       at 2 4 (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-QVQ-at0410233241 c4) ▸
       at 1 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0410233241 c4) ▸
       at 2 2 [] (wp0317 c4) ▸ done

-- box-cP @0412213043: 12 steps
lem-box-cP-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at0412213043 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ024 ∷ Toff204 ∷ CZ23 ∷ Toff204 ∷ CCZ024 ∷ CZ23 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0598 c4) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at0412213043 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0412213043 c4) ▸
       at 2 2 [] (wl0470 (lit c4)) ▸ done

-- F4-K1-CS1 @0440: 17 steps
lem-F4-K1-CS1-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-CS1-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (CCZ014 ∷ Toff423 ∷ X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 4 (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1395 c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 2 2 (Toff423 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Toffᵗ)) ▸
       at 1 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff423 ∷ X0 ∷ CK01 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b1 = at 2 4 (CCZ014 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wp1395 c4)) ▸
       at 5 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 4 2 (Toff423 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Toffᵗ)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 7 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (sym (wl1585 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b2 : Chain (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  b2 = at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸ done

-- sym-bc @04233240: 2 steps
lem-sym-bc-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-sym-bc-at04233240 c4 = run b0
  where
  b0 : Chain (Bx4-1320 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx4-1320 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at04233240 c4)) ▸
       at 0 3 (Bx4-1230 ∷ []) (lem-nat-SWbc-at04233240 c4) ▸ done

-- box-cP @0440: 12 steps
lem-box-cP-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at0440 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at0440 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0440 c4) ▸
       at 2 2 [] (wl0470 (lit c4)) ▸ done

-- sym-bc @0413203142: 2 steps
lem-sym-bc-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-sym-bc-at0413203142 c4 = run b0
  where
  b0 : Chain (Bx4-3012 ∷ []) (Bx4-3102 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx4-3012 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0413203142 c4)) ▸
       at 0 3 (Bx4-3102 ∷ []) (lem-nat-SWbc-at0413203142 c4) ▸ done

-- box-cP @02142140: 12 steps
lem-box-cP-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at02142140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4130 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 2 4 (Toff203 ∷ Toff214 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-QVQ-at02142140 c4) ▸
       at 1 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at02142140 c4) ▸
       at 2 2 [] (wl0636 (lit c4)) ▸ done

-- sym-bc @0413213042: 2 steps
lem-sym-bc-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-sym-bc-at0413213042 c4 = run b0
  where
  b0 : Chain (Bx4-3102 ∷ []) (Bx4-3012 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx4-3102 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at0413213042 c4)) ▸
       at 0 3 (Bx4-3012 ∷ []) (lem-nat-SWbc-at0413213042 c4) ▸ done

-- box-cP @0413203142: 12 steps
lem-box-cP-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0413203142 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ134 ∷ Toff314 ∷ CZ23 ∷ Toff314 ∷ CCZ134 ∷ CZ23 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl1596 (lit c4))) ▸
       at 2 4 (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-QVQ-at0413203142 c4) ▸
       at 1 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0413203142 c4) ▸
       at 2 2 [] (wp0317 c4) ▸ done

-- sym-bc @0440: 2 steps
lem-sym-bc-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-sym-bc-at0440 c4 = run b0
  where
  b0 : Chain (Bx4-1230 ∷ []) (Bx4-1320 ∷ [])
  b0 = at 0 1 (Sw23 ∷ Bx4-1230 ∷ Sw23 ∷ []) (sym (lem-SWbc-box-at0440 c4)) ▸
       at 0 3 (Bx4-1320 ∷ []) (lem-nat-SWbc-at0440 c4) ▸ done

-- box-cP @0413213240: 12 steps
lem-box-cP-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-box-cP-at0413213240 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 2 4 (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-QVQ-at0413213240 c4) ▸
       at 1 2 (Toff402 ∷ Toff413 ∷ []) (lem-tP-at0413213240 c4) ▸
       at 2 2 [] (wl1474 (lit c4)) ▸ done

-- box-perm-3124 @0310213442: 2 steps
lem-box-perm-3124-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-3124-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸ done

-- box-box-4 @0314203142: 103 steps
lem-box-box-4-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-4012 ∷ []) ⟫ʷ
lem-box-box-4-at0314203142 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (run b12))))))))))))
  where
  b0 : Chain (Bx3-4012 ∷ Bx2-3401 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CCZ234 ∷ CX30 ∷ CS13 ∷ CCZ123 ∷ Toff201 ∷ [])
  b0 = at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 4 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 2 (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1635 (lit c4)) ▸
       at 6 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CCZ234 ∷ CX30 ∷ CS13 ∷ CCZ123 ∷ Toff201 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff304 ∷ CCZ024 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 6 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 5 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl1353 (lit c4))) ▸
       at 6 3 (Toff201 ∷ CCZ123 ∷ []) (wl1636 (lit c4)) ▸
       at 3 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 3 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff304 ∷ CCZ024 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ K3 ∷ Toff201 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ [])
  b2 = at 4 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸ done

  b3 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ K3 ∷ Toff201 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ024 ∷ Toff201 ∷ CCZ123 ∷ [])
  b3 = at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 6 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 7 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 6 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸ done

  b4 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ024 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ Toff201 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ [])
  b4 = at 5 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 4 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 6 3 (CCZ014 ∷ []) (sym (wp0685 c4)) ▸
       at 6 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 5 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 11 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 10 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸ done

  b5 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ Toff201 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b5 = at 9 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 8 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 5 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 6 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 2 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸ done

  b6 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ234 ∷ Toff201 ∷ CS01 ∷ CCZ234 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ CCZ123 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b6 = at 1 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 2 2 (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1635 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 3 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4)) ▸
       at 7 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b7 : Chain (Toff304 ∷ CCZ234 ∷ Toff201 ∷ CS01 ∷ CCZ234 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ CCZ123 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b7 = at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl1353 (lit c4))) ▸
       at 4 3 (Toff201 ∷ CCZ123 ∷ []) (wl1636 (lit c4)) ▸
       at 1 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 2 2 (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4) ▸
       at 1 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸ done

  b8 : Chain (CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ Toff201 ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b8 = at 7 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 6 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 3 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 2 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 1 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 2 7 (Toff304 ∷ []) (wp1185 c4) ▸ done

  b9 : Chain (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ024 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ234 ∷ CCZ014 ∷ CCZ024 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b9 = at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 7 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 5 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 4 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b10 : Chain (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ234 ∷ CCZ014 ∷ CCZ024 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ Toff201 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b10 = at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 4 3 (CCZ014 ∷ []) (sym (wp0685 c4)) ▸
       at 4 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸ done

  b11 : Chain (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ Toff201 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3401 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b11 = at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 0 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b12 : Chain (Bx2-3401 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3401 ∷ Bx3-4012 ∷ [])
  b12 = at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done

-- CSdu-box-3 @0310213442: 17 steps
lem-CSdu-box-3-at0310213442 : Ws → ⟪ (CS34⁻ ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CS34⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS34⁻ ∷ Bx3-0142 ∷ []) (CCZ013 ∷ Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ Toff324 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4) ▸
       at 0 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 1 2 (Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ []) (wl1643 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 7 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS34⁻ ∷ [])
  b1 = at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 5 2 (Toff324 ∷ CZ24 ∷ CCZ234 ∷ []) (wl1204 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CS24⁻ ∷ []) (wl1644 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ []) (wl1643 (lit c4)) ▸
       at 4 6 (CS34⁻ ∷ []) (wl1645 (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS34⁻ ∷ []) (Bx3-0142 ∷ CS34⁻ ∷ [])
  b2 = at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-cP-at0310213442 c4)) ▸ done

-- CSu-box-3 @0310213442: 17 steps
lem-CSu-box-3-at0310213442 : Ws → ⟪ (CS34 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CS34 ∷ []) ⟫ʷ
lem-CSu-box-3-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS34 ∷ Bx3-0142 ∷ []) (CCZ013 ∷ Toff324 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ Toff324 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4) ▸
       at 0 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 1 2 (Toff324 ∷ CS34 ∷ CS24 ∷ CCZ234 ∷ []) (wl1652 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 7 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX34 ∷ []) (sym (wp0523 c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff324 ∷ CS34 ∷ CS24 ∷ CS24 ∷ CCZ013 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS34 ∷ [])
  b1 = at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 5 2 (Toff324 ∷ CZ24 ∷ CCZ234 ∷ []) (wl1204 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CS24 ∷ []) (wl1653 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CS34 ∷ CS24 ∷ CCZ234 ∷ []) (wl1652 (lit c4)) ▸
       at 4 6 (CS34 ∷ []) (wl1654 (lit c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS34 ∷ []) (Bx3-0142 ∷ CS34 ∷ [])
  b2 = at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-cP-at0310213442 c4)) ▸ done

-- box2 @0310213442: 11 steps
lem-box2-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0310213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0142 ∷ Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 4 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4) ▸
       at 4 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 5 5 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) (lem-t-cP-at0310213442 c4) ▸
       at 5 4 (Bx3-0142 ∷ []) (sym (lem-box-cP-at0310213442 c4)) ▸
       at 5 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) []
  b1 = at 2 2 [] (wl0443 (lit c4)) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸
       at 0 2 [] (wl0443 (lit c4)) ▸ done

-- box-perm-3124 @0210213443: 2 steps
lem-box-perm-3124-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-3124-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-4013 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ []) (lem-sym-bc-at0210213443 c4) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸ done

-- pairs @04203243: 4 steps
lem-pairs-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-pairs-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-2310 ∷ [])
  b0 = at 0 1 (Toff423 ∷ Bx4-1023 ∷ Toff423 ∷ []) (sym (lem-P-box-at04203243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 [] (wl0457 (lit c4)) ▸
       at 0 4 (Bx4-2310 ∷ []) (sym (lem-box-tQ-at0412233140 c4)) ▸ done

-- sym-bc @0412233140: 2 steps
lem-sym-bc-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-sym-bc-at0412233140 c4 = run b0
  where
  b0 : Chain (Bx4-2310 ∷ []) (Bx4-2130 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx4-2310 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at0412233140 c4)) ▸
       at 0 3 (Bx4-2130 ∷ []) (lem-nat-SWbc-at0412233140 c4) ▸ done

-- box-cP @0410233142: 12 steps
lem-box-cP-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0410233142 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ014 ∷ Toff014 ∷ CZ02 ∷ Toff014 ∷ CCZ014 ∷ CZ02 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp1437 c4) ▸
       at 2 4 (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-QVQ-at0410233142 c4) ▸
       at 1 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0410233142 c4) ▸
       at 2 2 [] (wp0317 c4) ▸ done

-- sym-bc @04122140: 2 steps
lem-sym-bc-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-sym-bc-at04122140 c4 = run b0
  where
  b0 : Chain (Bx4-2130 ∷ []) (Bx4-2310 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx4-2130 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at04122140 c4)) ▸
       at 0 3 (Bx4-2310 ∷ []) (lem-nat-SWbc-at04122140 c4) ▸ done

-- box-cP @0412233140: 12 steps
lem-box-cP-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-box-cP-at0412233140 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ124 ∷ Toff214 ∷ CZ02 ∷ Toff214 ∷ CCZ124 ∷ CZ02 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ [])
  b1 = at 5 6 (CCZ014 ∷ []) (sym (wp1436 c4)) ▸
       at 2 4 (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-QVQ-at0412233140 c4) ▸
       at 1 2 (Toff401 ∷ Toff423 ∷ []) (lem-tP-at0412233140 c4) ▸
       at 2 2 [] (wl0457 (lit c4)) ▸ done

-- CSu-box-3 @04203243: 17 steps
lem-CSu-box-3-at04203243 : Ws → ⟪ (CS24 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS24 ∷ []) ⟫ʷ
lem-CSu-box-3-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24 ∷ Bx4-1023 ∷ []) (CCZ014 ∷ Toff423 ∷ CS24 ∷ CS23 ∷ CS23 ∷ CCZ014 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ Toff423 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 1 2 (Toff423 ∷ CS24 ∷ CS23 ∷ CCZ234 ∷ []) (wl1682 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 7 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff423 ∷ CS24 ∷ CS23 ∷ CS23 ∷ CCZ014 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ Toff423 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS24 ∷ [])
  b1 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 5 2 (Toff423 ∷ CZ23 ∷ CCZ234 ∷ []) (wl1683 (lit c4)) ▸
       at 4 2 (Toff423 ∷ CS23 ∷ []) (wl1684 (lit c4)) ▸
       at 3 2 (Toff423 ∷ CS24 ∷ CS23 ∷ CCZ234 ∷ []) (wl1682 (lit c4)) ▸
       at 4 6 (CS24 ∷ []) (wl1685 (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS24 ∷ []) (Bx4-1023 ∷ CS24 ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done

-- CSdu-box-3 @04203243: 17 steps
lem-CSdu-box-3-at04203243 : Ws → ⟪ (CS24⁻ ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at04203243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS24⁻ ∷ Bx4-1023 ∷ []) (CCZ014 ∷ Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CS23 ∷ CCZ014 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ Toff423 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 1 2 (Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ []) (wl1686 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 7 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX42 ∷ []) (sym (wp0269 c4)) ▸ done

  b1 : Chain (CCZ014 ∷ Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CS23 ∷ CCZ014 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ Toff423 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS24⁻ ∷ [])
  b1 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS24⁻ ∷ []) (sym (wp0722 c4)) ▸
       at 5 2 (Toff423 ∷ CZ23 ∷ CCZ234 ∷ []) (wl1683 (lit c4)) ▸
       at 4 2 (Toff423 ∷ CS23⁻ ∷ []) (wl1687 (lit c4)) ▸
       at 3 2 (Toff423 ∷ CS24⁻ ∷ CS23⁻ ∷ CCZ234 ∷ []) (wl1686 (lit c4)) ▸
       at 4 6 (CS24⁻ ∷ []) (wl1688 (lit c4)) ▸ done

  b2 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS24⁻ ∷ []) (Bx4-1023 ∷ CS24⁻ ∷ [])
  b2 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done

-- box2 @04203243: 11 steps
lem-box2-at04203243 : Ws → ⟪ (Bx4-1023 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at04203243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1023 ∷ Bx4-1023 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ [])
  b0 = at 0 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 0 (Toff401 ∷ Toff401 ∷ []) (sym (wp0306 c4)) ▸
       at 5 5 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff401 ∷ []) (lem-t-cP-at04203243 c4) ▸
       at 5 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 5 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at04203243 c4) ▸
       at 4 2 [] (wp0306 c4) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) []
  b1 = at 2 2 [] (wp0306 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸
       at 0 2 [] (wp0306 c4) ▸ done

-- F4-S0-CS2 @0440: 13 steps
lem-F4-S0-CS2-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS2-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ CS04 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 4 (Bx4-2031 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (lem-XCSX-box-2-at04122041 c4) ▸
       at 1 4 (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1476 c4)) ▸
       at 2 4 (CS12 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1477 c4)) ▸
       at 3 4 (Toff103 ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1476 c4)) ▸
       at 4 4 (CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (sym (wp1478 c4)) ▸ done

  b1 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS04 ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  b1 = at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 1 3 (S4 ∷ CS04⁻ ∷ []) (sym (wp1281 c4)) ▸
       at 1 2 (X0 ∷ CS04 ∷ X0 ∷ []) (wp1281 c4) ▸ done

-- box-cP @0413203241: 12 steps
lem-box-cP-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0413203241 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ CCZ234 ∷ Toff324 ∷ CZ13 ∷ Toff324 ∷ CCZ234 ∷ CZ13 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (sym (wl0756 (lit c4))) ▸
       at 2 4 (Toff412 ∷ Toff403 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-QVQ-at0413203241 c4) ▸
       at 1 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0413203241 c4) ▸
       at 2 2 [] (wp0317 c4) ▸ done

-- box-cP @04122140: 12 steps
lem-box-cP-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at04122140 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ124 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ CCZ234 ∷ Toff234 ∷ CZ02 ∷ Toff234 ∷ CCZ234 ∷ CZ02 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0732 c4)) ▸
       at 2 4 (Toff403 ∷ Toff412 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-QVQ-at04122140 c4) ▸
       at 1 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at04122140 c4) ▸
       at 2 2 [] (wl0470 (lit c4)) ▸ done

-- sym-bc @04133140: 2 steps
lem-sym-bc-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-sym-bc-at04133140 c4 = run b0
  where
  b0 : Chain (Bx4-3210 ∷ []) (Bx4-3120 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx4-3210 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at04133140 c4)) ▸
       at 0 3 (Bx4-3120 ∷ []) (lem-nat-SWbc-at04133140 c4) ▸ done

-- sym-bc @0413213240: 2 steps
lem-sym-bc-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-sym-bc-at0413213240 c4 = run b0
  where
  b0 : Chain (Bx4-3120 ∷ []) (Bx4-3210 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx4-3120 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at0413213240 c4)) ▸
       at 0 3 (Bx4-3210 ∷ []) (lem-nat-SWbc-at0413213240 c4) ▸ done
