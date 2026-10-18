{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D133 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0006 ; wl0166 ; wl0181 ; wl0184 ; wl0207 ; wl0230 ; wl0233 ; wl0242 ; wl0274 ; wl0321 ; wl0341 ; wl0381 ; wl0393 ; wl0415 ; wl0432 ; wl0433 ; wl0448 ; wl0453 ; wl0454 ; wl0455 ; wl0456 ; wl0457 ; wl0458 ; wl0460 ; wl0461 ; wl0463 ; wl0618 ; wl0677 ; wl0836 ; wl0901 ; wl0923 ; wl0928 ; wl0929 ; wl0960 ; wl0961 ; wl1097 ; wl1098 ; wl1220 ; wl1221 ; wl1271 ; wl1273 ; wl1324 ; wl1433 ; wl1441 ; wl1443 ; wl1465 ; wl1466 ; wl1467 ; wl1468 ; wl1469 ; wl1470 ; wl1471 ; wl1472 ; wl1473 ; wl1474 ; wl1475 ; wl1476 ; wl1477 ; wl1478 ; wl1479 ; wl1480 ; wl1481 ; wl1482 ; wl1483 ; wl1484 ; wl1485 ; wl1486 ; wl1487 ; wl1488 ; wl1489 ; wl1490 ; wl1491 ; wl1492 ; wl1493 ; wl1494 ; wl1495 ; wl1496 ; wl1497 ; wl1498 ; wl1499 ; wl1500 ; wl1501 ; wl1502 ; wl1503 ; wl1504 ; wl1505 ; wl1506 ; wl1507 ; wl1508 ; wl1509 ; wl1510 ; wl1511 ; wl1512 ; wl1513 ; wl1514 ; wl1515 ; wp0034 ; wp0035 ; wp0036 ; wp0053 ; wp0054 ; wp0060 ; wp0062 ; wp0063 ; wp0064 ; wp0067 ; wp0081 ; wp0090 ; wp0091 ; wp0092 ; wp0135 ; wp0161 ; wp0167 ; wp0212 ; wp0218 ; wp0261 ; wp0265 ; wp0272 ; wp0279 ; wp0294 ; wp0296 ; wp0303 ; wp0304 ; wp0306 ; wp0359 ; wp0360 ; wp0368 ; wp0450 ; wp0550 ; wp0551 ; wp0553 ; wp0705 ; wp0765 ; wp0778 ; wp0896 ; wp0972 ; wp0973 ; wp1003 ; wp1010 ; wp1011 ; wp1027 ; wp1155 ; wp1156 ; wp1157 ; wp1158 ; wp1180 ; wp1181 ; wp1206 ; wp1284 ; wp1285 ; wp1309 ; wp1310 ; wp1311 ; wp1312 ; wp1313 ; wp1314 ; wp1315 ; wp1316 ; wp1317 ; wp1318 ; wp1319 ; wp1320 ; wp1321 ; wp1322 ; wp1323 ; wp1324 ; wp1325 ; wp1326 ; wp1327 ; wp1328 ; wp1329 ; wp1330 ; wp1331 ; wp1332 ; wp1333 ; wp1334 ; wp1335 ; wp1336 ; wp1337 ; wp1338 ; wp1339 ; wp1340 ; wp1341 ; wp1342 ; wp1343 ; wp1344 ; wp1345 ; wp1346 ; wp1347 ; wp1348 ; wp1349 ; wp1350)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-cP-at0410213243 ; lem-box-cP-at04203243 ; lem-box-tQ-at0410213243 ; lem-sym-ab-at04203243 ; lem-tP-at0410213243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-sym-ab-at0410213243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CX23-CCZ014 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS23-TOFF401 ; lem-comm-CSd23-TOFF401 ; lem-comm-CX02-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CX20-CCZ134 ; lem-comm-CZ02-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ134-CK02 ; lem-comm-CK02-TOFF413 ; lem-comm-CS13-TOFF402 ; lem-comm-CSd02-TOFF413 ; lem-comm-CSd13-TOFF402 ; lem-comm-CX23-TOFF401 ; lem-comm-CZ13-TOFF402 ; lem-comm-CZ23-TOFF401 ; lem-comm-SWAP03-BOX⟨4·21⟩ ; lem-comm-SWAP12-BOX⟨4·03⟩ ; lem-comm-TOFF402-CSd13 ; lem-comm-TOFF413-CSd02)
-- cQ @04122041: 7 steps
lem-cQ-at04122041 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at04122041 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 4 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS04⁻ ∷ []) (sym (wp1206 c4)) ▸
       at 1 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸ done


-- box-tQ @04122041: 13 steps
lem-box-tQ-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at04122041 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 0 2 (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) (wp1309 c4) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at04122041 c4) ▸
       at 2 4 (Toff402 ∷ []) (wp1310 c4) ▸ done


-- CXbc-box @04122041: 17 steps
lem-CXbc-box-at04122041 : Ws → ⟪ (CX03 ∷ Bx4-2031 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx4-2031 ∷ CX03 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CX03 ∷ CCZ014 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CCZ134 ∷ CX20 ∷ CS12 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 0 2 (Toff402 ∷ CX03 ∷ []) (wp1311 c4) ▸
       at 1 2 (CCZ134 ∷ CX03 ∷ CCZ014 ∷ []) (sym (wp1312 c4)) ▸
       at 3 2 (Toff402 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1313 c4) ▸
       at 2 2 (Toff402 ∷ CX03 ∷ []) (wp1311 c4) ▸
       at 5 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ CS12 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CX03 ∷ CCZ014 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CCZ134 ∷ CX20 ∷ CS12 ∷ CX03 ∷ []) (Bx4-2031 ∷ CX03 ∷ CCZ012 ∷ CX03 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS01⁻ ∷ []) (sym (wp1027 c4)) ▸
       at 6 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 3 2 (CCZ134 ∷ CX03 ∷ CCZ014 ∷ []) (sym (wp1312 c4)) ▸
       at 4 3 (CX03 ∷ []) (wp1314 c4) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-tQ-at04122041 c4)) ▸ done

  b2 : Chain (Bx4-2031 ∷ CX03 ∷ CCZ012 ∷ CX03 ∷ []) (Bx4-2031 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wl1465 (lit c4))) ▸ done


-- CXcb-box @04122041: 18 steps
lem-CXcb-box-at04122041 : Ws → ⟪ (CX30 ∷ Bx4-2031 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx4-2031 ∷ CX30 ∷ []) (Toff402 ∷ CCZ134 ∷ CX30 ∷ Toff423 ∷ CS13 ∷ CX23 ∷ Toff402 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ134 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 0 2 (Toff402 ∷ CX30 ∷ Toff423 ∷ []) (wp1315 c4) ▸
       at 2 2 (CCZ134 ∷ Toff423 ∷ CCZ123 ∷ []) (sym (wl1466 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX30 ∷ []) (sym (wp0705 c4)) ▸
       at 4 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 8 2 (Toff402 ∷ CS12 ∷ []) (wp1316 c4) ▸
       at 7 2 (Toff402 ∷ CX23 ∷ []) (wp1317 c4) ▸
       at 6 2 (Toff402 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF402 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CCZ134 ∷ CX30 ∷ Toff423 ∷ CS13 ∷ CX23 ∷ Toff402 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ134 ∷ CX30 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ CX30 ∷ CCZ123 ∷ CX30 ∷ [])
  b1 = at 5 2 (Toff402 ∷ CX23 ∷ []) (wp1317 c4) ▸
       at 4 2 (Toff402 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF402 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 2 2 (Toff402 ∷ CX30 ∷ Toff423 ∷ []) (wp1315 c4) ▸
       at 3 3 (CX30 ∷ []) (wp1319 c4) ▸
       at 4 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ CX30 ∷ []) (sym (wp0705 c4)) ▸ done

  b2 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ CX30 ∷ CCZ123 ∷ CX30 ∷ []) (Bx4-2031 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-tQ-at04122041 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl1467 (lit c4))) ▸ done


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


-- nat-SWbc @04122041: 23 steps
lem-nat-SWbc-at04122041 : Ws → ⟪ (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-nat-SWbc-at04122041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ Sw03 ∷ CCZ234 ∷ Bx4-21 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 1 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 3 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 4 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 5 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸ done

  b1 : Chain (CCZ234 ∷ Toff423 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ Sw03 ∷ CCZ234 ∷ Bx4-21 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ Sw03 ∷ []) (CCZ234 ∷ Toff423 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ Toff423 ∷ CCZ234 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Sw03 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 7 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 8 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 9 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 11 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 12 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff423 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ Toff423 ∷ CCZ234 ∷ CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Sw03 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ Sw03 ∷ []) (Bx4-2301 ∷ [])
  b2 = at 13 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 14 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 15 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx2-401 ∷ []) (refl) ▸
       at 5 6 (Bx2-401 ∷ []) (refl) ▸
       at 0 6 (Bx4-2301 ∷ []) (refl) ▸ done


-- sym-bc @04122041: 2 steps
lem-sym-bc-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-sym-bc-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-2301 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx4-2031 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at04122041 c4)) ▸
       at 0 3 (Bx4-2301 ∷ []) (lem-nat-SWbc-at04122041 c4) ▸ done


-- box-perm-1324 @04122041: 1 steps
lem-box-perm-1324-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-box-perm-1324-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-2301 ∷ [])
  b0 = at 0 1 (Bx4-2301 ∷ []) (lem-sym-bc-at04122041 c4) ▸ done


-- cQ @0412233041: 7 steps
lem-cQ-at0412233041 : Ws → ⟪ (CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0412233041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 1 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 0 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸ done


-- tP @0412233041: 7 steps
lem-tP-at0412233041 : Ws → ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ
lem-tP-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Toff401 ∷ []) (Toff401 ∷ Toff423 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0453 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (sym (wp0303 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233041 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff401 ∷ []) (wp0303 c4) ▸
       at 1 3 (Toff423 ∷ []) (wl0453 (lit c4)) ▸ done


-- VPQ @0412233041: 14 steps
lem-VPQ-at0412233041 : Ws → ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0412233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (CS01⁻ ∷ CS23⁻ ∷ S4 ∷ Toff401 ∷ Toff423 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (sym (wl0455 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (sym (wp0304 c4)) ▸
       at 3 2 (CS01⁻ ∷ S4⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff423 ∷ []) (sym (c₂ (CS • CS • CS) (Toffᵗ))) ▸
       at 1 2 (CS01⁻ ∷ S4 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑ ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS23⁻ ∷ []) (sym (c₂ (CS • CS • CS) (CS • CS • CS))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff401 ∷ Toff423 ∷ []) (lem-tP-at0412233041 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS23⁻ ∷ S4 ∷ Toff401 ∷ Toff423 ∷ S4⁻ ∷ []) (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S)) ▸
       at 2 2 (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff401 ∷ CCZ014 ∷ []) (wp0304 c4) ▸
       at 2 4 (Toff423 ∷ CCZ234 ∷ []) (wl0455 (lit c4)) ▸ done


-- QVQ @0412233041: 3 steps
lem-QVQ-at0412233041 : Ws → ⟪ (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-QVQ-at0412233041 c4 = run b0
  where
  b0 : Chain (CCZ014 ∷ Toff423 ∷ CCZ234 ∷ CCZ014 ∷ []) (Toff401 ∷ Toff423 ∷ CCZ234 ∷ Toff401 ∷ [])
  b0 = at 0 0 (Toff401 ∷ Toff401 ∷ []) (sym (wp0306 c4)) ▸
       at 1 4 (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (sym (lem-VPQ-at0412233041 c4)) ▸
       at 4 2 [] (wp0161 c4) ▸ done


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


-- F4-CS2-K1 @0440: 21 steps
lem-F4-CS2-K1-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K1-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ []) (X0 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K1 ∷ CK01 ∷ S0 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (sym (wl1441 (lit c4))) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K1 ∷ CK01 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1471 (lit c4))) ▸
       at 1 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 1 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 4 4 (K1 ∷ CK01 ∷ S0 ∷ Toff401 ∷ []) (sym (wp1320 c4)) ▸ done

  b1 : Chain (X0 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K1 ∷ CK01 ∷ S0 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx4-2301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K1 ∷ CCZ234 ∷ []) (sym (c₂ (K ↑) (CCZ))) ▸
       at 4 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 5 2 (S0 ∷ CCZ234 ∷ []) (sym (c₁ (S) (CCZ ↑))) ▸
       at 2 4 (K1 ∷ CK01 ∷ S0 ∷ Toff401 ∷ []) (sym (wp1320 c4)) ▸
       at 1 2 (K1 ∷ CCZ234 ∷ []) (sym (c₂ (K ↑) (CCZ))) ▸
       at 2 2 (CK01 ∷ CCZ234 ∷ []) (sym (c₂ (CK₀₁) (CCZ))) ▸
       at 3 2 (S0 ∷ CCZ234 ∷ []) (sym (c₁ (S) (CCZ ↑))) ▸
       at 4 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸ done

  b2 : Chain (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ Bx4-2301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 0 4 (CK01 ∷ X0 ∷ []) (sym (wl1443 (lit c4))) ▸ done


-- tP @04122041: 7 steps
lem-tP-at04122041 : Ws → ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ
lem-tP-at04122041 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Toff413 ∷ []) (Toff413 ∷ Toff402 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (sym (wp1321 c4)) ▸
       at 3 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (sym (wl1472 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at04122041 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff413 ∷ []) (wl1472 (lit c4)) ▸
       at 1 3 (Toff402 ∷ []) (wp1321 c4) ▸ done


-- VPQ @04122041: 14 steps
lem-VPQ-at04122041 : Ws → ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at04122041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (CS13⁻ ∷ CS02⁻ ∷ S4 ∷ Toff413 ∷ Toff402 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S4 ∷ Toff402 ∷ S4⁻ ∷ []) (sym (wp1322 c4)) ▸
       at 4 2 (CS13⁻ ∷ S4 ∷ Toff413 ∷ S4⁻ ∷ []) (sym (wl1473 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS13⁻ ∷ Toff402 ∷ []) (lem-comm-TOFF402-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS13⁻ ∷ CS02⁻ ∷ []) (wl0901 (lit c4)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff413 ∷ Toff402 ∷ []) (lem-tP-at04122041 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS02⁻ ∷ S4 ∷ Toff413 ∷ Toff402 ∷ S4⁻ ∷ []) (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S ↑)) ▸
       at 2 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff413 ∷ CCZ134 ∷ []) (wl1473 (lit c4)) ▸
       at 2 4 (Toff402 ∷ CCZ024 ∷ []) (wp1322 c4) ▸ done


-- QVQ @04122041: 3 steps
lem-QVQ-at04122041 : Ws → ⟪ (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-QVQ-at04122041 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Toff413 ∷ Toff413 ∷ []) (sym (wl1474 (lit c4))) ▸
       at 1 4 (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at04122041 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done


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


-- F4-K2-CS2 @0440: 17 steps
lem-F4-K2-CS2-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-CS2-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (CCZ024 ∷ Toff413 ∷ X0 ∷ CK02 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 4 (CCZ024 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wp1324 c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 2 (Toff413 ∷ CK02 ∷ []) (lem-comm-CK02-TOFF413 (lit c4)) ▸
       at 1 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff413 ∷ X0 ∷ CK02 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b1 = at 2 4 (CCZ024 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wp1324 c4)) ▸
       at 5 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 2 (Toff413 ∷ CK02 ∷ []) (lem-comm-CK02-TOFF413 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 7 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1475 (lit c4))) ▸
       at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b2 = at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done


-- F4-K2-K1 @0440: 1 steps
lem-F4-K2-K1-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1476 (lit c4))) ▸ done


-- CXbc-box @0410213243: 17 steps
lem-CXbc-box-at0410213243 : Ws → ⟪ (CX12 ∷ Bx4-0123 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx4-0123 ∷ CX12 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX12 ∷ CCZ134 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ234 ∷ CX01 ∷ CS03 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4) ▸
       at 0 2 (Toff401 ∷ CX12 ∷ []) (wp0368 c4) ▸
       at 1 2 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (sym (wl1097 (lit c4))) ▸
       at 3 2 (Toff401 ∷ CCZ134 ∷ CCZ013 ∷ []) (wp1325 c4) ▸
       at 2 2 (Toff401 ∷ CX12 ∷ []) (wp0368 c4) ▸
       at 5 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX12 ∷ CCZ134 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ234 ∷ CX01 ∷ CS03 ∷ CX12 ∷ []) (Bx4-0123 ∷ CX12 ∷ CCZ013 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ CCZ134 ∷ []) (wl0960 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (sym (wl1097 (lit c4))) ▸
       at 4 3 (CX12 ∷ []) (wl1098 (lit c4)) ▸
       at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-tQ-at0410213243 c4)) ▸ done

  b2 : Chain (Bx4-0123 ∷ CX12 ∷ CCZ013 ∷ CX12 ∷ []) (Bx4-0123 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wl1477 (lit c4))) ▸ done


-- CXcb-box @0410213243: 18 steps
lem-CXcb-box-at0410213243 : Ws → ⟪ (CX21 ∷ Bx4-0123 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx4-0123 ∷ CX21 ∷ []) (Toff401 ∷ CCZ234 ∷ CX21 ∷ Toff402 ∷ CS23 ∷ CX02 ∷ Toff401 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ234 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4) ▸
       at 0 2 (Toff401 ∷ CX21 ∷ Toff402 ∷ []) (wp1326 c4) ▸
       at 2 2 (CCZ234 ∷ Toff402 ∷ CCZ023 ∷ []) (sym (wp1327 c4)) ▸
       at 1 2 (CCZ234 ∷ CX21 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 4 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 7 2 (Toff401 ∷ CX02 ∷ []) (wp0360 c4) ▸
       at 6 2 (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 (lit c4)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ CX21 ∷ Toff402 ∷ CS23 ∷ CX02 ∷ Toff401 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ234 ∷ CX21 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX21 ∷ CCZ023 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff401 ∷ CX02 ∷ []) (wp0360 c4) ▸
       at 4 2 (Toff401 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF401 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸
       at 3 2 (Toff401 ∷ Toff402 ∷ []) (sym (wp1329 c4)) ▸
       at 2 2 (Toff401 ∷ CX21 ∷ Toff402 ∷ []) (wp1326 c4) ▸
       at 3 3 (CX21 ∷ []) (wp1330 c4) ▸
       at 4 2 (CCZ234 ∷ CCZ023 ∷ []) (wp0550 c4) ▸
       at 3 2 (CCZ234 ∷ CX21 ∷ []) (sym (wl0836 (lit c4))) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX21 ∷ CCZ023 ∷ CX21 ∷ []) (Bx4-0123 ∷ CCZ023 ∷ [])
  b2 = at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-tQ-at0410213243 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (sym (wl1478 (lit c4))) ▸ done


-- SWbc-box @0410213243: 11 steps
lem-SWbc-box-at0410213243 : Ws → ⟪ (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-SWbc-box-at0410213243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (CX12 ∷ Bx4-0123 ∷ CX12 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx4-0123 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0410213243 c4) ▸
       at 3 2 (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4)) ▸
       at 1 3 (Bx4-0123 ∷ CCZ023 ∷ []) (lem-CXcb-box-at0410213243 c4) ▸
       at 4 2 (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4)) ▸
       at 3 2 (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4)) ▸
       at 2 2 (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4)) ▸ done

  b1 : Chain (CX12 ∷ Bx4-0123 ∷ CX12 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ []) (Bx4-0123 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wl1481 (lit c4)) ▸
       at 0 3 (Bx4-0123 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0410213243 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done


-- nat-SWbc @0410213243: 23 steps
lem-nat-SWbc-at0410213243 : Ws → ⟪ (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-nat-SWbc-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ Sw12 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff401 ∷ Bx0-423 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 1 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 3 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 2 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 3 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 4 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4)) ▸
       at 5 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ Sw12 ∷ CCZ024 ∷ Bx4-03 ∷ Toff401 ∷ CCZ014 ∷ Bx0-423 ∷ Sw12 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Sw12 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 7 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4)) ▸
       at 8 2 (Toff402 ∷ Sw12 ∷ []) (wp0973 c4) ▸
       at 9 2 (CCZ024 ∷ Sw12 ∷ []) (sym (wp0551 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff024 ∷ Bx4-03 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ []) (refl) ▸
       at 10 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 11 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 12 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff402 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Sw12 ∷ Toff024 ∷ CCZ024 ∷ Bx4-03 ∷ Sw12 ∷ []) (Bx4-0213 ∷ [])
  b2 = at 13 2 (Toff014 ∷ Sw12 ∷ []) (wp0972 c4) ▸
       at 14 2 (CCZ014 ∷ Sw12 ∷ []) (sym (wp0553 c4)) ▸
       at 15 2 (Bx4-03 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨4·03⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx0-413 ∷ []) (refl) ▸
       at 5 6 (Bx0-413 ∷ []) (refl) ▸
       at 0 6 (Bx4-0213 ∷ []) (refl) ▸ done


-- sym-bc @0410213243: 2 steps
lem-sym-bc-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-sym-bc-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Bx4-0213 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at0410213243 c4)) ▸
       at 0 3 (Bx4-0213 ∷ []) (lem-nat-SWbc-at0410213243 c4) ▸ done


-- cQ @04103143: 7 steps
lem-cQ-at04103143 : Ws → ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 4 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸ done


-- box-tQ @04103143: 13 steps
lem-box-tQ-at04103143 : Ws → ⟪ (Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at04103143 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ CZ03 ∷ Toff014 ∷ CCZ014 ∷ CZ03 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1331 c4) ▸
       at 0 2 (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) (wp1309 c4) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at04103143 c4) ▸
       at 2 4 (Toff402 ∷ []) (wp1310 c4) ▸ done


-- tP @04103143: 7 steps
lem-tP-at04103143 : Ws → ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ
lem-tP-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Toff413 ∷ []) (Toff413 ∷ Toff402 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (sym (wp1321 c4)) ▸
       at 3 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (sym (wl1472 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at04103143 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff413 ∷ []) (wl1472 (lit c4)) ▸
       at 1 3 (Toff402 ∷ []) (wp1321 c4) ▸ done


-- P-box @04103143: 8 steps
lem-P-box-at04103143 : Ws → ⟪ (Toff413 ∷ Bx4-0213 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-P-box-at04103143 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx4-0213 ∷ Toff413 ∷ []) (Bx4-0213 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04103143 c4) ▸
       at 0 2 (Toff402 ∷ Toff413 ∷ []) (sym (lem-tP-at04103143 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ13 ∷ Toff413 ∷ []) (sym (wl1482 (lit c4))) ▸
       at 3 2 (Toff402 ∷ Toff413 ∷ []) (sym (lem-tP-at04103143 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ13 ∷ []) (sym (wl1483 (lit c4))) ▸
       at 2 2 (Toff402 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF402 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1484 (lit c4))) ▸
       at 0 4 (Bx4-0213 ∷ []) (sym (lem-box-tQ-at04103143 c4)) ▸ done


-- VPQ @04103143: 14 steps
lem-VPQ-at04103143 : Ws → ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at04103143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (CS13⁻ ∷ CS02⁻ ∷ S4 ∷ Toff413 ∷ Toff402 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S4 ∷ Toff402 ∷ S4⁻ ∷ []) (sym (wp1322 c4)) ▸
       at 4 2 (CS13⁻ ∷ S4 ∷ Toff413 ∷ S4⁻ ∷ []) (sym (wl1473 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS13⁻ ∷ Toff402 ∷ []) (lem-comm-TOFF402-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS13⁻ ∷ CS02⁻ ∷ []) (wl0901 (lit c4)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff413 ∷ Toff402 ∷ []) (lem-tP-at04103143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS02⁻ ∷ S4 ∷ Toff413 ∷ Toff402 ∷ S4⁻ ∷ []) (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S ↑)) ▸
       at 2 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff413 ∷ CCZ134 ∷ []) (wl1473 (lit c4)) ▸
       at 2 4 (Toff402 ∷ CCZ024 ∷ []) (wp1322 c4) ▸ done


-- QVQ @04103143: 3 steps
lem-QVQ-at04103143 : Ws → ⟪ (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-QVQ-at04103143 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ134 ∷ []) (Toff413 ∷ Toff402 ∷ CCZ024 ∷ Toff413 ∷ [])
  b0 = at 0 0 (Toff413 ∷ Toff413 ∷ []) (sym (wl1474 (lit c4))) ▸
       at 1 4 (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at04103143 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done


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


-- cQ @04233042: 7 steps
lem-cQ-at04233042 : Ws → ⟪ (CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ134 ∷ []) ⟫ʷ
lem-cQ-at04233042 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 1 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸ done


-- box-tQ @04233042: 13 steps
lem-box-tQ-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at04233042 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 0 2 (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1485 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at04233042 c4) ▸
       at 2 4 (Toff413 ∷ []) (wl1486 (lit c4)) ▸ done


-- pairs @04103143: 4 steps
lem-pairs-at04103143 : Ws → ⟪ (Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-pairs-at04103143 c4 = run b0
  where
  b0 : Chain (Bx4-0213 ∷ []) (Bx4-1302 ∷ [])
  b0 = at 0 1 (Toff413 ∷ Bx4-0213 ∷ Toff413 ∷ []) (sym (lem-P-box-at04103143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04103143 c4) ▸
       at 4 2 [] (wl1474 (lit c4)) ▸
       at 0 4 (Bx4-1302 ∷ []) (sym (lem-box-tQ-at04233042 c4)) ▸ done


-- box-perm-1423 @04203243: 3 steps
lem-box-perm-1423-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-box-perm-1423-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-1302 ∷ [])
  b0 = at 0 1 (Bx4-0123 ∷ []) (lem-sym-ab-at04203243 c4) ▸
       at 0 1 (Bx4-0213 ∷ []) (lem-sym-bc-at0410213243 c4) ▸
       at 0 1 (Bx4-1302 ∷ []) (lem-pairs-at04103143 c4) ▸ done


-- tP @04233042: 7 steps
lem-tP-at04233042 : Ws → ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ
lem-tP-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Toff402 ∷ []) (Toff402 ∷ Toff413 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (sym (wl1472 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (sym (wp1321 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at04233042 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff402 ∷ []) (wp1321 c4) ▸
       at 1 3 (Toff413 ∷ []) (wl1472 (lit c4)) ▸ done


-- VPQ @04233042: 14 steps
lem-VPQ-at04233042 : Ws → ⟪ (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at04233042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (CS02⁻ ∷ CS13⁻ ∷ S4 ∷ Toff402 ∷ Toff413 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S4 ∷ Toff413 ∷ S4⁻ ∷ []) (sym (wl1473 (lit c4))) ▸
       at 4 2 (CS02⁻ ∷ S4 ∷ Toff402 ∷ S4⁻ ∷ []) (sym (wp1322 c4)) ▸
       at 3 2 (CS02⁻ ∷ S4⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) ((S • S • S) ↑))) ▸
       at 2 2 (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ S4 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S ↑))) ▸
       at 0 2 (CS02⁻ ∷ CS13⁻ ∷ []) (sym (wl0901 (lit c4))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff402 ∷ Toff413 ∷ []) (lem-tP-at04233042 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS13⁻ ∷ S4 ∷ Toff402 ∷ Toff413 ∷ S4⁻ ∷ []) (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS13⁻ ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S)) ▸
       at 2 2 (Toff402 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF402 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS13⁻ ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff402 ∷ CCZ024 ∷ []) (wp1322 c4) ▸
       at 2 4 (Toff413 ∷ CCZ134 ∷ []) (wl1473 (lit c4)) ▸ done


-- QVQ @04233042: 3 steps
lem-QVQ-at04233042 : Ws → ⟪ (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-QVQ-at04233042 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff402 ∷ Toff413 ∷ CCZ134 ∷ Toff402 ∷ [])
  b0 = at 0 0 (Toff402 ∷ Toff402 ∷ []) (sym (wp1323 c4)) ▸
       at 1 4 (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at04233042 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


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


-- F4-CS1-K2 @0440: 21 steps
lem-F4-CS1-K2-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-K2-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ []) (X0 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ K2 ∷ CK02 ∷ S0 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K2 ∷ CK02 ∷ S0 ∷ X0 ∷ []) (sym (wl1487 (lit c4))) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 2 7 (K2 ∷ CK02 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1488 (lit c4))) ▸
       at 1 1 (Bx4-1302 ∷ []) (lem-box-perm-1423-at04203243 c4) ▸
       at 1 1 (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at04233042 c4) ▸
       at 4 4 (K2 ∷ CK02 ∷ S0 ∷ Toff402 ∷ []) (sym (wp1332 c4)) ▸ done

  b1 : Chain (X0 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ K2 ∷ CK02 ∷ S0 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ Bx4-1302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K2 ∷ CCZ134 ∷ []) (wl1489 (lit c4)) ▸
       at 4 2 (CK02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CK02 (lit c4)) ▸
       at 5 2 (S0 ∷ CCZ134 ∷ []) (sym (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 2 4 (K2 ∷ CK02 ∷ S0 ∷ Toff402 ∷ []) (sym (wp1332 c4)) ▸
       at 1 2 (K2 ∷ CCZ134 ∷ []) (wl1489 (lit c4)) ▸
       at 2 2 (CK02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CK02 (lit c4)) ▸
       at 3 2 (S0 ∷ CCZ134 ∷ []) (sym (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 4 4 (Bx4-1302 ∷ []) (sym (lem-box-cP-at04233042 c4)) ▸ done

  b2 : Chain (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ Bx4-1302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1423-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 0 4 (CK02 ∷ X0 ∷ []) (sym (wl1490 (lit c4))) ▸ done


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


-- pairs @0410213243: 4 steps
lem-pairs-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-pairs-at0410213243 c4 = run b0
  where
  b0 : Chain (Bx4-0123 ∷ []) (Bx4-2301 ∷ [])
  b0 = at 0 1 (Toff423 ∷ Bx4-0123 ∷ Toff423 ∷ []) (sym (lem-P-box-at0410213243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at0410213243 c4) ▸
       at 4 2 [] (wl0457 (lit c4)) ▸
       at 0 4 (Bx4-2301 ∷ []) (sym (lem-box-tQ-at0412233041 c4)) ▸ done


-- CXbc-box @0412233041: 17 steps
lem-CXbc-box-at0412233041 : Ws → ⟪ (CX30 ∷ Bx4-2301 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at0412233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx4-2301 ∷ CX30 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CX30 ∷ CCZ134 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CCZ014 ∷ CX23 ∷ CS12 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at0412233041 c4) ▸
       at 0 2 (Toff423 ∷ CX30 ∷ []) (wp1333 c4) ▸
       at 1 2 (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (sym (wp1010 c4)) ▸
       at 3 2 (Toff423 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl1496 (lit c4)) ▸
       at 2 2 (Toff423 ∷ CX30 ∷ []) (wp1333 c4) ▸
       at 5 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CX30 ∷ CCZ134 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CCZ014 ∷ CX23 ∷ CS12 ∷ CX30 ∷ []) (Bx4-2301 ∷ CX30 ∷ CCZ123 ∷ CX30 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 3 2 (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (sym (wp1010 c4)) ▸
       at 4 3 (CX30 ∷ []) (wp1011 c4) ▸
       at 0 4 (Bx4-2301 ∷ []) (sym (lem-box-tQ-at0412233041 c4)) ▸ done

  b2 : Chain (Bx4-2301 ∷ CX30 ∷ CCZ123 ∷ CX30 ∷ []) (Bx4-2301 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl1467 (lit c4))) ▸ done


-- CXcb-box @0412233041: 18 steps
lem-CXcb-box-at0412233041 : Ws → ⟪ (CX03 ∷ Bx4-2301 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0412233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx4-2301 ∷ CX03 ∷ []) (Toff423 ∷ CCZ014 ∷ CX03 ∷ Toff402 ∷ CS01 ∷ CX20 ∷ Toff423 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ CCZ014 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at0412233041 c4) ▸
       at 0 2 (Toff423 ∷ CX03 ∷ Toff402 ∷ []) (wp1334 c4) ▸
       at 2 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸
       at 1 2 (CCZ014 ∷ CX03 ∷ []) (sym (wp0778 c4)) ▸
       at 4 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 8 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 7 2 (Toff423 ∷ CX20 ∷ []) (wp1336 c4) ▸
       at 6 2 (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ)) ▸ done

  b1 : Chain (Toff423 ∷ CCZ014 ∷ CX03 ∷ Toff402 ∷ CS01 ∷ CX20 ∷ Toff423 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ CCZ014 ∷ CX03 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX03 ∷ CCZ012 ∷ CX03 ∷ [])
  b1 = at 5 2 (Toff423 ∷ CX20 ∷ []) (wp1336 c4) ▸
       at 4 2 (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 3 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸
       at 2 2 (Toff423 ∷ CX03 ∷ Toff402 ∷ []) (wp1334 c4) ▸
       at 3 3 (CX03 ∷ []) (wp1337 c4) ▸
       at 4 2 (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4) ▸
       at 3 2 (CCZ014 ∷ CX03 ∷ []) (sym (wp0778 c4)) ▸ done

  b2 : Chain (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX03 ∷ CCZ012 ∷ CX03 ∷ []) (Bx4-2301 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx4-2301 ∷ []) (sym (lem-box-tQ-at0412233041 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1465 (lit c4))) ▸ done


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


-- nat-SWbc @0412233041: 23 steps
lem-nat-SWbc-at0412233041 : Ws → ⟪ (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-nat-SWbc-at0412233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ Sw03 ∷ CCZ024 ∷ Bx4-21 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff423 ∷ Bx2-401 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 1 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 3 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 3 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 4 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 5 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ Sw03 ∷ CCZ024 ∷ Bx4-21 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ Sw03 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Sw03 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 7 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 8 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 9 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 11 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 12 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff402 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Sw03 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ Sw03 ∷ []) (Bx4-2031 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 14 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 15 2 (Bx4-21 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨4·21⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx2-431 ∷ []) (refl) ▸
       at 5 6 (Bx2-431 ∷ []) (refl) ▸
       at 0 6 (Bx4-2031 ∷ []) (refl) ▸ done


-- sym-bc @0412233041: 2 steps
lem-sym-bc-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-sym-bc-at0412233041 c4 = run b0
  where
  b0 : Chain (Bx4-2301 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx4-2301 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at0412233041 c4)) ▸
       at 0 3 (Bx4-2031 ∷ []) (lem-nat-SWbc-at0412233041 c4) ▸ done


-- box-perm-3241 @04203243: 3 steps
lem-box-perm-3241-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-box-perm-3241-at04203243 c4 = run b0
  where
  b0 : Chain (Bx4-1023 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 0 1 (Bx4-0123 ∷ []) (lem-sym-ab-at04203243 c4) ▸
       at 0 1 (Bx4-2301 ∷ []) (lem-pairs-at0410213243 c4) ▸
       at 0 1 (Bx4-2031 ∷ []) (lem-sym-bc-at0412233041 c4) ▸ done


-- P-box @0412233041: 8 steps
lem-P-box-at0412233041 : Ws → ⟪ (Toff401 ∷ Bx4-2301 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-P-box-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff401 ∷ Bx4-2301 ∷ Toff401 ∷ []) (Bx4-2301 ∷ [])
  b0 = at 1 1 (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at0412233041 c4) ▸
       at 0 2 (Toff423 ∷ Toff401 ∷ []) (sym (lem-tP-at0412233041 c4)) ▸
       at 1 2 (CCZ014 ∷ CZ01 ∷ Toff401 ∷ []) (sym (wp1338 c4)) ▸
       at 3 2 (Toff423 ∷ Toff401 ∷ []) (sym (lem-tP-at0412233041 c4)) ▸
       at 4 3 (CCZ014 ∷ CZ01 ∷ []) (sym (wp1339 c4)) ▸
       at 2 2 (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ)) ▸
       at 3 3 (CCZ014 ∷ []) (sym (wp1340 c4)) ▸
       at 0 4 (Bx4-2301 ∷ []) (sym (lem-box-tQ-at0412233041 c4)) ▸ done


-- pairs @0412233041: 4 steps
lem-pairs-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-pairs-at0412233041 c4 = run b0
  where
  b0 : Chain (Bx4-2301 ∷ []) (Bx4-0123 ∷ [])
  b0 = at 0 1 (Toff401 ∷ Bx4-2301 ∷ Toff401 ∷ []) (sym (lem-P-box-at0412233041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 4 2 [] (wp0306 c4) ▸
       at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-tQ-at0410213243 c4)) ▸ done


-- box-perm-4213 @04122041: 3 steps
lem-box-perm-4213-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-4213-at04122041 c4 = run b0
  where
  b0 : Chain (Bx4-2031 ∷ []) (Bx4-1023 ∷ [])
  b0 = at 0 1 (Bx4-2301 ∷ []) (lem-sym-bc-at04122041 c4) ▸
       at 0 1 (Bx4-0123 ∷ []) (lem-pairs-at0412233041 c4) ▸
       at 0 1 (Bx4-1023 ∷ []) (lem-sym-ab-at0410213243 c4) ▸ done


-- F4-CS1-CS2 @0440: 248 steps
lem-F4-CS1-CS2-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS2-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (run b30))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CCZ024 ∷ CS13⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 5 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 5 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b3 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CCZ024 ∷ CS13⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 6 2 (Toff413 ∷ CS13⁻ ∷ []) (wl1500 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS13⁻ ∷ []) (wl1500 (lit c4)) ▸
       at 5 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 5 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 5 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 4 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 6 2 (Toff401 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp1341 c4) ▸ done

  b4 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 5 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 11 2 (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4) ▸
       at 10 2 (Toff401 ∷ CS02 ∷ []) (wp1343 c4) ▸
       at 9 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4) ▸
       at 7 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 6 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 5 2 (Toff401 ∷ K3 ∷ []) (wp1345 c4) ▸ done

  b5 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ Toff302 ∷ CCZ024 ∷ CCZ234 ∷ CCZ012 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 6 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 8 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 12 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 11 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 10 2 (CCZ234 ∷ CS02⁻ ∷ []) (sym (wp0765 c4)) ▸
       at 9 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 8 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 9 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

  b6 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ Toff302 ∷ CCZ024 ∷ CCZ234 ∷ CCZ012 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 7 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 7 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 8 2 (Toff401 ∷ CCZ012 ∷ []) (wp0359 c4) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 13 2 (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4) ▸
       at 12 2 (Toff401 ∷ CS02 ∷ []) (wp1343 c4) ▸
       at 11 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸ done

  b7 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Bx4-2031 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b7 = at 10 2 (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4) ▸
       at 9 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 7 2 (Toff401 ∷ K3 ∷ []) (wp1345 c4) ▸
       at 8 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 4 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 4 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸ done

  b8 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Bx4-2031 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b8 = at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CS13 ∷ []) (wl1502 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CS13 ∷ []) (wl1502 (lit c4)) ▸
       at 3 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 3 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸ done

  b9 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b9 = at 2 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 4 2 (Toff401 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp1341 c4) ▸
       at 3 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 9 2 (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4) ▸
       at 8 2 (Toff401 ∷ CS02 ∷ []) (wp1343 c4) ▸
       at 7 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 6 2 (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4) ▸
       at 5 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ Toff401 ∷ Toff302 ∷ CCZ024 ∷ CS02 ∷ CCZ234 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b10 = at 4 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 3 2 (Toff401 ∷ K3 ∷ []) (wp1345 c4) ▸
       at 4 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 6 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 10 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 8 2 (CCZ234 ∷ CS02⁻ ∷ []) (sym (wp0765 c4)) ▸
       at 7 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b11 : Chain (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ Toff401 ∷ Toff302 ∷ CCZ024 ∷ CS02 ∷ CCZ234 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b11 = at 6 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 4 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 5 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 6 2 (Toff401 ∷ CCZ012 ∷ []) (wp0359 c4) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 11 2 (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4) ▸ done

  b12 : Chain (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b12 = at 10 2 (Toff401 ∷ CS02 ∷ []) (wp1343 c4) ▸
       at 9 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4) ▸
       at 7 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 6 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 5 2 (Toff401 ∷ K3 ∷ []) (wp1345 c4) ▸
       at 6 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 2 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸ done

  b13 : Chain (X0 ∷ Bx4-1023 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b13 = at 2 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 1 1 (Bx4-2031 ∷ []) (lem-box-perm-3241-at04203243 c4) ▸
       at 2 1 (Bx4-1023 ∷ []) (lem-box-perm-4213-at04122041 c4) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 2 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 1 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b14 = at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b15 : Chain (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b15 = at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b16 : Chain (Bx4-2031 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b16 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b17 : Chain (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b17 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 8 (Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) (wl1503 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b18 : Chain (Bx4-2031 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b18 = at 4 3 (CS13 ∷ Toff302 ∷ CCZ012 ∷ []) (wl1504 (lit c4)) ▸
       at 6 2 [] (wl0341 (lit c4)) ▸
       at 4 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸
       at 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b19 : Chain (Bx4-2031 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b19 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff103 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1506 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 5 2 (CX31 ∷ Toff423 ∷ []) (sym (wl1507 (lit c4))) ▸
       at 7 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸
       at 6 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 7 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸
       at 8 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸ done

  b20 : Chain (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff423 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b20 = at 9 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 10 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 11 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ Toff423 ∷ []) (sym (c₂ ((K • iI) ↑) (Toffᵗ))) ▸
       at 6 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸
       at 4 3 (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp1349 c4) ▸
       at 3 2 (CX31 ∷ Toff423 ∷ []) (sym (wl1507 (lit c4))) ▸
       at 5 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸ done

  b21 : Chain (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff423 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff103 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b21 = at 4 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 5 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸
       at 6 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 7 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 8 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 9 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 10 2 (K1⁻ ∷ Toff423 ∷ []) (sym (c₂ ((K • iI) ↑) (Toffᵗ))) ▸
       at 4 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸ done

  b22 : Chain (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff103 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b22 = at 2 3 (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp1349 c4) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 4 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸
       at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b23 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b23 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS12 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1512 (lit c4))) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 6 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 4 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸ done

  b24 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ [])
  b24 = at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸
       at 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b25 = at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX31 ∷ Toff103 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1506 (lit c4))) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 7 2 (CX31 ∷ Toff423 ∷ []) (sym (wl1507 (lit c4))) ▸
       at 9 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸
       at 8 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 9 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸
       at 10 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸ done

  b26 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff423 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b26 = at 11 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 12 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 13 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 14 2 (K1⁻ ∷ Toff423 ∷ []) (sym (c₂ ((K • iI) ↑) (Toffᵗ))) ▸
       at 8 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸
       at 6 3 (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp1349 c4) ▸
       at 5 2 (CX31 ∷ Toff423 ∷ []) (sym (wl1507 (lit c4))) ▸
       at 7 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸ done

  b27 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff423 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff103 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b27 = at 6 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 7 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸
       at 8 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 9 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 10 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 11 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ Toff423 ∷ []) (sym (c₂ ((K • iI) ↑) (Toffᵗ))) ▸
       at 6 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸ done

  b28 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff103 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS12⁻ ∷ X0 ∷ [])
  b28 = at 4 3 (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp1349 c4) ▸
       at 6 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b29 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS12⁻ ∷ X0 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b29 = at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 5 (CS12⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1514 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff423 ∷ []) (sym (wl0460 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff423 ∷ []) (sym (wl0460 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸ done

  b30 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b30 = at 6 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done


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

