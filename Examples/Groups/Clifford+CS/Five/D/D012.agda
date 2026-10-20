{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D012 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0179 ; wl0230 ; wl0297 ; wl0321 ; wl0327 ; wl0330 ; wl0341 ; wl0421 ; wl0423 ; wl0441 ; wl0442 ; wl0482 ; wl0618 ; wl0702 ; wl0707 ; wl0763 ; wl0765 ; wl0770 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0808 ; wl0831 ; wl0866 ; wl0867 ; wl0868 ; wl0912 ; wl0913 ; wl0914 ; wl0917 ; wl0920 ; wl0923 ; wl1273 ; wl1321 ; wl1323 ; wl1324 ; wl1325 ; wl1326 ; wl1327 ; wl1336 ; wl1337 ; wl1338 ; wl1339 ; wp0022 ; wp0034 ; wp0036 ; wp0081 ; wp0087 ; wp0092 ; wp0109 ; wp0161 ; wp0167 ; wp0189 ; wp0272 ; wp0378 ; wp0380 ; wp0499 ; wp0505 ; wp0566 ; wp0567 ; wp0703 ; wp0705 ; wp0746 ; wp0759 ; wp0762 ; wp0763 ; wp0764 ; wp0769 ; wp0778 ; wp0827 ; wp0945 ; wp1037 ; wp1055 ; wp1059 ; wp1143 ; wp1144 ; wp1151 ; wp1152 ; wp1153 ; wp1154 ; wp1159 ; wp1160 ; wp1161 ; wp1190 ; wp1191 ; wp1192 ; wp1193 ; wl0176 ; wl0177 ; wl0178 ; wl0271 ; wl0305 ; wl0332 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0471 ; wl0504 ; wl0505 ; wl0506 ; wl0534 ; wl0537 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0639 ; wl0757 ; wl0879 ; wl1222 ; wl1343 ; wl1348 ; wl1349 ; wl1350 ; wl1351 ; wl1352 ; wl1356 ; wl1357 ; wl1358 ; wl1359 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0066 ; wp0103 ; wp0106 ; wp0108 ; wp0123 ; wp0221 ; wp0225 ; wp0226 ; wp0301 ; wp0318 ; wp0384 ; wp0450 ; wp0514 ; wp0515 ; wp0550 ; wp0663 ; wp0670 ; wp0672 ; wp0679 ; wp0712 ; wp0780 ; wp0781 ; wp0782 ; wp1196 ; wp1197 ; wp1198 ; wp1199 ; wp1202 ; wl0488 ; wl1220 ; wl1233 ; wl1304 ; wl1367 ; wl1368 ; wl1369 ; wp0027 ; wp0028 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0513 ; wp1003 ; wp1006 ; wp1033 ; wp1034 ; wp1204 ; wp1205 ; wp1206 ; wp1207 ; wl0272 ; wl0277 ; wl0278 ; wl0280 ; wl0334 ; wl0527 ; wl0620 ; wl0621 ; wl0774 ; wl1235 ; wl1236 ; wl1253 ; wl1254 ; wl1255 ; wl1391 ; wl1393 ; wl1394 ; wp0003 ; wp0203 ; wp0231 ; wp0795 ; wp0817 ; wp0960 ; wp0963 ; wp1216 ; wp1217 ; wp1226 ; wp1228 ; wp1229 ; wp1230 ; wp1231 ; wp1233 ; wp1234 ; wp1235 ; wp1236 ; wl0159 ; wl0201 ; wl0202 ; wl0448 ; wl0825 ; wl0826 ; wl0827 ; wl0882 ; wl1398 ; wl1399 ; wl1400 ; wl1401 ; wl1402 ; wl1403 ; wp0050 ; wp0053 ; wp0058 ; wp0059 ; wp0593 ; wp1249 ; wp1250 ; wp1251 ; wl0233 ; wl0393 ; wl0455 ; wl0456 ; wl0461 ; wl0677 ; wl0901 ; wl1465 ; wl1466 ; wl1467 ; wl1473 ; wl1479 ; wl1480 ; wl1481 ; wl1482 ; wl1483 ; wl1484 ; wl1496 ; wp0060 ; wp0067 ; wp0261 ; wp0304 ; wp1010 ; wp1011 ; wp1027 ; wp1311 ; wp1312 ; wp1313 ; wp1314 ; wp1315 ; wp1316 ; wp1317 ; wp1318 ; wp1319 ; wp1322 ; wp1333 ; wp1334 ; wp1335 ; wp1336 ; wp1337 ; wp1338 ; wp1339 ; wp1340 ; wl0155 ; wl0289 ; wl0391 ; wl0392 ; wl0468 ; wl0469 ; wl0905 ; wl1021 ; wl1546 ; wl1562 ; wl1563 ; wl1564 ; wl1565 ; wl1569 ; wl1570 ; wl1571 ; wl1586 ; wl1587 ; wl1588 ; wl1589 ; wl1590 ; wp0021 ; wp0032 ; wp0039 ; wp0082 ; wp0142 ; wp0316 ; wp0717 ; wp0718 ; wp1374 ; wp1377 ; wp1385 ; wp1386 ; wp1387 ; wp1388 ; wp1389 ; wp1390 ; wp1396 ; wp1397 ; wp1398 ; wl1597 ; wl1598 ; wl1599 ; wl1603 ; wl1609 ; wl1610 ; wl1611 ; wl1612 ; wp0001 ; wp0002 ; wp0101 ; wp0104 ; wp0110 ; wp0186 ; wp0375 ; wp0669 ; wp1399 ; wp1400 ; wp1401 ; wp1402 ; wp1403 ; wp1404 ; wp1405 ; wp1406 ; wp1407 ; wp1408 ; wp1409 ; wp1410 ; wp1413 ; wp1414 ; wp1415)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at033440 ; lem-box-tQ-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CXbc-box-at021021 ; lem-CXbc-box-at0210213443 ; lem-CXbc-box-at0214233041 ; lem-CXbc-box-at0410213243 ; lem-CXcb-box-at021021 ; lem-CXcb-box-at0210213443 ; lem-CXcb-box-at0214233041 ; lem-CXcb-box-at0410213243 ; lem-VPQ-at0213243041 ; lem-VPQ-at0214233041 ; lem-VPQ-at0310213442 ; lem-box-tQ-at02102331 ; lem-box-tQ-at02102441 ; lem-box-tQ-at02132031 ; lem-box-tQ-at02132130 ; lem-box-tQ-at02142041 ; lem-box-tQ-at0310243241 ; lem-box-tQ-at031031 ; lem-box-tQ-at03122031 ; lem-box-tQ-at03122130 ; lem-box-tQ-at0312243041 ; lem-box-tQ-at0314203241 ; lem-box-tQ-at03143041 ; lem-box-tQ-at03243042 ; lem-box-tQ-at04103143 ; lem-box-tQ-at04122041 ; lem-box-tQ-at142142 ; lem-tP-at02102331 ; lem-tP-at02102441 ; lem-tP-at02132031 ; lem-tP-at02132130 ; lem-tP-at0214203143 ; lem-tP-at02142041 ; lem-tP-at0310243241 ; lem-tP-at031031 ; lem-tP-at03122031 ; lem-tP-at03122130 ; lem-tP-at0312243041 ; lem-tP-at0314203241 ; lem-tP-at03143041 ; lem-tP-at03243042 ; lem-tP-at033440 ; lem-tP-at04103143 ; lem-tP-at04122041 ; lem-tP-at0412233041 ; lem-tP-at04233042 ; lem-tP-at142142 ; lem-tP-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-tQ-at0410233241 ; lem-box-tQ-at041041 ; lem-box-tQ-at0412233041 ; lem-box-tQ-at0413203142 ; lem-box-tQ-at0413213042 ; lem-box-tQ-at04233240 ; lem-box-tQ-at0440 ; lem-tP-at02142140 ; lem-tP-at0410233241 ; lem-tP-at0412213043 ; lem-tP-at0413203142 ; lem-tP-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-TOFF412 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-TOFF403 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-TOFF014 ; lem-comm-CX02-CCZ134 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX31-CCZ024 ; lem-comm-CZ03-TOFF412 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ04-TOFF312 ; lem-comm-CZ14-TOFF023 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF204-CSd13 ; lem-comm-TOFF312-CSd04 ; lem-comm-TOFF412-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS04-TOFF213 ; lem-comm-CS04-TOFF312 ; lem-comm-CS12-TOFF304 ; lem-comm-CS13-TOFF204 ; lem-comm-CS14-TOFF203 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CSd14-TOFF302 ; lem-comm-CSd23-TOFF401 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX03-CCZ124 ; lem-comm-CX30-CCZ124 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ02-TOFF314 ; lem-comm-CZ12-TOFF304 ; lem-comm-CZ12-TOFF403 ; lem-comm-CZ13-TOFF204 ; lem-comm-CZ14-TOFF302 ; lem-comm-CZ23-TOFF014 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF214-CSd03 ; lem-comm-TOFF304-CSd12 ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CK40-TOFF312 ; lem-comm-CS13-TOFF402 ; lem-comm-CS14-TOFF302 ; lem-comm-CSd02-TOFF413 ; lem-comm-CSd13-TOFF402 ; lem-comm-CX20-CCZ134 ; lem-comm-CZ13-TOFF402 ; lem-comm-TOFF402-CSd13 ; lem-comm-TOFF413-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS02-TOFF413 ; lem-comm-CS12-TOFF403 ; lem-comm-TOFF403-CSd12)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF203-CSd14 ; lem-comm-TOFF302-CSd14)

-- CXcb-box @02142041: 18 steps
lem-CXcb-box-at02142041 : Ws → ⟪ (CX30 ∷ Bx2-4031 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at02142041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-4031 ∷ CX30 ∷ []) (Toff204 ∷ CCZ123 ∷ CX30 ∷ Toff234 ∷ CS13 ∷ CX43 ∷ Toff204 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ CCZ123 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 0 2 (Toff204 ∷ CX30 ∷ Toff234 ∷ []) (wp1151 c4) ▸
       at 2 2 (CCZ123 ∷ Toff234 ∷ CCZ134 ∷ []) (sym (wl1323 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 8 2 (Toff204 ∷ CS14 ∷ []) (wp1152 c4) ▸
       at 7 2 (Toff204 ∷ CX43 ∷ []) (wp0945 c4) ▸
       at 6 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ CX30 ∷ Toff234 ∷ CS13 ∷ CX43 ∷ Toff204 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ CCZ123 ∷ CX30 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 5 2 (Toff204 ∷ CX43 ∷ []) (wp0945 c4) ▸
       at 4 2 (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff234 ∷ []) (sym (wp1153 c4)) ▸
       at 2 2 (Toff204 ∷ CX30 ∷ Toff234 ∷ []) (wp1151 c4) ▸
       at 3 3 (CX30 ∷ []) (wp1154 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ134 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX30 ∷ []) (sym (wl1324 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-4031 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-4031 ∷ []) (sym (lem-box-tQ-at02142041 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wp0759 c4)) ▸ done

-- QVQ @0214233041: 3 steps
lem-QVQ-at0214233041 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0214233041 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Toff201 ∷ Toff201 ∷ []) (sym (wl0421 (lit c4))) ▸
       at 1 4 (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at0214233041 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done

-- CXbc-box @0314203241: 17 steps
lem-CXbc-box-at0314203241 : Ws → ⟪ (CX02 ∷ Bx3-4021 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0314203241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx3-4021 ∷ CX02 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX02 ∷ CCZ013 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 0 2 (Toff304 ∷ CX02 ∷ []) (wp1059 c4) ▸
       at 1 2 (CCZ123 ∷ CX02 ∷ CCZ013 ∷ []) (sym (wl1325 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp1159 c4) ▸
       at 2 2 (Toff304 ∷ CX02 ∷ []) (wp1059 c4) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX02 ∷ CCZ013 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CX02 ∷ []) (Bx3-4021 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ013 ∷ []) (wl0327 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX02 ∷ CCZ013 ∷ []) (sym (wl1325 (lit c4))) ▸
       at 4 3 (CX02 ∷ []) (wl1326 (lit c4)) ▸
       at 0 4 (Bx3-4021 ∷ []) (sym (lem-box-tQ-at0314203241 c4)) ▸ done

  b2 : Chain (Bx3-4021 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ []) (Bx3-4021 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0378 c4)) ▸ done

-- CXcb-box @0314203241: 18 steps
lem-CXcb-box-at0314203241 : Ws → ⟪ (CX20 ∷ Bx3-4021 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at0314203241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx3-4021 ∷ CX20 ∷ []) (Toff304 ∷ CCZ123 ∷ CX20 ∷ Toff324 ∷ CS12 ∷ CX42 ∷ Toff304 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ CCZ123 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 0 2 (Toff304 ∷ CX20 ∷ Toff324 ∷ []) (wp1160 c4) ▸
       at 2 2 (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1327 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4)) ▸
       at 8 2 (Toff304 ∷ CS14 ∷ []) (wp1037 c4) ▸
       at 7 2 (Toff304 ∷ CX42 ∷ []) (wp1055 c4) ▸
       at 6 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ CX20 ∷ Toff324 ∷ CS12 ∷ CX42 ∷ Toff304 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ CCZ123 ∷ CX20 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ [])
  b1 = at 5 2 (Toff304 ∷ CX42 ∷ []) (wp1055 c4) ▸
       at 4 2 (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0702 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff324 ∷ []) (sym (wp1144 c4)) ▸
       at 2 2 (Toff304 ∷ CX20 ∷ Toff324 ∷ []) (wp1160 c4) ▸
       at 3 3 (CX20 ∷ []) (wp1161 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ124 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX20 ∷ []) (sym (wl0482 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ []) (Bx3-4021 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-4021 ∷ []) (sym (lem-box-tQ-at0314203241 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸ done

-- SWbc-box @0210213443: 11 steps
lem-SWbc-box-at0210213443 : Ws → ⟪ (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-SWbc-box-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (CX14 ∷ Bx2-0143 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx2-0143 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210213443 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸
       at 1 3 (Bx2-0143 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0210213443 c4) ▸
       at 4 2 (CX14 ∷ CCZ013 ∷ []) (wp0189 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸
       at 2 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸ done

  b1 : Chain (CX14 ∷ Bx2-0143 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (Bx2-0143 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wp0769 c4) ▸
       at 0 3 (Bx2-0143 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210213443 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done

-- SWbc-box @0214233041: 11 steps
lem-SWbc-box-at0214233041 : Ws → ⟪ (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-SWbc-box-at0214233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (CX30 ∷ Bx2-4301 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 4 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 2 3 (Bx2-4301 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214233041 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸
       at 1 3 (Bx2-4301 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0214233041 c4) ▸
       at 4 2 (CX30 ∷ CCZ134 ∷ []) (wp0705 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸
       at 2 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸ done

  b1 : Chain (CX30 ∷ Bx2-4301 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (Bx2-4301 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wp0764 c4) ▸
       at 0 3 (Bx2-4301 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214233041 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- P-box @0312243041: 8 steps
lem-P-box-at0312243041 : Ws → ⟪ (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-P-box-at0312243041 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243041 c4) ▸
       at 0 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at0312243041 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at0312243041 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ01 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-tQ-at0312243041 c4)) ▸ done

-- P-box @02102441: 8 steps
lem-P-box-at02102441 : Ws → ⟪ (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-P-box-at02102441 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4) ▸
       at 0 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at02102441 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (sym (wl0912 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at02102441 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ13 ∷ []) (sym (wl0913 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0914 (lit c4))) ▸
       at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-tQ-at02102441 c4)) ▸ done

-- CXbc-box @02132130: 17 steps
lem-CXbc-box-at02132130 : Ws → ⟪ (CX10 ∷ Bx2-3104 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at02132130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx2-3104 ∷ CX10 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX10 ∷ CCZ124 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02132130 c4) ▸
       at 0 2 (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (sym (wp1190 c4)) ▸
       at 3 2 (Toff213 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1336 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX10 ∷ CCZ124 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CCZ024 ∷ CX31 ∷ CS34 ∷ CX10 ∷ []) (Bx2-3104 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS14⁻ ∷ []) (sym (wp0746 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0827 c4)) ▸
       at 3 2 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (sym (wp1190 c4)) ▸
       at 4 3 (CX10 ∷ []) (wp1191 c4) ▸
       at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-tQ-at02132130 c4)) ▸ done

  b2 : Chain (Bx2-3104 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ []) (Bx2-3104 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wp0505 c4)) ▸ done

-- CXcb-box @02132130: 18 steps
lem-CXcb-box-at02132130 : Ws → ⟪ (CX01 ∷ Bx2-3104 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at02132130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx2-3104 ∷ CX01 ∷ []) (Toff213 ∷ CCZ024 ∷ CX01 ∷ Toff203 ∷ CS04 ∷ CX30 ∷ Toff213 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ CCZ024 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02132130 c4) ▸
       at 0 2 (Toff213 ∷ CX01 ∷ Toff203 ∷ []) (wl1337 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (sym (wp1192 c4)) ▸
       at 1 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 8 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX01 ∷ Toff203 ∷ CS04 ∷ CX30 ∷ Toff213 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ CCZ024 ∷ CX01 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸
       at 3 2 (Toff213 ∷ Toff203 ∷ []) (wl1338 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX01 ∷ Toff203 ∷ []) (wl1337 (lit c4)) ▸
       at 3 3 (CX01 ∷ []) (wl1339 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ []) (Bx2-3104 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-tQ-at02132130 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp0499 c4)) ▸ done

-- P-box @03143041: 8 steps
lem-P-box-at03143041 : Ws → ⟪ (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-P-box-at03143041 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4) ▸
       at 0 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at03143041 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at03143041 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ01 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-tQ-at03143041 c4)) ▸ done

-- VPQ @03143041: 14 steps
lem-VPQ-at03143041 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at03143041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S3⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 1 2 (CS01⁻ ∷ S3 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS24⁻ ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143041 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS24⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS24⁻ ∷ []) (wl0439 (lit c4)) ▸
       at 0 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸
       at 2 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸ done

-- VPQ @02132031: 14 steps
lem-VPQ-at02132031 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (sym (wl0634 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (sym (wl0633 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (wp0514 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02132031 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (wl0632 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (wl0631 (lit c4)) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸ done

-- QVQ @0310213442: 3 steps
lem-QVQ-at0310213442 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at0310213442 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 1 4 (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0310213442 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done

-- CXbc-box @02132031: 17 steps
lem-CXbc-box-at02132031 : Ws → ⟪ (CX01 ∷ Bx2-3014 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx2-3014 ∷ CX01 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX01 ∷ CCZ024 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CCZ124 ∷ CX30 ∷ CS34 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02132031 c4) ▸
       at 0 2 (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (sym (wp1196 c4)) ▸
       at 3 2 (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1197 c4) ▸
       at 2 2 (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 9 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX01 ∷ CCZ024 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CCZ124 ∷ CX30 ∷ CS34 ∷ CX01 ∷ []) (Bx2-3014 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ124 ∷ CS04⁻ ∷ []) (sym (wp0318 c4)) ▸
       at 6 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 3 2 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (sym (wp1196 c4)) ▸
       at 4 3 (CX01 ∷ []) (wp1198 c4) ▸
       at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-tQ-at02132031 c4)) ▸ done

  b2 : Chain (Bx2-3014 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ []) (Bx2-3014 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (sym (wp0499 c4)) ▸ done

-- CXcb-box @02132031: 18 steps
lem-CXcb-box-at02132031 : Ws → ⟪ (CX10 ∷ Bx2-3014 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx2-3014 ∷ CX10 ∷ []) (Toff203 ∷ CCZ124 ∷ CX10 ∷ Toff213 ∷ CS14 ∷ CX31 ∷ Toff203 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ124 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02132031 c4) ▸
       at 0 2 (Toff203 ∷ CX10 ∷ Toff213 ∷ []) (wl1349 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (sym (wl1350 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX10 ∷ []) (sym (wp0672 c4)) ▸
       at 4 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 8 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 7 2 (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ CX10 ∷ Toff213 ∷ CS14 ∷ CX31 ∷ Toff203 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ124 ∷ CX10 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF203 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 3 2 (Toff203 ∷ Toff213 ∷ []) (sym (wl1338 (lit c4))) ▸
       at 2 2 (Toff203 ∷ CX10 ∷ Toff213 ∷ []) (wl1349 (lit c4)) ▸
       at 3 3 (CX10 ∷ []) (wl1352 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX10 ∷ []) (sym (wp0672 c4)) ▸ done

  b2 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ []) (Bx2-3014 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-tQ-at02132031 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wp0505 c4)) ▸ done

-- P-box @02132130: 8 steps
lem-P-box-at02132130 : Ws → ⟪ (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-P-box-at02132130 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02132130 c4) ▸
       at 0 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at02132130 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (sym (wp0780 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at02132130 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ04 ∷ []) (sym (wp0781 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0782 c4)) ▸
       at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-tQ-at02132130 c4)) ▸ done

-- VPQ @02132130: 14 steps
lem-VPQ-at02132130 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at02132130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 3 2 (CS04⁻ ∷ S2⁻ ∷ []) (sym (wp0018 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S2 ∷ []) (sym (wp0017 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS13⁻ ∷ []) (sym (wp0016 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02132130 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS13⁻ ∷ []) (wl0178 (lit c4)) ▸
       at 2 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS13⁻ ∷ []) (wl0177 (lit c4)) ▸
       at 0 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸
       at 2 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸ done

-- QVQ @0213243041: 3 steps
lem-QVQ-at0213243041 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0213243041 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Toff201 ∷ Toff201 ∷ []) (sym (wl0421 (lit c4))) ▸
       at 1 4 (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at0213243041 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done

-- P-box @0310243241: 8 steps
lem-P-box-at0310243241 : Ws → ⟪ (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-P-box-at0310243241 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4) ▸
       at 0 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0310243241 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (sym (wl0504 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0310243241 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ12 ∷ []) (sym (wl0505 (lit c4))) ▸
       at 2 2 (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0506 (lit c4))) ▸
       at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-tQ-at0310243241 c4)) ▸ done

-- CXbc-box @03122130: 17 steps
lem-CXbc-box-at03122130 : Ws → ⟪ (CX10 ∷ Bx3-2104 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at03122130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx3-2104 ∷ CX10 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX10 ∷ CCZ134 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CCZ034 ∷ CX21 ∷ CS24 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at03122130 c4) ▸
       at 0 2 (Toff312 ∷ CX10 ∷ []) (wl0537 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (sym (wp0225 c4)) ▸
       at 3 2 (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1356 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CX10 ∷ []) (wl0537 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX10 ∷ CCZ134 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CCZ034 ∷ CX21 ∷ CS24 ∷ CX10 ∷ []) (Bx3-2104 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS14⁻ ∷ []) (sym (wp0123 c4)) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 3 2 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (sym (wp0225 c4)) ▸
       at 4 3 (CX10 ∷ []) (wp0226 c4) ▸
       at 0 4 (Bx3-2104 ∷ []) (sym (lem-box-tQ-at03122130 c4)) ▸ done

  b2 : Chain (Bx3-2104 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ []) (Bx3-2104 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸ done

-- CXcb-box @03122130: 18 steps
lem-CXcb-box-at03122130 : Ws → ⟪ (CX01 ∷ Bx3-2104 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at03122130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx3-2104 ∷ CX01 ∷ []) (Toff312 ∷ CCZ034 ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CX20 ∷ Toff312 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ CCZ034 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at03122130 c4) ▸
       at 0 2 (Toff312 ∷ CX01 ∷ Toff302 ∷ []) (wl1357 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp1202 c4)) ▸
       at 1 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 4 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 8 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX20 ∷ []) (wl0534 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CX20 ∷ Toff312 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ CCZ034 ∷ CX01 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff312 ∷ CX20 ∷ []) (wl0534 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸
       at 3 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CX01 ∷ Toff302 ∷ []) (wl1357 (lit c4)) ▸
       at 3 3 (CX01 ∷ []) (wl1359 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 3 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ []) (Bx3-2104 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-2104 ∷ []) (sym (lem-box-tQ-at03122130 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0670 c4)) ▸ done

-- VPQ @03122031: 14 steps
lem-VPQ-at03122031 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at03122031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S3⁻ ∷ []) (sym (wl0786 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S3 ∷ []) (sym (wl0785 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03122031 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S)) ▸
       at 2 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S)) ▸
       at 0 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸
       at 2 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸ done

-- CXbc-box @03122031: 17 steps
lem-CXbc-box-at03122031 : Ws → ⟪ (CX01 ∷ Bx3-2014 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at03122031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx3-2014 ∷ CX01 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX01 ∷ CCZ034 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CCZ134 ∷ CX20 ∷ CS24 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03122031 c4) ▸
       at 0 2 (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CX01 ∷ CCZ034 ∷ []) (sym (wp1204 c4)) ▸
       at 3 2 (Toff302 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1205 c4) ▸
       at 2 2 (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 9 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX01 ∷ CCZ034 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CCZ134 ∷ CX20 ∷ CS24 ∷ CX01 ∷ []) (Bx3-2014 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS04⁻ ∷ []) (sym (wp1206 c4)) ▸
       at 6 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸
       at 4 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 3 2 (CCZ134 ∷ CX01 ∷ CCZ034 ∷ []) (sym (wp1204 c4)) ▸
       at 4 3 (CX01 ∷ []) (wp1207 c4) ▸
       at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-tQ-at03122031 c4)) ▸ done

  b2 : Chain (Bx3-2014 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ []) (Bx3-2014 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0670 c4)) ▸ done

-- CXcb-box @03122031: 18 steps
lem-CXcb-box-at03122031 : Ws → ⟪ (CX10 ∷ Bx3-2014 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at03122031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx3-2014 ∷ CX10 ∷ []) (Toff302 ∷ CCZ134 ∷ CX10 ∷ Toff312 ∷ CS14 ∷ CX21 ∷ Toff302 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ134 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03122031 c4) ▸
       at 0 2 (Toff302 ∷ CX10 ∷ Toff312 ∷ []) (wl1367 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (sym (wl1368 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX10 ∷ []) (sym (wp0712 c4)) ▸
       at 4 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 2 (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ CX10 ∷ Toff312 ∷ CS14 ∷ CX21 ∷ Toff302 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ134 ∷ CX10 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CX10 ∷ Toff312 ∷ []) (wl1367 (lit c4)) ▸
       at 3 3 (CX10 ∷ []) (wl1369 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ CX10 ∷ []) (sym (wp0712 c4)) ▸ done

  b2 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ []) (Bx3-2014 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-tQ-at03122031 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸ done

-- P-box @03122130: 8 steps
lem-P-box-at03122130 : Ws → ⟪ (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-P-box-at03122130 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at03122130 c4) ▸
       at 0 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at03122130 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (sym (wp0344 c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at03122130 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ04 ∷ []) (sym (wp0345 c4)) ▸
       at 2 2 (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4)) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0346 c4)) ▸
       at 0 4 (Bx3-2104 ∷ []) (sym (lem-box-tQ-at03122130 c4)) ▸ done

-- VPQ @03122130: 14 steps
lem-VPQ-at03122130 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at03122130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 3 2 (CS04⁻ ∷ S3⁻ ∷ []) (sym (wp0348 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff312 ∷ []) (lem-comm-TOFF312-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S3 ∷ []) (sym (wp0349 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS12⁻ ∷ []) (sym (wp0350 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at03122130 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S)) ▸
       at 2 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S • S • S)) ▸
       at 0 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸
       at 2 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸ done

-- VPQ @02142041: 14 steps
lem-VPQ-at02142041 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 4 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (sym (wl0177 (lit c4))) ▸
       at 2 2 (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S2 ∷ []) (sym (wl0178 (lit c4))) ▸
       at 0 2 (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS04⁻ ∷ []) (wp0017 c4) ▸
       at 2 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4) ▸
       at 0 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸
       at 2 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸ done

-- t-cP @02142041: 5 steps
lem-t-cP-at02142041 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-t-cP-at02142041 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 2 (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (sym (wp0027 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4) ▸
       at 2 3 (CCZ024 ∷ Toff204 ∷ []) (sym (wp0028 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4) ▸ done

-- VPQ @0314203241: 14 steps
lem-VPQ-at0314203241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 4 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S3⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S • S • S))) ▸
       at 2 2 (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S3 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S))) ▸
       at 0 2 (CS12⁻ ∷ CS04⁻ ∷ []) (wp0350 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS04⁻ ∷ []) (wp0349 c4) ▸
       at 2 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS04⁻ ∷ []) (wp0348 c4) ▸
       at 0 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸
       at 2 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸ done

-- t-cP @0314203241: 5 steps
lem-t-cP-at0314203241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-t-cP-at0314203241 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 2 (CCZ034 ∷ Toff304 ∷ CZ04 ∷ []) (sym (wp1033 c4)) ▸
       at 2 2 (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4)) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4) ▸
       at 2 3 (CCZ034 ∷ Toff304 ∷ []) (sym (wp1034 c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4) ▸ done

-- CK-box @033440: 6 steps
lem-CK-box-at033440 : Ws → ⟪ (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-CK-box-at033440 c4 = run b0
  where
  b0 : Chain (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 0 2 (Toff312 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF312 (lit c4)) ▸
       at 1 2 (Toff034 ∷ CK40 ∷ []) (wp1216 c4) ▸
       at 2 2 (Toff312 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF312 (lit c4)) ▸
       at 3 2 (Toff034 ∷ CK40 ∷ []) (wp1216 c4) ▸
       at 4 2 [] (wp1217 c4) ▸ done

-- SWbc-box @021021: 11 steps
lem-SWbc-box-at021021 : Ws → ⟪ (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-SWbc-box-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (CX13 ∷ Bx2-0134 ∷ CX13 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 4 1 (CX13 ∷ CX31 ∷ CX13 ∷ []) (sym (wl0278 (lit c4))) ▸
       at 2 3 (Bx2-0134 ∷ CCZ014 ∷ []) (lem-CXbc-box-at021021 c4) ▸
       at 3 2 (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1229 c4) ▸
       at 1 3 (Bx2-0134 ∷ CCZ034 ∷ []) (lem-CXcb-box-at021021 c4) ▸
       at 4 2 (CX13 ∷ CCZ014 ∷ []) (wp0795 c4) ▸
       at 3 2 (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp1230 c4) ▸
       at 2 2 (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp1230 c4) ▸ done

  b1 : Chain (CX13 ∷ Bx2-0134 ∷ CX13 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (Bx2-0134 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp1231 c4) ▸
       at 0 3 (Bx2-0134 ∷ CCZ014 ∷ []) (lem-CXbc-box-at021021 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done

-- VPQ @02102331: 14 steps
lem-VPQ-at02102331 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at02102331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (sym (wl0634 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (sym (wl0633 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (wp0514 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02102331 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (wl0632 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (wl0631 (lit c4)) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸ done

-- P-box @031031: 8 steps
lem-P-box-at031031 : Ws → ⟪ (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-P-box-at031031 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4) ▸
       at 0 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at031031 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (sym (wl1253 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at031031 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ14 ∷ []) (sym (wl1254 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1255 (lit c4))) ▸
       at 0 4 (Bx3-0214 ∷ []) (sym (lem-box-tQ-at031031 c4)) ▸ done

-- CXbc-box @142142: 17 steps
lem-CXbc-box-at142142 : Ws → ⟪ (CX13 ∷ Bx0-4132 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at142142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-4132 ∷ CX13 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX13 ∷ CCZ012 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4) ▸
       at 0 2 (Toff014 ∷ CX13 ∷ []) (wp0963 c4) ▸
       at 1 2 (CCZ023 ∷ CX13 ∷ CCZ012 ∷ []) (sym (wl1393 (lit c4))) ▸
       at 3 2 (Toff014 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1233 c4) ▸
       at 2 2 (Toff014 ∷ CX13 ∷ []) (wp0963 c4) ▸
       at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX13 ∷ CCZ012 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ023 ∷ CX41 ∷ CS24 ∷ CX13 ∷ []) (Bx0-4132 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS12⁻ ∷ []) (sym (wl0620 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX13 ∷ CCZ012 ∷ []) (sym (wl1393 (lit c4))) ▸
       at 4 3 (CX13 ∷ []) (wl1394 (lit c4)) ▸
       at 0 4 (Bx0-4132 ∷ []) (sym (lem-box-tQ-at142142 c4)) ▸ done

  b2 : Chain (Bx0-4132 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-4132 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0272 (lit c4))) ▸ done

-- CXcb-box @142142: 18 steps
lem-CXcb-box-at142142 : Ws → ⟪ (CX31 ∷ Bx0-4132 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at142142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-4132 ∷ CX31 ∷ []) (Toff014 ∷ CCZ023 ∷ CX31 ∷ Toff034 ∷ CS23 ∷ CX43 ∷ Toff014 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ CCZ023 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4) ▸
       at 0 2 (Toff014 ∷ CX31 ∷ Toff034 ∷ []) (wp1234 c4) ▸
       at 2 2 (CCZ023 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp1235 c4)) ▸
       at 1 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 4 1 (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0330 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 7 2 (Toff014 ∷ CX43 ∷ []) (wp0960 c4) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX31 ∷ Toff034 ∷ CS23 ∷ CX43 ∷ Toff014 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ CCZ023 ∷ CX31 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX43 ∷ []) (wp0960 c4) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4)) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0330 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff034 ∷ []) (sym (wp0203 c4)) ▸
       at 2 2 (Toff014 ∷ CX31 ∷ Toff034 ∷ []) (wp1234 c4) ▸
       at 3 3 (CX31 ∷ []) (wp1236 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 3 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-4132 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-4132 ∷ []) (sym (lem-box-tQ-at142142 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0277 (lit c4))) ▸ done

-- P-box @03243042: 8 steps
lem-P-box-at03243042 : Ws → ⟪ (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-P-box-at03243042 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) (Bx3-1402 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243042 c4) ▸
       at 0 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at03243042 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (sym (wl1235 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at03243042 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl1236 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 0 4 (Bx3-1402 ∷ []) (sym (lem-box-tQ-at03243042 c4)) ▸ done

-- VPQ @03243042: 14 steps
lem-VPQ-at03243042 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at03243042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 4 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 3 2 (CS02⁻ ∷ S3⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))) ▸
       at 2 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ S3 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))) ▸
       at 0 2 (CS02⁻ ∷ CS14⁻ ∷ []) (sym (wp0703 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243042 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS14⁻ ∷ []) (wl0785 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS14⁻ ∷ []) (wl0786 (lit c4)) ▸
       at 0 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸
       at 2 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸ done

-- P-box @2442: 8 steps
lem-P-box-at2442 : Ws → ⟪ (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-P-box-at2442 c4 = run b0
  where
  b0 : Chain (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) (Bx0-1432 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at2442 c4) ▸
       at 0 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at2442 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (sym (wl0825 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff023 ∷ []) (sym (lem-tP-at2442 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ23 ∷ []) (sym (wl0826 (lit c4))) ▸
       at 2 2 (Toff014 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF014 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0827 (lit c4))) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸ done

-- CXbc-box @02102331: 17 steps
lem-CXbc-box-at02102331 : Ws → ⟪ (CX31 ∷ Bx2-0314 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at02102331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx2-0314 ∷ CX31 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX31 ∷ CCZ234 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ124 ∷ CX03 ∷ CS04 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02102331 c4) ▸
       at 0 2 (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CX31 ∷ CCZ234 ∷ []) (sym (wl1398 (lit c4))) ▸
       at 3 2 (Toff203 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1249 c4) ▸
       at 2 2 (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4)) ▸
       at 5 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 9 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 8 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX31 ∷ CCZ234 ∷ CS34 ∷ CX03 ∷ CS34⁻ ∷ CCZ124 ∷ CX03 ∷ CS04 ∷ CX31 ∷ []) (Bx2-0314 ∷ CX31 ∷ CCZ034 ∷ CX31 ∷ [])
  b1 = at 7 2 (CCZ124 ∷ CS34⁻ ∷ []) (sym (wl1399 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ234 ∷ []) (sym (wl0527 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX31 ∷ CCZ234 ∷ []) (sym (wl1398 (lit c4))) ▸
       at 4 3 (CX31 ∷ []) (wl1400 (lit c4)) ▸
       at 0 4 (Bx2-0314 ∷ []) (sym (lem-box-tQ-at02102331 c4)) ▸ done

  b2 : Chain (Bx2-0314 ∷ CX31 ∷ CCZ034 ∷ CX31 ∷ []) (Bx2-0314 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (sym (wp1228 c4)) ▸ done

-- CXcb-box @02102331: 18 steps
lem-CXcb-box-at02102331 : Ws → ⟪ (CX13 ∷ Bx2-0314 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at02102331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx2-0314 ∷ CX13 ∷ []) (Toff203 ∷ CCZ124 ∷ CX13 ∷ Toff201 ∷ CS14 ∷ CX01 ∷ Toff203 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ124 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02102331 c4) ▸
       at 0 2 (Toff203 ∷ CX13 ∷ Toff201 ∷ []) (wl1401 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸
       at 1 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 8 2 (Toff203 ∷ CS04 ∷ []) (wp1251 c4) ▸
       at 7 2 (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ CX13 ∷ Toff201 ∷ CS14 ∷ CX01 ∷ Toff203 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ124 ∷ CX13 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX13 ∷ CCZ014 ∷ CX13 ∷ [])
  b1 = at 5 2 (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF203 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 3 2 (Toff203 ∷ Toff201 ∷ []) (wl1391 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CX13 ∷ Toff201 ∷ []) (wl1401 (lit c4)) ▸
       at 3 3 (CX13 ∷ []) (wl1402 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸ done

  b2 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX13 ∷ CCZ014 ∷ CX13 ∷ []) (Bx2-0314 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-0314 ∷ []) (sym (lem-box-tQ-at02102331 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp1226 c4)) ▸ done

-- VPQ @142142: 14 steps
lem-VPQ-at142142 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 4 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 3 2 (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS23⁻ ∷ CS14⁻ ∷ []) (wl0202 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS14⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS14⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸
       at 2 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸ done

-- t-cP @142142: 5 steps
lem-t-cP-at142142 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-t-cP-at142142 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 2 (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (sym (wp0058 c4)) ▸
       at 2 2 (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4)) ▸
       at 1 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4) ▸
       at 2 3 (CCZ014 ∷ Toff014 ∷ []) (sym (wp0059 c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4) ▸ done

-- t-cP @033440: 5 steps
lem-t-cP-at033440 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-t-cP-at033440 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ [])
  b0 = at 0 2 (CCZ123 ∷ Toff312 ∷ CZ12 ∷ []) (sym (wl1403 (lit c4))) ▸
       at 2 2 (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4)) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4) ▸
       at 2 3 (CCZ123 ∷ Toff312 ∷ []) (sym (wl0882 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4) ▸ done

-- t-cP @0214203143: 5 steps
lem-t-cP-at0214203143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-t-cP-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 2 (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (sym (wp0027 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4) ▸
       at 2 3 (CCZ024 ∷ Toff204 ∷ []) (sym (wp0028 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4) ▸ done

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

-- CXbc-box @041041: 17 steps
lem-CXbc-box-at041041 : Ws → ⟪ (CX23 ∷ Bx4-0231 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at041041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx4-0231 ∷ CX23 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CX23 ∷ CCZ124 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at041041 c4) ▸
       at 0 2 (Toff402 ∷ CX23 ∷ []) (wp1317 c4) ▸
       at 1 2 (CCZ134 ∷ CX23 ∷ CCZ124 ∷ []) (sym (wl1562 (lit c4))) ▸
       at 3 2 (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1385 c4) ▸
       at 2 2 (Toff402 ∷ CX23 ∷ []) (wp1317 c4) ▸
       at 5 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 8 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CX23 ∷ CCZ124 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ CX23 ∷ []) (Bx4-0231 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS12⁻ ∷ []) (sym (wl0392 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS12 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ CX23 ∷ CCZ124 ∷ []) (sym (wl1562 (lit c4))) ▸
       at 4 3 (CX23 ∷ []) (wl1563 (lit c4)) ▸
       at 0 4 (Bx4-0231 ∷ []) (sym (lem-box-tQ-at041041 c4)) ▸ done

  b2 : Chain (Bx4-0231 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ []) (Bx4-0231 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wl1564 (lit c4))) ▸ done

-- CXcb-box @041041: 18 steps
lem-CXcb-box-at041041 : Ws → ⟪ (CX32 ∷ Bx4-0231 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at041041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx4-0231 ∷ CX32 ∷ []) (Toff402 ∷ CCZ134 ∷ CX32 ∷ Toff403 ∷ CS13 ∷ CX03 ∷ Toff402 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ134 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at041041 c4) ▸
       at 0 2 (Toff402 ∷ CX32 ∷ Toff403 ∷ []) (wp1386 c4) ▸
       at 2 2 (CCZ134 ∷ Toff403 ∷ CCZ013 ∷ []) (sym (wp1387 c4)) ▸
       at 1 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl1021 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (Toff402 ∷ CS01 ∷ []) (wp1388 c4) ▸
       at 7 2 (Toff402 ∷ CX03 ∷ []) (wp1311 c4) ▸
       at 6 2 (Toff402 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF402 (lit c4)) ▸ done

  b1 : Chain (Toff402 ∷ CCZ134 ∷ CX32 ∷ Toff403 ∷ CS13 ∷ CX03 ∷ Toff402 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ134 ∷ CX32 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ [])
  b1 = at 5 2 (Toff402 ∷ CX03 ∷ []) (wp1311 c4) ▸
       at 4 2 (Toff402 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF402 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (Toff402 ∷ Toff403 ∷ []) (sym (wp1389 c4)) ▸
       at 2 2 (Toff402 ∷ CX32 ∷ Toff403 ∷ []) (wp1386 c4) ▸
       at 3 3 (CX32 ∷ []) (wp1390 c4) ▸
       at 4 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 3 2 (CCZ134 ∷ CX32 ∷ []) (sym (wl1021 (lit c4))) ▸ done

  b2 : Chain (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ []) (Bx4-0231 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx4-0231 ∷ []) (sym (lem-box-tQ-at041041 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wl1565 (lit c4))) ▸ done

-- P-box @0410233241: 8 steps
lem-P-box-at0410233241 : Ws → ⟪ (Toff412 ∷ Bx4-0321 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-P-box-at0410233241 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx4-0321 ∷ Toff412 ∷ []) (Bx4-0321 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0410233241 c4) ▸
       at 0 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0410233241 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (sym (wl1569 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0410233241 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ12 ∷ []) (sym (wl1570 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4)) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wl1571 (lit c4))) ▸
       at 0 4 (Bx4-0321 ∷ []) (sym (lem-box-tQ-at0410233241 c4)) ▸ done

-- VPQ @0410233241: 14 steps
lem-VPQ-at0410233241 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0410233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 4 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S4⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))) ▸
       at 2 2 (CS12⁻ ∷ Toff403 ∷ []) (lem-comm-TOFF403-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S4 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S ↑))) ▸
       at 0 2 (CS12⁻ ∷ CS03⁻ ∷ []) (wl0469 (lit c4)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0410233241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S)) ▸
       at 2 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸
       at 2 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸ done

-- VPQ @0412213043: 14 steps
lem-VPQ-at0412213043 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0412213043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 3 2 (CS03⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS03⁻ ∷ CS12⁻ ∷ []) (sym (wl0469 (lit c4))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0412213043 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑)) ▸
       at 2 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸
       at 2 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸ done

-- P-box @04122041: 8 steps
lem-P-box-at04122041 : Ws → ⟪ (Toff413 ∷ Bx4-2031 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-P-box-at04122041 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Bx4-2031 ∷ Toff413 ∷ []) (Bx4-2031 ∷ [])
  b0 = at 1 1 (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4) ▸
       at 0 2 (Toff402 ∷ Toff413 ∷ []) (sym (lem-tP-at04122041 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ13 ∷ Toff413 ∷ []) (sym (wl1482 (lit c4))) ▸
       at 3 2 (Toff402 ∷ Toff413 ∷ []) (sym (lem-tP-at04122041 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ13 ∷ []) (sym (wl1483 (lit c4))) ▸
       at 2 2 (Toff402 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF402 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1484 (lit c4))) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-tQ-at04122041 c4)) ▸ done

-- CXbc-box @04233240: 17 steps
lem-CXbc-box-at04233240 : Ws → ⟪ (CX32 ∷ Bx4-1320 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at04233240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx4-1320 ∷ CX32 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX32 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233240 c4) ▸
       at 0 2 (Toff413 ∷ CX32 ∷ []) (wl1586 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 3 2 (Toff413 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp1396 c4) ▸
       at 2 2 (Toff413 ∷ CX32 ∷ []) (wl1586 (lit c4)) ▸
       at 5 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX32 ∷ CCZ034 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ024 ∷ CX13 ∷ CS01 ∷ CX32 ∷ []) (Bx4-1320 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 3 2 (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (sym (wp0717 c4)) ▸
       at 4 3 (CX32 ∷ []) (wp0718 c4) ▸
       at 0 4 (Bx4-1320 ∷ []) (sym (lem-box-tQ-at04233240 c4)) ▸ done

  b2 : Chain (Bx4-1320 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ []) (Bx4-1320 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wl1565 (lit c4))) ▸ done

-- CXcb-box @04233240: 18 steps
lem-CXcb-box-at04233240 : Ws → ⟪ (CX23 ∷ Bx4-1320 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at04233240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx4-1320 ∷ CX23 ∷ []) (Toff413 ∷ CCZ024 ∷ CX23 ∷ Toff412 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233240 c4) ▸
       at 0 2 (Toff413 ∷ CX23 ∷ Toff412 ∷ []) (wl1587 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff412 ∷ CCZ012 ∷ []) (sym (wp1397 c4)) ▸
       at 1 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸
       at 4 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS01 ∷ []) (wp1398 c4) ▸
       at 7 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ CX23 ∷ Toff412 ∷ CS02 ∷ CX12 ∷ Toff413 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ024 ∷ CX23 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ [])
  b1 = at 5 2 (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (Toff413 ∷ Toff412 ∷ []) (wl1589 (lit c4)) ▸
       at 2 2 (Toff413 ∷ CX23 ∷ Toff412 ∷ []) (wl1587 (lit c4)) ▸
       at 3 3 (CX23 ∷ []) (wl1590 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ012 ∷ []) (wp0142 c4) ▸
       at 3 2 (CCZ024 ∷ CX23 ∷ []) (sym (wp0082 c4)) ▸ done

  b2 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ []) (Bx4-1320 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx4-1320 ∷ []) (sym (lem-box-tQ-at04233240 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1564 (lit c4))) ▸ done

-- P-box @0440: 8 steps
lem-P-box-at0440 : Ws → ⟪ (Toff403 ∷ Bx4-1230 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-P-box-at0440 c4 = run b0
  where
  b0 : Chain (Toff403 ∷ Bx4-1230 ∷ Toff403 ∷ []) (Bx4-1230 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 0 2 (Toff412 ∷ Toff403 ∷ []) (sym (lem-tP-at0440 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) (sym (wp1399 c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (sym (lem-tP-at0440 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ03 ∷ []) (sym (wp1400 c4)) ▸
       at 2 2 (Toff412 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF412 (lit c4)) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0375 c4)) ▸
       at 0 4 (Bx4-1230 ∷ []) (sym (lem-box-tQ-at0440 c4)) ▸ done

-- VPQ @0440: 14 steps
lem-VPQ-at0440 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 3 2 (CS03⁻ ∷ S4⁻ ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))) ▸
       at 2 2 (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S4 ∷ []) (sym (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))) ▸
       at 0 2 (CS03⁻ ∷ CS12⁻ ∷ []) (sym (wl0469 (lit c4))) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0440 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS12⁻ ∷ S4 ∷ Toff403 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑)) ▸
       at 2 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑)) ▸
       at 0 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸
       at 2 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸ done

-- CXbc-box @0413203142: 17 steps
lem-CXbc-box-at0413203142 : Ws → ⟪ (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXbc-box-at0413203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CX01 ∷ CCZ024 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ CCZ124 ∷ CX30 ∷ CS23 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203142 c4) ▸
       at 0 2 (Toff403 ∷ CX01 ∷ []) (wp1401 c4) ▸
       at 1 2 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (sym (wp1196 c4)) ▸
       at 3 2 (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1402 c4) ▸
       at 2 2 (Toff403 ∷ CX01 ∷ []) (wp1401 c4) ▸
       at 5 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸ done

  b1 : Chain (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CX01 ∷ CCZ024 ∷ CS02 ∷ CX30 ∷ CS02⁻ ∷ CCZ124 ∷ CX30 ∷ CS23 ∷ CX01 ∷ []) (Bx4-3012 ∷ CX01 ∷ CCZ023 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ124 ∷ CS02⁻ ∷ []) (sym (wp0679 c4)) ▸
       at 6 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 6 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 3 2 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (sym (wp1196 c4)) ▸
       at 4 3 (CX01 ∷ []) (wp1198 c4) ▸
       at 0 4 (Bx4-3012 ∷ []) (sym (lem-box-tQ-at0413203142 c4)) ▸ done

  b2 : Chain (Bx4-3012 ∷ CX01 ∷ CCZ023 ∷ CX01 ∷ []) (Bx4-3012 ∷ CCZ023 ∷ [])
  b2 = at 1 3 (CCZ023 ∷ []) (sym (wl1597 (lit c4))) ▸ done

-- CXcb-box @0413203142: 18 steps
lem-CXcb-box-at0413203142 : Ws → ⟪ (CX10 ∷ Bx4-3012 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at0413203142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx4-3012 ∷ CX10 ∷ []) (Toff403 ∷ CCZ124 ∷ CX10 ∷ Toff413 ∷ CS12 ∷ CX31 ∷ Toff403 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ124 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203142 c4) ▸
       at 0 2 (Toff403 ∷ CX10 ∷ Toff413 ∷ []) (wp1403 c4) ▸
       at 2 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX10 ∷ []) (sym (wp0672 c4)) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (Toff403 ∷ CS23 ∷ []) (wp1404 c4) ▸
       at 7 2 (Toff403 ∷ CX31 ∷ []) (wp1405 c4) ▸
       at 6 2 (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4)) ▸ done

  b1 : Chain (Toff403 ∷ CCZ124 ∷ CX10 ∷ Toff413 ∷ CS12 ∷ CX31 ∷ Toff403 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ124 ∷ CX10 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX10 ∷ CCZ123 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff403 ∷ CX31 ∷ []) (wp1405 c4) ▸
       at 4 2 (Toff403 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF403 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff413 ∷ []) (sym (wp1377 c4)) ▸
       at 2 2 (Toff403 ∷ CX10 ∷ Toff413 ∷ []) (wp1403 c4) ▸
       at 3 3 (CX10 ∷ []) (wp1406 c4) ▸
       at 4 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ CX10 ∷ []) (sym (wp0672 c4)) ▸ done

  b2 : Chain (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX10 ∷ CCZ123 ∷ CX10 ∷ []) (Bx4-3012 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx4-3012 ∷ []) (sym (lem-box-tQ-at0413203142 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl1599 (lit c4))) ▸ done

-- VPQ @02142140: 14 steps
lem-VPQ-at02142140 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at02142140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 4 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 3 2 (CS03⁻ ∷ S2⁻ ∷ []) (sym (wl0631 (lit c4))) ▸
       at 2 2 (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4)) ▸
       at 1 2 (CS03⁻ ∷ S2 ∷ []) (sym (wl0632 (lit c4))) ▸
       at 0 2 (CS03⁻ ∷ CS14⁻ ∷ []) (sym (wp0514 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff203 ∷ Toff214 ∷ []) (lem-tP-at02142140 c4) ▸ done

  b1 : Chain (CS03⁻ ∷ CS14⁻ ∷ S2 ∷ Toff203 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS14⁻ ∷ []) (wl0633 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS14⁻ ∷ []) (wl0634 (lit c4)) ▸
       at 0 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸
       at 2 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸ done

-- CXbc-box @0413213042: 17 steps
lem-CXbc-box-at0413213042 : Ws → ⟪ (CX10 ∷ Bx4-3102 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at0413213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx4-3102 ∷ CX10 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX10 ∷ CCZ124 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CCZ024 ∷ CX31 ∷ CS23 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213042 c4) ▸
       at 0 2 (Toff413 ∷ CX10 ∷ []) (wp1407 c4) ▸
       at 1 2 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (sym (wp1190 c4)) ▸
       at 3 2 (Toff413 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl1603 (lit c4)) ▸
       at 2 2 (Toff413 ∷ CX10 ∷ []) (wp1407 c4) ▸
       at 5 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CX10 ∷ CCZ124 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CCZ024 ∷ CX31 ∷ CS23 ∷ CX10 ∷ []) (Bx4-3102 ∷ CX10 ∷ CCZ123 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0827 c4)) ▸
       at 3 2 (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (sym (wp1190 c4)) ▸
       at 4 3 (CX10 ∷ []) (wp1191 c4) ▸
       at 0 4 (Bx4-3102 ∷ []) (sym (lem-box-tQ-at0413213042 c4)) ▸ done

  b2 : Chain (Bx4-3102 ∷ CX10 ∷ CCZ123 ∷ CX10 ∷ []) (Bx4-3102 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl1599 (lit c4))) ▸ done

-- CXcb-box @0413213042: 18 steps
lem-CXcb-box-at0413213042 : Ws → ⟪ (CX01 ∷ Bx4-3102 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at0413213042 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx4-3102 ∷ CX01 ∷ []) (Toff413 ∷ CCZ024 ∷ CX01 ∷ Toff403 ∷ CS02 ∷ CX30 ∷ Toff413 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ CCZ024 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213042 c4) ▸
       at 0 2 (Toff413 ∷ CX01 ∷ Toff403 ∷ []) (wp1408 c4) ▸
       at 2 2 (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (sym (wp1374 c4)) ▸
       at 1 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4)) ▸
       at 7 2 (Toff413 ∷ CX30 ∷ []) (wp1409 c4) ▸
       at 6 2 (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4)) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ CX01 ∷ Toff403 ∷ CS02 ∷ CX30 ∷ Toff413 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ CCZ024 ∷ CX01 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX01 ∷ CCZ023 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff413 ∷ CX30 ∷ []) (wp1409 c4) ▸
       at 4 2 (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸
       at 3 2 (Toff413 ∷ Toff403 ∷ []) (wp1377 c4) ▸
       at 2 2 (Toff413 ∷ CX01 ∷ Toff403 ∷ []) (wp1408 c4) ▸
       at 3 3 (CX01 ∷ []) (wp1410 c4) ▸
       at 4 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸ done

  b2 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CX01 ∷ CCZ023 ∷ CX01 ∷ []) (Bx4-3102 ∷ CCZ023 ∷ [])
  b2 = at 0 4 (Bx4-3102 ∷ []) (sym (lem-box-tQ-at0413213042 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (sym (wl1597 (lit c4))) ▸ done

-- P-box @0413203142: 8 steps
lem-P-box-at0413203142 : Ws → ⟪ (Toff412 ∷ Bx4-3012 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-P-box-at0413203142 c4 = run b0
  where
  b0 : Chain (Toff412 ∷ Bx4-3012 ∷ Toff412 ∷ []) (Bx4-3012 ∷ [])
  b0 = at 1 1 (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203142 c4) ▸
       at 0 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0413203142 c4)) ▸
       at 1 2 (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (sym (wl1569 (lit c4))) ▸
       at 3 2 (Toff403 ∷ Toff412 ∷ []) (sym (lem-tP-at0413203142 c4)) ▸
       at 4 3 (CCZ124 ∷ CZ12 ∷ []) (sym (wl1570 (lit c4))) ▸
       at 2 2 (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4)) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wl1571 (lit c4))) ▸
       at 0 4 (Bx4-3012 ∷ []) (sym (lem-box-tQ-at0413203142 c4)) ▸ done

-- VPQ @0413203142: 14 steps
lem-VPQ-at0413203142 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0413203142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (sym (wp0316 c4)) ▸
       at 4 2 (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (sym (wl0468 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S4⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))) ▸
       at 2 2 (CS12⁻ ∷ Toff403 ∷ []) (lem-comm-TOFF403-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S4 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S ↑))) ▸
       at 0 2 (CS12⁻ ∷ CS03⁻ ∷ []) (wl0469 (lit c4)) ▸
       at 4 2 [] (wl0456 (lit c4)) ▸
       at 3 2 (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0413203142 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS03⁻ ∷ S4 ∷ Toff412 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S4⁻ ∷ S4 ∷ []) (sym (wl0456 (lit c4))) ▸
       at 1 2 (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S)) ▸
       at 2 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸
       at 3 2 (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S)) ▸
       at 0 4 (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4)) ▸
       at 2 4 (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4) ▸ done

-- CXbc-box @0440: 17 steps
lem-CXbc-box-at0440 : Ws → ⟪ (CX23 ∷ Bx4-1230 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx4-1230 ∷ CX23 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX23 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CCZ034 ∷ CX12 ∷ CS01 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 0 2 (Toff412 ∷ CX23 ∷ []) (wl1609 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 3 2 (Toff412 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp1413 c4) ▸
       at 2 2 (Toff412 ∷ CX23 ∷ []) (wl1609 (lit c4)) ▸
       at 5 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CX23 ∷ CCZ024 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CCZ034 ∷ CX12 ∷ CS01 ∷ CX23 ∷ []) (Bx4-1230 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 3 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 4 3 (CX23 ∷ []) (wp0110 c4) ▸
       at 0 4 (Bx4-1230 ∷ []) (sym (lem-box-tQ-at0440 c4)) ▸ done

  b2 : Chain (Bx4-1230 ∷ CX23 ∷ CCZ012 ∷ CX23 ∷ []) (Bx4-1230 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wl1564 (lit c4))) ▸ done

-- CXcb-box @0440: 18 steps
lem-CXcb-box-at0440 : Ws → ⟪ (CX32 ∷ Bx4-1230 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx4-1230 ∷ CX32 ∷ []) (Toff412 ∷ CCZ034 ∷ CX32 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ Toff412 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ034 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4) ▸
       at 0 2 (Toff412 ∷ CX32 ∷ Toff413 ∷ []) (wl1610 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff413 ∷ CCZ013 ∷ []) (sym (wp1414 c4)) ▸
       at 1 2 (CCZ034 ∷ CX32 ∷ []) (sym (wp0101 c4)) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (Toff412 ∷ CS01 ∷ []) (wp1415 c4) ▸
       at 7 2 (Toff412 ∷ CX13 ∷ []) (wl1611 (lit c4)) ▸
       at 6 2 (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ CX32 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ Toff412 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ034 ∷ CX32 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ [])
  b1 = at 5 2 (Toff412 ∷ CX13 ∷ []) (wl1611 (lit c4)) ▸
       at 4 2 (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (Toff412 ∷ Toff413 ∷ []) (sym (wl1589 (lit c4))) ▸
       at 2 2 (Toff412 ∷ CX32 ∷ Toff413 ∷ []) (wl1610 (lit c4)) ▸
       at 3 3 (CX32 ∷ []) (wl1612 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4) ▸
       at 3 2 (CCZ034 ∷ CX32 ∷ []) (sym (wp0101 c4)) ▸ done

  b2 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ CX32 ∷ CCZ013 ∷ CX32 ∷ []) (Bx4-1230 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx4-1230 ∷ []) (sym (lem-box-tQ-at0440 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wl1565 (lit c4))) ▸ done
