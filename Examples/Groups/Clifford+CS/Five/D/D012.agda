{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D012 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0179 ; wl0230 ; wl0297 ; wl0321 ; wl0327 ; wl0330 ; wl0341 ; wl0421 ; wl0423 ; wl0441 ; wl0442 ; wl0482 ; wl0618 ; wl0702 ; wl0707 ; wl0763 ; wl0765 ; wl0770 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0808 ; wl0831 ; wl0866 ; wl0867 ; wl0868 ; wl0912 ; wl0913 ; wl0914 ; wl0917 ; wl0920 ; wl0923 ; wl1273 ; wl1321 ; wl1323 ; wl1324 ; wl1325 ; wl1326 ; wl1327 ; wl1336 ; wl1337 ; wl1338 ; wl1339 ; wp0022 ; wp0034 ; wp0036 ; wp0081 ; wp0087 ; wp0092 ; wp0109 ; wp0161 ; wp0167 ; wp0189 ; wp0272 ; wp0378 ; wp0380 ; wp0499 ; wp0505 ; wp0566 ; wp0567 ; wp0703 ; wp0705 ; wp0746 ; wp0759 ; wp0762 ; wp0763 ; wp0764 ; wp0769 ; wp0778 ; wp0827 ; wp0945 ; wp1037 ; wp1055 ; wp1059 ; wp1143 ; wp1144 ; wp1151 ; wp1152 ; wp1153 ; wp1154 ; wp1159 ; wp1160 ; wp1161 ; wp1190 ; wp1191 ; wp1192 ; wp1193 ; wl0176 ; wl0177 ; wl0178 ; wl0271 ; wl0305 ; wl0332 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0471 ; wl0504 ; wl0505 ; wl0506 ; wl0534 ; wl0537 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0639 ; wl0757 ; wl0879 ; wl1222 ; wl1343 ; wl1348 ; wl1349 ; wl1350 ; wl1351 ; wl1352 ; wl1356 ; wl1357 ; wl1358 ; wl1359 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0066 ; wp0103 ; wp0106 ; wp0108 ; wp0123 ; wp0221 ; wp0225 ; wp0226 ; wp0301 ; wp0318 ; wp0384 ; wp0450 ; wp0514 ; wp0515 ; wp0550 ; wp0663 ; wp0670 ; wp0672 ; wp0679 ; wp0712 ; wp0780 ; wp0781 ; wp0782 ; wp1196 ; wp1197 ; wp1198 ; wp1199 ; wp1202 ; wl0488 ; wl1220 ; wl1233 ; wl1304 ; wl1367 ; wl1368 ; wl1369 ; wp0027 ; wp0028 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0513 ; wp1003 ; wp1006 ; wp1033 ; wp1034 ; wp1204 ; wp1205 ; wp1206 ; wp1207 ; wl0272 ; wl0277 ; wl0278 ; wl0280 ; wl0334 ; wl0527 ; wl0620 ; wl0621 ; wl0774 ; wl1235 ; wl1236 ; wl1253 ; wl1254 ; wl1255 ; wl1391 ; wl1393 ; wl1394 ; wp0003 ; wp0203 ; wp0231 ; wp0795 ; wp0817 ; wp0960 ; wp0963 ; wp1216 ; wp1217 ; wp1226 ; wp1228 ; wp1229 ; wp1230 ; wp1231 ; wp1233 ; wp1234 ; wp1235 ; wp1236 ; wl0159 ; wl0201 ; wl0202 ; wl0448 ; wl0825 ; wl0826 ; wl0827 ; wl0882 ; wl1398 ; wl1399 ; wl1400 ; wl1401 ; wl1402 ; wl1403 ; wp0050 ; wp0053 ; wp0058 ; wp0059 ; wp0593 ; wp1249 ; wp1250 ; wp1251 ; wl0233 ; wl0393 ; wl0455 ; wl0456 ; wl0461 ; wl0677 ; wl0901 ; wl1465 ; wl1466 ; wl1467 ; wl1473 ; wl1479 ; wl1480 ; wl1481 ; wl1482 ; wl1483 ; wl1484 ; wl1496 ; wp0060 ; wp0067 ; wp0261 ; wp0304 ; wp1010 ; wp1011 ; wp1027 ; wp1311 ; wp1312 ; wp1313 ; wp1314 ; wp1315 ; wp1316 ; wp1317 ; wp1318 ; wp1319 ; wp1322 ; wp1333 ; wp1334 ; wp1335 ; wp1336 ; wp1337 ; wp1338 ; wp1339 ; wp1340 ; wl0155 ; wl0289 ; wl0391 ; wl0392 ; wl0468 ; wl0469 ; wl0905 ; wl1021 ; wl1546 ; wl1562 ; wl1563 ; wl1564 ; wl1565 ; wl1569 ; wl1570 ; wl1571 ; wl1586 ; wl1587 ; wl1588 ; wl1589 ; wl1590 ; wp0021 ; wp0032 ; wp0039 ; wp0082 ; wp0142 ; wp0316 ; wp0717 ; wp0718 ; wp1374 ; wp1377 ; wp1385 ; wp1386 ; wp1387 ; wp1388 ; wp1389 ; wp1390 ; wp1396 ; wp1397 ; wp1398 ; wl1597 ; wl1598 ; wl1599 ; wl1603 ; wl1609 ; wl1610 ; wl1611 ; wl1612 ; wp0001 ; wp0002 ; wp0101 ; wp0104 ; wp0110 ; wp0186 ; wp0375 ; wp0669 ; wp1399 ; wp1400 ; wp1401 ; wp1402 ; wp1403 ; wp1404 ; wp1405 ; wp1406 ; wp1407 ; wp1408 ; wp1409 ; wp1410 ; wp1413 ; wp1414 ; wp1415)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at033440 ; lem-box-tQ-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CXbc-box-at021021 ; lem-CXbc-box-at0210213443 ; lem-CXbc-box-at0214233041 ; lem-CXbc-box-at0410213243 ; lem-CXcb-box-at021021 ; lem-CXcb-box-at0210213443 ; lem-CXcb-box-at0214233041 ; lem-CXcb-box-at0410213243 ; lem-VPQ-at0213243041 ; lem-VPQ-at0214233041 ; lem-VPQ-at0310213442 ; lem-box-tQ-at02102331 ; lem-box-tQ-at02102441 ; lem-box-tQ-at02132031 ; lem-box-tQ-at02132130 ; lem-box-tQ-at02142041 ; lem-box-tQ-at0310243241 ; lem-box-tQ-at031031 ; lem-box-tQ-at03122031 ; lem-box-tQ-at03122130 ; lem-box-tQ-at0312243041 ; lem-box-tQ-at0314203241 ; lem-box-tQ-at03143041 ; lem-box-tQ-at03243042 ; lem-box-tQ-at04103143 ; lem-box-tQ-at04122041 ; lem-box-tQ-at142142 ; lem-tP-at02102331 ; lem-tP-at02102441 ; lem-tP-at02132031 ; lem-tP-at02132130 ; lem-tP-at0214203143 ; lem-tP-at02142041 ; lem-tP-at0310243241 ; lem-tP-at031031 ; lem-tP-at03122031 ; lem-tP-at03122130 ; lem-tP-at0312243041 ; lem-tP-at0314203241 ; lem-tP-at03143041 ; lem-tP-at03243042 ; lem-tP-at033440 ; lem-tP-at04103143 ; lem-tP-at04122041 ; lem-tP-at0412233041 ; lem-tP-at04233042 ; lem-tP-at142142 ; lem-tP-at2442)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-tQ-at0410233241 ; lem-box-tQ-at041041 ; lem-box-tQ-at0412233041 ; lem-box-tQ-at0413203142 ; lem-box-tQ-at0413213042 ; lem-box-tQ-at04233240 ; lem-box-tQ-at0440 ; lem-tP-at02142140 ; lem-tP-at0410233241 ; lem-tP-at0412213043 ; lem-tP-at0413203142 ; lem-tP-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-TOFF412 ; lem-comm-CSd03-TOFF412 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd12-TOFF403 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-TOFF014 ; lem-comm-CX02-CCZ134 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX21-CCZ034 ; lem-comm-CX23-CCZ014 ; lem-comm-CX31-CCZ024 ; lem-comm-CZ03-TOFF412 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ04-TOFF312 ; lem-comm-CZ14-TOFF023 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF204-CSd13 ; lem-comm-TOFF312-CSd04 ; lem-comm-TOFF412-CSd03)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS04-TOFF213 ; lem-comm-CS04-TOFF312 ; lem-comm-CS12-TOFF304 ; lem-comm-CS13-TOFF204 ; lem-comm-CS14-TOFF203 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CSd14-TOFF302 ; lem-comm-CSd23-TOFF401 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX03-CCZ124 ; lem-comm-CX30-CCZ124 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ02-TOFF314 ; lem-comm-CZ12-TOFF304 ; lem-comm-CZ12-TOFF403 ; lem-comm-CZ13-TOFF204 ; lem-comm-CZ14-TOFF302 ; lem-comm-CZ23-TOFF014 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF214-CSd03 ; lem-comm-TOFF304-CSd12 ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CK40-TOFF312 ; lem-comm-CS13-TOFF402 ; lem-comm-CS14-TOFF302 ; lem-comm-CSd02-TOFF413 ; lem-comm-CSd13-TOFF402 ; lem-comm-CX20-CCZ134 ; lem-comm-CZ13-TOFF402 ; lem-comm-TOFF402-CSd13 ; lem-comm-TOFF413-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS02-TOFF413 ; lem-comm-CS12-TOFF403 ; lem-comm-TOFF403-CSd12)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF203-CSd14 ; lem-comm-TOFF302-CSd14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-4031 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CX30 ∷ Toff204 ∷ []) (Toff204 ∷ CX30 ∷ Toff234 ∷ []) (wp1151 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ123 ∷ Toff234 ∷ CCZ134 ∷ []) (Toff234 ∷ CCZ123 ∷ []) (wl1323 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ123 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ []) (wl1324 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS14 ∷ Toff204 ∷ []) (Toff204 ∷ CS14 ∷ []) (wp1152 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CX43 ∷ Toff204 ∷ []) (Toff204 ∷ CX43 ∷ []) (wp0945 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CS13⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS13 ∷ Toff204 ∷ []) (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Toff204 ∷ Toff234 ∷ []) (Toff234 ∷ Toff204 ∷ []) (wp1153 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (CX30 ∷ Toff234 ∷ Toff234 ∷ []) (CX30 ∷ []) (wp1154 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ134 ∷ []) (CX30 ∷ CCZ134 ∷ CX30 ∷ []) (wp0759 c4)

-- CXcb-box @02142041: 18 steps
lem-CXcb-box-at02142041 : Ws → ⟪ (CX30 ∷ Bx2-4031 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at02142041 c4 = derive (CX30 ∷ Bx2-4031 ∷ CX30 ∷ []) (Bx2-4031 ∷ CCZ134 ∷ [])
  (rw 1 (q1 c4) ∷
   rw 0 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = eqn (Toff201 ∷ Toff201 ∷ []) [] (wl0421 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (lem-VPQ-at0214233041 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0341 (lit c4))

-- QVQ @0214233041: 3 steps
lem-QVQ-at0214233041 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0214233041 c4 = derive (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q15 c4) ∷
   rw 4 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx3-4021 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CX02 ∷ Toff304 ∷ []) (Toff304 ∷ CX02 ∷ []) (wp1059 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ123 ∷ CX02 ∷ CCZ013 ∷ []) (CX02 ∷ CCZ123 ∷ []) (wl1325 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ013 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp1159 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ123 ∷ []) (wl1321 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) (wl0327 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CX02 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX02 ∷ []) (wl1326 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ014 ∷ []) (CX02 ∷ CCZ014 ∷ CX02 ∷ []) (wp0378 c4)

-- CXbc-box @0314203241: 17 steps
lem-CXbc-box-at0314203241 : Ws → ⟪ (CX02 ∷ Bx3-4021 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0314203241 c4 = derive (CX02 ∷ Bx3-4021 ∷ CX02 ∷ []) (Bx3-4021 ∷ CCZ014 ∷ [])
  (rw 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw 2 (q18 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 5 (q25 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (CX20 ∷ Toff304 ∷ []) (Toff304 ∷ CX20 ∷ Toff324 ∷ []) (wp1160 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ123 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ123 ∷ []) (wl1327 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ123 ∷ CX20 ∷ []) (CX20 ∷ CCZ123 ∷ []) (wl0482 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CS14 ∷ Toff304 ∷ []) (Toff304 ∷ CS14 ∷ []) (wp1037 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CX42 ∷ Toff304 ∷ []) (Toff304 ∷ CX42 ∷ []) (wp1055 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CS12⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS12 ∷ Toff304 ∷ []) (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff304 ∷ Toff324 ∷ []) (Toff324 ∷ Toff304 ∷ []) (wp1144 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CX20 ∷ Toff324 ∷ Toff324 ∷ []) (CX20 ∷ []) (wp1161 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ124 ∷ []) (CX20 ∷ CCZ124 ∷ CX20 ∷ []) (wp0380 c4)

-- CXcb-box @0314203241: 18 steps
lem-CXcb-box-at0314203241 : Ws → ⟪ (CX20 ∷ Bx3-4021 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at0314203241 c4 = derive (CX20 ∷ Bx3-4021 ∷ CX20 ∷ []) (Bx3-4021 ∷ CCZ124 ∷ [])
  (rw 1 (q17 c4) ∷
   rw 0 (q29 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw 7 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 5 (q34 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw⁻ 3 (q37 c4) ∷
   rw 2 (q29 c4) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw⁻ 1 (q40 c4) ∷ []) Eq.refl

private
  q41 : Ws → Eqn
  q41 c4 = eqn (CX14 ∷ CX41 ∷ CX14 ∷ []) (Sw14 ∷ []) (wl0423 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CX14 ∷ Bx2-0143 ∷ CX14 ∷ []) (Bx2-0143 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210213443 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ013 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CX41 ∷ Bx2-0143 ∷ CX41 ∷ []) (Bx2-0143 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0210213443 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ []) (wp0189 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ034 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) (wp0769 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl0230 (lit c4))

-- SWbc-box @0210213443: 11 steps
lem-SWbc-box-at0210213443 : Ws → ⟪ (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-SWbc-box-at0210213443 c4 = derive (Sw14 ∷ Bx2-0143 ∷ Sw14 ∷ []) (Bx2-0143 ∷ [])
  (rw⁻ 0 (q41 c4) ∷
   rw⁻ 4 (q41 c4) ∷
   rw 2 (q42 c4) ∷
   rw 3 (q43 c4) ∷
   rw 1 (q44 c4) ∷
   rw 4 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw 0 (q42 c4) ∷
   rw 1 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = eqn (CX30 ∷ CX03 ∷ CX30 ∷ []) (Sw03 ∷ []) (wl0923 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CX30 ∷ Bx2-4301 ∷ CX30 ∷ []) (Bx2-4301 ∷ CCZ134 ∷ []) (lem-CXbc-box-at0214233041 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ134 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CX03 ∷ Bx2-4301 ∷ CX03 ∷ []) (Bx2-4301 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0214233041 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ134 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ []) (wp0705 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ014 ∷ CX30 ∷ []) (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wp0764 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0321 (lit c4))

-- SWbc-box @0214233041: 11 steps
lem-SWbc-box-at0214233041 : Ws → ⟪ (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-SWbc-box-at0214233041 c4 = derive (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (Bx2-4301 ∷ [])
  (rw⁻ 0 (q49 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 3 (q51 c4) ∷
   rw 1 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   rw 2 (q54 c4) ∷
   rw 3 (q55 c4) ∷
   rw 0 (q50 c4) ∷
   rw 1 (q56 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (Bx3-2401 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243041 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243041 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ013 ∷ []) (wl0866 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ013 ∷ CZ01 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff301 ∷ []) (wl0867 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CZ01 ∷ Toff324 ∷ []) (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI))
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ013 ∷ []) (CZ01 ∷ CCZ013 ∷ CZ01 ∷ []) (wl0868 (lit c4))

-- P-box @0312243041: 8 steps
lem-P-box-at0312243041 : Ws → ⟪ (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-P-box-at0312243041 c4 = derive (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) (Bx3-2401 ∷ [])
  (rw 1 (q57 c4) ∷
   rw⁻ 0 (q58 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 0 (q57 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx2-0431 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02102441 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ123 ∷ []) (wl0912 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ123 ∷ CZ13 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff213 ∷ []) (wl0913 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CZ13 ∷ Toff204 ∷ []) (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0914 (lit c4))

-- P-box @02102441: 8 steps
lem-P-box-at02102441 : Ws → ⟪ (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-P-box-at02102441 c4 = derive (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) (Bx2-0431 ∷ [])
  (rw 1 (q63 c4) ∷
   rw⁻ 0 (q64 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw⁻ 3 (q64 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (Bx2-3104 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02132130 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CX10 ∷ Toff213 ∷ []) (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ024 ∷ CX10 ∷ CCZ124 ∷ []) (CX10 ∷ CCZ024 ∷ []) (wp1190 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ124 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1336 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp0036 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ []) (wp0746 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp0034 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CX10 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX10 ∷ []) (wp1191 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ134 ∷ []) (CX10 ∷ CCZ134 ∷ CX10 ∷ []) (wp0505 c4)

-- CXbc-box @02132130: 17 steps
lem-CXbc-box-at02132130 : Ws → ⟪ (CX10 ∷ Bx2-3104 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at02132130 c4 = derive (CX10 ∷ Bx2-3104 ∷ CX10 ∷ []) (Bx2-3104 ∷ CCZ134 ∷ [])
  (rw 1 (q69 c4) ∷
   rw 0 (q70 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 3 (q72 c4) ∷
   rw 2 (q70 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 9 (q74 c4) ∷
   rw 8 (q75 c4) ∷
   rw⁻ 7 (q76 c4) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 5 (q77 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 1 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CX01 ∷ Toff213 ∷ []) (Toff213 ∷ CX01 ∷ Toff203 ∷ []) (wl1337 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (Toff203 ∷ CCZ024 ∷ []) (wp1192 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ024 ∷ CX01 ∷ []) (CX01 ∷ CCZ024 ∷ []) (wp0022 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (CCZ034 ∷ []) (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CX30 ∷ Toff213 ∷ []) (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CS04⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CS04 ∷ Toff213 ∷ []) (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (Toff203 ∷ Toff213 ∷ []) (Toff213 ∷ Toff203 ∷ []) (wl1338 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CX01 ∷ Toff203 ∷ Toff203 ∷ []) (CX01 ∷ []) (wl1339 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ034 ∷ []) (CX01 ∷ CCZ034 ∷ CX01 ∷ []) (wp0499 c4)

-- CXcb-box @02132130: 18 steps
lem-CXcb-box-at02132130 : Ws → ⟪ (CX01 ∷ Bx2-3104 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at02132130 c4 = derive (CX01 ∷ Bx2-3104 ∷ CX01 ∷ []) (Bx2-3104 ∷ CCZ034 ∷ [])
  (rw 1 (q69 c4) ∷
   rw 0 (q81 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 4 (q84 c4) ∷
   rw 8 (q85 c4) ∷
   rw 7 (q86 c4) ∷
   rw 6 (q87 c4) ∷
   rw 5 (q86 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   rw 3 (q89 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q90 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 1 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (Bx3-4201 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143041 c4)

-- P-box @03143041: 8 steps
lem-P-box-at03143041 : Ws → ⟪ (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-P-box-at03143041 c4 = derive (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) (Bx3-4201 ∷ [])
  (rw 1 (q93 c4) ∷
   rw⁻ 0 (q94 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw⁻ 3 (q94 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 0 (q93 c4) ∷ []) Eq.refl

private
  q95 : Ws → Eqn
  q95 c4 = eqn (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (CS01⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑))
  q98 : Ws → Eqn
  q98 c4 = eqn (CS01⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))
  q99 : Ws → Eqn
  q99 c4 = eqn (CS01⁻ ∷ S3 ∷ []) (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑))
  q100 : Ws → Eqn
  q100 c4 = eqn (CS01⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q101 : Ws → Eqn
  q101 c4 = eqn (S3⁻ ∷ S3 ∷ []) [] (wl0441 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CS24⁻ ∷ S3 ∷ []) (S3 ∷ CS24⁻ ∷ []) (wl0440 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CS24⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (CS24⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS24⁻ ∷ []) (wl0439 (lit c4))

-- VPQ @03143041: 14 steps
lem-VPQ-at03143041 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at03143041 c4 = derive (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q95 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw⁻ 3 (q97 c4) ∷
   rw⁻ 2 (q98 c4) ∷
   rw⁻ 1 (q99 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q94 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q102 c4) ∷
   rw 2 (q103 c4) ∷
   rw 3 (q104 c4) ∷
   rw 0 (q96 c4) ∷
   rw 2 (q95 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CS14⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS14⁻ ∷ []) (wl0634 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (Toff203 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (CS14⁻ ∷ S2 ∷ []) (S2 ∷ CS14⁻ ∷ []) (wl0633 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CS03⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS03⁻ ∷ []) (wp0514 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (S2⁻ ∷ S2 ∷ []) [] (wl0179 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02132031 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (CS03⁻ ∷ S2 ∷ []) (S2 ∷ CS03⁻ ∷ []) (wl0632 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (CS03⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CS03⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS03⁻ ∷ []) (wl0631 (lit c4))

-- VPQ @02132031: 14 steps
lem-VPQ-at02132031 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at02132031 c4 = derive (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q105 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw⁻ 1 (q109 c4) ∷
   rw 0 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q112 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw 0 (q106 c4) ∷
   rw 2 (q105 c4) ∷ []) Eq.refl

private
  q116 : Ws → Eqn
  q116 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl0442 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (lem-VPQ-at0310213442 c4)
  q118 : Ws → Eqn
  q118 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl0305 (lit c4))

-- QVQ @0310213442: 3 steps
lem-QVQ-at0310213442 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at0310213442 c4 = derive (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  (rw⁻ 0 (q116 c4) ∷
   rw⁻ 1 (q117 c4) ∷
   rw 4 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = eqn (Bx2-3014 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02132031 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (CX01 ∷ Toff203 ∷ []) (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (CX01 ∷ CCZ124 ∷ []) (wp1196 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1197 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CCZ124 ∷ CS34 ∷ []) (CS34 ∷ CCZ124 ∷ []) (wl0471 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CX30 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ124 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ124 ∷ []) (wp0318 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ124 ∷ CS04 ∷ []) (CS04 ∷ CCZ124 ∷ []) (wp0384 c4)
  q127 : Ws → Eqn
  q127 c4 = eqn (CX01 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX01 ∷ []) (wp1198 c4)

-- CXbc-box @02132031: 17 steps
lem-CXbc-box-at02132031 : Ws → ⟪ (CX01 ∷ Bx2-3014 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at02132031 c4 = derive (CX01 ∷ Bx2-3014 ∷ CX01 ∷ []) (Bx2-3014 ∷ CCZ034 ∷ [])
  (rw 1 (q119 c4) ∷
   rw 0 (q120 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 3 (q122 c4) ∷
   rw 2 (q120 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 9 (q123 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 7 (q125 c4) ∷
   rw 6 (q124 c4) ∷
   rw⁻ 5 (q126 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 3 (q121 c4) ∷
   rw 4 (q127 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw⁻ 1 (q92 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = eqn (CX10 ∷ Toff203 ∷ []) (Toff203 ∷ CX10 ∷ Toff213 ∷ []) (wl1349 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (Toff213 ∷ CCZ124 ∷ []) (wl1350 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CCZ124 ∷ CX10 ∷ []) (CX10 ∷ CCZ124 ∷ []) (wp0672 c4)
  q131 : Ws → Eqn
  q131 c4 = eqn (CS34 ∷ Toff203 ∷ []) (Toff203 ∷ CS34 ∷ []) (wp1199 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CX31 ∷ Toff203 ∷ []) (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (CS14⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (CS14 ∷ Toff203 ∷ []) (Toff203 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF203 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (CX10 ∷ Toff213 ∷ Toff213 ∷ []) (CX10 ∷ []) (wl1352 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4))

-- CXcb-box @02132031: 18 steps
lem-CXcb-box-at02132031 : Ws → ⟪ (CX10 ∷ Bx2-3014 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at02132031 c4 = derive (CX10 ∷ Bx2-3014 ∷ CX10 ∷ []) (Bx2-3014 ∷ CCZ134 ∷ [])
  (rw 1 (q119 c4) ∷
   rw 0 (q128 c4) ∷
   rw⁻ 2 (q129 c4) ∷
   rw⁻ 1 (q130 c4) ∷
   rw 4 (q73 c4) ∷
   rw 8 (q131 c4) ∷
   rw 7 (q132 c4) ∷
   rw 6 (q133 c4) ∷
   rw 5 (q132 c4) ∷
   rw 4 (q134 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw 2 (q128 c4) ∷
   rw 3 (q135 c4) ∷
   rw⁻ 4 (q136 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw⁻ 1 (q80 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = eqn (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02132130 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp0780 c4)
  q139 : Ws → Eqn
  q139 c4 = eqn (CCZ024 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff204 ∷ []) (wp0781 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (CZ04 ∷ Toff213 ∷ []) (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ024 ∷ []) (CZ04 ∷ CCZ024 ∷ CZ04 ∷ []) (wp0782 c4)

-- P-box @02132130: 8 steps
lem-P-box-at02132130 : Ws → ⟪ (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-P-box-at02132130 c4 = derive (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) (Bx2-3104 ∷ [])
  (rw 1 (q69 c4) ∷
   rw⁻ 0 (q137 c4) ∷
   rw⁻ 1 (q138 c4) ∷
   rw⁻ 3 (q137 c4) ∷
   rw⁻ 4 (q139 c4) ∷
   rw 2 (q140 c4) ∷
   rw⁻ 3 (q141 c4) ∷
   rw⁻ 0 (q69 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = eqn (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (CS04⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Toff213 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4))
  q146 : Ws → Eqn
  q146 c4 = eqn (CS04⁻ ∷ S2 ∷ []) (S2 ∷ CS04⁻ ∷ []) (wp0017 c4)
  q147 : Ws → Eqn
  q147 c4 = eqn (CS04⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (CS13⁻ ∷ S2 ∷ []) (S2 ∷ CS13⁻ ∷ []) (wl0178 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS13⁻ ∷ []) (wl0177 (lit c4))

-- VPQ @02132130: 14 steps
lem-VPQ-at02132130 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at02132130 c4 = derive (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q142 c4) ∷
   rw⁻ 4 (q143 c4) ∷
   rw⁻ 3 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw⁻ 1 (q146 c4) ∷
   rw⁻ 0 (q147 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q137 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q148 c4) ∷
   rw 2 (q8 c4) ∷
   rw 3 (q149 c4) ∷
   rw 0 (q143 c4) ∷
   rw 2 (q142 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = eqn (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (lem-VPQ-at0213243041 c4)

-- QVQ @0213243041: 3 steps
lem-QVQ-at0213243041 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0213243041 c4 = derive (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  (rw⁻ 0 (q14 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   rw 4 (q16 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = eqn (Bx3-0421 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243241 c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ []) (wl0504 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ123 ∷ CZ12 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff312 ∷ []) (wl0505 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (CZ12 ∷ Toff304 ∷ []) (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ CZ12 ∷ []) (wl0506 (lit c4))

-- P-box @0310243241: 8 steps
lem-P-box-at0310243241 : Ws → ⟪ (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-P-box-at0310243241 c4 = derive (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) (Bx3-0421 ∷ [])
  (rw 1 (q151 c4) ∷
   rw⁻ 0 (q152 c4) ∷
   rw⁻ 1 (q153 c4) ∷
   rw⁻ 3 (q152 c4) ∷
   rw⁻ 4 (q154 c4) ∷
   rw 2 (q155 c4) ∷
   rw⁻ 3 (q156 c4) ∷
   rw⁻ 0 (q151 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = eqn (Bx3-2104 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at03122130 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (CX10 ∷ Toff312 ∷ []) (Toff312 ∷ CX10 ∷ []) (wl0537 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (CX10 ∷ CCZ034 ∷ []) (wp0225 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CCZ134 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1356 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp0108 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (CX21 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (CCZ034 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ034 ∷ []) (wp0123 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ034 ∷ CS14 ∷ []) (CS14 ∷ CCZ034 ∷ []) (wp0106 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (CX10 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX10 ∷ []) (wp0226 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (CCZ124 ∷ []) (CX10 ∷ CCZ124 ∷ CX10 ∷ []) (wp0663 c4)

-- CXbc-box @03122130: 17 steps
lem-CXbc-box-at03122130 : Ws → ⟪ (CX10 ∷ Bx3-2104 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at03122130 c4 = derive (CX10 ∷ Bx3-2104 ∷ CX10 ∷ []) (Bx3-2104 ∷ CCZ124 ∷ [])
  (rw 1 (q157 c4) ∷
   rw 0 (q158 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 3 (q160 c4) ∷
   rw 2 (q158 c4) ∷
   rw 5 (q161 c4) ∷
   rw⁻ 9 (q162 c4) ∷
   rw 8 (q163 c4) ∷
   rw⁻ 7 (q164 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   rw⁻ 6 (q161 c4) ∷
   rw⁻ 4 (q166 c4) ∷
   rw⁻ 3 (q159 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw⁻ 1 (q168 c4) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = eqn (CX01 ∷ Toff312 ∷ []) (Toff312 ∷ CX01 ∷ Toff302 ∷ []) (wl1357 (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (Toff302 ∷ CCZ034 ∷ []) (wp1202 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) (wp0221 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (CCZ024 ∷ []) (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CS24 ∷ Toff312 ∷ []) (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (CX20 ∷ Toff312 ∷ []) (Toff312 ∷ CX20 ∷ []) (wl0534 (lit c4))
  q175 : Ws → Eqn
  q175 c4 = eqn (CS04⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4))
  q176 : Ws → Eqn
  q176 c4 = eqn (CS04 ∷ Toff312 ∷ []) (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4))
  q177 : Ws → Eqn
  q177 c4 = eqn (Toff302 ∷ Toff312 ∷ []) (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4))
  q178 : Ws → Eqn
  q178 c4 = eqn (CX01 ∷ Toff302 ∷ Toff302 ∷ []) (CX01 ∷ []) (wl1359 (lit c4))
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ024 ∷ []) (CX01 ∷ CCZ024 ∷ CX01 ∷ []) (wp0670 c4)

-- CXcb-box @03122130: 18 steps
lem-CXcb-box-at03122130 : Ws → ⟪ (CX01 ∷ Bx3-2104 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at03122130 c4 = derive (CX01 ∷ Bx3-2104 ∷ CX01 ∷ []) (Bx3-2104 ∷ CCZ024 ∷ [])
  (rw 1 (q157 c4) ∷
   rw 0 (q169 c4) ∷
   rw⁻ 2 (q170 c4) ∷
   rw⁻ 1 (q171 c4) ∷
   rw 4 (q172 c4) ∷
   rw 8 (q173 c4) ∷
   rw 7 (q174 c4) ∷
   rw 6 (q175 c4) ∷
   rw 5 (q174 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 5 (q172 c4) ∷
   rw 3 (q177 c4) ∷
   rw 2 (q169 c4) ∷
   rw 3 (q178 c4) ∷
   rw 4 (q91 c4) ∷
   rw⁻ 3 (q171 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw⁻ 1 (q179 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CS14⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS14⁻ ∷ []) (wl0786 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (Toff302 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CS14⁻ ∷ S3 ∷ []) (S3 ∷ CS14⁻ ∷ []) (wl0785 (lit c4))
  q185 : Ws → Eqn
  q185 c4 = eqn (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4)
  q186 : Ws → Eqn
  q186 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03122031 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (CS02⁻ ∷ S3 ∷ []) (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))
  q188 : Ws → Eqn
  q188 c4 = eqn (CS02⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (CS02⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))

-- VPQ @03122031: 14 steps
lem-VPQ-at03122031 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at03122031 c4 = derive (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q180 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw⁻ 3 (q182 c4) ∷
   rw 2 (q183 c4) ∷
   rw⁻ 1 (q184 c4) ∷
   rw 0 (q185 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q186 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q187 c4) ∷
   rw 2 (q188 c4) ∷
   rw 3 (q189 c4) ∷
   rw 0 (q181 c4) ∷
   rw 2 (q180 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = eqn (Bx3-2014 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03122031 c4)
  q191 : Ws → Eqn
  q191 c4 = eqn (CX01 ∷ Toff302 ∷ []) (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CCZ134 ∷ CX01 ∷ CCZ034 ∷ []) (CX01 ∷ CCZ134 ∷ []) (wp1204 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1205 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4))
  q195 : Ws → Eqn
  q195 c4 = eqn (CX20 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4))
  q196 : Ws → Eqn
  q196 c4 = eqn (CCZ134 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ134 ∷ []) (wp1206 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp1003 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (CX01 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX01 ∷ []) (wp1207 c4)

-- CXbc-box @03122031: 17 steps
lem-CXbc-box-at03122031 : Ws → ⟪ (CX01 ∷ Bx3-2014 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at03122031 c4 = derive (CX01 ∷ Bx3-2014 ∷ CX01 ∷ []) (Bx3-2014 ∷ CCZ024 ∷ [])
  (rw 1 (q190 c4) ∷
   rw 0 (q191 c4) ∷
   rw⁻ 1 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw 2 (q191 c4) ∷
   rw 5 (q172 c4) ∷
   rw⁻ 9 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw⁻ 7 (q196 c4) ∷
   rw 6 (q195 c4) ∷
   rw⁻ 5 (q197 c4) ∷
   rw⁻ 6 (q172 c4) ∷
   rw 4 (q166 c4) ∷
   rw⁻ 3 (q192 c4) ∷
   rw 4 (q198 c4) ∷
   rw⁻ 0 (q190 c4) ∷
   rw⁻ 1 (q179 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (CX10 ∷ Toff302 ∷ []) (Toff302 ∷ CX10 ∷ Toff312 ∷ []) (wl1367 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (Toff312 ∷ CCZ134 ∷ []) (wl1368 (lit c4))
  q201 : Ws → Eqn
  q201 c4 = eqn (CCZ134 ∷ CX10 ∷ []) (CX10 ∷ CCZ134 ∷ []) (wp0712 c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp1006 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (CX21 ∷ Toff302 ∷ []) (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4))
  q204 : Ws → Eqn
  q204 c4 = eqn (CS14⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4))
  q205 : Ws → Eqn
  q205 c4 = eqn (CS14 ∷ Toff302 ∷ []) (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (CX10 ∷ Toff312 ∷ Toff312 ∷ []) (CX10 ∷ []) (wl1369 (lit c4))

-- CXcb-box @03122031: 18 steps
lem-CXcb-box-at03122031 : Ws → ⟪ (CX10 ∷ Bx3-2014 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at03122031 c4 = derive (CX10 ∷ Bx3-2014 ∷ CX10 ∷ []) (Bx3-2014 ∷ CCZ124 ∷ [])
  (rw 1 (q190 c4) ∷
   rw 0 (q199 c4) ∷
   rw⁻ 2 (q200 c4) ∷
   rw⁻ 1 (q201 c4) ∷
   rw 4 (q161 c4) ∷
   rw 8 (q202 c4) ∷
   rw 7 (q203 c4) ∷
   rw 6 (q204 c4) ∷
   rw 5 (q203 c4) ∷
   rw 4 (q205 c4) ∷
   rw⁻ 5 (q161 c4) ∷
   rw⁻ 3 (q177 c4) ∷
   rw 2 (q199 c4) ∷
   rw 3 (q206 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 3 (q201 c4) ∷
   rw⁻ 0 (q190 c4) ∷
   rw⁻ 1 (q168 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = eqn (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ []) (lem-tP-at03122130 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ []) (wp0344 c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (CCZ034 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff304 ∷ []) (wp0345 c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (CZ04 ∷ Toff312 ∷ []) (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4))
  q211 : Ws → Eqn
  q211 c4 = eqn (CCZ034 ∷ []) (CZ04 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0346 c4)

-- P-box @03122130: 8 steps
lem-P-box-at03122130 : Ws → ⟪ (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-P-box-at03122130 c4 = derive (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) (Bx3-2104 ∷ [])
  (rw 1 (q157 c4) ∷
   rw⁻ 0 (q207 c4) ∷
   rw⁻ 1 (q208 c4) ∷
   rw⁻ 3 (q207 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw⁻ 3 (q211 c4) ∷
   rw⁻ 0 (q157 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = eqn (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4))
  q213 : Ws → Eqn
  q213 c4 = eqn (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (CS04⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS04⁻ ∷ []) (wp0348 c4)
  q215 : Ws → Eqn
  q215 c4 = eqn (Toff312 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff312 ∷ []) (lem-comm-TOFF312-CSd04 (lit c4))
  q216 : Ws → Eqn
  q216 c4 = eqn (CS04⁻ ∷ S3 ∷ []) (S3 ∷ CS04⁻ ∷ []) (wp0349 c4)
  q217 : Ws → Eqn
  q217 c4 = eqn (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ []) (wp0350 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (CS12⁻ ∷ S3 ∷ []) (S3 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S))
  q219 : Ws → Eqn
  q219 c4 = eqn (CS12⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S • S • S))

-- VPQ @03122130: 14 steps
lem-VPQ-at03122130 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at03122130 c4 = derive (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q212 c4) ∷
   rw⁻ 4 (q213 c4) ∷
   rw⁻ 3 (q214 c4) ∷
   rw 2 (q215 c4) ∷
   rw⁻ 1 (q216 c4) ∷
   rw⁻ 0 (q217 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q207 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q218 c4) ∷
   rw 2 (q35 c4) ∷
   rw 3 (q219 c4) ∷
   rw 0 (q213 c4) ∷
   rw 2 (q212 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (Toff204 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4))
  q221 : Ws → Eqn
  q221 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4)

-- VPQ @02142041: 14 steps
lem-VPQ-at02142041 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at02142041 c4 = derive (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q143 c4) ∷
   rw⁻ 4 (q142 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw 2 (q220 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   rw 0 (q147 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q221 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q146 c4) ∷
   rw 2 (q87 c4) ∷
   rw 3 (q144 c4) ∷
   rw 0 (q142 c4) ∷
   rw 2 (q143 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = eqn (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp0027 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (CCZ024 ∷ Toff204 ∷ []) (Toff204 ∷ CZ04 ∷ CCZ024 ∷ []) (wp0028 c4)

-- t-cP @02142041: 5 steps
lem-t-cP-at02142041 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-t-cP-at02142041 c4 = derive (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q222 c4) ∷
   rw 2 (q140 c4) ∷
   rw 1 (q221 c4) ∷
   rw⁻ 2 (q223 c4) ∷
   rw 3 (q221 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (Toff304 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4))
  q225 : Ws → Eqn
  q225 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4)

-- VPQ @0314203241: 14 steps
lem-VPQ-at0314203241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0314203241 c4 = derive (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q213 c4) ∷
   rw⁻ 4 (q212 c4) ∷
   rw⁻ 3 (q219 c4) ∷
   rw 2 (q224 c4) ∷
   rw⁻ 1 (q218 c4) ∷
   rw 0 (q217 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q225 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q216 c4) ∷
   rw 2 (q175 c4) ∷
   rw 3 (q214 c4) ∷
   rw 0 (q212 c4) ∷
   rw 2 (q213 c4) ∷ []) Eq.refl

private
  q226 : Ws → Eqn
  q226 c4 = eqn (CCZ034 ∷ Toff304 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ []) (wp1033 c4)
  q227 : Ws → Eqn
  q227 c4 = eqn (CCZ034 ∷ Toff304 ∷ []) (Toff304 ∷ CZ04 ∷ CCZ034 ∷ []) (wp1034 c4)

-- t-cP @0314203241: 5 steps
lem-t-cP-at0314203241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-t-cP-at0314203241 c4 = derive (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q226 c4) ∷
   rw 2 (q210 c4) ∷
   rw 1 (q225 c4) ∷
   rw⁻ 2 (q227 c4) ∷
   rw 3 (q225 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = eqn (Bx3-1240 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4)
  q229 : Ws → Eqn
  q229 c4 = eqn (CK40 ∷ Toff312 ∷ []) (Toff312 ∷ CK40 ∷ []) (lem-comm-CK40-TOFF312 (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (CK40 ∷ CCZ034 ∷ []) (Toff034 ∷ CK40 ∷ []) (wp1216 c4)
  q231 : Ws → Eqn
  q231 c4 = eqn (CK40 ∷ CK40⁻ ∷ []) [] (wp1217 c4)

-- CK-box @033440: 6 steps
lem-CK-box-at033440 : Ws → ⟪ (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ []) ⟫ʷ
lem-CK-box-at033440 c4 = derive (CK40 ∷ Bx3-1240 ∷ CK40⁻ ∷ []) (Toff312 ∷ Toff034 ∷ Toff312 ∷ Toff034 ∷ [])
  (rw 1 (q228 c4) ∷
   rw 0 (q229 c4) ∷
   rw 1 (q230 c4) ∷
   rw 2 (q229 c4) ∷
   rw 3 (q230 c4) ∷
   rw 4 (q231 c4) ∷ []) Eq.refl

private
  q232 : Ws → Eqn
  q232 c4 = eqn (CX13 ∷ CX31 ∷ CX13 ∷ []) (Sw13 ∷ []) (wl0278 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (CX13 ∷ Bx2-0134 ∷ CX13 ∷ []) (Bx2-0134 ∷ CCZ014 ∷ []) (lem-CXbc-box-at021021 c4)
  q234 : Ws → Eqn
  q234 c4 = eqn (CCZ014 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1229 c4)
  q235 : Ws → Eqn
  q235 c4 = eqn (CX31 ∷ Bx2-0134 ∷ CX31 ∷ []) (Bx2-0134 ∷ CCZ034 ∷ []) (lem-CXcb-box-at021021 c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (CCZ014 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ []) (wp0795 c4)
  q237 : Ws → Eqn
  q237 c4 = eqn (CCZ034 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp1230 c4)
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ CCZ034 ∷ CCZ014 ∷ []) (CCZ014 ∷ []) (wp1231 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0161 c4)

-- SWbc-box @021021: 11 steps
lem-SWbc-box-at021021 : Ws → ⟪ (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-SWbc-box-at021021 c4 = derive (Sw13 ∷ Bx2-0134 ∷ Sw13 ∷ []) (Bx2-0134 ∷ [])
  (rw⁻ 0 (q232 c4) ∷
   rw⁻ 4 (q232 c4) ∷
   rw 2 (q233 c4) ∷
   rw 3 (q234 c4) ∷
   rw 1 (q235 c4) ∷
   rw 4 (q236 c4) ∷
   rw 3 (q237 c4) ∷
   rw 2 (q237 c4) ∷
   rw 3 (q238 c4) ∷
   rw 0 (q233 c4) ∷
   rw 1 (q239 c4) ∷ []) Eq.refl

private
  q240 : Ws → Eqn
  q240 c4 = eqn (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02102331 c4)

-- VPQ @02102331: 14 steps
lem-VPQ-at02102331 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at02102331 c4 = derive (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q105 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw 2 (q108 c4) ∷
   rw⁻ 1 (q109 c4) ∷
   rw 0 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q240 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q113 c4) ∷
   rw 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw 0 (q106 c4) ∷
   rw 2 (q105 c4) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = eqn (Bx3-0214 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4)
  q242 : Ws → Eqn
  q242 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at031031 c4)
  q243 : Ws → Eqn
  q243 c4 = eqn (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ134 ∷ []) (wl1253 (lit c4))
  q244 : Ws → Eqn
  q244 c4 = eqn (CCZ134 ∷ CZ14 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff314 ∷ []) (wl1254 (lit c4))
  q245 : Ws → Eqn
  q245 c4 = eqn (CZ14 ∷ Toff302 ∷ []) (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4))
  q246 : Ws → Eqn
  q246 c4 = eqn (CCZ134 ∷ []) (CZ14 ∷ CCZ134 ∷ CZ14 ∷ []) (wl1255 (lit c4))

-- P-box @031031: 8 steps
lem-P-box-at031031 : Ws → ⟪ (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-P-box-at031031 c4 = derive (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) (Bx3-0214 ∷ [])
  (rw 1 (q241 c4) ∷
   rw⁻ 0 (q242 c4) ∷
   rw⁻ 1 (q243 c4) ∷
   rw⁻ 3 (q242 c4) ∷
   rw⁻ 4 (q244 c4) ∷
   rw 2 (q245 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw⁻ 0 (q241 c4) ∷ []) Eq.refl

private
  q247 : Ws → Eqn
  q247 c4 = eqn (Bx0-4132 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4)
  q248 : Ws → Eqn
  q248 c4 = eqn (CX13 ∷ Toff014 ∷ []) (Toff014 ∷ CX13 ∷ []) (wp0963 c4)
  q249 : Ws → Eqn
  q249 c4 = eqn (CCZ023 ∷ CX13 ∷ CCZ012 ∷ []) (CX13 ∷ CCZ023 ∷ []) (wl1393 (lit c4))
  q250 : Ws → Eqn
  q250 c4 = eqn (CCZ012 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1233 c4)
  q251 : Ws → Eqn
  q251 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4))
  q252 : Ws → Eqn
  q252 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp0513 c4)
  q253 : Ws → Eqn
  q253 c4 = eqn (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4))
  q254 : Ws → Eqn
  q254 c4 = eqn (CCZ023 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ023 ∷ []) (wl0620 (lit c4))
  q255 : Ws → Eqn
  q255 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4))
  q256 : Ws → Eqn
  q256 c4 = eqn (CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4))
  q257 : Ws → Eqn
  q257 c4 = eqn (CX13 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX13 ∷ []) (wl1394 (lit c4))
  q258 : Ws → Eqn
  q258 c4 = eqn (CCZ124 ∷ []) (CX13 ∷ CCZ124 ∷ CX13 ∷ []) (wl0272 (lit c4))

-- CXbc-box @142142: 17 steps
lem-CXbc-box-at142142 : Ws → ⟪ (CX13 ∷ Bx0-4132 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at142142 c4 = derive (CX13 ∷ Bx0-4132 ∷ CX13 ∷ []) (Bx0-4132 ∷ CCZ124 ∷ [])
  (rw 1 (q247 c4) ∷
   rw 0 (q248 c4) ∷
   rw⁻ 1 (q249 c4) ∷
   rw 3 (q250 c4) ∷
   rw 2 (q248 c4) ∷
   rw 5 (q251 c4) ∷
   rw⁻ 9 (q252 c4) ∷
   rw 8 (q253 c4) ∷
   rw⁻ 7 (q254 c4) ∷
   rw 6 (q253 c4) ∷
   rw⁻ 5 (q255 c4) ∷
   rw⁻ 6 (q251 c4) ∷
   rw 4 (q256 c4) ∷
   rw⁻ 3 (q249 c4) ∷
   rw 4 (q257 c4) ∷
   rw⁻ 0 (q247 c4) ∷
   rw⁻ 1 (q258 c4) ∷ []) Eq.refl

private
  q259 : Ws → Eqn
  q259 c4 = eqn (CX31 ∷ Toff014 ∷ []) (Toff014 ∷ CX31 ∷ Toff034 ∷ []) (wp1234 c4)
  q260 : Ws → Eqn
  q260 c4 = eqn (CCZ023 ∷ Toff034 ∷ CCZ234 ∷ []) (Toff034 ∷ CCZ023 ∷ []) (wp1235 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (CCZ023 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ []) (wl1343 (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX43 ∷ CS23⁻ ∷ CX43 ∷ CS24 ∷ []) (wl0330 (lit c4))
  q263 : Ws → Eqn
  q263 c4 = eqn (CS24 ∷ Toff014 ∷ []) (Toff014 ∷ CS24 ∷ []) (wp0817 c4)
  q264 : Ws → Eqn
  q264 c4 = eqn (CX43 ∷ Toff014 ∷ []) (Toff014 ∷ CX43 ∷ []) (wp0960 c4)
  q265 : Ws → Eqn
  q265 c4 = eqn (CS23⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4))
  q266 : Ws → Eqn
  q266 c4 = eqn (CS23 ∷ Toff014 ∷ []) (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4))
  q267 : Ws → Eqn
  q267 c4 = eqn (Toff014 ∷ Toff034 ∷ []) (Toff034 ∷ Toff014 ∷ []) (wp0203 c4)
  q268 : Ws → Eqn
  q268 c4 = eqn (CX31 ∷ Toff034 ∷ Toff034 ∷ []) (CX31 ∷ []) (wp1236 c4)
  q269 : Ws → Eqn
  q269 c4 = eqn (CCZ023 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ023 ∷ []) (wp0550 c4)
  q270 : Ws → Eqn
  q270 c4 = eqn (CCZ234 ∷ []) (CX31 ∷ CCZ234 ∷ CX31 ∷ []) (wl0277 (lit c4))

-- CXcb-box @142142: 18 steps
lem-CXcb-box-at142142 : Ws → ⟪ (CX31 ∷ Bx0-4132 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at142142 c4 = derive (CX31 ∷ Bx0-4132 ∷ CX31 ∷ []) (Bx0-4132 ∷ CCZ234 ∷ [])
  (rw 1 (q247 c4) ∷
   rw 0 (q259 c4) ∷
   rw⁻ 2 (q260 c4) ∷
   rw⁻ 1 (q261 c4) ∷
   rw 4 (q262 c4) ∷
   rw 8 (q263 c4) ∷
   rw 7 (q264 c4) ∷
   rw 6 (q265 c4) ∷
   rw 5 (q264 c4) ∷
   rw 4 (q266 c4) ∷
   rw⁻ 5 (q262 c4) ∷
   rw⁻ 3 (q267 c4) ∷
   rw 2 (q259 c4) ∷
   rw 3 (q268 c4) ∷
   rw⁻ 4 (q269 c4) ∷
   rw⁻ 3 (q261 c4) ∷
   rw⁻ 0 (q247 c4) ∷
   rw⁻ 1 (q270 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = eqn (Bx3-1402 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243042 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243042 c4)
  q273 : Ws → Eqn
  q273 c4 = eqn (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ023 ∷ []) (wl1235 (lit c4))
  q274 : Ws → Eqn
  q274 c4 = eqn (CCZ023 ∷ CZ02 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff302 ∷ []) (wl1236 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (CZ02 ∷ Toff314 ∷ []) (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4))
  q276 : Ws → Eqn
  q276 c4 = eqn (CCZ023 ∷ []) (CZ02 ∷ CCZ023 ∷ CZ02 ∷ []) (wl0774 (lit c4))

-- P-box @03243042: 8 steps
lem-P-box-at03243042 : Ws → ⟪ (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-P-box-at03243042 c4 = derive (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) (Bx3-1402 ∷ [])
  (rw 1 (q271 c4) ∷
   rw⁻ 0 (q272 c4) ∷
   rw⁻ 1 (q273 c4) ∷
   rw⁻ 3 (q272 c4) ∷
   rw⁻ 4 (q274 c4) ∷
   rw 2 (q275 c4) ∷
   rw⁻ 3 (q276 c4) ∷
   rw⁻ 0 (q271 c4) ∷ []) Eq.refl

private
  q277 : Ws → Eqn
  q277 c4 = eqn (Toff314 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4))

-- VPQ @03243042: 14 steps
lem-VPQ-at03243042 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at03243042 c4 = derive (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q181 c4) ∷
   rw⁻ 4 (q180 c4) ∷
   rw⁻ 3 (q189 c4) ∷
   rw 2 (q277 c4) ∷
   rw⁻ 1 (q187 c4) ∷
   rw⁻ 0 (q185 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q272 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 1 (q184 c4) ∷
   rw 2 (q204 c4) ∷
   rw 3 (q182 c4) ∷
   rw 0 (q180 c4) ∷
   rw 2 (q181 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = eqn (Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at2442 c4)
  q279 : Ws → Eqn
  q279 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at2442 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (CCZ023 ∷ CZ23 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ023 ∷ []) (wl0825 (lit c4))
  q281 : Ws → Eqn
  q281 c4 = eqn (CCZ023 ∷ CZ23 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff023 ∷ []) (wl0826 (lit c4))
  q282 : Ws → Eqn
  q282 c4 = eqn (CZ23 ∷ Toff014 ∷ []) (Toff014 ∷ CZ23 ∷ []) (lem-comm-CZ23-TOFF014 (lit c4))
  q283 : Ws → Eqn
  q283 c4 = eqn (CCZ023 ∷ []) (CZ23 ∷ CCZ023 ∷ CZ23 ∷ []) (wl0827 (lit c4))

-- P-box @2442: 8 steps
lem-P-box-at2442 : Ws → ⟪ (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-P-box-at2442 c4 = derive (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) (Bx0-1432 ∷ [])
  (rw 1 (q278 c4) ∷
   rw⁻ 0 (q279 c4) ∷
   rw⁻ 1 (q280 c4) ∷
   rw⁻ 3 (q279 c4) ∷
   rw⁻ 4 (q281 c4) ∷
   rw 2 (q282 c4) ∷
   rw⁻ 3 (q283 c4) ∷
   rw⁻ 0 (q278 c4) ∷ []) Eq.refl

private
  q284 : Ws → Eqn
  q284 c4 = eqn (Bx2-0314 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02102331 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (CCZ124 ∷ CX31 ∷ CCZ234 ∷ []) (CX31 ∷ CCZ124 ∷ []) (wl1398 (lit c4))
  q286 : Ws → Eqn
  q286 c4 = eqn (CCZ234 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1249 c4)
  q287 : Ws → Eqn
  q287 c4 = eqn (CCZ034 ∷ []) (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4)
  q288 : Ws → Eqn
  q288 c4 = eqn (CX03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4))
  q289 : Ws → Eqn
  q289 c4 = eqn (CCZ124 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ124 ∷ []) (wl1399 (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (CCZ124 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ124 ∷ []) (wl0527 (lit c4))
  q291 : Ws → Eqn
  q291 c4 = eqn (CX31 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX31 ∷ []) (wl1400 (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (CCZ034 ∷ []) (CX31 ∷ CCZ034 ∷ CX31 ∷ []) (wp1228 c4)

-- CXbc-box @02102331: 17 steps
lem-CXbc-box-at02102331 : Ws → ⟪ (CX31 ∷ Bx2-0314 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at02102331 c4 = derive (CX31 ∷ Bx2-0314 ∷ CX31 ∷ []) (Bx2-0314 ∷ CCZ034 ∷ [])
  (rw 1 (q284 c4) ∷
   rw 0 (q132 c4) ∷
   rw⁻ 1 (q285 c4) ∷
   rw 3 (q286 c4) ∷
   rw 2 (q132 c4) ∷
   rw 5 (q287 c4) ∷
   rw⁻ 9 (q126 c4) ∷
   rw 8 (q288 c4) ∷
   rw⁻ 7 (q289 c4) ∷
   rw 6 (q288 c4) ∷
   rw⁻ 5 (q123 c4) ∷
   rw⁻ 6 (q287 c4) ∷
   rw⁻ 4 (q290 c4) ∷
   rw⁻ 3 (q285 c4) ∷
   rw 4 (q291 c4) ∷
   rw⁻ 0 (q284 c4) ∷
   rw⁻ 1 (q292 c4) ∷ []) Eq.refl

private
  q293 : Ws → Eqn
  q293 c4 = eqn (CX13 ∷ Toff203 ∷ []) (Toff203 ∷ CX13 ∷ Toff201 ∷ []) (wl1401 (lit c4))
  q294 : Ws → Eqn
  q294 c4 = eqn (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ124 ∷ []) (wp1250 c4)
  q295 : Ws → Eqn
  q295 c4 = eqn (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) (wl0280 (lit c4))
  q296 : Ws → Eqn
  q296 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4)
  q297 : Ws → Eqn
  q297 c4 = eqn (CS04 ∷ Toff203 ∷ []) (Toff203 ∷ CS04 ∷ []) (wp1251 c4)
  q298 : Ws → Eqn
  q298 c4 = eqn (Toff201 ∷ Toff203 ∷ []) (Toff203 ∷ Toff201 ∷ []) (wl1391 (lit c4))
  q299 : Ws → Eqn
  q299 c4 = eqn (CX13 ∷ Toff201 ∷ Toff201 ∷ []) (CX13 ∷ []) (wl1402 (lit c4))
  q300 : Ws → Eqn
  q300 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (CCZ014 ∷ []) (CX13 ∷ CCZ014 ∷ CX13 ∷ []) (wp1226 c4)

-- CXcb-box @02102331: 18 steps
lem-CXcb-box-at02102331 : Ws → ⟪ (CX13 ∷ Bx2-0314 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at02102331 c4 = derive (CX13 ∷ Bx2-0314 ∷ CX13 ∷ []) (Bx2-0314 ∷ CCZ014 ∷ [])
  (rw 1 (q284 c4) ∷
   rw 0 (q293 c4) ∷
   rw⁻ 2 (q294 c4) ∷
   rw⁻ 1 (q295 c4) ∷
   rw 4 (q296 c4) ∷
   rw 8 (q297 c4) ∷
   rw 7 (q120 c4) ∷
   rw 6 (q133 c4) ∷
   rw 5 (q120 c4) ∷
   rw 4 (q134 c4) ∷
   rw⁻ 5 (q296 c4) ∷
   rw 3 (q298 c4) ∷
   rw 2 (q293 c4) ∷
   rw 3 (q299 c4) ∷
   rw 4 (q300 c4) ∷
   rw⁻ 3 (q295 c4) ∷
   rw⁻ 0 (q284 c4) ∷
   rw⁻ 1 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = eqn (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4)
  q303 : Ws → Eqn
  q303 c4 = eqn (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4))
  q304 : Ws → Eqn
  q304 c4 = eqn (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑))
  q305 : Ws → Eqn
  q305 c4 = eqn (Toff014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4))
  q306 : Ws → Eqn
  q306 c4 = eqn (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑))
  q307 : Ws → Eqn
  q307 c4 = eqn (CS14⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS14⁻ ∷ []) (wl0202 (lit c4))
  q308 : Ws → Eqn
  q308 c4 = eqn (S0⁻ ∷ S0 ∷ []) [] (wl0159 (lit c4))
  q309 : Ws → Eqn
  q309 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at142142 c4)
  q310 : Ws → Eqn
  q310 c4 = eqn (S0 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q311 : Ws → Eqn
  q311 c4 = eqn (CS14⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4))
  q312 : Ws → Eqn
  q312 c4 = eqn (S0⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))

-- VPQ @142142: 14 steps
lem-VPQ-at142142 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at142142 c4 = derive (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q302 c4) ∷
   rw⁻ 4 (q303 c4) ∷
   rw 3 (q304 c4) ∷
   rw 2 (q305 c4) ∷
   rw 1 (q306 c4) ∷
   rw 0 (q307 c4) ∷
   rw 4 (q308 c4) ∷
   rw 3 (q309 c4) ∷
   rw⁻ 4 (q308 c4) ∷
   rw⁻ 1 (q310 c4) ∷
   rw 2 (q311 c4) ∷
   rw⁻ 3 (q312 c4) ∷
   rw 0 (q303 c4) ∷
   rw 2 (q302 c4) ∷ []) Eq.refl

private
  q313 : Ws → Eqn
  q313 c4 = eqn (CCZ014 ∷ Toff014 ∷ CZ14 ∷ []) (Toff014 ∷ CCZ014 ∷ []) (wp0058 c4)
  q314 : Ws → Eqn
  q314 c4 = eqn (CZ14 ∷ Toff023 ∷ []) (Toff023 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF023 (lit c4))
  q315 : Ws → Eqn
  q315 c4 = eqn (CCZ014 ∷ Toff014 ∷ []) (Toff014 ∷ CZ14 ∷ CCZ014 ∷ []) (wp0059 c4)

-- t-cP @142142: 5 steps
lem-t-cP-at142142 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-t-cP-at142142 c4 = derive (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ [])
  (rw⁻ 0 (q313 c4) ∷
   rw 2 (q314 c4) ∷
   rw 1 (q309 c4) ∷
   rw⁻ 2 (q315 c4) ∷
   rw 3 (q309 c4) ∷ []) Eq.refl

private
  q316 : Ws → Eqn
  q316 c4 = eqn (CCZ123 ∷ Toff312 ∷ CZ12 ∷ []) (Toff312 ∷ CCZ123 ∷ []) (wl1403 (lit c4))
  q317 : Ws → Eqn
  q317 c4 = eqn (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4)
  q318 : Ws → Eqn
  q318 c4 = eqn (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4))

-- t-cP @033440: 5 steps
lem-t-cP-at033440 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-t-cP-at033440 c4 = derive (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ [])
  (rw⁻ 0 (q316 c4) ∷
   rw 2 (q155 c4) ∷
   rw 1 (q317 c4) ∷
   rw⁻ 2 (q318 c4) ∷
   rw 3 (q317 c4) ∷ []) Eq.refl

private
  q319 : Ws → Eqn
  q319 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at0214203143 c4)

-- t-cP @0214203143: 5 steps
lem-t-cP-at0214203143 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-t-cP-at0214203143 c4 = derive (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ [])
  (rw⁻ 0 (q222 c4) ∷
   rw 2 (q140 c4) ∷
   rw 1 (q319 c4) ∷
   rw⁻ 2 (q223 c4) ∷
   rw 3 (q319 c4) ∷ []) Eq.refl

private
  q320 : Ws → Eqn
  q320 c4 = eqn (Bx4-2031 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (CX03 ∷ Toff402 ∷ []) (Toff402 ∷ CX03 ∷ []) (wp1311 c4)
  q322 : Ws → Eqn
  q322 c4 = eqn (CCZ134 ∷ CX03 ∷ CCZ014 ∷ []) (CX03 ∷ CCZ134 ∷ []) (wp1312 c4)
  q323 : Ws → Eqn
  q323 c4 = eqn (CCZ014 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1313 c4)
  q324 : Ws → Eqn
  q324 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4))
  q325 : Ws → Eqn
  q325 c4 = eqn (CCZ134 ∷ CS12 ∷ []) (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4))
  q326 : Ws → Eqn
  q326 c4 = eqn (CCZ134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4)
  q327 : Ws → Eqn
  q327 c4 = eqn (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) (wp0261 c4)
  q328 : Ws → Eqn
  q328 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4)
  q329 : Ws → Eqn
  q329 c4 = eqn (CX03 ∷ CCZ014 ∷ CCZ014 ∷ []) (CX03 ∷ []) (wp1314 c4)
  q330 : Ws → Eqn
  q330 c4 = eqn (CCZ012 ∷ []) (CX03 ∷ CCZ012 ∷ CX03 ∷ []) (wl1465 (lit c4))

-- CXbc-box @04122041: 17 steps
lem-CXbc-box-at04122041 : Ws → ⟪ (CX03 ∷ Bx4-2031 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at04122041 c4 = derive (CX03 ∷ Bx4-2031 ∷ CX03 ∷ []) (Bx4-2031 ∷ CCZ012 ∷ [])
  (rw 1 (q320 c4) ∷
   rw 0 (q321 c4) ∷
   rw⁻ 1 (q322 c4) ∷
   rw 3 (q323 c4) ∷
   rw 2 (q321 c4) ∷
   rw 5 (q324 c4) ∷
   rw⁻ 9 (q325 c4) ∷
   rw 8 (q195 c4) ∷
   rw⁻ 7 (q326 c4) ∷
   rw 6 (q195 c4) ∷
   rw⁻ 5 (q327 c4) ∷
   rw⁻ 6 (q324 c4) ∷
   rw 4 (q328 c4) ∷
   rw⁻ 3 (q322 c4) ∷
   rw 4 (q329 c4) ∷
   rw⁻ 0 (q320 c4) ∷
   rw⁻ 1 (q330 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = eqn (CX30 ∷ Toff402 ∷ []) (Toff402 ∷ CX30 ∷ Toff423 ∷ []) (wp1315 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (CCZ134 ∷ Toff423 ∷ CCZ123 ∷ []) (Toff423 ∷ CCZ134 ∷ []) (wl1466 (lit c4))
  q333 : Ws → Eqn
  q333 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4))
  q334 : Ws → Eqn
  q334 c4 = eqn (CS12 ∷ Toff402 ∷ []) (Toff402 ∷ CS12 ∷ []) (wp1316 c4)
  q335 : Ws → Eqn
  q335 c4 = eqn (CX23 ∷ Toff402 ∷ []) (Toff402 ∷ CX23 ∷ []) (wp1317 c4)
  q336 : Ws → Eqn
  q336 c4 = eqn (CS13⁻ ∷ Toff402 ∷ []) (Toff402 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF402 (lit c4))
  q337 : Ws → Eqn
  q337 c4 = eqn (CS13 ∷ Toff402 ∷ []) (Toff402 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF402 (lit c4))
  q338 : Ws → Eqn
  q338 c4 = eqn (Toff402 ∷ Toff423 ∷ []) (Toff423 ∷ Toff402 ∷ []) (wp1318 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (CX30 ∷ Toff423 ∷ Toff423 ∷ []) (CX30 ∷ []) (wp1319 c4)
  q340 : Ws → Eqn
  q340 c4 = eqn (CCZ123 ∷ []) (CX30 ∷ CCZ123 ∷ CX30 ∷ []) (wl1467 (lit c4))

-- CXcb-box @04122041: 18 steps
lem-CXcb-box-at04122041 : Ws → ⟪ (CX30 ∷ Bx4-2031 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at04122041 c4 = derive (CX30 ∷ Bx4-2031 ∷ CX30 ∷ []) (Bx4-2031 ∷ CCZ123 ∷ [])
  (rw 1 (q320 c4) ∷
   rw 0 (q331 c4) ∷
   rw⁻ 2 (q332 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 4 (q333 c4) ∷
   rw 8 (q334 c4) ∷
   rw 7 (q335 c4) ∷
   rw 6 (q336 c4) ∷
   rw 5 (q335 c4) ∷
   rw 4 (q337 c4) ∷
   rw⁻ 5 (q333 c4) ∷
   rw⁻ 3 (q338 c4) ∷
   rw 2 (q331 c4) ∷
   rw 3 (q339 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw⁻ 0 (q320 c4) ∷
   rw⁻ 1 (q340 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = eqn (CS23⁻ ∷ S4 ∷ Toff423 ∷ S4⁻ ∷ []) (Toff423 ∷ CCZ234 ∷ []) (wl0455 (lit c4))
  q342 : Ws → Eqn
  q342 c4 = eqn (CS01⁻ ∷ S4 ∷ Toff401 ∷ S4⁻ ∷ []) (Toff401 ∷ CCZ014 ∷ []) (wp0304 c4)
  q343 : Ws → Eqn
  q343 c4 = eqn (CS01⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑ ↑))
  q344 : Ws → Eqn
  q344 c4 = eqn (CS01⁻ ∷ Toff423 ∷ []) (Toff423 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toffᵗ))
  q345 : Ws → Eqn
  q345 c4 = eqn (CS01⁻ ∷ S4 ∷ []) (S4 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑ ↑))
  q346 : Ws → Eqn
  q346 c4 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CS • CS • CS))
  q347 : Ws → Eqn
  q347 c4 = eqn (S4⁻ ∷ S4 ∷ []) [] (wl0456 (lit c4))
  q348 : Ws → Eqn
  q348 c4 = eqn (Toff423 ∷ Toff401 ∷ []) (Toff401 ∷ Toff423 ∷ []) (lem-tP-at0412233041 c4)
  q349 : Ws → Eqn
  q349 c4 = eqn (CS23⁻ ∷ S4 ∷ []) (S4 ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S))
  q350 : Ws → Eqn
  q350 c4 = eqn (CS23⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 (lit c4))
  q351 : Ws → Eqn
  q351 c4 = eqn (CS23⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS23⁻ ∷ []) (c₄ ((CS • CS • CS) ↑ ↑) (S • S • S))

-- VPQ @0412233041: 14 steps
lem-VPQ-at0412233041 : Ws → ⟪ (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0412233041 c4 = derive (Toff423 ∷ CCZ234 ∷ Toff401 ∷ CCZ014 ∷ []) (Toff401 ∷ CCZ014 ∷ Toff423 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q341 c4) ∷
   rw⁻ 4 (q342 c4) ∷
   rw⁻ 3 (q343 c4) ∷
   rw⁻ 2 (q344 c4) ∷
   rw⁻ 1 (q345 c4) ∷
   rw⁻ 0 (q346 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q348 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q349 c4) ∷
   rw 2 (q350 c4) ∷
   rw 3 (q351 c4) ∷
   rw 0 (q342 c4) ∷
   rw 2 (q341 c4) ∷ []) Eq.refl

private
  q352 : Ws → Eqn
  q352 c4 = eqn (CS02⁻ ∷ S4 ∷ Toff402 ∷ S4⁻ ∷ []) (Toff402 ∷ CCZ024 ∷ []) (wp1322 c4)
  q353 : Ws → Eqn
  q353 c4 = eqn (CS13⁻ ∷ S4 ∷ Toff413 ∷ S4⁻ ∷ []) (Toff413 ∷ CCZ134 ∷ []) (wl1473 (lit c4))
  q354 : Ws → Eqn
  q354 c4 = eqn (CS13⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS13⁻ ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S • S • S))
  q355 : Ws → Eqn
  q355 c4 = eqn (Toff402 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff402 ∷ []) (lem-comm-TOFF402-CSd13 (lit c4))
  q356 : Ws → Eqn
  q356 c4 = eqn (CS13⁻ ∷ S4 ∷ []) (S4 ∷ CS13⁻ ∷ []) (c₄ (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑) (S))
  q357 : Ws → Eqn
  q357 c4 = eqn (CS02⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS02⁻ ∷ []) (wl0901 (lit c4))
  q358 : Ws → Eqn
  q358 c4 = eqn (Toff402 ∷ Toff413 ∷ []) (Toff413 ∷ Toff402 ∷ []) (lem-tP-at04122041 c4)
  q359 : Ws → Eqn
  q359 c4 = eqn (CS02⁻ ∷ S4 ∷ []) (S4 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S ↑))
  q360 : Ws → Eqn
  q360 c4 = eqn (CS02⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF413 (lit c4))
  q361 : Ws → Eqn
  q361 c4 = eqn (CS02⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) ((S • S • S) ↑))

-- VPQ @04122041: 14 steps
lem-VPQ-at04122041 : Ws → ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at04122041 c4 = derive (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q352 c4) ∷
   rw⁻ 4 (q353 c4) ∷
   rw⁻ 3 (q354 c4) ∷
   rw 2 (q355 c4) ∷
   rw⁻ 1 (q356 c4) ∷
   rw 0 (q357 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q358 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q359 c4) ∷
   rw 2 (q360 c4) ∷
   rw 3 (q361 c4) ∷
   rw 0 (q353 c4) ∷
   rw 2 (q352 c4) ∷ []) Eq.refl

private
  q362 : Ws → Eqn
  q362 c4 = eqn (CX12 ∷ CX21 ∷ CX12 ∷ []) (Sw12 ∷ []) (wl0677 (lit c4))
  q363 : Ws → Eqn
  q363 c4 = eqn (CX12 ∷ Bx4-0123 ∷ CX12 ∷ []) (Bx4-0123 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0410213243 c4)
  q364 : Ws → Eqn
  q364 c4 = eqn (CCZ013 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ CCZ013 ∷ []) (wl1479 (lit c4))
  q365 : Ws → Eqn
  q365 c4 = eqn (CX21 ∷ Bx4-0123 ∷ CX21 ∷ []) (Bx4-0123 ∷ CCZ023 ∷ []) (lem-CXcb-box-at0410213243 c4)
  q366 : Ws → Eqn
  q366 c4 = eqn (CCZ013 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4))
  q367 : Ws → Eqn
  q367 c4 = eqn (CCZ023 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ CCZ023 ∷ []) (wl1480 (lit c4))
  q368 : Ws → Eqn
  q368 c4 = eqn (CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ CCZ023 ∷ CCZ013 ∷ []) (CCZ013 ∷ []) (wl1481 (lit c4))

-- SWbc-box @0410213243: 11 steps
lem-SWbc-box-at0410213243 : Ws → ⟪ (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-SWbc-box-at0410213243 c4 = derive (Sw12 ∷ Bx4-0123 ∷ Sw12 ∷ []) (Bx4-0123 ∷ [])
  (rw⁻ 0 (q362 c4) ∷
   rw⁻ 4 (q362 c4) ∷
   rw 2 (q363 c4) ∷
   rw 3 (q364 c4) ∷
   rw 1 (q365 c4) ∷
   rw 4 (q366 c4) ∷
   rw 3 (q367 c4) ∷
   rw 2 (q367 c4) ∷
   rw 3 (q368 c4) ∷
   rw 0 (q363 c4) ∷
   rw 1 (q48 c4) ∷ []) Eq.refl

private
  q369 : Ws → Eqn
  q369 c4 = eqn (Bx4-0213 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04103143 c4)
  q370 : Ws → Eqn
  q370 c4 = eqn (Toff402 ∷ Toff413 ∷ []) (Toff413 ∷ Toff402 ∷ []) (lem-tP-at04103143 c4)
  q371 : Ws → Eqn
  q371 c4 = eqn (CCZ134 ∷ CZ13 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ []) (wl1482 (lit c4))
  q372 : Ws → Eqn
  q372 c4 = eqn (CCZ134 ∷ CZ13 ∷ []) (Toff413 ∷ CCZ134 ∷ Toff413 ∷ []) (wl1483 (lit c4))
  q373 : Ws → Eqn
  q373 c4 = eqn (CZ13 ∷ Toff402 ∷ []) (Toff402 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF402 (lit c4))
  q374 : Ws → Eqn
  q374 c4 = eqn (CCZ134 ∷ []) (CZ13 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1484 (lit c4))

-- P-box @04103143: 8 steps
lem-P-box-at04103143 : Ws → ⟪ (Toff413 ∷ Bx4-0213 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0213 ∷ []) ⟫ʷ
lem-P-box-at04103143 c4 = derive (Toff413 ∷ Bx4-0213 ∷ Toff413 ∷ []) (Bx4-0213 ∷ [])
  (rw 1 (q369 c4) ∷
   rw⁻ 0 (q370 c4) ∷
   rw⁻ 1 (q371 c4) ∷
   rw⁻ 3 (q370 c4) ∷
   rw⁻ 4 (q372 c4) ∷
   rw 2 (q373 c4) ∷
   rw⁻ 3 (q374 c4) ∷
   rw⁻ 0 (q369 c4) ∷ []) Eq.refl

-- VPQ @04103143: 14 steps
lem-VPQ-at04103143 : Ws → ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at04103143 c4 = derive (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q352 c4) ∷
   rw⁻ 4 (q353 c4) ∷
   rw⁻ 3 (q354 c4) ∷
   rw 2 (q355 c4) ∷
   rw⁻ 1 (q356 c4) ∷
   rw 0 (q357 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q370 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q359 c4) ∷
   rw 2 (q360 c4) ∷
   rw 3 (q361 c4) ∷
   rw 0 (q353 c4) ∷
   rw 2 (q352 c4) ∷ []) Eq.refl

private
  q375 : Ws → Eqn
  q375 c4 = eqn (Toff413 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4))
  q376 : Ws → Eqn
  q376 c4 = eqn (Toff413 ∷ Toff402 ∷ []) (Toff402 ∷ Toff413 ∷ []) (lem-tP-at04233042 c4)

-- VPQ @04233042: 14 steps
lem-VPQ-at04233042 : Ws → ⟪ (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at04233042 c4 = derive (Toff413 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ []) (Toff402 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q353 c4) ∷
   rw⁻ 4 (q352 c4) ∷
   rw⁻ 3 (q361 c4) ∷
   rw 2 (q375 c4) ∷
   rw⁻ 1 (q359 c4) ∷
   rw⁻ 0 (q357 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q376 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q356 c4) ∷
   rw 2 (q336 c4) ∷
   rw 3 (q354 c4) ∷
   rw 0 (q352 c4) ∷
   rw 2 (q353 c4) ∷ []) Eq.refl

private
  q377 : Ws → Eqn
  q377 c4 = eqn (Bx4-2301 ∷ []) (Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ []) (lem-box-tQ-at0412233041 c4)
  q378 : Ws → Eqn
  q378 c4 = eqn (CX30 ∷ Toff423 ∷ []) (Toff423 ∷ CX30 ∷ []) (wp1333 c4)
  q379 : Ws → Eqn
  q379 c4 = eqn (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (CX30 ∷ CCZ014 ∷ []) (wp1010 c4)
  q380 : Ws → Eqn
  q380 c4 = eqn (CCZ134 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl1496 (lit c4))
  q381 : Ws → Eqn
  q381 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp0067 c4)
  q382 : Ws → Eqn
  q382 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q383 : Ws → Eqn
  q383 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4)
  q384 : Ws → Eqn
  q384 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp0053 c4)
  q385 : Ws → Eqn
  q385 c4 = eqn (CX30 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX30 ∷ []) (wp1011 c4)

-- CXbc-box @0412233041: 17 steps
lem-CXbc-box-at0412233041 : Ws → ⟪ (CX30 ∷ Bx4-2301 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at0412233041 c4 = derive (CX30 ∷ Bx4-2301 ∷ CX30 ∷ []) (Bx4-2301 ∷ CCZ123 ∷ [])
  (rw 1 (q377 c4) ∷
   rw 0 (q378 c4) ∷
   rw⁻ 1 (q379 c4) ∷
   rw 3 (q380 c4) ∷
   rw 2 (q378 c4) ∷
   rw 5 (q333 c4) ∷
   rw⁻ 9 (q381 c4) ∷
   rw 8 (q382 c4) ∷
   rw⁻ 7 (q383 c4) ∷
   rw 6 (q382 c4) ∷
   rw⁻ 5 (q384 c4) ∷
   rw⁻ 6 (q333 c4) ∷
   rw⁻ 4 (q328 c4) ∷
   rw⁻ 3 (q379 c4) ∷
   rw 4 (q385 c4) ∷
   rw⁻ 0 (q377 c4) ∷
   rw⁻ 1 (q340 c4) ∷ []) Eq.refl

private
  q386 : Ws → Eqn
  q386 c4 = eqn (CX03 ∷ Toff423 ∷ []) (Toff423 ∷ CX03 ∷ Toff402 ∷ []) (wp1334 c4)
  q387 : Ws → Eqn
  q387 c4 = eqn (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (Toff402 ∷ CCZ014 ∷ []) (wp1335 c4)
  q388 : Ws → Eqn
  q388 c4 = eqn (CCZ014 ∷ CX03 ∷ []) (CX03 ∷ CCZ014 ∷ []) (wp0778 c4)
  q389 : Ws → Eqn
  q389 c4 = eqn (CS12 ∷ Toff423 ∷ []) (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4))
  q390 : Ws → Eqn
  q390 c4 = eqn (CX20 ∷ Toff423 ∷ []) (Toff423 ∷ CX20 ∷ []) (wp1336 c4)
  q391 : Ws → Eqn
  q391 c4 = eqn (CS01 ∷ Toff423 ∷ []) (Toff423 ∷ CS01 ∷ []) (c₂ (CS) (Toffᵗ))
  q392 : Ws → Eqn
  q392 c4 = eqn (CX03 ∷ Toff402 ∷ Toff402 ∷ []) (CX03 ∷ []) (wp1337 c4)
  q393 : Ws → Eqn
  q393 c4 = eqn (CCZ012 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4)

-- CXcb-box @0412233041: 18 steps
lem-CXcb-box-at0412233041 : Ws → ⟪ (CX03 ∷ Bx4-2301 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0412233041 c4 = derive (CX03 ∷ Bx4-2301 ∷ CX03 ∷ []) (Bx4-2301 ∷ CCZ012 ∷ [])
  (rw 1 (q377 c4) ∷
   rw 0 (q386 c4) ∷
   rw⁻ 2 (q387 c4) ∷
   rw⁻ 1 (q388 c4) ∷
   rw 4 (q324 c4) ∷
   rw 8 (q389 c4) ∷
   rw 7 (q390 c4) ∷
   rw 6 (q344 c4) ∷
   rw 5 (q390 c4) ∷
   rw 4 (q391 c4) ∷
   rw⁻ 5 (q324 c4) ∷
   rw 3 (q338 c4) ∷
   rw 2 (q386 c4) ∷
   rw 3 (q392 c4) ∷
   rw 4 (q393 c4) ∷
   rw⁻ 3 (q388 c4) ∷
   rw⁻ 0 (q377 c4) ∷
   rw⁻ 1 (q330 c4) ∷ []) Eq.refl

private
  q394 : Ws → Eqn
  q394 c4 = eqn (CCZ014 ∷ CZ01 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ014 ∷ []) (wp1338 c4)
  q395 : Ws → Eqn
  q395 c4 = eqn (CCZ014 ∷ CZ01 ∷ []) (Toff401 ∷ CCZ014 ∷ Toff401 ∷ []) (wp1339 c4)
  q396 : Ws → Eqn
  q396 c4 = eqn (CZ01 ∷ Toff423 ∷ []) (Toff423 ∷ CZ01 ∷ []) (c₂ (CZ) (Toffᵗ))
  q397 : Ws → Eqn
  q397 c4 = eqn (CCZ014 ∷ []) (CZ01 ∷ CCZ014 ∷ CZ01 ∷ []) (wp1340 c4)

-- P-box @0412233041: 8 steps
lem-P-box-at0412233041 : Ws → ⟪ (Toff401 ∷ Bx4-2301 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-P-box-at0412233041 c4 = derive (Toff401 ∷ Bx4-2301 ∷ Toff401 ∷ []) (Bx4-2301 ∷ [])
  (rw 1 (q377 c4) ∷
   rw⁻ 0 (q348 c4) ∷
   rw⁻ 1 (q394 c4) ∷
   rw⁻ 3 (q348 c4) ∷
   rw⁻ 4 (q395 c4) ∷
   rw 2 (q396 c4) ∷
   rw⁻ 3 (q397 c4) ∷
   rw⁻ 0 (q377 c4) ∷ []) Eq.refl

private
  q398 : Ws → Eqn
  q398 c4 = eqn (Bx4-0231 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at041041 c4)
  q399 : Ws → Eqn
  q399 c4 = eqn (CCZ134 ∷ CX23 ∷ CCZ124 ∷ []) (CX23 ∷ CCZ134 ∷ []) (wl1562 (lit c4))
  q400 : Ws → Eqn
  q400 c4 = eqn (CCZ124 ∷ Toff402 ∷ []) (Toff402 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1385 c4)
  q401 : Ws → Eqn
  q401 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4))
  q402 : Ws → Eqn
  q402 c4 = eqn (CX02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4))
  q403 : Ws → Eqn
  q403 c4 = eqn (CCZ134 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4))
  q404 : Ws → Eqn
  q404 c4 = eqn (CX23 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX23 ∷ []) (wl1563 (lit c4))
  q405 : Ws → Eqn
  q405 c4 = eqn (CCZ012 ∷ []) (CX23 ∷ CCZ012 ∷ CX23 ∷ []) (wl1564 (lit c4))

-- CXbc-box @041041: 17 steps
lem-CXbc-box-at041041 : Ws → ⟪ (CX23 ∷ Bx4-0231 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at041041 c4 = derive (CX23 ∷ Bx4-0231 ∷ CX23 ∷ []) (Bx4-0231 ∷ CCZ012 ∷ [])
  (rw 1 (q398 c4) ∷
   rw 0 (q335 c4) ∷
   rw⁻ 1 (q399 c4) ∷
   rw 3 (q400 c4) ∷
   rw 2 (q335 c4) ∷
   rw 5 (q401 c4) ∷
   rw⁻ 9 (q327 c4) ∷
   rw 8 (q402 c4) ∷
   rw⁻ 7 (q403 c4) ∷
   rw 6 (q402 c4) ∷
   rw⁻ 5 (q325 c4) ∷
   rw⁻ 6 (q401 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 3 (q399 c4) ∷
   rw 4 (q404 c4) ∷
   rw⁻ 0 (q398 c4) ∷
   rw⁻ 1 (q405 c4) ∷ []) Eq.refl

private
  q406 : Ws → Eqn
  q406 c4 = eqn (CX32 ∷ Toff402 ∷ []) (Toff402 ∷ CX32 ∷ Toff403 ∷ []) (wp1386 c4)
  q407 : Ws → Eqn
  q407 c4 = eqn (CCZ134 ∷ Toff403 ∷ CCZ013 ∷ []) (Toff403 ∷ CCZ134 ∷ []) (wp1387 c4)
  q408 : Ws → Eqn
  q408 c4 = eqn (CCZ134 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ []) (wl1021 (lit c4))
  q409 : Ws → Eqn
  q409 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4))
  q410 : Ws → Eqn
  q410 c4 = eqn (CS01 ∷ Toff402 ∷ []) (Toff402 ∷ CS01 ∷ []) (wp1388 c4)
  q411 : Ws → Eqn
  q411 c4 = eqn (Toff402 ∷ Toff403 ∷ []) (Toff403 ∷ Toff402 ∷ []) (wp1389 c4)
  q412 : Ws → Eqn
  q412 c4 = eqn (CX32 ∷ Toff403 ∷ Toff403 ∷ []) (CX32 ∷ []) (wp1390 c4)
  q413 : Ws → Eqn
  q413 c4 = eqn (CCZ013 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4)
  q414 : Ws → Eqn
  q414 c4 = eqn (CCZ013 ∷ []) (CX32 ∷ CCZ013 ∷ CX32 ∷ []) (wl1565 (lit c4))

-- CXcb-box @041041: 18 steps
lem-CXcb-box-at041041 : Ws → ⟪ (CX32 ∷ Bx4-0231 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0231 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at041041 c4 = derive (CX32 ∷ Bx4-0231 ∷ CX32 ∷ []) (Bx4-0231 ∷ CCZ013 ∷ [])
  (rw 1 (q398 c4) ∷
   rw 0 (q406 c4) ∷
   rw⁻ 2 (q407 c4) ∷
   rw⁻ 1 (q408 c4) ∷
   rw 4 (q409 c4) ∷
   rw 8 (q410 c4) ∷
   rw 7 (q321 c4) ∷
   rw 6 (q336 c4) ∷
   rw 5 (q321 c4) ∷
   rw 4 (q337 c4) ∷
   rw⁻ 5 (q409 c4) ∷
   rw⁻ 3 (q411 c4) ∷
   rw 2 (q406 c4) ∷
   rw 3 (q412 c4) ∷
   rw 4 (q413 c4) ∷
   rw⁻ 3 (q408 c4) ∷
   rw⁻ 0 (q398 c4) ∷
   rw⁻ 1 (q414 c4) ∷ []) Eq.refl

private
  q415 : Ws → Eqn
  q415 c4 = eqn (Bx4-0321 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0410233241 c4)
  q416 : Ws → Eqn
  q416 c4 = eqn (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0410233241 c4)
  q417 : Ws → Eqn
  q417 c4 = eqn (CCZ124 ∷ CZ12 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ124 ∷ []) (wl1569 (lit c4))
  q418 : Ws → Eqn
  q418 c4 = eqn (CCZ124 ∷ CZ12 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff412 ∷ []) (wl1570 (lit c4))
  q419 : Ws → Eqn
  q419 c4 = eqn (CZ12 ∷ Toff403 ∷ []) (Toff403 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF403 (lit c4))
  q420 : Ws → Eqn
  q420 c4 = eqn (CCZ124 ∷ []) (CZ12 ∷ CCZ124 ∷ CZ12 ∷ []) (wl1571 (lit c4))

-- P-box @0410233241: 8 steps
lem-P-box-at0410233241 : Ws → ⟪ (Toff412 ∷ Bx4-0321 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-P-box-at0410233241 c4 = derive (Toff412 ∷ Bx4-0321 ∷ Toff412 ∷ []) (Bx4-0321 ∷ [])
  (rw 1 (q415 c4) ∷
   rw⁻ 0 (q416 c4) ∷
   rw⁻ 1 (q417 c4) ∷
   rw⁻ 3 (q416 c4) ∷
   rw⁻ 4 (q418 c4) ∷
   rw 2 (q419 c4) ∷
   rw⁻ 3 (q420 c4) ∷
   rw⁻ 0 (q415 c4) ∷ []) Eq.refl

private
  q421 : Ws → Eqn
  q421 c4 = eqn (CS03⁻ ∷ S4 ∷ Toff403 ∷ S4⁻ ∷ []) (Toff403 ∷ CCZ034 ∷ []) (wp0316 c4)
  q422 : Ws → Eqn
  q422 c4 = eqn (CS12⁻ ∷ S4 ∷ Toff412 ∷ S4⁻ ∷ []) (Toff412 ∷ CCZ124 ∷ []) (wl0468 (lit c4))
  q423 : Ws → Eqn
  q423 c4 = eqn (CS12⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) ((S • S • S) ↑))
  q424 : Ws → Eqn
  q424 c4 = eqn (Toff403 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff403 ∷ []) (lem-comm-TOFF403-CSd12 (lit c4))
  q425 : Ws → Eqn
  q425 c4 = eqn (CS12⁻ ∷ S4 ∷ []) (S4 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S ↑))
  q426 : Ws → Eqn
  q426 c4 = eqn (CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS03⁻ ∷ []) (wl0469 (lit c4))
  q427 : Ws → Eqn
  q427 c4 = eqn (CS03⁻ ∷ S4 ∷ []) (S4 ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S))
  q428 : Ws → Eqn
  q428 c4 = eqn (CS03⁻ ∷ Toff412 ∷ []) (Toff412 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF412 (lit c4))
  q429 : Ws → Eqn
  q429 c4 = eqn (CS03⁻ ∷ S4⁻ ∷ []) (S4⁻ ∷ CS03⁻ ∷ []) (c₄ (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑) (S • S • S))

-- VPQ @0410233241: 14 steps
lem-VPQ-at0410233241 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0410233241 c4 = derive (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q421 c4) ∷
   rw⁻ 4 (q422 c4) ∷
   rw⁻ 3 (q423 c4) ∷
   rw 2 (q424 c4) ∷
   rw⁻ 1 (q425 c4) ∷
   rw 0 (q426 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q416 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q427 c4) ∷
   rw 2 (q428 c4) ∷
   rw 3 (q429 c4) ∷
   rw 0 (q422 c4) ∷
   rw 2 (q421 c4) ∷ []) Eq.refl

private
  q430 : Ws → Eqn
  q430 c4 = eqn (Toff412 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff412 ∷ []) (lem-comm-TOFF412-CSd03 (lit c4))
  q431 : Ws → Eqn
  q431 c4 = eqn (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0412213043 c4)
  q432 : Ws → Eqn
  q432 c4 = eqn (CS12⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF403 (lit c4))

-- VPQ @0412213043: 14 steps
lem-VPQ-at0412213043 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0412213043 c4 = derive (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q422 c4) ∷
   rw⁻ 4 (q421 c4) ∷
   rw⁻ 3 (q429 c4) ∷
   rw 2 (q430 c4) ∷
   rw⁻ 1 (q427 c4) ∷
   rw⁻ 0 (q426 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q431 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q425 c4) ∷
   rw 2 (q432 c4) ∷
   rw 3 (q423 c4) ∷
   rw 0 (q421 c4) ∷
   rw 2 (q422 c4) ∷ []) Eq.refl

-- P-box @04122041: 8 steps
lem-P-box-at04122041 : Ws → ⟪ (Toff413 ∷ Bx4-2031 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-P-box-at04122041 c4 = derive (Toff413 ∷ Bx4-2031 ∷ Toff413 ∷ []) (Bx4-2031 ∷ [])
  (rw 1 (q320 c4) ∷
   rw⁻ 0 (q358 c4) ∷
   rw⁻ 1 (q371 c4) ∷
   rw⁻ 3 (q358 c4) ∷
   rw⁻ 4 (q372 c4) ∷
   rw 2 (q373 c4) ∷
   rw⁻ 3 (q374 c4) ∷
   rw⁻ 0 (q320 c4) ∷ []) Eq.refl

private
  q433 : Ws → Eqn
  q433 c4 = eqn (Bx4-1320 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233240 c4)
  q434 : Ws → Eqn
  q434 c4 = eqn (CX32 ∷ Toff413 ∷ []) (Toff413 ∷ CX32 ∷ []) (wl1586 (lit c4))
  q435 : Ws → Eqn
  q435 c4 = eqn (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (CX32 ∷ CCZ024 ∷ []) (wp0717 c4)
  q436 : Ws → Eqn
  q436 c4 = eqn (CCZ034 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp1396 c4)
  q437 : Ws → Eqn
  q437 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4))
  q438 : Ws → Eqn
  q438 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp0039 c4)
  q439 : Ws → Eqn
  q439 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q440 : Ws → Eqn
  q440 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4)
  q441 : Ws → Eqn
  q441 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp0021 c4)
  q442 : Ws → Eqn
  q442 c4 = eqn (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ []) (wp0718 c4)

-- CXbc-box @04233240: 17 steps
lem-CXbc-box-at04233240 : Ws → ⟪ (CX32 ∷ Bx4-1320 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at04233240 c4 = derive (CX32 ∷ Bx4-1320 ∷ CX32 ∷ []) (Bx4-1320 ∷ CCZ013 ∷ [])
  (rw 1 (q433 c4) ∷
   rw 0 (q434 c4) ∷
   rw⁻ 1 (q435 c4) ∷
   rw 3 (q436 c4) ∷
   rw 2 (q434 c4) ∷
   rw 5 (q437 c4) ∷
   rw⁻ 9 (q438 c4) ∷
   rw 8 (q439 c4) ∷
   rw⁻ 7 (q440 c4) ∷
   rw 6 (q439 c4) ∷
   rw⁻ 5 (q441 c4) ∷
   rw⁻ 6 (q437 c4) ∷
   rw⁻ 4 (q91 c4) ∷
   rw⁻ 3 (q435 c4) ∷
   rw 4 (q442 c4) ∷
   rw⁻ 0 (q433 c4) ∷
   rw⁻ 1 (q414 c4) ∷ []) Eq.refl

private
  q443 : Ws → Eqn
  q443 c4 = eqn (CX23 ∷ Toff413 ∷ []) (Toff413 ∷ CX23 ∷ Toff412 ∷ []) (wl1587 (lit c4))
  q444 : Ws → Eqn
  q444 c4 = eqn (CCZ024 ∷ Toff412 ∷ CCZ012 ∷ []) (Toff412 ∷ CCZ024 ∷ []) (wp1397 c4)
  q445 : Ws → Eqn
  q445 c4 = eqn (CCZ024 ∷ CX23 ∷ []) (CX23 ∷ CCZ024 ∷ []) (wp0082 c4)
  q446 : Ws → Eqn
  q446 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4))
  q447 : Ws → Eqn
  q447 c4 = eqn (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ []) (wp1398 c4)
  q448 : Ws → Eqn
  q448 c4 = eqn (CX12 ∷ Toff413 ∷ []) (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4))
  q449 : Ws → Eqn
  q449 c4 = eqn (CS02 ∷ Toff413 ∷ []) (Toff413 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF413 (lit c4))
  q450 : Ws → Eqn
  q450 c4 = eqn (Toff412 ∷ Toff413 ∷ []) (Toff413 ∷ Toff412 ∷ []) (wl1589 (lit c4))
  q451 : Ws → Eqn
  q451 c4 = eqn (CX23 ∷ Toff412 ∷ Toff412 ∷ []) (CX23 ∷ []) (wl1590 (lit c4))
  q452 : Ws → Eqn
  q452 c4 = eqn (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) (wp0142 c4)

-- CXcb-box @04233240: 18 steps
lem-CXcb-box-at04233240 : Ws → ⟪ (CX23 ∷ Bx4-1320 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at04233240 c4 = derive (CX23 ∷ Bx4-1320 ∷ CX23 ∷ []) (Bx4-1320 ∷ CCZ012 ∷ [])
  (rw 1 (q433 c4) ∷
   rw 0 (q443 c4) ∷
   rw⁻ 2 (q444 c4) ∷
   rw⁻ 1 (q445 c4) ∷
   rw 4 (q446 c4) ∷
   rw 8 (q447 c4) ∷
   rw 7 (q448 c4) ∷
   rw 6 (q360 c4) ∷
   rw 5 (q448 c4) ∷
   rw 4 (q449 c4) ∷
   rw⁻ 5 (q446 c4) ∷
   rw 3 (q450 c4) ∷
   rw 2 (q443 c4) ∷
   rw 3 (q451 c4) ∷
   rw 4 (q452 c4) ∷
   rw⁻ 3 (q445 c4) ∷
   rw⁻ 0 (q433 c4) ∷
   rw⁻ 1 (q405 c4) ∷ []) Eq.refl

private
  q453 : Ws → Eqn
  q453 c4 = eqn (Bx4-1230 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4)
  q454 : Ws → Eqn
  q454 c4 = eqn (Toff412 ∷ Toff403 ∷ []) (Toff403 ∷ Toff412 ∷ []) (lem-tP-at0440 c4)
  q455 : Ws → Eqn
  q455 c4 = eqn (CCZ034 ∷ CZ03 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ034 ∷ []) (wp1399 c4)
  q456 : Ws → Eqn
  q456 c4 = eqn (CCZ034 ∷ CZ03 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff403 ∷ []) (wp1400 c4)
  q457 : Ws → Eqn
  q457 c4 = eqn (CZ03 ∷ Toff412 ∷ []) (Toff412 ∷ CZ03 ∷ []) (lem-comm-CZ03-TOFF412 (lit c4))
  q458 : Ws → Eqn
  q458 c4 = eqn (CCZ034 ∷ []) (CZ03 ∷ CCZ034 ∷ CZ03 ∷ []) (wp0375 c4)

-- P-box @0440: 8 steps
lem-P-box-at0440 : Ws → ⟪ (Toff403 ∷ Bx4-1230 ∷ Toff403 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-P-box-at0440 c4 = derive (Toff403 ∷ Bx4-1230 ∷ Toff403 ∷ []) (Bx4-1230 ∷ [])
  (rw 1 (q453 c4) ∷
   rw⁻ 0 (q454 c4) ∷
   rw⁻ 1 (q455 c4) ∷
   rw⁻ 3 (q454 c4) ∷
   rw⁻ 4 (q456 c4) ∷
   rw 2 (q457 c4) ∷
   rw⁻ 3 (q458 c4) ∷
   rw⁻ 0 (q453 c4) ∷ []) Eq.refl

-- VPQ @0440: 14 steps
lem-VPQ-at0440 : Ws → ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at0440 c4 = derive (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q422 c4) ∷
   rw⁻ 4 (q421 c4) ∷
   rw⁻ 3 (q429 c4) ∷
   rw 2 (q430 c4) ∷
   rw⁻ 1 (q427 c4) ∷
   rw⁻ 0 (q426 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q454 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q425 c4) ∷
   rw 2 (q432 c4) ∷
   rw 3 (q423 c4) ∷
   rw 0 (q421 c4) ∷
   rw 2 (q422 c4) ∷ []) Eq.refl

private
  q459 : Ws → Eqn
  q459 c4 = eqn (Bx4-3012 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203142 c4)
  q460 : Ws → Eqn
  q460 c4 = eqn (CX01 ∷ Toff403 ∷ []) (Toff403 ∷ CX01 ∷ []) (wp1401 c4)
  q461 : Ws → Eqn
  q461 c4 = eqn (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1402 c4)
  q462 : Ws → Eqn
  q462 c4 = eqn (CCZ023 ∷ []) (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4))
  q463 : Ws → Eqn
  q463 c4 = eqn (CCZ124 ∷ CS23 ∷ []) (CS23 ∷ CCZ124 ∷ []) (wl0639 (lit c4))
  q464 : Ws → Eqn
  q464 c4 = eqn (CCZ124 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ124 ∷ []) (wp0679 c4)
  q465 : Ws → Eqn
  q465 c4 = eqn (CCZ124 ∷ CS02 ∷ []) (CS02 ∷ CCZ124 ∷ []) (wp0515 c4)
  q466 : Ws → Eqn
  q466 c4 = eqn (CCZ023 ∷ []) (CX01 ∷ CCZ023 ∷ CX01 ∷ []) (wl1597 (lit c4))

-- CXbc-box @0413203142: 17 steps
lem-CXbc-box-at0413203142 : Ws → ⟪ (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXbc-box-at0413203142 c4 = derive (CX01 ∷ Bx4-3012 ∷ CX01 ∷ []) (Bx4-3012 ∷ CCZ023 ∷ [])
  (rw 1 (q459 c4) ∷
   rw 0 (q460 c4) ∷
   rw⁻ 1 (q121 c4) ∷
   rw 3 (q461 c4) ∷
   rw 2 (q460 c4) ∷
   rw 5 (q462 c4) ∷
   rw⁻ 9 (q463 c4) ∷
   rw 8 (q124 c4) ∷
   rw⁻ 7 (q464 c4) ∷
   rw 6 (q124 c4) ∷
   rw⁻ 5 (q465 c4) ∷
   rw⁻ 6 (q462 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 3 (q121 c4) ∷
   rw 4 (q127 c4) ∷
   rw⁻ 0 (q459 c4) ∷
   rw⁻ 1 (q466 c4) ∷ []) Eq.refl

private
  q467 : Ws → Eqn
  q467 c4 = eqn (CX10 ∷ Toff403 ∷ []) (Toff403 ∷ CX10 ∷ Toff413 ∷ []) (wp1403 c4)
  q468 : Ws → Eqn
  q468 c4 = eqn (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (Toff413 ∷ CCZ124 ∷ []) (wl1598 (lit c4))
  q469 : Ws → Eqn
  q469 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4))
  q470 : Ws → Eqn
  q470 c4 = eqn (CS23 ∷ Toff403 ∷ []) (Toff403 ∷ CS23 ∷ []) (wp1404 c4)
  q471 : Ws → Eqn
  q471 c4 = eqn (CX31 ∷ Toff403 ∷ []) (Toff403 ∷ CX31 ∷ []) (wp1405 c4)
  q472 : Ws → Eqn
  q472 c4 = eqn (CS12 ∷ Toff403 ∷ []) (Toff403 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF403 (lit c4))
  q473 : Ws → Eqn
  q473 c4 = eqn (Toff403 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ []) (wp1377 c4)
  q474 : Ws → Eqn
  q474 c4 = eqn (CX10 ∷ Toff413 ∷ Toff413 ∷ []) (CX10 ∷ []) (wp1406 c4)
  q475 : Ws → Eqn
  q475 c4 = eqn (CCZ123 ∷ []) (CX10 ∷ CCZ123 ∷ CX10 ∷ []) (wl1599 (lit c4))

-- CXcb-box @0413203142: 18 steps
lem-CXcb-box-at0413203142 : Ws → ⟪ (CX10 ∷ Bx4-3012 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at0413203142 c4 = derive (CX10 ∷ Bx4-3012 ∷ CX10 ∷ []) (Bx4-3012 ∷ CCZ123 ∷ [])
  (rw 1 (q459 c4) ∷
   rw 0 (q467 c4) ∷
   rw⁻ 2 (q468 c4) ∷
   rw⁻ 1 (q130 c4) ∷
   rw 4 (q469 c4) ∷
   rw 8 (q470 c4) ∷
   rw 7 (q471 c4) ∷
   rw 6 (q432 c4) ∷
   rw 5 (q471 c4) ∷
   rw 4 (q472 c4) ∷
   rw⁻ 5 (q469 c4) ∷
   rw⁻ 3 (q473 c4) ∷
   rw 2 (q467 c4) ∷
   rw 3 (q474 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw⁻ 0 (q459 c4) ∷
   rw⁻ 1 (q475 c4) ∷ []) Eq.refl

private
  q476 : Ws → Eqn
  q476 c4 = eqn (Toff214 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff214 ∷ []) (lem-comm-TOFF214-CSd03 (lit c4))
  q477 : Ws → Eqn
  q477 c4 = eqn (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ []) (lem-tP-at02142140 c4)

-- VPQ @02142140: 14 steps
lem-VPQ-at02142140 : Ws → ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ
lem-VPQ-at02142140 c4 = derive (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ [])
  (rw⁻ 0 (q106 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw 2 (q476 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw⁻ 0 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q477 c4) ∷
   rw⁻ 4 (q111 c4) ∷
   rw 1 (q109 c4) ∷
   rw 2 (q133 c4) ∷
   rw 3 (q107 c4) ∷
   rw 0 (q105 c4) ∷
   rw 2 (q106 c4) ∷ []) Eq.refl

private
  q478 : Ws → Eqn
  q478 c4 = eqn (Bx4-3102 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213042 c4)
  q479 : Ws → Eqn
  q479 c4 = eqn (CX10 ∷ Toff413 ∷ []) (Toff413 ∷ CX10 ∷ []) (wp1407 c4)
  q480 : Ws → Eqn
  q480 c4 = eqn (CCZ124 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl1603 (lit c4))
  q481 : Ws → Eqn
  q481 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp0092 c4)
  q482 : Ws → Eqn
  q482 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4)
  q483 : Ws → Eqn
  q483 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp0081 c4)

-- CXbc-box @0413213042: 17 steps
lem-CXbc-box-at0413213042 : Ws → ⟪ (CX10 ∷ Bx4-3102 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at0413213042 c4 = derive (CX10 ∷ Bx4-3102 ∷ CX10 ∷ []) (Bx4-3102 ∷ CCZ123 ∷ [])
  (rw 1 (q478 c4) ∷
   rw 0 (q479 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 3 (q480 c4) ∷
   rw 2 (q479 c4) ∷
   rw 5 (q469 c4) ∷
   rw⁻ 9 (q481 c4) ∷
   rw 8 (q75 c4) ∷
   rw⁻ 7 (q482 c4) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 5 (q483 c4) ∷
   rw⁻ 6 (q469 c4) ∷
   rw⁻ 4 (q78 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 0 (q478 c4) ∷
   rw⁻ 1 (q475 c4) ∷ []) Eq.refl

private
  q484 : Ws → Eqn
  q484 c4 = eqn (CX01 ∷ Toff413 ∷ []) (Toff413 ∷ CX01 ∷ Toff403 ∷ []) (wp1408 c4)
  q485 : Ws → Eqn
  q485 c4 = eqn (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (Toff403 ∷ CCZ024 ∷ []) (wp1374 c4)
  q486 : Ws → Eqn
  q486 c4 = eqn (CS23 ∷ Toff413 ∷ []) (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4))
  q487 : Ws → Eqn
  q487 c4 = eqn (CX30 ∷ Toff413 ∷ []) (Toff413 ∷ CX30 ∷ []) (wp1409 c4)
  q488 : Ws → Eqn
  q488 c4 = eqn (CX01 ∷ Toff403 ∷ Toff403 ∷ []) (CX01 ∷ []) (wp1410 c4)
  q489 : Ws → Eqn
  q489 c4 = eqn (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4)

-- CXcb-box @0413213042: 18 steps
lem-CXcb-box-at0413213042 : Ws → ⟪ (CX01 ∷ Bx4-3102 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at0413213042 c4 = derive (CX01 ∷ Bx4-3102 ∷ CX01 ∷ []) (Bx4-3102 ∷ CCZ023 ∷ [])
  (rw 1 (q478 c4) ∷
   rw 0 (q484 c4) ∷
   rw⁻ 2 (q485 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 4 (q462 c4) ∷
   rw 8 (q486 c4) ∷
   rw 7 (q487 c4) ∷
   rw 6 (q360 c4) ∷
   rw 5 (q487 c4) ∷
   rw 4 (q449 c4) ∷
   rw⁻ 5 (q462 c4) ∷
   rw 3 (q473 c4) ∷
   rw 2 (q484 c4) ∷
   rw 3 (q488 c4) ∷
   rw 4 (q489 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 0 (q478 c4) ∷
   rw⁻ 1 (q466 c4) ∷ []) Eq.refl

private
  q490 : Ws → Eqn
  q490 c4 = eqn (Toff403 ∷ Toff412 ∷ []) (Toff412 ∷ Toff403 ∷ []) (lem-tP-at0413203142 c4)

-- P-box @0413203142: 8 steps
lem-P-box-at0413203142 : Ws → ⟪ (Toff412 ∷ Bx4-3012 ∷ Toff412 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-P-box-at0413203142 c4 = derive (Toff412 ∷ Bx4-3012 ∷ Toff412 ∷ []) (Bx4-3012 ∷ [])
  (rw 1 (q459 c4) ∷
   rw⁻ 0 (q490 c4) ∷
   rw⁻ 1 (q417 c4) ∷
   rw⁻ 3 (q490 c4) ∷
   rw⁻ 4 (q418 c4) ∷
   rw 2 (q419 c4) ∷
   rw⁻ 3 (q420 c4) ∷
   rw⁻ 0 (q459 c4) ∷ []) Eq.refl

-- VPQ @0413203142: 14 steps
lem-VPQ-at0413203142 : Ws → ⟪ (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0413203142 c4 = derive (Toff403 ∷ CCZ034 ∷ Toff412 ∷ CCZ124 ∷ []) (Toff412 ∷ CCZ124 ∷ Toff403 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q421 c4) ∷
   rw⁻ 4 (q422 c4) ∷
   rw⁻ 3 (q423 c4) ∷
   rw 2 (q424 c4) ∷
   rw⁻ 1 (q425 c4) ∷
   rw 0 (q426 c4) ∷
   rw 4 (q347 c4) ∷
   rw 3 (q490 c4) ∷
   rw⁻ 4 (q347 c4) ∷
   rw 1 (q427 c4) ∷
   rw 2 (q428 c4) ∷
   rw 3 (q429 c4) ∷
   rw 0 (q422 c4) ∷
   rw 2 (q421 c4) ∷ []) Eq.refl

private
  q491 : Ws → Eqn
  q491 c4 = eqn (CX23 ∷ Toff412 ∷ []) (Toff412 ∷ CX23 ∷ []) (wl1609 (lit c4))
  q492 : Ws → Eqn
  q492 c4 = eqn (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (CX23 ∷ CCZ034 ∷ []) (wp0104 c4)
  q493 : Ws → Eqn
  q493 c4 = eqn (CCZ024 ∷ Toff412 ∷ []) (Toff412 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp1413 c4)
  q494 : Ws → Eqn
  q494 c4 = eqn (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) (wp0001 c4)
  q495 : Ws → Eqn
  q495 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q496 : Ws → Eqn
  q496 c4 = eqn (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4)
  q497 : Ws → Eqn
  q497 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp0003 c4)
  q498 : Ws → Eqn
  q498 c4 = eqn (CX23 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX23 ∷ []) (wp0110 c4)

-- CXbc-box @0440: 17 steps
lem-CXbc-box-at0440 : Ws → ⟪ (CX23 ∷ Bx4-1230 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0440 c4 = derive (CX23 ∷ Bx4-1230 ∷ CX23 ∷ []) (Bx4-1230 ∷ CCZ012 ∷ [])
  (rw 1 (q453 c4) ∷
   rw 0 (q491 c4) ∷
   rw⁻ 1 (q492 c4) ∷
   rw 3 (q493 c4) ∷
   rw 2 (q491 c4) ∷
   rw 5 (q446 c4) ∷
   rw⁻ 9 (q494 c4) ∷
   rw 8 (q495 c4) ∷
   rw⁻ 7 (q496 c4) ∷
   rw 6 (q495 c4) ∷
   rw⁻ 5 (q497 c4) ∷
   rw⁻ 6 (q446 c4) ∷
   rw 4 (q91 c4) ∷
   rw⁻ 3 (q492 c4) ∷
   rw 4 (q498 c4) ∷
   rw⁻ 0 (q453 c4) ∷
   rw⁻ 1 (q405 c4) ∷ []) Eq.refl

private
  q499 : Ws → Eqn
  q499 c4 = eqn (CX32 ∷ Toff412 ∷ []) (Toff412 ∷ CX32 ∷ Toff413 ∷ []) (wl1610 (lit c4))
  q500 : Ws → Eqn
  q500 c4 = eqn (CCZ034 ∷ Toff413 ∷ CCZ013 ∷ []) (Toff413 ∷ CCZ034 ∷ []) (wp1414 c4)
  q501 : Ws → Eqn
  q501 c4 = eqn (CCZ034 ∷ CX32 ∷ []) (CX32 ∷ CCZ034 ∷ []) (wp0101 c4)
  q502 : Ws → Eqn
  q502 c4 = eqn (CS01 ∷ Toff412 ∷ []) (Toff412 ∷ CS01 ∷ []) (wp1415 c4)
  q503 : Ws → Eqn
  q503 c4 = eqn (CX13 ∷ Toff412 ∷ []) (Toff412 ∷ CX13 ∷ []) (wl1611 (lit c4))
  q504 : Ws → Eqn
  q504 c4 = eqn (CS03 ∷ Toff412 ∷ []) (Toff412 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF412 (lit c4))
  q505 : Ws → Eqn
  q505 c4 = eqn (CX32 ∷ Toff413 ∷ Toff413 ∷ []) (CX32 ∷ []) (wl1612 (lit c4))
  q506 : Ws → Eqn
  q506 c4 = eqn (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4)

-- CXcb-box @0440: 18 steps
lem-CXcb-box-at0440 : Ws → ⟪ (CX32 ∷ Bx4-1230 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0440 c4 = derive (CX32 ∷ Bx4-1230 ∷ CX32 ∷ []) (Bx4-1230 ∷ CCZ013 ∷ [])
  (rw 1 (q453 c4) ∷
   rw 0 (q499 c4) ∷
   rw⁻ 2 (q500 c4) ∷
   rw⁻ 1 (q501 c4) ∷
   rw 4 (q437 c4) ∷
   rw 8 (q502 c4) ∷
   rw 7 (q503 c4) ∷
   rw 6 (q428 c4) ∷
   rw 5 (q503 c4) ∷
   rw 4 (q504 c4) ∷
   rw⁻ 5 (q437 c4) ∷
   rw⁻ 3 (q450 c4) ∷
   rw 2 (q499 c4) ∷
   rw 3 (q505 c4) ∷
   rw 4 (q506 c4) ∷
   rw⁻ 3 (q501 c4) ∷
   rw⁻ 0 (q453 c4) ∷
   rw⁻ 1 (q414 c4) ∷ []) Eq.refl
