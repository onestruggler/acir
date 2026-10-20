{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D023 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0193 ; wl0195 ; wl0321 ; wl0746 ; wl0748 ; wl0807 ; wl0808 ; wl0831 ; wl0921 ; wl0954 ; wl1380 ; wl1421 ; wl1422 ; wl1432 ; wl1433 ; wl1434 ; wl1435 ; wl1436 ; wl1437 ; wl1438 ; wl1446 ; wl1447 ; wl1448 ; wl1451 ; wl1452 ; wl1453 ; wp0021 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0039 ; wp0161 ; wp0179 ; wp0653 ; wp0655 ; wp0746 ; wp0760 ; wp1143 ; wp1275 ; wp1276 ; wp1282 ; wp1283 ; wp1284 ; wp1285 ; wp1286 ; wp1287 ; wp1288 ; wp1289 ; wp1290 ; wp1291 ; wp1297 ; wp1298 ; wp1301 ; wp1302 ; wp1304 ; wp1305 ; wl0181 ; wl0242 ; wl1474 ; wl1475 ; wl1487 ; wl1490 ; wl1498 ; wl1499 ; wl1500 ; wl1502 ; wl1505 ; wl1510 ; wl1511 ; wl1513 ; wp0081 ; wp0091 ; wp0092 ; wp0306 ; wp1323 ; wp1324 ; wl0204 ; wl1431 ; wl1535 ; wl1536 ; wl1537 ; wl1538 ; wp1278 ; wp1361 ; wp1362 ; wp1363 ; wl0326 ; wl0470 ; wl0964 ; wl0965 ; wl0966 ; wl0967 ; wl0968 ; wl0969 ; wl0970 ; wl1270 ; wl1544 ; wl1545 ; wl1546 ; wl1547 ; wl1548 ; wl1549 ; wl1550 ; wl1551 ; wl1552 ; wl1553 ; wl1554 ; wl1555 ; wl1561 ; wl1574 ; wl1576 ; wl1577 ; wl1581 ; wp0032 ; wp0087 ; wp0088 ; wp0089 ; wp0109 ; wp0317 ; wp0717 ; wp0718 ; wp0749 ; wp1373 ; wp1374 ; wp1375 ; wp1376 ; wp1377 ; wp1378 ; wp1379 ; wp1380 ; wp1381 ; wp1382 ; wp1384 ; wp1393 ; wl0297 ; wl0707 ; wl1615 ; wl1616 ; wl1617 ; wl1618 ; wl1619 ; wp0914 ; wl0191 ; wl0196 ; wl0443 ; wl0662 ; wl0663 ; wl0809 ; wl0882 ; wl0885 ; wl0886 ; wl0887 ; wl1646 ; wl1647 ; wl1648 ; wl1649 ; wl1650 ; wl1651 ; wp0127 ; wp0314 ; wp0320 ; wp0536 ; wp0537 ; wp0734)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab-at0214203143 ; lem-sym-ab-at0314203142 ; lem-sym-ab-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at0213243041 ; lem-sym-ab-at0214233041)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at0410213243)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0214203143)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at04122041 ; lem-box-tQ-at04233042)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-box-tQ-at0412213043 ; lem-box-tQ-at0413203142 ; lem-box-tQ-at0413213240 ; lem-box-tQ-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-P-box-at0410233241 ; lem-P-box-at04103143 ; lem-P-box-at04122041 ; lem-P-box-at0412233041 ; lem-P-box-at0413203142 ; lem-P-box-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D013 using (lem-P-box-at0413213240)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0214203143 ; lem-box-cP-at0314203142 ; lem-box-cP-at043043 ; lem-pairs-at0210213443 ; lem-pairs-at0214233041 ; lem-sym-bc-at0210243143 ; lem-sym-bc-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-CSdu-box-3-at0310213442 ; lem-box-cP-at0410233241 ; lem-box-cP-at04103143 ; lem-box-cP-at04122041 ; lem-box-cP-at0412233041 ; lem-box-cP-at0413203142 ; lem-box-cP-at0413213240 ; lem-box-cP-at0440 ; lem-box-perm-1324-at04203243 ; lem-pairs-at0410213243 ; lem-sym-bc-at04122041 ; lem-sym-bc-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CS13-CCZ024 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024 ; lem-comm-CX31-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-CCZ024-CX31 ; lem-comm-CS24-TOFF301 ; lem-comm-TOFF213-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CK02-TOFF413 ; lem-comm-CX40-TOFF213 ; lem-comm-TOFF213-CX40 ; lem-comm-TOFF413-CK02)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ124-CK03 ; lem-comm-CK03-CCZ124 ; lem-comm-CX20-TOFF413 ; lem-comm-TOFF413-CX20)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-4013 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (X0 ∷ CCZ024 ∷ []) (wp1284 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CZ24 ∷ Toff213 ∷ []) (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl1432 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ Toff213 ∷ []) (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ134 ∷ []) (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp0036 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CX31 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ024 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ024 ∷ []) (wp0746 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp0034 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ024 ∷ []) (wp1285 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ CZ24 ∷ CZ24 ∷ []) (X0 ∷ []) (wl1433 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ134 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (CS34⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (K3 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ K3⁻ ∷ []) (Toff301 ∷ []) (wl1380 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp0021 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ024 ∷ []) (wp0179 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp0039 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp0037 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff213 ∷ Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ Toff213 ∷ []) (wl1421 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ024 ∷ []) (wp0760 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CX40 ∷ Toff213 ∷ []) (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS01⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS01⁻ ∷ []) (wl1422 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff201 ∷ Toff213 ∷ []) (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ014 ∷ []) (Toff201 ∷ CCZ014 ∷ Toff201 ∷ []) (wp1275 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4))
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ Toff301 ∷ CS34 ∷ CCZ014 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ []) (wp1286 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0321 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ014 ∷ Toff301 ∷ CS34 ∷ []) (Toff301 ∷ CS34 ∷ CCZ014 ∷ []) (wp1276 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp0161 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CX13 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ []) (wl1434 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CX13 ∷ Toff301 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX13 ∷ Toff301 ∷ []) (wp1287 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CX12 ∷ CX13 ∷ Toff213 ∷ []) (Toff213 ∷ CX13 ∷ []) (wl0746 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (Toff201 ∷ Toff301 ∷ Toff213 ∷ []) (Toff213 ∷ Toff301 ∷ []) (wl1435 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ024 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ024 ∷ CX31 ∷ []) (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CX12 ∷ Toff213 ∷ []) (Toff213 ∷ CX12 ∷ []) (wl0748 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (Toff213 ∷ CX40 ∷ []) (CX40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX40 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ014 ∷ []) (CX12 ∷ CCZ014 ∷ CX12 ∷ []) (wp0655 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ014 ∷ CX13 ∷ CCZ014 ∷ Toff301 ∷ []) (CX13 ∷ Toff301 ∷ []) (wp1289 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff301 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ Toff301 ∷ []) (wl1436 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ []) (wl1437 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CS34 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34 ∷ []) (wp1290 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CS34⁻ ∷ X0 ∷ []) (X0 ∷ CS34⁻ ∷ []) (wl1438 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS34⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CS34⁻ ∷ []) (wp1291 c4)

-- F4-CS2-CS2 @0213243140: 286 steps
lem-F4-CS2-CS2-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS2-at0213243140 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 10 (q18 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw 11 (q25 c4) ∷
   rw 10 (q26 c4) ∷
   rw 9 (q25 c4) ∷
   rw 8 (q27 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 7 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 3 1 (CS34 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 4 (q30 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q30 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 6 (q23 c4) ∷
   rw 10 (q24 c4) ∷
   rw 9 (q25 c4) ∷
   rw 8 (q26 c4) ∷
   rw 7 (q25 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 5 (q28 c4) ∷
   rw⁻ 6 (q29 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw 10 (q32 c4) ∷
   rw 3 (q33 c4) ∷
   rw 5 (q34 c4) ∷
   re 4 1 (Sb2-4-3-1 ∷ []) ∷
   re 6 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 2 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 3 (q35 c4) ∷
   re 2 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 4 1 (CS34 ∷ []) ∷
   re 6 1 (CS34⁻ ∷ []) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 9 (q20 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q42 c4) ∷
   rw 12 (q18 c4) ∷
   rw 13 (q42 c4) ∷
   rw 14 (q17 c4) ∷
   rw 15 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 4 (q27 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q26 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q24 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 3 (q46 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q42 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q42 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q16 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 1 (q47 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 2 (q48 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   re 4 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 6 1 (CS34 ∷ []) ∷
   re 8 1 (CS34⁻ ∷ []) ∷
   rw⁻ 5 (q36 c4) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 11 (q20 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q42 c4) ∷
   rw 14 (q18 c4) ∷
   rw 15 (q42 c4) ∷
   rw 16 (q17 c4) ∷
   rw 17 (q16 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 7 (q23 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q26 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q26 c4) ∷
   rw 13 (q44 c4) ∷
   rw⁻ 14 (q24 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw⁻ 11 (q38 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 5 (q46 c4) ∷
   rw 4 (q40 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 5 (q20 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q42 c4) ∷
   rw 8 (q18 c4) ∷
   rw 9 (q42 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q16 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (Sb2-4-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 6 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   re 5 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 7 1 (CS34 ∷ []) ∷
   re 9 1 (CS34⁻ ∷ []) ∷
   rw⁻ 6 (q51 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (Sb2-4-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 6 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 4 (q50 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Bx2-0143 ∷ []) (Bx2-4301 ∷ []) (lem-pairs-at0210213443 c4)

-- box-perm-1423 @0214203143: 3 steps
lem-box-perm-1423-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-box-perm-1423-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-4301 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 0 (q54 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (S4 ∷ CS04⁻ ∷ X0 ∷ []) (X0 ∷ CS04 ∷ []) (wp1297 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (S4 ∷ CS04⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S4 ∷ CS04⁻ ∷ []) (wp1283 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (Toff213 ∷ S4 ∷ []) (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))
  q58 : Ws → Eqn
  q58 c4 = eqn (Toff213 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ024 ∷ S4 ∷ CS04⁻ ∷ []) (S4 ∷ CS04⁻ ∷ CCZ024 ∷ []) (wp1282 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (CS04 ∷ X0 ∷ []) (X0 ∷ S4 ∷ CS04⁻ ∷ []) (wp1298 c4)

-- F4-CS2-S2 @0213243140: 17 steps
lem-F4-CS2-S2-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-S2-at0213243140 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS04 ∷ []) (CS04 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw⁻ 2 (q55 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw⁻ 2 (q56 c4) ∷
   rw 1 (q1 c4) ∷
   rw 4 (q57 c4) ∷
   rw 5 (q58 c4) ∷
   rw 3 (q59 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q58 c4) ∷
   rw 1 (q59 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sb2-4-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 3 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 0 (q60 c4) ∷ []) Eq.refl

private
  q61 : Ws → Eqn
  q61 c4 = eqn (X0 ∷ S0 ∷ []) (ι ∷ S0⁻ ∷ X0 ∷ []) (wl1446 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (wp1301 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Toff213 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff213 ∷ []) (wl1447 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ024 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ CCZ024 ∷ []) (wp1302 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (S0 ∷ X0 ∷ []) (X0 ∷ ι ∷ S0⁻ ∷ []) (wl1448 (lit c4))

-- F4-CS2-I @0213243140: 15 steps
lem-F4-CS2-I-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-I-at0213243140 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw 2 (q61 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw 2 (q62 c4) ∷
   rw 1 (q1 c4) ∷
   rw 4 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw 2 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sb2-4-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 3 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q66 : Ws → Eqn
  q66 c4 = eqn (S1 ∷ CS01⁻ ∷ X0 ∷ []) (X0 ∷ CS01 ∷ []) (wl1451 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (S1 ∷ CS01⁻ ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ S1 ∷ CS01⁻ ∷ []) (wp1304 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (S1 ∷ CS01⁻ ∷ Toff213 ∷ []) (Toff213 ∷ S1 ∷ CS01⁻ ∷ []) (wl1452 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CCZ024 ∷ S1 ∷ CS01⁻ ∷ []) (S1 ∷ CS01⁻ ∷ CCZ024 ∷ []) (wp1305 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (CS01 ∷ X0 ∷ []) (X0 ∷ S1 ∷ CS01⁻ ∷ []) (wl1453 (lit c4))

-- F4-CS2-S3 @0213243140: 15 steps
lem-F4-CS2-S3-at0213243140 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-S3-at0213243140 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CS01 ∷ []) (CS01 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw⁻ 2 (q66 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw 1 (q69 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   re 5 1 (Sb2-4-3-1 ∷ []) ∷
   re 7 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 3 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 0 (q70 c4) ∷ []) Eq.refl

private
  q71 : Ws → Eqn
  q71 c4 = eqn (Bx4-2031 ∷ []) (Bx4-2301 ∷ []) (lem-sym-bc-at04122041 c4)

-- box-perm-1324 @04122041: 1 steps
lem-box-perm-1324-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-box-perm-1324-at04122041 c4 = derive (Bx4-2031 ∷ []) (Bx4-2301 ∷ [])
  (rw 0 (q71 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx4-2031 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CCZ024 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CCZ024 ∷ []) (wp1324 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (X0 ∷ Toff413 ∷ []) (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑))
  q75 : Ws → Eqn
  q75 c4 = eqn (CK02 ∷ Toff413 ∷ []) (Toff413 ∷ CK02 ∷ []) (lem-comm-CK02-TOFF413 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (wl1475 (lit c4))

-- F4-K2-CS2 @0440: 17 steps
lem-F4-K2-CS2-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-CS2-at0440 c4 = derive (X0 ∷ CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  (re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 0 (q73 c4) ∷
   rw 3 (q74 c4) ∷
   rw 2 (q75 c4) ∷
   rw 1 (q74 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw 5 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw 3 (q74 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q76 c4) ∷
   re 2 1 (Sb4-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 0 5 (Sb4-2-03-1 ∷ []) ∷ []) Eq.refl

private
  q77 : Ws → Eqn
  q77 c4 = eqn (Toff413 ∷ Bx4-0213 ∷ Toff413 ∷ []) (Bx4-0213 ∷ []) (lem-P-box-at04103143 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx4-0213 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04103143 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (Toff413 ∷ Toff413 ∷ []) [] (wl1474 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (Bx4-1302 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233042 c4)

-- pairs @04103143: 4 steps
lem-pairs-at04103143 : Ws → ⟪ (Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-pairs-at04103143 c4 = derive (Bx4-0213 ∷ []) (Bx4-1302 ∷ [])
  (rw⁻ 0 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 0 (q80 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (Bx4-1023 ∷ []) (Bx4-0123 ∷ []) (lem-sym-ab-at04203243 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (Bx4-0123 ∷ []) (Bx4-2301 ∷ []) (lem-pairs-at0410213243 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Bx4-2301 ∷ []) (Bx4-2031 ∷ []) (lem-sym-bc-at0412233041 c4)

-- box-perm-3241 @04203243: 3 steps
lem-box-perm-3241-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-box-perm-3241-at04203243 c4 = derive (Bx4-1023 ∷ []) (Bx4-2031 ∷ [])
  (rw 0 (q81 c4) ∷
   rw 0 (q82 c4) ∷
   rw 0 (q83 c4) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (Toff401 ∷ Bx4-2301 ∷ Toff401 ∷ []) (Bx4-2301 ∷ []) (lem-P-box-at0412233041 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx4-2301 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (Toff401 ∷ Toff401 ∷ []) [] (wp0306 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Bx4-0123 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4)

-- pairs @0412233041: 4 steps
lem-pairs-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ []) ⟫ʷ
lem-pairs-at0412233041 c4 = derive (Bx4-2301 ∷ []) (Bx4-0123 ∷ [])
  (rw⁻ 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ CCZ024 ∷ []) (wp1278 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff413 ∷ []) (wp1361 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (X0 ∷ S0 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (wl1535 (lit c4))
  q91 : Ws → Eqn
  q91 c4 = eqn (X0 ∷ S0 ∷ X0 ∷ []) (ι ∷ S0⁻ ∷ []) (wl1431 (lit c4))

-- F4-I-CS2 @0440: 15 steps
lem-F4-I-CS2-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS2-at0440 c4 = derive (X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 0 (q88 c4) ∷
   rw⁻ 1 (q89 c4) ∷
   rw⁻ 2 (q88 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q90 c4) ∷
   re 2 1 (Sb4-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 0 5 (Sb4-2-03-1 ∷ []) ∷
   rw 1 (q91 c4) ∷
   rw⁻ 1 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (wl1536 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (Toff413 ∷ ι ∷ S0⁻ ∷ []) (ι ∷ S0⁻ ∷ Toff413 ∷ []) (wp1362 c4)

-- F4-CS2-I @0440: 15 steps
lem-F4-CS2-I-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-I-at0440 c4 = derive (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  (rw 2 (q61 c4) ∷
   re 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 2 (q92 c4) ∷
   rw 1 (q72 c4) ∷
   rw 4 (q93 c4) ∷
   rw 3 (q64 c4) ∷
   rw 2 (q93 c4) ∷
   rw 1 (q64 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   re 5 1 (Sb4-2-1-3 ∷ []) ∷
   re 7 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 3 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 0 (q65 c4) ∷ []) Eq.refl

private
  q94 : Ws → Eqn
  q94 c4 = eqn (K2 ∷ CK02 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ []) (wl1487 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (K2 ∷ CK02 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K2 ∷ CK02 ∷ S0 ∷ []) (wl1537 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (K2 ∷ Toff413 ∷ []) (Toff413 ∷ K2 ∷ []) (wl1538 (lit c4))
  q97 : Ws → Eqn
  q97 c4 = eqn (Toff413 ∷ CK02 ∷ []) (CK02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CK02 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (S0 ∷ Toff413 ∷ []) (Toff413 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑))
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ024 ∷ K2 ∷ CK02 ∷ S0 ∷ []) (K2 ∷ CK02 ∷ S0 ∷ CCZ024 ∷ []) (wp1363 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CK02 ∷ X0 ∷ []) (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ []) (wl1490 (lit c4))

-- F4-CS2-K2 @0440: 19 steps
lem-F4-CS2-K2-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K2-at0440 c4 = derive (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  (rw⁻ 2 (q94 c4) ∷
   re 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q95 c4) ∷
   rw 1 (q72 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw 5 (q97 c4) ∷
   rw⁻ 6 (q98 c4) ∷
   rw 3 (q99 c4) ∷
   rw⁻ 2 (q96 c4) ∷
   rw 3 (q97 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw 1 (q99 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 0 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (CZ24 ∷ Toff413 ∷ []) (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4))
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp0081 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp0092 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ123 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CS12⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS12⁻ ∷ []) (wl1544 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (Toff103 ∷ []) (wl1545 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4)
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp0089 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ Toff103 ∷ []) (wp1373 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (CCZ024 ∷ Toff403 ∷ CCZ023 ∷ []) (Toff403 ∷ CCZ024 ∷ []) (wp1374 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4))
  q117 : Ws → Eqn
  q117 c4 = eqn (CS23 ∷ Toff413 ∷ []) (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CX20 ∷ Toff413 ∷ []) (Toff413 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF413 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (CS03⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS03⁻ ∷ []) (wp1375 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (CS03 ∷ Toff413 ∷ []) (Toff413 ∷ CS03 ∷ []) (wp1376 c4)
  q121 : Ws → Eqn
  q121 c4 = eqn (Toff403 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ []) (wp1377 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (CCZ023 ∷ []) (Toff403 ∷ CCZ023 ∷ Toff403 ∷ []) (wp1378 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CS12 ∷ Toff413 ∷ []) (Toff413 ∷ CS12 ∷ []) (wl1547 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (wl1548 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0181 (lit c4))
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ023 ∷ Toff103 ∷ CS12 ∷ []) (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) (wl1549 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (CCZ023 ∷ CCZ023 ∷ []) [] (wl0204 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (CX31 ∷ Toff103 ∷ X0 ∷ []) (X0 ∷ Toff103 ∷ []) (wl1505 (lit c4))
  q129 : Ws → Eqn
  q129 c4 = eqn (CX31 ∷ Toff103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX31 ∷ Toff103 ∷ []) (wl1550 (lit c4))
  q130 : Ws → Eqn
  q130 c4 = eqn (CX34 ∷ CX31 ∷ Toff413 ∷ []) (Toff413 ∷ CX31 ∷ []) (wl1551 (lit c4))
  q131 : Ws → Eqn
  q131 c4 = eqn (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff103 ∷ []) (wp1379 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CCZ024 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1380 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (CX34 ∷ Toff413 ∷ []) (Toff413 ∷ CX34 ∷ []) (wl1552 (lit c4))
  q135 : Ws → Eqn
  q135 c4 = eqn (Toff413 ∷ CX20 ∷ []) (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ023 ∷ []) (CX34 ∷ CCZ023 ∷ CX34 ∷ []) (wp1382 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ023 ∷ CX31 ∷ CCZ023 ∷ Toff103 ∷ []) (CX31 ∷ Toff103 ∷ []) (wl1553 (lit c4))
  q138 : Ws → Eqn
  q138 c4 = eqn (Toff103 ∷ X0 ∷ []) (X0 ∷ CX31 ∷ Toff103 ∷ []) (wl1510 (lit c4))
  q139 : Ws → Eqn
  q139 c4 = eqn (CS12 ∷ X0 ∷ []) (X0 ∷ CS12 ∷ []) (wl1511 (lit c4))
  q140 : Ws → Eqn
  q140 c4 = eqn (CS12 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12 ∷ []) (wl1554 (lit c4))
  q141 : Ws → Eqn
  q141 c4 = eqn (CS12⁻ ∷ X0 ∷ []) (X0 ∷ CS12⁻ ∷ []) (wl1513 (lit c4))
  q142 : Ws → Eqn
  q142 c4 = eqn (CS12⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS12⁻ ∷ []) (wl1555 (lit c4))

-- F4-CS2-CS2 @0440: 286 steps
lem-F4-CS2-CS2-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS2-at0440 c4 = derive (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  (re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q101 c4) ∷
   rw 3 (q74 c4) ∷
   rw 6 (q102 c4) ∷
   rw⁻ 10 (q103 c4) ∷
   rw 9 (q104 c4) ∷
   rw⁻ 8 (q105 c4) ∷
   rw 7 (q104 c4) ∷
   rw⁻ 6 (q106 c4) ∷
   rw⁻ 7 (q102 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q107 c4) ∷
   rw 5 (q74 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   re 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 6 (q72 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw 8 (q109 c4) ∷
   rw⁻ 5 (q72 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw⁻ 10 (q111 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 8 (q104 c4) ∷
   rw⁻ 7 (q112 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw 5 (q110 c4) ∷
   rw 5 (q114 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw⁻ 13 (q111 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw 11 (q104 c4) ∷
   rw⁻ 10 (q112 c4) ∷
   rw 9 (q104 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw⁻ 7 (q113 c4) ∷
   rw 8 (q110 c4) ∷
   rw⁻ 6 (q115 c4) ∷
   rw 9 (q114 c4) ∷
   rw 8 (q116 c4) ∷
   rw 12 (q117 c4) ∷
   rw 11 (q118 c4) ∷
   rw 10 (q119 c4) ∷
   rw 9 (q118 c4) ∷
   rw 8 (q120 c4) ∷
   rw⁻ 9 (q116 c4) ∷
   rw 7 (q121 c4) ∷
   rw⁻ 8 (q122 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw 4 (q72 c4) ∷
   rw⁻ 3 (q103 c4) ∷
   rw 4 (q123 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw 6 (q123 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 2 (q110 c4) ∷
   rw⁻ 8 (q111 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q112 c4) ∷
   rw 4 (q104 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw⁻ 2 (q113 c4) ∷
   rw 3 (q110 c4) ∷
   rw 3 (q114 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw⁻ 11 (q111 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 9 (q104 c4) ∷
   rw⁻ 8 (q112 c4) ∷
   rw 7 (q104 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw⁻ 5 (q113 c4) ∷
   rw 6 (q110 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   rw 7 (q114 c4) ∷
   rw 6 (q116 c4) ∷
   rw 10 (q117 c4) ∷
   rw 9 (q118 c4) ∷
   rw 8 (q119 c4) ∷
   rw 7 (q118 c4) ∷
   rw 6 (q120 c4) ∷
   rw⁻ 7 (q116 c4) ∷
   rw 5 (q121 c4) ∷
   rw⁻ 6 (q122 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 1 (q72 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q101 c4) ∷
   rw 1 (q74 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 8 (q103 c4) ∷
   rw 7 (q104 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q107 c4) ∷
   rw 3 (q74 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw 3 (q72 c4) ∷
   rw 2 (q102 c4) ∷
   rw⁻ 6 (q103 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 4 (q105 c4) ∷
   rw 3 (q104 c4) ∷
   rw⁻ 2 (q106 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw 3 (q107 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 8 (q103 c4) ∷
   rw 7 (q104 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 4 (q106 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw 5 (q107 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw⁻ 3 (q124 c4) ∷
   rw 10 (q125 c4) ∷
   rw 3 (q126 c4) ∷
   rw 5 (q127 c4) ∷
   re 4 1 (Sb4-2-1-3 ∷ []) ∷
   re 6 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 2 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 3 (q128 c4) ∷
   re 2 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 6 1 (CS12⁻ ∷ []) ∷
   rw⁻ 3 (q129 c4) ∷
   rw 2 (q72 c4) ∷
   rw⁻ 5 (q130 c4) ∷
   rw⁻ 7 (q131 c4) ∷
   rw 4 (q132 c4) ∷
   rw 6 (q42 c4) ∷
   rw 7 (q133 c4) ∷
   rw⁻ 10 (q110 c4) ∷
   rw 9 (q113 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q40 c4) ∷
   rw 12 (q112 c4) ∷
   rw 13 (q40 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q111 c4) ∷
   rw 9 (q110 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw 5 (q116 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw 5 (q135 c4) ∷
   rw⁻ 6 (q119 c4) ∷
   rw 7 (q135 c4) ∷
   rw⁻ 8 (q117 c4) ∷
   rw⁻ 4 (q116 c4) ∷
   rw⁻ 5 (q130 c4) ∷
   rw⁻ 7 (q121 c4) ∷
   rw 9 (q116 c4) ∷
   rw⁻ 8 (q120 c4) ∷
   rw 9 (q135 c4) ∷
   rw⁻ 10 (q119 c4) ∷
   rw 11 (q135 c4) ∷
   rw⁻ 12 (q117 c4) ∷
   rw⁻ 8 (q116 c4) ∷
   rw⁻ 9 (q131 c4) ∷
   rw⁻ 3 (q136 c4) ∷
   rw⁻ 5 (q122 c4) ∷
   rw 3 (q137 c4) ∷
   rw 2 (q42 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw 3 (q113 c4) ∷
   rw 4 (q17 c4) ∷
   rw 5 (q40 c4) ∷
   rw 6 (q112 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q111 c4) ∷
   rw 3 (q110 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 1 (q138 c4) ∷
   rw⁻ 4 (q139 c4) ∷
   re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q140 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw 5 (q103 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   rw 3 (q103 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 2 (q139 c4) ∷
   rw⁻ 5 (q128 c4) ∷
   re 4 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 6 1 (CS12 ∷ []) ∷
   re 8 1 (CS12⁻ ∷ []) ∷
   rw⁻ 5 (q129 c4) ∷
   rw 4 (q72 c4) ∷
   rw⁻ 7 (q130 c4) ∷
   rw⁻ 9 (q131 c4) ∷
   rw 6 (q132 c4) ∷
   rw 8 (q42 c4) ∷
   rw 9 (q133 c4) ∷
   rw⁻ 12 (q110 c4) ∷
   rw 11 (q113 c4) ∷
   rw 12 (q17 c4) ∷
   rw 13 (q40 c4) ∷
   rw 14 (q112 c4) ∷
   rw 15 (q40 c4) ∷
   rw 16 (q19 c4) ∷
   rw 17 (q111 c4) ∷
   rw 11 (q110 c4) ∷
   rw⁻ 5 (q134 c4) ∷
   rw 7 (q116 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   rw 7 (q135 c4) ∷
   rw⁻ 8 (q119 c4) ∷
   rw 9 (q135 c4) ∷
   rw⁻ 10 (q117 c4) ∷
   rw⁻ 6 (q116 c4) ∷
   rw⁻ 7 (q130 c4) ∷
   rw⁻ 9 (q121 c4) ∷
   rw 11 (q116 c4) ∷
   rw⁻ 10 (q120 c4) ∷
   rw 11 (q135 c4) ∷
   rw⁻ 12 (q119 c4) ∷
   rw 13 (q135 c4) ∷
   rw⁻ 14 (q117 c4) ∷
   rw⁻ 10 (q116 c4) ∷
   rw⁻ 11 (q131 c4) ∷
   rw⁻ 5 (q136 c4) ∷
   rw⁻ 7 (q122 c4) ∷
   rw 5 (q137 c4) ∷
   rw 4 (q42 c4) ∷
   rw⁻ 6 (q110 c4) ∷
   rw 5 (q113 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q40 c4) ∷
   rw 8 (q112 c4) ∷
   rw 9 (q40 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q111 c4) ∷
   rw 5 (q110 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   re 8 1 (Sb4-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 6 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 3 (q138 c4) ∷
   rw⁻ 6 (q141 c4) ∷
   re 5 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw⁻ 6 (q142 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 8 (q109 c4) ∷
   rw 7 (q108 c4) ∷
   rw⁻ 6 (q109 c4) ∷
   rw 5 (q108 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   re 8 1 (Sb4-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 6 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 4 (q141 c4) ∷
   re 2 1 (Sb4-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 0 5 (Sb4-2-03-1 ∷ []) ∷ []) Eq.refl

private
  q143 : Ws → Eqn
  q143 c4 = eqn (Bx4-1023 ∷ []) (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (Bx4-1203 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (X0 ∷ CCZ124 ∷ []) (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q146 : Ws → Eqn
  q146 c4 = eqn (CK03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ []) (wp1384 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (wl1561 (lit c4))

-- F4-K3-CS1 @0440: 19 steps
lem-F4-K3-CS1-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS1-at0440 c4 = derive (X0 ∷ CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  (re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q143 c4) ∷
   rw 3 (q144 c4) ∷
   rw 2 (q145 c4) ∷
   rw 1 (q146 c4) ∷
   rw 0 (q145 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 4 (q145 c4) ∷
   rw 3 (q146 c4) ∷
   rw 2 (q145 c4) ∷
   rw⁻ 3 (q147 c4) ∷
   rw⁻ 0 (q144 c4) ∷
   rw⁻ 0 (q143 c4) ∷
   rw⁻ 1 (q148 c4) ∷
   re 2 1 (Sb4-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = eqn (Toff412 ∷ Bx4-0321 ∷ Toff412 ∷ []) (Bx4-0321 ∷ []) (lem-P-box-at0410233241 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (Bx4-0321 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-box-cP-at0410233241 c4)
  q151 : Ws → Eqn
  q151 c4 = eqn (Toff412 ∷ Toff412 ∷ []) [] (wl0470 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (Bx4-2103 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0412213043 c4)

-- pairs @0410233241: 4 steps
lem-pairs-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2103 ∷ []) ⟫ʷ
lem-pairs-at0410233241 c4 = derive (Bx4-0321 ∷ []) (Bx4-2103 ∷ [])
  (rw⁻ 0 (q149 c4) ∷
   rw 1 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ []) (wl1574 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wl1581 (lit c4))
  q155 : Ws → Eqn
  q155 c4 = eqn (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (Toff403 ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wp1393 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ124 ∷ K3 ∷ []) (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (CCZ124 ∷ CK03 ∷ []) (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (S0 ∷ CCZ124 ∷ []) (CCZ124 ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q159 : Ws → Eqn
  q159 c4 = eqn (CK03 ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ []) (wl1577 (lit c4))

-- F4-CS1-K3 @0440: 21 steps
lem-F4-CS1-K3-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-K3-at0440 c4 = derive (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK03 ∷ []) (CK03 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  (rw⁻ 2 (q153 c4) ∷
   re 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q154 c4) ∷
   rw 1 (q143 c4) ∷
   rw 1 (q144 c4) ∷
   rw⁻ 4 (q155 c4) ∷
   rw 3 (q156 c4) ∷
   rw 4 (q157 c4) ∷
   rw⁻ 5 (q158 c4) ∷
   rw⁻ 2 (q155 c4) ∷
   rw 1 (q156 c4) ∷
   rw 2 (q157 c4) ∷
   rw⁻ 3 (q158 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw⁻ 4 (q143 c4) ∷
   re 6 1 (Sb4-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 4 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 0 (q159 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = eqn (CS12⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) (wl0968 (lit c4))
  q161 : Ws → Eqn
  q161 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (CCZ024 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ []) (wp0749 c4)
  q163 : Ws → Eqn
  q163 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q164 : Ws → Eqn
  q164 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ123 ∷ Toff213 ∷ []) (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl0965 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = eqn (CS13⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS13⁻ ∷ []) (wl0969 (lit c4))
  q167 : Ws → Eqn
  q167 c4 = eqn (CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ CS13⁻ ∷ CZ13 ∷ CCZ123 ∷ []) (CS12⁻ ∷ []) (wl0970 (lit c4))

-- CSdu-box-3 @0214203143: 17 steps
lem-CSdu-box-3-at0214203143 : Ws → ⟪ (CS12⁻ ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0214203143 c4 = derive (CS12⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CS12⁻ ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q108 c4) ∷
   rw 1 (q160 c4) ∷
   rw 4 (q161 c4) ∷
   rw⁻ 8 (q106 c4) ∷
   rw⁻ 7 (q162 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q162 c4) ∷
   rw 4 (q164 c4) ∷
   rw⁻ 5 (q161 c4) ∷
   rw 3 (q163 c4) ∷
   rw⁻ 2 (q108 c4) ∷
   rw 5 (q165 c4) ∷
   rw 4 (q166 c4) ∷
   rw 3 (q160 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q168 : Ws → Eqn
  q168 c4 = eqn (CS12 ∷ Toff213 ∷ []) (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) (wl0964 (lit c4))
  q169 : Ws → Eqn
  q169 c4 = eqn (CS13 ∷ Toff213 ∷ []) (Toff213 ∷ CS13 ∷ []) (wl0966 (lit c4))
  q170 : Ws → Eqn
  q170 c4 = eqn (CS12 ∷ CS13 ∷ CCZ123 ∷ CS13 ∷ CZ13 ∷ CCZ123 ∷ []) (CS12 ∷ []) (wl0967 (lit c4))

-- CSu-box-3 @0214203143: 17 steps
lem-CSu-box-3-at0214203143 : Ws → ⟪ (CS12 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CS12 ∷ []) ⟫ʷ
lem-CSu-box-3-at0214203143 c4 = derive (CS12 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CS12 ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q103 c4) ∷
   rw 1 (q168 c4) ∷
   rw 4 (q161 c4) ∷
   rw⁻ 8 (q106 c4) ∷
   rw⁻ 7 (q162 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q162 c4) ∷
   rw 4 (q164 c4) ∷
   rw⁻ 5 (q161 c4) ∷
   rw 3 (q164 c4) ∷
   rw⁻ 2 (q103 c4) ∷
   rw 5 (q165 c4) ∷
   rw 4 (q169 c4) ∷
   rw 3 (q168 c4) ∷
   rw 4 (q170 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = eqn (Toff413 ∷ Bx4-2031 ∷ Toff413 ∷ []) (Bx4-2031 ∷ []) (lem-P-box-at04122041 c4)
  q172 : Ws → Eqn
  q172 c4 = eqn (Bx4-3120 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at0413213240 c4)

-- pairs @04122041: 4 steps
lem-pairs-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-pairs-at04122041 c4 = derive (Bx4-2031 ∷ []) (Bx4-3120 ∷ [])
  (rw⁻ 0 (q171 c4) ∷
   rw 1 (q72 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 0 (q172 c4) ∷ []) Eq.refl

private
  q173 : Ws → Eqn
  q173 c4 = eqn (Toff403 ∷ Bx4-1230 ∷ Toff403 ∷ []) (Bx4-1230 ∷ []) (lem-P-box-at0440 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (Bx4-1230 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0440 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (Toff403 ∷ Toff403 ∷ []) [] (wp0317 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx4-3012 ∷ []) (Toff403 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ []) (lem-box-tQ-at0413203142 c4)

-- pairs @0440: 4 steps
lem-pairs-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-pairs-at0440 c4 = derive (Bx4-1230 ∷ []) (Bx4-3012 ∷ [])
  (rw⁻ 0 (q173 c4) ∷
   rw 1 (q174 c4) ∷
   rw 4 (q175 c4) ∷
   rw⁻ 0 (q176 c4) ∷ []) Eq.refl

private
  q177 : Ws → Eqn
  q177 c4 = eqn (Toff412 ∷ Bx4-3012 ∷ Toff412 ∷ []) (Bx4-3012 ∷ []) (lem-P-box-at0413203142 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (Bx4-3012 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) (lem-box-cP-at0413203142 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (Bx4-1230 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at0440 c4)

-- pairs @0413203142: 4 steps
lem-pairs-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-pairs-at0413203142 c4 = derive (Bx4-3012 ∷ []) (Bx4-1230 ∷ [])
  (rw⁻ 0 (q177 c4) ∷
   rw 1 (q178 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 0 (q179 c4) ∷ []) Eq.refl

private
  q180 : Ws → Eqn
  q180 c4 = eqn (Toff402 ∷ Bx4-3120 ∷ Toff402 ∷ []) (Bx4-3120 ∷ []) (lem-P-box-at0413213240 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (Bx4-3120 ∷ []) (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at0413213240 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (Toff402 ∷ Toff402 ∷ []) [] (wp1323 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (Bx4-2031 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) (lem-box-tQ-at04122041 c4)

-- pairs @0413213240: 4 steps
lem-pairs-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-pairs-at0413213240 c4 = derive (Bx4-3120 ∷ []) (Bx4-2031 ∷ [])
  (rw⁻ 0 (q180 c4) ∷
   rw 1 (q181 c4) ∷
   rw 4 (q182 c4) ∷
   rw⁻ 0 (q183 c4) ∷ []) Eq.refl

private
  q184 : Ws → Eqn
  q184 c4 = eqn (CS34 ∷ Toff413 ∷ []) (Toff413 ∷ CS34 ∷ CS13 ∷ CCZ134 ∷ []) (wl1615 (lit c4))
  q185 : Ws → Eqn
  q185 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4))
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) (wp0914 c4)
  q187 : Ws → Eqn
  q187 c4 = eqn (CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1616 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (CS13 ∷ Toff413 ∷ []) (Toff413 ∷ CS13 ∷ []) (wl1502 (lit c4))
  q189 : Ws → Eqn
  q189 c4 = eqn (CS34 ∷ CS13 ∷ CCZ134 ∷ CS13 ∷ CZ13 ∷ CCZ134 ∷ []) (CS34 ∷ []) (wl1617 (lit c4))

-- CSu-box-3 @04122041: 17 steps
lem-CSu-box-3-at04122041 : Ws → ⟪ (CS34 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CS34 ∷ []) ⟫ʷ
lem-CSu-box-3-at04122041 c4 = derive (CS34 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ CS34 ∷ [])
  (rw 1 (q72 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw 1 (q184 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 7 (q186 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q186 c4) ∷
   rw 4 (q164 c4) ∷
   rw⁻ 5 (q185 c4) ∷
   rw 3 (q164 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 5 (q187 c4) ∷
   rw 4 (q188 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q190 : Ws → Eqn
  q190 c4 = eqn (CS34⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ []) (wl1618 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CS13⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS13⁻ ∷ []) (wl1500 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CS34⁻ ∷ CS13⁻ ∷ CCZ134 ∷ CS13⁻ ∷ CZ13 ∷ CCZ134 ∷ []) (CS34⁻ ∷ []) (wl1619 (lit c4))

-- CSdu-box-3 @04122041: 17 steps
lem-CSdu-box-3-at04122041 : Ws → ⟪ (CS34⁻ ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ CS34⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at04122041 c4 = derive (CS34⁻ ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ CS34⁻ ∷ [])
  (rw 1 (q72 c4) ∷
   rw⁻ 0 (q13 c4) ∷
   rw 1 (q190 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 8 (q9 c4) ∷
   rw⁻ 7 (q186 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 5 (q186 c4) ∷
   rw 4 (q164 c4) ∷
   rw⁻ 5 (q185 c4) ∷
   rw 3 (q163 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 5 (q187 c4) ∷
   rw 4 (q191 c4) ∷
   rw 3 (q190 c4) ∷
   rw 4 (q192 c4) ∷
   rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = eqn (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (CCZ024 ∷ K2 ∷ []) (K2 ∷ Toff204 ∷ []) (wp0536 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (K2 ∷ CCZ123 ∷ []) (Toff213 ∷ K2 ∷ []) (wl0662 (lit c4))

-- Ku-box @0214203143: 6 steps
lem-Ku-box-at0214203143 : Ws → ⟪ (K2 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ K2 ∷ []) ⟫ʷ
lem-Ku-box-at0214203143 c4 = derive (K2 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2 ∷ [])
  (rw 1 (q193 c4) ∷
   rw⁻ 0 (q194 c4) ∷
   rw 1 (q195 c4) ∷
   rw⁻ 2 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = eqn (CCZ024 ∷ K2⁻ ∷ []) (K2⁻ ∷ Toff204 ∷ []) (wp0537 c4)
  q197 : Ws → Eqn
  q197 c4 = eqn (K2⁻ ∷ CCZ123 ∷ []) (Toff213 ∷ K2⁻ ∷ []) (wl0663 (lit c4))

-- Kdu-box @0214203143: 6 steps
lem-Kdu-box-at0214203143 : Ws → ⟪ (K2⁻ ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ K2⁻ ∷ []) ⟫ʷ
lem-Kdu-box-at0214203143 c4 = derive (K2⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2⁻ ∷ [])
  (rw 1 (q193 c4) ∷
   rw⁻ 0 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw⁻ 2 (q196 c4) ∷
   rw 3 (q197 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

-- box-perm-2314 @0214203143: 2 steps
lem-box-perm-2314-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-2314-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-0143 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷ []) Eq.refl

private
  q198 : Ws → Eqn
  q198 c4 = eqn (Bx2-4301 ∷ []) (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4)

-- box-perm-4312 @0210213443: 2 steps
lem-box-perm-4312-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-box-perm-4312-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Bx2-3401 ∷ [])
  (rw 0 (q54 c4) ∷
   rw 0 (q198 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (Bx2-3401 ∷ []) (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4)
  q200 : Ws → Eqn
  q200 c4 = eqn (Bx2-4301 ∷ []) (Bx2-0143 ∷ []) (lem-pairs-at0214233041 c4)

-- box-perm-3421 @0213243041: 2 steps
lem-box-perm-3421-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-3421-at0213243041 c4 = derive (Bx2-3401 ∷ []) (Bx2-0143 ∷ [])
  (rw 0 (q199 c4) ∷
   rw 0 (q200 c4) ∷ []) Eq.refl

private
  q201 : Ws → Eqn
  q201 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4)
  q202 : Ws → Eqn
  q202 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4)

-- box-perm-2314 @0314203142: 2 steps
lem-box-perm-2314-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-box-perm-2314-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-0142 ∷ [])
  (rw 0 (q201 c4) ∷
   rw 0 (q202 c4) ∷ []) Eq.refl

private
  q203 : Ws → Eqn
  q203 c4 = eqn (CX23 ∷ Toff301 ∷ []) (Toff301 ∷ CX23 ∷ []) (wl1646 (lit c4))
  q204 : Ws → Eqn
  q204 c4 = eqn (CS34 ∷ CS24 ∷ CCZ234 ∷ CX23 ∷ []) (CX23 ∷ CS34 ∷ []) (wl1647 (lit c4))
  q205 : Ws → Eqn
  q205 c4 = eqn (CS34⁻ ∷ CS24⁻ ∷ CCZ234 ∷ CX23 ∷ []) (CX23 ∷ CS34⁻ ∷ []) (wl1648 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ234 ∷ CS24 ∷ []) (CS24 ∷ CCZ234 ∷ []) (wl1649 (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (CS24 ∷ Toff301 ∷ []) (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4))
  q208 : Ws → Eqn
  q208 c4 = eqn (CS24 ∷ CS34⁻ ∷ CS24⁻ ∷ []) (CS34⁻ ∷ []) (wl1650 (lit c4))
  q209 : Ws → Eqn
  q209 c4 = eqn (Toff301 ∷ Toff301 ∷ []) [] (wl0443 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (CCZ234 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ234 ∷ []) (wl1651 (lit c4))
  q211 : Ws → Eqn
  q211 c4 = eqn (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4)
  q212 : Ws → Eqn
  q212 c4 = eqn (CS34⁻ ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CS34⁻ ∷ []) (lem-CSdu-box-3-at0310213442 c4)

-- F0-R @0410213243: 11 steps
lem-F0-R-at0410213243 : Ws → ⟪ (CX23 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Bx3-0142 ∷ CX23 ∷ []) ⟫ʷ
lem-F0-R-at0410213243 c4 = derive (CX23 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Bx3-0142 ∷ CX23 ∷ [])
  (rw 0 (q203 c4) ∷
   rw⁻ 1 (q204 c4) ∷
   rw 4 (q203 c4) ∷
   rw⁻ 5 (q205 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw 3 (q207 c4) ∷
   rw 4 (q208 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw⁻ 6 (q210 c4) ∷
   rw⁻ 3 (q211 c4) ∷
   rw⁻ 3 (q212 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (CCZ024 ∷ CX32 ∷ CCZ034 ∷ []) (CX32 ∷ CCZ024 ∷ []) (wp0717 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp0320 c4)
  q215 : Ws → Eqn
  q215 c4 = eqn (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4))
  q216 : Ws → Eqn
  q216 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4))
  q217 : Ws → Eqn
  q217 c4 = eqn (CX32 ∷ Toff213 ∷ []) (Toff213 ∷ CX32 ∷ []) (wl0809 (lit c4))
  q218 : Ws → Eqn
  q218 c4 = eqn (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4)
  q219 : Ws → Eqn
  q219 c4 = eqn (CX32 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX32 ∷ []) (wp0718 c4)

-- CXu-box-4 @0214203143: 15 steps
lem-CXu-box-4-at0214203143 : Ws → ⟪ (CX32 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CX32 ∷ []) ⟫ʷ
lem-CXu-box-4-at0214203143 c4 = derive (CX32 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CX32 ∷ [])
  (rw 1 (q1 c4) ∷
   rw⁻ 0 (q213 c4) ∷
   rw 2 (q214 c4) ∷
   rw 6 (q30 c4) ∷
   rw 5 (q25 c4) ∷
   rw 4 (q215 c4) ∷
   rw 3 (q25 c4) ∷
   rw 2 (q216 c4) ∷
   rw⁻ 3 (q214 c4) ∷
   rw 1 (q217 c4) ∷
   rw⁻ 3 (q218 c4) ∷
   rw⁻ 2 (q213 c4) ∷
   rw 3 (q219 c4) ∷
   rw 3 (q217 c4) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (Bx3-4012 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (CCZ034 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4)
  q222 : Ws → Eqn
  q222 c4 = eqn (CS13⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl0885 (lit c4))
  q223 : Ws → Eqn
  q223 c4 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4))
  q224 : Ws → Eqn
  q224 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp0314 c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (CCZ034 ∷ CX31 ∷ []) (CX31 ∷ CCZ034 ∷ []) (wp0127 c4)
  q226 : Ws → Eqn
  q226 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q227 : Ws → Eqn
  q227 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q228 : Ws → Eqn
  q228 c4 = eqn (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4))
  q229 : Ws → Eqn
  q229 c4 = eqn (CS12⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS12⁻ ∷ []) (wl0886 (lit c4))
  q230 : Ws → Eqn
  q230 c4 = eqn (CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ CS12⁻ ∷ CZ12 ∷ CCZ123 ∷ []) (CS13⁻ ∷ []) (wl0887 (lit c4))

-- CSdu-box-3 @0314203142: 17 steps
lem-CSdu-box-3-at0314203142 : Ws → ⟪ (CS13⁻ ∷ Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0314203142 c4 = derive (CS13⁻ ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CS13⁻ ∷ [])
  (rw 1 (q220 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   rw 4 (q223 c4) ∷
   rw⁻ 8 (q224 c4) ∷
   rw⁻ 7 (q225 c4) ∷
   rw 6 (q226 c4) ∷
   rw⁻ 5 (q225 c4) ∷
   rw 4 (q227 c4) ∷
   rw⁻ 5 (q223 c4) ∷
   rw 3 (q226 c4) ∷
   rw⁻ 2 (q221 c4) ∷
   rw 5 (q228 c4) ∷
   rw 4 (q229 c4) ∷
   rw 3 (q222 c4) ∷
   rw 4 (q230 c4) ∷
   rw⁻ 0 (q220 c4) ∷ []) Eq.refl
