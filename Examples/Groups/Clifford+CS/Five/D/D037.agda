{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD037 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D037 (Sᴰ : SD037) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS12-CCZ034 : Ws → St 191
  lem-comm-CS12-CCZ034 = pickᴰ 0 Sᴰ
  lem-comm-CS23-CCZ014 : Ws → St 703
  lem-comm-CS23-CCZ014 = pickᴰ 1 Sᴰ
  lem-comm-CS24-CCZ013 : Ws → St 194
  lem-comm-CS24-CCZ013 = pickᴰ 2 Sᴰ
  lem-comm-CSd12-CCZ034 : Ws → St 199
  lem-comm-CSd12-CCZ034 = pickᴰ 3 Sᴰ
  lem-comm-CSd23-CCZ014 : Ws → St 704
  lem-comm-CSd23-CCZ014 = pickᴰ 4 Sᴰ
  lem-comm-CSd24-CCZ013 : Ws → St 204
  lem-comm-CSd24-CCZ013 = pickᴰ 5 Sᴰ
  lem-comm-CX02-TOFF134 : Ws → St 1464
  lem-comm-CX02-TOFF134 = pickᴰ 6 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 7 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 8 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 9 Sᴰ
  lem-comm-CZ03-TOFF412 : Ws → St 373
  lem-comm-CZ03-TOFF412 = pickᴰ 10 Sᴰ
  lem-comm-CCZ013-CK42 : Ws → St 1465
  lem-comm-CCZ013-CK42 = pickᴰ 11 Sᴰ
  lem-comm-CK41-CCZ023 : Ws → St 1221
  lem-comm-CK41-CCZ023 = pickᴰ 12 Sᴰ
  lem-comm-CK42-CCZ013 : Ws → St 1466
  lem-comm-CK42-CCZ013 = pickᴰ 13 Sᴰ
  lem-comm-CS14-CCZ023 : Ws → St 219
  lem-comm-CS14-CCZ023 = pickᴰ 14 Sᴰ
  lem-comm-CSd14-CCZ023 : Ws → St 224
  lem-comm-CSd14-CCZ023 = pickᴰ 15 Sᴰ
  lem-comm-CX04-TOFF312 : Ws → St 1025
  lem-comm-CX04-TOFF312 = pickᴰ 16 Sᴰ
  lem-comm-CX31-TOFF024 : Ws → St 1069
  lem-comm-CX31-TOFF024 = pickᴰ 17 Sᴰ
  lem-comm-CZ02-TOFF314 : Ws → St 337
  lem-comm-CZ02-TOFF314 = pickᴰ 18 Sᴰ
  lem-comm-CCZ023-CK41 : Ws → St 1224
  lem-comm-CCZ023-CK41 = pickᴰ 19 Sᴰ
  lem-box-tQ-at0214213043 : Ws → St 250
  lem-box-tQ-at0214213043 = pickᴰ 20 Sᴰ
  lem-box-tQ-at0314213042 : Ws → St 311
  lem-box-tQ-at0314213042 = pickᴰ 21 Sᴰ
  lem-box-tQ-at0330 : Ws → St 252
  lem-box-tQ-at0330 = pickᴰ 22 Sᴰ
  lem-box-tQ-at033440 : Ws → St 340
  lem-box-tQ-at033440 = pickᴰ 23 Sᴰ
  lem-box-tQ-at043043 : Ws → St 253
  lem-box-tQ-at043043 = pickᴰ 24 Sᴰ
  lem-box-tQ-at12233441 : Ws → St 312
  lem-box-tQ-at12233441 = pickᴰ 25 Sᴰ
  lem-box-tQ-at233442 : Ws → St 342
  lem-box-tQ-at233442 = pickᴰ 26 Sᴰ
  lem-box-tQ-at3443 : Ws → St 264
  lem-box-tQ-at3443 = pickᴰ 27 Sᴰ
  lem-box-cP-at021021 : Ws → St 863
  lem-box-cP-at021021 = pickᴰ 28 Sᴰ
  lem-box-cP-at03102132 : Ws → St 867
  lem-box-cP-at03102132 = pickᴰ 29 Sᴰ
  lem-box-cP-at04203243 : Ws → St 919
  lem-box-cP-at04203243 = pickᴰ 30 Sᴰ
  lem-box-cP-at0110 : Ws → St 1467
  lem-box-cP-at0110 = pickᴰ 31 Sᴰ
  lem-box-cP-at0210233441 : Ws → St 1042
  lem-box-cP-at0210233441 = pickᴰ 32 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 994
  lem-box-cP-at0210243143 = pickᴰ 33 Sᴰ
  lem-box-cP-at0314203142 : Ws → St 997
  lem-box-cP-at0314203142 = pickᴰ 34 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 35 Sᴰ
  lem-box-cP-at132132 : Ws → St 1003
  lem-box-cP-at132132 = pickᴰ 36 Sᴰ
  lem-box-cP-at233442 : Ws → St 1129
  lem-box-cP-at233442 = pickᴰ 37 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 38 Sᴰ
  lem-box-perm-2314-at0410213243 : Ws → St 1468
  lem-box-perm-2314-at0410213243 = pickᴰ 39 Sᴰ
  lem-Kdu-box : Ws → St 1243
  lem-Kdu-box = pickᴰ 40 Sᴰ
  lem-Ku-box : Ws → St 1247
  lem-Ku-box = pickᴰ 41 Sᴰ
  lem-Ku-box-at0210243143 : Ws → St 1248
  lem-Ku-box-at0210243143 = pickᴰ 42 Sᴰ
  lem-Ku-box-at122441 : Ws → St 1249
  lem-Ku-box-at122441 = pickᴰ 43 Sᴰ
  lem-Ku-box-at243243 : Ws → St 1250
  lem-Ku-box-at243243 = pickᴰ 44 Sᴰ
  lem-box-box-4-at0410213243 : Ws → St 1469
  lem-box-box-4-at0410213243 = pickᴰ 45 Sᴰ
  lem-box-perm-1324-at043043 : Ws → St 1470
  lem-box-perm-1324-at043043 = pickᴰ 46 Sᴰ
  lem-box-perm-1423-at233442 : Ws → St 1471
  lem-box-perm-1423-at233442 = pickᴰ 47 Sᴰ
  lem-box-perm-3124-at043043 : Ws → St 1472
  lem-box-perm-3124-at043043 = pickᴰ 48 Sᴰ
  lem-box-perm-4123-at12233441 : Ws → St 1473
  lem-box-perm-4123-at12233441 = pickᴰ 49 Sᴰ
  lem-box-box-4-at0310243142 : Ws → St 1474
  lem-box-box-4-at0310243142 = pickᴰ 50 Sᴰ
  lem-box-perm-1324-at0314213042 : Ws → St 1475
  lem-box-perm-1324-at0314213042 = pickᴰ 51 Sᴰ
  lem-box-perm-2314-at0310243142 : Ws → St 1476
  lem-box-perm-2314-at0310243142 = pickᴰ 52 Sᴰ
  lem-box-perm-2341-at03102132 : Ws → St 1477
  lem-box-perm-2341-at03102132 = pickᴰ 53 Sᴰ
  lem-box-perm-3124-at0314213042 : Ws → St 1478
  lem-box-perm-3124-at0314213042 = pickᴰ 54 Sᴰ
  lem-CKdu-box-1 : Ws → St 1479
  lem-CKdu-box-1 = pickᴰ 55 Sᴰ
  lem-CKdu-box-2 : Ws → St 1480
  lem-CKdu-box-2 = pickᴰ 56 Sᴰ
  lem-CKdu-box-2-at0210243143 : Ws → St 1481
  lem-CKdu-box-2-at0210243143 = pickᴰ 57 Sᴰ
  lem-CKdu-box-2-at122441 : Ws → St 1482
  lem-CKdu-box-2-at122441 = pickᴰ 58 Sᴰ
  lem-CKdu-box-2-at243243 : Ws → St 1483
  lem-CKdu-box-2-at243243 = pickᴰ 59 Sᴰ
  lem-CKdu-box-3 : Ws → St 1484
  lem-CKdu-box-3 = pickᴰ 60 Sᴰ
  lem-CKdu-box-4 : Ws → St 1485
  lem-CKdu-box-4 = pickᴰ 61 Sᴰ
  lem-CKu-box-1 : Ws → St 1486
  lem-CKu-box-1 = pickᴰ 62 Sᴰ
  lem-CKu-box-2 : Ws → St 1487
  lem-CKu-box-2 = pickᴰ 63 Sᴰ
  lem-CKu-box-2-at0210243143 : Ws → St 1488
  lem-CKu-box-2-at0210243143 = pickᴰ 64 Sᴰ
  lem-CKu-box-2-at122441 : Ws → St 1489
  lem-CKu-box-2-at122441 = pickᴰ 65 Sᴰ
  lem-CKu-box-2-at243243 : Ws → St 1490
  lem-CKu-box-2-at243243 = pickᴰ 66 Sᴰ
  lem-CKu-box-3 : Ws → St 1491
  lem-CKu-box-3 = pickᴰ 67 Sᴰ
  lem-CKu-box-4 : Ws → St 1492
  lem-CKu-box-4 = pickᴰ 68 Sᴰ
  lem-box-perm-1243 : Ws → St 1493
  lem-box-perm-1243 = pickᴰ 69 Sᴰ
  lem-box-perm-1243-at3443 : Ws → St 1494
  lem-box-perm-1243-at3443 = pickᴰ 70 Sᴰ
  lem-box-perm-1342 : Ws → St 1495
  lem-box-perm-1342 = pickᴰ 71 Sᴰ
  lem-box-perm-1423-at0210243143 : Ws → St 1496
  lem-box-perm-1423-at0210243143 = pickᴰ 72 Sᴰ
  lem-box-perm-1423-at243243 : Ws → St 1497
  lem-box-perm-1423-at243243 = pickᴰ 73 Sᴰ
  lem-box-perm-2341 : Ws → St 1498
  lem-box-perm-2341 = pickᴰ 74 Sᴰ
  lem-box-perm-3421-at0213203441 : Ws → St 1499
  lem-box-perm-3421-at0213203441 = pickᴰ 75 Sᴰ
  lem-box-perm-3421-at0314203142 : Ws → St 1500
  lem-box-perm-3421-at0314203142 = pickᴰ 76 Sᴰ
  lem-box-perm-4123-at033440 : Ws → St 1501
  lem-box-perm-4123-at033440 = pickᴰ 77 Sᴰ
  lem-box-perm-4312-at0214213043 : Ws → St 1502
  lem-box-perm-4312-at0214213043 = pickᴰ 78 Sᴰ
  lem-box-perm-4312-at0330 : Ws → St 1503
  lem-box-perm-4312-at0330 = pickᴰ 79 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 366 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1479 (lem-CKdu-box-1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1247 (lem-Ku-box c4)

-- XCKX-box-1: 4 steps
lem-XCKX-box-1 : Ws → ⟪ (X1 ∷ CK10 ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-XCKX-box-1 c4 = derive (X1 ∷ CK10 ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 1 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q4 : Ws → Eqn
  q4 c4 = wlE 367 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1486 (lem-CKu-box-1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1243 (lem-Kdu-box c4)

-- XCKdX-box-1: 4 steps
lem-XCKdX-box-1 : Ws → ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ
lem-XCKdX-box-1 c4 = derive (X1 ∷ CK10⁻ ∷ X1 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ [])
  (rw⁻ 0 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q6 c4) ∷
   rw 1 (q4 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = wlE 379 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1480 (lem-CKdu-box-2 c4)

-- XCKX-box-2: 4 steps
lem-XCKX-box-2 : Ws → ⟪ (X2 ∷ CK20 ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-XCKX-box-2 c4 = derive (X2 ∷ CK20 ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw⁻ 0 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q7 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = wlE 380 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1487 (lem-CKu-box-2 c4)

-- XCKdX-box-2: 4 steps
lem-XCKdX-box-2 : Ws → ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-XCKdX-box-2 c4 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw⁻ 0 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 0 (q6 c4) ∷
   rw 1 (q9 c4) ∷ []) Eq.refl

private
  q11 : Ws → Eqn
  q11 c4 = wlE 389 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1484 (lem-CKdu-box-3 c4)

-- XCKX-box-3: 4 steps
lem-XCKX-box-3 : Ws → ⟪ (X3 ∷ CK30 ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-XCKX-box-3 c4 = derive (X3 ∷ CK30 ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw⁻ 0 (q11 c4) ∷
   rw 1 (q12 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q11 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = wlE 390 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1491 (lem-CKu-box-3 c4)

-- XCKdX-box-3: 4 steps
lem-XCKdX-box-3 : Ws → ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-XCKdX-box-3 c4 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw⁻ 0 (q13 c4) ∷
   rw 1 (q14 c4) ∷
   rw 0 (q6 c4) ∷
   rw 1 (q13 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = wpE 259 c4
  q16 : Ws → Eqn
  q16 c4 = sE 1485 (lem-CKdu-box-4 c4)

-- XCKX-box-4: 4 steps
lem-XCKX-box-4 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-4 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q15 c4) ∷
   rw 1 (q16 c4) ∷
   rw 0 (q3 c4) ∷
   rw 1 (q15 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = wpE 260 c4
  q18 : Ws → Eqn
  q18 c4 = sE 1492 (lem-CKu-box-4 c4)

-- XCKdX-box-4: 4 steps
lem-XCKdX-box-4 : Ws → ⟪ (X4 ∷ CK40⁻ ∷ X4 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ []) ⟫ʷ
lem-XCKdX-box-4 c4 = derive (X4 ∷ CK40⁻ ∷ X4 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ X4 ∷ CK40⁻ ∷ X4 ∷ [])
  (rw⁻ 0 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 0 (q6 c4) ∷
   rw 1 (q17 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = sE 1498 (lem-box-perm-2341 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 312 (lem-box-tQ-at12233441 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1467 (lem-box-cP-at0110 c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 167 c4
  q23 : Ws → Eqn
  q23 c4 = wpE 275 c4
  q24 : Ws → Eqn
  q24 c4 = wpE 231 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 117 c4
  q26 : Ws → Eqn
  q26 c4 = wlE 381 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q29 : Ws → Eqn
  q29 c4 = wpE 276 c4
  q30 : Ws → Eqn
  q30 c4 = wlE 313 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wlE 408 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 409 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (K0⁻ ∷ Toff134 ∷ []) (Toff134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑))
  q34 : Ws → Eqn
  q34 c4 = wpE 277 c4
  q35 : Ws → Eqn
  q35 c4 = sE 1464 (lem-comm-CX02-TOFF134 c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 410 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 238 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (K0 ∷ Toff134 ∷ []) (Toff134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑))
  q39 : Ws → Eqn
  q39 c4 = wlE 274 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 141 c4
  q41 : Ws → Eqn
  q41 c4 = wlE 411 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 298 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 412 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 413 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 62 c4
  q46 : Ws → Eqn
  q46 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 63 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 64 c4
  q49 : Ws → Eqn
  q49 c4 = wpE 278 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 305 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = sE 1473 (lem-box-perm-4123-at12233441 c4)

-- box-box-1: 105 steps
lem-box-box-1 : Ws → ⟪ (Bx0-1234 ∷ Bx1-0234 ∷ []) ⟫ʷ ≈ ⟪ (Bx1-0234 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-1 c4 = derive (Bx0-1234 ∷ Bx1-0234 ∷ []) (Bx1-0234 ∷ Bx0-1234 ∷ [])
  (rw 0 (q19 c4) ∷
   rw 0 (q20 c4) ∷
   rw 4 (q21 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 4 (q23 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw 6 (q29 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 4 (q31 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 9 (q33 c4) ∷
   rw 8 (q34 c4) ∷
   rw 7 (q35 c4) ∷
   rw 6 (q36 c4) ∷
   rw 5 (q35 c4) ∷
   rw 4 (q37 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q32 c4) ∷
   rw 6 (q39 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   rw 5 (q43 c4) ∷
   rw 6 (q44 c4) ∷
   rw⁻ 5 (q32 c4) ∷
   rw 11 (q33 c4) ∷
   rw 10 (q34 c4) ∷
   rw 9 (q35 c4) ∷
   rw 8 (q36 c4) ∷
   rw 7 (q35 c4) ∷
   rw 6 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw 6 (q32 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 2 (q21 c4) ∷
   rw⁻ 1 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 4 (q29 c4) ∷
   rw⁻ 1 (q21 c4) ∷
   rw 1 (q21 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw 7 (q33 c4) ∷
   rw 6 (q34 c4) ∷
   rw 5 (q35 c4) ∷
   rw 4 (q36 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q32 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 3 (q43 c4) ∷
   rw 4 (q44 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 9 (q33 c4) ∷
   rw 8 (q34 c4) ∷
   rw 7 (q35 c4) ∷
   rw 6 (q36 c4) ∷
   rw 5 (q35 c4) ∷
   rw 4 (q37 c4) ∷
   rw 3 (q38 c4) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 0 (q21 c4) ∷
   rw 2 (q39 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw 5 (q46 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   rw 3 (q46 c4) ∷
   rw⁻ 2 (q48 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 3 (q49 c4) ∷
   rw 4 (q50 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw 1 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = sE 1495 (lem-box-perm-1342 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 342 (lem-box-tQ-at233442 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 863 (lem-box-cP-at021021 c4)
  q55 : Ws → Eqn
  q55 c4 = wpE 142 c4
  q56 : Ws → Eqn
  q56 c4 = wpE 290 c4
  q57 : Ws → Eqn
  q57 c4 = wpE 291 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 296 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wlE 426 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wlE 427 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (K0⁻ ∷ Toff234 ∷ []) (Toff234 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toff ↑))
  q62 : Ws → Eqn
  q62 c4 = wpE 292 c4
  q63 : Ws → Eqn
  q63 c4 = eqn (CX01 ∷ Toff234 ∷ []) (Toff234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toff))
  q64 : Ws → Eqn
  q64 c4 = wlE 428 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 429 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (K0 ∷ Toff234 ∷ []) (Toff234 ∷ K0 ∷ []) (c₁ (K) (Toff ↑))
  q67 : Ws → Eqn
  q67 c4 = wlE 166 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 11 c4
  q69 : Ws → Eqn
  q69 c4 = wlE 167 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 430 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 431 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wpE 34 c4
  q73 : Ws → Eqn
  q73 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q74 : Ws → Eqn
  q74 c4 = wpE 35 c4
  q75 : Ws → Eqn
  q75 c4 = wpE 36 c4
  q76 : Ws → Eqn
  q76 c4 = wpE 293 c4
  q77 : Ws → Eqn
  q77 c4 = wlE 321 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = sE 1471 (lem-box-perm-1423-at233442 c4)

-- box-box-2: 105 steps
lem-box-box-2 : Ws → ⟪ (Bx0-1234 ∷ Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-2 c4 = derive (Bx0-1234 ∷ Bx2-0134 ∷ []) (Bx2-0134 ∷ Bx0-1234 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 3 (q55 c4) ∷
   rw 4 (q56 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 6 (q57 c4) ∷
   rw⁻ 3 (q54 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw 4 (q59 c4) ∷
   rw⁻ 3 (q60 c4) ∷
   rw 9 (q61 c4) ∷
   rw 8 (q62 c4) ∷
   rw 7 (q63 c4) ∷
   rw 6 (q64 c4) ∷
   rw 5 (q63 c4) ∷
   rw 4 (q65 c4) ∷
   rw 3 (q66 c4) ∷
   rw 4 (q60 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 10 (q68 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw⁻ 5 (q42 c4) ∷
   rw⁻ 4 (q58 c4) ∷
   rw 5 (q70 c4) ∷
   rw 6 (q71 c4) ∷
   rw⁻ 5 (q60 c4) ∷
   rw 11 (q61 c4) ∷
   rw 10 (q62 c4) ∷
   rw 9 (q63 c4) ∷
   rw 8 (q64 c4) ∷
   rw 7 (q63 c4) ∷
   rw 6 (q65 c4) ∷
   rw 5 (q66 c4) ∷
   rw 6 (q60 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw 2 (q54 c4) ∷
   rw⁻ 1 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw⁻ 5 (q26 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   rw⁻ 3 (q55 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw 1 (q54 c4) ∷
   rw⁻ 0 (q58 c4) ∷
   rw 2 (q59 c4) ∷
   rw⁻ 1 (q60 c4) ∷
   rw 7 (q61 c4) ∷
   rw 6 (q62 c4) ∷
   rw 5 (q63 c4) ∷
   rw 4 (q64 c4) ∷
   rw 3 (q63 c4) ∷
   rw 2 (q65 c4) ∷
   rw 1 (q66 c4) ∷
   rw 2 (q60 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw⁻ 3 (q42 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw 3 (q70 c4) ∷
   rw 4 (q71 c4) ∷
   rw⁻ 3 (q60 c4) ∷
   rw 9 (q61 c4) ∷
   rw 8 (q62 c4) ∷
   rw 7 (q63 c4) ∷
   rw 6 (q64 c4) ∷
   rw 5 (q63 c4) ∷
   rw 4 (q65 c4) ∷
   rw 3 (q66 c4) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 0 (q54 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   rw 3 (q76 c4) ∷
   rw 4 (q77 c4) ∷
   rw⁻ 1 (q53 c4) ∷
   rw 1 (q78 c4) ∷ []) Eq.refl

private
  q79 : Ws → Eqn
  q79 c4 = sE 1493 (lem-box-perm-1243 c4)
  q80 : Ws → Eqn
  q80 c4 = sE 264 (lem-box-tQ-at3443 c4)
  q81 : Ws → Eqn
  q81 c4 = sE 867 (lem-box-cP-at03102132 c4)
  q82 : Ws → Eqn
  q82 c4 = wpE 186 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 295 c4
  q84 : Ws → Eqn
  q84 c4 = wpE 296 c4
  q85 : Ws → Eqn
  q85 c4 = wpE 77 c4
  q86 : Ws → Eqn
  q86 c4 = wlE 444 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = sE 204 (lem-comm-CSd24-CCZ013 c4)
  q88 : Ws → Eqn
  q88 c4 = sE 194 (lem-comm-CS24-CCZ013 c4)
  q89 : Ws → Eqn
  q89 c4 = wpE 297 c4
  q90 : Ws → Eqn
  q90 c4 = wlE 325 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wlE 445 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = wlE 446 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (K0⁻ ∷ Toff324 ∷ []) (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑))
  q94 : Ws → Eqn
  q94 c4 = wpE 298 c4
  q95 : Ws → Eqn
  q95 c4 = eqn (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))
  q96 : Ws → Eqn
  q96 c4 = wlE 447 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = wlE 214 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (K0 ∷ Toff324 ∷ []) (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑))
  q99 : Ws → Eqn
  q99 c4 = wlE 256 (lit c4)
  q100 : Ws → Eqn
  q100 c4 = wpE 299 c4
  q101 : Ws → Eqn
  q101 c4 = wlE 448 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 327 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = wlE 449 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 450 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wpE 106 c4
  q106 : Ws → Eqn
  q106 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q107 : Ws → Eqn
  q107 c4 = wpE 107 c4
  q108 : Ws → Eqn
  q108 c4 = wpE 108 c4
  q109 : Ws → Eqn
  q109 c4 = wpE 300 c4
  q110 : Ws → Eqn
  q110 c4 = wlE 263 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = sE 1494 (lem-box-perm-1243-at3443 c4)

-- box-box-3: 105 steps
lem-box-box-3 : Ws → ⟪ (Bx0-1234 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-box-box-3 c4 = derive (Bx0-1234 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ Bx0-1234 ∷ [])
  (rw 0 (q79 c4) ∷
   rw 0 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 4 (q83 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 9 (q85 c4) ∷
   rw⁻ 8 (q86 c4) ∷
   rw 7 (q87 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw 5 (q88 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 6 (q89 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw 3 (q81 c4) ∷
   rw⁻ 2 (q90 c4) ∷
   rw 4 (q91 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw 9 (q93 c4) ∷
   rw 8 (q94 c4) ∷
   rw 7 (q95 c4) ∷
   rw 6 (q96 c4) ∷
   rw 5 (q95 c4) ∷
   rw 4 (q97 c4) ∷
   rw 3 (q98 c4) ∷
   rw 4 (q92 c4) ∷
   rw 6 (q99 c4) ∷
   rw⁻ 10 (q100 c4) ∷
   rw⁻ 9 (q101 c4) ∷
   rw 8 (q87 c4) ∷
   rw⁻ 7 (q101 c4) ∷
   rw 6 (q88 c4) ∷
   rw⁻ 7 (q99 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw⁻ 4 (q90 c4) ∷
   rw 5 (q103 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw 11 (q93 c4) ∷
   rw 10 (q94 c4) ∷
   rw 9 (q95 c4) ∷
   rw 8 (q96 c4) ∷
   rw 7 (q95 c4) ∷
   rw 6 (q97 c4) ∷
   rw 5 (q98 c4) ∷
   rw 6 (q92 c4) ∷
   rw⁻ 2 (q81 c4) ∷
   rw 2 (q81 c4) ∷
   rw⁻ 1 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 1 (q81 c4) ∷
   rw 1 (q81 c4) ∷
   rw⁻ 0 (q90 c4) ∷
   rw 2 (q91 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw 7 (q93 c4) ∷
   rw 6 (q94 c4) ∷
   rw 5 (q95 c4) ∷
   rw 4 (q96 c4) ∷
   rw 3 (q95 c4) ∷
   rw 2 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q92 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 8 (q100 c4) ∷
   rw⁻ 7 (q101 c4) ∷
   rw 6 (q87 c4) ∷
   rw⁻ 5 (q101 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 5 (q99 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw⁻ 2 (q90 c4) ∷
   rw 3 (q103 c4) ∷
   rw 4 (q104 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw 9 (q93 c4) ∷
   rw 8 (q94 c4) ∷
   rw 7 (q95 c4) ∷
   rw 6 (q96 c4) ∷
   rw 5 (q95 c4) ∷
   rw 4 (q97 c4) ∷
   rw 3 (q98 c4) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   rw 2 (q99 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw 5 (q106 c4) ∷
   rw⁻ 4 (q107 c4) ∷
   rw 3 (q106 c4) ∷
   rw⁻ 2 (q108 c4) ∷
   rw⁻ 3 (q99 c4) ∷
   rw 3 (q109 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 1 (q80 c4) ∷
   rw 1 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = sE 252 (lem-box-tQ-at0330 c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 511 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wpE 372 c4
  q115 : Ws → Eqn
  q115 c4 = wpE 373 c4
  q116 : Ws → Eqn
  q116 c4 = wlE 512 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = wpE 374 c4
  q118 : Ws → Eqn
  q118 c4 = sE 373 (lem-comm-CZ03-TOFF412 c4)
  q119 : Ws → Eqn
  q119 c4 = wlE 382 (lit c4)
  q120 : Ws → Eqn
  q120 c4 = wpE 375 c4
  q121 : Ws → Eqn
  q121 c4 = wlE 513 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = wpE 7 c4
  q123 : Ws → Eqn
  q123 c4 = sE 253 (lem-box-tQ-at043043 c4)
  q124 : Ws → Eqn
  q124 c4 = sE 1470 (lem-box-perm-1324-at043043 c4)
  q125 : Ws → Eqn
  q125 c4 = sE 919 (lem-box-cP-at04203243 c4)
  q126 : Ws → Eqn
  q126 c4 = wlE 514 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = wpE 61 c4
  q128 : Ws → Eqn
  q128 c4 = wpE 53 c4
  q129 : Ws → Eqn
  q129 c4 = wpE 54 c4
  q130 : Ws → Eqn
  q130 c4 = sE 704 (lem-comm-CSd23-CCZ014 c4)
  q131 : Ws → Eqn
  q131 c4 = sE 703 (lem-comm-CS23-CCZ014 c4)
  q132 : Ws → Eqn
  q132 c4 = wpE 65 c4
  q133 : Ws → Eqn
  q133 c4 = wlE 515 (lit c4)
  q134 : Ws → Eqn
  q134 c4 = wpE 376 c4
  q135 : Ws → Eqn
  q135 c4 = wlE 348 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wpE 311 c4
  q137 : Ws → Eqn
  q137 c4 = eqn (CX01 ∷ Toff423 ∷ []) (Toff423 ∷ CX01 ∷ []) (c₂ (CX₀₁) (Toffᵗ))
  q138 : Ws → Eqn
  q138 c4 = wlE 460 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = wlE 461 (lit c4)
  q140 : Ws → Eqn
  q140 c4 = wlE 516 (lit c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 517 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = wpE 3 c4
  q143 : Ws → Eqn
  q143 c4 = wpE 221 c4
  q144 : Ws → Eqn
  q144 c4 = sE 199 (lem-comm-CSd12-CCZ034 c4)
  q145 : Ws → Eqn
  q145 c4 = sE 191 (lem-comm-CS12-CCZ034 c4)
  q146 : Ws → Eqn
  q146 c4 = wlE 503 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = wlE 341 (lit c4)
  q148 : Ws → Eqn
  q148 c4 = sE 1472 (lem-box-perm-3124-at043043 c4)
  q149 : Ws → Eqn
  q149 c4 = sE 1503 (lem-box-perm-4312-at0330 c4)
  q150 : Ws → Eqn
  q150 c4 = sE 1469 (lem-box-box-4-at0410213243 c4)
  q151 : Ws → Eqn
  q151 c4 = sE 1500 (lem-box-perm-3421-at0314203142 c4)
  q152 : Ws → Eqn
  q152 c4 = sE 1468 (lem-box-perm-2314-at0410213243 c4)

-- F0-B: 62 steps
lem-F0-B : Ws → ⟪ (CX34 ∷ Bx3-1204 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ Bx4-1203 ∷ []) ⟫ʷ
lem-F0-B c4 = derive (CX34 ∷ Bx3-1204 ∷ CX34 ∷ []) (Bx3-1204 ∷ Bx4-1203 ∷ [])
  (rw 1 (q112 c4) ∷
   rw 0 (q113 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 4 (q113 c4) ∷
   rw⁻ 6 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 5 (q117 c4) ∷
   rw 4 (q118 c4) ∷
   rw⁻ 5 (q119 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   rw 3 (q121 c4) ∷
   rw⁻ 4 (q122 c4) ∷
   rw⁻ 1 (q123 c4) ∷
   rw 1 (q124 c4) ∷
   rw 1 (q125 c4) ∷
   rw⁻ 0 (q126 c4) ∷
   rw⁻ 6 (q127 c4) ∷
   rw⁻ 5 (q128 c4) ∷
   rw⁻ 4 (q129 c4) ∷
   rw 3 (q130 c4) ∷
   rw⁻ 2 (q129 c4) ∷
   rw 1 (q131 c4) ∷
   rw⁻ 0 (q132 c4) ∷
   rw 1 (q126 c4) ∷
   rw 1 (q133 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw⁻ 2 (q126 c4) ∷
   rw⁻ 8 (q127 c4) ∷
   rw⁻ 7 (q128 c4) ∷
   rw⁻ 6 (q129 c4) ∷
   rw 5 (q130 c4) ∷
   rw⁻ 4 (q129 c4) ∷
   rw 3 (q131 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw 3 (q126 c4) ∷
   rw 5 (q135 c4) ∷
   rw 9 (q136 c4) ∷
   rw 8 (q137 c4) ∷
   rw 7 (q138 c4) ∷
   rw 6 (q137 c4) ∷
   rw 5 (q139 c4) ∷
   rw⁻ 6 (q135 c4) ∷
   rw 4 (q140 c4) ∷
   rw 3 (q133 c4) ∷
   rw 4 (q141 c4) ∷
   rw⁻ 0 (q125 c4) ∷
   rw⁻ 0 (q124 c4) ∷
   rw 2 (q135 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw⁻ 5 (q143 c4) ∷
   rw 4 (q144 c4) ∷
   rw⁻ 3 (q143 c4) ∷
   rw 2 (q145 c4) ∷
   rw⁻ 3 (q135 c4) ∷
   rw 3 (q146 c4) ∷
   rw 4 (q147 c4) ∷
   rw⁻ 1 (q112 c4) ∷
   rw 0 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 0 (q150 c4) ∷
   rw 0 (q151 c4) ∷
   rw 1 (q152 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = sE 1483 (lem-CKdu-box-2-at243243 c4)
  q154 : Ws → Eqn
  q154 c4 = sE 1250 (lem-Ku-box-at243243 c4)

-- XCKX-box-2 @243243: 4 steps
lem-XCKX-box-2-at243243 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at243243 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q15 c4) ∷
   rw 1 (q153 c4) ∷
   rw 0 (q154 c4) ∷
   rw 1 (q15 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = sE 1482 (lem-CKdu-box-2-at122441 c4)
  q156 : Ws → Eqn
  q156 c4 = sE 1249 (lem-Ku-box-at122441 c4)

-- XCKX-box-2 @122441: 4 steps
lem-XCKX-box-2-at122441 : Ws → ⟪ (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at122441 c4 = derive (X4 ∷ CK40 ∷ X4 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ X4 ∷ CK40 ∷ X4 ∷ [])
  (rw⁻ 0 (q15 c4) ∷
   rw 1 (q155 c4) ∷
   rw 0 (q156 c4) ∷
   rw 1 (q15 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = sE 1496 (lem-box-perm-1423-at0210243143 c4)
  q158 : Ws → Eqn
  q158 c4 = sE 1042 (lem-box-cP-at0210233441 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))
  q160 : Ws → Eqn
  q160 c4 = sE 1221 (lem-comm-CK41-CCZ023 c4)
  q161 : Ws → Eqn
  q161 c4 = wlE 642 (lit c4)
  q162 : Ws → Eqn
  q162 c4 = wpE 517 c4

-- F4-K1-CS0: 19 steps
lem-F4-K1-CS0 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K1-CS0 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw⁻ 2 (q159 c4) ∷
   rw 1 (q160 c4) ∷
   rw⁻ 0 (q159 c4) ∷
   rw⁻ 1 (q161 c4) ∷
   rw⁻ 4 (q159 c4) ∷
   rw 3 (q160 c4) ∷
   rw⁻ 2 (q159 c4) ∷
   rw⁻ 3 (q161 c4) ∷
   rw⁻ 0 (q158 c4) ∷
   rw⁻ 0 (q157 c4) ∷
   rw⁻ 1 (q162 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = wlE 665 (lit c4)
  q164 : Ws → Eqn
  q164 c4 = sE 1481 (lem-CKdu-box-2-at0210243143 c4)
  q165 : Ws → Eqn
  q165 c4 = sE 1248 (lem-Ku-box-at0210243143 c4)

-- XCKX-box-2 @0210243143: 4 steps
lem-XCKX-box-2-at0210243143 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-XCKX-box-2-at0210243143 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (rw⁻ 0 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 0 (q165 c4) ∷
   rw 1 (q163 c4) ∷ []) Eq.refl

private
  q166 : Ws → Eqn
  q166 c4 = sE 1497 (lem-box-perm-1423-at243243 c4)
  q167 : Ws → Eqn
  q167 c4 = sE 1129 (lem-box-cP-at233442 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))
  q169 : Ws → Eqn
  q169 c4 = sE 1466 (lem-comm-CK42-CCZ013 c4)
  q170 : Ws → Eqn
  q170 c4 = wpE 555 c4
  q171 : Ws → Eqn
  q171 c4 = wlE 685 (lit c4)

-- F4-K2-CS1: 19 steps
lem-F4-K2-CS1 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K2-CS1 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q166 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 2 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw⁻ 0 (q168 c4) ∷
   rw⁻ 1 (q170 c4) ∷
   rw⁻ 4 (q168 c4) ∷
   rw 3 (q169 c4) ∷
   rw⁻ 2 (q168 c4) ∷
   rw⁻ 3 (q170 c4) ∷
   rw⁻ 0 (q167 c4) ∷
   rw⁻ 0 (q166 c4) ∷
   rw⁻ 1 (q171 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = wlE 720 (lit c4)
  q173 : Ws → Eqn
  q173 c4 = wpE 614 c4
  q174 : Ws → Eqn
  q174 c4 = wlE 721 (lit c4)
  q175 : Ws → Eqn
  q175 c4 = wlE 722 (lit c4)
  q176 : Ws → Eqn
  q176 c4 = sE 1224 (lem-comm-CCZ023-CK41 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CCZ023 ∷ S4 ∷ []) (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S))
  q178 : Ws → Eqn
  q178 c4 = wlE 723 (lit c4)

-- F4-CS0-K1: 21 steps
lem-F4-CS0-K1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q172 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q173 c4) ∷
   rw 1 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw⁻ 4 (q174 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw 5 (q177 c4) ∷
   rw⁻ 2 (q174 c4) ∷
   rw 1 (q175 c4) ∷
   rw 2 (q176 c4) ∷
   rw 3 (q177 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   rw⁻ 4 (q157 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q178 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = wlE 725 (lit c4)
  q180 : Ws → Eqn
  q180 c4 = wpE 615 c4
  q181 : Ws → Eqn
  q181 c4 = wlE 726 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = wpE 616 c4
  q183 : Ws → Eqn
  q183 c4 = sE 1488 (lem-CKu-box-2-at0210243143 c4)
  q184 : Ws → Eqn
  q184 c4 = sE 994 (lem-box-cP-at0210243143 c4)
  q185 : Ws → Eqn
  q185 c4 = wlE 727 (lit c4)
  q186 : Ws → Eqn
  q186 c4 = wpE 617 c4
  q187 : Ws → Eqn
  q187 c4 = wlE 728 (lit c4)

-- F4-CS0-K2: 20 steps
lem-F4-CS0-K2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-K2 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q179 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 5 (q180 c4) ∷
   rw⁻ 4 (q181 c4) ∷
   rw 3 (q182 c4) ∷
   rw⁻ 2 (q181 c4) ∷
   rw⁻ 1 (q165 c4) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw⁻ 6 (q185 c4) ∷
   rw 5 (q186 c4) ∷
   rw⁻ 4 (q185 c4) ∷
   rw 3 (q186 c4) ∷
   rw⁻ 4 (q184 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q187 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = wpE 610 c4
  q189 : Ws → Eqn
  q189 c4 = wpE 629 c4
  q190 : Ws → Eqn
  q190 c4 = wpE 630 c4
  q191 : Ws → Eqn
  q191 c4 = wpE 631 c4
  q192 : Ws → Eqn
  q192 c4 = sE 1490 (lem-CKu-box-2-at243243 c4)
  q193 : Ws → Eqn
  q193 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q194 : Ws → Eqn
  q194 c4 = wpE 632 c4
  q195 : Ws → Eqn
  q195 c4 = wpE 633 c4
  q196 : Ws → Eqn
  q196 c4 = wpE 613 c4

-- F4-CS1-K0: 20 steps
lem-F4-CS1-K0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K0 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q188 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 5 (q189 c4) ∷
   rw⁻ 4 (q190 c4) ∷
   rw 3 (q191 c4) ∷
   rw⁻ 2 (q190 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw⁻ 2 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw⁻ 6 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw⁻ 4 (q193 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q196 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = wlE 736 (lit c4)
  q198 : Ws → Eqn
  q198 c4 = wpE 635 c4
  q199 : Ws → Eqn
  q199 c4 = wlE 737 (lit c4)
  q200 : Ws → Eqn
  q200 c4 = sE 1465 (lem-comm-CCZ013-CK42 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (CCZ013 ∷ S4 ∷ []) (S4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (S))

-- F4-CS1-K2: 21 steps
lem-F4-CS1-K2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-K2 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q179 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q197 c4) ∷
   rw 1 (q166 c4) ∷
   rw 1 (q167 c4) ∷
   rw⁻ 4 (q198 c4) ∷
   rw 3 (q199 c4) ∷
   rw 4 (q200 c4) ∷
   rw 5 (q201 c4) ∷
   rw⁻ 2 (q198 c4) ∷
   rw 1 (q199 c4) ∷
   rw 2 (q200 c4) ∷
   rw 3 (q201 c4) ∷
   rw⁻ 4 (q167 c4) ∷
   rw⁻ 4 (q166 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q187 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = wpE 644 c4
  q203 : Ws → Eqn
  q203 c4 = wpE 645 c4
  q204 : Ws → Eqn
  q204 c4 = wpE 646 c4
  q205 : Ws → Eqn
  q205 c4 = sE 1489 (lem-CKu-box-2-at122441 c4)
  q206 : Ws → Eqn
  q206 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q207 : Ws → Eqn
  q207 c4 = wpE 647 c4

-- F4-CS2-K0: 20 steps
lem-F4-CS2-K0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K0 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK40 ∷ []) (CK40 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q188 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 5 (q202 c4) ∷
   rw⁻ 4 (q203 c4) ∷
   rw 3 (q204 c4) ∷
   rw⁻ 2 (q203 c4) ∷
   rw⁻ 1 (q156 c4) ∷
   rw⁻ 2 (q205 c4) ∷
   rw 3 (q206 c4) ∷
   rw⁻ 6 (q207 c4) ∷
   rw 5 (q186 c4) ∷
   rw⁻ 4 (q207 c4) ∷
   rw 3 (q186 c4) ∷
   rw⁻ 4 (q206 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q196 c4) ∷ []) Eq.refl

private
  q208 : Ws → Eqn
  q208 c4 = sE 250 (lem-box-tQ-at0214213043 c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 771 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = wlE 772 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = wlE 773 (lit c4)
  q212 : Ws → Eqn
  q212 c4 = wpE 697 c4
  q213 : Ws → Eqn
  q213 c4 = wpE 698 c4
  q214 : Ws → Eqn
  q214 c4 = sE 337 (lem-comm-CZ02-TOFF314 c4)
  q215 : Ws → Eqn
  q215 c4 = wpE 699 c4
  q216 : Ws → Eqn
  q216 c4 = wlE 774 (lit c4)
  q217 : Ws → Eqn
  q217 c4 = wlE 775 (lit c4)
  q218 : Ws → Eqn
  q218 c4 = wlE 204 (lit c4)
  q219 : Ws → Eqn
  q219 c4 = sE 311 (lem-box-tQ-at0314213042 c4)
  q220 : Ws → Eqn
  q220 c4 = sE 1475 (lem-box-perm-1324-at0314213042 c4)
  q221 : Ws → Eqn
  q221 c4 = sE 997 (lem-box-cP-at0314203142 c4)
  q222 : Ws → Eqn
  q222 c4 = wlE 776 (lit c4)
  q223 : Ws → Eqn
  q223 c4 = wpE 700 c4
  q224 : Ws → Eqn
  q224 c4 = wpE 357 c4
  q225 : Ws → Eqn
  q225 c4 = wpE 701 c4
  q226 : Ws → Eqn
  q226 c4 = wlE 777 (lit c4)
  q227 : Ws → Eqn
  q227 c4 = wpE 702 c4
  q228 : Ws → Eqn
  q228 c4 = wpE 41 c4
  q229 : Ws → Eqn
  q229 c4 = wlE 501 (lit c4)
  q230 : Ws → Eqn
  q230 c4 = sE 1025 (lem-comm-CX04-TOFF312 c4)
  q231 : Ws → Eqn
  q231 c4 = wlE 778 (lit c4)
  q232 : Ws → Eqn
  q232 c4 = wlE 499 (lit c4)
  q233 : Ws → Eqn
  q233 c4 = wlE 779 (lit c4)
  q234 : Ws → Eqn
  q234 c4 = wlE 780 (lit c4)
  q235 : Ws → Eqn
  q235 c4 = wlE 199 (lit c4)
  q236 : Ws → Eqn
  q236 c4 = wpE 684 c4
  q237 : Ws → Eqn
  q237 c4 = sE 224 (lem-comm-CSd14-CCZ023 c4)
  q238 : Ws → Eqn
  q238 c4 = sE 219 (lem-comm-CS14-CCZ023 c4)
  q239 : Ws → Eqn
  q239 c4 = wpE 686 c4
  q240 : Ws → Eqn
  q240 c4 = wpE 161 c4
  q241 : Ws → Eqn
  q241 c4 = sE 1478 (lem-box-perm-3124-at0314213042 c4)
  q242 : Ws → Eqn
  q242 c4 = sE 1502 (lem-box-perm-4312-at0214213043 c4)
  q243 : Ws → Eqn
  q243 c4 = sE 1474 (lem-box-box-4-at0310243142 c4)
  q244 : Ws → Eqn
  q244 c4 = sE 1499 (lem-box-perm-3421-at0213203441 c4)
  q245 : Ws → Eqn
  q245 c4 = sE 1476 (lem-box-perm-2314-at0310243142 c4)

-- F0-B @14213243: 62 steps
lem-F0-B-at14213243 : Ws → ⟪ (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ Bx3-4102 ∷ []) ⟫ʷ
lem-F0-B-at14213243 c4 = derive (CX23 ∷ Bx2-4103 ∷ CX23 ∷ []) (Bx2-4103 ∷ Bx3-4102 ∷ [])
  (rw 1 (q208 c4) ∷
   rw 0 (q209 c4) ∷
   rw⁻ 2 (q210 c4) ∷
   rw 4 (q209 c4) ∷
   rw⁻ 6 (q211 c4) ∷
   rw 3 (q212 c4) ∷
   rw 5 (q213 c4) ∷
   rw 4 (q214 c4) ∷
   rw⁻ 5 (q215 c4) ∷
   rw⁻ 6 (q216 c4) ∷
   rw 3 (q217 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw⁻ 1 (q219 c4) ∷
   rw 1 (q220 c4) ∷
   rw 1 (q221 c4) ∷
   rw⁻ 0 (q222 c4) ∷
   rw⁻ 6 (q223 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw⁻ 4 (q224 c4) ∷
   rw 3 (q144 c4) ∷
   rw⁻ 2 (q224 c4) ∷
   rw 1 (q145 c4) ∷
   rw⁻ 0 (q225 c4) ∷
   rw 1 (q222 c4) ∷
   rw 1 (q226 c4) ∷
   rw⁻ 3 (q227 c4) ∷
   rw⁻ 2 (q222 c4) ∷
   rw⁻ 8 (q223 c4) ∷
   rw⁻ 7 (q108 c4) ∷
   rw⁻ 6 (q224 c4) ∷
   rw 5 (q144 c4) ∷
   rw⁻ 4 (q224 c4) ∷
   rw 3 (q145 c4) ∷
   rw⁻ 2 (q225 c4) ∷
   rw 3 (q222 c4) ∷
   rw 5 (q228 c4) ∷
   rw 9 (q229 c4) ∷
   rw 8 (q230 c4) ∷
   rw 7 (q231 c4) ∷
   rw 6 (q230 c4) ∷
   rw 5 (q232 c4) ∷
   rw⁻ 6 (q228 c4) ∷
   rw⁻ 4 (q233 c4) ∷
   rw 3 (q226 c4) ∷
   rw 4 (q234 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw⁻ 0 (q220 c4) ∷
   rw 2 (q228 c4) ∷
   rw⁻ 6 (q235 c4) ∷
   rw⁻ 5 (q236 c4) ∷
   rw 4 (q237 c4) ∷
   rw⁻ 3 (q236 c4) ∷
   rw 2 (q238 c4) ∷
   rw⁻ 3 (q228 c4) ∷
   rw 3 (q239 c4) ∷
   rw 4 (q240 c4) ∷
   rw⁻ 1 (q208 c4) ∷
   rw 0 (q241 c4) ∷
   rw 1 (q242 c4) ∷
   rw 0 (q243 c4) ∷
   rw 0 (q244 c4) ∷
   rw 1 (q245 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = sE 1477 (lem-box-perm-2341-at03102132 c4)
  q247 : Ws → Eqn
  q247 c4 = sE 340 (lem-box-tQ-at033440 c4)
  q248 : Ws → Eqn
  q248 c4 = sE 1003 (lem-box-cP-at132132 c4)
  q249 : Ws → Eqn
  q249 c4 = wpE 183 c4
  q250 : Ws → Eqn
  q250 c4 = wlE 829 (lit c4)
  q251 : Ws → Eqn
  q251 c4 = wpE 185 c4
  q252 : Ws → Eqn
  q252 c4 = wlE 706 (lit c4)
  q253 : Ws → Eqn
  q253 c4 = wpE 739 c4
  q254 : Ws → Eqn
  q254 c4 = wlE 850 (lit c4)
  q255 : Ws → Eqn
  q255 c4 = wpE 587 c4
  q256 : Ws → Eqn
  q256 c4 = wlE 869 (lit c4)
  q257 : Ws → Eqn
  q257 c4 = wpE 740 c4
  q258 : Ws → Eqn
  q258 c4 = wpE 190 c4
  q259 : Ws → Eqn
  q259 c4 = sE 1069 (lem-comm-CX31-TOFF024 c4)
  q260 : Ws → Eqn
  q260 c4 = wpE 741 c4
  q261 : Ws → Eqn
  q261 c4 = wpE 524 c4
  q262 : Ws → Eqn
  q262 c4 = wpE 742 c4
  q263 : Ws → Eqn
  q263 c4 = wlE 704 (lit c4)
  q264 : Ws → Eqn
  q264 c4 = wlE 870 (lit c4)
  q265 : Ws → Eqn
  q265 c4 = wpE 743 c4
  q266 : Ws → Eqn
  q266 c4 = wlE 871 (lit c4)
  q267 : Ws → Eqn
  q267 c4 = sE 1501 (lem-box-perm-4123-at033440 c4)

-- box-box-1 @03102132: 105 steps
lem-box-box-1-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-box-box-1-at03102132 c4 = derive (Bx3-0124 ∷ Bx0-3124 ∷ []) (Bx0-3124 ∷ Bx3-0124 ∷ [])
  (rw 0 (q246 c4) ∷
   rw 0 (q247 c4) ∷
   rw 4 (q248 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 4 (q249 c4) ∷
   rw 6 (q250 c4) ∷
   rw⁻ 10 (q251 c4) ∷
   rw⁻ 9 (q252 c4) ∷
   rw 8 (q87 c4) ∷
   rw⁻ 7 (q252 c4) ∷
   rw 6 (q88 c4) ∷
   rw⁻ 7 (q250 c4) ∷
   rw⁻ 5 (q82 c4) ∷
   rw 6 (q253 c4) ∷
   rw⁻ 3 (q248 c4) ∷
   rw 3 (q248 c4) ∷
   rw⁻ 2 (q254 c4) ∷
   rw 4 (q255 c4) ∷
   rw⁻ 3 (q256 c4) ∷
   rw 9 (q257 c4) ∷
   rw 8 (q258 c4) ∷
   rw 7 (q259 c4) ∷
   rw 6 (q260 c4) ∷
   rw 5 (q259 c4) ∷
   rw 4 (q261 c4) ∷
   rw 3 (q262 c4) ∷
   rw 4 (q256 c4) ∷
   rw 6 (q99 c4) ∷
   rw⁻ 10 (q100 c4) ∷
   rw⁻ 9 (q101 c4) ∷
   rw 8 (q87 c4) ∷
   rw⁻ 7 (q101 c4) ∷
   rw 6 (q88 c4) ∷
   rw⁻ 7 (q99 c4) ∷
   rw 5 (q263 c4) ∷
   rw⁻ 4 (q254 c4) ∷
   rw 5 (q264 c4) ∷
   rw 6 (q265 c4) ∷
   rw⁻ 5 (q256 c4) ∷
   rw 11 (q257 c4) ∷
   rw 10 (q258 c4) ∷
   rw 9 (q259 c4) ∷
   rw 8 (q260 c4) ∷
   rw 7 (q259 c4) ∷
   rw 6 (q261 c4) ∷
   rw 5 (q262 c4) ∷
   rw 6 (q256 c4) ∷
   rw⁻ 2 (q248 c4) ∷
   rw 2 (q248 c4) ∷
   rw⁻ 1 (q82 c4) ∷
   rw 2 (q249 c4) ∷
   rw 4 (q250 c4) ∷
   rw⁻ 8 (q251 c4) ∷
   rw⁻ 7 (q252 c4) ∷
   rw 6 (q87 c4) ∷
   rw⁻ 5 (q252 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 5 (q250 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw 4 (q253 c4) ∷
   rw⁻ 1 (q248 c4) ∷
   rw 1 (q248 c4) ∷
   rw⁻ 0 (q254 c4) ∷
   rw 2 (q255 c4) ∷
   rw⁻ 1 (q256 c4) ∷
   rw 7 (q257 c4) ∷
   rw 6 (q258 c4) ∷
   rw 5 (q259 c4) ∷
   rw 4 (q260 c4) ∷
   rw 3 (q259 c4) ∷
   rw 2 (q261 c4) ∷
   rw 1 (q262 c4) ∷
   rw 2 (q256 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 8 (q100 c4) ∷
   rw⁻ 7 (q101 c4) ∷
   rw 6 (q87 c4) ∷
   rw⁻ 5 (q101 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 5 (q99 c4) ∷
   rw 3 (q263 c4) ∷
   rw⁻ 2 (q254 c4) ∷
   rw 3 (q264 c4) ∷
   rw 4 (q265 c4) ∷
   rw⁻ 3 (q256 c4) ∷
   rw 9 (q257 c4) ∷
   rw 8 (q258 c4) ∷
   rw 7 (q259 c4) ∷
   rw 6 (q260 c4) ∷
   rw 5 (q259 c4) ∷
   rw 4 (q261 c4) ∷
   rw 3 (q262 c4) ∷
   rw 4 (q256 c4) ∷
   rw⁻ 0 (q248 c4) ∷
   rw 2 (q99 c4) ∷
   rw⁻ 6 (q105 c4) ∷
   rw 5 (q106 c4) ∷
   rw⁻ 4 (q107 c4) ∷
   rw 3 (q106 c4) ∷
   rw⁻ 2 (q108 c4) ∷
   rw⁻ 3 (q99 c4) ∷
   rw 3 (q266 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 1 (q247 c4) ∷
   rw 1 (q267 c4) ∷ []) Eq.refl
