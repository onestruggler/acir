{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD033 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D033 (Sᴰ : SD033) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS12-CCZ034 : Ws → St 191
  lem-comm-CS12-CCZ034 = pickᴰ 0 Sᴰ
  lem-comm-CSd12-CCZ034 : Ws → St 199
  lem-comm-CSd12-CCZ034 = pickᴰ 1 Sᴰ
  lem-comm-CX40-TOFF312 : Ws → St 965
  lem-comm-CX40-TOFF312 = pickᴰ 2 Sᴰ
  lem-comm-CZ24-TOFF301 : Ws → St 79
  lem-comm-CZ24-TOFF301 = pickᴰ 3 Sᴰ
  lem-comm-CK03-CCZ124 : Ws → St 1177
  lem-comm-CK03-CCZ124 = pickᴰ 4 Sᴰ
  lem-F4-I-I : Ws → St 1386
  lem-F4-I-I = pickᴰ 5 Sᴰ
  lem-F4-I-K1 : Ws → St 1409
  lem-F4-I-K1 = pickᴰ 6 Sᴰ
  lem-F4-I-K2 : Ws → St 1410
  lem-F4-I-K2 = pickᴰ 7 Sᴰ
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 8 Sᴰ
  lem-sym-ab-at0410213243 : Ws → St 713
  lem-sym-ab-at0410213243 = pickᴰ 9 Sᴰ
  lem-sym-ab-at04203243 : Ws → St 969
  lem-sym-ab-at04203243 = pickᴰ 10 Sᴰ
  lem-sym-ab-at0314213240 : Ws → St 1076
  lem-sym-ab-at0314213240 = pickᴰ 11 Sᴰ
  lem-sym-ab-at03243240 : Ws → St 1078
  lem-sym-ab-at03243240 = pickᴰ 12 Sᴰ
  lem-sym-ab-at02142140 : Ws → St 1412
  lem-sym-ab-at02142140 = pickᴰ 13 Sᴰ
  lem-sym-ab-at022440 : Ws → St 1413
  lem-sym-ab-at022440 = pickᴰ 14 Sᴰ
  lem-sym-ab-at0410233142 : Ws → St 1414
  lem-sym-ab-at0410233142 = pickᴰ 15 Sᴰ
  lem-sym-ab-at04122041 : Ws → St 1415
  lem-sym-ab-at04122041 = pickᴰ 16 Sᴰ
  lem-sym-ab-at0413203142 : Ws → St 1416
  lem-sym-ab-at0413203142 = pickᴰ 17 Sᴰ
  lem-sym-ab-at0413213042 : Ws → St 1417
  lem-sym-ab-at0413213042 = pickᴰ 18 Sᴰ
  lem-sym-ab-at0413213240 : Ws → St 1418
  lem-sym-ab-at0413213240 = pickᴰ 19 Sᴰ
  lem-sym-ab-at04233042 : Ws → St 1419
  lem-sym-ab-at04233042 = pickᴰ 20 Sᴰ
  lem-sym-ab-at04233240 : Ws → St 1420
  lem-sym-ab-at04233240 = pickᴰ 21 Sᴰ
  lem-sym-ab-at0440 : Ws → St 1421
  lem-sym-ab-at0440 = pickᴰ 22 Sᴰ
  lem-box-tQ-at0210213443 : Ws → St 137
  lem-box-tQ-at0210213443 = pickᴰ 23 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 149
  lem-box-tQ-at0310213442 = pickᴰ 24 Sᴰ
  lem-CSu-box-2-at0214203143 : Ws → St 1422
  lem-CSu-box-2-at0214203143 = pickᴰ 25 Sᴰ
  lem-box-cP-at0214233041 : Ws → St 890
  lem-box-cP-at0214233041 = pickᴰ 26 Sᴰ
  lem-sym-bc-at0410213243 : Ws → St 1423
  lem-sym-bc-at0410213243 = pickᴰ 27 Sᴰ
  lem-box-cP-at0214213043 : Ws → St 995
  lem-box-cP-at0214213043 = pickᴰ 28 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 996
  lem-box-cP-at0310243142 = pickᴰ 29 Sᴰ
  lem-box-perm-1324-at0310213442 : Ws → St 1311
  lem-box-perm-1324-at0310213442 = pickᴰ 30 Sᴰ
  lem-sym-bc-at02233440 : Ws → St 1142
  lem-sym-bc-at02233440 = pickᴰ 31 Sᴰ
  lem-sym-bc-at022440 : Ws → St 1143
  lem-sym-bc-at022440 = pickᴰ 32 Sᴰ
  lem-sym-bc-at03243240 : Ws → St 1154
  lem-sym-bc-at03243240 = pickᴰ 33 Sᴰ
  lem-sym-bc-at033440 : Ws → St 1155
  lem-sym-bc-at033440 = pickᴰ 34 Sᴰ
  lem-box-box-4-at0314203142 : Ws → St 1424
  lem-box-box-4-at0314203142 = pickᴰ 35 Sᴰ
  lem-box-cP-at0412233041 : Ws → St 1193
  lem-box-cP-at0412233041 = pickᴰ 36 Sᴰ
  lem-box-perm-3124-at0310213442 : Ws → St 1425
  lem-box-perm-3124-at0310213442 = pickᴰ 37 Sᴰ
  lem-sym-bc-at041041 : Ws → St 1426
  lem-sym-bc-at041041 = pickᴰ 38 Sᴰ
  lem-sym-bc-at04122041 : Ws → St 1199
  lem-sym-bc-at04122041 = pickᴰ 39 Sᴰ
  lem-sym-bc-at04122140 : Ws → St 1427
  lem-sym-bc-at04122140 = pickᴰ 40 Sᴰ
  lem-sym-bc-at0413203142 : Ws → St 1428
  lem-sym-bc-at0413203142 = pickᴰ 41 Sᴰ
  lem-sym-bc-at0413213042 : Ws → St 1429
  lem-sym-bc-at0413213042 = pickᴰ 42 Sᴰ
  lem-sym-bc-at04233240 : Ws → St 1430
  lem-sym-bc-at04233240 = pickᴰ 43 Sᴰ
  lem-sym-bc-at0440 : Ws → St 1431
  lem-sym-bc-at0440 = pickᴰ 44 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 45 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 46 Sᴰ
  lem-pairs-at0214203143 : Ws → St 1343
  lem-pairs-at0214203143 = pickᴰ 47 Sᴰ
  lem-pairs-at02233440 : Ws → St 1344
  lem-pairs-at02233440 = pickᴰ 48 Sᴰ
  lem-pairs-at0314203142 : Ws → St 1347
  lem-pairs-at0314203142 = pickᴰ 49 Sᴰ
  lem-pairs-at033440 : Ws → St 1350
  lem-pairs-at033440 = pickᴰ 50 Sᴰ
  lem-CXu-box-4-at0214203143 : Ws → St 1434
  lem-CXu-box-4-at0214203143 = pickᴰ 51 Sᴰ
  lem-Kdu-box-at0214203143 : Ws → St 1435
  lem-Kdu-box-at0214203143 = pickᴰ 52 Sᴰ
  lem-Ku-box-at0214203143 : Ws → St 1436
  lem-Ku-box-at0214203143 = pickᴰ 53 Sᴰ
  lem-box-perm-1324-at04122041 : Ws → St 1437
  lem-box-perm-1324-at04122041 = pickᴰ 54 Sᴰ
  lem-box-perm-1423-at0214203143 : Ws → St 1408
  lem-box-perm-1423-at0214203143 = pickᴰ 55 Sᴰ
  lem-box-perm-2314-at0314203142 : Ws → St 1438
  lem-box-perm-2314-at0314203142 = pickᴰ 56 Sᴰ
  lem-box-perm-3421-at0213243041 : Ws → St 1439
  lem-box-perm-3421-at0213243041 = pickᴰ 57 Sᴰ
  lem-box-perm-4312-at0210213443 : Ws → St 1440
  lem-box-perm-4312-at0210213443 = pickᴰ 58 Sᴰ
  lem-pairs-at0410233241 : Ws → St 1441
  lem-pairs-at0410233241 = pickᴰ 59 Sᴰ
  lem-pairs-at04103143 : Ws → St 1442
  lem-pairs-at04103143 = pickᴰ 60 Sᴰ
  lem-pairs-at04122041 : Ws → St 1443
  lem-pairs-at04122041 = pickᴰ 61 Sᴰ
  lem-pairs-at0412233041 : Ws → St 1444
  lem-pairs-at0412233041 = pickᴰ 62 Sᴰ
  lem-pairs-at0413203142 : Ws → St 1445
  lem-pairs-at0413203142 = pickᴰ 63 Sᴰ
  lem-pairs-at0413213240 : Ws → St 1446
  lem-pairs-at0413213240 = pickᴰ 64 Sᴰ
  lem-pairs-at0440 : Ws → St 1447
  lem-pairs-at0440 = pickᴰ 65 Sᴰ
  lem-S2-SBOX⟨0·1·42·3⟩-at0440 : Ws → St 1448
  lem-S2-SBOX⟨0·1·42·3⟩-at0440 = pickᴰ 66 Sᴰ
  lem-box-perm-1324-at0214203143 : Ws → St 1449
  lem-box-perm-1324-at0214203143 = pickᴰ 67 Sᴰ
  lem-pairs-at0410233142 : Ws → St 1450
  lem-pairs-at0410233142 = pickᴰ 68 Sᴰ
  lem-pairs-at0412233140 : Ws → St 1451
  lem-pairs-at0412233140 = pickᴰ 69 Sᴰ
  lem-pairs-at043043 : Ws → St 1452
  lem-pairs-at043043 = pickᴰ 70 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1410 (lem-F4-I-K2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1386 (lem-F4-I-I c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1411 (lem-F4-I-K3 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1409 (lem-F4-I-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1083 (lit c4)

-- ckt-TST part51: 82 steps
lem-ckt-TST-part51 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇並丢並丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part51 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇並丢並丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw⁻ 324 (q1 c4) ∷
   rw⁻ 323 (q2 c4) ∷
   rw⁻ 322 (q2 c4) ∷
   rw⁻ 321 (q1 c4) ∷
   rw⁻ 320 (q3 c4) ∷
   rw⁻ 319 (q4 c4) ∷
   rw⁻ 318 (q2 c4) ∷
   rw⁻ 317 (q2 c4) ∷
   rw⁻ 316 (q4 c4) ∷
   rw⁻ 315 (q5 c4) ∷
   rw⁻ 314 (q3 c4) ∷
   rw⁻ 313 (q4 c4) ∷
   rw⁻ 312 (q2 c4) ∷
   rw⁻ 311 (q2 c4) ∷
   rw⁻ 310 (q4 c4) ∷
   rw⁻ 309 (q3 c4) ∷
   rw⁻ 308 (q1 c4) ∷
   rw⁻ 307 (q2 c4) ∷
   rw⁻ 306 (q2 c4) ∷
   rw⁻ 305 (q1 c4) ∷
   rw⁻ 304 (q3 c4) ∷
   rw⁻ 303 (q4 c4) ∷
   rw⁻ 302 (q2 c4) ∷
   rw⁻ 301 (q2 c4) ∷
   rw⁻ 300 (q4 c4) ∷
   rw⁻ 299 (q3 c4) ∷
   rw⁻ 298 (q1 c4) ∷
   rw⁻ 297 (q5 c4) ∷
   rw⁻ 296 (q5 c4) ∷
   rw⁻ 295 (q1 c4) ∷
   rw⁻ 294 (q2 c4) ∷
   rw⁻ 293 (q2 c4) ∷
   rw⁻ 292 (q2 c4) ∷
   rw⁻ 291 (q3 c4) ∷
   rw⁻ 290 (q1 c4) ∷
   rw⁻ 289 (q5 c4) ∷
   rw⁻ 288 (q5 c4) ∷
   rw⁻ 287 (q1 c4) ∷
   rw⁻ 286 (q2 c4) ∷
   rw⁻ 285 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q7 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q7 c4) ∷
   rw 26 (q7 c4) ∷
   rw 27 (q7 c4) ∷
   rw 28 (q7 c4) ∷
   rw 29 (q7 c4) ∷
   rw 30 (q7 c4) ∷
   rw 31 (q7 c4) ∷
   rw 32 (q7 c4) ∷
   rw 33 (q7 c4) ∷
   rw 34 (q7 c4) ∷
   rw 35 (q7 c4) ∷
   rw 36 (q7 c4) ∷
   rw 37 (q7 c4) ∷
   rw 38 (q7 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q7 c4) ∷
   rw 41 (q7 c4) ∷
   rw 42 (q7 c4) ∷
   rw 43 (q7 c4) ∷ []) Eq.refl

private
  q8 : Ws → Eqn
  q8 c4 = wlE 1441 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = wlE 1471 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1437 (lem-box-perm-1324-at04122041 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1193 (lem-box-cP-at0412233041 c4)
  q12 : Ws → Eqn
  q12 c4 = wpE 1320 c4
  q13 : Ws → Eqn
  q13 c4 = eqn (ℓ "丒亰") (ℓ "亰丒") (c₂ (K ↑) (CCZ))
  q14 : Ws → Eqn
  q14 c4 = eqn (ℓ "中亰") (ℓ "亰中") (c₂ (CK₀₁) (CCZ))
  q15 : Ws → Eqn
  q15 c4 = eqn (ℓ "上亰") (ℓ "亰上") (c₁ (S) (CCZ ↑))
  q16 : Ws → Eqn
  q16 c4 = wlE 1443 (lit c4)

-- F4-CS2-K1 @0440: 21 steps
lem-F4-CS2-K1-at0440 : Ws → ⟪ (ℓ "与俵与中") ⟫ʷ ≈ ⟪ (ℓ "中与俵与") ⟫ʷ
lem-F4-CS2-K1-at0440 c4 = derive (ℓ "与俵与中") (ℓ "中与俵与")
  (rw⁻ 2 (q8 c4) ∷
   re 1 1 (ℓ "侗互俳互俴") ∷
   re 3 1 (ℓ "乇") ∷
   re 5 1 (ℓ "么") ∷
   rw⁻ 2 (q9 c4) ∷
   rw 1 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw⁻ 1 (q13 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 4 (q11 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   re 6 1 (ℓ "俳") ∷
   re 8 1 (ℓ "俴") ∷
   re 4 5 (ℓ "俵") ∷
   rw⁻ 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = sE 969 (lem-sym-ab-at04203243 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1423 (lem-sym-bc-at0410213243 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1442 (lem-pairs-at04103143 c4)

-- box-perm-1423 @04203243: 3 steps
lem-box-perm-1423-at04203243 : Ws → ⟪ (ℓ "侒") ⟫ʷ ≈ ⟪ (ℓ "侕") ⟫ʷ
lem-box-perm-1423-at04203243 c4 = derive (ℓ "侒") (ℓ "侕")
  (rw 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 0 (q19 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = sE 1199 (lem-sym-bc-at04122041 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1444 (lem-pairs-at0412233041 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 713 (lem-sym-ab-at0410213243 c4)

-- box-perm-4213 @04122041: 3 steps
lem-box-perm-4213-at04122041 : Ws → ⟪ (ℓ "侗") ⟫ʷ ≈ ⟪ (ℓ "侒") ⟫ʷ
lem-box-perm-4213-at04122041 c4 = derive (ℓ "侗") (ℓ "侒")
  (rw 0 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw 0 (q22 c4) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = sE 1415 (lem-sym-ab-at04122041 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1426 (lem-sym-bc-at041041 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1441 (lem-pairs-at0410233241 c4)

-- box-perm-1423 @04122041: 3 steps
lem-box-perm-1423-at04122041 : Ws → ⟪ (ℓ "侗") ⟫ʷ ≈ ⟪ (ℓ "侘") ⟫ʷ
lem-box-perm-1423-at04122041 c4 = derive (ℓ "侗") (ℓ "侘")
  (rw 0 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 0 (q25 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (ℓ "与亰") (ℓ "亰与") (c₁ (X) (CCZ ↑))
  q27 : Ws → Eqn
  q27 c4 = wpE 1394 c4
  q28 : Ws → Eqn
  q28 c4 = wlE 1583 (lit c4)

-- F4-K1-CS2 @0440: 19 steps
lem-F4-K1-CS2-at0440 : Ws → ⟪ (ℓ "与中与俵") ⟫ʷ ≈ ⟪ (ℓ "俵与中与") ⟫ʷ
lem-F4-K1-CS2-at0440 c4 = derive (ℓ "与中与俵") (ℓ "俵与中与")
  (re 3 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 3 (q10 c4) ∷
   rw 3 (q11 c4) ∷
   rw 2 (q26 c4) ∷
   rw 1 (q14 c4) ∷
   rw 0 (q26 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 4 (q26 c4) ∷
   rw 3 (q14 c4) ∷
   rw 2 (q26 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   rw⁻ 0 (q11 c4) ∷
   rw⁻ 0 (q10 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   re 2 1 (ℓ "俳") ∷
   re 4 1 (ℓ "俴") ∷
   re 0 5 (ℓ "俵") ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = sE 1408 (lem-box-perm-1423-at0214203143 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 890 (lem-box-cP-at0214233041 c4)
  q31 : Ws → Eqn
  q31 c4 = wlE 1439 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 1292 c4

-- F4-K1-CS0 @0440: 19 steps
lem-F4-K1-CS0-at0440 : Ws → ⟪ (ℓ "与中与俊") ⟫ʷ ≈ ⟪ (ℓ "俊与中与") ⟫ʷ
lem-F4-K1-CS0-at0440 c4 = derive (ℓ "与中与俊") (ℓ "俊与中与")
  (re 3 1 (ℓ "佔亓俈亓俉") ∷
   re 5 1 (ℓ "乹") ∷
   re 7 1 (ℓ "乺") ∷
   rw 3 (q29 c4) ∷
   rw 3 (q30 c4) ∷
   rw 2 (q26 c4) ∷
   rw 1 (q14 c4) ∷
   rw 0 (q26 c4) ∷
   rw⁻ 1 (q31 c4) ∷
   rw 4 (q26 c4) ∷
   rw 3 (q14 c4) ∷
   rw 2 (q26 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw⁻ 0 (q30 c4) ∷
   rw⁻ 0 (q29 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   re 2 1 (ℓ "俈") ∷
   re 4 1 (ℓ "俉") ∷
   re 0 5 (ℓ "俊") ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = sE 1443 (lem-pairs-at04122041 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1418 (lem-sym-ab-at0413213240 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1430 (lem-sym-bc-at04233240 c4)

-- box-perm-4132 @04122041: 3 steps
lem-box-perm-4132-at04122041 : Ws → ⟪ (ℓ "侗") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-box-perm-4132-at04122041 c4 = derive (ℓ "侗") (ℓ "侔")
  (rw 0 (q33 c4) ∷
   rw 0 (q34 c4) ∷
   rw 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = sE 1343 (lem-pairs-at0214203143 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1142 (lem-sym-bc-at02233440 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1413 (lem-sym-ab-at022440 c4)

-- box-perm-1342 @0214203143: 3 steps
lem-box-perm-1342-at0214203143 : Ws → ⟪ (ℓ "佔") ⟫ʷ ≈ ⟪ (ℓ "佟") ⟫ʷ
lem-box-perm-1342-at0214203143 c4 = derive (ℓ "佔") (ℓ "佟")
  (rw 0 (q36 c4) ∷
   rw 0 (q37 c4) ∷
   rw 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = sE 1447 (lem-pairs-at0440 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 1428 (lem-sym-bc-at0413203142 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1417 (lem-sym-ab-at0413213042 c4)

-- box-perm-1342 @0440: 3 steps
lem-box-perm-1342-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "侕") ⟫ʷ
lem-box-perm-1342-at0440 c4 = derive (ℓ "侔") (ℓ "侕")
  (rw 0 (q39 c4) ∷
   rw 0 (q40 c4) ∷
   rw 0 (q41 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = sE 1419 (lem-sym-ab-at04233042 c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1429 (lem-sym-bc-at0413213042 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 1445 (lem-pairs-at0413203142 c4)

-- box-perm-1423 @04233042: 3 steps
lem-box-perm-1423-at04233042 : Ws → ⟪ (ℓ "侕") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-box-perm-1423-at04233042 c4 = derive (ℓ "侕") (ℓ "侔")
  (rw 0 (q42 c4) ∷
   rw 0 (q43 c4) ∷
   rw 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = sE 1412 (lem-sym-ab-at02142140 c4)
  q46 : Ws → Eqn
  q46 c4 = sE 1143 (lem-sym-bc-at022440 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 1344 (lem-pairs-at02233440 c4)

-- box-perm-1423 @02142140: 3 steps
lem-box-perm-1423-at02142140 : Ws → ⟪ (ℓ "佟") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-box-perm-1423-at02142140 c4 = derive (ℓ "佟") (ℓ "佔")
  (rw 0 (q45 c4) ∷
   rw 0 (q46 c4) ∷
   rw 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = sE 1431 (lem-sym-bc-at0440 c4)
  q49 : Ws → Eqn
  q49 c4 = sE 1420 (lem-sym-ab-at04233240 c4)
  q50 : Ws → Eqn
  q50 c4 = sE 1446 (lem-pairs-at0413213240 c4)

-- box-perm-2431 @0440: 3 steps
lem-box-perm-2431-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "侗") ⟫ʷ
lem-box-perm-2431-at0440 c4 = derive (ℓ "侔") (ℓ "侗")
  (rw 0 (q48 c4) ∷
   rw 0 (q49 c4) ∷
   rw 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = wlE 1632 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = sE 1422 (lem-CSu-box-2-at0214203143 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 1436 (lem-Ku-box-at0214203143 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 1435 (lem-Kdu-box-at0214203143 c4)

-- CKdu-box-2 @0214203143: 7 steps
lem-CKdu-box-2-at0214203143 : Ws → ⟪ (ℓ "丵佔") ⟫ʷ ≈ ⟪ (ℓ "佔丵") ⟫ʷ
lem-CKdu-box-2-at0214203143 c4 = derive (ℓ "丵佔") (ℓ "佔丵")
  (rw 0 (q51 c4) ∷
   rw 4 (q52 c4) ∷
   rw 3 (q53 c4) ∷
   rw 2 (q52 c4) ∷
   rw 1 (q54 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 1 (q51 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = sE 137 (lem-box-tQ-at0210213443 c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 1637 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wlE 1638 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = wlE 1639 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 1433 c4
  q60 : Ws → Eqn
  q60 c4 = wpE 1173 c4
  q61 : Ws → Eqn
  q61 c4 = sE 79 (lem-comm-CZ24-TOFF301 c4)
  q62 : Ws → Eqn
  q62 c4 = wpE 1434 c4
  q63 : Ws → Eqn
  q63 c4 = wlE 844 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 1386 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 305 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = sE 149 (lem-box-tQ-at0310213442 c4)
  q67 : Ws → Eqn
  q67 c4 = sE 1311 (lem-box-perm-1324-at0310213442 c4)
  q68 : Ws → Eqn
  q68 c4 = sE 996 (lem-box-cP-at0310243142 c4)
  q69 : Ws → Eqn
  q69 c4 = wlE 1640 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wpE 700 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 3 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 221 c4
  q73 : Ws → Eqn
  q73 c4 = sE 199 (lem-comm-CSd12-CCZ034 c4)
  q74 : Ws → Eqn
  q74 c4 = sE 191 (lem-comm-CS12-CCZ034 c4)
  q75 : Ws → Eqn
  q75 c4 = wpE 701 c4
  q76 : Ws → Eqn
  q76 c4 = wlE 1641 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wpE 388 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 1143 c4
  q79 : Ws → Eqn
  q79 c4 = wlE 499 (lit c4)
  q80 : Ws → Eqn
  q80 c4 = sE 965 (lem-comm-CX40-TOFF312 c4)
  q81 : Ws → Eqn
  q81 c4 = wlE 500 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wlE 501 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 525 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = wlE 1642 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 452 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wpE 1171 c4
  q87 : Ws → Eqn
  q87 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))
  q88 : Ws → Eqn
  q88 c4 = eqn (ℓ "丨亰") (ℓ "亰丨") (c₂ (CS) (CCZ))
  q89 : Ws → Eqn
  q89 c4 = wpE 1189 c4
  q90 : Ws → Eqn
  q90 c4 = wpE 161 c4
  q91 : Ws → Eqn
  q91 c4 = sE 1425 (lem-box-perm-3124-at0310213442 c4)
  q92 : Ws → Eqn
  q92 c4 = sE 1440 (lem-box-perm-4312-at0210213443 c4)
  q93 : Ws → Eqn
  q93 c4 = sE 1424 (lem-box-box-4-at0314203142 c4)
  q94 : Ws → Eqn
  q94 c4 = sE 1439 (lem-box-perm-3421-at0213243041 c4)
  q95 : Ws → Eqn
  q95 c4 = sE 1438 (lem-box-perm-2314-at0314203142 c4)

-- F0-B @0410213243: 62 steps
lem-F0-B-at0410213243 : Ws → ⟪ (ℓ "书伮书") ⟫ʷ ≈ ⟪ (ℓ "伮佥") ⟫ʷ
lem-F0-B-at0410213243 c4 = derive (ℓ "书伮书") (ℓ "伮佥")
  (rw 1 (q55 c4) ∷
   rw 0 (q56 c4) ∷
   rw⁻ 2 (q57 c4) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 3 (q59 c4) ∷
   rw 5 (q60 c4) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 5 (q62 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q65 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw 1 (q68 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw⁻ 5 (q71 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 1 (q74 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 1 (q69 c4) ∷
   rw 1 (q76 c4) ∷
   rw⁻ 3 (q77 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw⁻ 8 (q70 c4) ∷
   rw⁻ 7 (q71 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 3 (q74 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw 3 (q69 c4) ∷
   rw 5 (q78 c4) ∷
   rw 9 (q79 c4) ∷
   rw 8 (q80 c4) ∷
   rw 7 (q81 c4) ∷
   rw 6 (q80 c4) ∷
   rw 5 (q82 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw 4 (q83 c4) ∷
   rw 3 (q76 c4) ∷
   rw 4 (q84 c4) ∷
   rw⁻ 0 (q68 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw 2 (q78 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw 4 (q87 c4) ∷
   rw⁻ 3 (q86 c4) ∷
   rw 2 (q88 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   rw 3 (q89 c4) ∷
   rw 4 (q90 c4) ∷
   rw⁻ 1 (q55 c4) ∷
   rw 0 (q91 c4) ∷
   rw 1 (q92 c4) ∷
   rw 0 (q93 c4) ∷
   rw 0 (q94 c4) ∷
   rw 1 (q95 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = sE 1434 (lem-CXu-box-4-at0214203143 c4)
  q97 : Ws → Eqn
  q97 c4 = wlE 1655 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (ℓ "亏乹") (ℓ "乹亏") (c₃ (Toffᵗ) (CS))
  q99 : Ws → Eqn
  q99 c4 = wlE 1656 (lit c4)
  q100 : Ws → Eqn
  q100 c4 = wlE 1657 (lit c4)
  q101 : Ws → Eqn
  q101 c4 = wlE 1658 (lit c4)

-- CXAu-S @0410213243: 12 steps
lem-CXAu-S-at0410213243 : Ws → ⟪ (ℓ "乶俊") ⟫ʷ ≈ ⟪ (ℓ "俊乶") ⟫ʷ
lem-CXAu-S-at0410213243 c4 = derive (ℓ "乶俊") (ℓ "俊乶")
  (re 1 1 (ℓ "佔亓俈亓俉") ∷
   re 3 1 (ℓ "乹") ∷
   re 5 1 (ℓ "乺") ∷
   rw 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 3 (q98 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 3 (q100 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   re 2 1 (ℓ "俈") ∷
   re 4 1 (ℓ "俉") ∷
   re 0 5 (ℓ "俊") ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = sE 1347 (lem-pairs-at0314203142 c4)
  q103 : Ws → Eqn
  q103 c4 = sE 1155 (lem-sym-bc-at033440 c4)
  q104 : Ws → Eqn
  q104 c4 = sE 1078 (lem-sym-ab-at03243240 c4)

-- box-perm-1342 @0314203142: 3 steps
lem-box-perm-1342-at0314203142 : Ws → ⟪ (ℓ "佹") ⟫ʷ ≈ ⟪ (ℓ "侅") ⟫ʷ
lem-box-perm-1342-at0314203142 c4 = derive (ℓ "佹") (ℓ "侅")
  (rw 0 (q102 c4) ∷
   rw 0 (q103 c4) ∷
   rw 0 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = sE 1416 (lem-sym-ab-at0413203142 c4)
  q106 : Ws → Eqn
  q106 c4 = sE 1450 (lem-pairs-at0410233142 c4)

-- box-perm-1243 @0440: 3 steps
lem-box-perm-1243-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "侓") ⟫ʷ
lem-box-perm-1243-at0440 c4 = derive (ℓ "侔") (ℓ "侓")
  (rw 0 (q39 c4) ∷
   rw 0 (q105 c4) ∷
   rw 0 (q106 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = sE 1452 (lem-pairs-at043043 c4)
  q108 : Ws → Eqn
  q108 c4 = sE 1414 (lem-sym-ab-at0410233142 c4)

-- box-perm-1243 @043043: 3 steps
lem-box-perm-1243-at043043 : Ws → ⟪ (ℓ "侓") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-box-perm-1243-at043043 c4 = derive (ℓ "侓") (ℓ "侔")
  (rw 0 (q107 c4) ∷
   rw 0 (q108 c4) ∷
   rw 0 (q44 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = sE 1076 (lem-sym-ab-at0314213240 c4)
  q110 : Ws → Eqn
  q110 c4 = sE 1154 (lem-sym-bc-at03243240 c4)
  q111 : Ws → Eqn
  q111 c4 = sE 1350 (lem-pairs-at033440 c4)

-- box-perm-1423 @0314213240: 3 steps
lem-box-perm-1423-at0314213240 : Ws → ⟪ (ℓ "侅") ⟫ʷ ≈ ⟪ (ℓ "佹") ⟫ʷ
lem-box-perm-1423-at0314213240 c4 = derive (ℓ "侅") (ℓ "佹")
  (rw 0 (q109 c4) ∷
   rw 0 (q110 c4) ∷
   rw 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = sE 1421 (lem-sym-ab-at0440 c4)
  q113 : Ws → Eqn
  q113 c4 = sE 1427 (lem-sym-bc-at04122140 c4)
  q114 : Ws → Eqn
  q114 c4 = sE 1451 (lem-pairs-at0412233140 c4)

-- box-perm-1423 @0440: 3 steps
lem-box-perm-1423-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "侒") ⟫ʷ
lem-box-perm-1423-at0440 c4 = derive (ℓ "侔") (ℓ "侒")
  (rw 0 (q112 c4) ∷
   rw 0 (q113 c4) ∷
   rw 0 (q114 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = sE 1449 (lem-box-perm-1324-at0214203143 c4)
  q116 : Ws → Eqn
  q116 c4 = sE 995 (lem-box-cP-at0214213043 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (ℓ "与亨") (ℓ "亨与") (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q118 : Ws → Eqn
  q118 c4 = sE 1177 (lem-comm-CK03-CCZ124 c4)
  q119 : Ws → Eqn
  q119 c4 = wlE 1702 (lit c4)
  q120 : Ws → Eqn
  q120 c4 = wpE 1455 c4

-- F4-K3-CS0 @0440: 19 steps
lem-F4-K3-CS0-at0440 : Ws → ⟪ (ℓ "与主与俊") ⟫ʷ ≈ ⟪ (ℓ "俊与主与") ⟫ʷ
lem-F4-K3-CS0-at0440 c4 = derive (ℓ "与主与俊") (ℓ "俊与主与")
  (re 3 1 (ℓ "佔亓俈亓俉") ∷
   re 5 1 (ℓ "乹") ∷
   re 7 1 (ℓ "乺") ∷
   rw 3 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw 0 (q117 c4) ∷
   rw⁻ 1 (q119 c4) ∷
   rw 4 (q117 c4) ∷
   rw 3 (q118 c4) ∷
   rw 2 (q117 c4) ∷
   rw⁻ 3 (q119 c4) ∷
   rw⁻ 0 (q116 c4) ∷
   rw⁻ 0 (q115 c4) ∷
   rw⁻ 1 (q120 c4) ∷
   re 2 1 (ℓ "俈") ∷
   re 4 1 (ℓ "俉") ∷
   re 0 5 (ℓ "俊") ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = sE 1448 (lem-S2-SBOX⟨0·1·42·3⟩-at0440 c4)
  q122 : Ws → Eqn
  q122 c4 = wlE 1704 (lit c4)

-- L-CX01-1 @0440: 2 steps
lem-L-CX01-1-at0440 : Ws → ⟪ (ℓ "临俭俭临上") ⟫ʷ ≈ ⟪ (ℓ "亏") ⟫ʷ
lem-L-CX01-1-at0440 c4 = derive (ℓ "临俭俭临上") (ℓ "亏")
  (rw 1 (q121 c4) ∷
   rw 0 (q122 c4) ∷ []) Eq.refl
