{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD027 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D027 (Sᴰ : SD027) where

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
  lem-comm-CX02-CCZ134 : Ws → St 0
  lem-comm-CX02-CCZ134 = pickᴰ 0 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 1 Sᴰ
  lem-comm-CCZ014-CX23 : Ws → St 893
  lem-comm-CCZ014-CX23 = pickᴰ 2 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 3 Sᴰ
  lem-comm-CCZ024-CX31 : Ws → St 1058
  lem-comm-CCZ024-CX31 = pickᴰ 4 Sᴰ
  lem-comm-CCZ034-CX12 : Ws → St 1285
  lem-comm-CCZ034-CX12 = pickᴰ 5 Sᴰ
  lem-comm-CCZ034-CX21 : Ws → St 1298
  lem-comm-CCZ034-CX21 = pickᴰ 6 Sᴰ
  lem-comm-CCZ124-CX03 : Ws → St 1299
  lem-comm-CCZ124-CX03 = pickᴰ 7 Sᴰ
  lem-comm-CCZ134-CX02 : Ws → St 1300
  lem-comm-CCZ134-CX02 = pickᴰ 8 Sᴰ
  lem-comm-CX04-TOFF312 : Ws → St 1025
  lem-comm-CX04-TOFF312 = pickᴰ 9 Sᴰ
  lem-comm-CX14-TOFF302 : Ws → St 1301
  lem-comm-CX14-TOFF302 = pickᴰ 10 Sᴰ
  lem-comm-TOFF013-CK42 : Ws → St 1027
  lem-comm-TOFF013-CK42 = pickᴰ 11 Sᴰ
  lem-comm-TOFF013-CX24 : Ws → St 1059
  lem-comm-TOFF013-CX24 = pickᴰ 12 Sᴰ
  lem-comm-TOFF024-CS13 : Ws → St 1302
  lem-comm-TOFF024-CS13 = pickᴰ 13 Sᴰ
  lem-comm-TOFF213-CK40 : Ws → St 966
  lem-comm-TOFF213-CK40 = pickᴰ 14 Sᴰ
  lem-comm-CCZ134-CX20 : Ws → St 1303
  lem-comm-CCZ134-CX20 = pickᴰ 15 Sᴰ
  lem-comm-TOFF301-CK42 : Ws → St 1304
  lem-comm-TOFF301-CK42 = pickᴰ 16 Sᴰ
  lem-comm-TOFF312-CK40 : Ws → St 1305
  lem-comm-TOFF312-CK40 = pickᴰ 17 Sᴰ
  lem-comm-TOFF023-CK41 : Ws → St 968
  lem-comm-TOFF023-CK41 = pickᴰ 18 Sᴰ
  lem-comm-TOFF203-CK41 : Ws → St 1306
  lem-comm-TOFF203-CK41 = pickᴰ 19 Sᴰ
  lem-comm-TOFF302-CK41 : Ws → St 1307
  lem-comm-TOFF302-CK41 = pickᴰ 20 Sᴰ
  lem-sym-ab-at0210243143 : Ws → St 53
  lem-sym-ab-at0210243143 = pickᴰ 21 Sᴰ
  lem-sym-ab-at0214203143 : Ws → St 1029
  lem-sym-ab-at0214203143 = pickᴰ 22 Sᴰ
  lem-sym-ab-at0310243142 : Ws → St 894
  lem-sym-ab-at0310243142 = pickᴰ 23 Sᴰ
  lem-sym-ab-at0314203142 : Ws → St 1031
  lem-sym-ab-at0314203142 = pickᴰ 24 Sᴰ
  lem-sym-ab-at122441 : Ws → St 972
  lem-sym-ab-at122441 = pickᴰ 25 Sᴰ
  lem-sym-ab-at13213442 : Ws → St 1229
  lem-sym-ab-at13213442 = pickᴰ 26 Sᴰ
  lem-sym-ab-at233442 : Ws → St 974
  lem-sym-ab-at233442 = pickᴰ 27 Sᴰ
  lem-sym-ab-at243243 : Ws → St 1071
  lem-sym-ab-at243243 = pickᴰ 28 Sᴰ
  lem-sym-ab-at0314213240 : Ws → St 1076
  lem-sym-ab-at0314213240 = pickᴰ 29 Sᴰ
  lem-sym-ab-at03243240 : Ws → St 1078
  lem-sym-ab-at03243240 = pickᴰ 30 Sᴰ
  lem-sym-ab-at14213243 : Ws → St 1079
  lem-sym-ab-at14213243 = pickᴰ 31 Sᴰ
  lem-sym-ab-at1441 : Ws → St 1308
  lem-sym-ab-at1441 = pickᴰ 32 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 149
  lem-box-tQ-at0310213442 = pickᴰ 33 Sᴰ
  lem-box-tQ-at0210233441 : Ws → St 306
  lem-box-tQ-at0210233441 = pickᴰ 34 Sᴰ
  lem-box-tQ-at033440 : Ws → St 340
  lem-box-tQ-at033440 = pickᴰ 35 Sᴰ
  lem-box-tQ-at12213443 : Ws → St 341
  lem-box-tQ-at12213443 = pickᴰ 36 Sᴰ
  lem-box-tQ-at12233441 : Ws → St 312
  lem-box-tQ-at12233441 = pickᴰ 37 Sᴰ
  lem-box-tQ-at13213442 : Ws → St 259
  lem-box-tQ-at13213442 = pickᴰ 38 Sᴰ
  lem-box-tQ-at233442 : Ws → St 342
  lem-box-tQ-at233442 = pickᴰ 39 Sᴰ
  lem-box-tQ-at02233440 : Ws → St 330
  lem-box-tQ-at02233440 = pickᴰ 40 Sᴰ
  lem-box-tQ-at03103441 : Ws → St 352
  lem-box-tQ-at03103441 = pickᴰ 41 Sᴰ
  lem-box-tQ-at0312203441 : Ws → St 353
  lem-box-tQ-at0312203441 = pickᴰ 42 Sᴰ
  lem-box-tQ-at03143140 : Ws → St 357
  lem-box-tQ-at03143140 = pickᴰ 43 Sᴰ
  lem-sym-bc-at14233241 : Ws → St 1309
  lem-sym-bc-at14233241 = pickᴰ 44 Sᴰ
  lem-Xb-box-at13243142 : Ws → St 1310
  lem-Xb-box-at13243142 = pickᴰ 45 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 996
  lem-box-cP-at0310243142 = pickᴰ 46 Sᴰ
  lem-box-cP-at03243240 : Ws → St 1124
  lem-box-cP-at03243240 = pickᴰ 47 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 48 Sᴰ
  lem-box-perm-1324-at0310213442 : Ws → St 1311
  lem-box-perm-1324-at0310213442 = pickᴰ 49 Sᴰ
  lem-box-perm-1324-at13243142 : Ws → St 1312
  lem-box-perm-1324-at13243142 = pickᴰ 50 Sᴰ
  lem-sym-bc-at0214213043 : Ws → St 1052
  lem-sym-bc-at0214213043 = pickᴰ 51 Sᴰ
  lem-sym-bc-at0314203142 : Ws → St 1054
  lem-sym-bc-at0314203142 = pickᴰ 52 Sᴰ
  lem-sym-bc-at0314213042 : Ws → St 1055
  lem-sym-bc-at0314213042 = pickᴰ 53 Sᴰ
  lem-sym-bc-at03243240 : Ws → St 1154
  lem-sym-bc-at03243240 = pickᴰ 54 Sᴰ
  lem-sym-bc-at033440 : Ws → St 1155
  lem-sym-bc-at033440 = pickᴰ 55 Sᴰ
  lem-sym-bc-at143143 : Ws → St 1160
  lem-sym-bc-at143143 = pickᴰ 56 Sᴰ
  lem-Xb-box-at122441 : Ws → St 1252
  lem-Xb-box-at122441 = pickᴰ 57 Sᴰ
  lem-box-perm-1324-at122441 : Ws → St 1255
  lem-box-perm-1324-at122441 = pickᴰ 58 Sᴰ
  lem-pairs-at13213442 : Ws → St 1268
  lem-pairs-at13213442 = pickᴰ 59 Sᴰ
  lem-pairs-at143143 : Ws → St 1270
  lem-pairs-at143143 = pickᴰ 60 Sᴰ
  lem-pairs-at0210233441 : Ws → St 1277
  lem-pairs-at0210233441 = pickᴰ 61 Sᴰ
  lem-pairs-at12233441 : Ws → St 1282
  lem-pairs-at12233441 = pickᴰ 62 Sᴰ
  lem-pairs-at14213243 : Ws → St 1284
  lem-pairs-at14213243 = pickᴰ 63 Sᴰ
  lem-CSdu-box-3-at03143140 : Ws → St 1313
  lem-CSdu-box-3-at03143140 = pickᴰ 64 Sᴰ
  lem-CXu-box-4-at243243 : Ws → St 1314
  lem-CXu-box-4-at243243 = pickᴰ 65 Sᴰ
  lem-Xb-box-at02102441 : Ws → St 1315
  lem-Xb-box-at02102441 = pickᴰ 66 Sᴰ
  lem-Xb-box-at022440 : Ws → St 1316
  lem-Xb-box-at022440 = pickᴰ 67 Sᴰ
  lem-Xb-box-at0310243142 : Ws → St 1317
  lem-Xb-box-at0310243142 = pickᴰ 68 Sᴰ
  lem-Xb-box-at0310243241 : Ws → St 1318
  lem-Xb-box-at0310243241 = pickᴰ 69 Sᴰ
  lem-Xb-box-at0312243041 : Ws → St 1319
  lem-Xb-box-at0312243041 = pickᴰ 70 Sᴰ
  lem-Xb-box-at03243240 : Ws → St 1320
  lem-Xb-box-at03243240 = pickᴰ 71 Sᴰ
  lem-Xb-box-at12243143 : Ws → St 1321
  lem-Xb-box-at12243143 = pickᴰ 72 Sᴰ
  lem-Xb-box-at2442 : Ws → St 1322
  lem-Xb-box-at2442 = pickᴰ 73 Sᴰ
  lem-box-perm-1324-at0210233441 : Ws → St 1323
  lem-box-perm-1324-at0210233441 = pickᴰ 74 Sᴰ
  lem-box-perm-1324-at02102441 : Ws → St 1324
  lem-box-perm-1324-at02102441 = pickᴰ 75 Sᴰ
  lem-box-perm-1324-at02233440 : Ws → St 1325
  lem-box-perm-1324-at02233440 = pickᴰ 76 Sᴰ
  lem-box-perm-1324-at022440 : Ws → St 1326
  lem-box-perm-1324-at022440 = pickᴰ 77 Sᴰ
  lem-box-perm-1324-at0310243142 : Ws → St 1327
  lem-box-perm-1324-at0310243142 = pickᴰ 78 Sᴰ
  lem-box-perm-1324-at0310243241 : Ws → St 1328
  lem-box-perm-1324-at0310243241 = pickᴰ 79 Sᴰ
  lem-box-perm-1324-at03103441 : Ws → St 1329
  lem-box-perm-1324-at03103441 = pickᴰ 80 Sᴰ
  lem-box-perm-1324-at0312203441 : Ws → St 1330
  lem-box-perm-1324-at0312203441 = pickᴰ 81 Sᴰ
  lem-box-perm-1324-at0312243041 : Ws → St 1331
  lem-box-perm-1324-at0312243041 = pickᴰ 82 Sᴰ
  lem-box-perm-1324-at03243240 : Ws → St 1332
  lem-box-perm-1324-at03243240 = pickᴰ 83 Sᴰ
  lem-box-perm-1324-at033440 : Ws → St 1333
  lem-box-perm-1324-at033440 = pickᴰ 84 Sᴰ
  lem-box-perm-1324-at12213443 : Ws → St 1334
  lem-box-perm-1324-at12213443 = pickᴰ 85 Sᴰ
  lem-box-perm-1324-at12233441 : Ws → St 1335
  lem-box-perm-1324-at12233441 = pickᴰ 86 Sᴰ
  lem-box-perm-1324-at12243143 : Ws → St 1336
  lem-box-perm-1324-at12243143 = pickᴰ 87 Sᴰ
  lem-box-perm-1324-at13213442 : Ws → St 1337
  lem-box-perm-1324-at13213442 = pickᴰ 88 Sᴰ
  lem-box-perm-1324-at233442 : Ws → St 1338
  lem-box-perm-1324-at233442 = pickᴰ 89 Sᴰ
  lem-box-perm-1324-at2442 : Ws → St 1339
  lem-box-perm-1324-at2442 = pickᴰ 90 Sᴰ
  lem-box2-at0310243142 : Ws → St 1340
  lem-box2-at0310243142 = pickᴰ 91 Sᴰ
  lem-box2-at03243240 : Ws → St 1341
  lem-box2-at03243240 = pickᴰ 92 Sᴰ
  lem-nf-comm-CS-S1at2 : Ws → St 1342
  lem-nf-comm-CS-S1at2 = pickᴰ 93 Sᴰ
  lem-pairs-at0214203143 : Ws → St 1343
  lem-pairs-at0214203143 = pickᴰ 94 Sᴰ
  lem-pairs-at02233440 : Ws → St 1344
  lem-pairs-at02233440 = pickᴰ 95 Sᴰ
  lem-pairs-at03103441 : Ws → St 1345
  lem-pairs-at03103441 = pickᴰ 96 Sᴰ
  lem-pairs-at0312203441 : Ws → St 1346
  lem-pairs-at0312203441 = pickᴰ 97 Sᴰ
  lem-pairs-at0314203142 : Ws → St 1347
  lem-pairs-at0314203142 = pickᴰ 98 Sᴰ
  lem-pairs-at0314213042 : Ws → St 1348
  lem-pairs-at0314213042 = pickᴰ 99 Sᴰ
  lem-pairs-at0314213240 : Ws → St 1349
  lem-pairs-at0314213240 = pickᴰ 100 Sᴰ
  lem-pairs-at033440 : Ws → St 1350
  lem-pairs-at033440 = pickᴰ 101 Sᴰ
  lem-pairs-at12213443 : Ws → St 1351
  lem-pairs-at12213443 = pickᴰ 102 Sᴰ
  lem-pairs-at1441 : Ws → St 1352
  lem-pairs-at1441 = pickᴰ 103 Sᴰ
  lem-pairs-at233442 : Ws → St 1353
  lem-pairs-at233442 = pickᴰ 104 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 843 c4
  q3 : Ws → Eqn
  q3 c4 = wpE 845 c4
  q4 : Ws → Eqn
  q4 c4 = wlE 241 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wpE 89 c4
  q6 : Ws → Eqn
  q6 c4 = wpE 36 c4
  q7 : Ws → Eqn
  q7 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 35 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 34 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 88 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 97 c4
  q12 : Ws → Eqn
  q12 c4 = wlE 245 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 95 c4
  q14 : Ws → Eqn
  q14 c4 = sE 1059 (lem-comm-TOFF013-CX24 c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 94 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 246 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 842 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 90 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 247 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 81 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 244 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 87 c4
  q23 : Ws → Eqn
  q23 c4 = wlE 1037 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 305 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 1118 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1342 (lem-nf-comm-CS-S1at2 c4)

-- F1-comm-CS-S1@2: 91 steps
lem-F1-comm-CS-S1at2 : Ws → ⟪ (ℓ "侬乹") ⟫ʷ ≈ ⟪ (ℓ "乹侬") ⟫ʷ
lem-F1-comm-CS-S1at2 c4 = derive (ℓ "侬乹") (ℓ "乹侬")
  (re 0 1 (ℓ "仞亭侪亭侫") ∷
   re 2 1 (ℓ "乇") ∷
   re 4 1 (ℓ "么") ∷
   rw 0 (q1 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 1 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw 7 (q4 c4) ∷
   rw 4 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 9 (q13 c4) ∷
   rw 8 (q6 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 0 (q23 c4) ∷
   rw 2 (q24 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw⁻ 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = sE 53 (lem-sym-ab-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1343 (lem-pairs-at0214203143 c4)

-- box-perm-3421 @0210243143: 2 steps
lem-box-perm-3421-at0210243143 : Ws → ⟪ (ℓ "伱") ⟫ʷ ≈ ⟪ (ℓ "伵") ⟫ʷ
lem-box-perm-3421-at0210243143 c4 = derive (ℓ "伱") (ℓ "伵")
  (rw 0 (q27 c4) ∷
   rw 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wlE 230 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1325 (lem-box-perm-1324-at02233440 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1316 (lem-Xb-box-at022440 c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 925 c4
  q33 : Ws → Eqn
  q33 c4 = eqn (ℓ "亐並") (ℓ "並亐") (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))
  q34 : Ws → Eqn
  q34 c4 = wpE 610 c4
  q35 : Ws → Eqn
  q35 c4 = sE 1326 (lem-box-perm-1324-at022440 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 330 (lem-box-tQ-at02233440 c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 289 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wpE 21 c4
  q39 : Ws → Eqn
  q39 c4 = wpE 32 c4
  q40 : Ws → Eqn
  q40 c4 = wpE 39 c4
  q41 : Ws → Eqn
  q41 c4 = wpE 926 c4
  q42 : Ws → Eqn
  q42 c4 = wpE 927 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 617 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 928 c4
  q45 : Ws → Eqn
  q45 c4 = wlE 186 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (ℓ "丌亦") (ℓ "亦丌") (c₁ (K) (K ↑ • CCZ • K ↑ • iI))
  q47 : Ws → Eqn
  q47 c4 = sE 966 (lem-comm-TOFF213-CK40 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (ℓ "亦丢") (ℓ "丢亦") (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))
  q49 : Ws → Eqn
  q49 c4 = wpE 929 c4

-- CKc-box @02233440: 61 steps
lem-CKc-box-at02233440 : Ws → ⟪ (ℓ "伵亁") ⟫ʷ ≈ ⟪ (ℓ "亐亁亐伵") ⟫ʷ
lem-CKc-box-at02233440 c4 = derive (ℓ "伵亁") (ℓ "亐亁亐伵")
  (rw⁻ 1 (q29 c4) ∷
   rw 0 (q30 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   rw 1 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw 4 (q38 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q39 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q40 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 5 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 11 (q43 c4) ∷
   rw 13 (q37 c4) ∷
   rw 12 (q38 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q39 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q40 c4) ∷
   rw⁻ 12 (q37 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 3 (q37 c4) ∷
   rw 2 (q38 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q39 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q40 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw 3 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 9 (q43 c4) ∷
   rw 11 (q37 c4) ∷
   rw 10 (q38 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q39 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q40 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 1 (q45 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q29 c4) ∷
   rw 3 (q35 c4) ∷ []) Eq.refl

private
  q50 : Ws → Eqn
  q50 c4 = sE 1344 (lem-pairs-at02233440 c4)
  q51 : Ws → Eqn
  q51 c4 = sE 1029 (lem-sym-ab-at0214203143 c4)

-- box-perm-4312 @02233440: 2 steps
lem-box-perm-4312-at02233440 : Ws → ⟪ (ℓ "伵") ⟫ʷ ≈ ⟪ (ℓ "伱") ⟫ʷ
lem-box-perm-4312-at02233440 c4 = derive (ℓ "伵") (ℓ "伱")
  (rw 0 (q50 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = sE 1071 (lem-sym-ab-at243243 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 1284 (lem-pairs-at14213243 c4)

-- box-perm-3421 @243243: 2 steps
lem-box-perm-3421-at243243 : Ws → ⟪ (ℓ "仄") ⟫ʷ ≈ ⟪ (ℓ "付") ⟫ʷ
lem-box-perm-3421-at243243 c4 = derive (ℓ "仄") (ℓ "付")
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = wlE 181 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = sE 1335 (lem-box-perm-1324-at12233441 c4)
  q56 : Ws → Eqn
  q56 c4 = sE 1252 (lem-Xb-box-at122441 c4)
  q57 : Ws → Eqn
  q57 c4 = wlE 1139 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (ℓ "交並") (ℓ "並交") (c₄ (CCZ ↑) (X))
  q59 : Ws → Eqn
  q59 c4 = wlE 720 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = sE 1255 (lem-box-perm-1324-at122441 c4)
  q61 : Ws → Eqn
  q61 c4 = sE 312 (lem-box-tQ-at12233441 c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 233 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wpE 53 c4
  q64 : Ws → Eqn
  q64 c4 = sE 893 (lem-comm-CCZ014-CX23 c4)
  q65 : Ws → Eqn
  q65 c4 = wpE 60 c4
  q66 : Ws → Eqn
  q66 c4 = wpE 67 c4
  q67 : Ws → Eqn
  q67 c4 = wpE 933 c4
  q68 : Ws → Eqn
  q68 c4 = wpE 934 c4
  q69 : Ws → Eqn
  q69 c4 = wpE 633 c4
  q70 : Ws → Eqn
  q70 c4 = wpE 935 c4
  q71 : Ws → Eqn
  q71 c4 = wlE 209 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wlE 735 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = sE 968 (lem-comm-TOFF023-CK41 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (ℓ "亙丢") (ℓ "丢亙") (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S))
  q75 : Ws → Eqn
  q75 c4 = wlE 1140 (lit c4)

-- CKc-box @12233441: 61 steps
lem-CKc-box-at12233441 : Ws → ⟪ (ℓ "付亄") ⟫ʷ ≈ ⟪ (ℓ "交亄交付") ⟫ʷ
lem-CKc-box-at12233441 c4 = derive (ℓ "付亄") (ℓ "交亄交付")
  (rw⁻ 1 (q54 c4) ∷
   rw 0 (q55 c4) ∷
   rw⁻ 0 (q56 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 1 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 5 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw 6 (q65 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw 5 (q67 c4) ∷
   rw 8 (q68 c4) ∷
   rw 11 (q69 c4) ∷
   rw 13 (q62 c4) ∷
   rw 12 (q63 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q65 c4) ∷
   rw 15 (q64 c4) ∷
   rw 16 (q66 c4) ∷
   rw⁻ 12 (q62 c4) ∷
   rw⁻ 5 (q70 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw 6 (q74 c4) ∷
   rw⁻ 7 (q71 c4) ∷
   rw 3 (q62 c4) ∷
   rw 2 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw 5 (q64 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw 3 (q67 c4) ∷
   rw 6 (q68 c4) ∷
   rw 9 (q69 c4) ∷
   rw 11 (q62 c4) ∷
   rw 10 (q63 c4) ∷
   rw 11 (q64 c4) ∷
   rw 12 (q65 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q66 c4) ∷
   rw⁻ 10 (q62 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw⁻ 2 (q72 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw⁻ 5 (q71 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 3 (q56 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q60 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = sE 1282 (lem-pairs-at12233441 c4)
  q77 : Ws → Eqn
  q77 c4 = sE 1079 (lem-sym-ab-at14213243 c4)

-- box-perm-4312 @12233441: 2 steps
lem-box-perm-4312-at12233441 : Ws → ⟪ (ℓ "付") ⟫ʷ ≈ ⟪ (ℓ "仄") ⟫ʷ
lem-box-perm-4312-at12233441 c4 = derive (ℓ "付") (ℓ "仄")
  (rw 0 (q76 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = sE 972 (lem-sym-ab-at122441 c4)
  q79 : Ws → Eqn
  q79 c4 = sE 1352 (lem-pairs-at1441 c4)

-- box-perm-3421 @122441: 2 steps
lem-box-perm-3421-at122441 : Ws → ⟪ (ℓ "仞") ⟫ʷ ≈ ⟪ (ℓ "仩") ⟫ʷ
lem-box-perm-3421-at122441 c4 = derive (ℓ "仞") (ℓ "仩")
  (rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = sE 1337 (lem-box-perm-1324-at13213442 c4)
  q81 : Ws → Eqn
  q81 c4 = sE 1310 (lem-Xb-box-at13243142 c4)
  q82 : Ws → Eqn
  q82 c4 = wlE 1144 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 725 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = sE 1312 (lem-box-perm-1324-at13243142 c4)
  q85 : Ws → Eqn
  q85 c4 = sE 259 (lem-box-tQ-at13213442 c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 297 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = sE 1058 (lem-comm-CCZ024-CX31 c4)
  q88 : Ws → Eqn
  q88 c4 = wpE 92 c4
  q89 : Ws → Eqn
  q89 c4 = wpE 936 c4
  q90 : Ws → Eqn
  q90 c4 = wpE 937 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 938 c4
  q92 : Ws → Eqn
  q92 c4 = wlE 234 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = wlE 743 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = sE 1027 (lem-comm-TOFF013-CK42 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (ℓ "云丢") (ℓ "丢云") (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S))
  q96 : Ws → Eqn
  q96 c4 = wlE 1145 (lit c4)

-- CKc-box @13213442: 61 steps
lem-CKc-box-at13213442 : Ws → ⟪ (ℓ "仩亇") ⟫ʷ ≈ ⟪ (ℓ "交亇交仩") ⟫ʷ
lem-CKc-box-at13213442 c4 = derive (ℓ "仩亇") (ℓ "交亇交仩")
  (rw⁻ 1 (q54 c4) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 1 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 5 (q86 c4) ∷
   rw 4 (q20 c4) ∷
   rw 5 (q87 c4) ∷
   rw 6 (q22 c4) ∷
   rw 7 (q87 c4) ∷
   rw 8 (q88 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 5 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 11 (q43 c4) ∷
   rw 13 (q86 c4) ∷
   rw 12 (q20 c4) ∷
   rw 13 (q87 c4) ∷
   rw 14 (q22 c4) ∷
   rw 15 (q87 c4) ∷
   rw 16 (q88 c4) ∷
   rw⁻ 12 (q86 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw⁻ 4 (q93 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q95 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 3 (q86 c4) ∷
   rw 2 (q20 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q22 c4) ∷
   rw 5 (q87 c4) ∷
   rw 6 (q88 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 3 (q89 c4) ∷
   rw 6 (q90 c4) ∷
   rw 9 (q43 c4) ∷
   rw 11 (q86 c4) ∷
   rw 10 (q20 c4) ∷
   rw 11 (q87 c4) ∷
   rw 12 (q22 c4) ∷
   rw 13 (q87 c4) ∷
   rw 14 (q88 c4) ∷
   rw⁻ 10 (q86 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q95 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q84 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = sE 1268 (lem-pairs-at13213442 c4)
  q98 : Ws → Eqn
  q98 c4 = sE 1308 (lem-sym-ab-at1441 c4)

-- box-perm-4312 @13213442: 2 steps
lem-box-perm-4312-at13213442 : Ws → ⟪ (ℓ "仩") ⟫ʷ ≈ ⟪ (ℓ "仞") ⟫ʷ
lem-box-perm-4312-at13213442 c4 = derive (ℓ "仩") (ℓ "仞")
  (rw 0 (q97 c4) ∷
   rw 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = sE 1323 (lem-box-perm-1324-at0210233441 c4)
  q100 : Ws → Eqn
  q100 c4 = sE 1315 (lem-Xb-box-at02102441 c4)
  q101 : Ws → Eqn
  q101 c4 = wpE 951 c4
  q102 : Ws → Eqn
  q102 c4 = sE 1324 (lem-box-perm-1324-at02102441 c4)
  q103 : Ws → Eqn
  q103 c4 = sE 306 (lem-box-tQ-at0210233441 c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 905 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 1152 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = sE 1299 (lem-comm-CCZ124-CX03 c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 1151 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wpE 919 c4
  q109 : Ws → Eqn
  q109 c4 = wlE 1159 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 1160 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wlE 1161 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = wlE 1162 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 1131 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wlE 1163 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = sE 1306 (lem-comm-TOFF203-CK41 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (ℓ "亚丢") (ℓ "丢亚") (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (S))
  q117 : Ws → Eqn
  q117 c4 = wpE 952 c4

-- CKc-box @0210233441: 61 steps
lem-CKc-box-at0210233441 : Ws → ⟪ (ℓ "估亄") ⟫ʷ ≈ ⟪ (ℓ "亐亄亐估") ⟫ʷ
lem-CKc-box-at0210233441 c4 = derive (ℓ "估亄") (ℓ "亐亄亐估")
  (rw⁻ 1 (q29 c4) ∷
   rw 0 (q99 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw⁻ 3 (q101 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   rw 1 (q102 c4) ∷
   rw 1 (q103 c4) ∷
   rw 5 (q104 c4) ∷
   rw 4 (q105 c4) ∷
   rw 5 (q106 c4) ∷
   rw 6 (q107 c4) ∷
   rw 7 (q106 c4) ∷
   rw 8 (q108 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 5 (q109 c4) ∷
   rw 8 (q110 c4) ∷
   rw 11 (q111 c4) ∷
   rw 13 (q104 c4) ∷
   rw 12 (q105 c4) ∷
   rw 13 (q106 c4) ∷
   rw 14 (q107 c4) ∷
   rw 15 (q106 c4) ∷
   rw 16 (q108 c4) ∷
   rw⁻ 12 (q104 c4) ∷
   rw⁻ 5 (q112 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q115 c4) ∷
   rw 6 (q116 c4) ∷
   rw⁻ 7 (q113 c4) ∷
   rw 3 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q106 c4) ∷
   rw 4 (q107 c4) ∷
   rw 5 (q106 c4) ∷
   rw 6 (q108 c4) ∷
   rw⁻ 2 (q104 c4) ∷
   rw 3 (q109 c4) ∷
   rw 6 (q110 c4) ∷
   rw 9 (q111 c4) ∷
   rw 11 (q104 c4) ∷
   rw 10 (q105 c4) ∷
   rw 11 (q106 c4) ∷
   rw 12 (q107 c4) ∷
   rw 13 (q106 c4) ∷
   rw 14 (q108 c4) ∷
   rw⁻ 10 (q104 c4) ∷
   rw⁻ 3 (q112 c4) ∷
   rw⁻ 1 (q113 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw 4 (q116 c4) ∷
   rw⁻ 5 (q113 c4) ∷
   rw⁻ 6 (q103 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw⁻ 0 (q117 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q29 c4) ∷
   rw 3 (q102 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = sE 1277 (lem-pairs-at0210233441 c4)
  q119 : Ws → Eqn
  q119 c4 = sE 1052 (lem-sym-bc-at0214213043 c4)

-- box-perm-1342 @0210233441: 3 steps
lem-box-perm-1342-at0210233441 : Ws → ⟪ (ℓ "估") ⟫ʷ ≈ ⟪ (ℓ "伱") ⟫ʷ
lem-box-perm-1342-at0210233441 c4 = derive (ℓ "估") (ℓ "伱")
  (rw 0 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = sE 1338 (lem-box-perm-1324-at233442 c4)
  q121 : Ws → Eqn
  q121 c4 = sE 1322 (lem-Xb-box-at2442 c4)
  q122 : Ws → Eqn
  q122 c4 = sE 1339 (lem-box-perm-1324-at2442 c4)
  q123 : Ws → Eqn
  q123 c4 = sE 342 (lem-box-tQ-at233442 c4)
  q124 : Ws → Eqn
  q124 c4 = wlE 242 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wpE 91 c4

-- CKc-box @233442: 61 steps
lem-CKc-box-at233442 : Ws → ⟪ (ℓ "仂亇") ⟫ʷ ≈ ⟪ (ℓ "交亇交仂") ⟫ʷ
lem-CKc-box-at233442 c4 = derive (ℓ "仂亇") (ℓ "交亇交仂")
  (rw⁻ 1 (q54 c4) ∷
   rw 0 (q120 c4) ∷
   rw⁻ 0 (q121 c4) ∷
   rw⁻ 3 (q82 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 1 (q122 c4) ∷
   rw 1 (q123 c4) ∷
   rw 5 (q124 c4) ∷
   rw 4 (q88 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q125 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 4 (q124 c4) ∷
   rw 5 (q89 c4) ∷
   rw 8 (q90 c4) ∷
   rw 11 (q43 c4) ∷
   rw 13 (q124 c4) ∷
   rw 12 (q88 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q125 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q20 c4) ∷
   rw⁻ 12 (q124 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw⁻ 3 (q92 c4) ∷
   rw⁻ 4 (q93 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q95 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 3 (q124 c4) ∷
   rw 2 (q88 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q125 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 2 (q124 c4) ∷
   rw 3 (q89 c4) ∷
   rw 6 (q90 c4) ∷
   rw 9 (q43 c4) ∷
   rw 11 (q124 c4) ∷
   rw 10 (q88 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q125 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 10 (q124 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 1 (q92 c4) ∷
   rw⁻ 2 (q93 c4) ∷
   rw 3 (q94 c4) ∷
   rw 4 (q95 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw⁻ 6 (q122 c4) ∷
   rw⁻ 0 (q96 c4) ∷
   rw 3 (q121 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q122 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = sE 1353 (lem-pairs-at233442 c4)
  q127 : Ws → Eqn
  q127 c4 = sE 1160 (lem-sym-bc-at143143 c4)

-- box-perm-1342 @233442: 3 steps
lem-box-perm-1342-at233442 : Ws → ⟪ (ℓ "仂") ⟫ʷ ≈ ⟪ (ℓ "仄") ⟫ʷ
lem-box-perm-1342-at233442 c4 = derive (ℓ "仂") (ℓ "仄")
  (rw 0 (q126 c4) ∷
   rw 0 (q127 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = sE 1334 (lem-box-perm-1324-at12213443 c4)
  q129 : Ws → Eqn
  q129 c4 = sE 1321 (lem-Xb-box-at12243143 c4)
  q130 : Ws → Eqn
  q130 c4 = wlE 1172 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = wlE 729 (lit c4)
  q132 : Ws → Eqn
  q132 c4 = sE 1336 (lem-box-perm-1324-at12243143 c4)
  q133 : Ws → Eqn
  q133 c4 = sE 341 (lem-box-tQ-at12213443 c4)
  q134 : Ws → Eqn
  q134 c4 = wlE 326 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = wpE 312 c4
  q136 : Ws → Eqn
  q136 c4 = sE 1298 (lem-comm-CCZ034-CX21 c4)
  q137 : Ws → Eqn
  q137 c4 = wpE 734 c4
  q138 : Ws → Eqn
  q138 c4 = wpE 314 c4
  q139 : Ws → Eqn
  q139 c4 = wpE 979 c4
  q140 : Ws → Eqn
  q140 c4 = wpE 980 c4
  q141 : Ws → Eqn
  q141 c4 = wpE 981 c4
  q142 : Ws → Eqn
  q142 c4 = wpE 982 c4
  q143 : Ws → Eqn
  q143 c4 = wlE 464 (lit c4)
  q144 : Ws → Eqn
  q144 c4 = eqn (ℓ "亍丞") (ℓ "丞亍") (c₃ (Toff) (K))
  q145 : Ws → Eqn
  q145 c4 = eqn (ℓ "亍亊") (ℓ "亊亍") (c₃ (Toff) (CK₁₀))
  q146 : Ws → Eqn
  q146 c4 = eqn (ℓ "亍丢") (ℓ "丢亍") (c₃ (Toff) (S ↑))
  q147 : Ws → Eqn
  q147 c4 = wlE 1173 (lit c4)

-- CKc-box @12213443: 61 steps
lem-CKc-box-at12213443 : Ws → ⟪ (ℓ "仑亊") ⟫ʷ ≈ ⟪ (ℓ "交亊交仑") ⟫ʷ
lem-CKc-box-at12213443 c4 = derive (ℓ "仑亊") (ℓ "交亊交仑")
  (rw⁻ 1 (q54 c4) ∷
   rw 0 (q128 c4) ∷
   rw⁻ 0 (q129 c4) ∷
   rw⁻ 3 (q130 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 3 (q131 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 1 (q132 c4) ∷
   rw 1 (q133 c4) ∷
   rw 5 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw 5 (q136 c4) ∷
   rw 6 (q137 c4) ∷
   rw 7 (q136 c4) ∷
   rw 8 (q138 c4) ∷
   rw⁻ 4 (q134 c4) ∷
   rw 5 (q139 c4) ∷
   rw 8 (q140 c4) ∷
   rw 11 (q141 c4) ∷
   rw 13 (q134 c4) ∷
   rw 12 (q135 c4) ∷
   rw 13 (q136 c4) ∷
   rw 14 (q137 c4) ∷
   rw 15 (q136 c4) ∷
   rw 16 (q138 c4) ∷
   rw⁻ 12 (q134 c4) ∷
   rw⁻ 5 (q142 c4) ∷
   rw⁻ 3 (q143 c4) ∷
   rw 4 (q144 c4) ∷
   rw 5 (q145 c4) ∷
   rw 6 (q146 c4) ∷
   rw⁻ 7 (q143 c4) ∷
   rw 3 (q134 c4) ∷
   rw 2 (q135 c4) ∷
   rw 3 (q136 c4) ∷
   rw 4 (q137 c4) ∷
   rw 5 (q136 c4) ∷
   rw 6 (q138 c4) ∷
   rw⁻ 2 (q134 c4) ∷
   rw 3 (q139 c4) ∷
   rw 6 (q140 c4) ∷
   rw 9 (q141 c4) ∷
   rw 11 (q134 c4) ∷
   rw 10 (q135 c4) ∷
   rw 11 (q136 c4) ∷
   rw 12 (q137 c4) ∷
   rw 13 (q136 c4) ∷
   rw 14 (q138 c4) ∷
   rw⁻ 10 (q134 c4) ∷
   rw⁻ 3 (q142 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw 2 (q144 c4) ∷
   rw 3 (q145 c4) ∷
   rw 4 (q146 c4) ∷
   rw⁻ 5 (q143 c4) ∷
   rw⁻ 6 (q133 c4) ∷
   rw⁻ 6 (q132 c4) ∷
   rw⁻ 0 (q147 c4) ∷
   rw 3 (q129 c4) ∷
   rw 4 (q54 c4) ∷
   rw 3 (q132 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = sE 1351 (lem-pairs-at12213443 c4)
  q149 : Ws → Eqn
  q149 c4 = sE 1309 (lem-sym-bc-at14233241 c4)

-- box-perm-1342 @12213443: 3 steps
lem-box-perm-1342-at12213443 : Ws → ⟪ (ℓ "仑") ⟫ʷ ≈ ⟪ (ℓ "仞") ⟫ʷ
lem-box-perm-1342-at12213443 c4 = derive (ℓ "仑") (ℓ "仞")
  (rw 0 (q148 c4) ∷
   rw 0 (q149 c4) ∷
   rw 0 (q98 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = sE 1270 (lem-pairs-at143143 c4)
  q151 : Ws → Eqn
  q151 c4 = sE 974 (lem-sym-ab-at233442 c4)

-- box-perm-4312 @143143: 2 steps
lem-box-perm-4312-at143143 : Ws → ⟪ (ℓ "伅") ⟫ʷ ≈ ⟪ (ℓ "仩") ⟫ʷ
lem-box-perm-4312-at143143 c4 = derive (ℓ "伅") (ℓ "仩")
  (rw 0 (q150 c4) ∷
   rw 0 (q151 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = sE 1229 (lem-sym-ab-at13213442 c4)

-- box-perm-3421 @13213442: 2 steps
lem-box-perm-3421-at13213442 : Ws → ⟪ (ℓ "仩") ⟫ʷ ≈ ⟪ (ℓ "伅") ⟫ʷ
lem-box-perm-3421-at13213442 c4 = derive (ℓ "仩") (ℓ "伅")
  (rw 0 (q152 c4) ∷
   rw 0 (q126 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = wpE 1009 c4
  q154 : Ws → Eqn
  q154 c4 = wlE 1195 (lit c4)
  q155 : Ws → Eqn
  q155 c4 = wlE 1196 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = wlE 1197 (lit c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (ℓ "丨亲") (ℓ "亲丨") (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))
  q158 : Ws → Eqn
  q158 c4 = wlE 1198 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wlE 442 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = wlE 1199 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = sE 357 (lem-box-tQ-at03143140 c4)
  q162 : Ws → Eqn
  q162 c4 = sE 1313 (lem-CSdu-box-3-at03143140 c4)

-- F0-R @01143043: 11 steps
lem-F0-R-at01143043 : Ws → ⟪ (ℓ "为亲乎亲乏") ⟫ʷ ≈ ⟪ (ℓ "亲乎亲乏侌为") ⟫ʷ
lem-F0-R-at01143043 c4 = derive (ℓ "为亲乎亲乏") (ℓ "亲乎亲乏侌为")
  (rw 0 (q153 c4) ∷
   rw⁻ 1 (q154 c4) ∷
   rw 4 (q153 c4) ∷
   rw⁻ 5 (q155 c4) ∷
   rw⁻ 2 (q156 c4) ∷
   rw 3 (q157 c4) ∷
   rw 4 (q158 c4) ∷
   rw⁻ 2 (q159 c4) ∷
   rw⁻ 6 (q160 c4) ∷
   rw⁻ 3 (q161 c4) ∷
   rw⁻ 3 (q162 c4) ∷ []) Eq.refl

private
  q163 : Ws → Eqn
  q163 c4 = sE 1314 (lem-CXu-box-4-at243243 c4)
  q164 : Ws → Eqn
  q164 c4 = wpE 1012 c4
  q165 : Ws → Eqn
  q165 c4 = sE 1302 (lem-comm-TOFF024-CS13 c4)
  q166 : Ws → Eqn
  q166 c4 = wlE 1208 (lit c4)
  q167 : Ws → Eqn
  q167 c4 = wpE 1013 c4
  q168 : Ws → Eqn
  q168 c4 = wlE 1209 (lit c4)

-- CXAu-S @01143043: 12 steps
lem-CXAu-S-at01143043 : Ws → ⟪ (ℓ "买侧") ⟫ʷ ≈ ⟪ (ℓ "侧买") ⟫ʷ
lem-CXAu-S-at01143043 c4 = derive (ℓ "买侧") (ℓ "侧买")
  (re 1 1 (ℓ "仄亲侥亲侦") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw 0 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 4 (q168 c4) ∷
   re 2 1 (ℓ "侥") ∷
   re 4 1 (ℓ "侦") ∷
   re 0 5 (ℓ "侧") ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = sE 894 (lem-sym-ab-at0310243142 c4)
  q170 : Ws → Eqn
  q170 c4 = sE 1347 (lem-pairs-at0314203142 c4)
  q171 : Ws → Eqn
  q171 c4 = sE 1155 (lem-sym-bc-at033440 c4)

-- box-perm-3241 @0310243142: 3 steps
lem-box-perm-3241-at0310243142 : Ws → ⟪ (ℓ "佨") ⟫ʷ ≈ ⟪ (ℓ "佯") ⟫ʷ
lem-box-perm-3241-at0310243142 c4 = derive (ℓ "佨") (ℓ "佯")
  (rw 0 (q169 c4) ∷
   rw 0 (q170 c4) ∷
   rw 0 (q171 c4) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = sE 1154 (lem-sym-bc-at03243240 c4)
  q173 : Ws → Eqn
  q173 c4 = sE 1350 (lem-pairs-at033440 c4)
  q174 : Ws → Eqn
  q174 c4 = sE 1031 (lem-sym-ab-at0314203142 c4)

-- box-perm-4213 @03243240: 3 steps
lem-box-perm-4213-at03243240 : Ws → ⟪ (ℓ "佯") ⟫ʷ ≈ ⟪ (ℓ "佨") ⟫ʷ
lem-box-perm-4213-at03243240 c4 = derive (ℓ "佯") (ℓ "佨")
  (rw 0 (q172 c4) ∷
   rw 0 (q173 c4) ∷
   rw 0 (q174 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = sE 1124 (lem-box-cP-at03243240 c4)
  q176 : Ws → Eqn
  q176 c4 = wpE 1027 c4
  q177 : Ws → Eqn
  q177 c4 = wlE 1224 (lit c4)
  q178 : Ws → Eqn
  q178 c4 = wpE 1026 c4
  q179 : Ws → Eqn
  q179 c4 = eqn (ℓ "不京") (ℓ "京不") (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q180 : Ws → Eqn
  q180 c4 = wpE 1003 c4
  q181 : Ws → Eqn
  q181 c4 = sE 0 (lem-comm-CX02-CCZ134 c4)
  q182 : Ws → Eqn
  q182 c4 = wlE 1221 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = wlE 1220 (lit c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (ℓ "丌京") (ℓ "京丌") (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q185 : Ws → Eqn
  q185 c4 = wpE 1004 c4
  q186 : Ws → Eqn
  q186 c4 = wlE 1189 (lit c4)
  q187 : Ws → Eqn
  q187 c4 = wlE 220 (lit c4)
  q188 : Ws → Eqn
  q188 c4 = wlE 1190 (lit c4)
  q189 : Ws → Eqn
  q189 c4 = sE 1301 (lem-comm-CX14-TOFF302 c4)
  q190 : Ws → Eqn
  q190 c4 = wpE 1005 c4
  q191 : Ws → Eqn
  q191 c4 = wpE 1006 c4
  q192 : Ws → Eqn
  q192 c4 = wpE 1007 c4
  q193 : Ws → Eqn
  q193 c4 = wpE 1008 c4
  q194 : Ws → Eqn
  q194 c4 = wpE 261 c4
  q195 : Ws → Eqn
  q195 c4 = wlE 1223 (lit c4)
  q196 : Ws → Eqn
  q196 c4 = sE 1341 (lem-box2-at03243240 c4)
  q197 : Ws → Eqn
  q197 c4 = wpE 1042 c4
  q198 : Ws → Eqn
  q198 c4 = wlE 263 (lit c4)
  q199 : Ws → Eqn
  q199 c4 = wpE 1047 c4

-- S2-SBOX(3;1;42;0): 86 steps
lem-S2-SBOX⟨3·1·42·0⟩ : Ws → ⟪ (ℓ "俜俜") ⟫ʷ ≈ ⟪ (ℓ "亨") ⟫ʷ
lem-S2-SBOX⟨3·1·42·0⟩ c4 = derive (ℓ "俜俜") (ℓ "亨")
  (re 1 1 (ℓ "佯亝俗亝俛") ∷
   re 3 1 (ℓ "丨") ∷
   re 5 1 (ℓ "丩") ∷
   re 0 1 (ℓ "佯亝俗亝俛") ∷
   re 2 1 (ℓ "丨") ∷
   re 4 1 (ℓ "丩") ∷
   rw 5 (q175 c4) ∷
   rw⁻ 4 (q176 c4) ∷
   rw 5 (q177 c4) ∷
   rw⁻ 6 (q176 c4) ∷
   rw 7 (q177 c4) ∷
   rw⁻ 4 (q175 c4) ∷
   rw 4 (q175 c4) ∷
   rw⁻ 3 (q178 c4) ∷
   rw 9 (q179 c4) ∷
   rw⁻ 8 (q180 c4) ∷
   rw 7 (q181 c4) ∷
   rw⁻ 6 (q182 c4) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 4 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q178 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 6 (q186 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw 11 (q179 c4) ∷
   rw⁻ 10 (q180 c4) ∷
   rw 9 (q181 c4) ∷
   rw⁻ 8 (q182 c4) ∷
   rw 7 (q181 c4) ∷
   rw⁻ 6 (q183 c4) ∷
   rw 5 (q184 c4) ∷
   rw 6 (q178 c4) ∷
   rw 8 (q187 c4) ∷
   rw 12 (q188 c4) ∷
   rw 11 (q189 c4) ∷
   rw 10 (q190 c4) ∷
   rw 9 (q189 c4) ∷
   rw 8 (q191 c4) ∷
   rw⁻ 9 (q187 c4) ∷
   rw⁻ 7 (q192 c4) ∷
   rw 6 (q185 c4) ∷
   rw 7 (q193 c4) ∷
   rw⁻ 3 (q175 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 2 (q194 c4) ∷
   rw 3 (q195 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw⁻ 2 (q175 c4) ∷
   rw 2 (q175 c4) ∷
   rw⁻ 1 (q178 c4) ∷
   rw 7 (q179 c4) ∷
   rw⁻ 6 (q180 c4) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 4 (q182 c4) ∷
   rw 3 (q181 c4) ∷
   rw⁻ 2 (q183 c4) ∷
   rw 1 (q184 c4) ∷
   rw 2 (q178 c4) ∷
   rw 2 (q185 c4) ∷
   rw⁻ 4 (q186 c4) ∷
   rw⁻ 3 (q178 c4) ∷
   rw 9 (q179 c4) ∷
   rw⁻ 8 (q180 c4) ∷
   rw 7 (q181 c4) ∷
   rw⁻ 6 (q182 c4) ∷
   rw 5 (q181 c4) ∷
   rw⁻ 4 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 4 (q178 c4) ∷
   rw 6 (q187 c4) ∷
   rw 10 (q188 c4) ∷
   rw 9 (q189 c4) ∷
   rw 8 (q190 c4) ∷
   rw 7 (q189 c4) ∷
   rw 6 (q191 c4) ∷
   rw⁻ 7 (q187 c4) ∷
   rw⁻ 5 (q192 c4) ∷
   rw 4 (q185 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 1 (q175 c4) ∷
   rw 0 (q196 c4) ∷
   rw 1 (q197 c4) ∷
   rw 3 (q198 c4) ∷
   rw⁻ 0 (q199 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = sE 1054 (lem-sym-bc-at0314203142 c4)
  q201 : Ws → Eqn
  q201 c4 = sE 1348 (lem-pairs-at0314213042 c4)

-- box-perm-1423 @0310243142: 3 steps
lem-box-perm-1423-at0310243142 : Ws → ⟪ (ℓ "佨") ⟫ʷ ≈ ⟪ (ℓ "佧") ⟫ʷ
lem-box-perm-1423-at0310243142 c4 = derive (ℓ "佨") (ℓ "佧")
  (rw 0 (q169 c4) ∷
   rw 0 (q200 c4) ∷
   rw 0 (q201 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = wlE 341 (lit c4)
  q203 : Ws → Eqn
  q203 c4 = sE 1329 (lem-box-perm-1324-at03103441 c4)
  q204 : Ws → Eqn
  q204 c4 = sE 1318 (lem-Xb-box-at0310243241 c4)
  q205 : Ws → Eqn
  q205 c4 = wpE 1061 c4
  q206 : Ws → Eqn
  q206 c4 = eqn (ℓ "二並") (ℓ "並二") (c₃ (CCZ) (X ↑))
  q207 : Ws → Eqn
  q207 c4 = sE 1328 (lem-box-perm-1324-at0310243241 c4)
  q208 : Ws → Eqn
  q208 c4 = sE 352 (lem-box-tQ-at03103441 c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 391 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = wlE 393 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = sE 1300 (lem-comm-CCZ134-CX02 c4)
  q212 : Ws → Eqn
  q212 c4 = wlE 392 (lit c4)
  q213 : Ws → Eqn
  q213 c4 = wlE 1247 (lit c4)
  q214 : Ws → Eqn
  q214 c4 = wlE 1248 (lit c4)
  q215 : Ws → Eqn
  q215 c4 = wlE 1249 (lit c4)
  q216 : Ws → Eqn
  q216 c4 = wlE 1250 (lit c4)
  q217 : Ws → Eqn
  q217 c4 = wlE 1251 (lit c4)
  q218 : Ws → Eqn
  q218 c4 = wlE 1252 (lit c4)
  q219 : Ws → Eqn
  q219 c4 = sE 1307 (lem-comm-TOFF302-CK41 c4)
  q220 : Ws → Eqn
  q220 c4 = eqn (ℓ "些丢") (ℓ "丢些") (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S))
  q221 : Ws → Eqn
  q221 c4 = wpE 1062 c4

-- CKc-box @03103441: 61 steps
lem-CKc-box-at03103441 : Ws → ⟪ (ℓ "佧亄") ⟫ʷ ≈ ⟪ (ℓ "二亄二佧") ⟫ʷ
lem-CKc-box-at03103441 c4 = derive (ℓ "佧亄") (ℓ "二亄二佧")
  (rw⁻ 1 (q202 c4) ∷
   rw 0 (q203 c4) ∷
   rw⁻ 0 (q204 c4) ∷
   rw⁻ 3 (q205 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 1 (q207 c4) ∷
   rw 1 (q208 c4) ∷
   rw 5 (q209 c4) ∷
   rw 4 (q210 c4) ∷
   rw 5 (q211 c4) ∷
   rw 6 (q212 c4) ∷
   rw 7 (q211 c4) ∷
   rw 8 (q194 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   rw 5 (q213 c4) ∷
   rw 8 (q214 c4) ∷
   rw 11 (q215 c4) ∷
   rw 13 (q209 c4) ∷
   rw 12 (q210 c4) ∷
   rw 13 (q211 c4) ∷
   rw 14 (q212 c4) ∷
   rw 15 (q211 c4) ∷
   rw 16 (q194 c4) ∷
   rw⁻ 12 (q209 c4) ∷
   rw⁻ 5 (q216 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw 5 (q219 c4) ∷
   rw 6 (q220 c4) ∷
   rw⁻ 7 (q217 c4) ∷
   rw 3 (q209 c4) ∷
   rw 2 (q210 c4) ∷
   rw 3 (q211 c4) ∷
   rw 4 (q212 c4) ∷
   rw 5 (q211 c4) ∷
   rw 6 (q194 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw 3 (q213 c4) ∷
   rw 6 (q214 c4) ∷
   rw 9 (q215 c4) ∷
   rw 11 (q209 c4) ∷
   rw 10 (q210 c4) ∷
   rw 11 (q211 c4) ∷
   rw 12 (q212 c4) ∷
   rw 13 (q211 c4) ∷
   rw 14 (q194 c4) ∷
   rw⁻ 10 (q209 c4) ∷
   rw⁻ 3 (q216 c4) ∷
   rw⁻ 1 (q217 c4) ∷
   rw⁻ 2 (q218 c4) ∷
   rw 3 (q219 c4) ∷
   rw 4 (q220 c4) ∷
   rw⁻ 5 (q217 c4) ∷
   rw⁻ 6 (q208 c4) ∷
   rw⁻ 6 (q207 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 3 (q204 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q207 c4) ∷ []) Eq.refl

private
  q222 : Ws → Eqn
  q222 c4 = sE 1345 (lem-pairs-at03103441 c4)
  q223 : Ws → Eqn
  q223 c4 = sE 1055 (lem-sym-bc-at0314213042 c4)

-- box-perm-1342 @03103441: 3 steps
lem-box-perm-1342-at03103441 : Ws → ⟪ (ℓ "佧") ⟫ʷ ≈ ⟪ (ℓ "佨") ⟫ʷ
lem-box-perm-1342-at03103441 c4 = derive (ℓ "佧") (ℓ "佨")
  (rw 0 (q222 c4) ∷
   rw 0 (q223 c4) ∷
   rw 0 (q174 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = sE 1311 (lem-box-perm-1324-at0310213442 c4)
  q225 : Ws → Eqn
  q225 c4 = sE 1317 (lem-Xb-box-at0310243142 c4)
  q226 : Ws → Eqn
  q226 c4 = wpE 1074 c4
  q227 : Ws → Eqn
  q227 c4 = sE 1327 (lem-box-perm-1324-at0310243142 c4)
  q228 : Ws → Eqn
  q228 c4 = sE 149 (lem-box-tQ-at0310213442 c4)
  q229 : Ws → Eqn
  q229 c4 = wlE 348 (lit c4)
  q230 : Ws → Eqn
  q230 c4 = wlE 415 (lit c4)
  q231 : Ws → Eqn
  q231 c4 = eqn (ℓ "丬亰") (ℓ "亰丬") (c₂ (CX₀₁) (CCZ))
  q232 : Ws → Eqn
  q232 c4 = wlE 414 (lit c4)
  q233 : Ws → Eqn
  q233 c4 = wpE 279 c4
  q234 : Ws → Eqn
  q234 c4 = wlE 1261 (lit c4)
  q235 : Ws → Eqn
  q235 c4 = wlE 1262 (lit c4)
  q236 : Ws → Eqn
  q236 c4 = wlE 1263 (lit c4)
  q237 : Ws → Eqn
  q237 c4 = wlE 1264 (lit c4)
  q238 : Ws → Eqn
  q238 c4 = wlE 1265 (lit c4)
  q239 : Ws → Eqn
  q239 c4 = wlE 1266 (lit c4)
  q240 : Ws → Eqn
  q240 c4 = sE 1304 (lem-comm-TOFF301-CK42 c4)
  q241 : Ws → Eqn
  q241 c4 = eqn (ℓ "亓丢") (ℓ "丢亓") (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (S))
  q242 : Ws → Eqn
  q242 c4 = wpE 1075 c4

-- CKc-box @0310213442: 61 steps
lem-CKc-box-at0310213442 : Ws → ⟪ (ℓ "佥亇") ⟫ʷ ≈ ⟪ (ℓ "二亇二佥") ⟫ʷ
lem-CKc-box-at0310213442 c4 = derive (ℓ "佥亇") (ℓ "二亇二佥")
  (rw⁻ 1 (q202 c4) ∷
   rw 0 (q224 c4) ∷
   rw⁻ 0 (q225 c4) ∷
   rw⁻ 3 (q226 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 1 (q227 c4) ∷
   rw 1 (q228 c4) ∷
   rw 5 (q229 c4) ∷
   rw 4 (q230 c4) ∷
   rw⁻ 5 (q231 c4) ∷
   rw 6 (q232 c4) ∷
   rw⁻ 7 (q231 c4) ∷
   rw 8 (q233 c4) ∷
   rw⁻ 4 (q229 c4) ∷
   rw 5 (q234 c4) ∷
   rw 8 (q235 c4) ∷
   rw 11 (q236 c4) ∷
   rw 13 (q229 c4) ∷
   rw 12 (q230 c4) ∷
   rw⁻ 13 (q231 c4) ∷
   rw 14 (q232 c4) ∷
   rw⁻ 15 (q231 c4) ∷
   rw 16 (q233 c4) ∷
   rw⁻ 12 (q229 c4) ∷
   rw⁻ 5 (q237 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw⁻ 4 (q239 c4) ∷
   rw 5 (q240 c4) ∷
   rw 6 (q241 c4) ∷
   rw⁻ 7 (q238 c4) ∷
   rw 3 (q229 c4) ∷
   rw 2 (q230 c4) ∷
   rw⁻ 3 (q231 c4) ∷
   rw 4 (q232 c4) ∷
   rw⁻ 5 (q231 c4) ∷
   rw 6 (q233 c4) ∷
   rw⁻ 2 (q229 c4) ∷
   rw 3 (q234 c4) ∷
   rw 6 (q235 c4) ∷
   rw 9 (q236 c4) ∷
   rw 11 (q229 c4) ∷
   rw 10 (q230 c4) ∷
   rw⁻ 11 (q231 c4) ∷
   rw 12 (q232 c4) ∷
   rw⁻ 13 (q231 c4) ∷
   rw 14 (q233 c4) ∷
   rw⁻ 10 (q229 c4) ∷
   rw⁻ 3 (q237 c4) ∷
   rw⁻ 1 (q238 c4) ∷
   rw⁻ 2 (q239 c4) ∷
   rw 3 (q240 c4) ∷
   rw 4 (q241 c4) ∷
   rw⁻ 5 (q238 c4) ∷
   rw⁻ 6 (q228 c4) ∷
   rw⁻ 6 (q227 c4) ∷
   rw⁻ 0 (q242 c4) ∷
   rw 3 (q225 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q227 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = sE 996 (lem-box-cP-at0310243142 c4)
  q244 : Ws → Eqn
  q244 c4 = wpE 2 c4
  q245 : Ws → Eqn
  q245 c4 = wlE 1226 (lit c4)
  q246 : Ws → Eqn
  q246 c4 = wlE 888 (lit c4)
  q247 : Ws → Eqn
  q247 c4 = wpE 700 c4
  q248 : Ws → Eqn
  q248 c4 = wpE 106 c4
  q249 : Ws → Eqn
  q249 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q250 : Ws → Eqn
  q250 c4 = wpE 107 c4
  q251 : Ws → Eqn
  q251 c4 = wpE 108 c4
  q252 : Ws → Eqn
  q252 c4 = wpE 701 c4
  q253 : Ws → Eqn
  q253 c4 = wlE 777 (lit c4)
  q254 : Ws → Eqn
  q254 c4 = wpE 702 c4
  q255 : Ws → Eqn
  q255 c4 = wpE 41 c4
  q256 : Ws → Eqn
  q256 c4 = wlE 501 (lit c4)
  q257 : Ws → Eqn
  q257 c4 = sE 1025 (lem-comm-CX04-TOFF312 c4)
  q258 : Ws → Eqn
  q258 c4 = wlE 778 (lit c4)
  q259 : Ws → Eqn
  q259 c4 = wlE 499 (lit c4)
  q260 : Ws → Eqn
  q260 c4 = wlE 779 (lit c4)
  q261 : Ws → Eqn
  q261 c4 = wlE 780 (lit c4)
  q262 : Ws → Eqn
  q262 c4 = wpE 3 c4
  q263 : Ws → Eqn
  q263 c4 = wlE 861 (lit c4)
  q264 : Ws → Eqn
  q264 c4 = sE 1340 (lem-box2-at0310243142 c4)
  q265 : Ws → Eqn
  q265 c4 = wpE 1030 c4
  q266 : Ws → Eqn
  q266 c4 = wpE 161 c4
  q267 : Ws → Eqn
  q267 c4 = wpE 1076 c4

-- S2-SBOX(3;0;41;2): 86 steps
lem-S2-SBOX⟨3·0·41·2⟩ : Ws → ⟪ (ℓ "俖俖") ⟫ʷ ≈ ⟪ (ℓ "五") ⟫ʷ
lem-S2-SBOX⟨3·0·41·2⟩ c4 = derive (ℓ "俖俖") (ℓ "五")
  (re 1 1 (ℓ "佨亪俑亪俕") ∷
   re 3 1 (ℓ "丯") ∷
   re 5 1 (ℓ "丰") ∷
   re 0 1 (ℓ "佨亪俑亪俕") ∷
   re 2 1 (ℓ "丯") ∷
   re 4 1 (ℓ "丰") ∷
   rw 5 (q243 c4) ∷
   rw⁻ 4 (q244 c4) ∷
   rw 5 (q245 c4) ∷
   rw⁻ 6 (q244 c4) ∷
   rw 7 (q245 c4) ∷
   rw⁻ 4 (q243 c4) ∷
   rw 4 (q243 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw⁻ 9 (q247 c4) ∷
   rw⁻ 8 (q248 c4) ∷
   rw 7 (q249 c4) ∷
   rw⁻ 6 (q250 c4) ∷
   rw 5 (q249 c4) ∷
   rw⁻ 4 (q251 c4) ∷
   rw⁻ 3 (q252 c4) ∷
   rw 4 (q246 c4) ∷
   rw 4 (q253 c4) ∷
   rw⁻ 6 (q254 c4) ∷
   rw⁻ 5 (q246 c4) ∷
   rw⁻ 11 (q247 c4) ∷
   rw⁻ 10 (q248 c4) ∷
   rw 9 (q249 c4) ∷
   rw⁻ 8 (q250 c4) ∷
   rw 7 (q249 c4) ∷
   rw⁻ 6 (q251 c4) ∷
   rw⁻ 5 (q252 c4) ∷
   rw 6 (q246 c4) ∷
   rw 8 (q255 c4) ∷
   rw 12 (q256 c4) ∷
   rw 11 (q257 c4) ∷
   rw 10 (q258 c4) ∷
   rw 9 (q257 c4) ∷
   rw 8 (q259 c4) ∷
   rw⁻ 9 (q255 c4) ∷
   rw⁻ 7 (q260 c4) ∷
   rw 6 (q253 c4) ∷
   rw 7 (q261 c4) ∷
   rw⁻ 3 (q243 c4) ∷
   rw 3 (q243 c4) ∷
   rw⁻ 2 (q262 c4) ∷
   rw 3 (q263 c4) ∷
   rw⁻ 4 (q262 c4) ∷
   rw 5 (q263 c4) ∷
   rw⁻ 2 (q243 c4) ∷
   rw 2 (q243 c4) ∷
   rw⁻ 1 (q246 c4) ∷
   rw⁻ 7 (q247 c4) ∷
   rw⁻ 6 (q248 c4) ∷
   rw 5 (q249 c4) ∷
   rw⁻ 4 (q250 c4) ∷
   rw 3 (q249 c4) ∷
   rw⁻ 2 (q251 c4) ∷
   rw⁻ 1 (q252 c4) ∷
   rw 2 (q246 c4) ∷
   rw 2 (q253 c4) ∷
   rw⁻ 4 (q254 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw⁻ 9 (q247 c4) ∷
   rw⁻ 8 (q248 c4) ∷
   rw 7 (q249 c4) ∷
   rw⁻ 6 (q250 c4) ∷
   rw 5 (q249 c4) ∷
   rw⁻ 4 (q251 c4) ∷
   rw⁻ 3 (q252 c4) ∷
   rw 4 (q246 c4) ∷
   rw 6 (q255 c4) ∷
   rw 10 (q256 c4) ∷
   rw 9 (q257 c4) ∷
   rw 8 (q258 c4) ∷
   rw 7 (q257 c4) ∷
   rw 6 (q259 c4) ∷
   rw⁻ 7 (q255 c4) ∷
   rw⁻ 5 (q260 c4) ∷
   rw 4 (q253 c4) ∷
   rw 5 (q261 c4) ∷
   rw⁻ 1 (q243 c4) ∷
   rw 0 (q264 c4) ∷
   rw 1 (q265 c4) ∷
   rw 3 (q266 c4) ∷
   rw⁻ 0 (q267 c4) ∷ []) Eq.refl

private
  q268 : Ws → Eqn
  q268 c4 = sE 1078 (lem-sym-ab-at03243240 c4)
  q269 : Ws → Eqn
  q269 c4 = sE 1349 (lem-pairs-at0314213240 c4)

-- box-perm-3421 @03243240: 2 steps
lem-box-perm-3421-at03243240 : Ws → ⟪ (ℓ "佯") ⟫ʷ ≈ ⟪ (ℓ "佱") ⟫ʷ
lem-box-perm-3421-at03243240 c4 = derive (ℓ "佯") (ℓ "佱")
  (rw 0 (q268 c4) ∷
   rw 0 (q269 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = sE 1330 (lem-box-perm-1324-at0312203441 c4)
  q271 : Ws → Eqn
  q271 c4 = sE 1319 (lem-Xb-box-at0312243041 c4)
  q272 : Ws → Eqn
  q272 c4 = sE 1331 (lem-box-perm-1324-at0312243041 c4)
  q273 : Ws → Eqn
  q273 c4 = sE 353 (lem-box-tQ-at0312203441 c4)
  q274 : Ws → Eqn
  q274 c4 = wlE 1273 (lit c4)
  q275 : Ws → Eqn
  q275 c4 = sE 1303 (lem-comm-CCZ134-CX20 c4)

-- CKc-box @0312203441: 61 steps
lem-CKc-box-at0312203441 : Ws → ⟪ (ℓ "佱亄") ⟫ʷ ≈ ⟪ (ℓ "二亄二佱") ⟫ʷ
lem-CKc-box-at0312203441 c4 = derive (ℓ "佱亄") (ℓ "二亄二佱")
  (rw⁻ 1 (q202 c4) ∷
   rw 0 (q270 c4) ∷
   rw⁻ 0 (q271 c4) ∷
   rw⁻ 3 (q205 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 1 (q272 c4) ∷
   rw 1 (q273 c4) ∷
   rw 5 (q274 c4) ∷
   rw 4 (q194 c4) ∷
   rw 5 (q275 c4) ∷
   rw 6 (q176 c4) ∷
   rw 7 (q275 c4) ∷
   rw 8 (q210 c4) ∷
   rw⁻ 4 (q274 c4) ∷
   rw 5 (q213 c4) ∷
   rw 8 (q214 c4) ∷
   rw 11 (q215 c4) ∷
   rw 13 (q274 c4) ∷
   rw 12 (q194 c4) ∷
   rw 13 (q275 c4) ∷
   rw 14 (q176 c4) ∷
   rw 15 (q275 c4) ∷
   rw 16 (q210 c4) ∷
   rw⁻ 12 (q274 c4) ∷
   rw⁻ 5 (q216 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw 5 (q219 c4) ∷
   rw 6 (q220 c4) ∷
   rw⁻ 7 (q217 c4) ∷
   rw 3 (q274 c4) ∷
   rw 2 (q194 c4) ∷
   rw 3 (q275 c4) ∷
   rw 4 (q176 c4) ∷
   rw 5 (q275 c4) ∷
   rw 6 (q210 c4) ∷
   rw⁻ 2 (q274 c4) ∷
   rw 3 (q213 c4) ∷
   rw 6 (q214 c4) ∷
   rw 9 (q215 c4) ∷
   rw 11 (q274 c4) ∷
   rw 10 (q194 c4) ∷
   rw 11 (q275 c4) ∷
   rw 12 (q176 c4) ∷
   rw 13 (q275 c4) ∷
   rw 14 (q210 c4) ∷
   rw⁻ 10 (q274 c4) ∷
   rw⁻ 3 (q216 c4) ∷
   rw⁻ 1 (q217 c4) ∷
   rw⁻ 2 (q218 c4) ∷
   rw 3 (q219 c4) ∷
   rw 4 (q220 c4) ∷
   rw⁻ 5 (q217 c4) ∷
   rw⁻ 6 (q273 c4) ∷
   rw⁻ 6 (q272 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw 3 (q271 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q272 c4) ∷ []) Eq.refl

private
  q276 : Ws → Eqn
  q276 c4 = sE 1346 (lem-pairs-at0312203441 c4)
  q277 : Ws → Eqn
  q277 c4 = sE 1076 (lem-sym-ab-at0314213240 c4)

-- box-perm-4312 @0312203441: 2 steps
lem-box-perm-4312-at0312203441 : Ws → ⟪ (ℓ "佱") ⟫ʷ ≈ ⟪ (ℓ "佯") ⟫ʷ
lem-box-perm-4312-at0312203441 c4 = derive (ℓ "佱") (ℓ "佯")
  (rw 0 (q276 c4) ∷
   rw 0 (q277 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = sE 1333 (lem-box-perm-1324-at033440 c4)
  q279 : Ws → Eqn
  q279 c4 = sE 1320 (lem-Xb-box-at03243240 c4)
  q280 : Ws → Eqn
  q280 c4 = wpE 1105 c4
  q281 : Ws → Eqn
  q281 c4 = sE 1332 (lem-box-perm-1324-at03243240 c4)
  q282 : Ws → Eqn
  q282 c4 = sE 340 (lem-box-tQ-at033440 c4)
  q283 : Ws → Eqn
  q283 c4 = wlE 155 (lit c4)
  q284 : Ws → Eqn
  q284 c4 = sE 1285 (lem-comm-CCZ034-CX12 c4)
  q285 : Ws → Eqn
  q285 c4 = wpE 1 c4
  q286 : Ws → Eqn
  q286 c4 = wpE 1106 c4
  q287 : Ws → Eqn
  q287 c4 = wpE 1107 c4
  q288 : Ws → Eqn
  q288 c4 = wpE 1108 c4
  q289 : Ws → Eqn
  q289 c4 = wlE 503 (lit c4)
  q290 : Ws → Eqn
  q290 c4 = eqn (ℓ "丌产") (ℓ "产丌") (c₁ (K) (Toffᵗ))
  q291 : Ws → Eqn
  q291 c4 = sE 1305 (lem-comm-TOFF312-CK40 c4)
  q292 : Ws → Eqn
  q292 c4 = eqn (ℓ "产丢") (ℓ "丢产") (c₄ (Toffᵗ ↑) (S))
  q293 : Ws → Eqn
  q293 c4 = wpE 1109 c4

-- CKc-box @033440: 61 steps
lem-CKc-box-at033440 : Ws → ⟪ (ℓ "佭亁") ⟫ʷ ≈ ⟪ (ℓ "二亁二佭") ⟫ʷ
lem-CKc-box-at033440 c4 = derive (ℓ "佭亁") (ℓ "二亁二佭")
  (rw⁻ 1 (q202 c4) ∷
   rw 0 (q278 c4) ∷
   rw⁻ 0 (q279 c4) ∷
   rw⁻ 3 (q280 c4) ∷
   rw⁻ 2 (q206 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   rw⁻ 6 (q206 c4) ∷
   rw 1 (q281 c4) ∷
   rw 1 (q282 c4) ∷
   rw 5 (q283 c4) ∷
   rw 4 (q262 c4) ∷
   rw 5 (q284 c4) ∷
   rw 6 (q244 c4) ∷
   rw 7 (q284 c4) ∷
   rw 8 (q285 c4) ∷
   rw⁻ 4 (q283 c4) ∷
   rw 5 (q286 c4) ∷
   rw 8 (q287 c4) ∷
   rw 11 (q141 c4) ∷
   rw 13 (q283 c4) ∷
   rw 12 (q262 c4) ∷
   rw 13 (q284 c4) ∷
   rw 14 (q244 c4) ∷
   rw 15 (q284 c4) ∷
   rw 16 (q285 c4) ∷
   rw⁻ 12 (q283 c4) ∷
   rw⁻ 5 (q288 c4) ∷
   rw⁻ 3 (q289 c4) ∷
   rw⁻ 4 (q290 c4) ∷
   rw 5 (q291 c4) ∷
   rw 6 (q292 c4) ∷
   rw⁻ 7 (q289 c4) ∷
   rw 3 (q283 c4) ∷
   rw 2 (q262 c4) ∷
   rw 3 (q284 c4) ∷
   rw 4 (q244 c4) ∷
   rw 5 (q284 c4) ∷
   rw 6 (q285 c4) ∷
   rw⁻ 2 (q283 c4) ∷
   rw 3 (q286 c4) ∷
   rw 6 (q287 c4) ∷
   rw 9 (q141 c4) ∷
   rw 11 (q283 c4) ∷
   rw 10 (q262 c4) ∷
   rw 11 (q284 c4) ∷
   rw 12 (q244 c4) ∷
   rw 13 (q284 c4) ∷
   rw 14 (q285 c4) ∷
   rw⁻ 10 (q283 c4) ∷
   rw⁻ 3 (q288 c4) ∷
   rw⁻ 1 (q289 c4) ∷
   rw⁻ 2 (q290 c4) ∷
   rw 3 (q291 c4) ∷
   rw 4 (q292 c4) ∷
   rw⁻ 5 (q289 c4) ∷
   rw⁻ 6 (q282 c4) ∷
   rw⁻ 6 (q281 c4) ∷
   rw⁻ 0 (q293 c4) ∷
   rw 3 (q279 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q281 c4) ∷ []) Eq.refl
