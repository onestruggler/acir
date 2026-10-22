{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD033 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D033 (Sᴰ : SD033) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX40-TOFF312 ; lem-comm-CZ24-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CK03-CCZ124)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-I : Ws → St 1183
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K1 : Ws → St 1206
  lem-F4-I-K1 = pickᴰ 1 Sᴰ
  lem-F4-I-K2 : Ws → St 1207
  lem-F4-I-K2 = pickᴰ 2 Sᴰ
  lem-F4-I-K3 : Ws → St 1208
  lem-F4-I-K3 = pickᴰ 3 Sᴰ
  lem-sym-ab-at0410213243 : Ws → St 574
  lem-sym-ab-at0410213243 = pickᴰ 4 Sᴰ
  lem-sym-ab-at04203243 : Ws → St 817
  lem-sym-ab-at04203243 = pickᴰ 5 Sᴰ
  lem-sym-ab-at0314213240 : Ws → St 912
  lem-sym-ab-at0314213240 = pickᴰ 6 Sᴰ
  lem-sym-ab-at03243240 : Ws → St 914
  lem-sym-ab-at03243240 = pickᴰ 7 Sᴰ
  lem-sym-ab-at02142140 : Ws → St 1209
  lem-sym-ab-at02142140 = pickᴰ 8 Sᴰ
  lem-sym-ab-at022440 : Ws → St 1210
  lem-sym-ab-at022440 = pickᴰ 9 Sᴰ
  lem-sym-ab-at0410233142 : Ws → St 1211
  lem-sym-ab-at0410233142 = pickᴰ 10 Sᴰ
  lem-sym-ab-at04122041 : Ws → St 1212
  lem-sym-ab-at04122041 = pickᴰ 11 Sᴰ
  lem-sym-ab-at0413203142 : Ws → St 1213
  lem-sym-ab-at0413203142 = pickᴰ 12 Sᴰ
  lem-sym-ab-at0413213042 : Ws → St 1214
  lem-sym-ab-at0413213042 = pickᴰ 13 Sᴰ
  lem-sym-ab-at0413213240 : Ws → St 1215
  lem-sym-ab-at0413213240 = pickᴰ 14 Sᴰ
  lem-sym-ab-at04233042 : Ws → St 1216
  lem-sym-ab-at04233042 = pickᴰ 15 Sᴰ
  lem-sym-ab-at04233240 : Ws → St 1217
  lem-sym-ab-at04233240 = pickᴰ 16 Sᴰ
  lem-sym-ab-at0440 : Ws → St 1218
  lem-sym-ab-at0440 = pickᴰ 17 Sᴰ
  lem-box-tQ-at0210213443 : Ws → St 77
  lem-box-tQ-at0210213443 = pickᴰ 18 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 89
  lem-box-tQ-at0310213442 = pickᴰ 19 Sᴰ
  lem-CSu-box-2-at0214203143 : Ws → St 1219
  lem-CSu-box-2-at0214203143 = pickᴰ 20 Sᴰ
  lem-box-cP-at0214233041 : Ws → St 751
  lem-box-cP-at0214233041 = pickᴰ 21 Sᴰ
  lem-sym-bc-at0410213243 : Ws → St 1220
  lem-sym-bc-at0410213243 = pickᴰ 22 Sᴰ
  lem-box-cP-at0214213043 : Ws → St 843
  lem-box-cP-at0214213043 = pickᴰ 23 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 844
  lem-box-cP-at0310243142 = pickᴰ 24 Sᴰ
  lem-box-perm-1324-at0310213442 : Ws → St 1120
  lem-box-perm-1324-at0310213442 = pickᴰ 25 Sᴰ
  lem-sym-bc-at02233440 : Ws → St 978
  lem-sym-bc-at02233440 = pickᴰ 26 Sᴰ
  lem-sym-bc-at022440 : Ws → St 979
  lem-sym-bc-at022440 = pickᴰ 27 Sᴰ
  lem-sym-bc-at03243240 : Ws → St 990
  lem-sym-bc-at03243240 = pickᴰ 28 Sᴰ
  lem-sym-bc-at033440 : Ws → St 991
  lem-sym-bc-at033440 = pickᴰ 29 Sᴰ
  lem-box-box-4-at0314203142 : Ws → St 1221
  lem-box-box-4-at0314203142 = pickᴰ 30 Sᴰ
  lem-box-cP-at0412233041 : Ws → St 1020
  lem-box-cP-at0412233041 = pickᴰ 31 Sᴰ
  lem-box-perm-3124-at0310213442 : Ws → St 1222
  lem-box-perm-3124-at0310213442 = pickᴰ 32 Sᴰ
  lem-sym-bc-at041041 : Ws → St 1223
  lem-sym-bc-at041041 = pickᴰ 33 Sᴰ
  lem-sym-bc-at04122041 : Ws → St 1026
  lem-sym-bc-at04122041 = pickᴰ 34 Sᴰ
  lem-sym-bc-at04122140 : Ws → St 1224
  lem-sym-bc-at04122140 = pickᴰ 35 Sᴰ
  lem-sym-bc-at0413203142 : Ws → St 1225
  lem-sym-bc-at0413203142 = pickᴰ 36 Sᴰ
  lem-sym-bc-at0413213042 : Ws → St 1226
  lem-sym-bc-at0413213042 = pickᴰ 37 Sᴰ
  lem-sym-bc-at04233240 : Ws → St 1227
  lem-sym-bc-at04233240 = pickᴰ 38 Sᴰ
  lem-sym-bc-at0440 : Ws → St 1228
  lem-sym-bc-at0440 = pickᴰ 39 Sᴰ
  lem-F4-I-CS1 : Ws → St 1229
  lem-F4-I-CS1 = pickᴰ 40 Sᴰ
  lem-F4-I-CS2 : Ws → St 1230
  lem-F4-I-CS2 = pickᴰ 41 Sᴰ
  lem-pairs-at0214203143 : Ws → St 1152
  lem-pairs-at0214203143 = pickᴰ 42 Sᴰ
  lem-pairs-at02233440 : Ws → St 1153
  lem-pairs-at02233440 = pickᴰ 43 Sᴰ
  lem-pairs-at0314203142 : Ws → St 1156
  lem-pairs-at0314203142 = pickᴰ 44 Sᴰ
  lem-pairs-at033440 : Ws → St 1159
  lem-pairs-at033440 = pickᴰ 45 Sᴰ
  lem-CXu-box-4-at0214203143 : Ws → St 1231
  lem-CXu-box-4-at0214203143 = pickᴰ 46 Sᴰ
  lem-Kdu-box-at0214203143 : Ws → St 1232
  lem-Kdu-box-at0214203143 = pickᴰ 47 Sᴰ
  lem-Ku-box-at0214203143 : Ws → St 1233
  lem-Ku-box-at0214203143 = pickᴰ 48 Sᴰ
  lem-box-perm-1324-at04122041 : Ws → St 1234
  lem-box-perm-1324-at04122041 = pickᴰ 49 Sᴰ
  lem-box-perm-1423-at0214203143 : Ws → St 1205
  lem-box-perm-1423-at0214203143 = pickᴰ 50 Sᴰ
  lem-box-perm-2314-at0314203142 : Ws → St 1235
  lem-box-perm-2314-at0314203142 = pickᴰ 51 Sᴰ
  lem-box-perm-3421-at0213243041 : Ws → St 1236
  lem-box-perm-3421-at0213243041 = pickᴰ 52 Sᴰ
  lem-box-perm-4312-at0210213443 : Ws → St 1237
  lem-box-perm-4312-at0210213443 = pickᴰ 53 Sᴰ
  lem-pairs-at0410233241 : Ws → St 1238
  lem-pairs-at0410233241 = pickᴰ 54 Sᴰ
  lem-pairs-at04103143 : Ws → St 1239
  lem-pairs-at04103143 = pickᴰ 55 Sᴰ
  lem-pairs-at04122041 : Ws → St 1240
  lem-pairs-at04122041 = pickᴰ 56 Sᴰ
  lem-pairs-at0412233041 : Ws → St 1241
  lem-pairs-at0412233041 = pickᴰ 57 Sᴰ
  lem-pairs-at0413203142 : Ws → St 1242
  lem-pairs-at0413203142 = pickᴰ 58 Sᴰ
  lem-pairs-at0413213240 : Ws → St 1243
  lem-pairs-at0413213240 = pickᴰ 59 Sᴰ
  lem-pairs-at0440 : Ws → St 1244
  lem-pairs-at0440 = pickᴰ 60 Sᴰ
  lem-S2-SBOX⟨0·1·42·3⟩-at0440 : Ws → St 1245
  lem-S2-SBOX⟨0·1·42·3⟩-at0440 = pickᴰ 61 Sᴰ
  lem-box-perm-1324-at0214203143 : Ws → St 1246
  lem-box-perm-1324-at0214203143 = pickᴰ 62 Sᴰ
  lem-pairs-at0410233142 : Ws → St 1247
  lem-pairs-at0410233142 = pickᴰ 63 Sᴰ
  lem-pairs-at0412233140 : Ws → St 1248
  lem-pairs-at0412233140 = pickᴰ 64 Sᴰ
  lem-pairs-at043043 : Ws → St 1249
  lem-pairs-at043043 = pickᴰ 65 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K2 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS2 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ S4 ∷ []) (S4 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-I c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK43 ∷ []) (CK43 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K3 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-CS1 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (X4 ∷ S4 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ S4 ∷ X4 ∷ []) (lem-F4-I-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (X4 ∷ X4 ∷ []) [] (wl 1083 (lit c4))

-- ckt-TST part51: 82 steps
lem-ckt-TST-part51 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-ckt-TST-part51 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ X4 ∷ S4 ∷ X4 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) (X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ [])
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
  q8 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ []) (wl 1441 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wl 1471 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Bx4-2031 ∷ []) (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Bx4-2301 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (K1 ∷ CK01 ∷ S0 ∷ Toff401 ∷ []) (Toff401 ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wp 1320 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (K1 ∷ CCZ234 ∷ []) (CCZ234 ∷ K1 ∷ []) (c₂ (K ↑) (CCZ))
  q14 : Ws → Eqn
  q14 c4 = eqn (CK01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CK01 ∷ []) (c₂ (CK₀₁) (CCZ))
  q15 : Ws → Eqn
  q15 c4 = eqn (S0 ∷ CCZ234 ∷ []) (CCZ234 ∷ S0 ∷ []) (c₁ (S) (CCZ ↑))
  q16 : Ws → Eqn
  q16 c4 = eqn (CK01 ∷ X0 ∷ []) (X0 ∷ K1 ∷ CK01 ∷ S0 ∷ []) (wl 1443 (lit c4))

-- F4-CS2-K1 @0440: 21 steps
lem-F4-CS2-K1-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K1-at0440 c4 = derive (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  (rw⁻ 2 (q8 c4) ∷
   re 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
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
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = eqn (Bx4-1023 ∷ []) (Bx4-0123 ∷ []) (lem-sym-ab-at04203243 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Bx4-0123 ∷ []) (Bx4-0213 ∷ []) (lem-sym-bc-at0410213243 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (Bx4-0213 ∷ []) (Bx4-1302 ∷ []) (lem-pairs-at04103143 c4)

-- box-perm-1423 @04203243: 3 steps
lem-box-perm-1423-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-box-perm-1423-at04203243 c4 = derive (Bx4-1023 ∷ []) (Bx4-1302 ∷ [])
  (rw 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 0 (q19 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = eqn (Bx4-2031 ∷ []) (Bx4-2301 ∷ []) (lem-sym-bc-at04122041 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Bx4-2301 ∷ []) (Bx4-0123 ∷ []) (lem-pairs-at0412233041 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (Bx4-0123 ∷ []) (Bx4-1023 ∷ []) (lem-sym-ab-at0410213243 c4)

-- box-perm-4213 @04122041: 3 steps
lem-box-perm-4213-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-4213-at04122041 c4 = derive (Bx4-2031 ∷ []) (Bx4-1023 ∷ [])
  (rw 0 (q20 c4) ∷
   rw 0 (q21 c4) ∷
   rw 0 (q22 c4) ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = eqn (Bx4-2031 ∷ []) (Bx4-0231 ∷ []) (lem-sym-ab-at04122041 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx4-0231 ∷ []) (Bx4-0321 ∷ []) (lem-sym-bc-at041041 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx4-0321 ∷ []) (Bx4-2103 ∷ []) (lem-pairs-at0410233241 c4)

-- box-perm-1423 @04122041: 3 steps
lem-box-perm-1423-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2103 ∷ []) ⟫ʷ
lem-box-perm-1423-at04122041 c4 = derive (Bx4-2031 ∷ []) (Bx4-2103 ∷ [])
  (rw 0 (q23 c4) ∷
   rw 0 (q24 c4) ∷
   rw 0 (q25 c4) ∷ []) Eq.refl

private
  q26 : Ws → Eqn
  q26 c4 = eqn (X0 ∷ CCZ234 ∷ []) (CCZ234 ∷ X0 ∷ []) (c₁ (X) (CCZ ↑))
  q27 : Ws → Eqn
  q27 c4 = eqn (Toff401 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff401 ∷ []) (wp 1394 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (wl 1583 (lit c4))

-- F4-K1-CS2 @0440: 19 steps
lem-F4-K1-CS2-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-CS2-at0440 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
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
   re 2 1 (Sb4-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 0 5 (Sb4-2-03-1 ∷ []) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4301 ∷ []) (lem-box-perm-1423-at0214203143 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx2-4301 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0214233041 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff201 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff201 ∷ []) (wl 1439 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK01 ∷ X0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (wp 1292 c4)

-- F4-K1-CS0 @0440: 19 steps
lem-F4-K1-CS0-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-CS0-at0440 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
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
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx4-2031 ∷ []) (Bx4-3120 ∷ []) (lem-pairs-at04122041 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx4-3120 ∷ []) (Bx4-1320 ∷ []) (lem-sym-ab-at0413213240 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx4-1320 ∷ []) (Bx4-1230 ∷ []) (lem-sym-bc-at04233240 c4)

-- box-perm-4132 @04122041: 3 steps
lem-box-perm-4132-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-4132-at04122041 c4 = derive (Bx4-2031 ∷ []) (Bx4-1230 ∷ [])
  (rw 0 (q33 c4) ∷
   rw 0 (q34 c4) ∷
   rw 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx2-4013 ∷ []) (Bx2-1340 ∷ []) (lem-pairs-at0214203143 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Bx2-1340 ∷ []) (Bx2-1430 ∷ []) (lem-sym-bc-at02233440 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (Bx2-1430 ∷ []) (Bx2-4130 ∷ []) (lem-sym-ab-at022440 c4)

-- box-perm-1342 @0214203143: 3 steps
lem-box-perm-1342-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ []) ⟫ʷ
lem-box-perm-1342-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-4130 ∷ [])
  (rw 0 (q36 c4) ∷
   rw 0 (q37 c4) ∷
   rw 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx4-1230 ∷ []) (Bx4-3012 ∷ []) (lem-pairs-at0440 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx4-3012 ∷ []) (Bx4-3102 ∷ []) (lem-sym-bc-at0413203142 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx4-3102 ∷ []) (Bx4-1302 ∷ []) (lem-sym-ab-at0413213042 c4)

-- box-perm-1342 @0440: 3 steps
lem-box-perm-1342-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1302 ∷ []) ⟫ʷ
lem-box-perm-1342-at0440 c4 = derive (Bx4-1230 ∷ []) (Bx4-1302 ∷ [])
  (rw 0 (q39 c4) ∷
   rw 0 (q40 c4) ∷
   rw 0 (q41 c4) ∷ []) Eq.refl

private
  q42 : Ws → Eqn
  q42 c4 = eqn (Bx4-1302 ∷ []) (Bx4-3102 ∷ []) (lem-sym-ab-at04233042 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (Bx4-3102 ∷ []) (Bx4-3012 ∷ []) (lem-sym-bc-at0413213042 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx4-3012 ∷ []) (Bx4-1230 ∷ []) (lem-pairs-at0413203142 c4)

-- box-perm-1423 @04233042: 3 steps
lem-box-perm-1423-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-1423-at04233042 c4 = derive (Bx4-1302 ∷ []) (Bx4-1230 ∷ [])
  (rw 0 (q42 c4) ∷
   rw 0 (q43 c4) ∷
   rw 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx2-4130 ∷ []) (Bx2-1430 ∷ []) (lem-sym-ab-at02142140 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-1430 ∷ []) (Bx2-1340 ∷ []) (lem-sym-bc-at022440 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Bx2-1340 ∷ []) (Bx2-4013 ∷ []) (lem-pairs-at02233440 c4)

-- box-perm-1423 @02142140: 3 steps
lem-box-perm-1423-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-1423-at02142140 c4 = derive (Bx2-4130 ∷ []) (Bx2-4013 ∷ [])
  (rw 0 (q45 c4) ∷
   rw 0 (q46 c4) ∷
   rw 0 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = eqn (Bx4-1230 ∷ []) (Bx4-1320 ∷ []) (lem-sym-bc-at0440 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (Bx4-1320 ∷ []) (Bx4-3120 ∷ []) (lem-sym-ab-at04233240 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (Bx4-3120 ∷ []) (Bx4-2031 ∷ []) (lem-pairs-at0413213240 c4)

-- box-perm-2431 @0440: 3 steps
lem-box-perm-2431-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-box-perm-2431-at0440 c4 = derive (Bx4-1230 ∷ []) (Bx4-2031 ∷ [])
  (rw 0 (q48 c4) ∷
   rw 0 (q49 c4) ∷
   rw 0 (q50 c4) ∷ []) Eq.refl

private
  q51 : Ws → Eqn
  q51 c4 = eqn (CK02⁻ ∷ []) (CS02 ∷ K2⁻ ∷ CS02 ∷ K2 ∷ CS02 ∷ []) (wl 1632 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CS02 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CS02 ∷ []) (lem-CSu-box-2-at0214203143 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (K2 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2 ∷ []) (lem-Ku-box-at0214203143 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (K2⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ K2⁻ ∷ []) (lem-Kdu-box-at0214203143 c4)

-- CKdu-box-2 @0214203143: 7 steps
lem-CKdu-box-2-at0214203143 : Ws → ⟪ (CK02⁻ ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ CK02⁻ ∷ []) ⟫ʷ
lem-CKdu-box-2-at0214203143 c4 = derive (CK02⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CK02⁻ ∷ [])
  (rw 0 (q51 c4) ∷
   rw 4 (q52 c4) ∷
   rw 3 (q53 c4) ∷
   rw 2 (q52 c4) ∷
   rw 1 (q54 c4) ∷
   rw 0 (q52 c4) ∷
   rw⁻ 1 (q51 c4) ∷ []) Eq.refl

private
  q55 : Ws → Eqn
  q55 c4 = eqn (Bx2-0143 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CX23 ∷ Toff201 ∷ []) (Toff201 ∷ Toff301 ∷ CX23 ∷ []) (wl 1637 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ234 ∷ CZ24 ∷ CX23 ∷ []) (CX23 ∷ CCZ234 ∷ []) (wl 1638 (lit c4))
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ234 ∷ CZ24 ∷ []) (CX23 ∷ CCZ234 ∷ CX23 ∷ []) (wl 1639 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CZ24 ∷ Toff201 ∷ []) (Toff201 ∷ CZ24 ∷ CCZ014 ∷ []) (wp 1433 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ []) (wp 1173 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CZ24 ∷ Toff301 ∷ []) (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ014 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ014 ∷ []) (wp 1434 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ234 ∷ []) (CZ24 ∷ CCZ234 ∷ CZ24 ∷ []) (wl 844 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ Toff201 ∷ []) (wl 1386 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (Bx3-0142 ∷ []) (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2⁻ ∷ []) (Toff201 ∷ []) (wl 1640 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CCZ034 ∷ K2⁻ ∷ []) (K2⁻ ∷ CCZ034 ∷ []) (wp 700 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp 3 c4)
  q72 : Ws → Eqn
  q72 c4 = eqn (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) (wp 221 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ034 ∷ K2 ∷ []) (K2 ∷ CCZ034 ∷ []) (wp 701 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (Toff201 ∷ Toff312 ∷ []) (Toff312 ∷ Toff201 ∷ Toff301 ∷ []) (wl 1641 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ034 ∷ []) (wp 388 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp 1143 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CS14 ∷ Toff312 ∷ []) (Toff312 ∷ CS14 ∷ []) (wl 499 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (CX40 ∷ Toff312 ∷ []) (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (CS01⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS01⁻ ∷ []) (wl 500 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) (wl 501 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (Toff301 ∷ Toff312 ∷ []) (Toff312 ∷ Toff301 ∷ []) (wl 525 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (Toff201 ∷ Toff301 ∷ Toff301 ∷ []) (Toff201 ∷ []) (wl 1642 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ234 ∷ CS14 ∷ []) (CS14 ∷ CCZ234 ∷ []) (wl 452 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ234 ∷ CX40 ∷ []) (CX40 ∷ CCZ234 ∷ []) (wp 1171 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))
  q88 : Ws → Eqn
  q88 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ014 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ []) (wp 1189 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Bx3-0142 ∷ []) (Bx3-4012 ∷ []) (lem-box-perm-3124-at0310213442 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (Bx2-0143 ∷ []) (Bx2-3401 ∷ []) (lem-box-perm-4312-at0210213443 c4)
  q93 : Ws → Eqn
  q93 c4 = eqn (Bx3-4012 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-4012 ∷ []) (lem-box-box-4-at0314203142 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Bx2-3401 ∷ []) (Bx2-0143 ∷ []) (lem-box-perm-3421-at0213243041 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0142 ∷ []) (lem-box-perm-2314-at0314203142 c4)

-- F0-B @0410213243: 62 steps
lem-F0-B-at0410213243 : Ws → ⟪ (CX23 ∷ Bx2-0143 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ Bx3-0142 ∷ []) ⟫ʷ
lem-F0-B-at0410213243 c4 = derive (CX23 ∷ Bx2-0143 ∷ CX23 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ [])
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
  q96 c4 = eqn (CX32 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CX32 ∷ []) (lem-CXu-box-4-at0214203143 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CX32 ∷ Toff301 ∷ []) (Toff301 ∷ CX32 ∷ Toff201 ∷ []) (wl 1655 (lit c4))
  q98 : Ws → Eqn
  q98 c4 = eqn (Toff201 ∷ CS34 ∷ []) (CS34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS))
  q99 : Ws → Eqn
  q99 c4 = eqn (CS34 ∷ CX32 ∷ []) (CX32 ∷ CS34 ∷ []) (wl 1656 (lit c4))
  q100 : Ws → Eqn
  q100 c4 = eqn (CX32 ∷ Toff201 ∷ Toff301 ∷ []) (Toff301 ∷ CX32 ∷ []) (wl 1657 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (CS34⁻ ∷ CX32 ∷ []) (CX32 ∷ CS34⁻ ∷ []) (wl 1658 (lit c4))

-- CXAu-S @0410213243: 12 steps
lem-CXAu-S-at0410213243 : Ws → ⟪ (CX32 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ CX32 ∷ []) ⟫ʷ
lem-CXAu-S-at0410213243 c4 = derive (CX32 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ CX32 ∷ [])
  (re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw 0 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 3 (q98 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 3 (q100 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q102 : Ws → Eqn
  q102 c4 = eqn (Bx3-4012 ∷ []) (Bx3-1240 ∷ []) (lem-pairs-at0314203142 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (Bx3-1240 ∷ []) (Bx3-1420 ∷ []) (lem-sym-bc-at033440 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (Bx3-1420 ∷ []) (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4)

-- box-perm-1342 @0314203142: 3 steps
lem-box-perm-1342-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-box-perm-1342-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-4120 ∷ [])
  (rw 0 (q102 c4) ∷
   rw 0 (q103 c4) ∷
   rw 0 (q104 c4) ∷ []) Eq.refl

private
  q105 : Ws → Eqn
  q105 c4 = eqn (Bx4-3012 ∷ []) (Bx4-0312 ∷ []) (lem-sym-ab-at0413203142 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (Bx4-0312 ∷ []) (Bx4-1203 ∷ []) (lem-pairs-at0410233142 c4)

-- box-perm-1243 @0440: 3 steps
lem-box-perm-1243-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-1243-at0440 c4 = derive (Bx4-1230 ∷ []) (Bx4-1203 ∷ [])
  (rw 0 (q39 c4) ∷
   rw 0 (q105 c4) ∷
   rw 0 (q106 c4) ∷ []) Eq.refl

private
  q107 : Ws → Eqn
  q107 c4 = eqn (Bx4-1203 ∷ []) (Bx4-0312 ∷ []) (lem-pairs-at043043 c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Bx4-0312 ∷ []) (Bx4-3012 ∷ []) (lem-sym-ab-at0410233142 c4)

-- box-perm-1243 @043043: 3 steps
lem-box-perm-1243-at043043 : Ws → ⟪ (Bx4-1203 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-box-perm-1243-at043043 c4 = derive (Bx4-1203 ∷ []) (Bx4-1230 ∷ [])
  (rw 0 (q107 c4) ∷
   rw 0 (q108 c4) ∷
   rw 0 (q44 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = eqn (Bx3-4120 ∷ []) (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1240 ∷ []) (lem-sym-bc-at03243240 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx3-1240 ∷ []) (Bx3-4012 ∷ []) (lem-pairs-at033440 c4)

-- box-perm-1423 @0314213240: 3 steps
lem-box-perm-1423-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-1423-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Bx3-4012 ∷ [])
  (rw 0 (q109 c4) ∷
   rw 0 (q110 c4) ∷
   rw 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Bx4-1230 ∷ []) (Bx4-2130 ∷ []) (lem-sym-ab-at0440 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (Bx4-2130 ∷ []) (Bx4-2310 ∷ []) (lem-sym-bc-at04122140 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (Bx4-2310 ∷ []) (Bx4-1023 ∷ []) (lem-pairs-at0412233140 c4)

-- box-perm-1423 @0440: 3 steps
lem-box-perm-1423-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ []) ⟫ʷ
lem-box-perm-1423-at0440 c4 = derive (Bx4-1230 ∷ []) (Bx4-1023 ∷ [])
  (rw 0 (q112 c4) ∷
   rw 0 (q113 c4) ∷
   rw 0 (q114 c4) ∷ []) Eq.refl

private
  q115 : Ws → Eqn
  q115 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4103 ∷ []) (lem-box-perm-1324-at0214203143 c4)
  q116 : Ws → Eqn
  q116 c4 = eqn (Bx2-4103 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at0214213043 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (X0 ∷ CCZ124 ∷ []) (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))
  q118 : Ws → Eqn
  q118 c4 = eqn (CK03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4))
  q119 : Ws → Eqn
  q119 c4 = eqn (Toff203 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff203 ∷ []) (wl 1702 (lit c4))
  q120 : Ws → Eqn
  q120 c4 = eqn (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (wp 1455 c4)

-- F4-K3-CS0 @0440: 19 steps
lem-F4-K3-CS0-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS0-at0440 c4 = derive (X0 ∷ CK03 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
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
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q121 : Ws → Eqn
  q121 c4 = eqn (Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ []) (CCZ012 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩-at0440 c4)
  q122 : Ws → Eqn
  q122 c4 = eqn (CK02 ∷ CCZ012 ∷ CK02 ∷ S0 ∷ []) (Toff201 ∷ []) (wl 1704 (lit c4))

-- L-CX01-1 @0440: 2 steps
lem-L-CX01-1-at0440 : Ws → ⟪ (CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ []) ⟫ʷ
lem-L-CX01-1-at0440 c4 = derive (CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ []) (Toff201 ∷ [])
  (rw 1 (q121 c4) ∷
   rw 0 (q122 c4) ∷ []) Eq.refl
