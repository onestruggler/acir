{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD027 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D027 (Sᴰ : SD027) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX02-CCZ134 ; lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ024-CX31 ; lem-comm-CCZ034-CX12 ; lem-comm-CCZ034-CX21 ; lem-comm-CCZ124-CX03 ; lem-comm-CCZ134-CX02 ; lem-comm-CX04-TOFF312 ; lem-comm-CX14-TOFF302 ; lem-comm-TOFF013-CK42 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF024-CS13 ; lem-comm-TOFF213-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ134-CX20 ; lem-comm-TOFF301-CK42 ; lem-comm-TOFF312-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CK41 ; lem-comm-TOFF203-CK41 ; lem-comm-TOFF302-CK41)

-- The lemmas of other derivation modules (DSig).
private
  lem-sym-ab-at0210243143 : Ws → St 14
  lem-sym-ab-at0210243143 = pickᴰ 0 Sᴰ
  lem-sym-ab-at0214203143 : Ws → St 871
  lem-sym-ab-at0214203143 = pickᴰ 1 Sᴰ
  lem-sym-ab-at0310243142 : Ws → St 754
  lem-sym-ab-at0310243142 = pickᴰ 2 Sᴰ
  lem-sym-ab-at0314203142 : Ws → St 873
  lem-sym-ab-at0314203142 = pickᴰ 3 Sᴰ
  lem-sym-ab-at122441 : Ws → St 820
  lem-sym-ab-at122441 = pickᴰ 4 Sᴰ
  lem-sym-ab-at13213442 : Ws → St 1052
  lem-sym-ab-at13213442 = pickᴰ 5 Sᴰ
  lem-sym-ab-at233442 : Ws → St 822
  lem-sym-ab-at233442 = pickᴰ 6 Sᴰ
  lem-sym-ab-at243243 : Ws → St 907
  lem-sym-ab-at243243 = pickᴰ 7 Sᴰ
  lem-sym-ab-at0314213240 : Ws → St 912
  lem-sym-ab-at0314213240 = pickᴰ 8 Sᴰ
  lem-sym-ab-at03243240 : Ws → St 914
  lem-sym-ab-at03243240 = pickᴰ 9 Sᴰ
  lem-sym-ab-at14213243 : Ws → St 915
  lem-sym-ab-at14213243 = pickᴰ 10 Sᴰ
  lem-sym-ab-at1441 : Ws → St 1117
  lem-sym-ab-at1441 = pickᴰ 11 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 89
  lem-box-tQ-at0310213442 = pickᴰ 12 Sᴰ
  lem-box-tQ-at0210233441 : Ws → St 187
  lem-box-tQ-at0210233441 = pickᴰ 13 Sᴰ
  lem-box-tQ-at033440 : Ws → St 217
  lem-box-tQ-at033440 = pickᴰ 14 Sᴰ
  lem-box-tQ-at12213443 : Ws → St 218
  lem-box-tQ-at12213443 = pickᴰ 15 Sᴰ
  lem-box-tQ-at12233441 : Ws → St 193
  lem-box-tQ-at12233441 = pickᴰ 16 Sᴰ
  lem-box-tQ-at13213442 : Ws → St 158
  lem-box-tQ-at13213442 = pickᴰ 17 Sᴰ
  lem-box-tQ-at233442 : Ws → St 219
  lem-box-tQ-at233442 = pickᴰ 18 Sᴰ
  lem-box-tQ-at02233440 : Ws → St 211
  lem-box-tQ-at02233440 = pickᴰ 19 Sᴰ
  lem-box-tQ-at03103441 : Ws → St 229
  lem-box-tQ-at03103441 = pickᴰ 20 Sᴰ
  lem-box-tQ-at0312203441 : Ws → St 230
  lem-box-tQ-at0312203441 = pickᴰ 21 Sᴰ
  lem-box-tQ-at03143140 : Ws → St 234
  lem-box-tQ-at03143140 = pickᴰ 22 Sᴰ
  lem-sym-bc-at14233241 : Ws → St 1118
  lem-sym-bc-at14233241 = pickᴰ 23 Sᴰ
  lem-Xb-box-at13243142 : Ws → St 1119
  lem-Xb-box-at13243142 = pickᴰ 24 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 844
  lem-box-cP-at0310243142 = pickᴰ 25 Sᴰ
  lem-box-cP-at03243240 : Ws → St 960
  lem-box-cP-at03243240 = pickᴰ 26 Sᴰ
  lem-box-cP-at122441 : Ws → St 850
  lem-box-cP-at122441 = pickᴰ 27 Sᴰ
  lem-box-perm-1324-at0310213442 : Ws → St 1120
  lem-box-perm-1324-at0310213442 = pickᴰ 28 Sᴰ
  lem-box-perm-1324-at13243142 : Ws → St 1121
  lem-box-perm-1324-at13243142 = pickᴰ 29 Sᴰ
  lem-sym-bc-at0214213043 : Ws → St 894
  lem-sym-bc-at0214213043 = pickᴰ 30 Sᴰ
  lem-sym-bc-at0314203142 : Ws → St 896
  lem-sym-bc-at0314203142 = pickᴰ 31 Sᴰ
  lem-sym-bc-at0314213042 : Ws → St 897
  lem-sym-bc-at0314213042 = pickᴰ 32 Sᴰ
  lem-sym-bc-at03243240 : Ws → St 990
  lem-sym-bc-at03243240 = pickᴰ 33 Sᴰ
  lem-sym-bc-at033440 : Ws → St 991
  lem-sym-bc-at033440 = pickᴰ 34 Sᴰ
  lem-sym-bc-at143143 : Ws → St 996
  lem-sym-bc-at143143 = pickᴰ 35 Sᴰ
  lem-Xb-box-at122441 : Ws → St 1075
  lem-Xb-box-at122441 = pickᴰ 36 Sᴰ
  lem-box-perm-1324-at122441 : Ws → St 1078
  lem-box-perm-1324-at122441 = pickᴰ 37 Sᴰ
  lem-pairs-at13213442 : Ws → St 1091
  lem-pairs-at13213442 = pickᴰ 38 Sᴰ
  lem-pairs-at143143 : Ws → St 1093
  lem-pairs-at143143 = pickᴰ 39 Sᴰ
  lem-pairs-at0210233441 : Ws → St 1100
  lem-pairs-at0210233441 = pickᴰ 40 Sᴰ
  lem-pairs-at12233441 : Ws → St 1105
  lem-pairs-at12233441 = pickᴰ 41 Sᴰ
  lem-pairs-at14213243 : Ws → St 1107
  lem-pairs-at14213243 = pickᴰ 42 Sᴰ
  lem-CSdu-box-3-at03143140 : Ws → St 1122
  lem-CSdu-box-3-at03143140 = pickᴰ 43 Sᴰ
  lem-CXu-box-4-at243243 : Ws → St 1123
  lem-CXu-box-4-at243243 = pickᴰ 44 Sᴰ
  lem-Xb-box-at02102441 : Ws → St 1124
  lem-Xb-box-at02102441 = pickᴰ 45 Sᴰ
  lem-Xb-box-at022440 : Ws → St 1125
  lem-Xb-box-at022440 = pickᴰ 46 Sᴰ
  lem-Xb-box-at0310243142 : Ws → St 1126
  lem-Xb-box-at0310243142 = pickᴰ 47 Sᴰ
  lem-Xb-box-at0310243241 : Ws → St 1127
  lem-Xb-box-at0310243241 = pickᴰ 48 Sᴰ
  lem-Xb-box-at0312243041 : Ws → St 1128
  lem-Xb-box-at0312243041 = pickᴰ 49 Sᴰ
  lem-Xb-box-at03243240 : Ws → St 1129
  lem-Xb-box-at03243240 = pickᴰ 50 Sᴰ
  lem-Xb-box-at12243143 : Ws → St 1130
  lem-Xb-box-at12243143 = pickᴰ 51 Sᴰ
  lem-Xb-box-at2442 : Ws → St 1131
  lem-Xb-box-at2442 = pickᴰ 52 Sᴰ
  lem-box-perm-1324-at0210233441 : Ws → St 1132
  lem-box-perm-1324-at0210233441 = pickᴰ 53 Sᴰ
  lem-box-perm-1324-at02102441 : Ws → St 1133
  lem-box-perm-1324-at02102441 = pickᴰ 54 Sᴰ
  lem-box-perm-1324-at02233440 : Ws → St 1134
  lem-box-perm-1324-at02233440 = pickᴰ 55 Sᴰ
  lem-box-perm-1324-at022440 : Ws → St 1135
  lem-box-perm-1324-at022440 = pickᴰ 56 Sᴰ
  lem-box-perm-1324-at0310243142 : Ws → St 1136
  lem-box-perm-1324-at0310243142 = pickᴰ 57 Sᴰ
  lem-box-perm-1324-at0310243241 : Ws → St 1137
  lem-box-perm-1324-at0310243241 = pickᴰ 58 Sᴰ
  lem-box-perm-1324-at03103441 : Ws → St 1138
  lem-box-perm-1324-at03103441 = pickᴰ 59 Sᴰ
  lem-box-perm-1324-at0312203441 : Ws → St 1139
  lem-box-perm-1324-at0312203441 = pickᴰ 60 Sᴰ
  lem-box-perm-1324-at0312243041 : Ws → St 1140
  lem-box-perm-1324-at0312243041 = pickᴰ 61 Sᴰ
  lem-box-perm-1324-at03243240 : Ws → St 1141
  lem-box-perm-1324-at03243240 = pickᴰ 62 Sᴰ
  lem-box-perm-1324-at033440 : Ws → St 1142
  lem-box-perm-1324-at033440 = pickᴰ 63 Sᴰ
  lem-box-perm-1324-at12213443 : Ws → St 1143
  lem-box-perm-1324-at12213443 = pickᴰ 64 Sᴰ
  lem-box-perm-1324-at12233441 : Ws → St 1144
  lem-box-perm-1324-at12233441 = pickᴰ 65 Sᴰ
  lem-box-perm-1324-at12243143 : Ws → St 1145
  lem-box-perm-1324-at12243143 = pickᴰ 66 Sᴰ
  lem-box-perm-1324-at13213442 : Ws → St 1146
  lem-box-perm-1324-at13213442 = pickᴰ 67 Sᴰ
  lem-box-perm-1324-at233442 : Ws → St 1147
  lem-box-perm-1324-at233442 = pickᴰ 68 Sᴰ
  lem-box-perm-1324-at2442 : Ws → St 1148
  lem-box-perm-1324-at2442 = pickᴰ 69 Sᴰ
  lem-box2-at0310243142 : Ws → St 1149
  lem-box2-at0310243142 = pickᴰ 70 Sᴰ
  lem-box2-at03243240 : Ws → St 1150
  lem-box2-at03243240 = pickᴰ 71 Sᴰ
  lem-nf-comm-CS-S1at2 : Ws → St 1151
  lem-nf-comm-CS-S1at2 = pickᴰ 72 Sᴰ
  lem-pairs-at0214203143 : Ws → St 1152
  lem-pairs-at0214203143 = pickᴰ 73 Sᴰ
  lem-pairs-at02233440 : Ws → St 1153
  lem-pairs-at02233440 = pickᴰ 74 Sᴰ
  lem-pairs-at03103441 : Ws → St 1154
  lem-pairs-at03103441 = pickᴰ 75 Sᴰ
  lem-pairs-at0312203441 : Ws → St 1155
  lem-pairs-at0312203441 = pickᴰ 76 Sᴰ
  lem-pairs-at0314203142 : Ws → St 1156
  lem-pairs-at0314203142 = pickᴰ 77 Sᴰ
  lem-pairs-at0314213042 : Ws → St 1157
  lem-pairs-at0314213042 = pickᴰ 78 Sᴰ
  lem-pairs-at0314213240 : Ws → St 1158
  lem-pairs-at0314213240 = pickᴰ 79 Sᴰ
  lem-pairs-at033440 : Ws → St 1159
  lem-pairs-at033440 = pickᴰ 80 Sᴰ
  lem-pairs-at12213443 : Ws → St 1160
  lem-pairs-at12213443 = pickᴰ 81 Sᴰ
  lem-pairs-at1441 : Ws → St 1161
  lem-pairs-at1441 = pickᴰ 82 Sᴰ
  lem-pairs-at233442 : Ws → St 1162
  lem-pairs-at233442 = pickᴰ 83 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 850 (lem-box-cP-at122441 c4)
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
  q7 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
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
  q14 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
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
  q26 c4 = sE 1151 (lem-nf-comm-CS-S1at2 c4)

-- F1-comm-CS-S1@2: 91 steps
lem-F1-comm-CS-S1at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1at2 c4 = derive (Sb0-2-43-1 ∷ CS34 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ [])
  (re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
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
  q27 c4 = sE 14 (lem-sym-ab-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1152 (lem-pairs-at0214203143 c4)

-- box-perm-3421 @0210243143: 2 steps
lem-box-perm-3421-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-3421-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-1340 ∷ [])
  (rw 0 (q27 c4) ∷
   rw 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wlE 230 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1134 (lem-box-perm-1324-at02233440 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1125 (lem-Xb-box-at022440 c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 925 c4
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))
  q34 : Ws → Eqn
  q34 c4 = wpE 610 c4
  q35 : Ws → Eqn
  q35 c4 = sE 1135 (lem-box-perm-1324-at022440 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 211 (lem-box-tQ-at02233440 c4)
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
  q46 c4 = eqn (K0 ∷ Toff213 ∷ []) (Toff213 ∷ K0 ∷ []) (c₁ (K) (K ↑ • CCZ • K ↑ • iI))
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff213 ∷ CK40 ∷ []) (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (Toff213 ∷ S4 ∷ []) (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S))
  q49 : Ws → Eqn
  q49 c4 = wpE 929 c4

-- CKc-box @02233440: 61 steps
lem-CKc-box-at02233440 : Ws → ⟪ (Bx2-1340 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ []) ⟫ʷ
lem-CKc-box-at02233440 c4 = derive (Bx2-1340 ∷ CK40 ∷ []) (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ [])
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
  q50 c4 = sE 1153 (lem-pairs-at02233440 c4)
  q51 : Ws → Eqn
  q51 c4 = sE 871 (lem-sym-ab-at0214203143 c4)

-- box-perm-4312 @02233440: 2 steps
lem-box-perm-4312-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-4312-at02233440 c4 = derive (Bx2-1340 ∷ []) (Bx2-0413 ∷ [])
  (rw 0 (q50 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = sE 907 (lem-sym-ab-at243243 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 1107 (lem-pairs-at14213243 c4)

-- box-perm-3421 @243243: 2 steps
lem-box-perm-3421-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-3421-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-2341 ∷ [])
  (rw 0 (q52 c4) ∷
   rw 0 (q53 c4) ∷ []) Eq.refl

private
  q54 : Ws → Eqn
  q54 c4 = wlE 181 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = sE 1144 (lem-box-perm-1324-at12233441 c4)
  q56 : Ws → Eqn
  q56 c4 = sE 1075 (lem-Xb-box-at122441 c4)
  q57 : Ws → Eqn
  q57 c4 = wlE 1139 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ123 ∷ X4 ∷ []) (X4 ∷ CCZ123 ∷ []) (c₄ (CCZ ↑) (X))
  q59 : Ws → Eqn
  q59 c4 = wlE 720 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = sE 1078 (lem-box-perm-1324-at122441 c4)
  q61 : Ws → Eqn
  q61 c4 = sE 193 (lem-box-tQ-at12233441 c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 233 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wpE 53 c4
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
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
  q73 c4 = eqn (Toff023 ∷ CK41 ∷ []) (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (Toff023 ∷ S4 ∷ []) (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S))
  q75 : Ws → Eqn
  q75 c4 = wlE 1140 (lit c4)

-- CKc-box @12233441: 61 steps
lem-CKc-box-at12233441 : Ws → ⟪ (Bx0-2341 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) ⟫ʷ
lem-CKc-box-at12233441 c4 = derive (Bx0-2341 ∷ CK41 ∷ []) (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ [])
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
  q76 c4 = sE 1105 (lem-pairs-at12233441 c4)
  q77 : Ws → Eqn
  q77 c4 = sE 915 (lem-sym-ab-at14213243 c4)

-- box-perm-4312 @12233441: 2 steps
lem-box-perm-4312-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-4312-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q76 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

private
  q78 : Ws → Eqn
  q78 c4 = sE 820 (lem-sym-ab-at122441 c4)
  q79 : Ws → Eqn
  q79 c4 = sE 1161 (lem-pairs-at1441 c4)

-- box-perm-3421 @122441: 2 steps
lem-box-perm-3421-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-3421-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-3142 ∷ [])
  (rw 0 (q78 c4) ∷
   rw 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = sE 1146 (lem-box-perm-1324-at13213442 c4)
  q81 : Ws → Eqn
  q81 c4 = sE 1119 (lem-Xb-box-at13243142 c4)
  q82 : Ws → Eqn
  q82 c4 = wlE 1144 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = wlE 725 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = sE 1121 (lem-box-perm-1324-at13243142 c4)
  q85 : Ws → Eqn
  q85 c4 = sE 158 (lem-box-tQ-at13213442 c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 297 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ024 ∷ CX31 ∷ []) (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4))
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
  q94 c4 = eqn (Toff013 ∷ CK42 ∷ []) (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4))
  q95 : Ws → Eqn
  q95 c4 = eqn (Toff013 ∷ S4 ∷ []) (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S))
  q96 : Ws → Eqn
  q96 c4 = wlE 1145 (lit c4)

-- CKc-box @13213442: 61 steps
lem-CKc-box-at13213442 : Ws → ⟪ (Bx0-3142 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) ⟫ʷ
lem-CKc-box-at13213442 c4 = derive (Bx0-3142 ∷ CK42 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ [])
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
  q97 c4 = sE 1091 (lem-pairs-at13213442 c4)
  q98 : Ws → Eqn
  q98 c4 = sE 1117 (lem-sym-ab-at1441 c4)

-- box-perm-4312 @13213442: 2 steps
lem-box-perm-4312-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-4312-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-2431 ∷ [])
  (rw 0 (q97 c4) ∷
   rw 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = sE 1132 (lem-box-perm-1324-at0210233441 c4)
  q100 : Ws → Eqn
  q100 c4 = sE 1124 (lem-Xb-box-at02102441 c4)
  q101 : Ws → Eqn
  q101 c4 = wpE 951 c4
  q102 : Ws → Eqn
  q102 c4 = sE 1133 (lem-box-perm-1324-at02102441 c4)
  q103 : Ws → Eqn
  q103 c4 = sE 187 (lem-box-tQ-at0210233441 c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 905 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 1152 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ124 ∷ CX03 ∷ []) (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4))
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
  q115 c4 = eqn (Toff203 ∷ CK41 ∷ []) (CK41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CK41 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Toff203 ∷ S4 ∷ []) (S4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (S))
  q117 : Ws → Eqn
  q117 c4 = wpE 952 c4

-- CKc-box @0210233441: 61 steps
lem-CKc-box-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ []) ⟫ʷ
lem-CKc-box-at0210233441 c4 = derive (Bx2-0341 ∷ CK41 ∷ []) (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ [])
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
  q118 c4 = sE 1100 (lem-pairs-at0210233441 c4)
  q119 : Ws → Eqn
  q119 c4 = sE 894 (lem-sym-bc-at0214213043 c4)

-- box-perm-1342 @0210233441: 3 steps
lem-box-perm-1342-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-1342-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-0413 ∷ [])
  (rw 0 (q118 c4) ∷
   rw 0 (q119 c4) ∷
   rw 0 (q51 c4) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = sE 1147 (lem-box-perm-1324-at233442 c4)
  q121 : Ws → Eqn
  q121 c4 = sE 1131 (lem-Xb-box-at2442 c4)
  q122 : Ws → Eqn
  q122 c4 = sE 1148 (lem-box-perm-1324-at2442 c4)
  q123 : Ws → Eqn
  q123 c4 = sE 219 (lem-box-tQ-at233442 c4)
  q124 : Ws → Eqn
  q124 c4 = wlE 242 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wpE 91 c4

-- CKc-box @233442: 61 steps
lem-CKc-box-at233442 : Ws → ⟪ (Bx0-1342 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) ⟫ʷ
lem-CKc-box-at233442 c4 = derive (Bx0-1342 ∷ CK42 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ [])
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
  q126 c4 = sE 1162 (lem-pairs-at233442 c4)
  q127 : Ws → Eqn
  q127 c4 = sE 996 (lem-sym-bc-at143143 c4)

-- box-perm-1342 @233442: 3 steps
lem-box-perm-1342-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1342-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q126 c4) ∷
   rw 0 (q127 c4) ∷
   rw 0 (q77 c4) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = sE 1143 (lem-box-perm-1324-at12213443 c4)
  q129 : Ws → Eqn
  q129 c4 = sE 1130 (lem-Xb-box-at12243143 c4)
  q130 : Ws → Eqn
  q130 c4 = wlE 1172 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = wlE 729 (lit c4)
  q132 : Ws → Eqn
  q132 c4 = sE 1145 (lem-box-perm-1324-at12243143 c4)
  q133 : Ws → Eqn
  q133 c4 = sE 218 (lem-box-tQ-at12213443 c4)
  q134 : Ws → Eqn
  q134 c4 = wlE 326 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = wpE 312 c4
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ034 ∷ CX21 ∷ []) (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4))
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
  q144 c4 = eqn (Toff012 ∷ K3 ∷ []) (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K))
  q145 : Ws → Eqn
  q145 c4 = eqn (Toff012 ∷ CK43 ∷ []) (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀))
  q146 : Ws → Eqn
  q146 c4 = eqn (Toff012 ∷ S4 ∷ []) (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑))
  q147 : Ws → Eqn
  q147 c4 = wlE 1173 (lit c4)

-- CKc-box @12213443: 61 steps
lem-CKc-box-at12213443 : Ws → ⟪ (Bx0-2143 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) ⟫ʷ
lem-CKc-box-at12213443 c4 = derive (Bx0-2143 ∷ CK43 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ [])
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
  q148 c4 = sE 1160 (lem-pairs-at12213443 c4)
  q149 : Ws → Eqn
  q149 c4 = sE 1118 (lem-sym-bc-at14233241 c4)

-- box-perm-1342 @12213443: 3 steps
lem-box-perm-1342-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1342-at12213443 c4 = derive (Bx0-2143 ∷ []) (Bx0-2431 ∷ [])
  (rw 0 (q148 c4) ∷
   rw 0 (q149 c4) ∷
   rw 0 (q98 c4) ∷ []) Eq.refl

private
  q150 : Ws → Eqn
  q150 c4 = sE 1093 (lem-pairs-at143143 c4)
  q151 : Ws → Eqn
  q151 c4 = sE 822 (lem-sym-ab-at233442 c4)

-- box-perm-4312 @143143: 2 steps
lem-box-perm-4312-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-4312-at143143 c4 = derive (Bx0-4213 ∷ []) (Bx0-3142 ∷ [])
  (rw 0 (q150 c4) ∷
   rw 0 (q151 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = sE 1052 (lem-sym-ab-at13213442 c4)

-- box-perm-3421 @13213442: 2 steps
lem-box-perm-3421-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-3421-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-4213 ∷ [])
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
  q157 c4 = eqn (CS01 ∷ Toff324 ∷ []) (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))
  q158 : Ws → Eqn
  q158 c4 = wlE 1198 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wlE 442 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = wlE 1199 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = sE 234 (lem-box-tQ-at03143140 c4)
  q162 : Ws → Eqn
  q162 c4 = sE 1122 (lem-CSdu-box-3-at03143140 c4)

-- F0-R @01143043: 11 steps
lem-F0-R-at01143043 : Ws → ⟪ (CX03 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx3-4210 ∷ CX03 ∷ []) ⟫ʷ
lem-F0-R-at01143043 c4 = derive (CX03 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx3-4210 ∷ CX03 ∷ [])
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
  q163 c4 = sE 1123 (lem-CXu-box-4-at243243 c4)
  q164 : Ws → Eqn
  q164 c4 = wpE 1012 c4
  q165 : Ws → Eqn
  q165 c4 = eqn (Toff024 ∷ CS13 ∷ []) (CS13 ∷ Toff024 ∷ []) (lem-comm-TOFF024-CS13 (lit c4))
  q166 : Ws → Eqn
  q166 c4 = wlE 1208 (lit c4)
  q167 : Ws → Eqn
  q167 c4 = wpE 1013 c4
  q168 : Ws → Eqn
  q168 c4 = wlE 1209 (lit c4)

-- CXAu-S @01143043: 12 steps
lem-CXAu-S-at01143043 : Ws → ⟪ (CX30 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CX30 ∷ []) ⟫ʷ
lem-CXAu-S-at01143043 c4 = derive (CX30 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CX30 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 0 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 4 (q168 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q169 : Ws → Eqn
  q169 c4 = sE 754 (lem-sym-ab-at0310243142 c4)
  q170 : Ws → Eqn
  q170 c4 = sE 1156 (lem-pairs-at0314203142 c4)
  q171 : Ws → Eqn
  q171 c4 = sE 991 (lem-sym-bc-at033440 c4)

-- box-perm-3241 @0310243142: 3 steps
lem-box-perm-3241-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-3241-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-1420 ∷ [])
  (rw 0 (q169 c4) ∷
   rw 0 (q170 c4) ∷
   rw 0 (q171 c4) ∷ []) Eq.refl

private
  q172 : Ws → Eqn
  q172 c4 = sE 990 (lem-sym-bc-at03243240 c4)
  q173 : Ws → Eqn
  q173 c4 = sE 1159 (lem-pairs-at033440 c4)
  q174 : Ws → Eqn
  q174 c4 = sE 873 (lem-sym-ab-at0314203142 c4)

-- box-perm-4213 @03243240: 3 steps
lem-box-perm-4213-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-4213-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-0412 ∷ [])
  (rw 0 (q172 c4) ∷
   rw 0 (q173 c4) ∷
   rw 0 (q174 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = sE 960 (lem-box-cP-at03243240 c4)
  q176 : Ws → Eqn
  q176 c4 = wpE 1027 c4
  q177 : Ws → Eqn
  q177 c4 = wlE 1224 (lit c4)
  q178 : Ws → Eqn
  q178 c4 = wpE 1026 c4
  q179 : Ws → Eqn
  q179 c4 = eqn (K0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q180 : Ws → Eqn
  q180 c4 = wpE 1003 c4
  q181 : Ws → Eqn
  q181 c4 = eqn (CX02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = wlE 1221 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = wlE 1220 (lit c4)
  q184 : Ws → Eqn
  q184 c4 = eqn (K0 ∷ CCZ134 ∷ []) (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q185 : Ws → Eqn
  q185 c4 = wpE 1004 c4
  q186 : Ws → Eqn
  q186 c4 = wlE 1189 (lit c4)
  q187 : Ws → Eqn
  q187 c4 = wlE 220 (lit c4)
  q188 : Ws → Eqn
  q188 c4 = wlE 1190 (lit c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (CX14 ∷ Toff302 ∷ []) (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4))
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
  q196 c4 = sE 1150 (lem-box2-at03243240 c4)
  q197 : Ws → Eqn
  q197 c4 = wpE 1042 c4
  q198 : Ws → Eqn
  q198 c4 = wlE 263 (lit c4)
  q199 : Ws → Eqn
  q199 c4 = wpE 1047 c4

-- S2-SBOX(3;1;42;0): 86 steps
lem-S2-SBOX⟨3·1·42·0⟩ : Ws → ⟪ (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨3·1·42·0⟩ c4 = derive (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (CCZ124 ∷ [])
  (re 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 3 1 (CS01 ∷ []) ∷
   re 5 1 (CS01⁻ ∷ []) ∷
   re 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 2 1 (CS01 ∷ []) ∷
   re 4 1 (CS01⁻ ∷ []) ∷
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
  q200 c4 = sE 896 (lem-sym-bc-at0314203142 c4)
  q201 : Ws → Eqn
  q201 c4 = sE 1157 (lem-pairs-at0314213042 c4)

-- box-perm-1423 @0310243142: 3 steps
lem-box-perm-1423-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-box-perm-1423-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-0241 ∷ [])
  (rw 0 (q169 c4) ∷
   rw 0 (q200 c4) ∷
   rw 0 (q201 c4) ∷ []) Eq.refl

private
  q202 : Ws → Eqn
  q202 c4 = wlE 341 (lit c4)
  q203 : Ws → Eqn
  q203 c4 = sE 1138 (lem-box-perm-1324-at03103441 c4)
  q204 : Ws → Eqn
  q204 c4 = sE 1127 (lem-Xb-box-at0310243241 c4)
  q205 : Ws → Eqn
  q205 c4 = wpE 1061 c4
  q206 : Ws → Eqn
  q206 c4 = eqn (CCZ012 ∷ X4 ∷ []) (X4 ∷ CCZ012 ∷ []) (c₃ (CCZ) (X ↑))
  q207 : Ws → Eqn
  q207 c4 = sE 1137 (lem-box-perm-1324-at0310243241 c4)
  q208 : Ws → Eqn
  q208 c4 = sE 229 (lem-box-tQ-at03103441 c4)
  q209 : Ws → Eqn
  q209 c4 = wlE 391 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = wlE 393 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = eqn (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4))
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
  q219 c4 = eqn (Toff302 ∷ CK41 ∷ []) (CK41 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CK41 (lit c4))
  q220 : Ws → Eqn
  q220 c4 = eqn (Toff302 ∷ S4 ∷ []) (S4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S))
  q221 : Ws → Eqn
  q221 c4 = wpE 1062 c4

-- CKc-box @03103441: 61 steps
lem-CKc-box-at03103441 : Ws → ⟪ (Bx3-0241 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ
lem-CKc-box-at03103441 c4 = derive (Bx3-0241 ∷ CK41 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ [])
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
  q222 c4 = sE 1154 (lem-pairs-at03103441 c4)
  q223 : Ws → Eqn
  q223 c4 = sE 897 (lem-sym-bc-at0314213042 c4)

-- box-perm-1342 @03103441: 3 steps
lem-box-perm-1342-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1342-at03103441 c4 = derive (Bx3-0241 ∷ []) (Bx3-0412 ∷ [])
  (rw 0 (q222 c4) ∷
   rw 0 (q223 c4) ∷
   rw 0 (q174 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = sE 1120 (lem-box-perm-1324-at0310213442 c4)
  q225 : Ws → Eqn
  q225 c4 = sE 1126 (lem-Xb-box-at0310243142 c4)
  q226 : Ws → Eqn
  q226 c4 = wpE 1074 c4
  q227 : Ws → Eqn
  q227 c4 = sE 1136 (lem-box-perm-1324-at0310243142 c4)
  q228 : Ws → Eqn
  q228 c4 = sE 89 (lem-box-tQ-at0310213442 c4)
  q229 : Ws → Eqn
  q229 c4 = wlE 348 (lit c4)
  q230 : Ws → Eqn
  q230 c4 = wlE 415 (lit c4)
  q231 : Ws → Eqn
  q231 c4 = eqn (CX01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ))
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
  q240 c4 = eqn (Toff301 ∷ CK42 ∷ []) (CK42 ∷ Toff301 ∷ []) (lem-comm-TOFF301-CK42 (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (Toff301 ∷ S4 ∷ []) (S4 ∷ Toff301 ∷ []) (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (S))
  q242 : Ws → Eqn
  q242 c4 = wpE 1075 c4

-- CKc-box @0310213442: 61 steps
lem-CKc-box-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ
lem-CKc-box-at0310213442 c4 = derive (Bx3-0142 ∷ CK42 ∷ []) (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ [])
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
  q243 c4 = sE 844 (lem-box-cP-at0310243142 c4)
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
  q249 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
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
  q257 c4 = eqn (CX04 ∷ Toff312 ∷ []) (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4))
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
  q264 c4 = sE 1149 (lem-box2-at0310243142 c4)
  q265 : Ws → Eqn
  q265 c4 = wpE 1030 c4
  q266 : Ws → Eqn
  q266 c4 = wpE 161 c4
  q267 : Ws → Eqn
  q267 c4 = wpE 1076 c4

-- S2-SBOX(3;0;41;2): 86 steps
lem-S2-SBOX⟨3·0·41·2⟩ : Ws → ⟪ (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨3·0·41·2⟩ c4 = derive (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) (CCZ014 ∷ [])
  (re 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 3 1 (CS02 ∷ []) ∷
   re 5 1 (CS02⁻ ∷ []) ∷
   re 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 2 1 (CS02 ∷ []) ∷
   re 4 1 (CS02⁻ ∷ []) ∷
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
  q268 c4 = sE 914 (lem-sym-ab-at03243240 c4)
  q269 : Ws → Eqn
  q269 c4 = sE 1158 (lem-pairs-at0314213240 c4)

-- box-perm-3421 @03243240: 2 steps
lem-box-perm-3421-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-box-perm-3421-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-2041 ∷ [])
  (rw 0 (q268 c4) ∷
   rw 0 (q269 c4) ∷ []) Eq.refl

private
  q270 : Ws → Eqn
  q270 c4 = sE 1139 (lem-box-perm-1324-at0312203441 c4)
  q271 : Ws → Eqn
  q271 c4 = sE 1128 (lem-Xb-box-at0312243041 c4)
  q272 : Ws → Eqn
  q272 c4 = sE 1140 (lem-box-perm-1324-at0312243041 c4)
  q273 : Ws → Eqn
  q273 c4 = sE 230 (lem-box-tQ-at0312203441 c4)
  q274 : Ws → Eqn
  q274 c4 = wlE 1273 (lit c4)
  q275 : Ws → Eqn
  q275 c4 = eqn (CCZ134 ∷ CX20 ∷ []) (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4))

-- CKc-box @0312203441: 61 steps
lem-CKc-box-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) ⟫ʷ
lem-CKc-box-at0312203441 c4 = derive (Bx3-2041 ∷ CK41 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ [])
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
  q276 c4 = sE 1155 (lem-pairs-at0312203441 c4)
  q277 : Ws → Eqn
  q277 c4 = sE 912 (lem-sym-ab-at0314213240 c4)

-- box-perm-4312 @0312203441: 2 steps
lem-box-perm-4312-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-4312-at0312203441 c4 = derive (Bx3-2041 ∷ []) (Bx3-1420 ∷ [])
  (rw 0 (q276 c4) ∷
   rw 0 (q277 c4) ∷ []) Eq.refl

private
  q278 : Ws → Eqn
  q278 c4 = sE 1142 (lem-box-perm-1324-at033440 c4)
  q279 : Ws → Eqn
  q279 c4 = sE 1129 (lem-Xb-box-at03243240 c4)
  q280 : Ws → Eqn
  q280 c4 = wpE 1105 c4
  q281 : Ws → Eqn
  q281 c4 = sE 1141 (lem-box-perm-1324-at03243240 c4)
  q282 : Ws → Eqn
  q282 c4 = sE 217 (lem-box-tQ-at033440 c4)
  q283 : Ws → Eqn
  q283 c4 = wlE 155 (lit c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (CCZ034 ∷ CX12 ∷ []) (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4))
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
  q290 c4 = eqn (K0 ∷ Toff312 ∷ []) (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ))
  q291 : Ws → Eqn
  q291 c4 = eqn (Toff312 ∷ CK40 ∷ []) (CK40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CK40 (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (Toff312 ∷ S4 ∷ []) (S4 ∷ Toff312 ∷ []) (c₄ (Toffᵗ ↑) (S))
  q293 : Ws → Eqn
  q293 c4 = wpE 1109 c4

-- CKc-box @033440: 61 steps
lem-CKc-box-at033440 : Ws → ⟪ (Bx3-1240 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ []) ⟫ʷ
lem-CKc-box-at033440 c4 = derive (Bx3-1240 ∷ CK40 ∷ []) (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ [])
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
