{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0197 ; wl0199 ; wl0220 ; wl0245 ; wl0247 ; wl0289 ; wl0621 ; wl0671 ; wl1133 ; wl1134 ; wl1135 ; wl1136 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0041 ; wp0046 ; wp0047 ; wp0048 ; wp0066 ; wp0081 ; wp0513 ; wp0669 ; wp0680 ; wp0780 ; wp0781 ; wp0782 ; wp0820 ; wp0911 ; wp0912 ; wp0913 ; wp0914 ; wp0915 ; wp0919 ; wp0920 ; wp0922 ; wp0923 ; wl0159 ; wl0171 ; wl0172 ; wl0173 ; wl0227 ; wl0228 ; wl0327 ; wl0651 ; wl0682 ; wl0683 ; wl0684 ; wl0763 ; wl0764 ; wl0765 ; wl0770 ; wl0905 ; wl1008 ; wl1149 ; wl1150 ; wl1151 ; wl1152 ; wl1153 ; wl1154 ; wl1156 ; wl1157 ; wl1158 ; wp0013 ; wp0079 ; wp0092 ; wp0314 ; wp0939 ; wp0940 ; wp0941 ; wp0942 ; wp0943 ; wp0944 ; wp0945 ; wp0946 ; wp0947 ; wp0948 ; wp0949 ; wp0950 ; wl0201 ; wl0202 ; wl0242 ; wl0295 ; wl0299 ; wl0324 ; wl0326 ; wl0423 ; wl0424 ; wl0448 ; wl0613 ; wl0617 ; wl0646 ; wl0648 ; wl0673 ; wl0675 ; wl0676 ; wl1164 ; wl1165 ; wl1166 ; wl1167 ; wl1168 ; wl1170 ; wl1171 ; wp0050 ; wp0091 ; wp0129 ; wp0132 ; wp0133 ; wp0134 ; wp0181 ; wp0185 ; wp0186 ; wp0191 ; wp0192 ; wp0281 ; wp0286 ; wp0312 ; wp0357 ; wp0548 ; wp0593 ; wp0734 ; wp0735 ; wp0736 ; wp0784 ; wp0786 ; wp0815 ; wp0827 ; wp0955 ; wp0956 ; wp0960 ; wp0961 ; wp0962 ; wp0963 ; wp0964 ; wp0967 ; wp0968 ; wp0969 ; wp0970 ; wp0971 ; wp0974 ; wp0975 ; wp0976 ; wp0977 ; wp0978 ; wl0225 ; wl0259 ; wl0261 ; wl0318 ; wl0321 ; wl0342 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0645 ; wl0667 ; wl0668 ; wl0672 ; wl0674 ; wl0698 ; wl0702 ; wl0704 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0848 ; wl0851 ; wl1020 ; wl1021 ; wl1022 ; wl1179 ; wl1180 ; wl1181 ; wl1183 ; wl1184 ; wl1185 ; wl1186 ; wl1189 ; wl1190 ; wp0077 ; wp0112 ; wp0113 ; wp0114 ; wp0213 ; wp0393 ; wp0394 ; wp0540 ; wp0655 ; wp0703 ; wp0814 ; wp0898 ; wp0989 ; wp0990 ; wp0997 ; wp0998 ; wp1003 ; wp1007 ; wl0155 ; wl0332 ; wl0341 ; wl0488 ; wl0501 ; wl0504 ; wl0505 ; wl0506 ; wl0779 ; wl0803 ; wl0804 ; wl0858 ; wl0862 ; wl1203 ; wl1204 ; wl1213 ; wl1214 ; wl1215 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1228 ; wl1229 ; wl1230 ; wp0001 ; wp0002 ; wp0003 ; wp0029 ; wp0124 ; wp0261 ; wp0272 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0572 ; wp0575 ; wp0576 ; wp0578 ; wp0702 ; wp1017 ; wp1018 ; wp1019 ; wp1020 ; wp1021 ; wp1027 ; wp1031 ; wp1033 ; wp1034 ; wl0298 ; wl0348 ; wl0391 ; wl0392 ; wl0393 ; wl0406 ; wl0508 ; wl0618 ; wl0694 ; wl0695 ; wl0774 ; wl1235 ; wl1236 ; wl1240 ; wl1241 ; wl1242 ; wl1244 ; wl1245 ; wl1246 ; wl1253 ; wl1254 ; wl1255 ; wl1256 ; wp0688 ; wp0692 ; wp0727 ; wp0728 ; wp0729 ; wp0730 ; wp1049 ; wp1050 ; wp1051 ; wp1052 ; wp1053 ; wp1054 ; wp1055 ; wp1056 ; wp1057 ; wp1058 ; wp1059 ; wp1060 ; wp1063 ; wp1064 ; wp1065 ; wp1066 ; wp1067 ; wl0214 ; wl0644 ; wl0679 ; wl1272 ; wl1273 ; wl1277 ; wl1278 ; wp0145 ; wp0299 ; wp0521 ; wp0738 ; wp1077 ; wp1078 ; wp1079 ; wp1080 ; wp1081 ; wp1082 ; wp1083 ; wp1094 ; wp1095 ; wp1096 ; wp1097 ; wp1098 ; wp1099 ; wp1100 ; wl0207 ; wl0312 ; wl0315 ; wl1233 ; wl1283 ; wl1284 ; wp0103 ; wp0301 ; wp0313 ; wp0580 ; wp1041 ; wp1113 ; wp1114 ; wp1115 ; wl0960 ; wl1100 ; wl1300 ; wl1304 ; wl1305 ; wl1306 ; wl1307 ; wl1308 ; wp0296 ; wp1126 ; wp1128 ; wp1129 ; wl0444 ; wl0445 ; wl0543 ; wl0703 ; wl1317 ; wl1318 ; wl1320 ; wl1321 ; wl1322 ; wp0378 ; wp0380 ; wp0761 ; wp1141 ; wp1142 ; wp1143 ; wp1144 ; wp1145 ; wp1150)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ ; lem-box-tQ-at0210233441 ; lem-box-tQ-at0310243142 ; lem-box-tQ-at0314203142 ; lem-box-tQ-at0314213042 ; lem-box-tQ-at033440 ; lem-box-tQ-at12213443 ; lem-box-tQ-at143143 ; lem-box-tQ-at1441 ; lem-box-tQ-at233442 ; lem-box-tQ-at2442 ; lem-box-tQ-at3443 ; lem-tP-at0310243142 ; lem-tP-at0314203142 ; lem-tP-at0314213042 ; lem-tP-at12213443 ; lem-tP-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CXbc-box-at0310213442 ; lem-CXbc-box-at14233241 ; lem-CXcb-box-at0310213442 ; lem-CXcb-box-at14233241 ; lem-box-tQ-at02102441 ; lem-box-tQ-at02142041 ; lem-box-tQ-at02233440 ; lem-box-tQ-at022440 ; lem-box-tQ-at0310243241 ; lem-box-tQ-at031031 ; lem-box-tQ-at03103441 ; lem-box-tQ-at0312203441 ; lem-box-tQ-at0312243041 ; lem-box-tQ-at0314213240 ; lem-box-tQ-at03143041 ; lem-box-tQ-at03143140 ; lem-box-tQ-at03243240 ; lem-tP-at02102441 ; lem-tP-at02233440 ; lem-tP-at0310243241 ; lem-tP-at031031 ; lem-tP-at03103441 ; lem-tP-at0312203441 ; lem-tP-at0312243041 ; lem-tP-at0314213240 ; lem-tP-at03143140 ; lem-tP-at03243240 ; lem-tP-at033440 ; lem-tP-at12243143 ; lem-tP-at1441 ; lem-tP-at2442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-TOFF024 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd13-TOFF024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX02-CCZ134 ; lem-comm-CX04-CCZ123 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX24-CCZ013 ; lem-comm-CX42-CCZ013 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ04-TOFF312 ; lem-comm-CZ24-TOFF013 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF024-CSd13 ; lem-comm-TOFF204-CSd13 ; lem-comm-TOFF312-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS02-TOFF314 ; lem-comm-CS03-TOFF214 ; lem-comm-CS04-TOFF312 ; lem-comm-CS12-TOFF304 ; lem-comm-CS13-TOFF204 ; lem-comm-CS14-TOFF203 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CSd14-TOFF302 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX03-CCZ124 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ02-TOFF314 ; lem-comm-CZ12-TOFF304 ; lem-comm-CZ13-TOFF024 ; lem-comm-CZ14-TOFF302 ; lem-comm-CZ24-TOFF301 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF304-CSd12 ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS14-TOFF302 ; lem-comm-CX20-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF302-CSd14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-1430 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at022440 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CX34 ∷ Toff214 ∷ []) (Toff214 ∷ CX34 ∷ Toff213 ∷ []) (wl1133 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ023 ∷ Toff213 ∷ CCZ013 ∷ []) (Toff213 ∷ CCZ023 ∷ []) (wl1134 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ023 ∷ CX34 ∷ []) (CX34 ∷ CCZ023 ∷ []) (wp0680 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CS01 ∷ Toff214 ∷ []) (Toff214 ∷ CS01 ∷ []) (wp0923 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CX13 ∷ Toff214 ∷ []) (Toff214 ∷ CX13 ∷ []) (wl1135 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CS03⁻ ∷ Toff214 ∷ []) (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS03 ∷ Toff214 ∷ []) (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CX34 ∷ Toff213 ∷ Toff213 ∷ []) (CX34 ∷ []) (wl1136 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CCZ013 ∷ []) (CX34 ∷ CCZ013 ∷ CX34 ∷ []) (wp0913 c4)

-- CXcb-box @022440: 18 steps
lem-CXcb-box-at022440 : Ws → ⟪ (CX34 ∷ Bx2-1430 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at022440 c4 = derive (CX34 ∷ Bx2-1430 ∷ CX34 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
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
   rw 3 (q10 c4) ∷
   rw 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx2-1340 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02233440 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp0780 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ024 ∷ CZ04 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff204 ∷ []) (wp0781 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CZ04 ∷ Toff213 ∷ []) (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ []) (CZ04 ∷ CCZ024 ∷ CZ04 ∷ []) (wp0782 c4)

-- P-box @02233440: 8 steps
lem-P-box-at02233440 : Ws → ⟪ (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-P-box-at02233440 c4 = derive (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) (Bx2-1340 ∷ [])
  (rw 1 (q14 c4) ∷
   rw⁻ 0 (q15 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 0 (q14 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = eqn (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CS04⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (Toff213 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS04⁻ ∷ S2 ∷ []) (S2 ∷ CS04⁻ ∷ []) (wp0017 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CS04⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (S2⁻ ∷ S2 ∷ []) [] (wl0179 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS13⁻ ∷ S2 ∷ []) (S2 ∷ CS13⁻ ∷ []) (wl0178 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CS13⁻ ∷ Toff204 ∷ []) (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ CS13⁻ ∷ []) (wl0177 (lit c4))

-- VPQ @02233440: 14 steps
lem-VPQ-at02233440 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at02233440 c4 = derive (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q20 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw 2 (q23 c4) ∷
   rw⁻ 1 (q24 c4) ∷
   rw⁻ 0 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 1 (q27 c4) ∷
   rw 2 (q28 c4) ∷
   rw 3 (q29 c4) ∷
   rw 0 (q21 c4) ∷
   rw 2 (q20 c4) ∷ []) Eq.refl

private
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx0-4231 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at1441 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at1441 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ013 ∷ []) (wl0682 (lit c4))
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ013 ∷ CZ13 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff013 ∷ []) (wl0683 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CZ13 ∷ Toff024 ∷ []) (Toff024 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF024 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ013 ∷ []) (CZ13 ∷ CCZ013 ∷ CZ13 ∷ []) (wl0684 (lit c4))

-- P-box @1441: 8 steps
lem-P-box-at1441 : Ws → ⟪ (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-P-box-at1441 c4 = derive (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) (Bx0-4231 ∷ [])
  (rw 1 (q30 c4) ∷
   rw⁻ 0 (q31 c4) ∷
   rw⁻ 1 (q32 c4) ∷
   rw⁻ 3 (q31 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw⁻ 0 (q30 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (S0⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q39 : Ws → Eqn
  q39 c4 = eqn (Toff024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (S0 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q41 : Ws → Eqn
  q41 c4 = eqn (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) (wl0228 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (S0⁻ ∷ S0 ∷ []) [] (wl0159 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (S0 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS24⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (S0⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))

-- VPQ @1441: 14 steps
lem-VPQ-at1441 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at1441 c4 = derive (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q36 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 3 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw 3 (q31 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw 0 (q37 c4) ∷
   rw 2 (q36 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx2-0341 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CX34 ∷ Toff203 ∷ []) (Toff203 ∷ CX34 ∷ []) (wp0939 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ124 ∷ CX34 ∷ CCZ123 ∷ []) (CX34 ∷ CCZ124 ∷ []) (wl1149 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ123 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1150 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ124 ∷ CS01 ∷ []) (CS01 ∷ CCZ124 ∷ []) (wp0919 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CX03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ124 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ124 ∷ CS13 ∷ []) (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ123 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (CX34 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX34 ∷ []) (wl1153 (lit c4))

-- CXbc-box @0210233441: 17 steps
lem-CXbc-box-at0210233441 : Ws → ⟪ (CX34 ∷ Bx2-0341 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0210233441 c4 = derive (CX34 ∷ Bx2-0341 ∷ CX34 ∷ []) (Bx2-0341 ∷ CCZ013 ∷ [])
  (rw 1 (q46 c4) ∷
   rw 0 (q47 c4) ∷
   rw⁻ 1 (q48 c4) ∷
   rw 3 (q49 c4) ∷
   rw 2 (q47 c4) ∷
   rw 5 (q50 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw 6 (q52 c4) ∷
   rw⁻ 5 (q54 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   rw 4 (q55 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q57 : Ws → Eqn
  q57 c4 = eqn (CX43 ∷ Toff203 ∷ []) (Toff203 ∷ CX43 ∷ Toff204 ∷ []) (wp0940 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ124 ∷ Toff204 ∷ CCZ014 ∷ []) (Toff204 ∷ CCZ124 ∷ []) (wp0941 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ124 ∷ CX43 ∷ []) (CX43 ∷ CCZ124 ∷ []) (wl0651 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CS01 ∷ Toff203 ∷ []) (Toff203 ∷ CS01 ∷ []) (wl1154 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CX04 ∷ Toff203 ∷ []) (Toff203 ∷ CX04 ∷ []) (wp0942 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CS14⁻ ∷ Toff203 ∷ []) (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CS14 ∷ Toff203 ∷ []) (Toff203 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF203 (lit c4))
  q65 : Ws → Eqn
  q65 c4 = eqn (Toff203 ∷ Toff204 ∷ []) (Toff204 ∷ Toff203 ∷ []) (wp0943 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CX43 ∷ Toff204 ∷ Toff204 ∷ []) (CX43 ∷ []) (wp0944 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ014 ∷ []) (CX43 ∷ CCZ014 ∷ CX43 ∷ []) (wp0915 c4)

-- CXcb-box @0210233441: 18 steps
lem-CXcb-box-at0210233441 : Ws → ⟪ (CX43 ∷ Bx2-0341 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0210233441 c4 = derive (CX43 ∷ Bx2-0341 ∷ CX43 ∷ []) (Bx2-0341 ∷ CCZ014 ∷ [])
  (rw 1 (q46 c4) ∷
   rw 0 (q57 c4) ∷
   rw⁻ 2 (q58 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw 8 (q61 c4) ∷
   rw 7 (q62 c4) ∷
   rw 6 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw 4 (q64 c4) ∷
   rw⁻ 5 (q60 c4) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 2 (q57 c4) ∷
   rw 3 (q66 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   rw⁻ 1 (q68 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff204 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02102441 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CS04⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4))

-- VPQ @02102441: 14 steps
lem-VPQ-at02102441 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at02102441 c4 = derive (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q21 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw⁻ 3 (q29 c4) ∷
   rw 2 (q69 c4) ∷
   rw⁻ 1 (q27 c4) ∷
   rw 0 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   rw 3 (q70 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 1 (q24 c4) ∷
   rw 2 (q71 c4) ∷
   rw 3 (q22 c4) ∷
   rw 0 (q20 c4) ∷
   rw 2 (q21 c4) ∷ []) Eq.refl

private
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx2-0431 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CX43 ∷ Toff204 ∷ []) (Toff204 ∷ CX43 ∷ []) (wp0945 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CCZ123 ∷ CX43 ∷ CCZ124 ∷ []) (CX43 ∷ CCZ123 ∷ []) (wl1156 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ124 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0946 c4)
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CX04 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ123 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ123 ∷ []) (wl0764 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (CX43 ∷ CCZ124 ∷ CCZ124 ∷ []) (CX43 ∷ []) (wl1157 (lit c4))

-- CXbc-box @02102441: 17 steps
lem-CXbc-box-at02102441 : Ws → ⟪ (CX43 ∷ Bx2-0431 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at02102441 c4 = derive (CX43 ∷ Bx2-0431 ∷ CX43 ∷ []) (Bx2-0431 ∷ CCZ014 ∷ [])
  (rw 1 (q72 c4) ∷
   rw 0 (q73 c4) ∷
   rw⁻ 1 (q74 c4) ∷
   rw 3 (q75 c4) ∷
   rw 2 (q73 c4) ∷
   rw 5 (q60 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   rw 4 (q80 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q68 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = eqn (CX34 ∷ Toff204 ∷ []) (Toff204 ∷ CX34 ∷ Toff203 ∷ []) (wp0947 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ123 ∷ Toff203 ∷ CCZ013 ∷ []) (Toff203 ∷ CCZ123 ∷ []) (wl1158 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ123 ∷ CX34 ∷ []) (CX34 ∷ CCZ123 ∷ []) (wl1008 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (CS01 ∷ Toff204 ∷ []) (Toff204 ∷ CS01 ∷ []) (wp0948 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CX03 ∷ Toff204 ∷ []) (Toff204 ∷ CX03 ∷ []) (wp0949 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CS13 ∷ Toff204 ∷ []) (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4))
  q87 : Ws → Eqn
  q87 c4 = eqn (CX34 ∷ Toff203 ∷ Toff203 ∷ []) (CX34 ∷ []) (wp0950 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) (wl0327 (lit c4))

-- CXcb-box @02102441: 18 steps
lem-CXcb-box-at02102441 : Ws → ⟪ (CX34 ∷ Bx2-0431 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at02102441 c4 = derive (CX34 ∷ Bx2-0431 ∷ CX34 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  (rw 1 (q72 c4) ∷
   rw 0 (q81 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 4 (q50 c4) ∷
   rw 8 (q84 c4) ∷
   rw 7 (q85 c4) ∷
   rw 6 (q28 c4) ∷
   rw 5 (q85 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw 3 (q65 c4) ∷
   rw 2 (q81 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 0 (q72 c4) ∷
   rw⁻ 1 (q13 c4) ∷ []) Eq.refl

private
  q89 : Ws → Eqn
  q89 c4 = eqn (Bx0-1342 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (CX34 ∷ Toff013 ∷ []) (Toff013 ∷ CX34 ∷ []) (wp0286 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (CX34 ∷ CCZ024 ∷ []) (wp0911 c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (CCZ023 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1164 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp0081 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp0092 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CX34 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX34 ∷ []) (wp0912 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ123 ∷ []) (CX34 ∷ CCZ123 ∷ CX34 ∷ []) (wl0648 (lit c4))

-- CXbc-box @233442: 17 steps
lem-CXbc-box-at233442 : Ws → ⟪ (CX34 ∷ Bx0-1342 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at233442 c4 = derive (CX34 ∷ Bx0-1342 ∷ CX34 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ [])
  (rw 1 (q89 c4) ∷
   rw 0 (q90 c4) ∷
   rw⁻ 1 (q91 c4) ∷
   rw 3 (q92 c4) ∷
   rw 2 (q90 c4) ∷
   rw 5 (q93 c4) ∷
   rw⁻ 9 (q94 c4) ∷
   rw 8 (q95 c4) ∷
   rw⁻ 7 (q96 c4) ∷
   rw 6 (q95 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 6 (q93 c4) ∷
   rw 4 (q98 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw 4 (q99 c4) ∷
   rw⁻ 0 (q89 c4) ∷
   rw⁻ 1 (q100 c4) ∷ []) Eq.refl

private
  q101 : Ws → Eqn
  q101 c4 = eqn (CX43 ∷ Toff013 ∷ []) (Toff013 ∷ CX43 ∷ Toff014 ∷ []) (wp0955 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (Toff014 ∷ CCZ024 ∷ []) (wp0784 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ024 ∷ CX43 ∷ []) (CX43 ∷ CCZ024 ∷ []) (wp0914 c4)
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CX14 ∷ Toff013 ∷ []) (Toff013 ∷ CX14 ∷ []) (wp0281 c4)
  q107 : Ws → Eqn
  q107 c4 = eqn (CS24 ∷ Toff013 ∷ []) (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (Toff013 ∷ Toff014 ∷ []) (Toff014 ∷ Toff013 ∷ []) (wp0786 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (CX43 ∷ Toff014 ∷ Toff014 ∷ []) (CX43 ∷ []) (wp0956 c4)
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ024 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4)
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ124 ∷ []) (CX43 ∷ CCZ124 ∷ CX43 ∷ []) (wl0646 (lit c4))

-- CXcb-box @233442: 18 steps
lem-CXcb-box-at233442 : Ws → ⟪ (CX43 ∷ Bx0-1342 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at233442 c4 = derive (CX43 ∷ Bx0-1342 ∷ CX43 ∷ []) (Bx0-1342 ∷ CCZ124 ∷ [])
  (rw 1 (q89 c4) ∷
   rw 0 (q101 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw⁻ 1 (q103 c4) ∷
   rw 4 (q104 c4) ∷
   rw 8 (q105 c4) ∷
   rw 7 (q106 c4) ∷
   rw 6 (q44 c4) ∷
   rw 5 (q106 c4) ∷
   rw 4 (q107 c4) ∷
   rw⁻ 5 (q104 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 2 (q101 c4) ∷
   rw 3 (q109 c4) ∷
   rw⁻ 4 (q110 c4) ∷
   rw⁻ 3 (q103 c4) ∷
   rw⁻ 0 (q89 c4) ∷
   rw⁻ 1 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4)
  q113 : Ws → Eqn
  q113 c4 = eqn (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (S0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑))
  q115 : Ws → Eqn
  q115 c4 = eqn (Toff014 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (S0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑))
  q117 : Ws → Eqn
  q117 c4 = eqn (CS14⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS14⁻ ∷ []) (wl0202 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ []) (lem-tP-at2442 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (S0 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))
  q120 : Ws → Eqn
  q120 c4 = eqn (CS14⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (S0⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))

-- VPQ @2442: 14 steps
lem-VPQ-at2442 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at2442 c4 = derive (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  (rw⁻ 0 (q112 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw 3 (q114 c4) ∷
   rw 2 (q115 c4) ∷
   rw 1 (q116 c4) ∷
   rw 0 (q117 c4) ∷
   rw 4 (q42 c4) ∷
   rw 3 (q118 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 1 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw⁻ 3 (q121 c4) ∷
   rw 0 (q113 c4) ∷
   rw 2 (q112 c4) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = eqn (Bx0-1432 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at2442 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (CX43 ∷ Toff014 ∷ []) (Toff014 ∷ CX43 ∷ []) (wp0960 c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (CX43 ∷ CCZ023 ∷ []) (wp0920 c4)
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ024 ∷ Toff014 ∷ []) (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0815 c4)
  q126 : Ws → Eqn
  q126 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl0621 (lit c4))
  q127 : Ws → Eqn
  q127 c4 = eqn (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4))
  q128 : Ws → Eqn
  q128 c4 = eqn (CCZ023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ023 ∷ []) (wp0820 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp0513 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (CX43 ∷ CCZ024 ∷ CCZ024 ∷ []) (CX43 ∷ []) (wp0922 c4)

-- CXbc-box @2442: 17 steps
lem-CXbc-box-at2442 : Ws → ⟪ (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at2442 c4 = derive (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ [])
  (rw 1 (q122 c4) ∷
   rw 0 (q123 c4) ∷
   rw⁻ 1 (q124 c4) ∷
   rw 3 (q125 c4) ∷
   rw 2 (q123 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 9 (q126 c4) ∷
   rw 8 (q127 c4) ∷
   rw⁻ 7 (q128 c4) ∷
   rw 6 (q127 c4) ∷
   rw⁻ 5 (q129 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q124 c4) ∷
   rw 4 (q130 c4) ∷
   rw⁻ 0 (q122 c4) ∷
   rw⁻ 1 (q111 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (CX34 ∷ Toff014 ∷ []) (Toff014 ∷ CX34 ∷ Toff013 ∷ []) (wp0961 c4)
  q132 : Ws → Eqn
  q132 c4 = eqn (CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (Toff013 ∷ CCZ023 ∷ []) (wl1165 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = eqn (CS12 ∷ Toff014 ∷ []) (Toff014 ∷ CS12 ∷ []) (wp0962 c4)
  q134 : Ws → Eqn
  q134 c4 = eqn (CX13 ∷ Toff014 ∷ []) (Toff014 ∷ CX13 ∷ []) (wp0963 c4)
  q135 : Ws → Eqn
  q135 c4 = eqn (CS23⁻ ∷ Toff014 ∷ []) (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CS23 ∷ Toff014 ∷ []) (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4))
  q137 : Ws → Eqn
  q137 c4 = eqn (CX34 ∷ Toff013 ∷ Toff013 ∷ []) (CX34 ∷ []) (wp0964 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ023 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ023 ∷ []) (wl0613 (lit c4))

-- CXcb-box @2442: 18 steps
lem-CXcb-box-at2442 : Ws → ⟪ (CX34 ∷ Bx0-1432 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at2442 c4 = derive (CX34 ∷ Bx0-1432 ∷ CX34 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ [])
  (rw 1 (q122 c4) ∷
   rw 0 (q131 c4) ∷
   rw⁻ 2 (q132 c4) ∷
   rw⁻ 1 (q4 c4) ∷
   rw 4 (q93 c4) ∷
   rw 8 (q133 c4) ∷
   rw 7 (q134 c4) ∷
   rw 6 (q135 c4) ∷
   rw 5 (q134 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 5 (q93 c4) ∷
   rw 3 (q108 c4) ∷
   rw 2 (q131 c4) ∷
   rw 3 (q137 c4) ∷
   rw⁻ 4 (q138 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q122 c4) ∷
   rw⁻ 1 (q100 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (Toff013 ∷ Toff024 ∷ []) (Toff024 ∷ Toff013 ∷ []) (lem-tP-at233442 c4)
  q140 : Ws → Eqn
  q140 c4 = eqn (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ024 ∷ []) (wp0132 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (CCZ024 ∷ CZ24 ∷ []) (Toff024 ∷ CCZ024 ∷ Toff024 ∷ []) (wp0133 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (CZ24 ∷ Toff013 ∷ []) (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 (lit c4))
  q143 : Ws → Eqn
  q143 c4 = eqn (CCZ024 ∷ []) (CZ24 ∷ CCZ024 ∷ CZ24 ∷ []) (wp0134 c4)

-- P-box @233442: 8 steps
lem-P-box-at233442 : Ws → ⟪ (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-P-box-at233442 c4 = derive (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) (Bx0-1342 ∷ [])
  (rw 1 (q89 c4) ∷
   rw⁻ 0 (q139 c4) ∷
   rw⁻ 1 (q140 c4) ∷
   rw⁻ 3 (q139 c4) ∷
   rw⁻ 4 (q141 c4) ∷
   rw 2 (q142 c4) ∷
   rw⁻ 3 (q143 c4) ∷
   rw⁻ 0 (q89 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = eqn (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (CX21 ∷ Toff024 ∷ []) (Toff024 ∷ CX21 ∷ []) (wp0191 c4)
  q146 : Ws → Eqn
  q146 c4 = eqn (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (CX21 ∷ CCZ013 ∷ []) (wl1166 (lit c4))
  q147 : Ws → Eqn
  q147 c4 = eqn (CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ023 ∷ CCZ234 ∷ []) (wp0967 c4)
  q148 : Ws → Eqn
  q148 c4 = eqn (CCZ234 ∷ []) (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4))
  q149 : Ws → Eqn
  q149 c4 = eqn (CCZ013 ∷ CS34 ∷ []) (CS34 ∷ CCZ013 ∷ []) (wp0185 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (CX42 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ013 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ013 ∷ []) (wl1167 (lit c4))
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) (wl0324 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (CX21 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX21 ∷ []) (wl1168 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ234 ∷ []) (CX21 ∷ CCZ234 ∷ CX21 ∷ []) (wl0676 (lit c4))

-- CXbc-box @143143: 17 steps
lem-CXbc-box-at143143 : Ws → ⟪ (CX21 ∷ Bx0-4213 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at143143 c4 = derive (CX21 ∷ Bx0-4213 ∷ CX21 ∷ []) (Bx0-4213 ∷ CCZ234 ∷ [])
  (rw 1 (q144 c4) ∷
   rw 0 (q145 c4) ∷
   rw⁻ 1 (q146 c4) ∷
   rw 3 (q147 c4) ∷
   rw 2 (q145 c4) ∷
   rw 5 (q148 c4) ∷
   rw⁻ 9 (q149 c4) ∷
   rw 8 (q150 c4) ∷
   rw⁻ 7 (q151 c4) ∷
   rw 6 (q150 c4) ∷
   rw⁻ 5 (q152 c4) ∷
   rw⁻ 6 (q148 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 3 (q146 c4) ∷
   rw 4 (q153 c4) ∷
   rw⁻ 0 (q144 c4) ∷
   rw⁻ 1 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = eqn (CX12 ∷ Toff024 ∷ []) (Toff024 ∷ CX12 ∷ Toff014 ∷ []) (wp0968 c4)
  q156 : Ws → Eqn
  q156 c4 = eqn (CCZ013 ∷ Toff014 ∷ CCZ134 ∷ []) (Toff014 ∷ CCZ013 ∷ []) (wp0969 c4)
  q157 : Ws → Eqn
  q157 c4 = eqn (CCZ013 ∷ CX12 ∷ []) (CX12 ∷ CCZ013 ∷ []) (wl0448 (lit c4))
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4))
  q159 : Ws → Eqn
  q159 c4 = eqn (CS34 ∷ Toff024 ∷ []) (Toff024 ∷ CS34 ∷ []) (wp0970 c4)
  q160 : Ws → Eqn
  q160 c4 = eqn (CX41 ∷ Toff024 ∷ []) (Toff024 ∷ CX41 ∷ []) (wp0181 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (CS13⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4))
  q162 : Ws → Eqn
  q162 c4 = eqn (CS13 ∷ Toff024 ∷ []) (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (Toff014 ∷ Toff024 ∷ []) (Toff024 ∷ Toff014 ∷ []) (wp0548 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (CX12 ∷ Toff014 ∷ Toff014 ∷ []) (CX12 ∷ []) (wp0971 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (CCZ013 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (CCZ134 ∷ []) (CX12 ∷ CCZ134 ∷ CX12 ∷ []) (wl0673 (lit c4))

-- CXcb-box @143143: 18 steps
lem-CXcb-box-at143143 : Ws → ⟪ (CX12 ∷ Bx0-4213 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at143143 c4 = derive (CX12 ∷ Bx0-4213 ∷ CX12 ∷ []) (Bx0-4213 ∷ CCZ134 ∷ [])
  (rw 1 (q144 c4) ∷
   rw 0 (q155 c4) ∷
   rw⁻ 2 (q156 c4) ∷
   rw⁻ 1 (q157 c4) ∷
   rw 4 (q158 c4) ∷
   rw 8 (q159 c4) ∷
   rw 7 (q160 c4) ∷
   rw 6 (q161 c4) ∷
   rw 5 (q160 c4) ∷
   rw 4 (q162 c4) ∷
   rw⁻ 5 (q158 c4) ∷
   rw 3 (q163 c4) ∷
   rw 2 (q155 c4) ∷
   rw 3 (q164 c4) ∷
   rw⁻ 4 (q165 c4) ∷
   rw⁻ 3 (q157 c4) ∷
   rw⁻ 0 (q144 c4) ∷
   rw⁻ 1 (q166 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = eqn (Bx0-2143 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4)
  q168 : Ws → Eqn
  q168 c4 = eqn (CX14 ∷ Toff012 ∷ []) (Toff012 ∷ CX14 ∷ []) (wp0974 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (CX14 ∷ CCZ034 ∷ []) (wp0735 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (CCZ013 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1170 (lit c4))
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4))
  q172 : Ws → Eqn
  q172 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp0314 c4)
  q173 : Ws → Eqn
  q173 c4 = eqn (CX21 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4))
  q174 : Ws → Eqn
  q174 c4 = eqn (CCZ034 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) (wp0312 c4)
  q176 : Ws → Eqn
  q176 c4 = eqn (CCZ013 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (CX14 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX14 ∷ []) (wp0736 c4)
  q178 : Ws → Eqn
  q178 c4 = eqn (CCZ123 ∷ []) (CX14 ∷ CCZ123 ∷ CX14 ∷ []) (wl0299 (lit c4))

-- CXbc-box @12213443: 17 steps
lem-CXbc-box-at12213443 : Ws → ⟪ (CX14 ∷ Bx0-2143 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at12213443 c4 = derive (CX14 ∷ Bx0-2143 ∷ CX14 ∷ []) (Bx0-2143 ∷ CCZ123 ∷ [])
  (rw 1 (q167 c4) ∷
   rw 0 (q168 c4) ∷
   rw⁻ 1 (q169 c4) ∷
   rw 3 (q170 c4) ∷
   rw 2 (q168 c4) ∷
   rw 5 (q171 c4) ∷
   rw⁻ 9 (q172 c4) ∷
   rw 8 (q173 c4) ∷
   rw⁻ 7 (q174 c4) ∷
   rw 6 (q173 c4) ∷
   rw⁻ 5 (q175 c4) ∷
   rw⁻ 6 (q171 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 3 (q169 c4) ∷
   rw 4 (q177 c4) ∷
   rw⁻ 0 (q167 c4) ∷
   rw⁻ 1 (q178 c4) ∷ []) Eq.refl

private
  q179 : Ws → Eqn
  q179 c4 = eqn (CX41 ∷ Toff012 ∷ []) (Toff012 ∷ CX41 ∷ Toff024 ∷ []) (wp0975 c4)
  q180 : Ws → Eqn
  q180 c4 = eqn (CCZ034 ∷ Toff024 ∷ CCZ234 ∷ []) (Toff024 ∷ CCZ034 ∷ []) (wp0976 c4)
  q181 : Ws → Eqn
  q181 c4 = eqn (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ []) (wp0357 c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4))
  q183 : Ws → Eqn
  q183 c4 = eqn (CS23 ∷ Toff012 ∷ []) (Toff012 ∷ CS23 ∷ []) (wl1171 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CX24 ∷ Toff012 ∷ []) (Toff012 ∷ CX24 ∷ []) (wp0977 c4)
  q185 : Ws → Eqn
  q185 c4 = eqn (Toff012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ Toff012 ∷ []) (c₃ (Toff) (CS • CS • CS))
  q186 : Ws → Eqn
  q186 c4 = eqn (Toff012 ∷ CS34 ∷ []) (CS34 ∷ Toff012 ∷ []) (c₃ (Toff) (CS))
  q187 : Ws → Eqn
  q187 c4 = eqn (Toff012 ∷ Toff024 ∷ []) (Toff024 ∷ Toff012 ∷ []) (wp0192 c4)
  q188 : Ws → Eqn
  q188 c4 = eqn (CX41 ∷ Toff024 ∷ Toff024 ∷ []) (CX41 ∷ []) (wp0978 c4)
  q189 : Ws → Eqn
  q189 c4 = eqn (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4)
  q190 : Ws → Eqn
  q190 c4 = eqn (CCZ234 ∷ []) (CX41 ∷ CCZ234 ∷ CX41 ∷ []) (wl0295 (lit c4))

-- CXcb-box @12213443: 18 steps
lem-CXcb-box-at12213443 : Ws → ⟪ (CX41 ∷ Bx0-2143 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at12213443 c4 = derive (CX41 ∷ Bx0-2143 ∷ CX41 ∷ []) (Bx0-2143 ∷ CCZ234 ∷ [])
  (rw 1 (q167 c4) ∷
   rw 0 (q179 c4) ∷
   rw⁻ 2 (q180 c4) ∷
   rw⁻ 1 (q181 c4) ∷
   rw 4 (q182 c4) ∷
   rw 8 (q183 c4) ∷
   rw 7 (q184 c4) ∷
   rw⁻ 6 (q185 c4) ∷
   rw 5 (q184 c4) ∷
   rw⁻ 4 (q186 c4) ∷
   rw⁻ 5 (q182 c4) ∷
   rw⁻ 3 (q187 c4) ∷
   rw 2 (q179 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 4 (q189 c4) ∷
   rw⁻ 3 (q181 c4) ∷
   rw⁻ 0 (q167 c4) ∷
   rw⁻ 1 (q190 c4) ∷ []) Eq.refl

private
  q191 : Ws → Eqn
  q191 c4 = eqn (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ []) (lem-tP-at12243143 c4)

-- VPQ @12243143: 14 steps
lem-VPQ-at12243143 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at12243143 c4 = derive (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  (rw⁻ 0 (q36 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw 3 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 0 (q41 c4) ∷
   rw 4 (q42 c4) ∷
   rw 3 (q191 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 1 (q43 c4) ∷
   rw 2 (q44 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw 0 (q37 c4) ∷
   rw 2 (q36 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = eqn (Toff012 ∷ Toff034 ∷ []) (Toff034 ∷ Toff012 ∷ []) (lem-tP-at12213443 c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ034 ∷ []) (wp0112 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (CCZ034 ∷ CZ34 ∷ []) (Toff034 ∷ CCZ034 ∷ Toff034 ∷ []) (wp0113 c4)
  q195 : Ws → Eqn
  q195 c4 = eqn (Toff012 ∷ CZ34 ∷ []) (CZ34 ∷ Toff012 ∷ []) (c₃ (Toff) (CZ))
  q196 : Ws → Eqn
  q196 c4 = eqn (CCZ034 ∷ []) (CZ34 ∷ CCZ034 ∷ CZ34 ∷ []) (wp0114 c4)

-- P-box @12213443: 8 steps
lem-P-box-at12213443 : Ws → ⟪ (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-P-box-at12213443 c4 = derive (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) (Bx0-2143 ∷ [])
  (rw 1 (q167 c4) ∷
   rw⁻ 0 (q192 c4) ∷
   rw⁻ 1 (q193 c4) ∷
   rw⁻ 3 (q192 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw⁻ 2 (q195 c4) ∷
   rw⁻ 3 (q196 c4) ∷
   rw⁻ 0 (q167 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = eqn (CX32 ∷ CX23 ∷ CX32 ∷ []) (Sw23 ∷ []) (wl1020 (lit c4))
  q198 : Ws → Eqn
  q198 c4 = eqn (CX32 ∷ Bx0-4321 ∷ CX32 ∷ []) (Bx0-4321 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14233241 c4)
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ134 ∷ CX23 ∷ []) (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4))
  q200 : Ws → Eqn
  q200 c4 = eqn (CX23 ∷ Bx0-4321 ∷ CX23 ∷ []) (Bx0-4321 ∷ CCZ124 ∷ []) (lem-CXcb-box-at14233241 c4)
  q201 : Ws → Eqn
  q201 c4 = eqn (CCZ134 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ []) (wl1021 (lit c4))
  q202 : Ws → Eqn
  q202 c4 = eqn (CCZ124 ∷ CX32 ∷ []) (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4))
  q203 : Ws → Eqn
  q203 c4 = eqn (CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ []) (wl1022 (lit c4))
  q204 : Ws → Eqn
  q204 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl0321 (lit c4))

-- SWbc-box @14233241: 11 steps
lem-SWbc-box-at14233241 : Ws → ⟪ (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-SWbc-box-at14233241 c4 = derive (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (Bx0-4321 ∷ [])
  (rw⁻ 0 (q197 c4) ∷
   rw⁻ 4 (q197 c4) ∷
   rw 2 (q198 c4) ∷
   rw 3 (q199 c4) ∷
   rw 1 (q200 c4) ∷
   rw 4 (q201 c4) ∷
   rw 3 (q202 c4) ∷
   rw 2 (q202 c4) ∷
   rw 3 (q203 c4) ∷
   rw 0 (q198 c4) ∷
   rw 1 (q204 c4) ∷ []) Eq.refl

private
  q205 : Ws → Eqn
  q205 c4 = eqn (Bx3-4210 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4)
  q206 : Ws → Eqn
  q206 c4 = eqn (CX21 ∷ Toff324 ∷ []) (Toff324 ∷ CX21 ∷ []) (wl0851 (lit c4))
  q207 : Ws → Eqn
  q207 c4 = eqn (CCZ023 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp0989 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (CCZ024 ∷ []) (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (CCZ013 ∷ CS04 ∷ []) (CS04 ∷ CCZ013 ∷ []) (wp0077 c4)
  q210 : Ws → Eqn
  q210 c4 = eqn (CCZ013 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ013 ∷ []) (wl0342 (lit c4))
  q211 : Ws → Eqn
  q211 c4 = eqn (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ []) (wl0225 (lit c4))
  q212 : Ws → Eqn
  q212 c4 = eqn (CCZ024 ∷ []) (CX21 ∷ CCZ024 ∷ CX21 ∷ []) (wp0898 c4)

-- CXbc-box @03143140: 17 steps
lem-CXbc-box-at03143140 : Ws → ⟪ (CX21 ∷ Bx3-4210 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at03143140 c4 = derive (CX21 ∷ Bx3-4210 ∷ CX21 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ [])
  (rw 1 (q205 c4) ∷
   rw 0 (q206 c4) ∷
   rw⁻ 1 (q146 c4) ∷
   rw 3 (q207 c4) ∷
   rw 2 (q206 c4) ∷
   rw 5 (q208 c4) ∷
   rw⁻ 9 (q209 c4) ∷
   rw 8 (q150 c4) ∷
   rw⁻ 7 (q210 c4) ∷
   rw 6 (q150 c4) ∷
   rw⁻ 5 (q211 c4) ∷
   rw⁻ 6 (q208 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw⁻ 3 (q146 c4) ∷
   rw 4 (q153 c4) ∷
   rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q212 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = eqn (CX12 ∷ Toff324 ∷ []) (Toff324 ∷ CX12 ∷ Toff314 ∷ []) (wl1179 (lit c4))
  q214 : Ws → Eqn
  q214 c4 = eqn (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ013 ∷ []) (wp0990 c4)
  q215 : Ws → Eqn
  q215 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4)
  q216 : Ws → Eqn
  q216 c4 = eqn (CS04 ∷ Toff324 ∷ []) (Toff324 ∷ CS04 ∷ []) (wp0393 c4)
  q217 : Ws → Eqn
  q217 c4 = eqn (CX41 ∷ Toff324 ∷ []) (Toff324 ∷ CX41 ∷ []) (wl0848 (lit c4))
  q218 : Ws → Eqn
  q218 c4 = eqn (CS01⁻ ∷ Toff324 ∷ []) (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))
  q219 : Ws → Eqn
  q219 c4 = eqn (CS01 ∷ Toff324 ∷ []) (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI))
  q220 : Ws → Eqn
  q220 c4 = eqn (Toff314 ∷ Toff324 ∷ []) (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4))
  q221 : Ws → Eqn
  q221 c4 = eqn (CX12 ∷ Toff314 ∷ Toff314 ∷ []) (CX12 ∷ []) (wl1181 (lit c4))
  q222 : Ws → Eqn
  q222 c4 = eqn (CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ013 ∷ []) (wp0394 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (CCZ014 ∷ []) (CX12 ∷ CCZ014 ∷ CX12 ∷ []) (wp0655 c4)

-- CXcb-box @03143140: 18 steps
lem-CXcb-box-at03143140 : Ws → ⟪ (CX12 ∷ Bx3-4210 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03143140 c4 = derive (CX12 ∷ Bx3-4210 ∷ CX12 ∷ []) (Bx3-4210 ∷ CCZ014 ∷ [])
  (rw 1 (q205 c4) ∷
   rw 0 (q213 c4) ∷
   rw⁻ 2 (q214 c4) ∷
   rw⁻ 1 (q157 c4) ∷
   rw 4 (q215 c4) ∷
   rw 8 (q216 c4) ∷
   rw 7 (q217 c4) ∷
   rw 6 (q218 c4) ∷
   rw 5 (q217 c4) ∷
   rw 4 (q219 c4) ∷
   rw⁻ 5 (q215 c4) ∷
   rw 3 (q220 c4) ∷
   rw 2 (q213 c4) ∷
   rw 3 (q221 c4) ∷
   rw⁻ 4 (q222 c4) ∷
   rw⁻ 3 (q157 c4) ∷
   rw⁻ 0 (q205 c4) ∷
   rw⁻ 1 (q223 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4))
  q225 : Ws → Eqn
  q225 c4 = eqn (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4))
  q226 : Ws → Eqn
  q226 c4 = eqn (CS02⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))
  q227 : Ws → Eqn
  q227 c4 = eqn (Toff314 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4))
  q228 : Ws → Eqn
  q228 c4 = eqn (CS02⁻ ∷ S3 ∷ []) (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))
  q229 : Ws → Eqn
  q229 c4 = eqn (CS02⁻ ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4)
  q230 : Ws → Eqn
  q230 c4 = eqn (S3⁻ ∷ S3 ∷ []) [] (wl0441 (lit c4))
  q231 : Ws → Eqn
  q231 c4 = eqn (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213240 c4)
  q232 : Ws → Eqn
  q232 c4 = eqn (CS14⁻ ∷ S3 ∷ []) (S3 ∷ CS14⁻ ∷ []) (wl0785 (lit c4))
  q233 : Ws → Eqn
  q233 c4 = eqn (CS14⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4))
  q234 : Ws → Eqn
  q234 c4 = eqn (CS14⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS14⁻ ∷ []) (wl0786 (lit c4))

-- VPQ @0314213240: 14 steps
lem-VPQ-at0314213240 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at0314213240 c4 = derive (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q224 c4) ∷
   rw⁻ 4 (q225 c4) ∷
   rw⁻ 3 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw⁻ 1 (q228 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q231 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q233 c4) ∷
   rw 3 (q234 c4) ∷
   rw 0 (q225 c4) ∷
   rw 2 (q224 c4) ∷ []) Eq.refl

private
  q235 : Ws → Eqn
  q235 c4 = eqn (Bx3-4120 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213240 c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (CX12 ∷ Toff314 ∷ []) (Toff314 ∷ CX12 ∷ []) (wl1183 (lit c4))
  q237 : Ws → Eqn
  q237 c4 = eqn (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (CX12 ∷ CCZ023 ∷ []) (wl0668 (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ013 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0997 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (CCZ023 ∷ CS04 ∷ []) (CS04 ∷ CCZ023 ∷ []) (wp0048 c4)
  q240 : Ws → Eqn
  q240 c4 = eqn (CX41 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (CCZ023 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ023 ∷ []) (wl0667 (lit c4))
  q242 : Ws → Eqn
  q242 c4 = eqn (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ []) (wl0199 (lit c4))
  q243 : Ws → Eqn
  q243 c4 = eqn (CX12 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX12 ∷ []) (wl0672 (lit c4))

-- CXbc-box @0314213240: 17 steps
lem-CXbc-box-at0314213240 : Ws → ⟪ (CX12 ∷ Bx3-4120 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0314213240 c4 = derive (CX12 ∷ Bx3-4120 ∷ CX12 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ [])
  (rw 1 (q235 c4) ∷
   rw 0 (q236 c4) ∷
   rw⁻ 1 (q237 c4) ∷
   rw 3 (q238 c4) ∷
   rw 2 (q236 c4) ∷
   rw 5 (q215 c4) ∷
   rw⁻ 9 (q239 c4) ∷
   rw 8 (q240 c4) ∷
   rw⁻ 7 (q241 c4) ∷
   rw 6 (q240 c4) ∷
   rw⁻ 5 (q242 c4) ∷
   rw⁻ 6 (q215 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q237 c4) ∷
   rw 4 (q243 c4) ∷
   rw⁻ 0 (q235 c4) ∷
   rw⁻ 1 (q223 c4) ∷ []) Eq.refl

private
  q244 : Ws → Eqn
  q244 c4 = eqn (CX21 ∷ Toff314 ∷ []) (Toff314 ∷ CX21 ∷ Toff324 ∷ []) (wl1184 (lit c4))
  q245 : Ws → Eqn
  q245 c4 = eqn (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4)
  q246 : Ws → Eqn
  q246 c4 = eqn (CCZ023 ∷ CX21 ∷ []) (CX21 ∷ CCZ023 ∷ []) (wl0674 (lit c4))
  q247 : Ws → Eqn
  q247 c4 = eqn (CS04 ∷ Toff314 ∷ []) (Toff314 ∷ CS04 ∷ []) (wp0998 c4)
  q248 : Ws → Eqn
  q248 c4 = eqn (CX42 ∷ Toff314 ∷ []) (Toff314 ∷ CX42 ∷ []) (wl1185 (lit c4))
  q249 : Ws → Eqn
  q249 c4 = eqn (CS02⁻ ∷ Toff314 ∷ []) (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4))
  q250 : Ws → Eqn
  q250 c4 = eqn (CS02 ∷ Toff314 ∷ []) (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4))
  q251 : Ws → Eqn
  q251 c4 = eqn (CX21 ∷ Toff324 ∷ Toff324 ∷ []) (CX21 ∷ []) (wl1186 (lit c4))

-- CXcb-box @0314213240: 18 steps
lem-CXcb-box-at0314213240 : Ws → ⟪ (CX21 ∷ Bx3-4120 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0314213240 c4 = derive (CX21 ∷ Bx3-4120 ∷ CX21 ∷ []) (Bx3-4120 ∷ CCZ024 ∷ [])
  (rw 1 (q235 c4) ∷
   rw 0 (q244 c4) ∷
   rw⁻ 2 (q245 c4) ∷
   rw⁻ 1 (q246 c4) ∷
   rw 4 (q208 c4) ∷
   rw 8 (q247 c4) ∷
   rw 7 (q248 c4) ∷
   rw 6 (q249 c4) ∷
   rw 5 (q248 c4) ∷
   rw 4 (q250 c4) ∷
   rw⁻ 5 (q208 c4) ∷
   rw⁻ 3 (q220 c4) ∷
   rw 2 (q244 c4) ∷
   rw 3 (q251 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q246 c4) ∷
   rw⁻ 0 (q235 c4) ∷
   rw⁻ 1 (q212 c4) ∷ []) Eq.refl

private
  q252 : Ws → Eqn
  q252 c4 = eqn (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4))
  q253 : Ws → Eqn
  q253 c4 = eqn (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4))
  q254 : Ws → Eqn
  q254 c4 = eqn (CS01⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑))
  q255 : Ws → Eqn
  q255 c4 = eqn (CS01⁻ ∷ S3 ∷ []) (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑))
  q256 : Ws → Eqn
  q256 c4 = eqn (CS01⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))
  q257 : Ws → Eqn
  q257 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143140 c4)
  q258 : Ws → Eqn
  q258 c4 = eqn (CS24⁻ ∷ S3 ∷ []) (S3 ∷ CS24⁻ ∷ []) (wl0440 (lit c4))
  q259 : Ws → Eqn
  q259 c4 = eqn (CS24⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4))
  q260 : Ws → Eqn
  q260 c4 = eqn (CS24⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS24⁻ ∷ []) (wl0439 (lit c4))

-- VPQ @03143140: 14 steps
lem-VPQ-at03143140 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at03143140 c4 = derive (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q252 c4) ∷
   rw⁻ 4 (q253 c4) ∷
   rw⁻ 3 (q254 c4) ∷
   rw⁻ 2 (q218 c4) ∷
   rw⁻ 1 (q255 c4) ∷
   rw⁻ 0 (q256 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q257 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q258 c4) ∷
   rw 2 (q259 c4) ∷
   rw 3 (q260 c4) ∷
   rw 0 (q253 c4) ∷
   rw 2 (q252 c4) ∷ []) Eq.refl

private
  q261 : Ws → Eqn
  q261 c4 = eqn (CCZ234 ∷ Toff324 ∷ CZ24 ∷ []) (Toff324 ∷ CCZ234 ∷ []) (wl1203 (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (CZ24 ∷ Toff301 ∷ []) (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4))
  q263 : Ws → Eqn
  q263 c4 = eqn (CCZ234 ∷ Toff324 ∷ []) (Toff324 ∷ CZ24 ∷ CCZ234 ∷ []) (wl1204 (lit c4))

-- t-cP @03143140: 5 steps
lem-t-cP-at03143140 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-t-cP-at03143140 c4 = derive (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff324 ∷ [])
  (rw⁻ 0 (q261 c4) ∷
   rw 2 (q262 c4) ∷
   rw 1 (q257 c4) ∷
   rw⁻ 2 (q263 c4) ∷
   rw 3 (q257 c4) ∷ []) Eq.refl

private
  q264 : Ws → Eqn
  q264 c4 = eqn (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243240 c4)

-- VPQ @03243240: 14 steps
lem-VPQ-at03243240 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at03243240 c4 = derive (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  (rw⁻ 0 (q224 c4) ∷
   rw⁻ 4 (q225 c4) ∷
   rw⁻ 3 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw⁻ 1 (q228 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q264 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q232 c4) ∷
   rw 2 (q233 c4) ∷
   rw 3 (q234 c4) ∷
   rw 0 (q225 c4) ∷
   rw 2 (q224 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = eqn (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4)
  q266 : Ws → Eqn
  q266 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203142 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ []) (wl0504 (lit c4))
  q268 : Ws → Eqn
  q268 c4 = eqn (CCZ123 ∷ CZ12 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff312 ∷ []) (wl0505 (lit c4))
  q269 : Ws → Eqn
  q269 c4 = eqn (CZ12 ∷ Toff304 ∷ []) (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4))
  q270 : Ws → Eqn
  q270 c4 = eqn (CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ CZ12 ∷ []) (wl0506 (lit c4))

-- P-box @0314203142: 8 steps
lem-P-box-at0314203142 : Ws → ⟪ (Toff312 ∷ Bx3-4012 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-P-box-at0314203142 c4 = derive (Toff312 ∷ Bx3-4012 ∷ Toff312 ∷ []) (Bx3-4012 ∷ [])
  (rw 1 (q265 c4) ∷
   rw⁻ 0 (q266 c4) ∷
   rw⁻ 1 (q267 c4) ∷
   rw⁻ 3 (q266 c4) ∷
   rw⁻ 4 (q268 c4) ∷
   rw 2 (q269 c4) ∷
   rw⁻ 3 (q270 c4) ∷
   rw⁻ 0 (q265 c4) ∷ []) Eq.refl

private
  q271 : Ws → Eqn
  q271 c4 = eqn (Bx3-1240 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4)
  q272 : Ws → Eqn
  q272 c4 = eqn (CX24 ∷ Toff312 ∷ []) (Toff312 ∷ CX24 ∷ []) (wl0862 (lit c4))
  q273 : Ws → Eqn
  q273 c4 = eqn (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (CX24 ∷ CCZ034 ∷ []) (wp1017 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (CCZ023 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1213 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4))
  q276 : Ws → Eqn
  q276 c4 = eqn (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) (wp0001 c4)
  q277 : Ws → Eqn
  q277 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q278 : Ws → Eqn
  q278 c4 = eqn (CCZ034 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4)
  q279 : Ws → Eqn
  q279 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp0003 c4)
  q280 : Ws → Eqn
  q280 c4 = eqn (CCZ023 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4)
  q281 : Ws → Eqn
  q281 c4 = eqn (CX24 ∷ CCZ023 ∷ CCZ023 ∷ []) (CX24 ∷ []) (wp1018 c4)
  q282 : Ws → Eqn
  q282 c4 = eqn (CCZ012 ∷ []) (CX24 ∷ CCZ012 ∷ CX24 ∷ []) (wp1019 c4)

-- CXbc-box @033440: 17 steps
lem-CXbc-box-at033440 : Ws → ⟪ (CX24 ∷ Bx3-1240 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at033440 c4 = derive (CX24 ∷ Bx3-1240 ∷ CX24 ∷ []) (Bx3-1240 ∷ CCZ012 ∷ [])
  (rw 1 (q271 c4) ∷
   rw 0 (q272 c4) ∷
   rw⁻ 1 (q273 c4) ∷
   rw 3 (q274 c4) ∷
   rw 2 (q272 c4) ∷
   rw 5 (q275 c4) ∷
   rw⁻ 9 (q276 c4) ∷
   rw 8 (q277 c4) ∷
   rw⁻ 7 (q278 c4) ∷
   rw 6 (q277 c4) ∷
   rw⁻ 5 (q279 c4) ∷
   rw⁻ 6 (q275 c4) ∷
   rw 4 (q280 c4) ∷
   rw⁻ 3 (q273 c4) ∷
   rw 4 (q281 c4) ∷
   rw⁻ 0 (q271 c4) ∷
   rw⁻ 1 (q282 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = eqn (CX42 ∷ Toff312 ∷ []) (Toff312 ∷ CX42 ∷ Toff314 ∷ []) (wl1214 (lit c4))
  q284 : Ws → Eqn
  q284 c4 = eqn (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ034 ∷ []) (wp0702 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (CCZ034 ∷ CX42 ∷ []) (CX42 ∷ CCZ034 ∷ []) (wp1020 c4)
  q286 : Ws → Eqn
  q286 c4 = eqn (CCZ014 ∷ []) (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4)
  q287 : Ws → Eqn
  q287 c4 = eqn (CS01 ∷ Toff312 ∷ []) (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4))
  q288 : Ws → Eqn
  q288 c4 = eqn (CX14 ∷ Toff312 ∷ []) (Toff312 ∷ CX14 ∷ []) (wl0858 (lit c4))
  q289 : Ws → Eqn
  q289 c4 = eqn (CS04⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4))
  q290 : Ws → Eqn
  q290 c4 = eqn (CS04 ∷ Toff312 ∷ []) (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4))
  q291 : Ws → Eqn
  q291 c4 = eqn (Toff312 ∷ Toff314 ∷ []) (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4))
  q292 : Ws → Eqn
  q292 c4 = eqn (CX42 ∷ Toff314 ∷ Toff314 ∷ []) (CX42 ∷ []) (wl1215 (lit c4))
  q293 : Ws → Eqn
  q293 c4 = eqn (CCZ014 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4)
  q294 : Ws → Eqn
  q294 c4 = eqn (CCZ014 ∷ []) (CX42 ∷ CCZ014 ∷ CX42 ∷ []) (wp1021 c4)

-- CXcb-box @033440: 18 steps
lem-CXcb-box-at033440 : Ws → ⟪ (CX42 ∷ Bx3-1240 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at033440 c4 = derive (CX42 ∷ Bx3-1240 ∷ CX42 ∷ []) (Bx3-1240 ∷ CCZ014 ∷ [])
  (rw 1 (q271 c4) ∷
   rw 0 (q283 c4) ∷
   rw⁻ 2 (q284 c4) ∷
   rw⁻ 1 (q285 c4) ∷
   rw 4 (q286 c4) ∷
   rw 8 (q287 c4) ∷
   rw 7 (q288 c4) ∷
   rw 6 (q289 c4) ∷
   rw 5 (q288 c4) ∷
   rw 4 (q290 c4) ∷
   rw⁻ 5 (q286 c4) ∷
   rw⁻ 3 (q291 c4) ∷
   rw 2 (q283 c4) ∷
   rw 3 (q292 c4) ∷
   rw 4 (q293 c4) ∷
   rw⁻ 3 (q285 c4) ∷
   rw⁻ 0 (q271 c4) ∷
   rw⁻ 1 (q294 c4) ∷ []) Eq.refl

private
  q295 : Ws → Eqn
  q295 c4 = eqn (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) (Toff314 ∷ CCZ134 ∷ []) (wl0803 (lit c4))
  q296 : Ws → Eqn
  q296 c4 = eqn (CZ14 ∷ Toff302 ∷ []) (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4))
  q297 : Ws → Eqn
  q297 c4 = eqn (CCZ134 ∷ Toff314 ∷ []) (Toff314 ∷ CZ14 ∷ CCZ134 ∷ []) (wl0804 (lit c4))

-- t-cP @03243240: 5 steps
lem-t-cP-at03243240 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-t-cP-at03243240 c4 = derive (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ [])
  (rw⁻ 0 (q295 c4) ∷
   rw 2 (q296 c4) ∷
   rw 1 (q264 c4) ∷
   rw⁻ 2 (q297 c4) ∷
   rw 3 (q264 c4) ∷ []) Eq.refl

private
  q298 : Ws → Eqn
  q298 c4 = eqn (Bx3-1420 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4)
  q299 : Ws → Eqn
  q299 c4 = eqn (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (CX42 ∷ CCZ023 ∷ []) (wp0572 c4)
  q300 : Ws → Eqn
  q300 c4 = eqn (CCZ034 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1031 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (CCZ023 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ CCZ023 ∷ []) (wp0047 c4)
  q302 : Ws → Eqn
  q302 c4 = eqn (CX42 ∷ CCZ034 ∷ CCZ034 ∷ []) (CX42 ∷ []) (wp0576 c4)

-- CXbc-box @03243240: 17 steps
lem-CXbc-box-at03243240 : Ws → ⟪ (CX42 ∷ Bx3-1420 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at03243240 c4 = derive (CX42 ∷ Bx3-1420 ∷ CX42 ∷ []) (Bx3-1420 ∷ CCZ014 ∷ [])
  (rw 1 (q298 c4) ∷
   rw 0 (q248 c4) ∷
   rw⁻ 1 (q299 c4) ∷
   rw 3 (q300 c4) ∷
   rw 2 (q248 c4) ∷
   rw 5 (q286 c4) ∷
   rw⁻ 9 (q242 c4) ∷
   rw 8 (q127 c4) ∷
   rw⁻ 7 (q301 c4) ∷
   rw 6 (q127 c4) ∷
   rw⁻ 5 (q239 c4) ∷
   rw⁻ 6 (q286 c4) ∷
   rw⁻ 4 (q280 c4) ∷
   rw⁻ 3 (q299 c4) ∷
   rw 4 (q302 c4) ∷
   rw⁻ 0 (q298 c4) ∷
   rw⁻ 1 (q294 c4) ∷ []) Eq.refl

private
  q303 : Ws → Eqn
  q303 c4 = eqn (CX24 ∷ Toff314 ∷ []) (Toff314 ∷ CX24 ∷ Toff312 ∷ []) (wl1228 (lit c4))
  q304 : Ws → Eqn
  q304 c4 = eqn (CCZ023 ∷ Toff312 ∷ CCZ012 ∷ []) (Toff312 ∷ CCZ023 ∷ []) (wl1229 (lit c4))
  q305 : Ws → Eqn
  q305 c4 = eqn (CCZ023 ∷ CX24 ∷ []) (CX24 ∷ CCZ023 ∷ []) (wp0578 c4)
  q306 : Ws → Eqn
  q306 c4 = eqn (CS01 ∷ Toff314 ∷ []) (Toff314 ∷ CS01 ∷ []) (wp0029 c4)
  q307 : Ws → Eqn
  q307 c4 = eqn (CX24 ∷ Toff312 ∷ Toff312 ∷ []) (CX24 ∷ []) (wl1230 (lit c4))
  q308 : Ws → Eqn
  q308 c4 = eqn (CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4))

-- CXcb-box @03243240: 18 steps
lem-CXcb-box-at03243240 : Ws → ⟪ (CX24 ∷ Bx3-1420 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at03243240 c4 = derive (CX24 ∷ Bx3-1420 ∷ CX24 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  (rw 1 (q298 c4) ∷
   rw 0 (q303 c4) ∷
   rw⁻ 2 (q304 c4) ∷
   rw⁻ 1 (q305 c4) ∷
   rw 4 (q275 c4) ∷
   rw 8 (q306 c4) ∷
   rw 7 (q236 c4) ∷
   rw 6 (q249 c4) ∷
   rw 5 (q236 c4) ∷
   rw 4 (q250 c4) ∷
   rw⁻ 5 (q275 c4) ∷
   rw 3 (q291 c4) ∷
   rw 2 (q303 c4) ∷
   rw 3 (q307 c4) ∷
   rw 4 (q308 c4) ∷
   rw⁻ 3 (q305 c4) ∷
   rw⁻ 0 (q298 c4) ∷
   rw⁻ 1 (q282 c4) ∷ []) Eq.refl

private
  q309 : Ws → Eqn
  q309 c4 = eqn (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4))
  q310 : Ws → Eqn
  q310 c4 = eqn (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4)
  q311 : Ws → Eqn
  q311 c4 = eqn (CS04⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS04⁻ ∷ []) (wp0348 c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (Toff312 ∷ CS04⁻ ∷ []) (CS04⁻ ∷ Toff312 ∷ []) (lem-comm-TOFF312-CSd04 (lit c4))
  q313 : Ws → Eqn
  q313 c4 = eqn (CS04⁻ ∷ S3 ∷ []) (S3 ∷ CS04⁻ ∷ []) (wp0349 c4)
  q314 : Ws → Eqn
  q314 c4 = eqn (CS04⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS04⁻ ∷ []) (wp0350 c4)
  q315 : Ws → Eqn
  q315 c4 = eqn (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (CS12⁻ ∷ S3 ∷ []) (S3 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S))
  q317 : Ws → Eqn
  q317 c4 = eqn (CS12⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4))
  q318 : Ws → Eqn
  q318 c4 = eqn (CS12⁻ ∷ S3⁻ ∷ []) (S3⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S • S • S))

-- VPQ @033440: 14 steps
lem-VPQ-at033440 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at033440 c4 = derive (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ [])
  (rw⁻ 0 (q309 c4) ∷
   rw⁻ 4 (q310 c4) ∷
   rw⁻ 3 (q311 c4) ∷
   rw 2 (q312 c4) ∷
   rw⁻ 1 (q313 c4) ∷
   rw⁻ 0 (q314 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q315 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q316 c4) ∷
   rw 2 (q317 c4) ∷
   rw 3 (q318 c4) ∷
   rw 0 (q310 c4) ∷
   rw 2 (q309 c4) ∷ []) Eq.refl

private
  q319 : Ws → Eqn
  q319 c4 = eqn (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ034 ∷ []) (wp0344 c4)
  q320 : Ws → Eqn
  q320 c4 = eqn (CCZ034 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ Toff304 ∷ []) (wp0345 c4)
  q321 : Ws → Eqn
  q321 c4 = eqn (CZ04 ∷ Toff312 ∷ []) (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4))
  q322 : Ws → Eqn
  q322 c4 = eqn (CCZ034 ∷ []) (CZ04 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0346 c4)

-- P-box @033440: 8 steps
lem-P-box-at033440 : Ws → ⟪ (Toff304 ∷ Bx3-1240 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-P-box-at033440 c4 = derive (Toff304 ∷ Bx3-1240 ∷ Toff304 ∷ []) (Bx3-1240 ∷ [])
  (rw 1 (q271 c4) ∷
   rw⁻ 0 (q315 c4) ∷
   rw⁻ 1 (q319 c4) ∷
   rw⁻ 3 (q315 c4) ∷
   rw⁻ 4 (q320 c4) ∷
   rw 2 (q321 c4) ∷
   rw⁻ 3 (q322 c4) ∷
   rw⁻ 0 (q271 c4) ∷ []) Eq.refl

private
  q323 : Ws → Eqn
  q323 c4 = eqn (CCZ034 ∷ Toff304 ∷ CZ04 ∷ []) (Toff304 ∷ CCZ034 ∷ []) (wp1033 c4)
  q324 : Ws → Eqn
  q324 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4)
  q325 : Ws → Eqn
  q325 c4 = eqn (CCZ034 ∷ Toff304 ∷ []) (Toff304 ∷ CZ04 ∷ CCZ034 ∷ []) (wp1034 c4)

-- t-cP @0310243142: 5 steps
lem-t-cP-at0310243142 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-t-cP-at0310243142 c4 = derive (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ [])
  (rw⁻ 0 (q323 c4) ∷
   rw 2 (q321 c4) ∷
   rw 1 (q324 c4) ∷
   rw⁻ 2 (q325 c4) ∷
   rw 3 (q324 c4) ∷ []) Eq.refl

private
  q326 : Ws → Eqn
  q326 c4 = eqn (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4)
  q327 : Ws → Eqn
  q327 c4 = eqn (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213042 c4)
  q328 : Ws → Eqn
  q328 c4 = eqn (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ023 ∷ []) (wl1235 (lit c4))
  q329 : Ws → Eqn
  q329 c4 = eqn (CCZ023 ∷ CZ02 ∷ []) (Toff302 ∷ CCZ023 ∷ Toff302 ∷ []) (wl1236 (lit c4))
  q330 : Ws → Eqn
  q330 c4 = eqn (CZ02 ∷ Toff314 ∷ []) (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4))
  q331 : Ws → Eqn
  q331 c4 = eqn (CCZ023 ∷ []) (CZ02 ∷ CCZ023 ∷ CZ02 ∷ []) (wl0774 (lit c4))

-- P-box @0314213042: 8 steps
lem-P-box-at0314213042 : Ws → ⟪ (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-P-box-at0314213042 c4 = derive (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) (Bx3-4102 ∷ [])
  (rw 1 (q326 c4) ∷
   rw⁻ 0 (q327 c4) ∷
   rw⁻ 1 (q328 c4) ∷
   rw⁻ 3 (q327 c4) ∷
   rw⁻ 4 (q329 c4) ∷
   rw 2 (q330 c4) ∷
   rw⁻ 3 (q331 c4) ∷
   rw⁻ 0 (q326 c4) ∷ []) Eq.refl

private
  q332 : Ws → Eqn
  q332 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4)
  q333 : Ws → Eqn
  q333 c4 = eqn (CX24 ∷ Toff302 ∷ []) (Toff302 ∷ CX24 ∷ []) (wp1049 c4)
  q334 : Ws → Eqn
  q334 c4 = eqn (CCZ134 ∷ CX24 ∷ CCZ123 ∷ []) (CX24 ∷ CCZ134 ∷ []) (wl1240 (lit c4))
  q335 : Ws → Eqn
  q335 c4 = eqn (CCZ123 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1241 (lit c4))
  q336 : Ws → Eqn
  q336 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4))
  q337 : Ws → Eqn
  q337 c4 = eqn (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) (wp0261 c4)
  q338 : Ws → Eqn
  q338 c4 = eqn (CX02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4))
  q339 : Ws → Eqn
  q339 c4 = eqn (CCZ134 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4))
  q340 : Ws → Eqn
  q340 c4 = eqn (CCZ134 ∷ CS12 ∷ []) (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4))
  q341 : Ws → Eqn
  q341 c4 = eqn (CCZ123 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4))
  q342 : Ws → Eqn
  q342 c4 = eqn (CX24 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX24 ∷ []) (wl1242 (lit c4))

-- CXbc-box @03103441: 17 steps
lem-CXbc-box-at03103441 : Ws → ⟪ (CX24 ∷ Bx3-0241 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at03103441 c4 = derive (CX24 ∷ Bx3-0241 ∷ CX24 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ [])
  (rw 1 (q332 c4) ∷
   rw 0 (q333 c4) ∷
   rw⁻ 1 (q334 c4) ∷
   rw 3 (q335 c4) ∷
   rw 2 (q333 c4) ∷
   rw 5 (q336 c4) ∷
   rw⁻ 9 (q337 c4) ∷
   rw 8 (q338 c4) ∷
   rw⁻ 7 (q339 c4) ∷
   rw 6 (q338 c4) ∷
   rw⁻ 5 (q340 c4) ∷
   rw⁻ 6 (q336 c4) ∷
   rw 4 (q341 c4) ∷
   rw⁻ 3 (q334 c4) ∷
   rw 4 (q342 c4) ∷
   rw⁻ 0 (q332 c4) ∷
   rw⁻ 1 (q282 c4) ∷ []) Eq.refl

private
  q343 : Ws → Eqn
  q343 c4 = eqn (CX42 ∷ Toff302 ∷ []) (Toff302 ∷ CX42 ∷ Toff304 ∷ []) (wp1050 c4)
  q344 : Ws → Eqn
  q344 c4 = eqn (CCZ134 ∷ Toff304 ∷ CCZ014 ∷ []) (Toff304 ∷ CCZ134 ∷ []) (wp1051 c4)
  q345 : Ws → Eqn
  q345 c4 = eqn (CCZ134 ∷ CX42 ∷ []) (CX42 ∷ CCZ134 ∷ []) (wl0318 (lit c4))
  q346 : Ws → Eqn
  q346 c4 = eqn (CS01 ∷ Toff302 ∷ []) (Toff302 ∷ CS01 ∷ []) (wl1223 (lit c4))
  q347 : Ws → Eqn
  q347 c4 = eqn (CX04 ∷ Toff302 ∷ []) (Toff302 ∷ CX04 ∷ []) (wp1052 c4)
  q348 : Ws → Eqn
  q348 c4 = eqn (CS14 ∷ Toff302 ∷ []) (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4))
  q349 : Ws → Eqn
  q349 c4 = eqn (Toff302 ∷ Toff304 ∷ []) (Toff304 ∷ Toff302 ∷ []) (wp1053 c4)
  q350 : Ws → Eqn
  q350 c4 = eqn (CX42 ∷ Toff304 ∷ Toff304 ∷ []) (CX42 ∷ []) (wp1054 c4)
  q351 : Ws → Eqn
  q351 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4)

-- CXcb-box @03103441: 18 steps
lem-CXcb-box-at03103441 : Ws → ⟪ (CX42 ∷ Bx3-0241 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03103441 c4 = derive (CX42 ∷ Bx3-0241 ∷ CX42 ∷ []) (Bx3-0241 ∷ CCZ014 ∷ [])
  (rw 1 (q332 c4) ∷
   rw 0 (q343 c4) ∷
   rw⁻ 2 (q344 c4) ∷
   rw⁻ 1 (q345 c4) ∷
   rw 4 (q60 c4) ∷
   rw 8 (q346 c4) ∷
   rw 7 (q347 c4) ∷
   rw 6 (q233 c4) ∷
   rw 5 (q347 c4) ∷
   rw 4 (q348 c4) ∷
   rw⁻ 5 (q60 c4) ∷
   rw⁻ 3 (q349 c4) ∷
   rw 2 (q343 c4) ∷
   rw 3 (q350 c4) ∷
   rw 4 (q351 c4) ∷
   rw⁻ 3 (q345 c4) ∷
   rw⁻ 0 (q332 c4) ∷
   rw⁻ 1 (q294 c4) ∷ []) Eq.refl

private
  q352 : Ws → Eqn
  q352 c4 = eqn (Toff304 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4))
  q353 : Ws → Eqn
  q353 c4 = eqn (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243241 c4)

-- VPQ @0310243241: 14 steps
lem-VPQ-at0310243241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0310243241 c4 = derive (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  (rw⁻ 0 (q310 c4) ∷
   rw⁻ 4 (q309 c4) ∷
   rw⁻ 3 (q318 c4) ∷
   rw 2 (q352 c4) ∷
   rw⁻ 1 (q316 c4) ∷
   rw 0 (q314 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q353 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q313 c4) ∷
   rw 2 (q289 c4) ∷
   rw 3 (q311 c4) ∷
   rw 0 (q309 c4) ∷
   rw 2 (q310 c4) ∷ []) Eq.refl

private
  q354 : Ws → Eqn
  q354 c4 = eqn (Bx3-0421 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4)
  q355 : Ws → Eqn
  q355 c4 = eqn (CX42 ∷ Toff304 ∷ []) (Toff304 ∷ CX42 ∷ []) (wp1055 c4)
  q356 : Ws → Eqn
  q356 c4 = eqn (CCZ123 ∷ CX42 ∷ CCZ134 ∷ []) (CX42 ∷ CCZ123 ∷ []) (wl1244 (lit c4))
  q357 : Ws → Eqn
  q357 c4 = eqn (CCZ134 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp1056 c4)
  q358 : Ws → Eqn
  q358 c4 = eqn (CX42 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX42 ∷ []) (wl1245 (lit c4))

-- CXbc-box @0310243241: 17 steps
lem-CXbc-box-at0310243241 : Ws → ⟪ (CX42 ∷ Bx3-0421 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0310243241 c4 = derive (CX42 ∷ Bx3-0421 ∷ CX42 ∷ []) (Bx3-0421 ∷ CCZ014 ∷ [])
  (rw 1 (q354 c4) ∷
   rw 0 (q355 c4) ∷
   rw⁻ 1 (q356 c4) ∷
   rw 3 (q357 c4) ∷
   rw 2 (q355 c4) ∷
   rw 5 (q60 c4) ∷
   rw⁻ 9 (q76 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 4 (q341 c4) ∷
   rw⁻ 3 (q356 c4) ∷
   rw 4 (q358 c4) ∷
   rw⁻ 0 (q354 c4) ∷
   rw⁻ 1 (q294 c4) ∷ []) Eq.refl

private
  q359 : Ws → Eqn
  q359 c4 = eqn (CX24 ∷ Toff304 ∷ []) (Toff304 ∷ CX24 ∷ Toff302 ∷ []) (wp1057 c4)
  q360 : Ws → Eqn
  q360 c4 = eqn (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ []) (Toff302 ∷ CCZ123 ∷ []) (wl1246 (lit c4))
  q361 : Ws → Eqn
  q361 c4 = eqn (CCZ123 ∷ CX24 ∷ []) (CX24 ∷ CCZ123 ∷ []) (wl0406 (lit c4))
  q362 : Ws → Eqn
  q362 c4 = eqn (CS01 ∷ Toff304 ∷ []) (Toff304 ∷ CS01 ∷ []) (wp1058 c4)
  q363 : Ws → Eqn
  q363 c4 = eqn (CX02 ∷ Toff304 ∷ []) (Toff304 ∷ CX02 ∷ []) (wp1059 c4)
  q364 : Ws → Eqn
  q364 c4 = eqn (CS12 ∷ Toff304 ∷ []) (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4))
  q365 : Ws → Eqn
  q365 c4 = eqn (CX24 ∷ Toff302 ∷ Toff302 ∷ []) (CX24 ∷ []) (wp1060 c4)
  q366 : Ws → Eqn
  q366 c4 = eqn (CCZ012 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4))

-- CXcb-box @0310243241: 18 steps
lem-CXcb-box-at0310243241 : Ws → ⟪ (CX24 ∷ Bx3-0421 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0310243241 c4 = derive (CX24 ∷ Bx3-0421 ∷ CX24 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  (rw 1 (q354 c4) ∷
   rw 0 (q359 c4) ∷
   rw⁻ 2 (q360 c4) ∷
   rw⁻ 1 (q361 c4) ∷
   rw 4 (q336 c4) ∷
   rw 8 (q362 c4) ∷
   rw 7 (q363 c4) ∷
   rw 6 (q317 c4) ∷
   rw 5 (q363 c4) ∷
   rw 4 (q364 c4) ∷
   rw⁻ 5 (q336 c4) ∷
   rw 3 (q349 c4) ∷
   rw 2 (q359 c4) ∷
   rw 3 (q365 c4) ∷
   rw 4 (q366 c4) ∷
   rw⁻ 3 (q361 c4) ∷
   rw⁻ 0 (q354 c4) ∷
   rw⁻ 1 (q282 c4) ∷ []) Eq.refl

private
  q367 : Ws → Eqn
  q367 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03103441 c4)
  q368 : Ws → Eqn
  q368 c4 = eqn (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ134 ∷ []) (wl1253 (lit c4))
  q369 : Ws → Eqn
  q369 c4 = eqn (CCZ134 ∷ CZ14 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff314 ∷ []) (wl1254 (lit c4))
  q370 : Ws → Eqn
  q370 c4 = eqn (CCZ134 ∷ []) (CZ14 ∷ CCZ134 ∷ CZ14 ∷ []) (wl1255 (lit c4))

-- P-box @03103441: 8 steps
lem-P-box-at03103441 : Ws → ⟪ (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-P-box-at03103441 c4 = derive (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) (Bx3-0241 ∷ [])
  (rw 1 (q332 c4) ∷
   rw⁻ 0 (q367 c4) ∷
   rw⁻ 1 (q368 c4) ∷
   rw⁻ 3 (q367 c4) ∷
   rw⁻ 4 (q369 c4) ∷
   rw 2 (q296 c4) ∷
   rw⁻ 3 (q370 c4) ∷
   rw⁻ 0 (q332 c4) ∷ []) Eq.refl

private
  q371 : Ws → Eqn
  q371 c4 = eqn (Toff302 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4))

-- VPQ @03103441: 14 steps
lem-VPQ-at03103441 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at03103441 c4 = derive (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q225 c4) ∷
   rw⁻ 4 (q224 c4) ∷
   rw⁻ 3 (q234 c4) ∷
   rw 2 (q371 c4) ∷
   rw⁻ 1 (q232 c4) ∷
   rw 0 (q229 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q367 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q228 c4) ∷
   rw 2 (q249 c4) ∷
   rw 3 (q226 c4) ∷
   rw 0 (q224 c4) ∷
   rw 2 (q225 c4) ∷ []) Eq.refl

private
  q372 : Ws → Eqn
  q372 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4)
  q373 : Ws → Eqn
  q373 c4 = eqn (CX41 ∷ Toff304 ∷ []) (Toff304 ∷ CX41 ∷ []) (wp0692 c4)
  q374 : Ws → Eqn
  q374 c4 = eqn (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (CX41 ∷ CCZ123 ∷ []) (wl0694 (lit c4))
  q375 : Ws → Eqn
  q375 c4 = eqn (CCZ234 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp1063 c4)
  q376 : Ws → Eqn
  q376 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4)
  q377 : Ws → Eqn
  q377 c4 = eqn (CCZ123 ∷ CS02 ∷ []) (CS02 ∷ CCZ123 ∷ []) (wl0171 (lit c4))
  q378 : Ws → Eqn
  q378 c4 = eqn (CCZ123 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ123 ∷ []) (wl0172 (lit c4))
  q379 : Ws → Eqn
  q379 c4 = eqn (CCZ123 ∷ CS24 ∷ []) (CS24 ∷ CCZ123 ∷ []) (wl0173 (lit c4))
  q380 : Ws → Eqn
  q380 c4 = eqn (CCZ123 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4))
  q381 : Ws → Eqn
  q381 c4 = eqn (CX41 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX41 ∷ []) (wl0695 (lit c4))
  q382 : Ws → Eqn
  q382 c4 = eqn (CCZ024 ∷ []) (CX41 ∷ CCZ024 ∷ CX41 ∷ []) (wp0727 c4)

-- CXbc-box @0310243142: 17 steps
lem-CXbc-box-at0310243142 : Ws → ⟪ (CX41 ∷ Bx3-0412 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0310243142 c4 = derive (CX41 ∷ Bx3-0412 ∷ CX41 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ [])
  (rw 1 (q372 c4) ∷
   rw 0 (q373 c4) ∷
   rw⁻ 1 (q374 c4) ∷
   rw 3 (q375 c4) ∷
   rw 2 (q373 c4) ∷
   rw 5 (q376 c4) ∷
   rw⁻ 9 (q377 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 7 (q378 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 5 (q379 c4) ∷
   rw⁻ 6 (q376 c4) ∷
   rw⁻ 4 (q380 c4) ∷
   rw⁻ 3 (q374 c4) ∷
   rw 4 (q381 c4) ∷
   rw⁻ 0 (q372 c4) ∷
   rw⁻ 1 (q382 c4) ∷ []) Eq.refl

private
  q383 : Ws → Eqn
  q383 c4 = eqn (CX14 ∷ Toff304 ∷ []) (Toff304 ∷ CX14 ∷ Toff301 ∷ []) (wp1064 c4)
  q384 : Ws → Eqn
  q384 c4 = eqn (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (Toff301 ∷ CCZ123 ∷ []) (wl1256 (lit c4))
  q385 : Ws → Eqn
  q385 c4 = eqn (CCZ123 ∷ CX14 ∷ []) (CX14 ∷ CCZ123 ∷ []) (wl0424 (lit c4))
  q386 : Ws → Eqn
  q386 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4))
  q387 : Ws → Eqn
  q387 c4 = eqn (CS02 ∷ Toff304 ∷ []) (Toff304 ∷ CS02 ∷ []) (wp1065 c4)
  q388 : Ws → Eqn
  q388 c4 = eqn (CX01 ∷ Toff304 ∷ []) (Toff304 ∷ CX01 ∷ []) (wp0688 c4)
  q389 : Ws → Eqn
  q389 c4 = eqn (Toff301 ∷ Toff304 ∷ []) (Toff304 ∷ Toff301 ∷ []) (wp1066 c4)
  q390 : Ws → Eqn
  q390 c4 = eqn (CX14 ∷ Toff301 ∷ Toff301 ∷ []) (CX14 ∷ []) (wp1067 c4)
  q391 : Ws → Eqn
  q391 c4 = eqn (CCZ012 ∷ []) (CX14 ∷ CCZ012 ∷ CX14 ∷ []) (wp0728 c4)

-- CXcb-box @0310243142: 18 steps
lem-CXcb-box-at0310243142 : Ws → ⟪ (CX14 ∷ Bx3-0412 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0310243142 c4 = derive (CX14 ∷ Bx3-0412 ∷ CX14 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  (rw 1 (q372 c4) ∷
   rw 0 (q383 c4) ∷
   rw⁻ 2 (q384 c4) ∷
   rw⁻ 1 (q385 c4) ∷
   rw 4 (q386 c4) ∷
   rw 8 (q387 c4) ∷
   rw 7 (q388 c4) ∷
   rw 6 (q317 c4) ∷
   rw 5 (q388 c4) ∷
   rw 4 (q364 c4) ∷
   rw⁻ 5 (q386 c4) ∷
   rw 3 (q389 c4) ∷
   rw 2 (q383 c4) ∷
   rw 3 (q390 c4) ∷
   rw 4 (q366 c4) ∷
   rw⁻ 3 (q385 c4) ∷
   rw⁻ 0 (q372 c4) ∷
   rw⁻ 1 (q391 c4) ∷ []) Eq.refl

private
  q392 : Ws → Eqn
  q392 c4 = eqn (CX14 ∷ CX41 ∷ CX14 ∷ []) (Sw14 ∷ []) (wl0423 (lit c4))
  q393 : Ws → Eqn
  q393 c4 = eqn (CX14 ∷ Bx3-0142 ∷ CX14 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0310213442 c4)
  q394 : Ws → Eqn
  q394 c4 = eqn (CCZ012 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4)
  q395 : Ws → Eqn
  q395 c4 = eqn (CX41 ∷ Bx3-0142 ∷ CX41 ∷ []) (Bx3-0142 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0310213442 c4)
  q396 : Ws → Eqn
  q396 c4 = eqn (CCZ012 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ []) (wp0145 c4)
  q397 : Ws → Eqn
  q397 c4 = eqn (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4)
  q398 : Ws → Eqn
  q398 c4 = eqn (CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (CCZ012 ∷ []) (wp0738 c4)
  q399 : Ws → Eqn
  q399 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0341 (lit c4))

-- SWbc-box @0310213442: 11 steps
lem-SWbc-box-at0310213442 : Ws → ⟪ (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-SWbc-box-at0310213442 c4 = derive (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (Bx3-0142 ∷ [])
  (rw⁻ 0 (q392 c4) ∷
   rw⁻ 4 (q392 c4) ∷
   rw 2 (q393 c4) ∷
   rw 3 (q394 c4) ∷
   rw 1 (q395 c4) ∷
   rw 4 (q396 c4) ∷
   rw 3 (q397 c4) ∷
   rw 2 (q397 c4) ∷
   rw 3 (q398 c4) ∷
   rw 0 (q393 c4) ∷
   rw 1 (q399 c4) ∷ []) Eq.refl

-- P-box @0314213240: 8 steps
lem-P-box-at0314213240 : Ws → ⟪ (Toff302 ∷ Bx3-4120 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-P-box-at0314213240 c4 = derive (Toff302 ∷ Bx3-4120 ∷ Toff302 ∷ []) (Bx3-4120 ∷ [])
  (rw 1 (q235 c4) ∷
   rw⁻ 0 (q231 c4) ∷
   rw⁻ 1 (q328 c4) ∷
   rw⁻ 3 (q231 c4) ∷
   rw⁻ 4 (q329 c4) ∷
   rw 2 (q330 c4) ∷
   rw⁻ 3 (q331 c4) ∷
   rw⁻ 0 (q235 c4) ∷ []) Eq.refl

private
  q400 : Ws → Eqn
  q400 c4 = eqn (Bx3-2041 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at0312203441 c4)
  q401 : Ws → Eqn
  q401 c4 = eqn (CCZ134 ∷ CX04 ∷ CCZ013 ∷ []) (CX04 ∷ CCZ134 ∷ []) (wp1077 c4)
  q402 : Ws → Eqn
  q402 c4 = eqn (CCZ013 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1272 (lit c4))
  q403 : Ws → Eqn
  q403 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4))
  q404 : Ws → Eqn
  q404 c4 = eqn (CX20 ∷ CCZ134 ∷ []) (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4))
  q405 : Ws → Eqn
  q405 c4 = eqn (CCZ134 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4)
  q406 : Ws → Eqn
  q406 c4 = eqn (CX04 ∷ CCZ013 ∷ CCZ013 ∷ []) (CX04 ∷ []) (wp1078 c4)
  q407 : Ws → Eqn
  q407 c4 = eqn (CCZ012 ∷ []) (CX04 ∷ CCZ012 ∷ CX04 ∷ []) (wp1079 c4)

-- CXbc-box @0312203441: 17 steps
lem-CXbc-box-at0312203441 : Ws → ⟪ (CX04 ∷ Bx3-2041 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0312203441 c4 = derive (CX04 ∷ Bx3-2041 ∷ CX04 ∷ []) (Bx3-2041 ∷ CCZ012 ∷ [])
  (rw 1 (q400 c4) ∷
   rw 0 (q347 c4) ∷
   rw⁻ 1 (q401 c4) ∷
   rw 3 (q402 c4) ∷
   rw 2 (q347 c4) ∷
   rw 5 (q403 c4) ∷
   rw⁻ 9 (q340 c4) ∷
   rw 8 (q404 c4) ∷
   rw⁻ 7 (q405 c4) ∷
   rw 6 (q404 c4) ∷
   rw⁻ 5 (q337 c4) ∷
   rw⁻ 6 (q403 c4) ∷
   rw 4 (q165 c4) ∷
   rw⁻ 3 (q401 c4) ∷
   rw 4 (q406 c4) ∷
   rw⁻ 0 (q400 c4) ∷
   rw⁻ 1 (q407 c4) ∷ []) Eq.refl

private
  q408 : Ws → Eqn
  q408 c4 = eqn (CX40 ∷ Toff302 ∷ []) (Toff302 ∷ CX40 ∷ Toff324 ∷ []) (wp1080 c4)
  q409 : Ws → Eqn
  q409 c4 = eqn (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ134 ∷ []) (wl1189 (lit c4))
  q410 : Ws → Eqn
  q410 c4 = eqn (CCZ134 ∷ CX40 ∷ []) (CX40 ∷ CCZ134 ∷ []) (wp1081 c4)
  q411 : Ws → Eqn
  q411 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0644 (lit c4))
  q412 : Ws → Eqn
  q412 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4))
  q413 : Ws → Eqn
  q413 c4 = eqn (Toff302 ∷ Toff324 ∷ []) (Toff324 ∷ Toff302 ∷ []) (wp1007 c4)
  q414 : Ws → Eqn
  q414 c4 = eqn (CX40 ∷ Toff324 ∷ Toff324 ∷ []) (CX40 ∷ []) (wp1082 c4)
  q415 : Ws → Eqn
  q415 c4 = eqn (CCZ124 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4))
  q416 : Ws → Eqn
  q416 c4 = eqn (CCZ124 ∷ []) (CX40 ∷ CCZ124 ∷ CX40 ∷ []) (wp1083 c4)

-- CXcb-box @0312203441: 18 steps
lem-CXcb-box-at0312203441 : Ws → ⟪ (CX40 ∷ Bx3-2041 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at0312203441 c4 = derive (CX40 ∷ Bx3-2041 ∷ CX40 ∷ []) (Bx3-2041 ∷ CCZ124 ∷ [])
  (rw 1 (q400 c4) ∷
   rw 0 (q408 c4) ∷
   rw⁻ 2 (q409 c4) ∷
   rw⁻ 1 (q410 c4) ∷
   rw 4 (q411 c4) ∷
   rw 8 (q412 c4) ∷
   rw 7 (q333 c4) ∷
   rw 6 (q233 c4) ∷
   rw 5 (q333 c4) ∷
   rw 4 (q348 c4) ∷
   rw⁻ 5 (q411 c4) ∷
   rw⁻ 3 (q413 c4) ∷
   rw 2 (q408 c4) ∷
   rw 3 (q414 c4) ∷
   rw 4 (q415 c4) ∷
   rw⁻ 3 (q410 c4) ∷
   rw⁻ 0 (q400 c4) ∷
   rw⁻ 1 (q416 c4) ∷ []) Eq.refl

private
  q417 : Ws → Eqn
  q417 c4 = eqn (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243041 c4)

-- VPQ @0312243041: 14 steps
lem-VPQ-at0312243041 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0312243041 c4 = derive (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  (rw⁻ 0 (q252 c4) ∷
   rw⁻ 4 (q253 c4) ∷
   rw⁻ 3 (q254 c4) ∷
   rw⁻ 2 (q218 c4) ∷
   rw⁻ 1 (q255 c4) ∷
   rw⁻ 0 (q256 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q417 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q258 c4) ∷
   rw 2 (q259 c4) ∷
   rw 3 (q260 c4) ∷
   rw 0 (q253 c4) ∷
   rw 2 (q252 c4) ∷ []) Eq.refl

private
  q418 : Ws → Eqn
  q418 c4 = eqn (Bx3-2401 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243041 c4)
  q419 : Ws → Eqn
  q419 c4 = eqn (CX40 ∷ Toff324 ∷ []) (Toff324 ∷ CX40 ∷ []) (wp1094 c4)
  q420 : Ws → Eqn
  q420 c4 = eqn (CCZ013 ∷ CX40 ∷ CCZ134 ∷ []) (CX40 ∷ CCZ013 ∷ []) (wp1095 c4)
  q421 : Ws → Eqn
  q421 c4 = eqn (CCZ134 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1277 (lit c4))
  q422 : Ws → Eqn
  q422 c4 = eqn (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) (wl0645 (lit c4))
  q423 : Ws → Eqn
  q423 c4 = eqn (CX24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4))
  q424 : Ws → Eqn
  q424 c4 = eqn (CCZ013 ∷ CS14⁻ ∷ []) (CS14⁻ ∷ CCZ013 ∷ []) (wp0521 c4)
  q425 : Ws → Eqn
  q425 c4 = eqn (CCZ013 ∷ CS14 ∷ []) (CS14 ∷ CCZ013 ∷ []) (wp0299 c4)
  q426 : Ws → Eqn
  q426 c4 = eqn (CX40 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX40 ∷ []) (wp1096 c4)

-- CXbc-box @0312243041: 17 steps
lem-CXbc-box-at0312243041 : Ws → ⟪ (CX40 ∷ Bx3-2401 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at0312243041 c4 = derive (CX40 ∷ Bx3-2401 ∷ CX40 ∷ []) (Bx3-2401 ∷ CCZ124 ∷ [])
  (rw 1 (q418 c4) ∷
   rw 0 (q419 c4) ∷
   rw⁻ 1 (q420 c4) ∷
   rw 3 (q421 c4) ∷
   rw 2 (q419 c4) ∷
   rw 5 (q411 c4) ∷
   rw⁻ 9 (q422 c4) ∷
   rw 8 (q423 c4) ∷
   rw⁻ 7 (q424 c4) ∷
   rw 6 (q423 c4) ∷
   rw⁻ 5 (q425 c4) ∷
   rw⁻ 6 (q411 c4) ∷
   rw⁻ 4 (q165 c4) ∷
   rw⁻ 3 (q420 c4) ∷
   rw 4 (q426 c4) ∷
   rw⁻ 0 (q418 c4) ∷
   rw⁻ 1 (q416 c4) ∷ []) Eq.refl

private
  q427 : Ws → Eqn
  q427 c4 = eqn (CX04 ∷ Toff324 ∷ []) (Toff324 ∷ CX04 ∷ Toff302 ∷ []) (wp1097 c4)
  q428 : Ws → Eqn
  q428 c4 = eqn (CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) (Toff302 ∷ CCZ013 ∷ []) (wl1278 (lit c4))
  q429 : Ws → Eqn
  q429 c4 = eqn (CCZ013 ∷ CX04 ∷ []) (CX04 ∷ CCZ013 ∷ []) (wp1098 c4)
  q430 : Ws → Eqn
  q430 c4 = eqn (CS12 ∷ Toff324 ∷ []) (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4))
  q431 : Ws → Eqn
  q431 c4 = eqn (CX20 ∷ Toff324 ∷ []) (Toff324 ∷ CX20 ∷ []) (wp1099 c4)
  q432 : Ws → Eqn
  q432 c4 = eqn (CX04 ∷ Toff302 ∷ Toff302 ∷ []) (CX04 ∷ []) (wp1100 c4)
  q433 : Ws → Eqn
  q433 c4 = eqn (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) (wl0704 (lit c4))

-- CXcb-box @0312243041: 18 steps
lem-CXcb-box-at0312243041 : Ws → ⟪ (CX04 ∷ Bx3-2401 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0312243041 c4 = derive (CX04 ∷ Bx3-2401 ∷ CX04 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ [])
  (rw 1 (q418 c4) ∷
   rw 0 (q427 c4) ∷
   rw⁻ 2 (q428 c4) ∷
   rw⁻ 1 (q429 c4) ∷
   rw 4 (q403 c4) ∷
   rw 8 (q430 c4) ∷
   rw 7 (q431 c4) ∷
   rw 6 (q218 c4) ∷
   rw 5 (q431 c4) ∷
   rw 4 (q219 c4) ∷
   rw⁻ 5 (q403 c4) ∷
   rw 3 (q413 c4) ∷
   rw 2 (q427 c4) ∷
   rw 3 (q432 c4) ∷
   rw 4 (q433 c4) ∷
   rw⁻ 3 (q429 c4) ∷
   rw⁻ 0 (q418 c4) ∷
   rw⁻ 1 (q407 c4) ∷ []) Eq.refl

private
  q434 : Ws → Eqn
  q434 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at0312203441 c4)

-- P-box @0312203441: 8 steps
lem-P-box-at0312203441 : Ws → ⟪ (Toff314 ∷ Bx3-2041 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-P-box-at0312203441 c4 = derive (Toff314 ∷ Bx3-2041 ∷ Toff314 ∷ []) (Bx3-2041 ∷ [])
  (rw 1 (q400 c4) ∷
   rw⁻ 0 (q434 c4) ∷
   rw⁻ 1 (q368 c4) ∷
   rw⁻ 3 (q434 c4) ∷
   rw⁻ 4 (q369 c4) ∷
   rw 2 (q296 c4) ∷
   rw⁻ 3 (q370 c4) ∷
   rw⁻ 0 (q400 c4) ∷ []) Eq.refl

-- VPQ @0312203441: 14 steps
lem-VPQ-at0312203441 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0312203441 c4 = derive (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q225 c4) ∷
   rw⁻ 4 (q224 c4) ∷
   rw⁻ 3 (q234 c4) ∷
   rw 2 (q371 c4) ∷
   rw⁻ 1 (q232 c4) ∷
   rw 0 (q229 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q434 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q228 c4) ∷
   rw 2 (q249 c4) ∷
   rw 3 (q226 c4) ∷
   rw 0 (q224 c4) ∷
   rw 2 (q225 c4) ∷ []) Eq.refl

private
  q435 : Ws → Eqn
  q435 c4 = eqn (Bx0-1243 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4)
  q436 : Ws → Eqn
  q436 c4 = eqn (CCZ023 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1283 (lit c4))
  q437 : Ws → Eqn
  q437 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4))
  q438 : Ws → Eqn
  q438 c4 = eqn (CCZ034 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4)
  q439 : Ws → Eqn
  q439 c4 = eqn (CCZ123 ∷ []) (CX24 ∷ CCZ123 ∷ CX24 ∷ []) (wl0315 (lit c4))

-- CXbc-box @3443: 17 steps
lem-CXbc-box-at3443 : Ws → ⟪ (CX24 ∷ Bx0-1243 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at3443 c4 = derive (CX24 ∷ Bx0-1243 ∷ CX24 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  (rw 1 (q435 c4) ∷
   rw 0 (q184 c4) ∷
   rw⁻ 1 (q273 c4) ∷
   rw 3 (q436 c4) ∷
   rw 2 (q184 c4) ∷
   rw 5 (q437 c4) ∷
   rw⁻ 9 (q175 c4) ∷
   rw 8 (q277 c4) ∷
   rw⁻ 7 (q438 c4) ∷
   rw 6 (q277 c4) ∷
   rw⁻ 5 (q172 c4) ∷
   rw⁻ 6 (q437 c4) ∷
   rw 4 (q280 c4) ∷
   rw⁻ 3 (q273 c4) ∷
   rw 4 (q281 c4) ∷
   rw⁻ 0 (q435 c4) ∷
   rw⁻ 1 (q439 c4) ∷ []) Eq.refl

private
  q440 : Ws → Eqn
  q440 c4 = eqn (CX42 ∷ Toff012 ∷ []) (Toff012 ∷ CX42 ∷ Toff014 ∷ []) (wp1113 c4)
  q441 : Ws → Eqn
  q441 c4 = eqn (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (Toff014 ∷ CCZ034 ∷ []) (wp1114 c4)
  q442 : Ws → Eqn
  q442 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4))
  q443 : Ws → Eqn
  q443 c4 = eqn (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) (wl1284 (lit c4))
  q444 : Ws → Eqn
  q444 c4 = eqn (Toff012 ∷ Toff014 ∷ []) (Toff014 ∷ Toff012 ∷ []) (wp0580 c4)
  q445 : Ws → Eqn
  q445 c4 = eqn (CX42 ∷ Toff014 ∷ Toff014 ∷ []) (CX42 ∷ []) (wp1115 c4)
  q446 : Ws → Eqn
  q446 c4 = eqn (CCZ034 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4)
  q447 : Ws → Eqn
  q447 c4 = eqn (CCZ134 ∷ []) (CX42 ∷ CCZ134 ∷ CX42 ∷ []) (wl0312 (lit c4))

-- CXcb-box @3443: 18 steps
lem-CXcb-box-at3443 : Ws → ⟪ (CX42 ∷ Bx0-1243 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at3443 c4 = derive (CX42 ∷ Bx0-1243 ∷ CX42 ∷ []) (Bx0-1243 ∷ CCZ134 ∷ [])
  (rw 1 (q435 c4) ∷
   rw 0 (q440 c4) ∷
   rw⁻ 2 (q441 c4) ∷
   rw⁻ 1 (q285 c4) ∷
   rw 4 (q442 c4) ∷
   rw 8 (q443 c4) ∷
   rw 7 (q168 c4) ∷
   rw⁻ 6 (q185 c4) ∷
   rw 5 (q168 c4) ∷
   rw⁻ 4 (q186 c4) ∷
   rw⁻ 5 (q442 c4) ∷
   rw⁻ 3 (q444 c4) ∷
   rw 2 (q440 c4) ∷
   rw 3 (q445 c4) ∷
   rw⁻ 4 (q446 c4) ∷
   rw⁻ 3 (q285 c4) ∷
   rw⁻ 0 (q435 c4) ∷
   rw⁻ 1 (q447 c4) ∷ []) Eq.refl

private
  q448 : Ws → Eqn
  q448 c4 = eqn (Bx0-1234 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4)
  q449 : Ws → Eqn
  q449 c4 = eqn (Toff012 ∷ CK34 ∷ []) (CK34 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₀₁))
  q450 : Ws → Eqn
  q450 c4 = eqn (CK34 ∷ CCZ034 ∷ []) (Toff403 ∷ CK34 ∷ []) (wp1126 c4)
  q451 : Ws → Eqn
  q451 c4 = eqn (CK34 ∷ CK34⁻ ∷ []) [] (wl1300 (lit c4))

-- CK-box: 6 steps
lem-CK-box : Ws → ⟪ (CK34 ∷ Bx0-1234 ∷ CK34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff403 ∷ Toff012 ∷ Toff403 ∷ []) ⟫ʷ
lem-CK-box c4 = derive (CK34 ∷ Bx0-1234 ∷ CK34⁻ ∷ []) (Toff012 ∷ Toff403 ∷ Toff012 ∷ Toff403 ∷ [])
  (rw 1 (q448 c4) ∷
   rw⁻ 0 (q449 c4) ∷
   rw 1 (q450 c4) ∷
   rw⁻ 2 (q449 c4) ∷
   rw 3 (q450 c4) ∷
   rw 4 (q451 c4) ∷ []) Eq.refl

-- P-box @03243240: 8 steps
lem-P-box-at03243240 : Ws → ⟪ (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-P-box-at03243240 c4 = derive (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) (Bx3-1420 ∷ [])
  (rw 1 (q298 c4) ∷
   rw⁻ 0 (q264 c4) ∷
   rw⁻ 1 (q328 c4) ∷
   rw⁻ 3 (q264 c4) ∷
   rw⁻ 4 (q329 c4) ∷
   rw 2 (q330 c4) ∷
   rw⁻ 3 (q331 c4) ∷
   rw⁻ 0 (q298 c4) ∷ []) Eq.refl

private
  q452 : Ws → Eqn
  q452 c4 = eqn (Bx3-0214 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4)
  q453 : Ws → Eqn
  q453 c4 = eqn (CX21 ∷ Toff302 ∷ []) (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4))
  q454 : Ws → Eqn
  q454 c4 = eqn (CCZ134 ∷ CX21 ∷ CCZ234 ∷ []) (CX21 ∷ CCZ134 ∷ []) (wl1305 (lit c4))
  q455 : Ws → Eqn
  q455 c4 = eqn (CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp1128 c4)
  q456 : Ws → Eqn
  q456 c4 = eqn (CCZ024 ∷ []) (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4)
  q457 : Ws → Eqn
  q457 c4 = eqn (CCZ134 ∷ CS04 ∷ []) (CS04 ∷ CCZ134 ∷ []) (wp1003 c4)
  q458 : Ws → Eqn
  q458 c4 = eqn (CCZ134 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4))
  q459 : Ws → Eqn
  q459 c4 = eqn (CCZ134 ∷ CS24 ∷ []) (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4))
  q460 : Ws → Eqn
  q460 c4 = eqn (CCZ134 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ134 ∷ []) (wl0960 (lit c4))
  q461 : Ws → Eqn
  q461 c4 = eqn (CX21 ∷ CCZ234 ∷ CCZ234 ∷ []) (CX21 ∷ []) (wl1306 (lit c4))

-- CXbc-box @031031: 17 steps
lem-CXbc-box-at031031 : Ws → ⟪ (CX21 ∷ Bx3-0214 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at031031 c4 = derive (CX21 ∷ Bx3-0214 ∷ CX21 ∷ []) (Bx3-0214 ∷ CCZ024 ∷ [])
  (rw 1 (q452 c4) ∷
   rw 0 (q453 c4) ∷
   rw⁻ 1 (q454 c4) ∷
   rw 3 (q455 c4) ∷
   rw 2 (q453 c4) ∷
   rw 5 (q456 c4) ∷
   rw⁻ 9 (q457 c4) ∷
   rw 8 (q338 c4) ∷
   rw⁻ 7 (q458 c4) ∷
   rw 6 (q338 c4) ∷
   rw⁻ 5 (q459 c4) ∷
   rw⁻ 6 (q456 c4) ∷
   rw⁻ 4 (q460 c4) ∷
   rw⁻ 3 (q454 c4) ∷
   rw 4 (q461 c4) ∷
   rw⁻ 0 (q452 c4) ∷
   rw⁻ 1 (q212 c4) ∷ []) Eq.refl

private
  q462 : Ws → Eqn
  q462 c4 = eqn (CX12 ∷ Toff302 ∷ []) (Toff302 ∷ CX12 ∷ Toff301 ∷ []) (wl1307 (lit c4))
  q463 : Ws → Eqn
  q463 c4 = eqn (CCZ134 ∷ Toff301 ∷ CCZ014 ∷ []) (Toff301 ∷ CCZ134 ∷ []) (wp1129 c4)
  q464 : Ws → Eqn
  q464 c4 = eqn (CCZ134 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ []) (wl0679 (lit c4))
  q465 : Ws → Eqn
  q465 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4)
  q466 : Ws → Eqn
  q466 c4 = eqn (CS04 ∷ Toff302 ∷ []) (Toff302 ∷ CS04 ∷ []) (wp1041 c4)
  q467 : Ws → Eqn
  q467 c4 = eqn (CX01 ∷ Toff302 ∷ []) (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4))
  q468 : Ws → Eqn
  q468 c4 = eqn (Toff301 ∷ Toff302 ∷ []) (Toff302 ∷ Toff301 ∷ []) (wl1100 (lit c4))
  q469 : Ws → Eqn
  q469 c4 = eqn (CX12 ∷ Toff301 ∷ Toff301 ∷ []) (CX12 ∷ []) (wl1308 (lit c4))

-- CXcb-box @031031: 18 steps
lem-CXcb-box-at031031 : Ws → ⟪ (CX12 ∷ Bx3-0214 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at031031 c4 = derive (CX12 ∷ Bx3-0214 ∷ CX12 ∷ []) (Bx3-0214 ∷ CCZ014 ∷ [])
  (rw 1 (q452 c4) ∷
   rw 0 (q462 c4) ∷
   rw⁻ 2 (q463 c4) ∷
   rw⁻ 1 (q464 c4) ∷
   rw 4 (q465 c4) ∷
   rw 8 (q466 c4) ∷
   rw 7 (q467 c4) ∷
   rw 6 (q233 c4) ∷
   rw 5 (q467 c4) ∷
   rw 4 (q348 c4) ∷
   rw⁻ 5 (q465 c4) ∷
   rw 3 (q468 c4) ∷
   rw 2 (q462 c4) ∷
   rw 3 (q469 c4) ∷
   rw 4 (q351 c4) ∷
   rw⁻ 3 (q464 c4) ∷
   rw⁻ 0 (q452 c4) ∷
   rw⁻ 1 (q223 c4) ∷ []) Eq.refl

private
  q470 : Ws → Eqn
  q470 c4 = eqn (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ []) (lem-tP-at031031 c4)

-- VPQ @031031: 14 steps
lem-VPQ-at031031 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at031031 c4 = derive (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  (rw⁻ 0 (q225 c4) ∷
   rw⁻ 4 (q224 c4) ∷
   rw⁻ 3 (q234 c4) ∷
   rw 2 (q371 c4) ∷
   rw⁻ 1 (q232 c4) ∷
   rw 0 (q229 c4) ∷
   rw 4 (q230 c4) ∷
   rw 3 (q470 c4) ∷
   rw⁻ 4 (q230 c4) ∷
   rw 1 (q228 c4) ∷
   rw 2 (q249 c4) ∷
   rw 3 (q226 c4) ∷
   rw 0 (q224 c4) ∷
   rw 2 (q225 c4) ∷ []) Eq.refl

private
  q471 : Ws → Eqn
  q471 c4 = eqn (Bx3-4201 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4)
  q472 : Ws → Eqn
  q472 c4 = eqn (CCZ013 ∷ CX20 ∷ CCZ123 ∷ []) (CX20 ∷ CCZ013 ∷ []) (wl1317 (lit c4))
  q473 : Ws → Eqn
  q473 c4 = eqn (CCZ123 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0445 (lit c4))
  q474 : Ws → Eqn
  q474 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4))
  q475 : Ws → Eqn
  q475 c4 = eqn (CCZ013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ013 ∷ []) (wl0703 (lit c4))
  q476 : Ws → Eqn
  q476 c4 = eqn (CX20 ∷ CCZ123 ∷ CCZ123 ∷ []) (CX20 ∷ []) (wl1318 (lit c4))
  q477 : Ws → Eqn
  q477 c4 = eqn (CCZ124 ∷ []) (CX20 ∷ CCZ124 ∷ CX20 ∷ []) (wp0380 c4)

-- CXbc-box @03143041: 17 steps
lem-CXbc-box-at03143041 : Ws → ⟪ (CX20 ∷ Bx3-4201 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at03143041 c4 = derive (CX20 ∷ Bx3-4201 ∷ CX20 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ [])
  (rw 1 (q471 c4) ∷
   rw 0 (q431 c4) ∷
   rw⁻ 1 (q472 c4) ∷
   rw 3 (q473 c4) ∷
   rw 2 (q431 c4) ∷
   rw 5 (q474 c4) ∷
   rw⁻ 9 (q425 c4) ∷
   rw 8 (q150 c4) ∷
   rw⁻ 7 (q475 c4) ∷
   rw 6 (q150 c4) ∷
   rw⁻ 5 (q422 c4) ∷
   rw⁻ 6 (q474 c4) ∷
   rw⁻ 4 (q88 c4) ∷
   rw⁻ 3 (q472 c4) ∷
   rw 4 (q476 c4) ∷
   rw⁻ 0 (q471 c4) ∷
   rw⁻ 1 (q477 c4) ∷ []) Eq.refl

private
  q478 : Ws → Eqn
  q478 c4 = eqn (CX02 ∷ Toff324 ∷ []) (Toff324 ∷ CX02 ∷ Toff304 ∷ []) (wp1141 c4)
  q479 : Ws → Eqn
  q479 c4 = eqn (CCZ013 ∷ Toff304 ∷ CCZ014 ∷ []) (Toff304 ∷ CCZ013 ∷ []) (wp1142 c4)
  q480 : Ws → Eqn
  q480 c4 = eqn (CCZ013 ∷ CX02 ∷ []) (CX02 ∷ CCZ013 ∷ []) (wl0444 (lit c4))
  q481 : Ws → Eqn
  q481 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4)
  q482 : Ws → Eqn
  q482 c4 = eqn (CS14 ∷ Toff324 ∷ []) (Toff324 ∷ CS14 ∷ []) (wl0543 (lit c4))
  q483 : Ws → Eqn
  q483 c4 = eqn (Toff304 ∷ Toff324 ∷ []) (Toff324 ∷ Toff304 ∷ []) (wp1144 c4)
  q484 : Ws → Eqn
  q484 c4 = eqn (CX02 ∷ Toff304 ∷ Toff304 ∷ []) (CX02 ∷ []) (wp1145 c4)
  q485 : Ws → Eqn
  q485 c4 = eqn (CCZ014 ∷ []) (CX02 ∷ CCZ014 ∷ CX02 ∷ []) (wp0378 c4)

-- CXcb-box @03143041: 18 steps
lem-CXcb-box-at03143041 : Ws → ⟪ (CX02 ∷ Bx3-4201 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03143041 c4 = derive (CX02 ∷ Bx3-4201 ∷ CX02 ∷ []) (Bx3-4201 ∷ CCZ014 ∷ [])
  (rw 1 (q471 c4) ∷
   rw 0 (q478 c4) ∷
   rw⁻ 2 (q479 c4) ∷
   rw⁻ 1 (q480 c4) ∷
   rw 4 (q481 c4) ∷
   rw 8 (q482 c4) ∷
   rw 7 (q419 c4) ∷
   rw 6 (q218 c4) ∷
   rw 5 (q419 c4) ∷
   rw 4 (q219 c4) ∷
   rw⁻ 5 (q481 c4) ∷
   rw 3 (q483 c4) ∷
   rw 2 (q478 c4) ∷
   rw 3 (q484 c4) ∷
   rw⁻ 4 (q222 c4) ∷
   rw⁻ 3 (q480 c4) ∷
   rw⁻ 0 (q471 c4) ∷
   rw⁻ 1 (q485 c4) ∷ []) Eq.refl

private
  q486 : Ws → Eqn
  q486 c4 = eqn (Bx2-4031 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4)
  q487 : Ws → Eqn
  q487 c4 = eqn (CCZ123 ∷ CX03 ∷ CCZ012 ∷ []) (CX03 ∷ CCZ123 ∷ []) (wl1320 (lit c4))
  q488 : Ws → Eqn
  q488 c4 = eqn (CCZ012 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1150 c4)
  q489 : Ws → Eqn
  q489 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q490 : Ws → Eqn
  q490 c4 = eqn (CCZ123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ123 ∷ []) (wl1321 (lit c4))
  q491 : Ws → Eqn
  q491 c4 = eqn (CX03 ∷ CCZ012 ∷ CCZ012 ∷ []) (CX03 ∷ []) (wl1322 (lit c4))
  q492 : Ws → Eqn
  q492 c4 = eqn (CCZ014 ∷ []) (CX03 ∷ CCZ014 ∷ CX03 ∷ []) (wp0761 c4)

-- CXbc-box @02142041: 17 steps
lem-CXbc-box-at02142041 : Ws → ⟪ (CX03 ∷ Bx2-4031 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at02142041 c4 = derive (CX03 ∷ Bx2-4031 ∷ CX03 ∷ []) (Bx2-4031 ∷ CCZ014 ∷ [])
  (rw 1 (q486 c4) ∷
   rw 0 (q85 c4) ∷
   rw⁻ 1 (q487 c4) ∷
   rw 3 (q488 c4) ∷
   rw 2 (q85 c4) ∷
   rw 5 (q481 c4) ∷
   rw⁻ 9 (q79 c4) ∷
   rw 8 (q489 c4) ∷
   rw⁻ 7 (q490 c4) ∷
   rw 6 (q489 c4) ∷
   rw⁻ 5 (q76 c4) ∷
   rw⁻ 6 (q481 c4) ∷
   rw 4 (q366 c4) ∷
   rw⁻ 3 (q487 c4) ∷
   rw 4 (q491 c4) ∷
   rw⁻ 0 (q486 c4) ∷
   rw⁻ 1 (q492 c4) ∷ []) Eq.refl
