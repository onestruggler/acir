{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0197 ; wl0199 ; wl0220 ; wl0245 ; wl0247 ; wl0289 ; wl0621 ; wl0671 ; wl1133 ; wl1134 ; wl1135 ; wl1136 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0041 ; wp0046 ; wp0047 ; wp0048 ; wp0066 ; wp0081 ; wp0513 ; wp0669 ; wp0680 ; wp0780 ; wp0781 ; wp0782 ; wp0820 ; wp0911 ; wp0912 ; wp0913 ; wp0914 ; wp0915 ; wp0919 ; wp0920 ; wp0922 ; wp0923 ; wl0159 ; wl0171 ; wl0172 ; wl0173 ; wl0227 ; wl0228 ; wl0327 ; wl0651 ; wl0682 ; wl0683 ; wl0684 ; wl0763 ; wl0764 ; wl0765 ; wl0770 ; wl0905 ; wl1008 ; wl1149 ; wl1150 ; wl1151 ; wl1152 ; wl1153 ; wl1154 ; wl1156 ; wl1157 ; wl1158 ; wp0013 ; wp0079 ; wp0092 ; wp0314 ; wp0939 ; wp0940 ; wp0941 ; wp0942 ; wp0943 ; wp0944 ; wp0945 ; wp0946 ; wp0947 ; wp0948 ; wp0949 ; wp0950 ; wl0201 ; wl0202 ; wl0242 ; wl0295 ; wl0299 ; wl0324 ; wl0326 ; wl0423 ; wl0424 ; wl0448 ; wl0613 ; wl0617 ; wl0646 ; wl0648 ; wl0673 ; wl0675 ; wl0676 ; wl1164 ; wl1165 ; wl1166 ; wl1167 ; wl1168 ; wl1170 ; wl1171 ; wp0050 ; wp0091 ; wp0129 ; wp0132 ; wp0133 ; wp0134 ; wp0181 ; wp0185 ; wp0186 ; wp0191 ; wp0192 ; wp0281 ; wp0286 ; wp0312 ; wp0357 ; wp0548 ; wp0593 ; wp0734 ; wp0735 ; wp0736 ; wp0784 ; wp0786 ; wp0815 ; wp0827 ; wp0955 ; wp0956 ; wp0960 ; wp0961 ; wp0962 ; wp0963 ; wp0964 ; wp0967 ; wp0968 ; wp0969 ; wp0970 ; wp0971 ; wp0974 ; wp0975 ; wp0976 ; wp0977 ; wp0978 ; wl0225 ; wl0259 ; wl0261 ; wl0318 ; wl0321 ; wl0342 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0645 ; wl0667 ; wl0668 ; wl0672 ; wl0674 ; wl0698 ; wl0702 ; wl0704 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0848 ; wl0851 ; wl1020 ; wl1021 ; wl1022 ; wl1179 ; wl1180 ; wl1181 ; wl1183 ; wl1184 ; wl1185 ; wl1186 ; wl1189 ; wl1190 ; wp0077 ; wp0112 ; wp0113 ; wp0114 ; wp0213 ; wp0393 ; wp0394 ; wp0540 ; wp0655 ; wp0703 ; wp0814 ; wp0898 ; wp0989 ; wp0990 ; wp0997 ; wp0998 ; wp1003 ; wp1007 ; wl0155 ; wl0332 ; wl0341 ; wl0488 ; wl0501 ; wl0504 ; wl0505 ; wl0506 ; wl0779 ; wl0803 ; wl0804 ; wl0858 ; wl0862 ; wl1203 ; wl1204 ; wl1213 ; wl1214 ; wl1215 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1228 ; wl1229 ; wl1230 ; wp0001 ; wp0002 ; wp0003 ; wp0029 ; wp0124 ; wp0261 ; wp0272 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0572 ; wp0575 ; wp0576 ; wp0578 ; wp0702 ; wp1017 ; wp1018 ; wp1019 ; wp1020 ; wp1021 ; wp1027 ; wp1031 ; wp1033 ; wp1034 ; wl0298 ; wl0348 ; wl0391 ; wl0392 ; wl0393 ; wl0406 ; wl0508 ; wl0618 ; wl0694 ; wl0695 ; wl0774 ; wl1235 ; wl1236 ; wl1240 ; wl1241 ; wl1242 ; wl1244 ; wl1245 ; wl1246 ; wl1253 ; wl1254 ; wl1255 ; wl1256 ; wp0688 ; wp0692 ; wp0727 ; wp0728 ; wp0729 ; wp0730 ; wp1049 ; wp1050 ; wp1051 ; wp1052 ; wp1053 ; wp1054 ; wp1055 ; wp1056 ; wp1057 ; wp1058 ; wp1059 ; wp1060 ; wp1063 ; wp1064 ; wp1065 ; wp1066 ; wp1067 ; wl0214 ; wl0644 ; wl0679 ; wl1272 ; wl1273 ; wl1277 ; wl1278 ; wp0145 ; wp0299 ; wp0521 ; wp0738 ; wp1077 ; wp1078 ; wp1079 ; wp1080 ; wp1081 ; wp1082 ; wp1083 ; wp1094 ; wp1095 ; wp1096 ; wp1097 ; wp1098 ; wp1099 ; wp1100 ; wl0207 ; wl0312 ; wl0315 ; wl1233 ; wl1283 ; wl1284 ; wp0103 ; wp0301 ; wp0313 ; wp0580 ; wp1041 ; wp1113 ; wp1114 ; wp1115 ; wl0960 ; wl1100 ; wl1300 ; wl1304 ; wl1305 ; wl1306 ; wl1307 ; wl1308 ; wp0296 ; wp1126 ; wp1128 ; wp1129 ; wl0444 ; wl0445 ; wl0543 ; wl0703 ; wl1317 ; wl1318 ; wl1320 ; wl1321 ; wl1322 ; wp0378 ; wp0380 ; wp0761 ; wp1141 ; wp1142 ; wp1143 ; wp1144 ; wp1145 ; wp1150)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ ; lem-box-tQ-at0210233441 ; lem-box-tQ-at0310243142 ; lem-box-tQ-at0314203142 ; lem-box-tQ-at0314213042 ; lem-box-tQ-at033440 ; lem-box-tQ-at12213443 ; lem-box-tQ-at143143 ; lem-box-tQ-at1441 ; lem-box-tQ-at233442 ; lem-box-tQ-at2442 ; lem-box-tQ-at3443 ; lem-tP-at0310243142 ; lem-tP-at0314203142 ; lem-tP-at0314213042 ; lem-tP-at12213443 ; lem-tP-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CXbc-box-at0310213442 ; lem-CXbc-box-at14233241 ; lem-CXcb-box-at0310213442 ; lem-CXcb-box-at14233241 ; lem-box-tQ-at02102441 ; lem-box-tQ-at02142041 ; lem-box-tQ-at02233440 ; lem-box-tQ-at022440 ; lem-box-tQ-at0310243241 ; lem-box-tQ-at031031 ; lem-box-tQ-at03103441 ; lem-box-tQ-at0312203441 ; lem-box-tQ-at0312243041 ; lem-box-tQ-at0314213240 ; lem-box-tQ-at03143041 ; lem-box-tQ-at03143140 ; lem-box-tQ-at03243240 ; lem-tP-at02102441 ; lem-tP-at02233440 ; lem-tP-at0310243241 ; lem-tP-at031031 ; lem-tP-at03103441 ; lem-tP-at0312203441 ; lem-tP-at0312243041 ; lem-tP-at0314213240 ; lem-tP-at03143140 ; lem-tP-at03243240 ; lem-tP-at033440 ; lem-tP-at12243143 ; lem-tP-at1441 ; lem-tP-at2442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-TOFF024 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd13-TOFF024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-TOFF014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX02-CCZ134 ; lem-comm-CX04-CCZ123 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX21-CCZ034 ; lem-comm-CX24-CCZ013 ; lem-comm-CX42-CCZ013 ; lem-comm-CZ04-TOFF213 ; lem-comm-CZ04-TOFF312 ; lem-comm-CZ24-TOFF013 ; lem-comm-TOFF014-CSd23 ; lem-comm-TOFF024-CSd13 ; lem-comm-TOFF204-CSd13 ; lem-comm-TOFF312-CSd04)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS02-TOFF314 ; lem-comm-CS03-TOFF214 ; lem-comm-CS04-TOFF312 ; lem-comm-CS12-TOFF304 ; lem-comm-CS13-TOFF204 ; lem-comm-CS14-TOFF203 ; lem-comm-CS23-TOFF014 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CSd14-TOFF302 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX03-CCZ124 ; lem-comm-CX40-CCZ123 ; lem-comm-CX41-CCZ023 ; lem-comm-CZ02-TOFF314 ; lem-comm-CZ12-TOFF304 ; lem-comm-CZ13-TOFF024 ; lem-comm-CZ14-TOFF302 ; lem-comm-CZ24-TOFF301 ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF304-CSd12 ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS14-TOFF302 ; lem-comm-CX20-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF302-CSd14)

-- CXcb-box @022440: 18 steps
lem-CXcb-box-at022440 : Ws → ⟪ (CX34 ∷ Bx2-1430 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at022440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx2-1430 ∷ CX34 ∷ []) (Toff214 ∷ CCZ023 ∷ CX34 ∷ Toff213 ∷ CS03 ∷ CX13 ∷ Toff214 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ023 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) (lem-box-tQ-at022440 c4) ▸
       at 0 2 (Toff214 ∷ CX34 ∷ Toff213 ∷ []) (wl1133 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl1134 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 7 2 (Toff214 ∷ CX13 ∷ []) (wl1135 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸ done

  b1 : Chain (Toff214 ∷ CCZ023 ∷ CX34 ∷ Toff213 ∷ CS03 ∷ CX13 ∷ Toff214 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ023 ∷ CX34 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff214 ∷ CX13 ∷ []) (wl1135 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS03 ∷ []) (lem-comm-CS03-TOFF214 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (Toff214 ∷ Toff213 ∷ []) (wl0197 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CX34 ∷ Toff213 ∷ []) (wl1133 (lit c4)) ▸
       at 3 3 (CX34 ∷ []) (wl1136 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸ done

  b2 : Chain (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-1430 ∷ []) (sym (lem-box-tQ-at022440 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0913 c4)) ▸ done

-- P-box @02233440: 8 steps
lem-P-box-at02233440 : Ws → ⟪ (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-P-box-at02233440 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 0 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at02233440 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (sym (wp0780 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at02233440 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ04 ∷ []) (sym (wp0781 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0782 c4)) ▸
       at 0 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

-- VPQ @02233440: 14 steps
lem-VPQ-at02233440 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 3 2 (CS04⁻ ∷ S2⁻ ∷ []) (sym (wp0018 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S2 ∷ []) (sym (wp0017 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS13⁻ ∷ []) (sym (wp0016 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02233440 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS13⁻ ∷ []) (wl0178 (lit c4)) ▸
       at 2 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS13⁻ ∷ []) (wl0177 (lit c4)) ▸
       at 0 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸
       at 2 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸ done

-- P-box @1441: 8 steps
lem-P-box-at1441 : Ws → ⟪ (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-P-box-at1441 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at1441 c4) ▸
       at 0 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at1441 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (sym (wl0682 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at1441 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ13 ∷ []) (sym (wl0683 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF024 (lit c4)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0684 (lit c4))) ▸
       at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸ done

-- VPQ @1441: 14 steps
lem-VPQ-at1441 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 4 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 2 2 (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 2 (CS13⁻ ∷ CS24⁻ ∷ []) (sym (wl0228 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at1441 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS24⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS24⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸
       at 2 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸ done

-- CXbc-box @0210233441: 17 steps
lem-CXbc-box-at0210233441 : Ws → ⟪ (CX34 ∷ Bx2-0341 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0210233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx2-0341 ∷ CX34 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX34 ∷ CCZ123 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CCZ124 ∷ CX03 ∷ CS01 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4) ▸
       at 0 2 (Toff203 ∷ CX34 ∷ []) (wp0939 c4) ▸
       at 1 2 (CCZ124 ∷ CX34 ∷ CCZ123 ∷ []) (sym (wl1149 (lit c4))) ▸
       at 3 2 (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1150 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CX34 ∷ []) (wp0939 c4) ▸
       at 5 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 8 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX34 ∷ CCZ123 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CCZ124 ∷ CX03 ∷ CS01 ∷ CX34 ∷ []) (Bx2-0341 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ [])
  b1 = at 7 2 (CCZ124 ∷ CS13⁻ ∷ []) (sym (wl1151 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CS13 ∷ []) (sym (wl1152 (lit c4))) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ CX34 ∷ CCZ123 ∷ []) (sym (wl1149 (lit c4))) ▸
       at 4 3 (CX34 ∷ []) (wl1153 (lit c4)) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done

  b2 : Chain (Bx2-0341 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ []) (Bx2-0341 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wp0913 c4)) ▸ done

-- CXcb-box @0210233441: 18 steps
lem-CXcb-box-at0210233441 : Ws → ⟪ (CX43 ∷ Bx2-0341 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0210233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx2-0341 ∷ CX43 ∷ []) (Toff203 ∷ CCZ124 ∷ CX43 ∷ Toff204 ∷ CS14 ∷ CX04 ∷ Toff203 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ124 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4) ▸
       at 0 2 (Toff203 ∷ CX43 ∷ Toff204 ∷ []) (wp0940 c4) ▸
       at 2 2 (CCZ124 ∷ Toff204 ∷ CCZ014 ∷ []) (sym (wp0941 c4)) ▸
       at 1 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 8 2 (Toff203 ∷ CS01 ∷ []) (wl1154 (lit c4)) ▸
       at 7 2 (Toff203 ∷ CX04 ∷ []) (wp0942 c4) ▸
       at 6 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ CX43 ∷ Toff204 ∷ CS14 ∷ CX04 ∷ Toff203 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ124 ∷ CX43 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ [])
  b1 = at 5 2 (Toff203 ∷ CX04 ∷ []) (wp0942 c4) ▸
       at 4 2 (Toff203 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF203 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff203 ∷ Toff204 ∷ []) (sym (wp0943 c4)) ▸
       at 2 2 (Toff203 ∷ CX43 ∷ Toff204 ∷ []) (wp0940 c4) ▸
       at 3 3 (CX43 ∷ []) (wp0944 c4) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸ done

  b2 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ []) (Bx2-0341 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0915 c4)) ▸ done

-- VPQ @02102441: 14 steps
lem-VPQ-at02102441 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at02102441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 4 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (sym (wl0177 (lit c4))) ▸
       at 2 2 (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S2 ∷ []) (sym (wl0178 (lit c4))) ▸
       at 0 2 (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02102441 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS04⁻ ∷ []) (wp0017 c4) ▸
       at 2 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4) ▸
       at 0 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸
       at 2 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸ done

-- CXbc-box @02102441: 17 steps
lem-CXbc-box-at02102441 : Ws → ⟪ (CX43 ∷ Bx2-0431 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx2-0431 ∷ CX43 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX43 ∷ CCZ124 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4) ▸
       at 0 2 (Toff204 ∷ CX43 ∷ []) (wp0945 c4) ▸
       at 1 2 (CCZ123 ∷ CX43 ∷ CCZ124 ∷ []) (sym (wl1156 (lit c4))) ▸
       at 3 2 (Toff204 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0946 c4) ▸
       at 2 2 (Toff204 ∷ CX43 ∷ []) (wp0945 c4) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX43 ∷ CCZ124 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ CX43 ∷ []) (Bx2-0431 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS14⁻ ∷ []) (sym (wl0764 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ124 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX43 ∷ CCZ124 ∷ []) (sym (wl1156 (lit c4))) ▸
       at 4 3 (CX43 ∷ []) (wl1157 (lit c4)) ▸
       at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-tQ-at02102441 c4)) ▸ done

  b2 : Chain (Bx2-0431 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ []) (Bx2-0431 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0915 c4)) ▸ done

-- CXcb-box @02102441: 18 steps
lem-CXcb-box-at02102441 : Ws → ⟪ (CX34 ∷ Bx2-0431 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx2-0431 ∷ CX34 ∷ []) (Toff204 ∷ CCZ123 ∷ CX34 ∷ Toff203 ∷ CS13 ∷ CX03 ∷ Toff204 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ123 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4) ▸
       at 0 2 (Toff204 ∷ CX34 ∷ Toff203 ∷ []) (wp0947 c4) ▸
       at 2 2 (CCZ123 ∷ Toff203 ∷ CCZ013 ∷ []) (sym (wl1158 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX34 ∷ []) (sym (wl1008 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 7 2 (Toff204 ∷ CX03 ∷ []) (wp0949 c4) ▸
       at 6 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ CX34 ∷ Toff203 ∷ CS13 ∷ CX03 ∷ Toff204 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ123 ∷ CX34 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff204 ∷ CX03 ∷ []) (wp0949 c4) ▸
       at 4 2 (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff203 ∷ []) (wp0943 c4) ▸
       at 2 2 (Toff204 ∷ CX34 ∷ Toff203 ∷ []) (wp0947 c4) ▸
       at 3 3 (CX34 ∷ []) (wp0950 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ013 ∷ []) (wl0327 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX34 ∷ []) (sym (wl1008 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-tQ-at02102441 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0913 c4)) ▸ done

-- CXbc-box @233442: 17 steps
lem-CXbc-box-at233442 : Ws → ⟪ (CX34 ∷ Bx0-1342 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-1342 ∷ CX34 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX34 ∷ CCZ023 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 0 2 (Toff013 ∷ CX34 ∷ []) (wp0286 c4) ▸
       at 1 2 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (sym (wp0911 c4)) ▸
       at 3 2 (Toff013 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1164 (lit c4)) ▸
       at 2 2 (Toff013 ∷ CX34 ∷ []) (wp0286 c4) ▸
       at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CX34 ∷ CCZ023 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ CX34 ∷ []) (Bx0-1342 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4) ▸
       at 3 2 (CCZ024 ∷ CX34 ∷ CCZ023 ∷ []) (sym (wp0911 c4)) ▸
       at 4 3 (CX34 ∷ []) (wp0912 c4) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

  b2 : Chain (Bx0-1342 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-1342 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0648 (lit c4))) ▸ done

-- CXcb-box @233442: 18 steps
lem-CXcb-box-at233442 : Ws → ⟪ (CX43 ∷ Bx0-1342 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at233442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-1342 ∷ CX43 ∷ []) (Toff013 ∷ CCZ024 ∷ CX43 ∷ Toff014 ∷ CS24 ∷ CX14 ∷ Toff013 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ024 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 0 2 (Toff013 ∷ CX43 ∷ Toff014 ∷ []) (wp0955 c4) ▸
       at 2 2 (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (sym (wp0784 c4)) ▸
       at 1 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸
       at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CX14 ∷ []) (wp0281 c4) ▸
       at 6 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸ done

  b1 : Chain (Toff013 ∷ CCZ024 ∷ CX43 ∷ Toff014 ∷ CS24 ∷ CX14 ∷ Toff013 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ024 ∷ CX43 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 5 2 (Toff013 ∷ CX14 ∷ []) (wp0281 c4) ▸
       at 4 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff013 ∷ Toff014 ∷ []) (sym (wp0786 c4)) ▸
       at 2 2 (Toff013 ∷ CX43 ∷ Toff014 ∷ []) (wp0955 c4) ▸
       at 3 3 (CX43 ∷ []) (wp0956 c4) ▸
       at 4 2 (CCZ024 ∷ CCZ124 ∷ []) (sym (wp0827 c4)) ▸
       at 3 2 (CCZ024 ∷ CX43 ∷ []) (sym (wp0914 c4)) ▸ done

  b2 : Chain (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-1342 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0646 (lit c4))) ▸ done

-- VPQ @2442: 14 steps
lem-VPQ-at2442 : Ws → ⟪ (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ []) ⟫ʷ
lem-VPQ-at2442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ023 ∷ []) (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S0 ∷ Toff014 ∷ S0⁻ ∷ []) (sym (wp0050 c4)) ▸
       at 4 2 (CS23⁻ ∷ S0 ∷ Toff023 ∷ S0⁻ ∷ []) (sym (wl0201 (lit c4))) ▸
       at 3 2 (CS23⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) ((CS • CS • CS) ↑)) ▸
       at 2 2 (CS23⁻ ∷ Toff014 ∷ []) (lem-comm-TOFF014-CSd23 (lit c4)) ▸
       at 1 2 (CS23⁻ ∷ S0 ∷ []) (c₁ (S) ((CS • CS • CS) ↑)) ▸
       at 0 2 (CS23⁻ ∷ CS14⁻ ∷ []) (wl0202 (lit c4)) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff023 ∷ Toff014 ∷ []) (lem-tP-at2442 c4) ▸ done

  b1 : Chain (CS23⁻ ∷ CS14⁻ ∷ S0 ∷ Toff023 ∷ Toff014 ∷ S0⁻ ∷ []) (Toff023 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS14⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS14⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • (Swap ↑ • (CS • CS • CS) • Swap ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff023 ∷ CCZ023 ∷ []) (wl0201 (lit c4)) ▸
       at 2 4 (Toff014 ∷ CCZ014 ∷ []) (wp0050 c4) ▸ done

-- CXbc-box @2442: 17 steps
lem-CXbc-box-at2442 : Ws → ⟪ (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx0-1432 ∷ CX43 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX43 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at2442 c4) ▸
       at 0 2 (Toff014 ∷ CX43 ∷ []) (wp0960 c4) ▸
       at 1 2 (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (sym (wp0920 c4)) ▸
       at 3 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0815 c4) ▸
       at 2 2 (Toff014 ∷ CX43 ∷ []) (wp0960 c4) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX43 ∷ CCZ024 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CCZ023 ∷ CX14 ∷ CS12 ∷ CX43 ∷ []) (Bx0-1432 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 6 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 3 2 (CCZ023 ∷ CX43 ∷ CCZ024 ∷ []) (sym (wp0920 c4)) ▸
       at 4 3 (CX43 ∷ []) (wp0922 c4) ▸
       at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸ done

  b2 : Chain (Bx0-1432 ∷ CX43 ∷ CCZ124 ∷ CX43 ∷ []) (Bx0-1432 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wl0646 (lit c4))) ▸ done

-- CXcb-box @2442: 18 steps
lem-CXcb-box-at2442 : Ws → ⟪ (CX34 ∷ Bx0-1432 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXcb-box-at2442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx0-1432 ∷ CX34 ∷ []) (Toff014 ∷ CCZ023 ∷ CX34 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ Toff014 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ023 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at2442 c4) ▸
       at 0 2 (Toff014 ∷ CX34 ∷ Toff013 ∷ []) (wp0961 c4) ▸
       at 2 2 (CCZ023 ∷ Toff013 ∷ CCZ123 ∷ []) (sym (wl1165 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS12 ∷ []) (wp0962 c4) ▸
       at 7 2 (Toff014 ∷ CX13 ∷ []) (wp0963 c4) ▸
       at 6 2 (Toff014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF014 (lit c4)) ▸ done

  b1 : Chain (Toff014 ∷ CCZ023 ∷ CX34 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ Toff014 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ023 ∷ CX34 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff014 ∷ CX13 ∷ []) (wp0963 c4) ▸
       at 4 2 (Toff014 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (Toff014 ∷ Toff013 ∷ []) (wp0786 c4) ▸
       at 2 2 (Toff014 ∷ CX34 ∷ Toff013 ∷ []) (wp0961 c4) ▸
       at 3 3 (CX34 ∷ []) (wp0964 c4) ▸
       at 4 2 (CCZ023 ∷ CCZ123 ∷ []) (sym (wl0613 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CX34 ∷ []) (sym (wp0680 c4)) ▸ done

  b2 : Chain (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX34 ∷ CCZ123 ∷ CX34 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-1432 ∷ []) (sym (lem-box-tQ-at2442 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0648 (lit c4))) ▸ done

-- P-box @233442: 8 steps
lem-P-box-at233442 : Ws → ⟪ (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-P-box-at233442 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) (Bx0-1342 ∷ [])
  b0 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 0 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at233442 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ24 ∷ Toff024 ∷ []) (sym (wp0132 c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (sym (lem-tP-at233442 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ24 ∷ []) (sym (wp0133 c4)) ▸
       at 2 2 (Toff013 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF013 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0134 c4)) ▸
       at 0 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

-- CXbc-box @143143: 17 steps
lem-CXbc-box-at143143 : Ws → ⟪ (CX21 ∷ Bx0-4213 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at143143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx0-4213 ∷ CX21 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX21 ∷ CCZ023 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CCZ013 ∷ CX42 ∷ CS34 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4) ▸
       at 0 2 (Toff024 ∷ CX21 ∷ []) (wp0191 c4) ▸
       at 1 2 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (sym (wl1166 (lit c4))) ▸
       at 3 2 (Toff024 ∷ CCZ023 ∷ CCZ234 ∷ []) (wp0967 c4) ▸
       at 2 2 (Toff024 ∷ CX21 ∷ []) (wp0191 c4) ▸
       at 5 1 (CS23 ∷ CX42 ∷ CS23⁻ ∷ CX42 ∷ CS34 ∷ []) (wl0675 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 8 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CX21 ∷ CCZ023 ∷ CS23 ∷ CX42 ∷ CS23⁻ ∷ CCZ013 ∷ CX42 ∷ CS34 ∷ CX21 ∷ []) (Bx0-4213 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS23⁻ ∷ []) (sym (wl1167 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0675 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (sym (wl1166 (lit c4))) ▸
       at 4 3 (CX21 ∷ []) (wl1168 (lit c4)) ▸
       at 0 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸ done

  b2 : Chain (Bx0-4213 ∷ CX21 ∷ CCZ234 ∷ CX21 ∷ []) (Bx0-4213 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (sym (wl0676 (lit c4))) ▸ done

-- CXcb-box @143143: 18 steps
lem-CXcb-box-at143143 : Ws → ⟪ (CX12 ∷ Bx0-4213 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at143143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx0-4213 ∷ CX12 ∷ []) (Toff024 ∷ CCZ013 ∷ CX12 ∷ Toff014 ∷ CS13 ∷ CX41 ∷ Toff024 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ013 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4) ▸
       at 0 2 (Toff024 ∷ CX12 ∷ Toff014 ∷ []) (wp0968 c4) ▸
       at 2 2 (CCZ013 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp0969 c4)) ▸
       at 1 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl0617 (lit c4)) ▸
       at 8 2 (Toff024 ∷ CS34 ∷ []) (wp0970 c4) ▸
       at 7 2 (Toff024 ∷ CX41 ∷ []) (wp0181 c4) ▸
       at 6 2 (Toff024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF024 (lit c4)) ▸ done

  b1 : Chain (Toff024 ∷ CCZ013 ∷ CX12 ∷ Toff014 ∷ CS13 ∷ CX41 ∷ Toff024 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ CCZ013 ∷ CX12 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff024 ∷ CX41 ∷ []) (wp0181 c4) ▸
       at 4 2 (Toff024 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF024 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0617 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff014 ∷ []) (wp0548 c4) ▸
       at 2 2 (Toff024 ∷ CX12 ∷ Toff014 ∷ []) (wp0968 c4) ▸
       at 3 3 (CX12 ∷ []) (wp0971 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ134 ∷ []) (sym (wp0593 c4)) ▸
       at 3 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸ done

  b2 : Chain (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ CX12 ∷ CCZ134 ∷ CX12 ∷ []) (Bx0-4213 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-4213 ∷ []) (sym (lem-box-tQ-at143143 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0673 (lit c4))) ▸ done

-- CXbc-box @12213443: 17 steps
lem-CXbc-box-at12213443 : Ws → ⟪ (CX14 ∷ Bx0-2143 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at12213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx0-2143 ∷ CX14 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX14 ∷ CCZ013 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CCZ034 ∷ CX21 ∷ CS23 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4) ▸
       at 0 2 (Toff012 ∷ CX14 ∷ []) (wp0974 c4) ▸
       at 1 2 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (sym (wp0735 c4)) ▸
       at 3 2 (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1170 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CX14 ∷ []) (wp0974 c4) ▸
       at 5 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX14 ∷ CCZ013 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CCZ034 ∷ CX21 ∷ CS23 ∷ CX14 ∷ []) (Bx0-2143 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ013 ∷ []) (wp0186 c4) ▸
       at 3 2 (CCZ034 ∷ CX14 ∷ CCZ013 ∷ []) (sym (wp0735 c4)) ▸
       at 4 3 (CX14 ∷ []) (wp0736 c4) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done

  b2 : Chain (Bx0-2143 ∷ CX14 ∷ CCZ123 ∷ CX14 ∷ []) (Bx0-2143 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0299 (lit c4))) ▸ done

-- CXcb-box @12213443: 18 steps
lem-CXcb-box-at12213443 : Ws → ⟪ (CX41 ∷ Bx0-2143 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXcb-box-at12213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx0-2143 ∷ CX41 ∷ []) (Toff012 ∷ CCZ034 ∷ CX41 ∷ Toff024 ∷ CS34 ∷ CX24 ∷ Toff012 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ034 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4) ▸
       at 0 2 (Toff012 ∷ CX41 ∷ Toff024 ∷ []) (wp0975 c4) ▸
       at 2 2 (CCZ034 ∷ Toff024 ∷ CCZ234 ∷ []) (sym (wp0976 c4)) ▸
       at 1 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 8 2 (Toff012 ∷ CS23 ∷ []) (wl1171 (lit c4)) ▸
       at 7 2 (Toff012 ∷ CX24 ∷ []) (wp0977 c4) ▸
       at 6 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX41 ∷ Toff024 ∷ CS34 ∷ CX24 ∷ Toff012 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ CCZ034 ∷ CX41 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff012 ∷ CX24 ∷ []) (wp0977 c4) ▸
       at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 3 2 (Toff012 ∷ Toff024 ∷ []) (sym (wp0192 c4)) ▸
       at 2 2 (Toff012 ∷ CX41 ∷ Toff024 ∷ []) (wp0975 c4) ▸
       at 3 3 (CX41 ∷ []) (wp0978 c4) ▸
       at 4 2 (CCZ034 ∷ CCZ234 ∷ []) (sym (wp0129 c4)) ▸
       at 3 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX41 ∷ CCZ234 ∷ CX41 ∷ []) (Bx0-2143 ∷ CCZ234 ∷ [])
  b2 = at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸
       at 1 3 (CCZ234 ∷ []) (sym (wl0295 (lit c4))) ▸ done

-- VPQ @12243143: 14 steps
lem-VPQ-at12243143 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at12243143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 4 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 2 2 (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 2 (CS13⁻ ∷ CS24⁻ ∷ []) (sym (wl0228 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at12243143 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS24⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS24⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸
       at 2 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸ done

-- P-box @12213443: 8 steps
lem-P-box-at12213443 : Ws → ⟪ (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-P-box-at12213443 c4 = run b0
  where
  b0 : Chain (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) (Bx0-2143 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4) ▸
       at 0 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at12213443 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ34 ∷ Toff034 ∷ []) (sym (wp0112 c4)) ▸
       at 3 2 (Toff012 ∷ Toff034 ∷ []) (sym (lem-tP-at12213443 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ34 ∷ []) (sym (wp0113 c4)) ▸
       at 2 2 (Toff012 ∷ CZ34 ∷ []) (sym (c₃ (Toff) (CZ))) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0114 c4)) ▸
       at 0 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done

-- SWbc-box @14233241: 11 steps
lem-SWbc-box-at14233241 : Ws → ⟪ (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-SWbc-box-at14233241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw23 ∷ Bx0-4321 ∷ Sw23 ∷ []) (CX32 ∷ Bx0-4321 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 4 1 (CX32 ∷ CX23 ∷ CX32 ∷ []) (sym (wl1020 (lit c4))) ▸
       at 2 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14233241 c4) ▸
       at 3 2 (CX23 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl0261 (lit c4)) ▸
       at 1 3 (Bx0-4321 ∷ CCZ124 ∷ []) (lem-CXcb-box-at14233241 c4) ▸
       at 4 2 (CX32 ∷ CCZ134 ∷ []) (wl1021 (lit c4)) ▸
       at 3 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸
       at 2 2 (CX32 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl0259 (lit c4)) ▸ done

  b1 : Chain (CX32 ∷ Bx0-4321 ∷ CX32 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ CCZ124 ∷ CCZ134 ∷ []) (Bx0-4321 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wl1022 (lit c4)) ▸
       at 0 3 (Bx0-4321 ∷ CCZ134 ∷ []) (lem-CXbc-box-at14233241 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done

-- CXbc-box @03143140: 17 steps
lem-CXbc-box-at03143140 : Ws → ⟪ (CX21 ∷ Bx3-4210 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx3-4210 ∷ CX21 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX21 ∷ CCZ023 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CCZ013 ∷ CX42 ∷ CS04 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4) ▸
       at 0 2 (Toff324 ∷ CX21 ∷ []) (wl0851 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (sym (wl1166 (lit c4))) ▸
       at 3 2 (Toff324 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp0989 c4) ▸
       at 2 2 (Toff324 ∷ CX21 ∷ []) (wl0851 (lit c4)) ▸
       at 5 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 9 2 (CCZ013 ∷ CS04 ∷ []) (sym (wp0077 c4)) ▸
       at 8 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX21 ∷ CCZ023 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CCZ013 ∷ CX42 ∷ CS04 ∷ CX21 ∷ []) (Bx3-4210 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS02⁻ ∷ []) (sym (wl0342 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS02 ∷ []) (sym (wl0225 (lit c4))) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 4 2 (CCZ013 ∷ CCZ023 ∷ []) (sym (wl0671 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX21 ∷ CCZ023 ∷ []) (sym (wl1166 (lit c4))) ▸
       at 4 3 (CX21 ∷ []) (wl1168 (lit c4)) ▸
       at 0 4 (Bx3-4210 ∷ []) (sym (lem-box-tQ-at03143140 c4)) ▸ done

  b2 : Chain (Bx3-4210 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ []) (Bx3-4210 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0898 c4)) ▸ done

-- CXcb-box @03143140: 18 steps
lem-CXcb-box-at03143140 : Ws → ⟪ (CX12 ∷ Bx3-4210 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx3-4210 ∷ CX12 ∷ []) (Toff324 ∷ CCZ013 ∷ CX12 ∷ Toff314 ∷ CS01 ∷ CX41 ∷ Toff324 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ CCZ013 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4) ▸
       at 0 2 (Toff324 ∷ CX12 ∷ Toff314 ∷ []) (wl1179 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0990 c4)) ▸
       at 1 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 8 2 (Toff324 ∷ CS04 ∷ []) (wp0393 c4) ▸
       at 7 2 (Toff324 ∷ CX41 ∷ []) (wl0848 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ CX12 ∷ Toff314 ∷ CS01 ∷ CX41 ∷ Toff324 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ CCZ013 ∷ CX12 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff324 ∷ CX41 ∷ []) (wl0848 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸
       at 3 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 2 2 (Toff324 ∷ CX12 ∷ Toff314 ∷ []) (wl1179 (lit c4)) ▸
       at 3 3 (CX12 ∷ []) (wl1181 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 3 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸ done

  b2 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ []) (Bx3-4210 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-4210 ∷ []) (sym (lem-box-tQ-at03143140 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸ done

-- VPQ @0314213240: 14 steps
lem-VPQ-at0314213240 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at0314213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 4 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 3 2 (CS02⁻ ∷ S3⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))) ▸
       at 2 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ S3 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))) ▸
       at 0 2 (CS02⁻ ∷ CS14⁻ ∷ []) (sym (wp0703 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at0314213240 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS14⁻ ∷ []) (wl0785 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS14⁻ ∷ []) (wl0786 (lit c4)) ▸
       at 0 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸
       at 2 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸ done

-- CXbc-box @0314213240: 17 steps
lem-CXbc-box-at0314213240 : Ws → ⟪ (CX12 ∷ Bx3-4120 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0314213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx3-4120 ∷ CX12 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX12 ∷ CCZ013 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CCZ023 ∷ CX41 ∷ CS04 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213240 c4) ▸
       at 0 2 (Toff314 ∷ CX12 ∷ []) (wl1183 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 3 2 (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0997 c4) ▸
       at 2 2 (Toff314 ∷ CX12 ∷ []) (wl1183 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX41 ∷ CS01⁻ ∷ CX41 ∷ CS04 ∷ []) (wp0540 c4) ▸
       at 9 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 8 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX12 ∷ CCZ013 ∷ CS01 ∷ CX41 ∷ CS01⁻ ∷ CCZ023 ∷ CX41 ∷ CS04 ∷ CX12 ∷ []) (Bx3-4120 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS01⁻ ∷ []) (sym (wl0667 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CX41 ∷ []) (lem-comm-CX41-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0540 c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX12 ∷ CCZ013 ∷ []) (sym (wl0668 (lit c4))) ▸
       at 4 3 (CX12 ∷ []) (wl0672 (lit c4)) ▸
       at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-tQ-at0314213240 c4)) ▸ done

  b2 : Chain (Bx3-4120 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ []) (Bx3-4120 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸ done

-- CXcb-box @0314213240: 18 steps
lem-CXcb-box-at0314213240 : Ws → ⟪ (CX21 ∷ Bx3-4120 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0314213240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx3-4120 ∷ CX21 ∷ []) (Toff314 ∷ CCZ023 ∷ CX21 ∷ Toff324 ∷ CS02 ∷ CX42 ∷ Toff314 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ CCZ023 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213240 c4) ▸
       at 0 2 (Toff314 ∷ CX21 ∷ Toff324 ∷ []) (wl1184 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 1 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 4 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 8 2 (Toff314 ∷ CS04 ∷ []) (wp0998 c4) ▸
       at 7 2 (Toff314 ∷ CX42 ∷ []) (wl1185 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ CX21 ∷ Toff324 ∷ CS02 ∷ CX42 ∷ Toff314 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ CCZ023 ∷ CX21 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff314 ∷ CX42 ∷ []) (wl1185 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 3 2 (Toff314 ∷ Toff324 ∷ []) (sym (wl1180 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CX21 ∷ Toff324 ∷ []) (wl1184 (lit c4)) ▸
       at 3 3 (CX21 ∷ []) (wl1186 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 3 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸ done

  b2 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ []) (Bx3-4120 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-tQ-at0314213240 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0898 c4)) ▸ done

-- VPQ @03143140: 14 steps
lem-VPQ-at03143140 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S3⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 1 2 (CS01⁻ ∷ S3 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS24⁻ ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143140 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS24⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS24⁻ ∷ []) (wl0439 (lit c4)) ▸
       at 0 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸
       at 2 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸ done

-- t-cP @03143140: 5 steps
lem-t-cP-at03143140 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-t-cP-at03143140 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff324 ∷ [])
  b0 = at 0 2 (CCZ234 ∷ Toff324 ∷ CZ24 ∷ []) (sym (wl1203 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4)) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143140 c4) ▸
       at 2 3 (CCZ234 ∷ Toff324 ∷ []) (sym (wl1204 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143140 c4) ▸ done

-- VPQ @03243240: 14 steps
lem-VPQ-at03243240 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ
lem-VPQ-at03243240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 4 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 3 2 (CS02⁻ ∷ S3⁻ ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S))) ▸
       at 2 2 (CS02⁻ ∷ Toff314 ∷ []) (lem-comm-TOFF314-CSd02 (lit c4)) ▸
       at 1 2 (CS02⁻ ∷ S3 ∷ []) (sym (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S))) ▸
       at 0 2 (CS02⁻ ∷ CS14⁻ ∷ []) (sym (wp0703 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243240 c4) ▸ done

  b1 : Chain (CS02⁻ ∷ CS14⁻ ∷ S3 ∷ Toff302 ∷ Toff314 ∷ S3⁻ ∷ []) (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS14⁻ ∷ []) (wl0785 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS14⁻ ∷ []) (wl0786 (lit c4)) ▸
       at 0 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸
       at 2 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸ done

-- P-box @0314203142: 8 steps
lem-P-box-at0314203142 : Ws → ⟪ (Toff312 ∷ Bx3-4012 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-P-box-at0314203142 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx3-4012 ∷ Toff312 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 0 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0314203142 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (sym (wl0504 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0314203142 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ12 ∷ []) (sym (wl0505 (lit c4))) ▸
       at 2 2 (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0506 (lit c4))) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done

-- CXbc-box @033440: 17 steps
lem-CXbc-box-at033440 : Ws → ⟪ (CX24 ∷ Bx3-1240 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at033440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx3-1240 ∷ CX24 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX24 ∷ CCZ023 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CCZ034 ∷ CX12 ∷ CS01 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 0 2 (Toff312 ∷ CX24 ∷ []) (wl0862 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (sym (wp1017 c4)) ▸
       at 3 2 (Toff312 ∷ CCZ023 ∷ CCZ012 ∷ []) (wl1213 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CX24 ∷ []) (wl0862 (lit c4)) ▸
       at 5 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX24 ∷ CCZ023 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CCZ034 ∷ CX12 ∷ CS01 ∷ CX24 ∷ []) (Bx3-1240 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 3 2 (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (sym (wp1017 c4)) ▸
       at 4 3 (CX24 ∷ []) (wp1018 c4) ▸
       at 0 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸ done

  b2 : Chain (Bx3-1240 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ []) (Bx3-1240 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸ done

-- CXcb-box @033440: 18 steps
lem-CXcb-box-at033440 : Ws → ⟪ (CX42 ∷ Bx3-1240 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at033440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx3-1240 ∷ CX42 ∷ []) (Toff312 ∷ CCZ034 ∷ CX42 ∷ Toff314 ∷ CS04 ∷ CX14 ∷ Toff312 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ CCZ034 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 0 2 (Toff312 ∷ CX42 ∷ Toff314 ∷ []) (wl1214 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 1 2 (CCZ034 ∷ CX42 ∷ []) (sym (wp1020 c4)) ▸
       at 4 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX14 ∷ []) (wl0858 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ CX42 ∷ Toff314 ∷ CS04 ∷ CX14 ∷ Toff312 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ CCZ034 ∷ CX42 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ [])
  b1 = at 5 2 (Toff312 ∷ CX14 ∷ []) (wl0858 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸
       at 3 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 2 2 (Toff312 ∷ CX42 ∷ Toff314 ∷ []) (wl1214 (lit c4)) ▸
       at 3 3 (CX42 ∷ []) (wl1215 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4) ▸
       at 3 2 (CCZ034 ∷ CX42 ∷ []) (sym (wp1020 c4)) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ []) (Bx3-1240 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp1021 c4)) ▸ done

-- t-cP @03243240: 5 steps
lem-t-cP-at03243240 : Ws → ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-t-cP-at03243240 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 2 (CCZ134 ∷ Toff314 ∷ CZ14 ∷ []) (sym (wl0803 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4)) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243240 c4) ▸
       at 2 3 (CCZ134 ∷ Toff314 ∷ []) (sym (wl0804 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243240 c4) ▸ done

-- CXbc-box @03243240: 17 steps
lem-CXbc-box-at03243240 : Ws → ⟪ (CX42 ∷ Bx3-1420 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at03243240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx3-1420 ∷ CX42 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX42 ∷ CCZ034 ∷ CS04 ∷ CX14 ∷ CS04⁻ ∷ CCZ023 ∷ CX14 ∷ CS01 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 0 2 (Toff314 ∷ CX42 ∷ []) (wl1185 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (sym (wp0572 c4)) ▸
       at 3 2 (Toff314 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1031 c4) ▸
       at 2 2 (Toff314 ∷ CX42 ∷ []) (wl1185 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX14 ∷ CS04⁻ ∷ CX14 ∷ CS01 ∷ []) (wp0046 c4) ▸
       at 9 2 (CCZ023 ∷ CS01 ∷ []) (sym (wl0199 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CX42 ∷ CCZ034 ∷ CS04 ∷ CX14 ∷ CS04⁻ ∷ CCZ023 ∷ CX14 ∷ CS01 ∷ CX42 ∷ []) (Bx3-1420 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ [])
  b1 = at 7 2 (CCZ023 ∷ CS04⁻ ∷ []) (sym (wp0047 c4)) ▸
       at 6 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0046 c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ034 ∷ []) (sym (wp0575 c4)) ▸
       at 3 2 (CCZ023 ∷ CX42 ∷ CCZ034 ∷ []) (sym (wp0572 c4)) ▸
       at 4 3 (CX42 ∷ []) (wp0576 c4) ▸
       at 0 4 (Bx3-1420 ∷ []) (sym (lem-box-tQ-at03243240 c4)) ▸ done

  b2 : Chain (Bx3-1420 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ []) (Bx3-1420 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp1021 c4)) ▸ done

-- CXcb-box @03243240: 18 steps
lem-CXcb-box-at03243240 : Ws → ⟪ (CX24 ∷ Bx3-1420 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at03243240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx3-1420 ∷ CX24 ∷ []) (Toff314 ∷ CCZ023 ∷ CX24 ∷ Toff312 ∷ CS02 ∷ CX12 ∷ Toff314 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ023 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 0 2 (Toff314 ∷ CX24 ∷ Toff312 ∷ []) (wl1228 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff312 ∷ CCZ012 ∷ []) (sym (wl1229 (lit c4))) ▸
       at 1 2 (CCZ023 ∷ CX24 ∷ []) (sym (wp0578 c4)) ▸
       at 4 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 7 2 (Toff314 ∷ CX12 ∷ []) (wl1183 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ CX24 ∷ Toff312 ∷ CS02 ∷ CX12 ∷ Toff314 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ023 ∷ CX24 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ [])
  b1 = at 5 2 (Toff314 ∷ CX12 ∷ []) (wl1183 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CS02 ∷ []) (lem-comm-CS02-TOFF314 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 2 2 (Toff314 ∷ CX24 ∷ Toff312 ∷ []) (wl1228 (lit c4)) ▸
       at 3 3 (CX24 ∷ []) (wl1230 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4)) ▸
       at 3 2 (CCZ023 ∷ CX24 ∷ []) (sym (wp0578 c4)) ▸ done

  b2 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-1420 ∷ []) (sym (lem-box-tQ-at03243240 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸ done

-- VPQ @033440: 14 steps
lem-VPQ-at033440 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 3 2 (CS04⁻ ∷ S3⁻ ∷ []) (sym (wp0348 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff312 ∷ []) (lem-comm-TOFF312-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S3 ∷ []) (sym (wp0349 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS12⁻ ∷ []) (sym (wp0350 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S)) ▸
       at 2 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S • S • S)) ▸
       at 0 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸
       at 2 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸ done

-- P-box @033440: 8 steps
lem-P-box-at033440 : Ws → ⟪ (Toff304 ∷ Bx3-1240 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-P-box-at033440 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx3-1240 ∷ Toff304 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 0 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at033440 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (sym (wp0344 c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at033440 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ04 ∷ []) (sym (wp0345 c4)) ▸
       at 2 2 (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4)) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0346 c4)) ▸
       at 0 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸ done

-- t-cP @0310243142: 5 steps
lem-t-cP-at0310243142 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-t-cP-at0310243142 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 2 (CCZ034 ∷ Toff304 ∷ CZ04 ∷ []) (sym (wp1033 c4)) ▸
       at 2 2 (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4)) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4) ▸
       at 2 3 (CCZ034 ∷ Toff304 ∷ []) (sym (wp1034 c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243142 c4) ▸ done

-- P-box @0314213042: 8 steps
lem-P-box-at0314213042 : Ws → ⟪ (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-P-box-at0314213042 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) (Bx3-4102 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4) ▸
       at 0 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at0314213042 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (sym (wl1235 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at0314213042 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl1236 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 0 4 (Bx3-4102 ∷ []) (sym (lem-box-tQ-at0314213042 c4)) ▸ done

-- CXbc-box @03103441: 17 steps
lem-CXbc-box-at03103441 : Ws → ⟪ (CX24 ∷ Bx3-0241 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at03103441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx3-0241 ∷ CX24 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX24 ∷ CCZ123 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4) ▸
       at 0 2 (Toff302 ∷ CX24 ∷ []) (wp1049 c4) ▸
       at 1 2 (CCZ134 ∷ CX24 ∷ CCZ123 ∷ []) (sym (wl1240 (lit c4))) ▸
       at 3 2 (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1241 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CX24 ∷ []) (wp1049 c4) ▸
       at 5 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 8 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX24 ∷ CCZ123 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CCZ134 ∷ CX02 ∷ CS01 ∷ CX24 ∷ []) (Bx3-0241 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS12⁻ ∷ []) (sym (wl0392 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS12 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ CX24 ∷ CCZ123 ∷ []) (sym (wl1240 (lit c4))) ▸
       at 4 3 (CX24 ∷ []) (wl1242 (lit c4)) ▸
       at 0 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸ done

  b2 : Chain (Bx3-0241 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ []) (Bx3-0241 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸ done

-- CXcb-box @03103441: 18 steps
lem-CXcb-box-at03103441 : Ws → ⟪ (CX42 ∷ Bx3-0241 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03103441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx3-0241 ∷ CX42 ∷ []) (Toff302 ∷ CCZ134 ∷ CX42 ∷ Toff304 ∷ CS14 ∷ CX04 ∷ Toff302 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4) ▸
       at 0 2 (Toff302 ∷ CX42 ∷ Toff304 ∷ []) (wp1050 c4) ▸
       at 2 2 (CCZ134 ∷ Toff304 ∷ CCZ014 ∷ []) (sym (wp1051 c4)) ▸
       at 1 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 8 2 (Toff302 ∷ CS01 ∷ []) (wl1223 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CX04 ∷ []) (wp1052 c4) ▸
       at 6 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ CX42 ∷ Toff304 ∷ CS14 ∷ CX04 ∷ Toff302 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ CX42 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ [])
  b1 = at 5 2 (Toff302 ∷ CX04 ∷ []) (wp1052 c4) ▸
       at 4 2 (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff302 ∷ Toff304 ∷ []) (sym (wp1053 c4)) ▸
       at 2 2 (Toff302 ∷ CX42 ∷ Toff304 ∷ []) (wp1050 c4) ▸
       at 3 3 (CX42 ∷ []) (wp1054 c4) ▸
       at 4 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 3 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸ done

  b2 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ []) (Bx3-0241 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp1021 c4)) ▸ done

-- VPQ @0310243241: 14 steps
lem-VPQ-at0310243241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0310243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 4 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S3⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S • S • S))) ▸
       at 2 2 (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S3 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S))) ▸
       at 0 2 (CS12⁻ ∷ CS04⁻ ∷ []) (wp0350 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0310243241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS04⁻ ∷ []) (wp0349 c4) ▸
       at 2 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS04⁻ ∷ []) (wp0348 c4) ▸
       at 0 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸
       at 2 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸ done

-- CXbc-box @0310243241: 17 steps
lem-CXbc-box-at0310243241 : Ws → ⟪ (CX42 ∷ Bx3-0421 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx3-0421 ∷ CX42 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX42 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4) ▸
       at 0 2 (Toff304 ∷ CX42 ∷ []) (wp1055 c4) ▸
       at 1 2 (CCZ123 ∷ CX42 ∷ CCZ134 ∷ []) (sym (wl1244 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp1056 c4) ▸
       at 2 2 (Toff304 ∷ CX42 ∷ []) (wp1055 c4) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX42 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ CX42 ∷ []) (Bx3-0421 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS14⁻ ∷ []) (sym (wl0764 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ134 ∷ []) (sym (wl0618 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX42 ∷ CCZ134 ∷ []) (sym (wl1244 (lit c4))) ▸
       at 4 3 (CX42 ∷ []) (wl1245 (lit c4)) ▸
       at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-tQ-at0310243241 c4)) ▸ done

  b2 : Chain (Bx3-0421 ∷ CX42 ∷ CCZ014 ∷ CX42 ∷ []) (Bx3-0421 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp1021 c4)) ▸ done

-- CXcb-box @0310243241: 18 steps
lem-CXcb-box-at0310243241 : Ws → ⟪ (CX24 ∷ Bx3-0421 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx3-0421 ∷ CX24 ∷ []) (Toff304 ∷ CCZ123 ∷ CX24 ∷ Toff302 ∷ CS12 ∷ CX02 ∷ Toff304 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CCZ123 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4) ▸
       at 0 2 (Toff304 ∷ CX24 ∷ Toff302 ∷ []) (wp1057 c4) ▸
       at 2 2 (CCZ123 ∷ Toff302 ∷ CCZ012 ∷ []) (sym (wl1246 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX24 ∷ []) (sym (wl0406 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 8 2 (Toff304 ∷ CS01 ∷ []) (wp1058 c4) ▸
       at 7 2 (Toff304 ∷ CX02 ∷ []) (wp1059 c4) ▸
       at 6 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ CX24 ∷ Toff302 ∷ CS12 ∷ CX02 ∷ Toff304 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CCZ123 ∷ CX24 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ [])
  b1 = at 5 2 (Toff304 ∷ CX02 ∷ []) (wp1059 c4) ▸
       at 4 2 (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff302 ∷ []) (wp1053 c4) ▸
       at 2 2 (Toff304 ∷ CX24 ∷ Toff302 ∷ []) (wp1057 c4) ▸
       at 3 3 (CX24 ∷ []) (wp1060 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX24 ∷ []) (sym (wl0406 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-tQ-at0310243241 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸ done

-- P-box @03103441: 8 steps
lem-P-box-at03103441 : Ws → ⟪ (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-P-box-at03103441 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4) ▸
       at 0 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at03103441 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (sym (wl1253 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at03103441 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ14 ∷ []) (sym (wl1254 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1255 (lit c4))) ▸
       at 0 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸ done

-- VPQ @03103441: 14 steps
lem-VPQ-at03103441 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at03103441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S3⁻ ∷ []) (sym (wl0786 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S3 ∷ []) (sym (wl0785 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03103441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S)) ▸
       at 2 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S)) ▸
       at 0 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸
       at 2 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸ done

-- CXbc-box @0310243142: 17 steps
lem-CXbc-box-at0310243142 : Ws → ⟪ (CX41 ∷ Bx3-0412 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx3-0412 ∷ CX41 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX41 ∷ CCZ234 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CCZ123 ∷ CX04 ∷ CS02 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 0 2 (Toff304 ∷ CX41 ∷ []) (wp0692 c4) ▸
       at 1 2 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (sym (wl0694 (lit c4))) ▸
       at 3 2 (Toff304 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp1063 c4) ▸
       at 2 2 (Toff304 ∷ CX41 ∷ []) (wp0692 c4) ▸
       at 5 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 9 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CX41 ∷ CCZ234 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CCZ123 ∷ CX04 ∷ CS02 ∷ CX41 ∷ []) (Bx3-0412 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS24⁻ ∷ []) (sym (wl0172 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ234 ∷ []) (sym (wl0508 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX41 ∷ CCZ234 ∷ []) (sym (wl0694 (lit c4))) ▸
       at 4 3 (CX41 ∷ []) (wl0695 (lit c4)) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸ done

  b2 : Chain (Bx3-0412 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ []) (Bx3-0412 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0727 c4)) ▸ done

-- CXcb-box @0310243142: 18 steps
lem-CXcb-box-at0310243142 : Ws → ⟪ (CX14 ∷ Bx3-0412 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx3-0412 ∷ CX14 ∷ []) (Toff304 ∷ CCZ123 ∷ CX14 ∷ Toff301 ∷ CS12 ∷ CX01 ∷ Toff304 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ123 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 0 2 (Toff304 ∷ CX14 ∷ Toff301 ∷ []) (wp1064 c4) ▸
       at 2 2 (CCZ123 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1256 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX14 ∷ []) (sym (wl0424 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (Toff304 ∷ CS02 ∷ []) (wp1065 c4) ▸
       at 7 2 (Toff304 ∷ CX01 ∷ []) (wp0688 c4) ▸
       at 6 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ CX14 ∷ Toff301 ∷ CS12 ∷ CX01 ∷ Toff304 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ123 ∷ CX14 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff304 ∷ CX01 ∷ []) (wp0688 c4) ▸
       at 4 2 (Toff304 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF304 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff301 ∷ []) (wp1066 c4) ▸
       at 2 2 (Toff304 ∷ CX14 ∷ Toff301 ∷ []) (wp1064 c4) ▸
       at 3 3 (CX14 ∷ []) (wp1067 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX14 ∷ []) (sym (wl0424 (lit c4))) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-tQ-at0310243142 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸ done

-- SWbc-box @0310213442: 11 steps
lem-SWbc-box-at0310213442 : Ws → ⟪ (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-SWbc-box-at0310213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (CX14 ∷ Bx3-0142 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0310213442 c4) ▸
       at 3 2 (CX41 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp0730 c4) ▸
       at 1 3 (Bx3-0142 ∷ CCZ024 ∷ []) (lem-CXcb-box-at0310213442 c4) ▸
       at 4 2 (CX14 ∷ CCZ012 ∷ []) (wp0145 c4) ▸
       at 3 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸
       at 2 2 (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp0729 c4) ▸ done

  b1 : Chain (CX14 ∷ Bx3-0142 ∷ CX14 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ CCZ024 ∷ CCZ012 ∷ []) (Bx3-0142 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp0738 c4) ▸
       at 0 3 (Bx3-0142 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0310213442 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done

-- P-box @0314213240: 8 steps
lem-P-box-at0314213240 : Ws → ⟪ (Toff302 ∷ Bx3-4120 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-P-box-at0314213240 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx3-4120 ∷ Toff302 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213240 c4) ▸
       at 0 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at0314213240 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (sym (wl1235 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at0314213240 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl1236 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-tQ-at0314213240 c4)) ▸ done

-- CXbc-box @0312203441: 17 steps
lem-CXbc-box-at0312203441 : Ws → ⟪ (CX04 ∷ Bx3-2041 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0312203441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX04 ∷ Bx3-2041 ∷ CX04 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX04 ∷ CCZ013 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CCZ134 ∷ CX20 ∷ CS12 ∷ CX04 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at0312203441 c4) ▸
       at 0 2 (Toff302 ∷ CX04 ∷ []) (wp1052 c4) ▸
       at 1 2 (CCZ134 ∷ CX04 ∷ CCZ013 ∷ []) (sym (wp1077 c4)) ▸
       at 3 2 (Toff302 ∷ CCZ013 ∷ CCZ012 ∷ []) (wl1272 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CX04 ∷ []) (wp1052 c4) ▸
       at 5 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ CS12 ∷ []) (sym (wl0393 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX04 ∷ CCZ013 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CCZ134 ∷ CX20 ∷ CS12 ∷ CX04 ∷ []) (Bx3-2041 ∷ CX04 ∷ CCZ012 ∷ CX04 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS01⁻ ∷ []) (sym (wp1027 c4)) ▸
       at 6 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CCZ013 ∷ []) (wp0593 c4) ▸
       at 3 2 (CCZ134 ∷ CX04 ∷ CCZ013 ∷ []) (sym (wp1077 c4)) ▸
       at 4 3 (CX04 ∷ []) (wp1078 c4) ▸
       at 0 4 (Bx3-2041 ∷ []) (sym (lem-box-tQ-at0312203441 c4)) ▸ done

  b2 : Chain (Bx3-2041 ∷ CX04 ∷ CCZ012 ∷ CX04 ∷ []) (Bx3-2041 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wp1079 c4)) ▸ done

-- CXcb-box @0312203441: 18 steps
lem-CXcb-box-at0312203441 : Ws → ⟪ (CX40 ∷ Bx3-2041 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at0312203441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX40 ∷ Bx3-2041 ∷ CX40 ∷ []) (Toff302 ∷ CCZ134 ∷ CX40 ∷ Toff324 ∷ CS14 ∷ CX24 ∷ Toff302 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ CCZ134 ∷ CX40 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at0312203441 c4) ▸
       at 0 2 (Toff302 ∷ CX40 ∷ Toff324 ∷ []) (wp1080 c4) ▸
       at 2 2 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1189 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX40 ∷ []) (sym (wp1081 c4)) ▸
       at 4 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0644 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CX24 ∷ []) (wp1049 c4) ▸
       at 6 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ CX40 ∷ Toff324 ∷ CS14 ∷ CX24 ∷ Toff302 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ CCZ134 ∷ CX40 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX40 ∷ CCZ124 ∷ CX40 ∷ [])
  b1 = at 5 2 (Toff302 ∷ CX24 ∷ []) (wp1049 c4) ▸
       at 4 2 (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0644 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 2 2 (Toff302 ∷ CX40 ∷ Toff324 ∷ []) (wp1080 c4) ▸
       at 3 3 (CX40 ∷ []) (wp1082 c4) ▸
       at 4 2 (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ CX40 ∷ []) (sym (wp1081 c4)) ▸ done

  b2 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX40 ∷ CCZ124 ∷ CX40 ∷ []) (Bx3-2041 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-2041 ∷ []) (sym (lem-box-tQ-at0312203441 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp1083 c4)) ▸ done

-- VPQ @0312243041: 14 steps
lem-VPQ-at0312243041 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0312243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S3⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 1 2 (CS01⁻ ∷ S3 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS24⁻ ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243041 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS24⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS24⁻ ∷ []) (wl0439 (lit c4)) ▸
       at 0 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸
       at 2 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸ done

-- CXbc-box @0312243041: 17 steps
lem-CXbc-box-at0312243041 : Ws → ⟪ (CX40 ∷ Bx3-2401 ∷ CX40 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at0312243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX40 ∷ Bx3-2401 ∷ CX40 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CCZ013 ∷ CX24 ∷ CS12 ∷ CX40 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243041 c4) ▸
       at 0 2 (Toff324 ∷ CX40 ∷ []) (wp1094 c4) ▸
       at 1 2 (CCZ013 ∷ CX40 ∷ CCZ134 ∷ []) (sym (wp1095 c4)) ▸
       at 3 2 (Toff324 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1277 (lit c4)) ▸
       at 2 2 (Toff324 ∷ CX40 ∷ []) (wp1094 c4) ▸
       at 5 1 (CS14 ∷ CX24 ∷ CS14⁻ ∷ CX24 ∷ CS12 ∷ []) (wl0644 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 8 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX40 ∷ CCZ134 ∷ CS14 ∷ CX24 ∷ CS14⁻ ∷ CCZ013 ∷ CX24 ∷ CS12 ∷ CX40 ∷ []) (Bx3-2401 ∷ CX40 ∷ CCZ124 ∷ CX40 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS14⁻ ∷ []) (sym (wp0521 c4)) ▸
       at 6 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0644 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ134 ∷ []) (sym (wp0593 c4)) ▸
       at 3 2 (CCZ013 ∷ CX40 ∷ CCZ134 ∷ []) (sym (wp1095 c4)) ▸
       at 4 3 (CX40 ∷ []) (wp1096 c4) ▸
       at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-tQ-at0312243041 c4)) ▸ done

  b2 : Chain (Bx3-2401 ∷ CX40 ∷ CCZ124 ∷ CX40 ∷ []) (Bx3-2401 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wp1083 c4)) ▸ done

-- CXcb-box @0312243041: 18 steps
lem-CXcb-box-at0312243041 : Ws → ⟪ (CX04 ∷ Bx3-2401 ∷ CX04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXcb-box-at0312243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX04 ∷ Bx3-2401 ∷ CX04 ∷ []) (Toff324 ∷ CCZ013 ∷ CX04 ∷ Toff302 ∷ CS01 ∷ CX20 ∷ Toff324 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ CCZ013 ∷ CX04 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at0312243041 c4) ▸
       at 0 2 (Toff324 ∷ CX04 ∷ Toff302 ∷ []) (wp1097 c4) ▸
       at 2 2 (CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) (sym (wl1278 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ CX04 ∷ []) (sym (wp1098 c4)) ▸
       at 4 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 8 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 7 2 (Toff324 ∷ CX20 ∷ []) (wp1099 c4) ▸
       at 6 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ CX04 ∷ Toff302 ∷ CS01 ∷ CX20 ∷ Toff324 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ CCZ013 ∷ CX04 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX04 ∷ CCZ012 ∷ CX04 ∷ [])
  b1 = at 5 2 (Toff324 ∷ CX20 ∷ []) (wp1099 c4) ▸
       at 4 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 2 2 (Toff324 ∷ CX04 ∷ Toff302 ∷ []) (wp1097 c4) ▸
       at 3 3 (CX04 ∷ []) (wp1100 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ012 ∷ []) (wl0704 (lit c4)) ▸
       at 3 2 (CCZ013 ∷ CX04 ∷ []) (sym (wp1098 c4)) ▸ done

  b2 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX04 ∷ CCZ012 ∷ CX04 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-tQ-at0312243041 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wp1079 c4)) ▸ done

-- P-box @0312203441: 8 steps
lem-P-box-at0312203441 : Ws → ⟪ (Toff314 ∷ Bx3-2041 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-P-box-at0312203441 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Bx3-2041 ∷ Toff314 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at0312203441 c4) ▸
       at 0 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at0312203441 c4)) ▸
       at 1 2 (CCZ134 ∷ CZ14 ∷ Toff314 ∷ []) (sym (wl1253 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff314 ∷ []) (sym (lem-tP-at0312203441 c4)) ▸
       at 4 3 (CCZ134 ∷ CZ14 ∷ []) (sym (wl1254 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ14 ∷ []) (lem-comm-CZ14-TOFF302 (lit c4)) ▸
       at 3 3 (CCZ134 ∷ []) (sym (wl1255 (lit c4))) ▸
       at 0 4 (Bx3-2041 ∷ []) (sym (lem-box-tQ-at0312203441 c4)) ▸ done

-- VPQ @0312203441: 14 steps
lem-VPQ-at0312203441 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at0312203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S3⁻ ∷ []) (sym (wl0786 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S3 ∷ []) (sym (wl0785 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at0312203441 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S)) ▸
       at 2 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S)) ▸
       at 0 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸
       at 2 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸ done

-- CXbc-box @3443: 17 steps
lem-CXbc-box-at3443 : Ws → ⟪ (CX24 ∷ Bx0-1243 ∷ CX24 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CXbc-box-at3443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX24 ∷ Bx0-1243 ∷ CX24 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX24 ∷ CCZ023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CX24 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 0 2 (Toff012 ∷ CX24 ∷ []) (wp0977 c4) ▸
       at 1 2 (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (sym (wp1017 c4)) ▸
       at 3 2 (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) (wl1283 (lit c4)) ▸
       at 2 2 (Toff012 ∷ CX24 ∷ []) (wp0977 c4) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CX24 ∷ CCZ023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ034 ∷ CX12 ∷ CS13 ∷ CX24 ∷ []) (Bx0-1243 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ023 ∷ []) (wp0575 c4) ▸
       at 3 2 (CCZ034 ∷ CX24 ∷ CCZ023 ∷ []) (sym (wp1017 c4)) ▸
       at 4 3 (CX24 ∷ []) (wp1018 c4) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸ done

  b2 : Chain (Bx0-1243 ∷ CX24 ∷ CCZ123 ∷ CX24 ∷ []) (Bx0-1243 ∷ CCZ123 ∷ [])
  b2 = at 1 3 (CCZ123 ∷ []) (sym (wl0315 (lit c4))) ▸ done

-- CXcb-box @3443: 18 steps
lem-CXcb-box-at3443 : Ws → ⟪ (CX42 ∷ Bx0-1243 ∷ CX42 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1243 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at3443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX42 ∷ Bx0-1243 ∷ CX42 ∷ []) (Toff012 ∷ CCZ034 ∷ CX42 ∷ Toff014 ∷ CS34 ∷ CX14 ∷ Toff012 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ034 ∷ CX42 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 0 2 (Toff012 ∷ CX42 ∷ Toff014 ∷ []) (wp1113 c4) ▸
       at 2 2 (CCZ034 ∷ Toff014 ∷ CCZ134 ∷ []) (sym (wp1114 c4)) ▸
       at 1 2 (CCZ034 ∷ CX42 ∷ []) (sym (wp1020 c4)) ▸
       at 4 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 8 2 (Toff012 ∷ CS13 ∷ []) (wl1284 (lit c4)) ▸
       at 7 2 (Toff012 ∷ CX14 ∷ []) (wp0974 c4) ▸
       at 6 2 (Toff012 ∷ CS34⁻ ∷ []) (sym (c₃ (Toff) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CX42 ∷ Toff014 ∷ CS34 ∷ CX14 ∷ Toff012 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ034 ∷ CX42 ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ [])
  b1 = at 5 2 (Toff012 ∷ CX14 ∷ []) (wp0974 c4) ▸
       at 4 2 (Toff012 ∷ CS34 ∷ []) (sym (c₃ (Toff) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 3 2 (Toff012 ∷ Toff014 ∷ []) (sym (wp0580 c4)) ▸
       at 2 2 (Toff012 ∷ CX42 ∷ Toff014 ∷ []) (wp1113 c4) ▸
       at 3 3 (CX42 ∷ []) (wp1115 c4) ▸
       at 4 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 3 2 (CCZ034 ∷ CX42 ∷ []) (sym (wp1020 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CX42 ∷ CCZ134 ∷ CX42 ∷ []) (Bx0-1243 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wl0312 (lit c4))) ▸ done

-- CK-box: 6 steps
lem-CK-box : Ws → ⟪ (CK34 ∷ Bx0-1234 ∷ CK34⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff403 ∷ Toff012 ∷ Toff403 ∷ []) ⟫ʷ
lem-CK-box c4 = run b0
  where
  b0 : Chain (CK34 ∷ Bx0-1234 ∷ CK34⁻ ∷ []) (Toff012 ∷ Toff403 ∷ Toff012 ∷ Toff403 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ CK34 ∷ []) (sym (c₃ (Toff) (CK₀₁))) ▸
       at 1 2 (Toff403 ∷ CK34 ∷ []) (wp1126 c4) ▸
       at 2 2 (Toff012 ∷ CK34 ∷ []) (sym (c₃ (Toff) (CK₀₁))) ▸
       at 3 2 (Toff403 ∷ CK34 ∷ []) (wp1126 c4) ▸
       at 4 2 [] (wl1300 (lit c4)) ▸ done

-- P-box @03243240: 8 steps
lem-P-box-at03243240 : Ws → ⟪ (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-P-box-at03243240 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 1 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 0 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at03243240 c4)) ▸
       at 1 2 (CCZ023 ∷ CZ02 ∷ Toff302 ∷ []) (sym (wl1235 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (sym (lem-tP-at03243240 c4)) ▸
       at 4 3 (CCZ023 ∷ CZ02 ∷ []) (sym (wl1236 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CZ02 ∷ []) (lem-comm-CZ02-TOFF314 (lit c4)) ▸
       at 3 3 (CCZ023 ∷ []) (sym (wl0774 (lit c4))) ▸
       at 0 4 (Bx3-1420 ∷ []) (sym (lem-box-tQ-at03243240 c4)) ▸ done

-- CXbc-box @031031: 17 steps
lem-CXbc-box-at031031 : Ws → ⟪ (CX21 ∷ Bx3-0214 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at031031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx3-0214 ∷ CX21 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX21 ∷ CCZ234 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4) ▸
       at 0 2 (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CX21 ∷ CCZ234 ∷ []) (sym (wl1305 (lit c4))) ▸
       at 3 2 (Toff302 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp1128 c4) ▸
       at 2 2 (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4)) ▸
       at 5 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 9 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 8 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX21 ∷ CCZ234 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ CX21 ∷ []) (Bx3-0214 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 4 2 (CCZ134 ∷ CCZ234 ∷ []) (sym (wl0960 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CX21 ∷ CCZ234 ∷ []) (sym (wl1305 (lit c4))) ▸
       at 4 3 (CX21 ∷ []) (wl1306 (lit c4)) ▸
       at 0 4 (Bx3-0214 ∷ []) (sym (lem-box-tQ-at031031 c4)) ▸ done

  b2 : Chain (Bx3-0214 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ []) (Bx3-0214 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0898 c4)) ▸ done

-- CXcb-box @031031: 18 steps
lem-CXcb-box-at031031 : Ws → ⟪ (CX12 ∷ Bx3-0214 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at031031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx3-0214 ∷ CX12 ∷ []) (Toff302 ∷ CCZ134 ∷ CX12 ∷ Toff301 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4) ▸
       at 0 2 (Toff302 ∷ CX12 ∷ Toff301 ∷ []) (wl1307 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Toff301 ∷ CCZ014 ∷ []) (sym (wp1129 c4)) ▸
       at 1 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 8 2 (Toff302 ∷ CS04 ∷ []) (wp1041 c4) ▸
       at 7 2 (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ CX12 ∷ Toff301 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ CX12 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ [])
  b1 = at 5 2 (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 3 2 (Toff302 ∷ Toff301 ∷ []) (wl1100 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CX12 ∷ Toff301 ∷ []) (wl1307 (lit c4)) ▸
       at 3 3 (CX12 ∷ []) (wl1308 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CCZ014 ∷ []) (wp0272 c4) ▸
       at 3 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸ done

  b2 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ []) (Bx3-0214 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-0214 ∷ []) (sym (lem-box-tQ-at031031 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸ done

-- VPQ @031031: 14 steps
lem-VPQ-at031031 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at031031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S3⁻ ∷ []) (sym (wl0786 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S3 ∷ []) (sym (wl0785 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at031031 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S)) ▸
       at 2 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S)) ▸
       at 0 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸
       at 2 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸ done

-- CXbc-box @03143041: 17 steps
lem-CXbc-box-at03143041 : Ws → ⟪ (CX20 ∷ Bx3-4201 ∷ CX20 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at03143041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX20 ∷ Bx3-4201 ∷ CX20 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX20 ∷ CCZ123 ∷ CS12 ∷ CX42 ∷ CS12⁻ ∷ CCZ013 ∷ CX42 ∷ CS14 ∷ CX20 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4) ▸
       at 0 2 (Toff324 ∷ CX20 ∷ []) (wp1099 c4) ▸
       at 1 2 (CCZ013 ∷ CX20 ∷ CCZ123 ∷ []) (sym (wl1317 (lit c4))) ▸
       at 3 2 (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0445 (lit c4)) ▸
       at 2 2 (Toff324 ∷ CX20 ∷ []) (wp1099 c4) ▸
       at 5 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4)) ▸
       at 9 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 8 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CX20 ∷ CCZ123 ∷ CS12 ∷ CX42 ∷ CS12⁻ ∷ CCZ013 ∷ CX42 ∷ CS14 ∷ CX20 ∷ []) (Bx3-4201 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ [])
  b1 = at 7 2 (CCZ013 ∷ CS12⁻ ∷ []) (sym (wl0703 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CX42 ∷ []) (lem-comm-CX42-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CS12 ∷ []) (sym (wl0645 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0702 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX20 ∷ CCZ123 ∷ []) (sym (wl1317 (lit c4))) ▸
       at 4 3 (CX20 ∷ []) (wl1318 (lit c4)) ▸
       at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-tQ-at03143041 c4)) ▸ done

  b2 : Chain (Bx3-4201 ∷ CX20 ∷ CCZ124 ∷ CX20 ∷ []) (Bx3-4201 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wp0380 c4)) ▸ done

-- CXcb-box @03143041: 18 steps
lem-CXcb-box-at03143041 : Ws → ⟪ (CX02 ∷ Bx3-4201 ∷ CX02 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at03143041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX02 ∷ Bx3-4201 ∷ CX02 ∷ []) (Toff324 ∷ CCZ013 ∷ CX02 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ Toff324 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ013 ∷ CX02 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4) ▸
       at 0 2 (Toff324 ∷ CX02 ∷ Toff304 ∷ []) (wp1141 c4) ▸
       at 2 2 (CCZ013 ∷ Toff304 ∷ CCZ014 ∷ []) (sym (wp1142 c4)) ▸
       at 1 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (Toff324 ∷ CS14 ∷ []) (wl0543 (lit c4)) ▸
       at 7 2 (Toff324 ∷ CX40 ∷ []) (wp1094 c4) ▸
       at 6 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ CX02 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ Toff324 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ013 ∷ CX02 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ [])
  b1 = at 5 2 (Toff324 ∷ CX40 ∷ []) (wp1094 c4) ▸
       at 4 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff324 ∷ Toff304 ∷ []) (wp1144 c4) ▸
       at 2 2 (Toff324 ∷ CX02 ∷ Toff304 ∷ []) (wp1141 c4) ▸
       at 3 3 (CX02 ∷ []) (wp1145 c4) ▸
       at 4 2 (CCZ013 ∷ CCZ014 ∷ []) (sym (wp0394 c4)) ▸
       at 3 2 (CCZ013 ∷ CX02 ∷ []) (sym (wl0444 (lit c4))) ▸ done

  b2 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ CX02 ∷ CCZ014 ∷ CX02 ∷ []) (Bx3-4201 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-tQ-at03143041 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0378 c4)) ▸ done

-- CXbc-box @02142041: 17 steps
lem-CXbc-box-at02142041 : Ws → ⟪ (CX03 ∷ Bx2-4031 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at02142041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-4031 ∷ CX03 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX03 ∷ CCZ012 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 0 2 (Toff204 ∷ CX03 ∷ []) (wp0949 c4) ▸
       at 1 2 (CCZ123 ∷ CX03 ∷ CCZ012 ∷ []) (sym (wl1320 (lit c4))) ▸
       at 3 2 (Toff204 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1150 c4) ▸
       at 2 2 (Toff204 ∷ CX03 ∷ []) (wp0949 c4) ▸
       at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX03 ∷ CCZ012 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CX03 ∷ []) (Bx2-4031 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ012 ∷ []) (wl0298 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX03 ∷ CCZ012 ∷ []) (sym (wl1320 (lit c4))) ▸
       at 4 3 (CX03 ∷ []) (wl1322 (lit c4)) ▸
       at 0 4 (Bx2-4031 ∷ []) (sym (lem-box-tQ-at02142041 c4)) ▸ done

  b2 : Chain (Bx2-4031 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-4031 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0761 c4)) ▸ done
