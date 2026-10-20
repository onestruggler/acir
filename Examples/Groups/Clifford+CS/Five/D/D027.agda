{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D027 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0186 ; wl0220 ; wl0230 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0263 ; wl0289 ; wl0305 ; wl1037 ; wl1118 ; wl1131 ; wp0021 ; wp0032 ; wp0034 ; wp0035 ; wp0036 ; wp0039 ; wp0041 ; wp0053 ; wp0060 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0094 ; wp0095 ; wp0097 ; wp0161 ; wp0610 ; wp0617 ; wp0842 ; wp0843 ; wp0845 ; wp0919 ; wp0925 ; wp0926 ; wp0927 ; wp0928 ; wp0929 ; wl0209 ; wl0233 ; wl0234 ; wl0297 ; wl0464 ; wl0720 ; wl0725 ; wl0735 ; wl0743 ; wl0905 ; wl1139 ; wl1140 ; wl1144 ; wl1145 ; wl1151 ; wl1152 ; wp0067 ; wp0092 ; wp0314 ; wp0633 ; wp0933 ; wp0934 ; wp0935 ; wp0936 ; wp0937 ; wp0938 ; wl0242 ; wl0326 ; wl1159 ; wl1160 ; wl1161 ; wl1162 ; wl1163 ; wp0091 ; wp0312 ; wp0734 ; wp0951 ; wp0952 ; wl0442 ; wl0729 ; wl1172 ; wl1173 ; wl1189 ; wl1190 ; wp0979 ; wp0980 ; wp0981 ; wp0982 ; wp1003 ; wp1004 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wl0155 ; wl0341 ; wl0499 ; wl0501 ; wl0778 ; wl0779 ; wl0780 ; wl0861 ; wl0888 ; wl1195 ; wl1196 ; wl1197 ; wl1198 ; wl1199 ; wl1208 ; wl1209 ; wl1220 ; wl1221 ; wl1223 ; wl1224 ; wl1226 ; wp0001 ; wp0002 ; wp0003 ; wp0106 ; wp0107 ; wp0108 ; wp0261 ; wp0700 ; wp0701 ; wp0702 ; wp1009 ; wp1012 ; wp1013 ; wp1026 ; wp1027 ; wp1030 ; wl0348 ; wl0391 ; wl0392 ; wl0393 ; wl0414 ; wl0415 ; wl0503 ; wl1247 ; wl1248 ; wl1249 ; wl1250 ; wl1251 ; wl1252 ; wp0279 ; wp1042 ; wp1047 ; wp1061 ; wp1062 ; wl0777 ; wl1261 ; wl1262 ; wl1263 ; wl1264 ; wl1265 ; wl1266 ; wl1273 ; wp1074 ; wp1075 ; wp1076 ; wp1105 ; wp1106 ; wp1107 ; wp1108 ; wp1109)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-sym-ab-at0210243143 ; lem-sym-ab-at0214203143 ; lem-sym-ab-at0310243142 ; lem-sym-ab-at0314203142 ; lem-sym-ab-at122441 ; lem-sym-ab-at13213442 ; lem-sym-ab-at233442 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-sym-ab-at0314213240 ; lem-sym-ab-at03243240 ; lem-sym-ab-at14213243 ; lem-sym-ab-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-tQ-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at0210233441 ; lem-box-tQ-at033440 ; lem-box-tQ-at12213443 ; lem-box-tQ-at12233441 ; lem-box-tQ-at13213442 ; lem-box-tQ-at233442)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at02233440 ; lem-box-tQ-at03103441 ; lem-box-tQ-at0312203441 ; lem-box-tQ-at03143140)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-sym-bc-at14233241)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-Xb-box-at13243142 ; lem-box-cP-at0310243142 ; lem-box-cP-at03243240 ; lem-box-cP-at122441 ; lem-box-perm-1324-at0310213442 ; lem-box-perm-1324-at13243142 ; lem-sym-bc-at0214213043 ; lem-sym-bc-at0314203142 ; lem-sym-bc-at0314213042 ; lem-sym-bc-at03243240 ; lem-sym-bc-at033440 ; lem-sym-bc-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-Xb-box-at122441 ; lem-box-perm-1324-at122441 ; lem-pairs-at13213442 ; lem-pairs-at143143)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-pairs-at0210233441)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-pairs-at12233441 ; lem-pairs-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-CSdu-box-3-at03143140 ; lem-CXu-box-4-at243243 ; lem-Xb-box-at02102441 ; lem-Xb-box-at022440 ; lem-Xb-box-at0310243142 ; lem-Xb-box-at0310243241 ; lem-Xb-box-at0312243041 ; lem-Xb-box-at03243240 ; lem-Xb-box-at12243143 ; lem-Xb-box-at2442 ; lem-box-perm-1324-at0210233441 ; lem-box-perm-1324-at02102441 ; lem-box-perm-1324-at02233440 ; lem-box-perm-1324-at022440 ; lem-box-perm-1324-at0310243142 ; lem-box-perm-1324-at0310243241 ; lem-box-perm-1324-at03103441 ; lem-box-perm-1324-at0312203441 ; lem-box-perm-1324-at0312243041 ; lem-box-perm-1324-at03243240 ; lem-box-perm-1324-at033440 ; lem-box-perm-1324-at12213443 ; lem-box-perm-1324-at12233441 ; lem-box-perm-1324-at12243143 ; lem-box-perm-1324-at13213442 ; lem-box-perm-1324-at233442 ; lem-box-perm-1324-at2442 ; lem-box2-at0310243142 ; lem-box2-at03243240 ; lem-nf-comm-CS-S1at2 ; lem-pairs-at0214203143 ; lem-pairs-at02233440 ; lem-pairs-at03103441 ; lem-pairs-at0312203441 ; lem-pairs-at0314203142 ; lem-pairs-at0314213042 ; lem-pairs-at0314213240 ; lem-pairs-at033440 ; lem-pairs-at12213443 ; lem-pairs-at1441 ; lem-pairs-at233442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX02-CCZ134 ; lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ024-CX31 ; lem-comm-CCZ034-CX12 ; lem-comm-CCZ034-CX21 ; lem-comm-CCZ124-CX03 ; lem-comm-CCZ134-CX02 ; lem-comm-CX04-TOFF312 ; lem-comm-CX14-TOFF302 ; lem-comm-TOFF013-CK42 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF024-CS13 ; lem-comm-TOFF213-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ134-CX20 ; lem-comm-TOFF301-CK42 ; lem-comm-TOFF312-CK40)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CK41 ; lem-comm-TOFF203-CK41 ; lem-comm-TOFF302-CK41)

-- F1-comm-CS-S1@2: 91 steps
lem-F1-comm-CS-S1at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-comm-CS-S1at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (run b11)))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ CS34 ∷ []) (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b0 = at 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b1 = at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 1 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b2 : Chain (CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b2 = at 3 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 2 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 3 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 6 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 2 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b3 : Chain (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b3 = at 1 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 0 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 1 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 2 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b4 : Chain (CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ [])
  b4 = at 6 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 7 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 1 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸ done

  b5 : Chain (CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ [])
  b5 = at 2 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 8 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b6 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ [])
  b6 = at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 6 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸ done

  b7 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ [])
  b7 = at 5 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 8 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 9 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 6 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 4 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸ done

  b8 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ [])
  b8 = at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 4 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 5 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b9 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CS34 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ [])
  b9 = at 10 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 4 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸ done

  b10 : Chain (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ Bx0-2431 ∷ [])
  b10 = at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸ done

  b11 : Chain (Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CS34 ∷ Bx0-2431 ∷ []) (CS34 ∷ Sb0-2-43-1 ∷ [])
  b11 = at 2 2 [] (wl0305 (lit c4)) ▸
       at 0 5 (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1118 (lit c4))) ▸
       at 0 6 (CS34 ∷ Sb0-2-43-1 ∷ []) (sym (lem-nf-comm-CS-S1at2 c4)) ▸ done

-- box-perm-3421 @0210243143: 2 steps
lem-box-perm-3421-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-3421-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-pairs-at0214203143 c4) ▸ done

-- CKc-box @02233440: 61 steps
lem-CKc-box-at02233440 : Ws → ⟪ (Bx2-1340 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ []) ⟫ʷ
lem-CKc-box-at02233440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx2-1340 ∷ CK40 ∷ []) (X4 ∷ Bx2-1340 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ [])
  b0 = at 1 0 (CCZ013 ∷ CCZ013 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 0 1 (Bx2-1430 ∷ []) (lem-box-perm-1324-at02233440 c4) ▸
       at 0 2 (X4 ∷ Bx2-1430 ∷ X4 ∷ []) (sym (lem-Xb-box-at022440 c4)) ▸
       at 3 2 (CCZ013 ∷ CK40 ∷ CCZ013 ∷ CCZ013 ∷ []) (sym (wp0925 c4)) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 6 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 1 1 (Bx2-1340 ∷ []) (lem-box-perm-1324-at022440 c4) ▸ done

  b1 : Chain (X4 ∷ Bx2-1340 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ [])
  b1 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 5 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 4 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ CCZ024 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ X4 ∷ CCZ013 ∷ [])
  b2 = at 5 2 (K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0926 c4) ▸
       at 8 2 (CZ02 ∷ CK40 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0927 c4) ▸
       at 11 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 13 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 12 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ024 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ [])
  b3 = at 16 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 12 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 5 7 (K0 ∷ CK40 ∷ S4 ∷ []) (sym (wp0928 c4)) ▸
       at 3 2 (CCZ013 ∷ Toff213 ∷ []) (sym (wl0186 (lit c4))) ▸
       at 4 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 5 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 7 2 (CCZ013 ∷ Toff213 ∷ []) (sym (wl0186 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff213 ∷ CCZ024 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ [])
  b4 = at 3 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 2 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸
       at 2 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0926 c4) ▸ done

  b5 : Chain (X4 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CCZ024 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ [])
  b5 = at 6 2 (CZ02 ∷ CK40 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0927 c4) ▸
       at 9 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 11 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 10 2 (CS03 ∷ CCZ024 ∷ []) (wp0021 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ024 ∷ []) (wp0039 c4) ▸ done

  b6 : Chain (X4 ∷ Toff213 ∷ CCZ013 ∷ K0 ∷ Toff024 ∷ CCZ024 ∷ CZ02 ∷ CK40 ∷ CZ02 ∷ S4 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Bx2-1340 ∷ X4 ∷ CCZ013 ∷ [])
  b6 = at 10 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 7 (K0 ∷ CK40 ∷ S4 ∷ []) (sym (wp0928 c4)) ▸
       at 1 2 (CCZ013 ∷ Toff213 ∷ []) (sym (wl0186 (lit c4))) ▸
       at 2 2 (K0 ∷ Toff213 ∷ []) (sym (c₁ (K) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 3 2 (CK40 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CK40 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (S)) ▸
       at 5 2 (CCZ013 ∷ Toff213 ∷ []) (sym (wl0186 (lit c4))) ▸
       at 6 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ013 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ013 ∷ Bx2-1340 ∷ X4 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK40 ∷ CCZ013 ∷ Bx2-1340 ∷ [])
  b7 = at 6 1 (Bx2-1430 ∷ []) (sym (lem-box-perm-1324-at022440 c4)) ▸
       at 0 6 (CCZ013 ∷ CK40 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0929 c4)) ▸
       at 3 3 (Bx2-1430 ∷ CCZ013 ∷ []) (lem-Xb-box-at022440 c4) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸
       at 3 1 (Bx2-1340 ∷ []) (lem-box-perm-1324-at022440 c4) ▸ done

-- box-perm-4312 @02233440: 2 steps
lem-box-perm-4312-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-4312-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-4013 ∷ []) (lem-pairs-at02233440 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸ done

-- box-perm-3421 @243243: 2 steps
lem-box-perm-3421-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-box-perm-3421-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-2341 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4) ▸
       at 0 1 (Bx0-2341 ∷ []) (lem-pairs-at14213243 c4) ▸ done

-- CKc-box @12233441: 61 steps
lem-CKc-box-at12233441 : Ws → ⟪ (Bx0-2341 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) ⟫ʷ
lem-CKc-box-at12233441 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-2341 ∷ CK41 ∷ []) (X4 ∷ Bx0-2341 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-box-perm-1324-at12233441 c4) ▸
       at 0 2 (X4 ∷ Bx0-2431 ∷ X4 ∷ []) (sym (lem-Xb-box-at122441 c4)) ▸
       at 3 2 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1139 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-2341 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 5 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 4 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CCZ014 ∷ CS12 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ []) (wp0933 c4) ▸
       at 8 2 (CZ01 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ []) (wp0934 c4) ▸
       at 11 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 13 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 12 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CCZ014 ∷ CS12 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ014 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 5 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wp0935 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 4 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 7 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff023 ∷ CCZ014 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 2 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 2 (K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ []) (wp0933 c4) ▸ done

  b5 : Chain (X4 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ01 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ []) (wp0934 c4) ▸
       at 9 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 11 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 10 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸ done

  b6 : Chain (X4 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Bx0-2341 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wp0935 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 2 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 5 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 6 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Bx0-2341 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ [])
  b7 = at 6 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 0 6 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1140 (lit c4))) ▸
       at 3 3 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-Xb-box-at122441 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸ done

-- box-perm-4312 @12233441: 2 steps
lem-box-perm-4312-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-4312-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-pairs-at12233441 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done

-- box-perm-3421 @122441: 2 steps
lem-box-perm-3421-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-3421-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-pairs-at1441 c4) ▸ done

-- CKc-box @13213442: 61 steps
lem-CKc-box-at13213442 : Ws → ⟪ (Bx0-3142 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) ⟫ʷ
lem-CKc-box-at13213442 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-3142 ∷ CK42 ∷ []) (X4 ∷ Bx0-3142 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-box-perm-1324-at13213442 c4) ▸
       at 0 2 (X4 ∷ Bx0-3412 ∷ X4 ∷ []) (sym (lem-Xb-box-at13243142 c4)) ▸
       at 3 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1144 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-box-perm-1324-at13243142 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-3142 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4) ▸
       at 5 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 5 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 8 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CCZ024 ∷ CS23 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0936 c4) ▸
       at 8 2 (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0937 c4) ▸
       at 11 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 13 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 12 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 13 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 14 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 15 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CCZ024 ∷ CS23 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 5 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wp0938 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 4 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 5 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 7 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 2 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 4 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 5 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0936 c4) ▸ done

  b5 : Chain (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0937 c4) ▸
       at 9 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 11 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 10 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 11 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 12 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 13 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 14 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸ done

  b6 : Chain (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Bx0-3142 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wp0938 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 3 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 5 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 6 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Bx0-3142 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ [])
  b7 = at 6 1 (Bx0-3412 ∷ []) (sym (lem-box-perm-1324-at13243142 c4)) ▸
       at 0 6 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1145 (lit c4))) ▸
       at 3 3 (Bx0-3412 ∷ CCZ123 ∷ []) (lem-Xb-box-at13243142 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-3142 ∷ []) (lem-box-perm-1324-at13243142 c4) ▸ done

-- box-perm-4312 @13213442: 2 steps
lem-box-perm-4312-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-4312-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-pairs-at13213442 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym-ab-at1441 c4) ▸ done

-- CKc-box @0210233441: 61 steps
lem-CKc-box-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ []) ⟫ʷ
lem-CKc-box-at0210233441 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx2-0341 ∷ CK41 ∷ []) (X4 ∷ Bx2-0341 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ [])
  b0 = at 1 0 (CCZ013 ∷ CCZ013 ∷ []) (sym (wl0230 (lit c4))) ▸
       at 0 1 (Bx2-0431 ∷ []) (lem-box-perm-1324-at0210233441 c4) ▸
       at 0 2 (X4 ∷ Bx2-0431 ∷ X4 ∷ []) (sym (lem-Xb-box-at02102441 c4)) ▸
       at 3 2 (CCZ013 ∷ CK41 ∷ CCZ013 ∷ CCZ013 ∷ []) (sym (wp0951 c4)) ▸
       at 2 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 3 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))) ▸
       at 1 1 (Bx2-0341 ∷ []) (lem-box-perm-1324-at02102441 c4) ▸ done

  b1 : Chain (X4 ∷ Bx2-0341 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ013 ∷ CCZ124 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ [])
  b1 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4) ▸
       at 5 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 4 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 5 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 7 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ124 ∷ []) (wp0919 c4) ▸
       at 4 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ013 ∷ CCZ124 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CCZ124 ∷ CS01 ∷ X4 ∷ CCZ013 ∷ [])
  b2 = at 5 2 (K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ []) (wl1159 (lit c4)) ▸
       at 8 2 (CZ12 ∷ CK41 ∷ CZ12 ∷ CCZ124 ∷ []) (wl1160 (lit c4)) ▸
       at 11 2 (S4 ∷ CCZ124 ∷ []) (wl1161 (lit c4)) ▸
       at 13 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 12 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 13 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 14 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 15 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CCZ124 ∷ CS01 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ124 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ [])
  b3 = at 16 2 (CS01 ∷ CCZ124 ∷ []) (wp0919 c4) ▸
       at 12 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 5 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1162 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ Toff203 ∷ []) (sym (wl1131 (lit c4))) ▸
       at 4 2 (K1 ∷ Toff203 ∷ []) (sym (wl1163 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CK41 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 7 2 (CCZ013 ∷ Toff203 ∷ []) (sym (wl1131 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff203 ∷ CCZ124 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ [])
  b4 = at 3 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 2 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 3 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 4 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 5 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 6 2 (CS01 ∷ CCZ124 ∷ []) (wp0919 c4) ▸
       at 2 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ []) (wl1159 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ [])
  b5 = at 6 2 (CZ12 ∷ CK41 ∷ CZ12 ∷ CCZ124 ∷ []) (wl1160 (lit c4)) ▸
       at 9 2 (S4 ∷ CCZ124 ∷ []) (wl1161 (lit c4)) ▸
       at 11 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 10 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 11 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 12 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 13 2 (CX03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CX03 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ124 ∷ []) (wp0919 c4) ▸ done

  b6 : Chain (X4 ∷ Toff203 ∷ CCZ013 ∷ K1 ∷ Toff124 ∷ CCZ124 ∷ CZ12 ∷ CK41 ∷ CZ12 ∷ S4 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ X4 ∷ CCZ013 ∷ []) (X4 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Bx2-0341 ∷ X4 ∷ CCZ013 ∷ [])
  b6 = at 10 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1162 (lit c4))) ▸
       at 1 2 (CCZ013 ∷ Toff203 ∷ []) (sym (wl1131 (lit c4))) ▸
       at 2 2 (K1 ∷ Toff203 ∷ []) (sym (wl1163 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff203 ∷ []) (lem-comm-TOFF203-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 5 2 (CCZ013 ∷ Toff203 ∷ []) (sym (wl1131 (lit c4))) ▸
       at 6 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ013 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ013 ∷ Bx2-0341 ∷ X4 ∷ CCZ013 ∷ []) (CCZ013 ∷ CK41 ∷ CCZ013 ∷ Bx2-0341 ∷ [])
  b7 = at 6 1 (Bx2-0431 ∷ []) (sym (lem-box-perm-1324-at02102441 c4)) ▸
       at 0 6 (CCZ013 ∷ CK41 ∷ CCZ013 ∷ X4 ∷ []) (sym (wp0952 c4)) ▸
       at 3 3 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-Xb-box-at02102441 c4) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸
       at 3 1 (Bx2-0341 ∷ []) (lem-box-perm-1324-at02102441 c4) ▸ done

-- box-perm-1342 @0210233441: 3 steps
lem-box-perm-1342-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-1342-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-4103 ∷ []) (lem-pairs-at0210233441 c4) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-sym-bc-at0214213043 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4) ▸ done

-- CKc-box @233442: 61 steps
lem-CKc-box-at233442 : Ws → ⟪ (Bx0-1342 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ []) ⟫ʷ
lem-CKc-box-at233442 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-1342 ∷ CK42 ∷ []) (X4 ∷ Bx0-1342 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-1432 ∷ []) (lem-box-perm-1324-at233442 c4) ▸
       at 0 2 (X4 ∷ Bx0-1432 ∷ X4 ∷ []) (sym (lem-Xb-box-at2442 c4)) ▸
       at 3 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1144 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-1342 ∷ []) (lem-box-perm-1324-at2442 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-1342 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at233442 c4) ▸
       at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 4 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0936 c4) ▸
       at 8 2 (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0937 c4) ▸
       at 11 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 13 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 12 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CCZ024 ∷ CS12 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wp0938 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 4 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 5 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 7 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 2 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 3 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0936 c4) ▸ done

  b5 : Chain (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0937 c4) ▸
       at 9 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 11 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 10 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS23⁻ ∷ CCZ024 ∷ []) (wp0091 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b6 : Chain (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Bx0-1342 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wp0938 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 3 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 5 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 6 4 (Bx0-1342 ∷ []) (sym (lem-box-tQ-at233442 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Bx0-1342 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-1342 ∷ [])
  b7 = at 6 1 (Bx0-1432 ∷ []) (sym (lem-box-perm-1324-at2442 c4)) ▸
       at 0 6 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1145 (lit c4))) ▸
       at 3 3 (Bx0-1432 ∷ CCZ123 ∷ []) (lem-Xb-box-at2442 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-1342 ∷ []) (lem-box-perm-1324-at2442 c4) ▸ done

-- box-perm-1342 @233442: 3 steps
lem-box-perm-1342-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1342-at233442 c4 = run b0
  where
  b0 : Chain (Bx0-1342 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-4213 ∷ []) (lem-pairs-at233442 c4) ▸
       at 0 1 (Bx0-4123 ∷ []) (lem-sym-bc-at143143 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done

-- CKc-box @12213443: 61 steps
lem-CKc-box-at12213443 : Ws → ⟪ (Bx0-2143 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) ⟫ʷ
lem-CKc-box-at12213443 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-2143 ∷ CK43 ∷ []) (X4 ∷ Bx0-2143 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-2413 ∷ []) (lem-box-perm-1324-at12213443 c4) ▸
       at 0 2 (X4 ∷ Bx0-2413 ∷ X4 ∷ []) (sym (lem-Xb-box-at12243143 c4)) ▸
       at 3 2 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1172 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K3 ∷ CK43 ∷ S4 ∷ X4 ∷ []) (sym (wl0729 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-2143 ∷ []) (lem-box-perm-1324-at12243143 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-2143 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at12213443 c4) ▸
       at 5 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 4 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 5 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4) ▸
       at 7 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 8 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ CCZ034 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CCZ034 ∷ CS23 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0979 c4) ▸
       at 8 2 (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0980 c4) ▸
       at 11 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 13 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 12 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 13 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 14 2 (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4) ▸
       at 15 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CCZ034 ∷ CS23 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ034 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 5 7 (K3 ∷ CK43 ∷ S4 ∷ []) (sym (wp0982 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 4 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 5 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 6 2 (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑)) ▸
       at 7 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff012 ∷ CCZ034 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 2 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 3 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 4 2 (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4) ▸
       at 5 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 6 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0979 c4) ▸ done

  b5 : Chain (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CCZ034 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ03 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ []) (wp0980 c4) ▸
       at 9 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 11 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 10 2 (CS13 ∷ CCZ034 ∷ []) (wp0312 c4) ▸
       at 11 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 12 2 (CS13⁻ ∷ CCZ034 ∷ []) (wp0734 c4) ▸
       at 13 2 (CX21 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX21 (lit c4)) ▸
       at 14 2 (CS23 ∷ CCZ034 ∷ []) (wp0314 c4) ▸ done

  b6 : Chain (X4 ∷ Toff012 ∷ CCZ123 ∷ K3 ∷ Toff304 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ S4 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Bx0-2143 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 7 (K3 ∷ CK43 ∷ S4 ∷ []) (sym (wp0982 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 2 2 (K3 ∷ Toff012 ∷ []) (c₃ (Toff) (K)) ▸
       at 3 2 (CK43 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₁₀)) ▸
       at 4 2 (S4 ∷ Toff012 ∷ []) (c₃ (Toff) (S ↑)) ▸
       at 5 2 (CCZ123 ∷ Toff012 ∷ []) (sym (wl0464 (lit c4))) ▸
       at 6 4 (Bx0-2143 ∷ []) (sym (lem-box-tQ-at12213443 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K3 ∷ CK43 ∷ S4 ∷ CCZ123 ∷ Bx0-2143 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ [])
  b7 = at 6 1 (Bx0-2413 ∷ []) (sym (lem-box-perm-1324-at12243143 c4)) ▸
       at 0 6 (CCZ123 ∷ CK43 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1173 (lit c4))) ▸
       at 3 3 (Bx0-2413 ∷ CCZ123 ∷ []) (lem-Xb-box-at12243143 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-2143 ∷ []) (lem-box-perm-1324-at12243143 c4) ▸ done

-- box-perm-1342 @12213443: 3 steps
lem-box-perm-1342-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1342-at12213443 c4 = run b0
  where
  b0 : Chain (Bx0-2143 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-4321 ∷ []) (lem-pairs-at12213443 c4) ▸
       at 0 1 (Bx0-4231 ∷ []) (lem-sym-bc-at14233241 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym-ab-at1441 c4) ▸ done

-- box-perm-4312 @143143: 2 steps
lem-box-perm-4312-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-4312-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-1342 ∷ []) (lem-pairs-at143143 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-sym-ab-at233442 c4) ▸ done

-- box-perm-3421 @13213442: 2 steps
lem-box-perm-3421-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-3421-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-4213 ∷ [])
  b0 = at 0 1 (Bx0-1342 ∷ []) (lem-sym-ab-at13213442 c4) ▸
       at 0 1 (Bx0-4213 ∷ []) (lem-pairs-at233442 c4) ▸ done

-- F0-R @01143043: 11 steps
lem-F0-R-at01143043 : Ws → ⟪ (CX03 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx3-4210 ∷ CX03 ∷ []) ⟫ʷ
lem-F0-R-at01143043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX03 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS13⁻ ∷ CCZ013 ∷ CX03 ∷ [])
  b0 = at 0 2 (Toff324 ∷ CX03 ∷ []) (wp1009 c4) ▸
       at 1 2 (CS13 ∷ CS01 ∷ CCZ013 ∷ CX03 ∷ []) (sym (wl1195 (lit c4))) ▸
       at 4 2 (Toff324 ∷ CX03 ∷ []) (wp1009 c4) ▸
       at 5 2 (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CX03 ∷ []) (sym (wl1196 (lit c4))) ▸
       at 2 2 (CCZ013 ∷ CS01 ∷ []) (sym (wl1197 (lit c4))) ▸
       at 3 2 (Toff324 ∷ CS01 ∷ []) (c₂ (CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 3 (CS13⁻ ∷ []) (wl1198 (lit c4)) ▸
       at 2 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸ done

  b1 : Chain (Toff324 ∷ CS13 ∷ Toff324 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CS13⁻ ∷ CCZ013 ∷ CX03 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx3-4210 ∷ CX03 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ CS13⁻ ∷ []) (sym (wl1199 (lit c4))) ▸
       at 3 4 (Bx3-4210 ∷ []) (sym (lem-box-tQ-at03143140 c4)) ▸
       at 3 2 (CS13⁻ ∷ Bx3-4210 ∷ []) (sym (lem-CSdu-box-3-at03143140 c4)) ▸ done

-- CXAu-S @01143043: 12 steps
lem-CXAu-S-at01143043 : Ws → ⟪ (CX30 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CX30 ∷ []) ⟫ʷ
lem-CXAu-S-at01143043 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CX30 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ CX30 ∷ []) (lem-CXu-box-4-at243243 c4) ▸
       at 1 2 (Toff324 ∷ CX30 ∷ Toff024 ∷ []) (wp1012 c4) ▸
       at 3 2 (CS13 ∷ Toff024 ∷ []) (lem-comm-TOFF024-CS13 (lit c4)) ▸
       at 2 2 (CS13 ∷ CX30 ∷ []) (sym (wl1208 (lit c4))) ▸
       at 3 3 (Toff324 ∷ CX30 ∷ []) (wp1013 c4) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CX30 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ CX30 ∷ [])
  b1 = at 4 2 (CS13⁻ ∷ CX30 ∷ []) (sym (wl1209 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

-- box-perm-3241 @0310243142: 3 steps
lem-box-perm-3241-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-3241-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸
       at 0 1 (Bx3-1240 ∷ []) (lem-pairs-at0314203142 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym-bc-at033440 c4) ▸ done

-- box-perm-4213 @03243240: 3 steps
lem-box-perm-4213-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-4213-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-1240 ∷ []) (lem-sym-bc-at03243240 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-pairs-at033440 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸ done

-- S2-SBOX(3;1;42;0): 86 steps
lem-S2-SBOX⟨3·1·42·0⟩ : Ws → ⟪ (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨3·1·42·0⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ134 ∷ CS01⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b0 = at 1 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 3 1 (CS01 ∷ []) (refl) ▸
       at 5 1 (CS01⁻ ∷ []) (refl) ▸
       at 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 4 2 (CCZ134 ∷ CS01⁻ ∷ []) (sym (wp1027 c4)) ▸ done

  b1 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CCZ134 ∷ CS01⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b1 = at 5 2 (Toff302 ∷ CS01⁻ ∷ []) (wl1224 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CS01⁻ ∷ []) (sym (wp1027 c4)) ▸
       at 7 2 (Toff302 ∷ CS01⁻ ∷ []) (wl1224 (lit c4)) ▸
       at 4 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 3 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 9 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 8 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸ done

  b2 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b2 = at 7 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 4 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸
       at 6 2 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1189 (lit c4))) ▸ done

  b3 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b3 = at 5 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 11 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 10 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 9 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 7 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸ done

  b4 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b4 = at 6 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 11 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 10 2 (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4) ▸
       at 9 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b5 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff302 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b5 = at 7 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 6 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸
       at 7 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 3 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 3 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 2 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 3 2 (Toff302 ∷ CS01 ∷ []) (wl1223 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸ done

  b6 : Chain (Bx3-1420 ∷ Toff024 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01 ∷ Toff302 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ K0 ∷ CS24 ∷ CX02 ∷ CCZ134 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b6 = at 5 2 (Toff302 ∷ CS01 ∷ []) (wl1223 (lit c4)) ▸
       at 2 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 1 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 7 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 5 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸ done

  b7 : Chain (Bx3-1420 ∷ K0 ∷ CS24 ∷ CX02 ∷ CCZ134 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b7 = at 3 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 2 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸
       at 4 2 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1189 (lit c4))) ▸
       at 3 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 9 2 (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸ done

  b8 : Chain (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ CCZ124 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b8 = at 8 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 7 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CS24⁻ ∷ []) (sym (wl1221 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CX02 ∷ []) (lem-comm-CX02-CCZ134 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b9 : Chain (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b9 = at 10 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 9 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4) ▸
       at 7 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 5 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 4 2 (Toff302 ∷ Toff024 ∷ Toff324 ∷ []) (wp1004 c4) ▸ done

  b10 : Chain (Bx3-1420 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (CCZ124 ∷ [])
  b10 = at 5 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 1 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 0 2 [] (lem-box2-at03243240 c4) ▸
       at 1 3 (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp1042 c4) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸
       at 0 8 (CCZ124 ∷ []) (sym (wp1047 c4)) ▸ done

-- box-perm-1423 @0310243142: 3 steps
lem-box-perm-1423-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-box-perm-1423-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-0241 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸
       at 0 1 (Bx3-4102 ∷ []) (lem-sym-bc-at0314203142 c4) ▸
       at 0 1 (Bx3-0241 ∷ []) (lem-pairs-at0314213042 c4) ▸ done

-- CKc-box @03103441: 61 steps
lem-CKc-box-at03103441 : Ws → ⟪ (Bx3-0241 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) ⟫ʷ
lem-CKc-box-at03103441 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx3-0241 ∷ CK41 ∷ []) (X4 ∷ Bx3-0241 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b0 = at 1 0 (CCZ012 ∷ CCZ012 ∷ []) (sym (wl0341 (lit c4))) ▸
       at 0 1 (Bx3-0421 ∷ []) (lem-box-perm-1324-at03103441 c4) ▸
       at 0 2 (X4 ∷ Bx3-0421 ∷ X4 ∷ []) (sym (lem-Xb-box-at0310243241 c4)) ▸
       at 3 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ []) (sym (wp1061 c4)) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 1 (Bx3-0241 ∷ []) (lem-box-perm-1324-at0310243241 c4) ▸ done

  b1 : Chain (X4 ∷ Bx3-0241 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ CCZ134 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b1 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4) ▸
       at 5 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 5 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 6 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ CCZ134 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ134 ∷ CS01 ∷ X4 ∷ CCZ012 ∷ [])
  b2 = at 5 2 (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) (wl1247 (lit c4)) ▸
       at 8 2 (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1248 (lit c4)) ▸
       at 11 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 13 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 12 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 13 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 14 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 15 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CCZ134 ∷ CS01 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b3 = at 16 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 12 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 5 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1250 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 4 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CK41 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 7 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b4 = at 3 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 2 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 3 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 4 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 5 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 6 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 2 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 3 2 (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) (wl1247 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b5 = at 6 2 (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1248 (lit c4)) ▸
       at 9 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 11 1 (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl0391 (lit c4)) ▸
       at 10 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 11 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 12 2 (CS12⁻ ∷ CCZ134 ∷ []) (wl0392 (lit c4)) ▸
       at 13 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸ done

  b6 : Chain (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Bx3-0241 ∷ X4 ∷ CCZ012 ∷ [])
  b6 = at 10 5 (CCZ012 ∷ []) (sym (wl0391 (lit c4))) ▸
       at 3 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1250 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 2 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 5 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 6 4 (Bx3-0241 ∷ []) (sym (lem-box-tQ-at03103441 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Bx3-0241 ∷ X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ [])
  b7 = at 6 1 (Bx3-0421 ∷ []) (sym (lem-box-perm-1324-at0310243241 c4)) ▸
       at 0 6 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ X4 ∷ []) (sym (wp1062 c4)) ▸
       at 3 3 (Bx3-0421 ∷ CCZ012 ∷ []) (lem-Xb-box-at0310243241 c4) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 3 1 (Bx3-0241 ∷ []) (lem-box-perm-1324-at0310243241 c4) ▸ done

-- box-perm-1342 @03103441: 3 steps
lem-box-perm-1342-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1342-at03103441 c4 = run b0
  where
  b0 : Chain (Bx3-0241 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-4102 ∷ []) (lem-pairs-at03103441 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-bc-at0314213042 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸ done

-- CKc-box @0310213442: 61 steps
lem-CKc-box-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ []) ⟫ʷ
lem-CKc-box-at0310213442 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx3-0142 ∷ CK42 ∷ []) (X4 ∷ Bx3-0142 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b0 = at 1 0 (CCZ012 ∷ CCZ012 ∷ []) (sym (wl0341 (lit c4))) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸
       at 0 2 (X4 ∷ Bx3-0412 ∷ X4 ∷ []) (sym (lem-Xb-box-at0310243142 c4)) ▸
       at 3 2 (CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ012 ∷ []) (sym (wp1074 c4)) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 1 (Bx3-0142 ∷ []) (lem-box-perm-1324-at0310243142 c4) ▸ done

  b1 : Chain (X4 ∷ Bx3-0142 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ012 ∷ CCZ234 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b1 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 5 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 6 2 (CS12⁻ ∷ CCZ234 ∷ []) (wl0414 (lit c4)) ▸
       at 7 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 8 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ012 ∷ CCZ234 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ012 ∷ K2 ∷ Toff234 ∷ CCZ234 ∷ CZ23 ∷ CK42 ∷ CZ23 ∷ S4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CCZ234 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ [])
  b2 = at 5 2 (K2 ∷ Toff234 ∷ CCZ234 ∷ CCZ234 ∷ []) (wl1261 (lit c4)) ▸
       at 8 2 (CZ23 ∷ CK42 ∷ CZ23 ∷ CCZ234 ∷ []) (wl1262 (lit c4)) ▸
       at 11 2 (S4 ∷ CCZ234 ∷ []) (wl1263 (lit c4)) ▸
       at 13 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 12 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 13 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 14 2 (CS12⁻ ∷ CCZ234 ∷ []) (wl0414 (lit c4)) ▸
       at 15 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸ done

  b3 : Chain (X4 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ012 ∷ K2 ∷ Toff234 ∷ CCZ234 ∷ CZ23 ∷ CK42 ∷ CZ23 ∷ S4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CCZ234 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff301 ∷ CCZ234 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ Toff301 ∷ CCZ234 ∷ X4 ∷ CCZ012 ∷ [])
  b3 = at 16 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 12 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 5 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wl1264 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ Toff301 ∷ []) (sym (wl1265 (lit c4))) ▸
       at 4 2 (K2 ∷ Toff301 ∷ []) (sym (wl1266 (lit c4))) ▸
       at 5 2 (CK42 ∷ Toff301 ∷ []) (lem-comm-TOFF301-CK42 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff301 ∷ []) (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (S)) ▸
       at 7 2 (CCZ012 ∷ Toff301 ∷ []) (sym (wl1265 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff301 ∷ CCZ234 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ Toff301 ∷ CCZ234 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff301 ∷ CCZ012 ∷ K2 ∷ Toff234 ∷ CCZ234 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ Toff301 ∷ CCZ234 ∷ X4 ∷ CCZ012 ∷ [])
  b4 = at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 2 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 3 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 4 2 (CS12⁻ ∷ CCZ234 ∷ []) (wl0414 (lit c4)) ▸
       at 5 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 6 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸
       at 2 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (K2 ∷ Toff234 ∷ CCZ234 ∷ CCZ234 ∷ []) (wl1261 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff301 ∷ CCZ012 ∷ K2 ∷ Toff234 ∷ CCZ234 ∷ CCZ234 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ Toff301 ∷ CCZ234 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff301 ∷ CCZ012 ∷ K2 ∷ Toff234 ∷ CCZ234 ∷ CZ23 ∷ CK42 ∷ CZ23 ∷ S4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ X4 ∷ CCZ012 ∷ [])
  b5 = at 6 2 (CZ23 ∷ CK42 ∷ CZ23 ∷ CCZ234 ∷ []) (wl1262 (lit c4)) ▸
       at 9 2 (S4 ∷ CCZ234 ∷ []) (wl1263 (lit c4)) ▸
       at 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 10 2 (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4)) ▸
       at 11 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 12 2 (CS12⁻ ∷ CCZ234 ∷ []) (wl0414 (lit c4)) ▸
       at 13 2 (CX01 ∷ CCZ234 ∷ []) (sym (c₂ (CX₀₁) (CCZ))) ▸
       at 14 2 (CS02 ∷ CCZ234 ∷ []) (wp0279 c4) ▸ done

  b6 : Chain (X4 ∷ Toff301 ∷ CCZ012 ∷ K2 ∷ Toff234 ∷ CCZ234 ∷ CZ23 ∷ CK42 ∷ CZ23 ∷ S4 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ Bx3-0142 ∷ X4 ∷ CCZ012 ∷ [])
  b6 = at 10 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wl1264 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Toff301 ∷ []) (sym (wl1265 (lit c4))) ▸
       at 2 2 (K2 ∷ Toff301 ∷ []) (sym (wl1266 (lit c4))) ▸
       at 3 2 (CK42 ∷ Toff301 ∷ []) (lem-comm-TOFF301-CK42 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff301 ∷ []) (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (S)) ▸
       at 5 2 (CCZ012 ∷ Toff301 ∷ []) (sym (wl1265 (lit c4))) ▸
       at 6 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ012 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ012 ∷ Bx3-0142 ∷ X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ [])
  b7 = at 6 1 (Bx3-0412 ∷ []) (sym (lem-box-perm-1324-at0310243142 c4)) ▸
       at 0 6 (CCZ012 ∷ CK42 ∷ CCZ012 ∷ X4 ∷ []) (sym (wp1075 c4)) ▸
       at 3 3 (Bx3-0412 ∷ CCZ012 ∷ []) (lem-Xb-box-at0310243142 c4) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 3 1 (Bx3-0142 ∷ []) (lem-box-perm-1324-at0310243142 c4) ▸ done

-- S2-SBOX(3;0;41;2): 86 steps
lem-S2-SBOX⟨3·0·41·2⟩ : Ws → ⟪ (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨3·0·41·2⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ034 ∷ CS02⁻ ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b0 = at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 2 1 (CS02 ∷ []) (refl) ▸
       at 4 1 (CS02⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸ done

  b1 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CCZ034 ∷ CS02⁻ ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b1 = at 5 2 (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 7 2 (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4)) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 9 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 8 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸ done

  b2 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b2 = at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 4 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 4 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl0777 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸ done

  b3 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b3 = at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 11 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 10 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 9 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 5 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸ done

  b4 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b4 = at 6 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 8 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 12 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 11 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 10 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 9 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b5 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02 ∷ Toff312 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b5 = at 7 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 6 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl0777 (lit c4)) ▸
       at 7 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 3 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 2 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 3 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸ done

  b6 : Chain (Bx3-0412 ∷ Toff214 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02 ∷ Toff312 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ K2 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b6 = at 5 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 1 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 7 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸ done

  b7 : Chain (Bx3-0412 ∷ K2 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b7 = at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 1 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 2 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 2 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl0777 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ Toff314 ∷ CCZ014 ∷ []) (sym (wp0702 c4)) ▸
       at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 9 2 (CCZ034 ∷ K2⁻ ∷ []) (sym (wp0700 c4)) ▸ done

  b8 : Chain (Bx3-0412 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ Toff314 ∷ CCZ014 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b8 = at 8 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 2 (CCZ034 ∷ K2 ∷ []) (sym (wp0701 c4)) ▸
       at 4 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 6 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b9 : Chain (Bx3-0412 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b9 = at 10 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 5 2 (Toff312 ∷ Toff314 ∷ []) (sym (wl0779 (lit c4))) ▸
       at 4 2 (Toff312 ∷ Toff214 ∷ Toff314 ∷ []) (wl0777 (lit c4)) ▸ done

  b10 : Chain (Bx3-0412 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (CCZ014 ∷ [])
  b10 = at 5 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 1 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 0 2 [] (lem-box2-at0310243142 c4) ▸
       at 1 3 (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp1030 c4) ▸
       at 3 2 [] (wp0161 c4) ▸
       at 0 8 (CCZ014 ∷ []) (sym (wp1076 c4)) ▸ done

-- box-perm-3421 @03243240: 2 steps
lem-box-perm-3421-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-box-perm-3421-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4) ▸
       at 0 1 (Bx3-2041 ∷ []) (lem-pairs-at0314213240 c4) ▸ done

-- CKc-box @0312203441: 61 steps
lem-CKc-box-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) ⟫ʷ
lem-CKc-box-at0312203441 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx3-2041 ∷ CK41 ∷ []) (X4 ∷ Bx3-2041 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b0 = at 1 0 (CCZ012 ∷ CCZ012 ∷ []) (sym (wl0341 (lit c4))) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-box-perm-1324-at0312203441 c4) ▸
       at 0 2 (X4 ∷ Bx3-2401 ∷ X4 ∷ []) (sym (lem-Xb-box-at0312243041 c4)) ▸
       at 3 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ012 ∷ []) (sym (wp1061 c4)) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 1 (Bx3-2041 ∷ []) (lem-box-perm-1324-at0312243041 c4) ▸ done

  b1 : Chain (X4 ∷ Bx3-2041 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ CCZ134 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b1 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at0312203441 c4) ▸
       at 5 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 4 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 5 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 6 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 7 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 8 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ CCZ134 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CCZ134 ∷ CS12 ∷ X4 ∷ CCZ012 ∷ [])
  b2 = at 5 2 (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) (wl1247 (lit c4)) ▸
       at 8 2 (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1248 (lit c4)) ▸
       at 11 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 13 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 12 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 13 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 14 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 15 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CCZ134 ∷ CS12 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ134 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b3 = at 16 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 12 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 5 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1250 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 4 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CK41 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 7 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff302 ∷ CCZ134 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b4 = at 3 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 2 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 3 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 4 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 5 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 6 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸
       at 2 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 3 2 (K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ []) (wl1247 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CCZ134 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ [])
  b5 = at 6 2 (CZ13 ∷ CK41 ∷ CZ13 ∷ CCZ134 ∷ []) (wl1248 (lit c4)) ▸
       at 9 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 11 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 10 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 11 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 12 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 13 2 (CX20 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX20 (lit c4)) ▸
       at 14 2 (CS12 ∷ CCZ134 ∷ []) (wl0393 (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Toff302 ∷ CCZ012 ∷ K1 ∷ Toff134 ∷ CCZ134 ∷ CZ13 ∷ CK41 ∷ CZ13 ∷ S4 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Bx3-2041 ∷ X4 ∷ CCZ012 ∷ [])
  b6 = at 10 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 3 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wl1250 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 2 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 5 2 (CCZ012 ∷ Toff302 ∷ []) (sym (wl1251 (lit c4))) ▸
       at 6 4 (Bx3-2041 ∷ []) (sym (lem-box-tQ-at0312203441 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ012 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ Bx3-2041 ∷ X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ [])
  b7 = at 6 1 (Bx3-2401 ∷ []) (sym (lem-box-perm-1324-at0312243041 c4)) ▸
       at 0 6 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ X4 ∷ []) (sym (wp1062 c4)) ▸
       at 3 3 (Bx3-2401 ∷ CCZ012 ∷ []) (lem-Xb-box-at0312243041 c4) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 3 1 (Bx3-2041 ∷ []) (lem-box-perm-1324-at0312243041 c4) ▸ done

-- box-perm-4312 @0312203441: 2 steps
lem-box-perm-4312-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-4312-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-pairs-at0312203441 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4) ▸ done

-- CKc-box @033440: 61 steps
lem-CKc-box-at033440 : Ws → ⟪ (Bx3-1240 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ []) ⟫ʷ
lem-CKc-box-at033440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx3-1240 ∷ CK40 ∷ []) (X4 ∷ Bx3-1240 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b0 = at 1 0 (CCZ012 ∷ CCZ012 ∷ []) (sym (wl0341 (lit c4))) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-box-perm-1324-at033440 c4) ▸
       at 0 2 (X4 ∷ Bx3-1420 ∷ X4 ∷ []) (sym (lem-Xb-box-at03243240 c4)) ▸
       at 3 2 (CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ012 ∷ []) (sym (wp1105 c4)) ▸
       at 2 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 3 2 (K0 ∷ CK40 ∷ S4 ∷ X4 ∷ []) (sym (wp0610 c4)) ▸
       at 6 2 (CCZ012 ∷ X4 ∷ []) (sym (c₃ (CCZ) (X ↑))) ▸
       at 1 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸ done

  b1 : Chain (X4 ∷ Bx3-1240 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ [])
  b1 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4) ▸
       at 5 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 4 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS01 ∷ CCZ034 ∷ []) (wp0001 c4) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ CCZ034 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ K0 ∷ Toff034 ∷ CCZ034 ∷ CZ03 ∷ CK40 ∷ CZ03 ∷ S4 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CCZ034 ∷ CS01 ∷ X4 ∷ CCZ012 ∷ [])
  b2 = at 5 2 (K0 ∷ Toff034 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp1106 c4) ▸
       at 8 2 (CZ03 ∷ CK40 ∷ CZ03 ∷ CCZ034 ∷ []) (wp1107 c4) ▸
       at 11 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 13 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 12 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ012 ∷ K0 ∷ Toff034 ∷ CCZ034 ∷ CZ03 ∷ CK40 ∷ CZ03 ∷ S4 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CCZ034 ∷ CS01 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff312 ∷ CCZ034 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ CCZ012 ∷ [])
  b3 = at 16 2 (CS01 ∷ CCZ034 ∷ []) (wp0001 c4) ▸
       at 12 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 5 7 (K0 ∷ CK40 ∷ S4 ∷ []) (sym (wp1108 c4)) ▸
       at 3 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 4 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 5 2 (CK40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CK40 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff312 ∷ []) (c₄ (Toffᵗ ↑) (S)) ▸
       at 7 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff312 ∷ CCZ034 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff312 ∷ CCZ012 ∷ K0 ∷ Toff034 ∷ CCZ034 ∷ CCZ034 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ CCZ012 ∷ [])
  b4 = at 3 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 2 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 3 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 4 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS01 ∷ CCZ034 ∷ []) (wp0001 c4) ▸
       at 2 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (K0 ∷ Toff034 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp1106 c4) ▸ done

  b5 : Chain (X4 ∷ Toff312 ∷ CCZ012 ∷ K0 ∷ Toff034 ∷ CCZ034 ∷ CCZ034 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ Toff312 ∷ CCZ012 ∷ K0 ∷ Toff034 ∷ CCZ034 ∷ CZ03 ∷ CK40 ∷ CZ03 ∷ S4 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ CCZ012 ∷ [])
  b5 = at 6 2 (CZ03 ∷ CK40 ∷ CZ03 ∷ CCZ034 ∷ []) (wp1107 c4) ▸
       at 9 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 11 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 10 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS01 ∷ CCZ034 ∷ []) (wp0001 c4) ▸ done

  b6 : Chain (X4 ∷ Toff312 ∷ CCZ012 ∷ K0 ∷ Toff034 ∷ CCZ034 ∷ CZ03 ∷ CK40 ∷ CZ03 ∷ S4 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ CCZ012 ∷ []) (X4 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ Bx3-1240 ∷ X4 ∷ CCZ012 ∷ [])
  b6 = at 10 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 7 (K0 ∷ CK40 ∷ S4 ∷ []) (sym (wp1108 c4)) ▸
       at 1 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 2 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 3 2 (CK40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CK40 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff312 ∷ []) (c₄ (Toffᵗ ↑) (S)) ▸
       at 5 2 (CCZ012 ∷ Toff312 ∷ []) (sym (wl0503 (lit c4))) ▸
       at 6 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ012 ∷ K0 ∷ CK40 ∷ S4 ∷ CCZ012 ∷ Bx3-1240 ∷ X4 ∷ CCZ012 ∷ []) (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ [])
  b7 = at 6 1 (Bx3-1420 ∷ []) (sym (lem-box-perm-1324-at03243240 c4)) ▸
       at 0 6 (CCZ012 ∷ CK40 ∷ CCZ012 ∷ X4 ∷ []) (sym (wp1109 c4)) ▸
       at 3 3 (Bx3-1420 ∷ CCZ012 ∷ []) (lem-Xb-box-at03243240 c4) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 3 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸ done
