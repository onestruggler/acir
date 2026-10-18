{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D023 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0155 ; wl0214 ; wl0230 ; wl0231 ; wl0245 ; wl0256 ; wl0263 ; wl0306 ; wl0321 ; wl0324 ; wl0341 ; wl0348 ; wl0393 ; wl0414 ; wl0415 ; wl0423 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0499 ; wl0501 ; wl0503 ; wl0512 ; wl0644 ; wl0645 ; wl0679 ; wl0704 ; wl0720 ; wl0725 ; wl0774 ; wl0777 ; wl0778 ; wl0779 ; wl0780 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0787 ; wl0788 ; wl0790 ; wl0846 ; wl0847 ; wl0861 ; wl0871 ; wl0888 ; wl1071 ; wl1189 ; wl1190 ; wl1222 ; wl1225 ; wl1226 ; wl1235 ; wl1236 ; wl1238 ; wl1239 ; wl1243 ; wl1247 ; wl1248 ; wl1249 ; wl1250 ; wl1251 ; wl1252 ; wl1253 ; wl1254 ; wl1255 ; wl1261 ; wl1262 ; wl1263 ; wl1264 ; wl1265 ; wl1266 ; wl1267 ; wl1268 ; wl1269 ; wl1270 ; wl1271 ; wl1272 ; wl1273 ; wl1274 ; wl1275 ; wl1276 ; wl1277 ; wl1278 ; wl1279 ; wl1280 ; wl1281 ; wl1282 ; wp0001 ; wp0002 ; wp0003 ; wp0041 ; wp0106 ; wp0107 ; wp0108 ; wp0124 ; wp0145 ; wp0149 ; wp0150 ; wp0151 ; wp0152 ; wp0161 ; wp0184 ; wp0185 ; wp0205 ; wp0221 ; wp0261 ; wp0279 ; wp0299 ; wp0321 ; wp0366 ; wp0521 ; wp0593 ; wp0610 ; wp0700 ; wp0701 ; wp0702 ; wp0703 ; wp0704 ; wp0706 ; wp0716 ; wp0729 ; wp0730 ; wp0738 ; wp0796 ; wp0797 ; wp0798 ; wp0981 ; wp1007 ; wp1027 ; wp1030 ; wp1049 ; wp1052 ; wp1061 ; wp1062 ; wp1074 ; wp1075 ; wp1076 ; wp1077 ; wp1078 ; wp1079 ; wp1080 ; wp1081 ; wp1082 ; wp1083 ; wp1084 ; wp1085 ; wp1086 ; wp1087 ; wp1088 ; wp1089 ; wp1090 ; wp1091 ; wp1092 ; wp1093 ; wp1094 ; wp1095 ; wp1096 ; wp1097 ; wp1098 ; wp1099 ; wp1100 ; wp1101 ; wp1102 ; wp1103 ; wp1104 ; wp1105 ; wp1106 ; wp1107 ; wp1108 ; wp1109)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-F0-at14213243 ; lem-box-tQ-at033440)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-box-cP-at0314213240 ; lem-box-tQ-at0314213240 ; lem-sym-ab-at0314213240 ; lem-sym-ab-at03243240 ; lem-tP-at0314213240)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F0-at01143043 ; lem-box-cP-at03243240 ; lem-box-perm-1324-at03243240 ; lem-box2-at0310243142 ; lem-sym-bc-at033440)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-CKc-box-at03103441 ; lem-CXbc-box-at0310213442 ; lem-CXcb-box-at0310213442 ; lem-S2-SBOX⟨3·1·42·0⟩ ; lem-box-perm-1324-at0310243142 ; lem-box-perm-1342-at03103441 ; lem-box-perm-1423-at0310243142 ; lem-box-tQ-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CX12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX24-CCZ013 ; lem-comm-CZ24-CCZ013)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd24-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CS02-CCZ134 ; lem-comm-CSd02-CCZ134 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd14-TOFF302 ; lem-comm-CX04-TOFF312 ; lem-comm-CZ02-TOFF314 ; lem-comm-CZ14-TOFF302 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ034-CX12 ; lem-comm-CCZ134-CX20 ; lem-comm-CS14-TOFF302 ; lem-comm-CX20-CCZ134 ; lem-comm-CZ02-CCZ134 ; lem-comm-SWAP04-BOX⟨3·21⟩ ; lem-comm-SWAP14-BOX⟨3·02⟩ ; lem-comm-TOFF301-CK42 ; lem-comm-TOFF302-CK41 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF312-CK40)
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


-- nat-SWbc @0310213442: 23 steps
lem-nat-SWbc-at0310213442 : Ws → ⟪ (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-nat-SWbc-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ Sw14 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 0 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 1 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 3 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 3 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 4 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 5 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ Sw14 ∷ CCZ034 ∷ Bx3-02 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ Sw14 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Sw14 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 7 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 8 2 (Toff304 ∷ Sw14 ∷ []) (wp0152 c4) ▸
       at 9 2 (CCZ034 ∷ Sw14 ∷ []) (sym (wp0151 c4)) ▸
       at 11 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 11 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 12 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Toff013 ∷ CCZ013 ∷ Bx3-02 ∷ Toff304 ∷ CCZ034 ∷ CCZ013 ∷ Toff013 ∷ Bx3-02 ∷ Sw14 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ Sw14 ∷ []) (Bx3-0412 ∷ [])
  b2 = at 13 2 (Toff013 ∷ Sw14 ∷ []) (wp0150 c4) ▸
       at 14 2 (CCZ013 ∷ Sw14 ∷ []) (sym (wp0149 c4)) ▸
       at 15 2 (Bx3-02 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨3·02⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx0-312 ∷ []) (refl) ▸
       at 5 6 (Bx0-312 ∷ []) (refl) ▸
       at 0 6 (Bx3-0412 ∷ []) (refl) ▸ done


-- sym-bc @0310213442: 2 steps
lem-sym-bc-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-sym-bc-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx3-0142 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0310213442 c4)) ▸
       at 0 3 (Bx3-0412 ∷ []) (lem-nat-SWbc-at0310213442 c4) ▸ done


-- box-perm-1324 @0310213442: 1 steps
lem-box-perm-1324-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4) ▸ done


-- Xb-box @0310243142: 18 steps
lem-Xb-box-at0310243142 : Ws → ⟪ (X4 ∷ Bx3-0412 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx3-0412 ∷ X4 ∷ []) (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX01 ∷ CCZ034 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 2 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (wl0512 (lit c4)) ▸
       at 1 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX01 ∷ CCZ034 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff312 ∷ X4 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ012 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 3 3 (X4 ∷ []) (wp0798 c4) ▸
       at 4 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 3 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1243 (lit c4))) ▸ done


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


-- nf-rel-266@0: 163 steps
lem-nf-rel-266at0 : Ws → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-nf-rel-266at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (run b20))))))))))))))))))))
  where
  b0 : Chain (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  b0 = at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 6 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 7 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 10 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 12 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 13 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 17 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸ done

  b1 : Chain (CK42 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ Sb3-0-41-2 ∷ CK41 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb3-1-42-0 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b1 = at 18 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 1 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 5 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 10 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 14 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 8 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 10 1 (CS02 ∷ []) (refl) ▸
       at 12 1 (CS02⁻ ∷ []) (refl) ▸ done

  b2 : Chain (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b2 = at 0 8 (Toff214 ∷ Toff124 ∷ []) (wl1267 (lit c4)) ▸
       at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 5 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 4 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 5 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 6 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b3 : Chain (Toff214 ∷ Toff124 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ Toff312 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b3 = at 8 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 9 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 10 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 4 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 5 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 5 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b4 : Chain (Toff214 ∷ Toff124 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ Toff312 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b4 = at 6 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 8 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 10 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b5 : Chain (Toff214 ∷ Toff124 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b5 = at 2 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 3 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 4 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 6 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 8 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 2 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b6 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Bx3-0412 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b6 = at 3 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 7 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 6 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 5 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 4 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 5 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b7 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Bx3-0412 ∷ Toff214 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b7 = at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 8 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 8 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 7 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 8 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b8 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b8 = at 12 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 13 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 7 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 8 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 10 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸ done

  b9 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b9 = at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 11 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 12 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 13 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 9 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 6 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 6 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 5 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸ done

  b10 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b10 = at 6 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 5 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸ done

  b11 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0241 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b11 = at 7 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 7 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 10 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 9 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 8 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 7 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 8 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 8 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸ done

  b12 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0241 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b12 = at 8 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 11 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 11 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 14 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 14 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 14 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b13 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b13 = at 16 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 13 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 12 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 12 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 11 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 12 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b14 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b14 = at 14 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 15 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 12 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 12 1 (Bx3-0241 ∷ []) (lem-box-perm-1423-at0310243142 c4) ▸
       at 12 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-0241 ∷ []) (lem-CKc-box-at03103441 c4) ▸
       at 15 1 (Bx3-0412 ∷ []) (lem-box-perm-1342-at03103441 c4) ▸
       at 15 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b15 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0412 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ [])
  b15 = at 18 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 17 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 16 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 15 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 16 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 16 1 (Bx3-0142 ∷ []) (lem-box-perm-1324-at0310243142 c4) ▸
       at 16 2 (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ []) (lem-CKc-box-at0310213442 c4) ▸
       at 19 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸ done

  b16 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0412 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CK42 ∷ S4 ∷ [])
  b16 = at 19 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 22 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 22 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 21 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 22 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 23 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 24 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 25 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b17 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK42 ∷ S4 ∷ [])
  b17 = at 21 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 20 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 20 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 19 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 20 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 21 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 22 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 23 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b18 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ [])
  b18 = at 19 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 20 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 20 1 (Bx3-0142 ∷ []) (lem-box-perm-1324-at0310243142 c4) ▸
       at 20 2 (CCZ012 ∷ CK42 ∷ CCZ012 ∷ Bx3-0142 ∷ []) (lem-CKc-box-at0310213442 c4) ▸
       at 23 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸
       at 23 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 26 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 25 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸ done

  b19 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ S4 ∷ CCZ034 ∷ Toff312 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b19 = at 24 2 (S4 ∷ Toff312 ∷ []) (sym (wl1268 (lit c4))) ▸
       at 23 2 (S4 ∷ CCZ034 ∷ []) (wp0981 c4) ▸
       at 24 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 3 (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp1030 c4) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 8 2 (CCZ124 ∷ CCZ012 ∷ []) (wp0205 c4) ▸
       at 9 2 [] (wl0341 (lit c4)) ▸
       at 10 2 (S4 ∷ CCZ012 ∷ []) (wl1269 (lit c4)) ▸ done

  b20 : Chain (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ []) (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ Bx3-0412 ∷ [])
  b20 = at 11 2 [] (wl0341 (lit c4)) ▸
       at 12 2 (CCZ124 ∷ CCZ012 ∷ []) (wp0205 c4) ▸
       at 13 2 [] (wl0341 (lit c4)) ▸ done


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


-- cQ @0312203441: 7 steps
lem-cQ-at0312203441 : Ws → ⟪ (CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at0312203441 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CS23 ∷ []) (sym (wl0790 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CS03⁻ ∷ []) (sym (wp0704 c4)) ▸
       at 1 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ CS03 ∷ []) (sym (wp0706 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl1270 (lit c4))) ▸ done


-- box-tQ @0312203441: 13 steps
lem-box-tQ-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at0312203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2041 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 0 2 (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) (wl1238 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at0312203441 c4) ▸
       at 2 4 (Toff302 ∷ []) (wl1239 (lit c4)) ▸ done


-- pairs @0314213240: 4 steps
lem-pairs-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-pairs-at0314213240 c4 = run b0
  where
  b0 : Chain (Bx3-4120 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 1 (Toff302 ∷ Bx3-4120 ∷ Toff302 ∷ []) (sym (lem-P-box-at0314213240 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 4 2 [] (wl0787 (lit c4)) ▸
       at 0 4 (Bx3-2041 ∷ []) (sym (lem-box-tQ-at0312203441 c4)) ▸ done


-- box-perm-3421 @03243240: 2 steps
lem-box-perm-3421-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-box-perm-3421-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4) ▸
       at 0 1 (Bx3-2041 ∷ []) (lem-pairs-at0314213240 c4) ▸ done


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


-- SWbc-box @0312203441: 11 steps
lem-SWbc-box-at0312203441 : Ws → ⟪ (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-SWbc-box-at0312203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (CX04 ∷ Bx3-2041 ∷ CX04 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX04 ∷ CX40 ∷ CX04 ∷ []) (sym (wp1084 c4)) ▸
       at 4 1 (CX04 ∷ CX40 ∷ CX04 ∷ []) (sym (wp1084 c4)) ▸
       at 2 3 (Bx3-2041 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312203441 c4) ▸
       at 3 2 (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1085 c4) ▸
       at 1 3 (Bx3-2041 ∷ CCZ124 ∷ []) (lem-CXcb-box-at0312203441 c4) ▸
       at 4 2 (CX04 ∷ CCZ012 ∷ []) (wp1086 c4) ▸
       at 3 2 (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1087 c4) ▸
       at 2 2 (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1087 c4) ▸ done

  b1 : Chain (CX04 ∷ Bx3-2041 ∷ CX04 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ []) (Bx3-2041 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp1088 c4) ▸
       at 0 3 (Bx3-2041 ∷ CCZ012 ∷ []) (lem-CXbc-box-at0312203441 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done


-- nat-SWbc @0312203441: 23 steps
lem-nat-SWbc-at0312203441 : Ws → ⟪ (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312203441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ Sw04 ∷ CCZ234 ∷ Bx3-21 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ Sw04 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 1 2 (Toff324 ∷ Sw04 ∷ []) (wp1090 c4) ▸
       at 3 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 3 2 (Toff203 ∷ Sw04 ∷ []) (wp1092 c4) ▸
       at 4 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 5 2 (Toff203 ∷ Sw04 ∷ []) (wp1092 c4) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ Sw04 ∷ CCZ234 ∷ Bx3-21 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ Sw04 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Sw04 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ Sw04 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 7 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 8 2 (Toff324 ∷ Sw04 ∷ []) (wp1090 c4) ▸
       at 9 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 11 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 11 2 (Toff203 ∷ Sw04 ∷ []) (wp1092 c4) ▸
       at 12 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff324 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Sw04 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ Sw04 ∷ []) (Bx3-2401 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw04 ∷ []) (wp1092 c4) ▸
       at 14 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 15 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 16 2 [] (wp1093 c4) ▸
       at 2 6 (Bx2-301 ∷ []) (refl) ▸
       at 5 6 (Bx2-301 ∷ []) (refl) ▸
       at 0 6 (Bx3-2401 ∷ []) (refl) ▸ done


-- sym-bc @0312203441: 2 steps
lem-sym-bc-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-sym-bc-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Sw04 ∷ Bx3-2041 ∷ Sw04 ∷ []) (sym (lem-SWbc-box-at0312203441 c4)) ▸
       at 0 3 (Bx3-2401 ∷ []) (lem-nat-SWbc-at0312203441 c4) ▸ done


-- box-perm-1324 @0312203441: 1 steps
lem-box-perm-1324-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-1324-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Bx3-2401 ∷ []) (lem-sym-bc-at0312203441 c4) ▸ done


-- cQ @0312243041: 7 steps
lem-cQ-at0312243041 : Ws → ⟪ (CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0312243041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 4 2 (CCZ013 ∷ CS23 ∷ []) (sym (wl0324 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CS34⁻ ∷ []) (sym (wp0184 c4)) ▸
       at 1 2 (CCZ013 ∷ CX24 ∷ []) (lem-comm-CX24-CCZ013 (lit c4)) ▸
       at 0 2 (CCZ013 ∷ CS34 ∷ []) (sym (wp0185 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done


-- tP @0312243041: 7 steps
lem-tP-at0312243041 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at0312243041 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at0312243041 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸
       at 1 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸ done


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


-- QVQ @0312243041: 3 steps
lem-QVQ-at0312243041 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at0312243041 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at0312243041 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done


-- box-cP @0312243041: 12 steps
lem-box-cP-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at0312243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2401 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at0312243041 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at0312243041 c4) ▸
       at 2 2 [] (wl0442 (lit c4)) ▸ done


-- Xb-box @0312243041: 18 steps
lem-Xb-box-at0312243041 : Ws → ⟪ (X4 ∷ Bx3-2401 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0312243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx3-2401 ∷ X4 ∷ []) (CCZ234 ∷ Toff301 ∷ X4 ∷ CZ23 ∷ CS01 ∷ CX20 ∷ CCZ234 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff301 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4) ▸
       at 0 2 (CCZ234 ∷ X4 ∷ CZ23 ∷ []) (sym (wl1274 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CZ23 ∷ CCZ012 ∷ []) (wl1275 (lit c4)) ▸
       at 1 2 (Toff301 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl1273 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff301 ∷ X4 ∷ CZ23 ∷ CS01 ∷ CX20 ∷ CCZ234 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff301 ∷ X4 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ X4 ∷ CCZ012 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ234 ∷ CX20 ∷ []) (sym (wp0366 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl1273 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CZ23 ∷ []) (sym (wl1071 (lit c4))) ▸
       at 2 2 (CCZ234 ∷ X4 ∷ CZ23 ∷ []) (sym (wl1274 (lit c4))) ▸
       at 3 3 (X4 ∷ []) (wl1276 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CCZ012 ∷ []) (wl1265 (lit c4)) ▸
       at 3 2 (Toff301 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (X))) ▸ done

  b2 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-2401 ∷ []) (sym (lem-box-cP-at0312243041 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1243 (lit c4))) ▸ done


-- box-tQ @0312243041: 13 steps
lem-box-tQ-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at0312243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2401 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wl0231 (lit c4))) ▸
       at 0 2 (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) (wl0846 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at0312243041 c4) ▸
       at 2 4 (Toff324 ∷ []) (wl0847 (lit c4)) ▸ done


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


-- SWbc-box @0312243041: 11 steps
lem-SWbc-box-at0312243041 : Ws → ⟪ (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-SWbc-box-at0312243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (CX40 ∷ Bx3-2401 ∷ CX40 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX40 ∷ CX04 ∷ CX40 ∷ []) (sym (wp1101 c4)) ▸
       at 4 1 (CX40 ∷ CX04 ∷ CX40 ∷ []) (sym (wp1101 c4)) ▸
       at 2 3 (Bx3-2401 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0312243041 c4) ▸
       at 3 2 (CX04 ∷ CCZ012 ∷ CCZ124 ∷ []) (wp1087 c4) ▸
       at 1 3 (Bx3-2401 ∷ CCZ012 ∷ []) (lem-CXcb-box-at0312243041 c4) ▸
       at 4 2 (CX40 ∷ CCZ124 ∷ []) (wp0321 c4) ▸
       at 3 2 (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1085 c4) ▸
       at 2 2 (CX40 ∷ CCZ124 ∷ CCZ012 ∷ []) (wp1085 c4) ▸ done

  b1 : Chain (CX40 ∷ Bx3-2401 ∷ CX40 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ CCZ012 ∷ CCZ124 ∷ []) (Bx3-2401 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp1102 c4) ▸
       at 0 3 (Bx3-2401 ∷ CCZ124 ∷ []) (lem-CXbc-box-at0312243041 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc @0312243041: 23 steps
lem-nat-SWbc-at0312243041 : Ws → ⟪ (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-nat-SWbc-at0312243041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ Sw04 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ Sw04 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff324 ∷ Bx2-301 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 1 2 (Toff302 ∷ Sw04 ∷ []) (wp1103 c4) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 3 2 (Toff234 ∷ Sw04 ∷ []) (wp1104 c4) ▸
       at 4 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 5 2 (Toff234 ∷ Sw04 ∷ []) (wp1104 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ Sw04 ∷ CCZ023 ∷ Bx3-21 ∷ Toff324 ∷ CCZ234 ∷ Bx2-301 ∷ Sw04 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Sw04 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Sw04 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 7 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 8 2 (Toff302 ∷ Sw04 ∷ []) (wp1103 c4) ▸
       at 9 2 (CCZ023 ∷ Sw04 ∷ []) (sym (wp1091 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx3-21 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 11 2 (Toff234 ∷ Sw04 ∷ []) (wp1104 c4) ▸
       at 12 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Sw04 ∷ Toff203 ∷ CCZ023 ∷ Bx3-21 ∷ Sw04 ∷ []) (Bx3-2041 ∷ [])
  b2 = at 13 2 (Toff234 ∷ Sw04 ∷ []) (wp1104 c4) ▸
       at 14 2 (CCZ234 ∷ Sw04 ∷ []) (sym (wp1089 c4)) ▸
       at 15 2 (Bx3-21 ∷ Sw04 ∷ []) (lem-comm-SWAP04-BOX⟨3·21⟩ (lit c4)) ▸
       at 16 2 [] (wp1093 c4) ▸
       at 2 6 (Bx2-341 ∷ []) (refl) ▸
       at 5 6 (Bx2-341 ∷ []) (refl) ▸
       at 0 6 (Bx3-2041 ∷ []) (refl) ▸ done


-- sym-bc @0312243041: 2 steps
lem-sym-bc-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-sym-bc-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 1 (Sw04 ∷ Bx3-2401 ∷ Sw04 ∷ []) (sym (lem-SWbc-box-at0312243041 c4)) ▸
       at 0 3 (Bx3-2041 ∷ []) (lem-nat-SWbc-at0312243041 c4) ▸ done


-- box-perm-1324 @0312243041: 1 steps
lem-box-perm-1324-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-box-perm-1324-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  b0 = at 0 1 (Bx3-2041 ∷ []) (lem-sym-bc-at0312243041 c4) ▸ done


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


-- tP @0312203441: 7 steps
lem-tP-at0312203441 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at0312203441 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at0312203441 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸
       at 1 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸ done


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


-- QVQ @0312203441: 3 steps
lem-QVQ-at0312203441 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at0312203441 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 4 (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at0312203441 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done


-- box-cP @0312203441: 12 steps
lem-box-cP-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at0312203441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2041 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-341 ∷ Toff302 ∷ CCZ023 ∷ Bx2-341 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx3-21 ∷ Toff234 ∷ CCZ234 ∷ Bx3-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 2 4 (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at0312203441 c4) ▸
       at 1 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at0312203441 c4) ▸
       at 2 2 [] (wl0787 (lit c4)) ▸ done


-- pairs @0312203441: 4 steps
lem-pairs-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-pairs-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-4120 ∷ [])
  b0 = at 0 1 (Toff314 ∷ Bx3-2041 ∷ Toff314 ∷ []) (sym (lem-P-box-at0312203441 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at0312203441 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-tQ-at0314213240 c4)) ▸ done


-- box-perm-4312 @0312203441: 2 steps
lem-box-perm-4312-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-4312-at0312203441 c4 = run b0
  where
  b0 : Chain (Bx3-2041 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Bx3-4120 ∷ []) (lem-pairs-at0312203441 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4) ▸ done


-- box-perm-1324 @033440: 1 steps
lem-box-perm-1324-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-1324-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Bx3-1420 ∷ []) (lem-sym-bc-at033440 c4) ▸ done


-- Xb-box @03243240: 18 steps
lem-Xb-box-at03243240 : Ws → ⟪ (X4 ∷ Bx3-1420 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at03243240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx3-1420 ∷ X4 ∷ []) (CCZ134 ∷ Toff302 ∷ X4 ∷ CZ13 ∷ CS02 ∷ CX12 ∷ CCZ134 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 0 2 (CCZ134 ∷ X4 ∷ CZ13 ∷ []) (sym (wl1279 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CZ13 ∷ CCZ012 ∷ []) (wl1280 (lit c4)) ▸
       at 1 2 (Toff302 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 7 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff302 ∷ X4 ∷ CZ13 ∷ CS02 ∷ CX12 ∷ CCZ134 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ X4 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X4 ∷ CCZ012 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CZ13 ∷ []) (sym (wl1281 (lit c4))) ▸
       at 2 2 (CCZ134 ∷ X4 ∷ CZ13 ∷ []) (sym (wl1279 (lit c4))) ▸
       at 3 3 (X4 ∷ []) (wl1282 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 3 2 (Toff302 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b2 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ X4 ∷ CCZ012 ∷ X4 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  b2 = at 0 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 1 3 (CCZ012 ∷ []) (sym (wl1243 (lit c4))) ▸ done


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

