{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D007 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0166 ; wl0175 ; wl0179 ; wl0415 ; wl0418 ; wl0419 ; wl0704 ; wl0915 ; wl0916 ; wl0921 ; wl0924 ; wl0926 ; wl0928 ; wl0932 ; wl0933 ; wl0934 ; wl0949 ; wl0950 ; wl0951 ; wp0011 ; wp0013 ; wp0090 ; wp0167 ; wp0251 ; wp0279 ; wp0341 ; wp0560 ; wp0565 ; wp0759 ; wp0761 ; wp0766 ; wp0767 ; wl0174 ; wl0311 ; wl0336 ; wl0348 ; wl0411 ; wl0452 ; wl0955 ; wl0956 ; wl0957 ; wl0958 ; wl0959 ; wl0960 ; wl0962 ; wl0963 ; wl0992 ; wp0014 ; wp0302 ; wp0342 ; wp0352 ; wp0771 ; wp0773 ; wp0774 ; wp0775 ; wp0776 ; wp0777 ; wl0157 ; wl0200 ; wl0254 ; wl0257 ; wp0049 ; wp0131 ; wl0184 ; wl0432 ; wl0433 ; wl0451 ; wl0521 ; wl0524 ; wl0836 ; wl1097 ; wl1098 ; wl1099 ; wl1100 ; wl1101 ; wp0294 ; wp0296 ; wp0301 ; wp0655 ; wp0894 ; wp0895 ; wp0896 ; wp0897 ; wp0898 ; wl0622 ; wl0623 ; wl0624 ; wl0625 ; wl1126 ; wl0226 ; wl0231 ; wl1155 ; wp0025 ; wp0026 ; wp0078 ; wp0214 ; wl0344 ; wp0129 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0702 ; wl0707 ; wl0749 ; wl0750 ; wl0781 ; wl0782 ; wl0846 ; wl0847 ; wl1174 ; wl1175 ; wp0163 ; wp0172 ; wp0205 ; wp0591 ; wp0983 ; wp0984 ; wp0985 ; wp0988 ; wp0992 ; wl0487 ; wl1192 ; wp0343 ; wl0298 ; wl0302 ; wl0414 ; wl0458 ; wl0508 ; wl1238 ; wl1239 ; wl1257 ; wl1258 ; wl1259 ; wl1260 ; wp0353 ; wp0354 ; wp0727 ; wp0728 ; wp1048 ; wp1066 ; wp1069 ; wp1070 ; wp1071 ; wp1072 ; wp1073 ; wl1271 ; wl1303 ; wp0262 ; wl0381 ; wl0383 ; wl0384 ; wl0426 ; wl0842 ; wl0843 ; wl0844 ; wl1319 ; wl1328 ; wl1329 ; wl1332 ; wp0563 ; wp1143 ; wp1153 ; wp1155 ; wp1156 ; wp1157 ; wp1158 ; wp1164 ; wp1165 ; wp1166 ; wp1167 ; wp1168 ; wp1175 ; wp1176 ; wp1177 ; wp1178 ; wp1179 ; wp1180 ; wp1181 ; wp1187 ; wl0473 ; wl0474 ; wl0640 ; wl0641 ; wl1341 ; wp0111 ; wp0550 ; wl1370 ; wl0527 ; wl1388 ; wl1389 ; wl1390 ; wl1391 ; wl1392 ; wp0056 ; wp0057 ; wp0231 ; wp0661 ; wp1223 ; wp1226 ; wp1227 ; wp1228 ; wp1232 ; wp1307 ; wl0453 ; wl0454 ; wl1472 ; wl1477 ; wl1478 ; wl1485 ; wl1486 ; wp0212 ; wp0303 ; wp0360 ; wp0368 ; wp1309 ; wp1310 ; wp1321 ; wp1325 ; wp1326 ; wp1327 ; wp1328 ; wp1329 ; wp1330 ; wp1331)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-perm-2134-at03102132 ; lem-box-tQ-at0210213443 ; lem-box-tQ-at0213243140 ; lem-box-tQ-at0220 ; lem-box-tQ-at03102132 ; lem-box-tQ-at0410213243 ; lem-box-tQ-at14233241 ; lem-cQ-at02102441 ; lem-cQ-at0213213440 ; lem-cQ-at0214203143 ; lem-cQ-at022330 ; lem-cQ-at02233440 ; lem-cQ-at022440 ; lem-cQ-at033440 ; lem-cQ-at12243143 ; lem-cQ-at14213243 ; lem-cQ-at1441 ; lem-cQ-at2442 ; lem-tP-at021021 ; lem-tP-at0210213443 ; lem-tP-at0213243140 ; lem-tP-at03102132 ; lem-tP-at032032)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-perm-2134-at0210243143 ; lem-box-tQ-at021021 ; lem-box-tQ-at0213243041 ; lem-box-tQ-at0214233041 ; lem-box-tQ-at0310213442 ; lem-cQ-at02102331 ; lem-cQ-at02132031 ; lem-cQ-at02132130 ; lem-cQ-at02142041 ; lem-cQ-at0310243241 ; lem-cQ-at031031 ; lem-cQ-at03103441 ; lem-cQ-at03122031 ; lem-cQ-at0312203441 ; lem-cQ-at03122130 ; lem-cQ-at0312243041 ; lem-cQ-at0314203241 ; lem-cQ-at0314213240 ; lem-cQ-at03143041 ; lem-cQ-at03143140 ; lem-cQ-at03243042 ; lem-cQ-at03243240 ; lem-cQ-at04103143 ; lem-cQ-at04122041 ; lem-cQ-at0412233041 ; lem-cQ-at04233042 ; lem-cQ-at142142 ; lem-tP-at0213243041 ; lem-tP-at0214233041 ; lem-tP-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-TOFF034 ; lem-comm-CSd12-TOFF034 ; lem-comm-CZ04-CCZ123 ; lem-comm-CZ12-CCZ034 ; lem-comm-CZ13-CCZ024 ; lem-comm-CZ14-CCZ023 ; lem-comm-CZ24-CCZ013 ; lem-comm-TOFF301-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-TOFF401 ; lem-comm-CS24-TOFF301 ; lem-comm-CSd23-TOFF401 ; lem-comm-CSd24-TOFF301 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ24-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CZ02-CCZ134)
open import Examples.Groups.Clifford+CS.Five.D.R006 using (lem-comm-SWAP03-BOX⟨2·14⟩ ; lem-comm-SWAP03-BOX⟨2·41⟩)

-- box-tQ @02233440: 13 steps
lem-box-tQ-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1340 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0915 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at02233440 c4) ▸
       at 2 4 (Toff213 ∷ []) (wl0916 (lit c4)) ▸ done

-- box-tQ @0213213440: 13 steps
lem-box-tQ-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0213213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3140 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0915 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at0213213440 c4) ▸
       at 2 4 (Toff213 ∷ []) (wl0916 (lit c4)) ▸ done

-- P-box @0213243140: 8 steps
lem-P-box-at0213243140 : Ws → ⟪ (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-P-box-at0213243140 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0213243140 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) (sym (wl0949 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0213243140 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ01 ∷ []) (sym (wl0950 (lit c4))) ▸
       at 2 2 (Toff234 ∷ CZ01 ∷ []) (c₂ (CZ) (Toff)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0951 (lit c4))) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done

-- VPQ @0213243140: 14 steps
lem-VPQ-at0213243140 : Ws → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S2⁻ ∷ []) (sym (c₂ (CS • CS • CS) (S • S • S))) ▸
       at 2 2 (CS01⁻ ∷ Toff234 ∷ []) (sym (c₂ (CS • CS • CS) (Toff))) ▸
       at 1 2 (CS01⁻ ∷ S2 ∷ []) (sym (c₂ (CS • CS • CS) (S))) ▸
       at 0 2 (CS01⁻ ∷ CS34⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((CS • CS • CS) ↑))) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243140 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS34⁻ ∷ []) (sym (c₃ (S ↑ ↑) (CS • CS • CS))) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (S2⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS))) ▸
       at 0 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸
       at 2 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸ done

-- CXbc-box @0220: 17 steps
lem-CXbc-box-at0220 : Ws → ⟪ (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX03 ∷ CCZ024 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ CX03 ∷ []) (wl0955 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (sym (wp0773 c4)) ▸
       at 3 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4) ▸
       at 2 2 (Toff201 ∷ CX03 ∷ []) (wl0955 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 9 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX03 ∷ CCZ024 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX03 ∷ []) (Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 6 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 2 (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (sym (wp0773 c4)) ▸
       at 4 3 (CX03 ∷ []) (wp0775 c4) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done

  b2 : Chain (Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-1034 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0761 c4)) ▸ done

-- CXcb-box @0220: 18 steps
lem-CXcb-box-at0220 : Ws → ⟪ (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) (Toff201 ∷ CCZ234 ∷ CX30 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ Toff201 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ234 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ CX30 ∷ Toff213 ∷ []) (wl0956 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Toff213 ∷ CCZ134 ∷ []) (sym (wl0957 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 8 2 (Toff201 ∷ CS14 ∷ []) (wp0777 c4) ▸
       at 7 2 (Toff201 ∷ CX13 ∷ []) (wl0958 (lit c4)) ▸
       at 6 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CX30 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ Toff201 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ234 ∷ CX30 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 5 2 (Toff201 ∷ CX13 ∷ []) (wl0958 (lit c4)) ▸
       at 4 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Toff213 ∷ []) (sym (wl0921 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CX30 ∷ Toff213 ∷ []) (wl0956 (lit c4)) ▸
       at 3 3 (CX30 ∷ []) (wl0959 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ134 ∷ []) (wl0960 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-1034 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wp0759 c4)) ▸ done

-- nat-SWbc @0220: 23 steps
lem-nat-SWbc-at0220 : Ws → ⟪ (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-nat-SWbc-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ Sw03 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw03 ∷ []) (wl0962 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 3 2 (Toff102 ∷ Sw03 ∷ []) (wl0963 (lit c4)) ▸
       at 4 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 5 2 (Toff102 ∷ Sw03 ∷ []) (wl0963 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ Sw03 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ Sw03 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Sw03 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 7 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 8 2 (Toff213 ∷ Sw03 ∷ []) (wl0962 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 11 2 (Toff102 ∷ Sw03 ∷ []) (wl0963 (lit c4)) ▸
       at 12 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Sw03 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Sw03 ∷ []) (Bx2-1304 ∷ [])
  b2 = at 13 2 (Toff102 ∷ Sw03 ∷ []) (wl0963 (lit c4)) ▸
       at 14 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 15 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx1-204 ∷ []) (refl) ▸
       at 5 6 (Bx1-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done

-- tP @022330: 7 steps
lem-tP-at022330 : Ws → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at022330 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at022330 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff204 ∷ []) (wp0014 c4) ▸
       at 1 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸ done

-- tP @14213243: 7 steps
lem-tP-at14213243 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at14213243 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at14213243 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸
       at 1 3 (Toff014 ∷ []) (wp0049 c4) ▸ done

-- S-sym-xt: 8 steps
lem-S-sym-xt : Ws → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-02-4 ∷ []) ⟫ʷ
lem-S-sym-xt c4 = run b0
  where
  b0 : Chain (Sb3-0-12-4 ∷ []) (Sb3-1-02-4 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 2 1 (CS04 ∷ []) (refl) ▸
       at 4 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 1 4 (Toff402 ∷ CS14 ∷ Toff402 ∷ CS14⁻ ∷ []) (sym (wp0894 c4)) ▸
       at 2 1 (Sb3-1-4-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-1-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-1-02-4 ∷ []) (refl) ▸ done

-- CXbc-box @03102132: 17 steps
lem-CXbc-box-at03102132 : Ws → ⟪ (CX12 ∷ Bx3-0124 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx3-0124 ∷ CX12 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX12 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CCZ234 ∷ CX01 ∷ CS04 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ CX12 ∷ []) (wl0524 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (sym (wl1097 (lit c4))) ▸
       at 3 2 (Toff301 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0895 c4) ▸
       at 2 2 (Toff301 ∷ CX12 ∷ []) (wl0524 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 9 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX12 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CCZ234 ∷ CX01 ∷ CS04 ∷ CX12 ∷ []) (Bx3-0124 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ134 ∷ []) (wl0960 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (sym (wl1097 (lit c4))) ▸
       at 4 3 (CX12 ∷ []) (wl1098 (lit c4)) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-tQ-at03102132 c4)) ▸ done

  b2 : Chain (Bx3-0124 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ []) (Bx3-0124 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸ done

-- CXcb-box @03102132: 18 steps
lem-CXcb-box-at03102132 : Ws → ⟪ (CX21 ∷ Bx3-0124 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx3-0124 ∷ CX21 ∷ []) (Toff301 ∷ CCZ234 ∷ CX21 ∷ Toff302 ∷ CS24 ∷ CX02 ∷ Toff301 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ234 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ CX21 ∷ Toff302 ∷ []) (wl1099 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 1 2 (CCZ234 ∷ CX21 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 4 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 8 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 7 2 (Toff301 ∷ CX02 ∷ []) (wl0521 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ CX21 ∷ Toff302 ∷ CS24 ∷ CX02 ∷ Toff301 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ234 ∷ CX21 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff301 ∷ CX02 ∷ []) (wl0521 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 3 2 (Toff301 ∷ Toff302 ∷ []) (sym (wl1100 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CX21 ∷ Toff302 ∷ []) (wl1099 (lit c4)) ▸
       at 3 3 (CX21 ∷ []) (wl1101 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 2 (CCZ234 ∷ CX21 ∷ []) (sym (wl0836 (lit c4))) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ []) (Bx3-0124 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-tQ-at03102132 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0898 c4)) ▸ done

-- tP @0214203143: 7 steps
lem-tP-at0214203143 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at0214203143 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 3 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at0214203143 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸
       at 1 3 (Toff204 ∷ []) (wp0014 c4) ▸ done

-- tP @022440: 7 steps
lem-tP-at022440 : Ws → ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ
lem-tP-at022440 c4 = run b0
  where
  b0 : Chain (Toff214 ∷ Toff203 ∷ []) (Toff203 ∷ Toff214 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at022440 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸
       at 1 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸ done

-- box-tQ @022440: 13 steps
lem-box-tQ-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at022440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1430 ∷ []) (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ124 ∷ Toff214 ∷ Bx1-230 ∷ Toff214 ∷ CCZ124 ∷ Bx1-230 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-10 ∷ Toff123 ∷ CCZ123 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ124 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 0 2 (Toff214 ∷ CCZ124 ∷ CZ14 ∷ []) (wl0622 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ124 ∷ []) (lem-cQ-at022440 c4) ▸
       at 2 4 (Toff214 ∷ []) (wl0623 (lit c4)) ▸ done

-- tP @02233440: 7 steps
lem-tP-at02233440 : Ws → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at02233440 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at02233440 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff204 ∷ []) (wp0014 c4) ▸
       at 1 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸ done

-- tP @1441: 7 steps
lem-tP-at1441 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at1441 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at1441 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸
       at 1 3 (Toff024 ∷ []) (wp0078 c4) ▸ done

-- tP @02102441: 7 steps
lem-tP-at02102441 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at02102441 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 3 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at02102441 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸
       at 1 3 (Toff204 ∷ []) (wp0014 c4) ▸ done

-- box-tQ @02102441: 13 steps
lem-box-tQ-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at02102441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0431 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 0 2 (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) (wp0025 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at02102441 c4) ▸
       at 2 4 (Toff204 ∷ []) (wp0026 c4) ▸ done

-- tP @2442: 7 steps
lem-tP-at2442 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at2442 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at2442 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸
       at 1 3 (Toff014 ∷ []) (wp0049 c4) ▸ done

-- tP @12243143: 7 steps
lem-tP-at12243143 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at12243143 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at12243143 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸
       at 1 3 (Toff024 ∷ []) (wp0078 c4) ▸ done

-- CXbc-box @14233241: 17 steps
lem-CXbc-box-at14233241 : Ws → ⟪ (CX32 ∷ Bx0-4321 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at14233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX32 ∷ Bx0-4321 ∷ CX32 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX32 ∷ CCZ013 ∷ CS13 ∷ CX43 ∷ CS13⁻ ∷ CCZ012 ∷ CX43 ∷ CS14 ∷ CX32 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233241 c4) ▸
       at 0 2 (Toff034 ∷ CX32 ∷ []) (wp0172 c4) ▸
       at 1 2 (CCZ012 ∷ CX32 ∷ CCZ013 ∷ []) (sym (wl1174 (lit c4))) ▸
       at 3 2 (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp0771 c4) ▸
       at 2 2 (Toff034 ∷ CX32 ∷ []) (wp0172 c4) ▸
       at 5 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 8 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CX32 ∷ CCZ013 ∷ CS13 ∷ CX43 ∷ CS13⁻ ∷ CCZ012 ∷ CX43 ∷ CS14 ∷ CX32 ∷ []) (Bx0-4321 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS13⁻ ∷ []) (sym (wl0992 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 5 2 (CCZ012 ∷ CS13 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CCZ013 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX32 ∷ CCZ013 ∷ []) (sym (wl1174 (lit c4))) ▸
       at 4 3 (CX32 ∷ []) (wl1175 (lit c4)) ▸
       at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸ done

  b2 : Chain (Bx0-4321 ∷ CX32 ∷ CCZ134 ∷ CX32 ∷ []) (Bx0-4321 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wl0254 (lit c4))) ▸ done

-- CXcb-box @14233241: 18 steps
lem-CXcb-box-at14233241 : Ws → ⟪ (CX23 ∷ Bx0-4321 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at14233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX23 ∷ Bx0-4321 ∷ CX23 ∷ []) (Toff034 ∷ CCZ012 ∷ CX23 ∷ Toff024 ∷ CS12 ∷ CX42 ∷ Toff034 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ CCZ012 ∷ CX23 ∷ [])
  b0 = at 1 1 (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233241 c4) ▸
       at 0 2 (Toff034 ∷ CX23 ∷ Toff024 ∷ []) (wp0983 c4) ▸
       at 2 2 (CCZ012 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0984 c4)) ▸
       at 1 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 4 1 (CS12 ∷ CX42 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ []) (wl0702 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS14 ∷ []) (wp0251 c4) ▸
       at 7 2 (Toff034 ∷ CX42 ∷ []) (wp0163 c4) ▸
       at 6 2 (Toff034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF034 (lit c4)) ▸ done

  b1 : Chain (Toff034 ∷ CCZ012 ∷ CX23 ∷ Toff024 ∷ CS12 ∷ CX42 ∷ Toff034 ∷ CS12⁻ ∷ CX42 ∷ CS14 ∷ CCZ012 ∷ CX23 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ [])
  b1 = at 5 2 (Toff034 ∷ CX42 ∷ []) (wp0163 c4) ▸
       at 4 2 (Toff034 ∷ CS12 ∷ []) (lem-comm-CS12-TOFF034 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0702 (lit c4))) ▸
       at 3 2 (Toff034 ∷ Toff024 ∷ []) (wp0591 c4) ▸
       at 2 2 (Toff034 ∷ CX23 ∷ Toff024 ∷ []) (wp0983 c4) ▸
       at 3 3 (CX23 ∷ []) (wp0985 c4) ▸
       at 4 2 (CCZ012 ∷ CCZ124 ∷ []) (sym (wp0205 c4)) ▸
       at 3 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸ done

  b2 : Chain (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX23 ∷ CCZ124 ∷ CX23 ∷ []) (Bx0-4321 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-4321 ∷ []) (sym (lem-box-tQ-at14233241 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0257 (lit c4))) ▸ done

-- box-tQ @03143140: 13 steps
lem-box-tQ-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4210 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-310 ∷ Toff324 ∷ CCZ234 ∷ Bx4-310 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0988 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff413 ∷ Bx3-40 ∷ Toff413 ∷ CCZ134 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ134 ∷ Toff413 ∷ CZ04 ∷ Toff413 ∷ CCZ134 ∷ CZ04 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0988 c4)) ▸
       at 0 2 (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) (wl0846 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at03143140 c4) ▸
       at 2 4 (Toff324 ∷ []) (wl0847 (lit c4)) ▸ done

-- tP @0314213240: 7 steps
lem-tP-at0314213240 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at0314213240 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213240 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸
       at 1 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸ done

-- box-tQ @03243240: 13 steps
lem-box-tQ-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at03243240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1420 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (wl0749 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at03243240 c4) ▸
       at 2 4 (Toff314 ∷ []) (wl0750 (lit c4)) ▸ done

-- box-tQ @0314213240: 13 steps
lem-box-tQ-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at0314213240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4120 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx4-320 ∷ Toff314 ∷ CCZ134 ∷ Bx4-320 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-40 ∷ Toff423 ∷ CCZ234 ∷ Bx3-40 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ234 ∷ Toff423 ∷ CZ04 ∷ Toff423 ∷ CCZ234 ∷ CZ04 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0992 c4)) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (wl0749 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at0314213240 c4) ▸
       at 2 4 (Toff314 ∷ []) (wl0750 (lit c4)) ▸ done

-- tP @03143140: 7 steps
lem-tP-at03143140 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at03143140 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at03143140 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸
       at 1 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸ done

-- tP @03243240: 7 steps
lem-tP-at03243240 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at03243240 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at03243240 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸
       at 1 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸ done

-- tP @033440: 7 steps
lem-tP-at033440 : Ws → ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-tP-at033440 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (sym (wl0487 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0343 c4)) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at033440 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff304 ∷ []) (wp0343 c4) ▸
       at 1 3 (Toff312 ∷ []) (wl0487 (lit c4)) ▸ done

-- box-tQ @03103441: 13 steps
lem-box-tQ-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at03103441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0241 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-341 ∷ Toff302 ∷ CCZ023 ∷ Bx0-341 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-01 ∷ Toff034 ∷ CCZ034 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ034 ∷ Toff034 ∷ CZ01 ∷ Toff034 ∷ CCZ034 ∷ CZ01 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1048 c4) ▸
       at 0 2 (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) (wl1238 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at03103441 c4) ▸
       at 2 4 (Toff302 ∷ []) (wl1239 (lit c4)) ▸ done

-- tP @0310243241: 7 steps
lem-tP-at0310243241 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0310243241 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0343 c4)) ▸
       at 3 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (sym (wl0487 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0310243241 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff312 ∷ []) (wl0487 (lit c4)) ▸
       at 1 3 (Toff304 ∷ []) (wp0343 c4) ▸ done

-- box-tQ @0310243241: 13 steps
lem-box-tQ-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0310243241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0421 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0353 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0310243241 c4) ▸
       at 2 4 (Toff304 ∷ []) (wp0354 c4) ▸ done

-- tP @03103441: 7 steps
lem-tP-at03103441 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at03103441 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at03103441 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸
       at 1 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸ done

-- CXbc-box @0310213442: 17 steps
lem-CXbc-box-at0310213442 : Ws → ⟪ (CX14 ∷ Bx3-0142 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ012 ∷ []) ⟫ʷ
lem-CXbc-box-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx3-0142 ∷ CX14 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX14 ∷ CCZ123 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ234 ∷ CX01 ∷ CS02 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 0 2 (Toff301 ∷ CX14 ∷ []) (wp1069 c4) ▸
       at 1 2 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (sym (wl1257 (lit c4))) ▸
       at 3 2 (Toff301 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1258 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CX14 ∷ []) (wp1069 c4) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX14 ∷ CCZ123 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ234 ∷ CX01 ∷ CS02 ∷ CX14 ∷ []) (Bx3-0142 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS12⁻ ∷ []) (sym (wl0414 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (sym (wl1257 (lit c4))) ▸
       at 4 3 (CX14 ∷ []) (wl1259 (lit c4)) ▸
       at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸ done

  b2 : Chain (Bx3-0142 ∷ CX14 ∷ CCZ012 ∷ CX14 ∷ []) (Bx3-0142 ∷ CCZ012 ∷ [])
  b2 = at 1 3 (CCZ012 ∷ []) (sym (wp0728 c4)) ▸ done

-- CXcb-box @0310213442: 18 steps
lem-CXcb-box-at0310213442 : Ws → ⟪ (CX41 ∷ Bx3-0142 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at0310213442 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx3-0142 ∷ CX41 ∷ []) (Toff301 ∷ CCZ234 ∷ CX41 ∷ Toff304 ∷ CS24 ∷ CX04 ∷ Toff301 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ234 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 0 2 (Toff301 ∷ CX41 ∷ Toff304 ∷ []) (wp1070 c4) ▸
       at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 1 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 4 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 8 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 7 2 (Toff301 ∷ CX04 ∷ []) (wp1072 c4) ▸
       at 6 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ CX41 ∷ Toff304 ∷ CS24 ∷ CX04 ∷ Toff301 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ234 ∷ CX41 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff301 ∷ CX04 ∷ []) (wp1072 c4) ▸
       at 4 2 (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 3 2 (Toff301 ∷ Toff304 ∷ []) (sym (wp1066 c4)) ▸
       at 2 2 (Toff301 ∷ CX41 ∷ Toff304 ∷ []) (wp1070 c4) ▸
       at 3 3 (CX41 ∷ []) (wp1073 c4) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX41 ∷ CCZ024 ∷ CX41 ∷ []) (Bx3-0142 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0727 c4)) ▸ done

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

-- box-tQ @03122031: 13 steps
lem-box-tQ-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at03122031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2014 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 0 2 (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) (wl1238 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at03122031 c4) ▸
       at 2 4 (Toff302 ∷ []) (wl1239 (lit c4)) ▸ done

-- box-tQ @031031: 13 steps
lem-box-tQ-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at031031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0214 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff302 ∷ Bx0-314 ∷ Toff302 ∷ CCZ023 ∷ Bx0-314 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 5 1 (CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ CZ04 ∷ Toff013 ∷ CCZ013 ∷ CZ04 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp0262 c4) ▸
       at 0 2 (Toff302 ∷ CCZ023 ∷ CZ02 ∷ []) (wl1238 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at031031 c4) ▸
       at 2 4 (Toff302 ∷ []) (wl1239 (lit c4)) ▸ done

-- tP @031031: 7 steps
lem-tP-at031031 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at031031 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at031031 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸
       at 1 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸ done

-- P-box @03102132: 8 steps
lem-P-box-at03102132 : Ws → ⟪ (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-P-box-at03102132 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at03102132 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) (sym (wl0842 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at03102132 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ24 ∷ []) (sym (wl0843 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4)) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0844 (lit c4))) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-tQ-at03102132 c4)) ▸ done

-- box-tQ @03143041: 13 steps
lem-box-tQ-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) ⟫ʷ
lem-box-tQ-at03143041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4201 ∷ []) (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff324 ∷ Bx4-301 ∷ Toff324 ∷ CCZ234 ∷ Bx4-301 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx3-41 ∷ Toff403 ∷ CCZ034 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 0 2 (Toff324 ∷ CCZ234 ∷ CZ24 ∷ []) (wl0846 (lit c4)) ▸
       at 2 2 (CCZ013 ∷ CZ24 ∷ []) (lem-comm-CZ24-CCZ013 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at03143041 c4) ▸
       at 2 4 (Toff324 ∷ []) (wl0847 (lit c4)) ▸ done

-- box-tQ @0314203241: 13 steps
lem-box-tQ-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4021 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 0 2 (Toff304 ∷ CCZ034 ∷ CZ04 ∷ []) (wp0353 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0314203241 c4) ▸
       at 2 4 (Toff304 ∷ []) (wp0354 c4) ▸ done

-- box-tQ @02142041: 13 steps
lem-box-tQ-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4031 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 0 2 (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) (wp0025 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at02142041 c4) ▸
       at 2 4 (Toff204 ∷ []) (wp0026 c4) ▸ done

-- nat-SWbc @02142041: 23 steps
lem-nat-SWbc-at02142041 : Ws → ⟪ (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-nat-SWbc-at02142041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-4031 ∷ Sw03 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ Sw03 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 1 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 3 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 3 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 4 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 5 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ Sw03 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ Sw03 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Sw03 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 7 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 8 2 (Toff234 ∷ Sw03 ∷ []) (wp1156 c4) ▸
       at 9 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 11 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 11 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 12 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Sw03 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Sw03 ∷ []) (Bx2-4301 ∷ [])
  b2 = at 13 2 (Toff402 ∷ Sw03 ∷ []) (wp1158 c4) ▸
       at 14 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 15 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx4-201 ∷ []) (refl) ▸
       at 5 6 (Bx4-201 ∷ []) (refl) ▸
       at 0 6 (Bx2-4301 ∷ []) (refl) ▸ done

-- VPQ @0214233041: 14 steps
lem-VPQ-at0214233041 : Ws → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0214233041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S2⁻ ∷ []) (sym (c₂ (CS • CS • CS) (S • S • S))) ▸
       at 2 2 (CS01⁻ ∷ Toff234 ∷ []) (sym (c₂ (CS • CS • CS) (Toff))) ▸
       at 1 2 (CS01⁻ ∷ S2 ∷ []) (sym (c₂ (CS • CS • CS) (S))) ▸
       at 0 2 (CS01⁻ ∷ CS34⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((CS • CS • CS) ↑))) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0214233041 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS34⁻ ∷ []) (sym (c₃ (S ↑ ↑) (CS • CS • CS))) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (S2⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS))) ▸
       at 0 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸
       at 2 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸ done

-- P-box @0214233041: 8 steps
lem-P-box-at0214233041 : Ws → ⟪ (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-P-box-at0214233041 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-4301 ∷ Toff201 ∷ []) (Bx2-4301 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0214233041 c4) ▸
       at 0 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0214233041 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) (sym (wl0949 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0214233041 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ01 ∷ []) (sym (wl0950 (lit c4))) ▸
       at 2 2 (Toff234 ∷ CZ01 ∷ []) (c₂ (CZ) (Toff)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0951 (lit c4))) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-tQ-at0214233041 c4)) ▸ done

-- CXbc-box @0210213443: 17 steps
lem-CXbc-box-at0210213443 : Ws → ⟪ (CX14 ∷ Bx2-0143 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0210213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-0143 ∷ CX14 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX14 ∷ CCZ123 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ234 ∷ CX01 ∷ CS03 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ CX14 ∷ []) (wp1164 c4) ▸
       at 1 2 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (sym (wl1257 (lit c4))) ▸
       at 3 2 (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1328 (lit c4)) ▸
       at 2 2 (Toff201 ∷ CX14 ∷ []) (wp1164 c4) ▸
       at 5 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX14 ∷ CCZ123 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ234 ∷ CX01 ∷ CS03 ∷ CX14 ∷ []) (Bx2-0143 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX14 ∷ CCZ123 ∷ []) (sym (wl1257 (lit c4))) ▸
       at 4 3 (CX14 ∷ []) (wl1259 (lit c4)) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸ done

  b2 : Chain (Bx2-0143 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-0143 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wp0565 c4)) ▸ done

-- CXcb-box @0210213443: 18 steps
lem-CXcb-box-at0210213443 : Ws → ⟪ (CX41 ∷ Bx2-0143 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0210213443 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-0143 ∷ CX41 ∷ []) (Toff201 ∷ CCZ234 ∷ CX41 ∷ Toff204 ∷ CS34 ∷ CX04 ∷ Toff201 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ234 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ CX41 ∷ Toff204 ∷ []) (wp1165 c4) ▸
       at 2 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 1 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸
       at 4 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX04 ∷ []) (wp1167 c4) ▸
       at 6 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CX41 ∷ Toff204 ∷ CS34 ∷ CX04 ∷ Toff201 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ234 ∷ CX41 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff201 ∷ CX04 ∷ []) (wp1167 c4) ▸
       at 4 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 3 2 (Toff201 ∷ Toff204 ∷ []) (sym (wp0563 c4)) ▸
       at 2 2 (Toff201 ∷ CX41 ∷ Toff204 ∷ []) (wp1165 c4) ▸
       at 3 3 (CX41 ∷ []) (wp1168 c4) ▸
       at 4 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 3 2 (CCZ234 ∷ CX41 ∷ []) (sym (wl0302 (lit c4))) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-0143 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp0560 c4)) ▸ done

-- P-box @0210213443: 8 steps
lem-P-box-at0210213443 : Ws → ⟪ (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-P-box-at0210213443 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx2-0143 ∷ Toff234 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0210213443 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) (sym (wl0932 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0210213443 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ34 ∷ []) (sym (wl0933 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0934 (lit c4))) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸ done

-- CXbc-box @0214233041: 17 steps
lem-CXbc-box-at0214233041 : Ws → ⟪ (CX30 ∷ Bx2-4301 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at0214233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-4301 ∷ CX30 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX30 ∷ CCZ123 ∷ CS13 ∷ CX43 ∷ CS13⁻ ∷ CCZ012 ∷ CX43 ∷ CS14 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0214233041 c4) ▸
       at 0 2 (Toff234 ∷ CX30 ∷ []) (wp1175 c4) ▸
       at 1 2 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 3 2 (Toff234 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0426 (lit c4)) ▸
       at 2 2 (Toff234 ∷ CX30 ∷ []) (wp1175 c4) ▸
       at 5 1 (CS13 ∷ CX43 ∷ CS13⁻ ∷ CX43 ∷ CS14 ∷ []) (wl0707 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 8 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX30 ∷ CCZ123 ∷ CS13 ∷ CX43 ∷ CS13⁻ ∷ CCZ012 ∷ CX43 ∷ CS14 ∷ CX30 ∷ []) (Bx2-4301 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS13⁻ ∷ []) (sym (wl0992 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CX43 ∷ []) (sym (c₃ (CCZ) (CX₁₀))) ▸
       at 5 2 (CCZ012 ∷ CS13 ∷ []) (sym (wl0311 (lit c4))) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0707 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CCZ123 ∷ []) (sym (wl0298 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX30 ∷ CCZ123 ∷ []) (sym (wl0383 (lit c4))) ▸
       at 4 3 (CX30 ∷ []) (wl0384 (lit c4)) ▸
       at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-tQ-at0214233041 c4)) ▸ done

  b2 : Chain (Bx2-4301 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-4301 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wp0759 c4)) ▸ done

-- CXcb-box @0214233041: 18 steps
lem-CXcb-box-at0214233041 : Ws → ⟪ (CX03 ∷ Bx2-4301 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0214233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-4301 ∷ CX03 ∷ []) (Toff234 ∷ CCZ012 ∷ CX03 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ Toff234 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ012 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0214233041 c4) ▸
       at 0 2 (Toff234 ∷ CX03 ∷ Toff204 ∷ []) (wp1176 c4) ▸
       at 2 2 (CCZ012 ∷ Toff204 ∷ CCZ014 ∷ []) (sym (wp1177 c4)) ▸
       at 1 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (Toff234 ∷ CS14 ∷ []) (wl1332 (lit c4)) ▸
       at 7 2 (Toff234 ∷ CX40 ∷ []) (wp1178 c4) ▸
       at 6 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ CX03 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ Toff234 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ012 ∷ CX03 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 5 2 (Toff234 ∷ CX40 ∷ []) (wp1178 c4) ▸
       at 4 2 (Toff234 ∷ CS01 ∷ []) (c₂ (CS) (Toff)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff234 ∷ Toff204 ∷ []) (wp1153 c4) ▸
       at 2 2 (Toff234 ∷ CX03 ∷ Toff204 ∷ []) (wp1176 c4) ▸
       at 3 3 (CX03 ∷ []) (wp1179 c4) ▸
       at 4 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 3 2 (CCZ012 ∷ CX03 ∷ []) (sym (wl0381 (lit c4))) ▸ done

  b2 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-4301 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-4301 ∷ []) (sym (lem-box-tQ-at0214233041 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0761 c4)) ▸ done

-- nat-SWbc @0214233041: 23 steps
lem-nat-SWbc-at0214233041 : Ws → ⟪ (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-nat-SWbc-at0214233041 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-4301 ∷ Sw03 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ Sw03 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx4-201 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 1 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 3 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 3 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 4 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 5 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ Sw03 ∷ CCZ024 ∷ Bx2-41 ∷ Toff234 ∷ CCZ234 ∷ Bx4-201 ∷ Sw03 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Sw03 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 7 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 8 2 (Toff204 ∷ Sw03 ∷ []) (wp1180 c4) ▸
       at 9 2 (CCZ024 ∷ Sw03 ∷ []) (sym (wp1157 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff402 ∷ Bx2-41 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 11 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 12 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Sw03 ∷ Toff402 ∷ CCZ024 ∷ Bx2-41 ∷ Sw03 ∷ []) (Bx2-4031 ∷ [])
  b2 = at 13 2 (Toff423 ∷ Sw03 ∷ []) (wp1181 c4) ▸
       at 14 2 (CCZ234 ∷ Sw03 ∷ []) (sym (wp1155 c4)) ▸
       at 15 2 (Bx2-41 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·41⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx4-231 ∷ []) (refl) ▸
       at 5 6 (Bx4-231 ∷ []) (refl) ▸
       at 0 6 (Bx2-4031 ∷ []) (refl) ▸ done

-- box-tQ @02132130: 13 steps
lem-box-tQ-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at02132130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3104 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0915 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at02132130 c4) ▸
       at 2 4 (Toff213 ∷ []) (wl0916 (lit c4)) ▸ done

-- tP @03143041: 7 steps
lem-tP-at03143041 : Ws → ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ
lem-tP-at03143041 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Toff301 ∷ []) (Toff301 ∷ Toff324 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ234 ∷ []) (lem-cQ-at03143041 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸
       at 1 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸ done

-- tP @02132031: 7 steps
lem-tP-at02132031 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at02132031 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at02132031 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸
       at 1 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸ done

-- P-box @0310213442: 8 steps
lem-P-box-at0310213442 : Ws → ⟪ (Toff324 ∷ Bx3-0142 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-P-box-at0310213442 c4 = run b0
  where
  b0 : Chain (Toff324 ∷ Bx3-0142 ∷ Toff324 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 0 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at0310213442 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ24 ∷ Toff324 ∷ []) (sym (wl0842 (lit c4))) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (sym (lem-tP-at0310213442 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ24 ∷ []) (sym (wl0843 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CZ24 ∷ []) (lem-comm-CZ24-TOFF301 (lit c4)) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0844 (lit c4))) ▸
       at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸ done

-- VPQ @0310213442: 14 steps
lem-VPQ-at0310213442 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ
lem-VPQ-at0310213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 4 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 3 2 (CS24⁻ ∷ S3⁻ ∷ []) (sym (wl0439 (lit c4))) ▸
       at 2 2 (CS24⁻ ∷ Toff301 ∷ []) (lem-comm-TOFF301-CSd24 (lit c4)) ▸
       at 1 2 (CS24⁻ ∷ S3 ∷ []) (sym (wl0440 (lit c4))) ▸
       at 0 2 (CS24⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4) ▸ done

  b1 : Chain (CS24⁻ ∷ CS01⁻ ∷ S3 ∷ Toff324 ∷ Toff301 ∷ S3⁻ ∷ []) (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S ↑)) ▸
       at 2 2 (Toff324 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (S3⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((S • S • S) ↑)) ▸
       at 0 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸
       at 2 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸ done

-- box-tQ @02132031: 13 steps
lem-box-tQ-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3014 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 4 1 (CZ34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 7 1 (CZ34 ∷ []) (refl) ▸
       at 10 1 (CZ34 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 0 2 (Toff203 ∷ CCZ023 ∷ CZ03 ∷ []) (wl0640 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at02132031 c4) ▸
       at 2 4 (Toff203 ∷ []) (wl0641 (lit c4)) ▸ done

-- tP @02132130: 7 steps
lem-tP-at02132130 : Ws → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at02132130 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at02132130 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff204 ∷ []) (wp0014 c4) ▸
       at 1 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸ done

-- VPQ @0213243041: 14 steps
lem-VPQ-at0213243041 : Ws → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0213243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S2⁻ ∷ []) (sym (c₂ (CS • CS • CS) (S • S • S))) ▸
       at 2 2 (CS01⁻ ∷ Toff234 ∷ []) (sym (c₂ (CS • CS • CS) (Toff))) ▸
       at 1 2 (CS01⁻ ∷ S2 ∷ []) (sym (c₂ (CS • CS • CS) (S))) ▸
       at 0 2 (CS01⁻ ∷ CS34⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((CS • CS • CS) ↑))) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243041 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS34⁻ ∷ []) (sym (c₃ (S ↑ ↑) (CS • CS • CS))) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (S2⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS))) ▸
       at 0 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸
       at 2 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸ done

-- P-box @0213243041: 8 steps
lem-P-box-at0213243041 : Ws → ⟪ (Toff201 ∷ Bx2-3401 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-P-box-at0213243041 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3401 ∷ Toff201 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243041 c4) ▸
       at 0 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0213243041 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) (sym (wl0949 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0213243041 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ01 ∷ []) (sym (wl0950 (lit c4))) ▸
       at 2 2 (Toff234 ∷ CZ01 ∷ []) (c₂ (CZ) (Toff)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0951 (lit c4))) ▸
       at 0 4 (Bx2-3401 ∷ []) (sym (lem-box-tQ-at0213243041 c4)) ▸ done

-- box-tQ @03122130: 13 steps
lem-box-tQ-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) ⟫ʷ
lem-box-tQ-at03122130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-2104 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 0 2 (Toff312 ∷ CCZ123 ∷ CZ12 ∷ []) (wl0473 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at03122130 c4) ▸
       at 2 4 (Toff312 ∷ []) (wl0474 (lit c4)) ▸ done

-- P-box @021021: 8 steps
lem-P-box-at021021 : Ws → ⟪ (Toff234 ∷ Bx2-0134 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-P-box-at021021 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx2-0134 ∷ Toff234 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at021021 c4) ▸
       at 0 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at021021 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) (sym (wl0932 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at021021 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ34 ∷ []) (sym (wl0933 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0934 (lit c4))) ▸
       at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-tQ-at021021 c4)) ▸ done

-- tP @03122031: 7 steps
lem-tP-at03122031 : Ws → ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ
lem-tP-at03122031 c4 = run b0
  where
  b0 : Chain (Toff302 ∷ Toff314 ∷ []) (Toff314 ∷ Toff302 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ023 ∷ []) (lem-cQ-at03122031 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸
       at 1 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸ done

-- tP @03122130: 7 steps
lem-tP-at03122130 : Ws → ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ
lem-tP-at03122130 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Toff304 ∷ []) (Toff304 ∷ Toff312 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (sym (wl0487 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0343 c4)) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CCZ123 ∷ []) (lem-cQ-at03122130 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff304 ∷ []) (wp0343 c4) ▸
       at 1 3 (Toff312 ∷ []) (wl0487 (lit c4)) ▸ done

-- t-cP @03102132: 5 steps
lem-t-cP-at03102132 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-t-cP-at03102132 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 2 (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) (sym (wl1370 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at03102132 c4) ▸
       at 2 3 (CCZ013 ∷ Toff301 ∷ []) (sym (wl1192 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at03102132 c4) ▸ done

-- tP @02142041: 7 steps
lem-tP-at02142041 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at02142041 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 3 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at02142041 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸
       at 1 3 (Toff204 ∷ []) (wp0014 c4) ▸ done

-- tP @0314203241: 7 steps
lem-tP-at0314203241 : Ws → ⟪ (Toff304 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-tP-at0314203241 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Toff312 ∷ []) (Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ034 ∷ K3⁻ ∷ []) (sym (wp0343 c4)) ▸
       at 3 1 (K3 ∷ CCZ123 ∷ K3⁻ ∷ []) (sym (wl0487 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ034 ∷ []) (lem-cQ-at0314203241 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff312 ∷ []) (wl0487 (lit c4)) ▸
       at 1 3 (Toff304 ∷ []) (wp0343 c4) ▸ done

-- CXbc-box @021021: 17 steps
lem-CXbc-box-at021021 : Ws → ⟪ (CX13 ∷ Bx2-0134 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at021021 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx2-0134 ∷ CX13 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX13 ∷ CCZ124 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CCZ234 ∷ CX01 ∷ CS04 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at021021 c4) ▸
       at 0 2 (Toff201 ∷ CX13 ∷ []) (wl0958 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CX13 ∷ CCZ124 ∷ []) (sym (wl1388 (lit c4))) ▸
       at 3 2 (Toff201 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp1223 c4) ▸
       at 2 2 (Toff201 ∷ CX13 ∷ []) (wl0958 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 9 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX13 ∷ CCZ124 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CCZ234 ∷ CX01 ∷ CS04 ∷ CX13 ∷ []) (Bx2-0134 ∷ CX13 ∷ CCZ014 ∷ CX13 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ124 ∷ []) (wl0527 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX13 ∷ CCZ124 ∷ []) (sym (wl1388 (lit c4))) ▸
       at 4 3 (CX13 ∷ []) (wl1389 (lit c4)) ▸
       at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-tQ-at021021 c4)) ▸ done

  b2 : Chain (Bx2-0134 ∷ CX13 ∷ CCZ014 ∷ CX13 ∷ []) (Bx2-0134 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp1226 c4)) ▸ done

-- CXcb-box @021021: 18 steps
lem-CXcb-box-at021021 : Ws → ⟪ (CX31 ∷ Bx2-0134 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at021021 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx2-0134 ∷ CX31 ∷ []) (Toff201 ∷ CCZ234 ∷ CX31 ∷ Toff203 ∷ CS34 ∷ CX03 ∷ Toff201 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ CCZ234 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at021021 c4) ▸
       at 0 2 (Toff201 ∷ CX31 ∷ Toff203 ∷ []) (wl1390 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Toff203 ∷ CCZ034 ∷ []) (sym (wp1227 c4)) ▸
       at 1 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 4 1 (CS34 ∷ CX03 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ []) (wp0231 c4) ▸
       at 8 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 7 2 (Toff201 ∷ CX03 ∷ []) (wl0955 (lit c4)) ▸
       at 6 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CX31 ∷ Toff203 ∷ CS34 ∷ CX03 ∷ Toff201 ∷ CS34⁻ ∷ CX03 ∷ CS04 ∷ CCZ234 ∷ CX31 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX31 ∷ CCZ034 ∷ CX31 ∷ [])
  b1 = at 5 2 (Toff201 ∷ CX03 ∷ []) (wl0955 (lit c4)) ▸
       at 4 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0231 c4)) ▸
       at 3 2 (Toff201 ∷ Toff203 ∷ []) (sym (wl1391 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CX31 ∷ Toff203 ∷ []) (wl1390 (lit c4)) ▸
       at 3 3 (CX31 ∷ []) (wl1392 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 3 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX31 ∷ CCZ034 ∷ CX31 ∷ []) (Bx2-0134 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-tQ-at021021 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp1228 c4)) ▸ done

-- tP @02102331: 7 steps
lem-tP-at02102331 : Ws → ⟪ (Toff203 ∷ Toff214 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ []) ⟫ʷ
lem-tP-at02102331 c4 = run b0
  where
  b0 : Chain (Toff203 ∷ Toff214 ∷ []) (Toff214 ∷ Toff203 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ023 ∷ K2⁻ ∷ []) (sym (wl0625 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ124 ∷ K2⁻ ∷ []) (sym (wl0624 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at02102331 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff214 ∷ []) (wl0624 (lit c4)) ▸
       at 1 3 (Toff203 ∷ []) (wl0625 (lit c4)) ▸ done

-- box-tQ @03243042: 13 steps
lem-box-tQ-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at03243042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1402 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) (refl) ▸
       at 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ013 ∷ Toff103 ∷ CZ12 ∷ Toff103 ∷ CCZ013 ∷ CZ12 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (wl0344 (lit c4)) ▸
       at 0 2 (Toff314 ∷ CCZ134 ∷ CZ14 ∷ []) (wl0749 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at03243042 c4) ▸
       at 2 4 (Toff314 ∷ []) (wl0750 (lit c4)) ▸ done

-- box-tQ @142142: 13 steps
lem-box-tQ-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) ⟫ʷ
lem-box-tQ-at142142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4132 ∷ []) (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ [])
  b0 = at 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 4 1 (CZ24 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 2 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) (refl) ▸
       at 7 1 (CZ24 ∷ []) (refl) ▸
       at 10 1 (CZ24 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ014 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ014 ∷ CCZ034 ∷ Toff403 ∷ CZ24 ∷ Toff403 ∷ CCZ034 ∷ CZ24 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wp0661 c4)) ▸
       at 0 2 (Toff014 ∷ CCZ014 ∷ CZ14 ∷ []) (wp0056 c4) ▸
       at 2 2 (CCZ023 ∷ CZ14 ∷ []) (lem-comm-CZ14-CCZ023 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at142142 c4) ▸
       at 2 4 (Toff014 ∷ []) (wp0057 c4) ▸ done

-- tP @03243042: 7 steps
lem-tP-at03243042 : Ws → ⟪ (Toff314 ∷ Toff302 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ []) ⟫ʷ
lem-tP-at03243042 c4 = run b0
  where
  b0 : Chain (Toff314 ∷ Toff302 ∷ []) (Toff302 ∷ Toff314 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ134 ∷ K3⁻ ∷ []) (sym (wl0781 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ023 ∷ K3⁻ ∷ []) (sym (wl0782 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ134 ∷ []) (lem-cQ-at03243042 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff302 ∷ []) (wl0782 (lit c4)) ▸
       at 1 3 (Toff314 ∷ []) (wl0781 (lit c4)) ▸ done

-- box-tQ @02102331: 13 steps
lem-box-tQ-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) ⟫ʷ
lem-box-tQ-at02102331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0314 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ012 ∷ Toff012 ∷ CZ04 ∷ Toff012 ∷ CCZ012 ∷ CZ04 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wp1232 c4) ▸
       at 0 2 (Toff203 ∷ CCZ023 ∷ CZ03 ∷ []) (wl0640 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CZ03 ∷ []) (lem-comm-CZ03-CCZ124 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ023 ∷ []) (lem-cQ-at02102331 c4) ▸
       at 2 4 (Toff203 ∷ []) (wl0641 (lit c4)) ▸ done

-- tP @142142: 7 steps
lem-tP-at142142 : Ws → ⟪ (Toff014 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ Toff014 ∷ []) ⟫ʷ
lem-tP-at142142 c4 = run b0
  where
  b0 : Chain (Toff014 ∷ Toff023 ∷ []) (Toff023 ∷ Toff014 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ014 ∷ K0⁻ ∷ []) (sym (wp0049 c4)) ▸
       at 3 1 (K0 ∷ CCZ023 ∷ K0⁻ ∷ []) (sym (wl0200 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ023 ∷ CCZ014 ∷ []) (lem-cQ-at142142 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff023 ∷ []) (wl0200 (lit c4)) ▸
       at 1 3 (Toff014 ∷ []) (wp0049 c4) ▸ done

-- t-cP @032032: 5 steps
lem-t-cP-at032032 : Ws → ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-t-cP-at032032 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 2 (CCZ013 ∷ Toff301 ∷ CZ01 ∷ []) (sym (wl1370 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸
       at 2 3 (CCZ013 ∷ Toff301 ∷ []) (sym (wl1192 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at032032 c4) ▸ done

-- S-sym-xt @14213243: 8 steps
lem-S-sym-xt-at14213243 : Ws → ⟪ (Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ []) ⟫ʷ
lem-S-sym-xt-at14213243 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ []) (Sb2-4-01-3 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Bx2-4013 ∷ []) (lem-box-perm-2134-at0210243143 c4) ▸
       at 1 4 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ []) (sym (wp1307 c4)) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

-- box-tQ @04122041: 13 steps
lem-box-tQ-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at04122041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-2031 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ234 ∷ Toff234 ∷ CZ12 ∷ Toff234 ∷ CCZ234 ∷ CZ12 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (sym (wl1271 (lit c4))) ▸
       at 0 2 (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) (wp1309 c4) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at04122041 c4) ▸
       at 2 4 (Toff402 ∷ []) (wp1310 c4) ▸ done

-- tP @0412233041: 7 steps
lem-tP-at0412233041 : Ws → ⟪ (Toff423 ∷ Toff401 ∷ []) ⟫ʷ ≈ ⟪ (Toff401 ∷ Toff423 ∷ []) ⟫ʷ
lem-tP-at0412233041 c4 = run b0
  where
  b0 : Chain (Toff423 ∷ Toff401 ∷ []) (Toff401 ∷ Toff423 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ234 ∷ K4⁻ ∷ []) (sym (wl0453 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ014 ∷ K4⁻ ∷ []) (sym (wp0303 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ234 ∷ []) (lem-cQ-at0412233041 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff401 ∷ []) (wp0303 c4) ▸
       at 1 3 (Toff423 ∷ []) (wl0453 (lit c4)) ▸ done

-- tP @04122041: 7 steps
lem-tP-at04122041 : Ws → ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ
lem-tP-at04122041 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Toff413 ∷ []) (Toff413 ∷ Toff402 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (sym (wp1321 c4)) ▸
       at 3 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (sym (wl1472 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at04122041 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff413 ∷ []) (wl1472 (lit c4)) ▸
       at 1 3 (Toff402 ∷ []) (wp1321 c4) ▸ done

-- CXbc-box @0410213243: 17 steps
lem-CXbc-box-at0410213243 : Ws → ⟪ (CX12 ∷ Bx4-0123 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx4-0123 ∷ CX12 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX12 ∷ CCZ134 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ234 ∷ CX01 ∷ CS03 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4) ▸
       at 0 2 (Toff401 ∷ CX12 ∷ []) (wp0368 c4) ▸
       at 1 2 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (sym (wl1097 (lit c4))) ▸
       at 3 2 (Toff401 ∷ CCZ134 ∷ CCZ013 ∷ []) (wp1325 c4) ▸
       at 2 2 (Toff401 ∷ CX12 ∷ []) (wp0368 c4) ▸
       at 5 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX12 ∷ CCZ134 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CCZ234 ∷ CX01 ∷ CS03 ∷ CX12 ∷ []) (Bx4-0123 ∷ CX12 ∷ CCZ013 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 4 2 (CCZ234 ∷ CCZ134 ∷ []) (wl0960 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (sym (wl1097 (lit c4))) ▸
       at 4 3 (CX12 ∷ []) (wl1098 (lit c4)) ▸
       at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-tQ-at0410213243 c4)) ▸ done

  b2 : Chain (Bx4-0123 ∷ CX12 ∷ CCZ013 ∷ CX12 ∷ []) (Bx4-0123 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wl1477 (lit c4))) ▸ done

-- CXcb-box @0410213243: 18 steps
lem-CXcb-box-at0410213243 : Ws → ⟪ (CX21 ∷ Bx4-0123 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0123 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CXcb-box-at0410213243 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx4-0123 ∷ CX21 ∷ []) (Toff401 ∷ CCZ234 ∷ CX21 ∷ Toff402 ∷ CS23 ∷ CX02 ∷ Toff401 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ234 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ []) (lem-box-tQ-at0410213243 c4) ▸
       at 0 2 (Toff401 ∷ CX21 ∷ Toff402 ∷ []) (wp1326 c4) ▸
       at 2 2 (CCZ234 ∷ Toff402 ∷ CCZ023 ∷ []) (sym (wp1327 c4)) ▸
       at 1 2 (CCZ234 ∷ CX21 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 4 1 (CS23 ∷ CX02 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ []) (wl0458 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 7 2 (Toff401 ∷ CX02 ∷ []) (wp0360 c4) ▸
       at 6 2 (Toff401 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-TOFF401 (lit c4)) ▸ done

  b1 : Chain (Toff401 ∷ CCZ234 ∷ CX21 ∷ Toff402 ∷ CS23 ∷ CX02 ∷ Toff401 ∷ CS23⁻ ∷ CX02 ∷ CS03 ∷ CCZ234 ∷ CX21 ∷ []) (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX21 ∷ CCZ023 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff401 ∷ CX02 ∷ []) (wp0360 c4) ▸
       at 4 2 (Toff401 ∷ CS23 ∷ []) (lem-comm-CS23-TOFF401 (lit c4)) ▸
       at 5 5 (CCZ023 ∷ []) (sym (wl0458 (lit c4))) ▸
       at 3 2 (Toff401 ∷ Toff402 ∷ []) (sym (wp1329 c4)) ▸
       at 2 2 (Toff401 ∷ CX21 ∷ Toff402 ∷ []) (wp1326 c4) ▸
       at 3 3 (CX21 ∷ []) (wp1330 c4) ▸
       at 4 2 (CCZ234 ∷ CCZ023 ∷ []) (wp0550 c4) ▸
       at 3 2 (CCZ234 ∷ CX21 ∷ []) (sym (wl0836 (lit c4))) ▸ done

  b2 : Chain (Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX21 ∷ CCZ023 ∷ CX21 ∷ []) (Bx4-0123 ∷ CCZ023 ∷ [])
  b2 = at 0 4 (Bx4-0123 ∷ []) (sym (lem-box-tQ-at0410213243 c4)) ▸
       at 1 3 (CCZ023 ∷ []) (sym (wl1478 (lit c4))) ▸ done

-- box-tQ @04103143: 13 steps
lem-box-tQ-at04103143 : Ws → ⟪ (Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ []) ⟫ʷ
lem-box-tQ-at04103143 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-0213 ∷ []) (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ CZ03 ∷ Toff014 ∷ CCZ014 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ134 ∷ []) (wp1331 c4) ▸
       at 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ024 ∷ CCZ014 ∷ Toff014 ∷ CZ03 ∷ Toff014 ∷ CCZ014 ∷ CZ03 ∷ []) (Toff402 ∷ CCZ134 ∷ Toff402 ∷ CCZ134 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wp1331 c4) ▸
       at 0 2 (Toff402 ∷ CCZ024 ∷ CZ02 ∷ []) (wp1309 c4) ▸
       at 2 2 (CCZ134 ∷ CZ02 ∷ []) (lem-comm-CZ02-CCZ134 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at04103143 c4) ▸
       at 2 4 (Toff402 ∷ []) (wp1310 c4) ▸ done

-- tP @04103143: 7 steps
lem-tP-at04103143 : Ws → ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ
lem-tP-at04103143 c4 = run b0
  where
  b0 : Chain (Toff402 ∷ Toff413 ∷ []) (Toff413 ∷ Toff402 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (sym (wp1321 c4)) ▸
       at 3 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (sym (wl1472 (lit c4))) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CCZ024 ∷ []) (lem-cQ-at04103143 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff413 ∷ []) (wl1472 (lit c4)) ▸
       at 1 3 (Toff402 ∷ []) (wp1321 c4) ▸ done

-- box-tQ @04233042: 13 steps
lem-box-tQ-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at04233042 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx4-1302 ∷ []) (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ [])
  b0 = at 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) (refl) ▸
       at 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 4 1 (CZ12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) (refl) ▸
       at 7 1 (CZ12 ∷ []) (refl) ▸
       at 10 1 (CZ12 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ134 ∷ CCZ014 ∷ Toff104 ∷ CZ12 ∷ Toff104 ∷ CCZ014 ∷ CZ12 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0212 c4) ▸
       at 0 2 (Toff413 ∷ CCZ134 ∷ CZ13 ∷ []) (wl1485 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at04233042 c4) ▸
       at 2 4 (Toff413 ∷ []) (wl1486 (lit c4)) ▸ done

-- tP @04233042: 7 steps
lem-tP-at04233042 : Ws → ⟪ (Toff413 ∷ Toff402 ∷ []) ⟫ʷ ≈ ⟪ (Toff402 ∷ Toff413 ∷ []) ⟫ʷ
lem-tP-at04233042 c4 = run b0
  where
  b0 : Chain (Toff413 ∷ Toff402 ∷ []) (Toff402 ∷ Toff413 ∷ [])
  b0 = at 0 1 (K4 ∷ CCZ134 ∷ K4⁻ ∷ []) (sym (wl1472 (lit c4))) ▸
       at 3 1 (K4 ∷ CCZ024 ∷ K4⁻ ∷ []) (sym (wp1321 c4)) ▸
       at 2 2 [] (wl0454 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ134 ∷ []) (lem-cQ-at04233042 c4) ▸
       at 2 0 (K4⁻ ∷ K4 ∷ []) (sym (wl0454 (lit c4))) ▸
       at 0 3 (Toff402 ∷ []) (wp1321 c4) ▸
       at 1 3 (Toff413 ∷ []) (wl1472 (lit c4)) ▸ done
