{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D035 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0018 ; wl0030 ; wl0031 ; wl0063 ; wl0135 ; wl0136 ; wl0174 ; wl0175 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0180 ; wl0181 ; wl0215 ; wl0230 ; wl0263 ; wl0271 ; wl0288 ; wl0293 ; wl0294 ; wl0305 ; wl0321 ; wl0326 ; wl0332 ; wl0341 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0420 ; wl0421 ; wl0433 ; wl0434 ; wl0435 ; wl0436 ; wl0437 ; wl0438 ; wl0439 ; wl0440 ; wl0441 ; wl0442 ; wl0443 ; wl0451 ; wl0452 ; wl0462 ; wl0471 ; wl0473 ; wl0474 ; wl0489 ; wl0504 ; wl0505 ; wl0506 ; wl0508 ; wl0534 ; wl0537 ; wl0560 ; wl0619 ; wl0624 ; wl0625 ; wl0629 ; wl0630 ; wl0631 ; wl0632 ; wl0633 ; wl0634 ; wl0635 ; wl0636 ; wl0639 ; wl0640 ; wl0641 ; wl0755 ; wl0757 ; wl0760 ; wl0762 ; wl0763 ; wl0765 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0787 ; wl0788 ; wl0831 ; wl0842 ; wl0843 ; wl0844 ; wl0866 ; wl0867 ; wl0868 ; wl0879 ; wl0898 ; wl0930 ; wl0931 ; wl0932 ; wl0933 ; wl0934 ; wl0936 ; wl0937 ; wl0949 ; wl0950 ; wl0951 ; wl1155 ; wl1222 ; wl1260 ; wl1266 ; wl1303 ; wl1319 ; wl1321 ; wl1328 ; wl1329 ; wl1331 ; wl1338 ; wl1340 ; wl1341 ; wl1342 ; wl1343 ; wl1344 ; wl1345 ; wl1346 ; wl1347 ; wl1348 ; wl1349 ; wl1350 ; wl1351 ; wl1352 ; wl1353 ; wl1354 ; wl1355 ; wl1356 ; wl1357 ; wl1358 ; wl1359 ; wp0007 ; wp0014 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0019 ; wp0048 ; wp0066 ; wp0090 ; wp0103 ; wp0106 ; wp0108 ; wp0109 ; wp0111 ; wp0123 ; wp0129 ; wp0131 ; wp0135 ; wp0140 ; wp0141 ; wp0161 ; wp0214 ; wp0221 ; wp0225 ; wp0226 ; wp0280 ; wp0301 ; wp0302 ; wp0312 ; wp0314 ; wp0318 ; wp0377 ; wp0384 ; wp0450 ; wp0499 ; wp0505 ; wp0506 ; wp0507 ; wp0508 ; wp0514 ; wp0515 ; wp0543 ; wp0550 ; wp0663 ; wp0670 ; wp0671 ; wp0672 ; wp0673 ; wp0674 ; wp0679 ; wp0686 ; wp0687 ; wp0691 ; wp0703 ; wp0712 ; wp0713 ; wp0734 ; wp0774 ; wp0776 ; wp0780 ; wp0781 ; wp0782 ; wp0827 ; wp0897 ; wp0923 ; wp0946 ; wp1037 ; wp1068 ; wp1071 ; wp1143 ; wp1166 ; wp1169 ; wp1170 ; wp1171 ; wp1172 ; wp1173 ; wp1174 ; wp1184 ; wp1185 ; wp1186 ; wp1187 ; wp1188 ; wp1189 ; wp1193 ; wp1194 ; wp1195 ; wp1196 ; wp1197 ; wp1198 ; wp1199 ; wp1200 ; wp1201 ; wp1202)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-box-cP-at021021 ; lem-cQ-at021021 ; lem-tP-at021021)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-sym-ab-at0310243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-sym-ab-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D008 using (lem-box-tQ-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D017 using (lem-box-tQ-at02102441)
open import Examples.Groups.Clifford+CS.FiveV.D.D022 using (lem-box-cP-at0310243241 ; lem-box-tQ-at0310213442 ; lem-box-tQ-at0310243241 ; lem-cQ-at0310213442 ; lem-sym-bc-at0310243142 ; lem-tP-at0310243241)
open import Examples.Groups.Clifford+CS.FiveV.D.D023 using (lem-sym-bc-at0310213442)
open import Examples.Groups.Clifford+CS.FiveV.D.D030 using (lem-cQ-at03122031)
open import Examples.Groups.Clifford+CS.FiveV.D.D034 using (lem-CXbc-box-at02132130 ; lem-CXcb-box-at02132130 ; lem-box-perm-2314-at0213243041 ; lem-box-perm-2314-at0312243041 ; lem-box-perm-3124-at02142041 ; lem-box-perm-3124-at0314203241 ; lem-box-tQ-at02132130 ; lem-box-tQ-at02142041 ; lem-box-tQ-at0314203241 ; lem-box-tQ-at03143041 ; lem-cQ-at02132130 ; lem-cQ-at03143041 ; lem-pairs-at0210213443 ; lem-pairs-at02102441 ; lem-pairs-at0214233041 ; lem-pairs-at03102132 ; lem-pairs-at0312243041 ; lem-sym-ab-at0213243041 ; lem-sym-ab-at02142041 ; lem-sym-ab-at0214233041 ; lem-sym-ab-at0312243041 ; lem-sym-ab-at03143041 ; lem-sym-bc-at02142041 ; lem-sym-bc-at0314203241)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CZ04-TOFF213 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CX21-CCZ034)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS04-TOFF312 ; lem-comm-CS14-CCZ023 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd14-CCZ023 ; lem-comm-CSd24-TOFF301 ; lem-comm-CX40-CCZ123 ; lem-comm-CZ12-TOFF304 ; lem-comm-TOFF301-CSd24)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CSd02-TOFF314 ; lem-comm-CSd03-TOFF214 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CX30-CCZ124 ; lem-comm-CX30-TOFF214 ; lem-comm-CZ03-CCZ124 ; lem-comm-CZ24-TOFF301 ; lem-comm-TOFF203-CSd14 ; lem-comm-TOFF213-CSd04)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CS14-TOFF203 ; lem-comm-CX21-TOFF304 ; lem-comm-CX24-TOFF301 ; lem-comm-TOFF302-CSd14)
-- SWbc-box @02132130: 11 steps
lem-SWbc-box-at02132130 : Ws → ⟪ (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-SWbc-box-at02132130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (CX10 ∷ Bx2-3104 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx2-3104 ∷ CCZ134 ∷ []) (lem-CXbc-box-at02132130 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸
       at 1 3 (Bx2-3104 ∷ CCZ034 ∷ []) (lem-CXcb-box-at02132130 c4) ▸
       at 4 2 (CX10 ∷ CCZ134 ∷ []) (wp0712 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸
       at 2 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸ done

  b1 : Chain (CX10 ∷ Bx2-3104 ∷ CX10 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ []) (Bx2-3104 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wp0713 c4) ▸
       at 0 3 (Bx2-3104 ∷ CCZ134 ∷ []) (lem-CXbc-box-at02132130 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


-- nat-SWbc @02132130: 23 steps
lem-nat-SWbc-at02132130 : Ws → ⟪ (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-nat-SWbc-at02132130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ Sw01 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-204 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 1 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 3 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 4 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ Sw01 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ Bx3-204 ∷ Sw01 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Sw01 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 7 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 11 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 12 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Sw01 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Sw01 ∷ []) (Bx2-3014 ∷ [])
  b2 = at 13 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 15 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx3-214 ∷ []) (refl) ▸
       at 5 6 (Bx3-214 ∷ []) (refl) ▸
       at 0 6 (Bx2-3014 ∷ []) (refl) ▸ done


-- sym-bc @02132130: 2 steps
lem-sym-bc-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-sym-bc-at02132130 c4 = run b0
  where
  b0 : Chain (Bx2-3104 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-3104 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at02132130 c4)) ▸
       at 0 3 (Bx2-3014 ∷ []) (lem-nat-SWbc-at02132130 c4) ▸ done


-- box-perm-3241 @02142041: 3 steps
lem-box-perm-3241-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-box-perm-3241-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-3014 ∷ [])
  b0 = at 0 1 (Bx2-0431 ∷ []) (lem-sym-ab-at02142041 c4) ▸
       at 0 1 (Bx2-3104 ∷ []) (lem-pairs-at02102441 c4) ▸
       at 0 1 (Bx2-3014 ∷ []) (lem-sym-bc-at02132130 c4) ▸ done


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


-- P-box @03143041: 8 steps
lem-P-box-at03143041 : Ws → ⟪ (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-P-box-at03143041 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 1 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143041 c4) ▸
       at 0 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at03143041 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ01 ∷ Toff301 ∷ []) (sym (wl0866 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Toff301 ∷ []) (sym (lem-tP-at03143041 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ01 ∷ []) (sym (wl0867 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CZ01 ∷ []) (c₂ (CZ) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0868 (lit c4))) ▸
       at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-tQ-at03143041 c4)) ▸ done


-- VPQ @03143041: 14 steps
lem-VPQ-at03143041 : Ws → ⟪ (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at03143041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S3 ∷ Toff324 ∷ S3⁻ ∷ []) (sym (wl0438 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S3 ∷ Toff301 ∷ S3⁻ ∷ []) (sym (wl0437 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S3⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((S • S • S) ↑))) ▸
       at 2 2 (CS01⁻ ∷ Toff324 ∷ []) (sym (c₂ (CS • CS • CS) (K ↑ • CCZ • K ↑ • iI))) ▸
       at 1 2 (CS01⁻ ∷ S3 ∷ []) (sym (c₂ (CS • CS • CS) (S ↑))) ▸
       at 0 2 (CS01⁻ ∷ CS24⁻ ∷ []) (sym (c₂ (CS • CS • CS) (Swap ↑ • (CS • CS • CS) • Swap ↑))) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143041 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS24⁻ ∷ S3 ∷ Toff301 ∷ Toff324 ∷ S3⁻ ∷ []) (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS24⁻ ∷ []) (wl0440 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS24⁻ ∷ []) (wl0439 (lit c4)) ▸
       at 0 4 (Toff301 ∷ CCZ013 ∷ []) (wl0437 (lit c4)) ▸
       at 2 4 (Toff324 ∷ CCZ234 ∷ []) (wl0438 (lit c4)) ▸ done


-- QVQ @03143041: 3 steps
lem-QVQ-at03143041 : Ws → ⟪ (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-QVQ-at03143041 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ013 ∷ []) (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 1 4 (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at03143041 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done


-- box-cP @03143041: 12 steps
lem-box-cP-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) ⟫ʷ
lem-box-cP-at03143041 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ234 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 2 4 (Toff301 ∷ Toff324 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-QVQ-at03143041 c4) ▸
       at 1 2 (Toff301 ∷ Toff324 ∷ []) (lem-tP-at03143041 c4) ▸
       at 2 2 [] (wl0442 (lit c4)) ▸ done


-- pairs @03143041: 4 steps
lem-pairs-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-pairs-at03143041 c4 = run b0
  where
  b0 : Chain (Bx3-4201 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) (sym (lem-P-box-at03143041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143041 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 0 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸ done


-- box-perm-1243 @03102132: 3 steps
lem-box-perm-1243-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-box-perm-1243-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0142 ∷ [])
  b0 = at 0 1 (Bx3-2401 ∷ []) (lem-pairs-at03102132 c4) ▸
       at 0 1 (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-pairs-at03143041 c4) ▸ done


-- cQ @02132031: 7 steps
lem-cQ-at02132031 : Ws → ⟪ (CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CCZ023 ∷ []) ⟫ʷ
lem-cQ-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ023 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX30 ∷ CS02⁻ ∷ CX30 ∷ CS23 ∷ []) (wl0757 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CS23 ∷ []) (sym (wl0639 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ CS02⁻ ∷ []) (sym (wp0679 c4)) ▸
       at 1 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ CS02 ∷ []) (sym (wp0515 c4)) ▸
       at 1 5 (CCZ023 ∷ []) (sym (wl0757 (lit c4))) ▸ done


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


-- VPQ @02132031: 14 steps
lem-VPQ-at02132031 : Ws → ⟪ (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS03⁻ ∷ S2 ∷ Toff203 ∷ S2⁻ ∷ []) (sym (wl0630 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S2 ∷ Toff214 ∷ S2⁻ ∷ []) (sym (wl0629 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S2⁻ ∷ []) (sym (wl0634 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff203 ∷ []) (lem-comm-TOFF203-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S2 ∷ []) (sym (wl0633 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS03⁻ ∷ []) (wp0514 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02132031 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS03⁻ ∷ S2 ∷ Toff214 ∷ Toff203 ∷ S2⁻ ∷ []) (Toff214 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS03⁻ ∷ []) (wl0632 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-TOFF214 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS03⁻ ∷ []) (wl0631 (lit c4)) ▸
       at 0 4 (Toff214 ∷ CCZ124 ∷ []) (wl0629 (lit c4)) ▸
       at 2 4 (Toff203 ∷ CCZ023 ∷ []) (wl0630 (lit c4)) ▸ done


-- QVQ @02132031: 3 steps
lem-QVQ-at02132031 : Ws → ⟪ (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-QVQ-at02132031 c4 = run b0
  where
  b0 : Chain (CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ124 ∷ []) (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ [])
  b0 = at 0 0 (Toff214 ∷ Toff214 ∷ []) (sym (wl0636 (lit c4))) ▸
       at 1 4 (Toff203 ∷ CCZ023 ∷ Toff214 ∷ CCZ124 ∷ []) (sym (lem-VPQ-at02132031 c4)) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸ done


-- box-cP @02132031: 12 steps
lem-box-cP-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at02132031 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ023 ∷ CCZ123 ∷ Toff312 ∷ CZ34 ∷ Toff312 ∷ CCZ123 ∷ CZ34 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  b1 = at 5 6 (CCZ124 ∷ []) (wl1341 (lit c4)) ▸
       at 2 4 (Toff214 ∷ Toff203 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-QVQ-at02132031 c4) ▸
       at 1 2 (Toff214 ∷ Toff203 ∷ []) (lem-tP-at02132031 c4) ▸
       at 2 2 [] (wl0635 (lit c4)) ▸ done


-- tP @0310213442: 7 steps
lem-tP-at0310213442 : Ws → ⟪ (Toff301 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ []) ⟫ʷ
lem-tP-at0310213442 c4 = run b0
  where
  b0 : Chain (Toff301 ∷ Toff324 ∷ []) (Toff324 ∷ Toff301 ∷ [])
  b0 = at 0 1 (K3 ∷ CCZ013 ∷ K3⁻ ∷ []) (sym (wl0434 (lit c4))) ▸
       at 3 1 (K3 ∷ CCZ234 ∷ K3⁻ ∷ []) (sym (wl0435 (lit c4))) ▸
       at 2 2 [] (wl0436 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at0310213442 c4) ▸
       at 2 0 (K3⁻ ∷ K3 ∷ []) (sym (wl0436 (lit c4))) ▸
       at 0 3 (Toff324 ∷ []) (wl0435 (lit c4)) ▸
       at 1 3 (Toff301 ∷ []) (wl0434 (lit c4)) ▸ done


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


-- QVQ @0310213442: 3 steps
lem-QVQ-at0310213442 : Ws → ⟪ (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-QVQ-at0310213442 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ234 ∷ []) (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 1 4 (Toff301 ∷ CCZ013 ∷ Toff324 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0310213442 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done


-- box-cP @0310213442: 12 steps
lem-box-cP-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) ⟫ʷ
lem-box-cP-at0310213442 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0142 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-342 ∷ Toff301 ∷ CCZ013 ∷ Bx0-342 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 4 1 (CZ02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 5 1 (CCZ034 ∷ Toff034 ∷ Bx3-02 ∷ Toff034 ∷ CCZ034 ∷ Bx3-02 ∷ []) (refl) ▸
       at 7 1 (CZ02 ∷ []) (refl) ▸
       at 10 1 (CZ02 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ034 ∷ Toff034 ∷ CZ02 ∷ Toff034 ∷ CCZ034 ∷ CZ02 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp1068 c4) ▸
       at 2 4 (Toff324 ∷ Toff301 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-QVQ-at0310213442 c4) ▸
       at 1 2 (Toff324 ∷ Toff301 ∷ []) (lem-tP-at0310213442 c4) ▸
       at 2 2 [] (wl0443 (lit c4)) ▸ done


-- pairs @0310213442: 4 steps
lem-pairs-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-pairs-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 1 (Toff324 ∷ Bx3-0142 ∷ Toff324 ∷ []) (sym (lem-P-box-at0310213442 c4)) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at0310213442 c4) ▸
       at 4 2 [] (wl0442 (lit c4)) ▸
       at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-tQ-at03143041 c4)) ▸ done


-- box-perm-1243 @0310213442: 3 steps
lem-box-perm-1243-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-box-perm-1243-at0310213442 c4 = run b0
  where
  b0 : Chain (Bx3-0142 ∷ []) (Bx3-0124 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-pairs-at0310213442 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-pairs-at0312243041 c4) ▸ done


-- box-box-3 @03102132: 105 steps
lem-box-box-3-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ Bx3-0124 ∷ []) ⟫ʷ
lem-box-box-3-at03102132 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-0124 ∷ Bx2-3014 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ023 ∷ CS34 ∷ CCZ234 ∷ Toff214 ∷ [])
  b0 = at 0 1 (Bx3-0142 ∷ []) (lem-box-perm-1243-at03102132 c4) ▸
       at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4) ▸
       at 4 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸
       at 3 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 4 2 (Toff214 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl1342 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 5 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CCZ023 ∷ CS34 ∷ CCZ234 ∷ Toff214 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ [])
  b1 = at 8 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 7 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 6 3 (Toff214 ∷ CCZ234 ∷ []) (wl1344 (lit c4)) ▸
       at 3 4 (Bx2-3014 ∷ []) (sym (lem-box-cP-at02132031 c4)) ▸
       at 3 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ Toff214 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ [])
  b2 = at 2 2 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1345 (lit c4))) ▸
       at 4 2 (Toff214 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1194 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1346 (lit c4))) ▸
       at 9 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4)) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸ done

  b3 : Chain (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ Toff214 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ Toff301 ∷ CCZ012 ∷ CS14 ∷ CCZ023 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff214 ∷ CCZ234 ∷ [])
  b3 = at 4 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 3 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 4 7 (Toff301 ∷ []) (wl1346 (lit c4)) ▸
       at 6 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 10 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 9 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b4 : Chain (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ Toff301 ∷ CCZ012 ∷ CS14 ∷ CCZ023 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff214 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ Toff214 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ [])
  b4 = at 6 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 5 2 (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1345 (lit c4))) ▸
       at 5 3 (Toff301 ∷ []) (wl1347 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 5 1 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1346 (lit c4))) ▸
       at 11 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸ done

  b5 : Chain (Toff301 ∷ CCZ234 ∷ CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ Toff214 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ234 ∷ Bx2-3014 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b5 = at 10 2 (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4)) ▸
       at 9 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 5 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 6 7 (Toff301 ∷ []) (wl1346 (lit c4)) ▸
       at 2 4 (Bx2-3014 ∷ []) (sym (lem-box-cP-at02132031 c4)) ▸ done

  b6 : Chain (Toff301 ∷ CCZ234 ∷ Bx2-3014 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff301 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX31 ∷ CCZ023 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ234 ∷ Toff214 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b6 = at 2 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 2 2 (Toff214 ∷ CCZ134 ∷ CCZ234 ∷ []) (wl1342 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 3 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CS34 ∷ []) (sym (wp0543 c4)) ▸
       at 6 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸ done

  b7 : Chain (Toff301 ∷ CCZ023 ∷ Toff214 ∷ CS14 ∷ CX31 ∷ CCZ023 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ234 ∷ Toff214 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff301 ∷ Toff214 ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b7 = at 4 2 (CCZ023 ∷ CX31 ∷ []) (sym (wl1343 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 4 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 4 3 (Toff214 ∷ CCZ234 ∷ []) (wl1344 (lit c4)) ▸
       at 1 4 (Bx2-3014 ∷ []) (sym (lem-box-cP-at02132031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) (lem-box-cP-at02132031 c4) ▸
       at 0 2 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1345 (lit c4))) ▸
       at 2 2 (Toff214 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1194 c4) ▸ done

  b8 : Chain (CCZ023 ∷ Toff301 ∷ Toff214 ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff214 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b8 = at 1 1 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1346 (lit c4))) ▸
       at 7 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 6 2 (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4)) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4) ▸
       at 3 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 2 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 1 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸ done

  b9 : Chain (CCZ023 ∷ Toff214 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ012 ∷ CCZ014 ∷ CCZ023 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff214 ∷ Toff301 ∷ CCZ012 ∷ CCZ023 ∷ CCZ014 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b9 = at 2 7 (Toff301 ∷ []) (wl1346 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 8 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 7 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

  b10 : Chain (CCZ023 ∷ Toff214 ∷ Toff301 ∷ CCZ012 ∷ CCZ023 ∷ CCZ014 ∷ Toff214 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ Toff214 ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b10 = at 3 2 (CCZ023 ∷ CCZ012 ∷ []) (wl0332 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff301 ∷ CCZ012 ∷ []) (sym (wl1345 (lit c4))) ▸
       at 3 3 (Toff301 ∷ []) (wl1347 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CCZ014 ∷ []) (wp0686 c4) ▸
       at 3 1 (K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ []) (sym (wl1346 (lit c4))) ▸
       at 9 2 (Toff214 ∷ K3⁻ ∷ []) (wl0760 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CS13 ∷ []) (wl0898 (lit c4)) ▸
       at 7 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸ done

  b11 : Chain (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ K3 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ Toff214 ∷ CX30 ∷ CS13 ∷ K3⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx2-3014 ∷ Toff301 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CCZ234 ∷ CS04 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b11 = at 6 2 (Toff214 ∷ CS01⁻ ∷ []) (wp1195 c4) ▸
       at 5 2 (Toff214 ∷ CX30 ∷ []) (lem-comm-CX30-TOFF214 (lit c4)) ▸
       at 4 2 (Toff214 ∷ CS01 ∷ []) (wp0923 c4) ▸
       at 3 2 (Toff214 ∷ K3 ∷ []) (wl0762 (lit c4)) ▸
       at 4 7 (Toff301 ∷ []) (wl1346 (lit c4)) ▸
       at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-cP-at02132031 c4)) ▸
       at 2 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 6 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸ done

  b12 : Chain (Bx2-3014 ∷ Toff301 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CCZ234 ∷ CS04 ∷ Toff301 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx2-3014 ∷ Bx3-0142 ∷ [])
  b12 = at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 3 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-0142 ∷ []) (sym (lem-box-tQ-at0310213442 c4)) ▸ done

  b13 : Chain (Bx2-3014 ∷ Bx3-0142 ∷ []) (Bx2-3014 ∷ Bx3-0124 ∷ [])
  b13 = at 1 1 (Bx3-0124 ∷ []) (lem-box-perm-1243-at0310213442 c4) ▸ done


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


-- CXbc-box @02132031: 17 steps
lem-CXbc-box-at02132031 : Ws → ⟪ (CX01 ∷ Bx2-3014 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx2-3014 ∷ CX01 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX01 ∷ CCZ024 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CCZ124 ∷ CX30 ∷ CS34 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02132031 c4) ▸
       at 0 2 (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4)) ▸
       at 1 2 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (sym (wp1196 c4)) ▸
       at 3 2 (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1197 c4) ▸
       at 2 2 (Toff203 ∷ CX01 ∷ []) (wl1348 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX30 ∷ CS04⁻ ∷ CX30 ∷ CS34 ∷ []) (wp1193 c4) ▸
       at 9 2 (CCZ124 ∷ CS34 ∷ []) (sym (wl0471 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX01 ∷ CCZ024 ∷ CS04 ∷ CX30 ∷ CS04⁻ ∷ CCZ124 ∷ CX30 ∷ CS34 ∷ CX01 ∷ []) (Bx2-3014 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ124 ∷ CS04⁻ ∷ []) (sym (wp0318 c4)) ▸
       at 6 2 (CCZ124 ∷ CX30 ∷ []) (lem-comm-CX30-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp1193 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 3 2 (CCZ124 ∷ CX01 ∷ CCZ024 ∷ []) (sym (wp1196 c4)) ▸
       at 4 3 (CX01 ∷ []) (wp1198 c4) ▸
       at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-tQ-at02132031 c4)) ▸ done

  b2 : Chain (Bx2-3014 ∷ CX01 ∷ CCZ034 ∷ CX01 ∷ []) (Bx2-3014 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (sym (wp0499 c4)) ▸ done


-- CXcb-box @02132031: 18 steps
lem-CXcb-box-at02132031 : Ws → ⟪ (CX10 ∷ Bx2-3014 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx2-3014 ∷ CX10 ∷ []) (Toff203 ∷ CCZ124 ∷ CX10 ∷ Toff213 ∷ CS14 ∷ CX31 ∷ Toff203 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ124 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at02132031 c4) ▸
       at 0 2 (Toff203 ∷ CX10 ∷ Toff213 ∷ []) (wl1349 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Toff213 ∷ CCZ134 ∷ []) (sym (wl1350 (lit c4))) ▸
       at 1 2 (CCZ124 ∷ CX10 ∷ []) (sym (wp0672 c4)) ▸
       at 4 1 (CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ []) (wl0831 (lit c4)) ▸
       at 8 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 7 2 (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ CX10 ∷ Toff213 ∷ CS14 ∷ CX31 ∷ Toff203 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ CCZ124 ∷ CX10 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff203 ∷ CX31 ∷ []) (wl1351 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF203 (lit c4)) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0831 (lit c4))) ▸
       at 3 2 (Toff203 ∷ Toff213 ∷ []) (sym (wl1338 (lit c4))) ▸
       at 2 2 (Toff203 ∷ CX10 ∷ Toff213 ∷ []) (wl1349 (lit c4)) ▸
       at 3 3 (CX10 ∷ []) (wl1352 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 3 2 (CCZ124 ∷ CX10 ∷ []) (sym (wp0672 c4)) ▸ done

  b2 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX10 ∷ CCZ134 ∷ CX10 ∷ []) (Bx2-3014 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-3014 ∷ []) (sym (lem-box-tQ-at02132031 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wp0505 c4)) ▸ done


-- SWbc-box @02132031: 11 steps
lem-SWbc-box-at02132031 : Ws → ⟪ (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-SWbc-box-at02132031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (CX01 ∷ Bx2-3014 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx2-3014 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02132031 c4) ▸
       at 3 2 (CX10 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp0506 c4) ▸
       at 1 3 (Bx2-3014 ∷ CCZ134 ∷ []) (lem-CXcb-box-at02132031 c4) ▸
       at 4 2 (CX01 ∷ CCZ034 ∷ []) (wp0221 c4) ▸
       at 3 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸
       at 2 2 (CX01 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp0507 c4) ▸ done

  b1 : Chain (CX01 ∷ Bx2-3014 ∷ CX01 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (Bx2-3014 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp0508 c4) ▸
       at 0 3 (Bx2-3014 ∷ CCZ034 ∷ []) (lem-CXbc-box-at02132031 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done


-- nat-SWbc @02132031: 23 steps
lem-nat-SWbc-at02132031 : Ws → ⟪ (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-nat-SWbc-at02132031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ Sw01 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx3-214 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 4 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 5 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ Sw01 ∷ CCZ123 ∷ Bx2-34 ∷ Toff203 ∷ CCZ023 ∷ Bx3-214 ∷ Sw01 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Sw01 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 7 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 8 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff312 ∷ Bx2-34 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 11 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 12 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Toff302 ∷ CCZ023 ∷ Bx2-34 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ Bx2-34 ∷ Sw01 ∷ Toff312 ∷ CCZ123 ∷ Bx2-34 ∷ Sw01 ∷ []) (Bx2-3104 ∷ [])
  b2 = at 13 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 15 2 (Bx2-34 ∷ Sw01 ∷ []) (c₂ (Swap) (CZ ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx3-204 ∷ []) (refl) ▸
       at 5 6 (Bx3-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-3104 ∷ []) (refl) ▸ done


-- sym-bc @02132031: 2 steps
lem-sym-bc-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-sym-bc-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx2-3014 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at02132031 c4)) ▸
       at 0 3 (Bx2-3104 ∷ []) (lem-nat-SWbc-at02132031 c4) ▸ done


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


-- P-box @02132130: 8 steps
lem-P-box-at02132130 : Ws → ⟪ (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-P-box-at02132130 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) (Bx2-3104 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02132130 c4) ▸
       at 0 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at02132130 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (sym (wp0780 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at02132130 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ04 ∷ []) (sym (wp0781 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0782 c4)) ▸
       at 0 4 (Bx2-3104 ∷ []) (sym (lem-box-tQ-at02132130 c4)) ▸ done


-- VPQ @02132130: 14 steps
lem-VPQ-at02132130 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at02132130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 3 2 (CS04⁻ ∷ S2⁻ ∷ []) (sym (wp0018 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S2 ∷ []) (sym (wp0017 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS13⁻ ∷ []) (sym (wp0016 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02132130 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS13⁻ ∷ []) (wl0178 (lit c4)) ▸
       at 2 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS13⁻ ∷ []) (wl0177 (lit c4)) ▸
       at 0 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸
       at 2 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸ done


-- QVQ @02132130: 3 steps
lem-QVQ-at02132130 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at02132130 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 1 4 (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at02132130 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


-- box-cP @02132130: 12 steps
lem-box-cP-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at02132130 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ023 ∷ Toff302 ∷ CZ34 ∷ Toff302 ∷ CCZ023 ∷ CZ34 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0131 c4) ▸
       at 2 4 (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at02132130 c4) ▸
       at 1 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at02132130 c4) ▸
       at 2 2 [] (wl0180 (lit c4)) ▸ done


-- pairs @02132130: 4 steps
lem-pairs-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-pairs-at02132130 c4 = run b0
  where
  b0 : Chain (Bx2-3104 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 1 (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) (sym (lem-P-box-at02132130 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-tQ-at02102441 c4)) ▸ done


-- sym-ab @02102441: 18 steps
lem-sym-ab-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-sym-ab-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0431 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4)) ▸
       at 4 1 (Bx2-41 ∷ []) (refl) ▸
       at 7 1 (Bx2-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ [])
  b1 = at 2 6 (Bx4-231 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4)) ▸
       at 7 1 (Bx2-41 ∷ []) (refl) ▸
       at 10 1 (Bx2-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) (Bx2-4031 ∷ [])
  b2 = at 5 6 (Bx4-231 ∷ []) (refl) ▸
       at 0 6 (Bx2-4031 ∷ []) (refl) ▸ done


-- box-perm-4213 @02132031: 3 steps
lem-box-perm-4213-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-4213-at02132031 c4 = run b0
  where
  b0 : Chain (Bx2-3014 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 1 (Bx2-3104 ∷ []) (lem-sym-bc-at02132031 c4) ▸
       at 0 1 (Bx2-0431 ∷ []) (lem-pairs-at02132130 c4) ▸
       at 0 1 (Bx2-4031 ∷ []) (lem-sym-ab-at02102441 c4) ▸ done


-- box-perm-1324 @0314203241: 1 steps
lem-box-perm-1324-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-box-perm-1324-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-bc-at0314203241 c4) ▸ done


-- box-perm-2341 @0312243041: 4 steps
lem-box-perm-2341-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-2341-at0312243041 c4 = run b0
  where
  b0 : Chain (Bx3-2401 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-pairs-at03143041 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-bc-at0310213442 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸ done


-- cQ @0213243041: 7 steps
lem-cQ-at0213243041 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0213243041 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CS23 ∷ []) (sym (wl0294 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS24⁻ ∷ []) (sym (wp0140 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸ done


-- tP @0213243041: 7 steps
lem-tP-at0213243041 : Ws → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0213243041 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243041 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸
       at 1 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸ done


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


-- QVQ @0213243041: 3 steps
lem-QVQ-at0213243041 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0213243041 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Toff201 ∷ Toff201 ∷ []) (sym (wl0421 (lit c4))) ▸
       at 1 4 (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at0213243041 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done


-- box-cP @0213243041: 12 steps
lem-box-cP-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0213243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3401 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 2 4 (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0213243041 c4) ▸
       at 1 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243041 c4) ▸
       at 2 2 [] (wl0420 (lit c4)) ▸ done


-- box-perm-4123 @0314203142: 4 steps
lem-box-perm-4123-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-4123-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-2401 ∷ [])
  b0 = at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸
       at 0 1 (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4) ▸
       at 0 1 (Bx3-4201 ∷ []) (lem-pairs-at0310213442 c4) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4) ▸ done


-- box-box-1 @0312243041: 105 steps
lem-box-box-1-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-2401 ∷ []) ⟫ʷ
lem-box-box-1-at0312243041 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx3-2401 ∷ Bx2-3401 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CCZ234 ∷ CX30 ∷ CS13 ∷ Toff201 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-box-perm-2341-at0312243041 c4) ▸
       at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4) ▸
       at 4 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 2 (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1328 (lit c4)) ▸
       at 6 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4)) ▸
       at 10 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ CS01 ∷ CX30 ∷ CS01⁻ ∷ CCZ234 ∷ CX30 ∷ CS13 ∷ Toff201 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ [])
  b1 = at 8 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl1353 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 6 3 (Toff201 ∷ CCZ123 ∷ []) (wl1354 (lit c4)) ▸
       at 3 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 3 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸ done

  b2 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ Toff201 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ [])
  b2 = at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 4 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸ done

  b3 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ Toff201 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ CCZ123 ∷ [])
  b3 = at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 6 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 8 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸ done

  b4 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CS01 ∷ CCZ234 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ Toff201 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ Toff201 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ [])
  b4 = at 6 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 4 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 5 3 (Toff304 ∷ []) (wp1188 c4) ▸
       at 6 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 5 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 11 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸ done

  b5 : Chain (Toff304 ∷ CCZ123 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ Toff201 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ123 ∷ Bx2-3401 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b5 = at 10 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 9 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 8 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 6 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 5 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 6 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 2 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸ done

  b6 : Chain (Toff304 ∷ CCZ123 ∷ Bx2-3401 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ CS01 ∷ CCZ234 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b6 = at 2 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 1 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 2 2 (Toff201 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1328 (lit c4)) ▸
       at 4 1 (CS01 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ []) (wl1353 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b7 : Chain (Toff304 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ CS01 ∷ CCZ234 ∷ CX30 ∷ CS01⁻ ∷ CX30 ∷ CS13 ∷ Toff201 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff304 ∷ Toff201 ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b7 = at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl1353 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CCZ123 ∷ []) (wl0508 (lit c4)) ▸
       at 4 3 (Toff201 ∷ CCZ123 ∷ []) (wl1354 (lit c4)) ▸
       at 1 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 2 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4) ▸ done

  b8 : Chain (CCZ234 ∷ Toff304 ∷ Toff201 ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b8 = at 1 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 7 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 6 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 3 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 2 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 1 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸ done

  b9 : Chain (CCZ234 ∷ Toff201 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ024 ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CCZ234 ∷ CCZ014 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b9 = at 2 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸ done

  b10 : Chain (CCZ234 ∷ Toff201 ∷ Toff304 ∷ CCZ024 ∷ CCZ234 ∷ CCZ014 ∷ Toff201 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ Toff201 ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b10 = at 3 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 2 2 (CCZ234 ∷ Toff304 ∷ CCZ024 ∷ []) (sym (wp1071 c4)) ▸
       at 3 3 (Toff304 ∷ []) (wp1188 c4) ▸
       at 4 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 3 1 (K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ []) (sym (wp1185 c4)) ▸
       at 9 2 (Toff201 ∷ K3⁻ ∷ []) (sym (c₃ (Toffᵗ) (K • iI))) ▸
       at 8 2 (Toff201 ∷ CS03 ∷ []) (wl1329 (lit c4)) ▸
       at 7 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸ done

  b11 : Chain (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ K3 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ Toff201 ∷ CX34 ∷ CS03 ∷ K3⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3401 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CCZ123 ∷ CS14 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b11 = at 6 2 (Toff201 ∷ CS04⁻ ∷ []) (wp1186 c4) ▸
       at 5 2 (Toff201 ∷ CX34 ∷ []) (sym (c₃ (Toffᵗ) (CX₀₁))) ▸
       at 4 2 (Toff201 ∷ CS04 ∷ []) (wp1187 c4) ▸
       at 3 2 (Toff201 ∷ K3 ∷ []) (sym (c₃ (Toffᵗ) (K))) ▸
       at 4 7 (Toff304 ∷ []) (wp1185 c4) ▸
       at 0 4 (Bx2-3401 ∷ []) (sym (lem-box-cP-at0213243041 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸ done

  b12 : Chain (Bx2-3401 ∷ Toff304 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CCZ123 ∷ CS14 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Bx2-3401 ∷ Bx3-4012 ∷ [])
  b12 = at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done

  b13 : Chain (Bx2-3401 ∷ Bx3-4012 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ [])
  b13 = at 1 1 (Bx3-2401 ∷ []) (lem-box-perm-4123-at0314203142 c4) ▸ done


-- Tu-box @02142041: 83 steps
lem-Tu-box-at02142041 : Ws → ⟪ (Toff324 ∷ Bx2-4031 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ Bx3-4021 ∷ []) ⟫ʷ
lem-Tu-box-at02142041 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff324 ∷ Bx2-4031 ∷ Toff324 ∷ []) (Toff204 ∷ Toff304 ∷ CCZ123 ∷ Toff204 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ CCZ124 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 0 2 (Toff204 ∷ Toff304 ∷ Toff324 ∷ []) (sym (wp1200 c4)) ▸
       at 2 2 (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (sym (wl0215 (lit c4))) ▸
       at 4 2 (Toff204 ∷ Toff304 ∷ Toff324 ∷ []) (sym (wp1200 c4)) ▸
       at 6 3 (CCZ123 ∷ CCZ124 ∷ []) (sym (wl1355 (lit c4))) ▸
       at 3 2 (Toff204 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0946 c4) ▸
       at 5 2 (Toff304 ∷ CCZ014 ∷ []) (wp0687 c4) ▸
       at 4 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ Toff304 ∷ CCZ123 ∷ Toff204 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ CCZ124 ∷ []) (Toff204 ∷ Toff304 ∷ CCZ123 ∷ Toff204 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ [])
  b1 = at 8 2 (Toff304 ∷ CS24 ∷ []) (wp0691 c4) ▸
       at 7 2 (Toff304 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF304 (lit c4)) ▸
       at 6 2 (Toff304 ∷ CS14⁻ ∷ []) (wp1201 c4) ▸
       at 5 2 (Toff304 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF304 (lit c4)) ▸
       at 4 2 (Toff304 ∷ CS14 ∷ []) (wp1037 c4) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 6 3 (CCZ123 ∷ []) (sym (wl0462 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ Toff304 ∷ CCZ123 ∷ Toff204 ∷ Toff304 ∷ CCZ014 ∷ CCZ123 ∷ []) (Toff204 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b2 = at 5 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 9 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 7 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff304 ∷ Toff204 ∷ []) (wp1184 c4) ▸ done

  b3 : Chain (Toff204 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff301 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b3 = at 4 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 1 4 (Bx3-4021 ∷ []) (sym (lem-box-tQ-at0314203241 c4)) ▸
       at 1 1 (Bx3-4201 ∷ []) (lem-box-perm-1324-at0314203241 c4) ▸
       at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143041 c4) ▸
       at 0 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸
       at 2 2 (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp0377 c4) ▸
       at 1 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 7 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸ done

  b4 : Chain (CCZ234 ∷ K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ Toff301 ∷ K2⁻ ∷ CCZ034 ∷ CCZ014 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b4 = at 6 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 3 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 2 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 1 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸
       at 2 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸ done

  b5 : Chain (CCZ234 ∷ Toff301 ∷ Toff204 ∷ CCZ034 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ234 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff204 ∷ CCZ034 ∷ CCZ034 ∷ CCZ014 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b5 = at 8 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX40 ∷ []) (sym (wp1171 c4)) ▸
       at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 2 2 (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (sym (wp1166 c4)) ▸ done

  b6 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff204 ∷ CCZ034 ∷ CCZ034 ∷ CCZ014 ∷ Toff301 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ Toff301 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b6 = at 3 3 (Toff204 ∷ []) (wp1172 c4) ▸
       at 4 2 (Toff301 ∷ CCZ014 ∷ []) (wp1173 c4) ▸
       at 3 1 (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (sym (wp1169 c4)) ▸
       at 9 2 (Toff301 ∷ K2⁻ ∷ []) (wl1331 (lit c4)) ▸
       at 8 2 (Toff301 ∷ CS02 ∷ []) (wl1260 (lit c4)) ▸
       at 7 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS04⁻ ∷ []) (wp1170 c4) ▸
       at 5 2 (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4)) ▸ done

  b7 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ K2 ∷ CS04 ∷ Toff301 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ CCZ014 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ []) (Bx3-4021 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ [])
  b7 = at 4 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 3 2 (Toff301 ∷ K2 ∷ []) (wl1266 (lit c4)) ▸
       at 4 7 (Toff204 ∷ []) (wp1169 c4) ▸
       at 0 4 (Bx3-4201 ∷ []) (sym (lem-box-cP-at03143041 c4)) ▸
       at 0 1 (Bx3-4021 ∷ []) (sym (lem-box-perm-1324-at0314203241 c4)) ▸
       at 2 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 6 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b8 : Chain (Bx3-4021 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ Toff204 ∷ CCZ123 ∷ CCZ014 ∷ []) (Bx3-4021 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CCZ014 ∷ [])
  b8 = at 4 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff204 ∷ CCZ014 ∷ []) (wp1174 c4) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 7 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸ done

  b9 : Chain (Bx3-4021 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CS01 ∷ CX40 ∷ CS01⁻ ∷ CCZ123 ∷ CX40 ∷ CS14 ∷ CCZ014 ∷ []) (Bx3-2401 ∷ Bx2-3401 ∷ [])
  b9 = at 6 2 (CCZ123 ∷ CS01⁻ ∷ []) (sym (wl1321 (lit c4))) ▸
       at 5 2 (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4)) ▸
       at 4 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 1 4 (Bx2-4031 ∷ []) (sym (lem-box-tQ-at02142041 c4)) ▸
       at 0 1 (Bx3-2401 ∷ []) (lem-box-perm-3124-at0314203241 c4) ▸
       at 1 1 (Bx2-3401 ∷ []) (lem-box-perm-3124-at02142041 c4) ▸ done

  b10 : Chain (Bx3-2401 ∷ Bx2-3401 ∷ []) (Bx2-4031 ∷ Bx3-4021 ∷ [])
  b10 = at 0 2 (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-box-box-1-at0312243041 c4) ▸
       at 0 1 (Bx2-4031 ∷ []) (lem-box-perm-2314-at0213243041 c4) ▸
       at 1 1 (Bx3-4021 ∷ []) (lem-box-perm-2314-at0312243041 c4) ▸ done


-- box-tQ @0213243041: 13 steps
lem-box-tQ-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0213243041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3401 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-201 ∷ Toff234 ∷ CCZ234 ∷ Bx3-201 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 4 1 (CZ13 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ Bx2-31 ∷ Toff302 ∷ CCZ023 ∷ Bx2-31 ∷ []) (refl) ▸
       at 7 1 (CZ13 ∷ []) (refl) ▸
       at 10 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0288 (lit c4))) ▸
       at 0 2 (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) (wl0936 (lit c4)) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243041 c4) ▸
       at 2 4 (Toff234 ∷ []) (wl0937 (lit c4)) ▸ done


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


-- box-tQ @021021: 13 steps
lem-box-tQ-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at021021 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0134 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 0 2 (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (wl0930 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at021021 c4) ▸
       at 2 4 (Toff201 ∷ []) (wl0931 (lit c4)) ▸ done


-- pairs @0213243041: 4 steps
lem-pairs-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-pairs-at0213243041 c4 = run b0
  where
  b0 : Chain (Bx2-3401 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Toff201 ∷ Bx2-3401 ∷ Toff201 ∷ []) (sym (lem-P-box-at0213243041 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243041 c4) ▸
       at 4 2 [] (wl0421 (lit c4)) ▸
       at 0 4 (Bx2-0134 ∷ []) (sym (lem-box-tQ-at021021 c4)) ▸ done


-- box-perm-2431 @02142041: 3 steps
lem-box-perm-2431-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2431-at02142041 c4 = run b0
  where
  b0 : Chain (Bx2-4031 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-sym-bc-at02142041 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-pairs-at0213243041 c4) ▸ done


-- sym-ab @0314203241: 18 steps
lem-sym-ab-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-sym-ab-at0314203241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-4021 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (sym (wl1155 (lit c4))) ▸
       at 4 1 (Bx3-01 ∷ []) (refl) ▸
       at 7 1 (Bx3-01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ [])
  b1 = at 2 6 (Bx0-321 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (sym (wl1155 (lit c4))) ▸
       at 7 1 (Bx3-01 ∷ []) (refl) ▸
       at 10 1 (Bx3-01 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (Bx3-0421 ∷ [])
  b2 = at 5 6 (Bx0-321 ∷ []) (refl) ▸
       at 0 6 (Bx3-0421 ∷ []) (refl) ▸ done


-- P-box @0310243241: 8 steps
lem-P-box-at0310243241 : Ws → ⟪ (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-P-box-at0310243241 c4 = run b0
  where
  b0 : Chain (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 1 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4) ▸
       at 0 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0310243241 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ12 ∷ Toff312 ∷ []) (sym (wl0504 (lit c4))) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (sym (lem-tP-at0310243241 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ12 ∷ []) (sym (wl0505 (lit c4))) ▸
       at 2 2 (Toff304 ∷ CZ12 ∷ []) (lem-comm-CZ12-TOFF304 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0506 (lit c4))) ▸
       at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-tQ-at0310243241 c4)) ▸ done


-- cQ @03122130: 7 steps
lem-cQ-at03122130 : Ws → ⟪ (CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at03122130 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 1 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸ done


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


-- pairs @0310243241: 4 steps
lem-pairs-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-pairs-at0310243241 c4 = run b0
  where
  b0 : Chain (Bx3-0421 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 1 (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) (sym (lem-P-box-at0310243241 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243241 c4) ▸
       at 4 2 [] (wl0489 (lit c4)) ▸
       at 0 4 (Bx3-2104 ∷ []) (sym (lem-box-tQ-at03122130 c4)) ▸ done


-- CXbc-box @03122130: 17 steps
lem-CXbc-box-at03122130 : Ws → ⟪ (CX10 ∷ Bx3-2104 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXbc-box-at03122130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx3-2104 ∷ CX10 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX10 ∷ CCZ134 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CCZ034 ∷ CX21 ∷ CS24 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at03122130 c4) ▸
       at 0 2 (Toff312 ∷ CX10 ∷ []) (wl0537 (lit c4)) ▸
       at 1 2 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (sym (wp0225 c4)) ▸
       at 3 2 (Toff312 ∷ CCZ134 ∷ CCZ124 ∷ []) (wl1356 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CX10 ∷ []) (wl0537 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 8 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CX10 ∷ CCZ134 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CCZ034 ∷ CX21 ∷ CS24 ∷ CX10 ∷ []) (Bx3-2104 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ [])
  b1 = at 7 2 (CCZ034 ∷ CS14⁻ ∷ []) (sym (wp0123 c4)) ▸
       at 6 2 (CCZ034 ∷ CX21 ∷ []) (lem-comm-CX21-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 3 2 (CCZ034 ∷ CX10 ∷ CCZ134 ∷ []) (sym (wp0225 c4)) ▸
       at 4 3 (CX10 ∷ []) (wp0226 c4) ▸
       at 0 4 (Bx3-2104 ∷ []) (sym (lem-box-tQ-at03122130 c4)) ▸ done

  b2 : Chain (Bx3-2104 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ []) (Bx3-2104 ∷ CCZ124 ∷ [])
  b2 = at 1 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸ done


-- CXcb-box @03122130: 18 steps
lem-CXcb-box-at03122130 : Ws → ⟪ (CX01 ∷ Bx3-2104 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at03122130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx3-2104 ∷ CX01 ∷ []) (Toff312 ∷ CCZ034 ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CX20 ∷ Toff312 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ CCZ034 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at03122130 c4) ▸
       at 0 2 (Toff312 ∷ CX01 ∷ Toff302 ∷ []) (wl1357 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp1202 c4)) ▸
       at 1 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 4 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 8 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX20 ∷ []) (wl0534 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸ done

  b1 : Chain (Toff312 ∷ CCZ034 ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CX20 ∷ Toff312 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ CCZ034 ∷ CX01 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ [])
  b1 = at 5 2 (Toff312 ∷ CX20 ∷ []) (wl0534 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF312 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸
       at 3 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CX01 ∷ Toff302 ∷ []) (wl1357 (lit c4)) ▸
       at 3 3 (CX01 ∷ []) (wl1359 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 3 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b2 : Chain (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ []) (Bx3-2104 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-2104 ∷ []) (sym (lem-box-tQ-at03122130 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0670 c4)) ▸ done


-- SWbc-box @03122130: 11 steps
lem-SWbc-box-at03122130 : Ws → ⟪ (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-SWbc-box-at03122130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (CX10 ∷ Bx3-2104 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ [])
  b0 = at 0 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 4 1 (CX10 ∷ CX01 ∷ CX10 ∷ []) (sym (wl0755 (lit c4))) ▸
       at 2 3 (Bx3-2104 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03122130 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸
       at 1 3 (Bx3-2104 ∷ CCZ024 ∷ []) (lem-CXcb-box-at03122130 c4) ▸
       at 4 2 (CX10 ∷ CCZ124 ∷ []) (wp0672 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 2 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸ done

  b1 : Chain (CX10 ∷ Bx3-2104 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ []) (Bx3-2104 ∷ [])
  b1 = at 3 5 (CCZ124 ∷ []) (wp0674 c4) ▸
       at 0 3 (Bx3-2104 ∷ CCZ124 ∷ []) (lem-CXbc-box-at03122130 c4) ▸
       at 1 2 [] (wl0263 (lit c4)) ▸ done


-- nat-SWbc @03122130: 23 steps
lem-nat-SWbc-at03122130 : Ws → ⟪ (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-nat-SWbc-at03122130 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ Sw01 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx2-304 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 3 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 4 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 5 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ Sw01 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ Bx2-304 ∷ Sw01 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Sw01 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 7 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 8 2 (Toff302 ∷ Sw01 ∷ []) (wl0063 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 11 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 12 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Sw01 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Sw01 ∷ []) (Bx3-2014 ∷ [])
  b2 = at 13 2 (Toff213 ∷ Sw01 ∷ []) (wl0136 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 15 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx2-314 ∷ []) (refl) ▸
       at 5 6 (Bx2-314 ∷ []) (refl) ▸
       at 0 6 (Bx3-2014 ∷ []) (refl) ▸ done


-- sym-bc @03122130: 2 steps
lem-sym-bc-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-sym-bc-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-2104 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at03122130 c4)) ▸
       at 0 3 (Bx3-2014 ∷ []) (lem-nat-SWbc-at03122130 c4) ▸ done


-- box-perm-3241 @0314203241: 3 steps
lem-box-perm-3241-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-box-perm-3241-at0314203241 c4 = run b0
  where
  b0 : Chain (Bx3-4021 ∷ []) (Bx3-2014 ∷ [])
  b0 = at 0 1 (Bx3-0421 ∷ []) (lem-sym-ab-at0314203241 c4) ▸
       at 0 1 (Bx3-2104 ∷ []) (lem-pairs-at0310243241 c4) ▸
       at 0 1 (Bx3-2014 ∷ []) (lem-sym-bc-at03122130 c4) ▸ done


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


-- pairs @021021: 4 steps
lem-pairs-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-pairs-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-3401 ∷ [])
  b0 = at 0 1 (Toff234 ∷ Bx2-0134 ∷ Toff234 ∷ []) (sym (lem-P-box-at021021 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at021021 c4) ▸
       at 4 2 [] (wl0420 (lit c4)) ▸
       at 0 4 (Bx2-3401 ∷ []) (sym (lem-box-tQ-at0213243041 c4)) ▸ done


-- box-perm-1243 @021021: 3 steps
lem-box-perm-1243-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-1243-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0143 ∷ [])
  b0 = at 0 1 (Bx2-3401 ∷ []) (lem-pairs-at021021 c4) ▸
       at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-0143 ∷ []) (lem-pairs-at0214233041 c4) ▸ done


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


-- VPQ @03122031: 14 steps
lem-VPQ-at03122031 : Ws → ⟪ (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) ⟫ʷ
lem-VPQ-at03122031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS02⁻ ∷ S3 ∷ Toff302 ∷ S3⁻ ∷ []) (sym (wl0784 (lit c4))) ▸
       at 4 2 (CS14⁻ ∷ S3 ∷ Toff314 ∷ S3⁻ ∷ []) (sym (wl0783 (lit c4))) ▸
       at 3 2 (CS14⁻ ∷ S3⁻ ∷ []) (sym (wl0786 (lit c4))) ▸
       at 2 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 1 2 (CS14⁻ ∷ S3 ∷ []) (sym (wl0785 (lit c4))) ▸
       at 0 2 (CS14⁻ ∷ CS02⁻ ∷ []) (wp0703 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03122031 c4) ▸ done

  b1 : Chain (CS14⁻ ∷ CS02⁻ ∷ S3 ∷ Toff314 ∷ Toff302 ∷ S3⁻ ∷ []) (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S)) ▸
       at 2 2 (Toff314 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-TOFF314 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS02⁻ ∷ []) (c₃ (Swap ↑ • (CS • CS • CS) • Swap ↑) (S • S • S)) ▸
       at 0 4 (Toff314 ∷ CCZ134 ∷ []) (wl0783 (lit c4)) ▸
       at 2 4 (Toff302 ∷ CCZ023 ∷ []) (wl0784 (lit c4)) ▸ done


-- QVQ @03122031: 3 steps
lem-QVQ-at03122031 : Ws → ⟪ (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) ⟫ʷ ≈ ⟪ (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-QVQ-at03122031 c4 = run b0
  where
  b0 : Chain (CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ134 ∷ []) (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 1 4 (Toff302 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ []) (sym (lem-VPQ-at03122031 c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸ done


-- box-cP @03122031: 12 steps
lem-box-cP-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) ⟫ʷ
lem-box-cP-at03122031 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ CCZ123 ∷ Toff213 ∷ CZ24 ∷ Toff213 ∷ CCZ123 ∷ CZ24 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b1 = at 5 6 (CCZ134 ∷ []) (wl1303 (lit c4)) ▸
       at 2 4 (Toff314 ∷ Toff302 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-QVQ-at03122031 c4) ▸
       at 1 2 (Toff314 ∷ Toff302 ∷ []) (lem-tP-at03122031 c4) ▸
       at 2 2 [] (wl0787 (lit c4)) ▸ done


-- box-perm-1243 @0210213443: 3 steps
lem-box-perm-1243-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-1243-at0210213443 c4 = run b0
  where
  b0 : Chain (Bx2-0143 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-4301 ∷ []) (lem-pairs-at0210213443 c4) ▸
       at 0 1 (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-pairs-at0213243041 c4) ▸ done

