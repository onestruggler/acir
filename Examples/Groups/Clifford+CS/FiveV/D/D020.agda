{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D020 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0155 ; wl0181 ; wl0199 ; wl0204 ; wl0220 ; wl0222 ; wl0230 ; wl0256 ; wl0263 ; wl0316 ; wl0322 ; wl0323 ; wl0332 ; wl0336 ; wl0341 ; wl0405 ; wl0432 ; wl0433 ; wl0436 ; wl0441 ; wl0442 ; wl0487 ; wl0488 ; wl0489 ; wl0497 ; wl0499 ; wl0500 ; wl0501 ; wl0504 ; wl0505 ; wl0506 ; wl0698 ; wl0778 ; wl0779 ; wl0780 ; wl0781 ; wl0782 ; wl0783 ; wl0784 ; wl0785 ; wl0786 ; wl0787 ; wl0788 ; wl0803 ; wl0804 ; wl0858 ; wl0861 ; wl0862 ; wl0871 ; wl0878 ; wl0879 ; wl0888 ; wl0928 ; wl0961 ; wl1126 ; wl1183 ; wl1185 ; wl1189 ; wl1190 ; wl1191 ; wl1192 ; wl1193 ; wl1194 ; wl1195 ; wl1196 ; wl1197 ; wl1198 ; wl1199 ; wl1200 ; wl1201 ; wl1202 ; wl1203 ; wl1204 ; wl1205 ; wl1206 ; wl1207 ; wl1208 ; wl1209 ; wl1210 ; wl1211 ; wl1212 ; wl1213 ; wl1214 ; wl1215 ; wl1216 ; wl1217 ; wl1218 ; wl1219 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1224 ; wl1225 ; wl1226 ; wl1227 ; wl1228 ; wl1229 ; wl1230 ; wl1231 ; wl1232 ; wp0001 ; wp0002 ; wp0003 ; wp0007 ; wp0029 ; wp0041 ; wp0046 ; wp0047 ; wp0048 ; wp0106 ; wp0107 ; wp0108 ; wp0120 ; wp0124 ; wp0129 ; wp0161 ; wp0170 ; wp0261 ; wp0269 ; wp0272 ; wp0294 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0351 ; wp0572 ; wp0575 ; wp0576 ; wp0578 ; wp0700 ; wp0701 ; wp0702 ; wp0703 ; wp0716 ; wp0725 ; wp0733 ; wp0823 ; wp1003 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1009 ; wp1010 ; wp1011 ; wp1012 ; wp1013 ; wp1014 ; wp1015 ; wp1016 ; wp1017 ; wp1018 ; wp1019 ; wp1020 ; wp1021 ; wp1022 ; wp1023 ; wp1024 ; wp1025 ; wp1026 ; wp1027 ; wp1028 ; wp1029 ; wp1030 ; wp1031 ; wp1032 ; wp1033 ; wp1034)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-tQ-at0310243142 ; lem-sym-ab-at0310243142 ; lem-tP-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-cP-at0310243142 ; lem-box-cP-at0314203142 ; lem-sym-ab-at0314203142 ; lem-tP-at0310243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D008 using (lem-box-tQ-at0314203142)
open import Examples.Groups.Clifford+CS.FiveV.D.D009 using (lem-F0-at14213243 ; lem-box-tQ-at033440 ; lem-cQ-at033440)
open import Examples.Groups.Clifford+CS.FiveV.D.D012 using (lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.FiveV.D.D018 using (lem-sym-bc-at143143)
open import Examples.Groups.Clifford+CS.FiveV.D.D019 using (lem-F0-B-at01143043 ; lem-box-cP-at0314213240 ; lem-box-cP-at03143140 ; lem-box-perm-1324-at03143140 ; lem-box-perm-2314-at243243 ; lem-box-tQ-at03143140 ; lem-box-tQ-at03243240 ; lem-cQ-at03243240 ; lem-tP-at03143140)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CX12-CCZ034 ; lem-comm-CX14-CCZ023)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CX14-TOFF023)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS04-TOFF312 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CZ04-TOFF312 ; lem-comm-CZ12-TOFF304 ; lem-comm-TOFF312-CSd04)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CS02-TOFF314 ; lem-comm-CSd02-TOFF314 ; lem-comm-CSd14-TOFF302 ; lem-comm-CZ14-TOFF302 ; lem-comm-CZ24-TOFF301 ; lem-comm-TOFF312-CX04 ; lem-comm-TOFF314-CSd02)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ034-CX12 ; lem-comm-CCZ134-CX02 ; lem-comm-CX14-TOFF302 ; lem-comm-TOFF024-CS13 ; lem-comm-TOFF302-CX14)
-- CSdu-box-3 @03143140: 17 steps
lem-CSdu-box-3-at03143140 : Ws → ⟪ (CS13⁻ ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13⁻ ∷ Bx3-4210 ∷ []) (CCZ234 ∷ Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CS01 ∷ CCZ234 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff301 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143140 c4) ▸
       at 0 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 1 2 (Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ []) (wl1191 (lit c4)) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 7 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸ done

  b1 : Chain (CCZ234 ∷ Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CS01 ∷ CCZ234 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff301 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS13⁻ ∷ [])
  b1 = at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 5 2 (Toff301 ∷ CZ01 ∷ CCZ013 ∷ []) (wl1192 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS01⁻ ∷ []) (wl1193 (lit c4)) ▸
       at 3 2 (Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ []) (wl1191 (lit c4)) ▸
       at 4 6 (CS13⁻ ∷ []) (wl1194 (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS13⁻ ∷ []) (Bx3-4210 ∷ CS13⁻ ∷ [])
  b2 = at 0 4 (Bx3-4210 ∷ []) (sym (lem-box-cP-at03143140 c4)) ▸ done


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


-- CSu-box-3 @03143140: 17 steps
lem-CSu-box-3-at03143140 : Ws → ⟪ (CS13 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at03143140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13 ∷ Bx3-4210 ∷ []) (CCZ234 ∷ Toff301 ∷ CS13 ∷ CS01 ∷ CS01 ∷ CCZ234 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff301 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143140 c4) ▸
       at 0 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 1 2 (Toff301 ∷ CS13 ∷ CS01 ∷ CCZ013 ∷ []) (wl1200 (lit c4)) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 7 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CX31 ∷ []) (sym (wl0336 (lit c4))) ▸ done

  b1 : Chain (CCZ234 ∷ Toff301 ∷ CS13 ∷ CS01 ∷ CS01 ∷ CCZ234 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ Toff301 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS13 ∷ [])
  b1 = at 4 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 5 2 (Toff301 ∷ CZ01 ∷ CCZ013 ∷ []) (wl1192 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS01 ∷ []) (wl1201 (lit c4)) ▸
       at 3 2 (Toff301 ∷ CS13 ∷ CS01 ∷ CCZ013 ∷ []) (wl1200 (lit c4)) ▸
       at 4 6 (CS13 ∷ []) (wl1202 (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CS13 ∷ []) (Bx3-4210 ∷ CS13 ∷ [])
  b2 = at 0 4 (Bx3-4210 ∷ []) (sym (lem-box-cP-at03143140 c4)) ▸ done


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


-- box2 @03143140: 11 steps
lem-box2-at03143140 : Ws → ⟪ (Bx3-4210 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03143140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4210 ∷ Bx3-4210 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ [])
  b0 = at 0 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4) ▸
       at 4 1 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143140 c4) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 5 5 (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff324 ∷ []) (lem-t-cP-at03143140 c4) ▸
       at 5 4 (Bx3-4210 ∷ []) (sym (lem-box-cP-at03143140 c4)) ▸
       at 5 1 (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4) ▸
       at 4 2 [] (wl0442 (lit c4)) ▸
       at 3 2 [] (wl0230 (lit c4)) ▸ done

  b1 : Chain (Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) []
  b1 = at 2 2 [] (wl0442 (lit c4)) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸
       at 0 2 [] (wl0442 (lit c4)) ▸ done


-- box-perm-3124 @143143: 2 steps
lem-box-perm-3124-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-3124-at143143 c4 = run b0
  where
  b0 : Chain (Bx0-4213 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-sym-bc-at143143 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done


-- CXuA-S @01143043: 44 steps
lem-CXuA-S-at01143043 : Ws → ⟪ (CX03 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CX03 ∷ []) ⟫ʷ
lem-CXuA-S-at01143043 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX03 ∷ Sb0-1-42-3 ∷ []) (Bx0-4213 ∷ Bx3-4210 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Bx3-4210 ∷ CS13⁻ ∷ CX03 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (Bx0-4213 ∷ []) (lem-box-perm-2314-at243243 c4) ▸
       at 2 0 (CX03 ∷ CX03 ∷ []) (sym (wl1205 (lit c4))) ▸
       at 0 3 (Bx0-4213 ∷ Bx3-4210 ∷ []) (lem-F0-B-at01143043 c4) ▸
       at 2 5 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx3-4210 ∷ CX03 ∷ []) (lem-F0-R-at01143043 c4) ▸
       at 5 2 (Bx3-4210 ∷ CS13⁻ ∷ []) (lem-CSdu-box-3-at03143140 c4) ▸ done

  b1 : Chain (Bx0-4213 ∷ Bx3-4210 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Bx3-4210 ∷ CS13⁻ ∷ CX03 ∷ []) (Bx0-4213 ∷ Bx3-4210 ∷ Toff324 ∷ CS13 ∷ CCZ134 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS13⁻ ∷ CX03 ∷ [])
  b1 = at 5 1 (Bx3-4120 ∷ []) (lem-box-perm-1324-at03143140 c4) ▸
       at 5 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 4 2 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1189 (lit c4))) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 9 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4) ▸
       at 7 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸ done

  b2 : Chain (Bx0-4213 ∷ Bx3-4210 ∷ Toff324 ∷ CS13 ∷ CCZ134 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS13⁻ ∷ CX03 ∷ []) (Bx0-4213 ∷ Bx3-4210 ∷ Toff324 ∷ Bx3-4210 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX03 ∷ [])
  b2 = at 6 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 5 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 6 3 (CCZ134 ∷ Toff324 ∷ []) (sym (wl1206 (lit c4))) ▸
       at 7 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 4 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 4 1 (Bx3-4210 ∷ []) (sym (lem-box-perm-1324-at03143140 c4)) ▸
       at 3 2 (Bx3-4210 ∷ CS13 ∷ []) (lem-CSu-box-3-at03143140 c4) ▸ done

  b3 : Chain (Bx0-4213 ∷ Bx3-4210 ∷ Toff324 ∷ Bx3-4210 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX03 ∷ []) (Bx0-4213 ∷ Bx3-4210 ∷ CCZ134 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX03 ∷ [])
  b3 = at 3 1 (Bx3-4120 ∷ []) (lem-box-perm-1324-at03143140 c4) ▸
       at 3 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 2 2 (CCZ134 ∷ Toff324 ∷ CCZ124 ∷ []) (sym (wl1189 (lit c4))) ▸
       at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4) ▸
       at 5 2 (Toff302 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF302 (lit c4)) ▸ done

  b4 : Chain (Bx0-4213 ∷ Bx3-4210 ∷ CCZ134 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX03 ∷ []) (Bx0-4213 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX03 ∷ [])
  b4 = at 4 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 4 3 (CCZ134 ∷ Toff324 ∷ []) (sym (wl1206 (lit c4))) ▸
       at 5 2 (Toff302 ∷ Toff324 ∷ []) (sym (wp1007 c4)) ▸
       at 2 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 2 1 (Bx3-4210 ∷ []) (sym (lem-box-perm-1324-at03143140 c4)) ▸
       at 1 2 [] (lem-box2-at03143140 c4) ▸ done

  b5 : Chain (Bx0-4213 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX03 ∷ []) (Sb0-1-42-3 ∷ CX03 ∷ [])
  b5 = at 0 1 (Bx0-1423 ∷ []) (lem-box-perm-3124-at143143 c4) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- CXu-box-4 @243243: 15 steps
lem-CXu-box-4-at243243 : Ws → ⟪ (CX30 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CX30 ∷ []) ⟫ʷ
lem-CXu-box-4-at243243 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX30 ∷ Bx0-1423 ∷ []) (CCZ014 ∷ CX30 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ [])
  b0 = at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (sym (wp1010 c4)) ▸
       at 2 1 (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl0698 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 5 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CS34⁻ ∷ []) (wp0823 c4) ▸
       at 3 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸ done

  b1 : Chain (CCZ014 ∷ CX30 ∷ Toff023 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ []) (Bx0-1423 ∷ CX30 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (sym (wl0698 (lit c4))) ▸
       at 1 2 (Toff023 ∷ CX30 ∷ []) (wl1207 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 2 2 (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (sym (wp1010 c4)) ▸
       at 3 3 (CX30 ∷ []) (wp1011 c4) ▸
       at 3 2 (Toff023 ∷ CX30 ∷ []) (wl1207 (lit c4)) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done


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


-- SW-S @01143043: 5 steps
lem-SW-S-at01143043 : Ws → ⟪ (Sw03 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sw03 ∷ []) ⟫ʷ
lem-SW-S-at01143043 c4 = run b0
  where
  b0 : Chain (Sw03 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ Sw03 ∷ [])
  b0 = at 0 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 2 2 (Sb0-1-42-3 ∷ CX03 ∷ []) (lem-CXuA-S-at01143043 c4) ▸
       at 1 2 (Sb0-1-42-3 ∷ CX30 ∷ []) (lem-CXAu-S-at01143043 c4) ▸
       at 0 2 (Sb0-1-42-3 ∷ CX03 ∷ []) (lem-CXuA-S-at01143043 c4) ▸
       at 1 3 (Sw03 ∷ []) (wl0961 (lit c4)) ▸ done


-- nat-S @01143043: 31 steps
lem-nat-S-at01143043 : Ws → ⟪ (Sw03 ∷ Sb0-1-42-3 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-nat-S-at01143043 c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sw03 ∷ Sb0-1-42-3 ∷ Sw03 ∷ []) (CCZ134 ∷ Toff314 ∷ Sw03 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff014 ∷ Bx1-023 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw03 ∷ []) (sym (wp1014 c4)) ▸
       at 1 2 (Toff314 ∷ Sw03 ∷ []) (wp1015 c4) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸
       at 5 1 (CZ13 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ Sw03 ∷ CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff014 ∷ CCZ014 ∷ Bx1-023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Sw03 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ [])
  b1 = at 8 1 (CZ13 ∷ []) (refl) ▸
       at 2 7 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ Sw03 ∷ []) (sym (wl1210 (lit c4))) ▸
       at 4 1 (Bx3-10 ∷ []) (refl) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸
       at 2 6 (Bx1-320 ∷ []) (refl) ▸
       at 3 2 (Toff314 ∷ Sw03 ∷ []) (wp1015 c4) ▸
       at 4 2 (CCZ134 ∷ Sw03 ∷ []) (sym (wp1014 c4)) ▸
       at 6 1 (CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Sw03 ∷ CCZ012 ∷ Toff102 ∷ Bx0-13 ∷ Toff102 ∷ CCZ012 ∷ Bx0-13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ []) (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ Toff024 ∷ CS01 ∷ Sw03 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ [])
  b2 = at 8 1 (CZ13 ∷ []) (refl) ▸
       at 11 1 (CZ13 ∷ []) (refl) ▸
       at 5 7 (CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ Sw03 ∷ []) (sym (wl1210 (lit c4))) ▸
       at 7 1 (Bx3-10 ∷ []) (refl) ▸
       at 10 1 (Bx3-10 ∷ []) (refl) ▸
       at 5 6 (Bx1-320 ∷ []) (refl) ▸
       at 6 2 (Toff024 ∷ Sw03 ∷ []) (wp1016 c4) ▸
       at 7 2 (CS01 ∷ Sw03 ∷ []) (sym (wl1211 (lit c4))) ▸ done

  b3 : Chain (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ Toff024 ∷ CS01 ∷ Sw03 ∷ Toff324 ∷ CS13⁻ ∷ Sw03 ∷ []) (Sb3-1-42-0 ∷ [])
  b3 = at 8 2 (Toff024 ∷ Sw03 ∷ []) (wp1016 c4) ▸
       at 9 2 (CS01⁻ ∷ Sw03 ∷ []) (sym (wl1212 (lit c4))) ▸
       at 10 2 [] (wl0928 (lit c4)) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸
       at 2 1 (Sb3-1-0-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-1-42-0 ∷ []) (refl) ▸ done


-- F0 @01143043: 3 steps
lem-F0-at01143043 : Ws → ⟪ (Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-42-0 ∷ []) ⟫ʷ
lem-F0-at01143043 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ []) (Sb3-1-42-0 ∷ [])
  b0 = at 0 0 (Sw03 ∷ Sw03 ∷ []) (sym (wl0928 (lit c4))) ▸
       at 1 2 (Sb0-1-42-3 ∷ Sw03 ∷ []) (lem-SW-S-at01143043 c4) ▸
       at 0 3 (Sb3-1-42-0 ∷ []) (lem-nat-S-at01143043 c4) ▸ done


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


-- QVQ @03243240: 3 steps
lem-QVQ-at03243240 : Ws → ⟪ (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-QVQ-at03243240 c4 = run b0
  where
  b0 : Chain (CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ023 ∷ []) (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ [])
  b0 = at 0 0 (Toff302 ∷ Toff302 ∷ []) (sym (wl0787 (lit c4))) ▸
       at 1 4 (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ023 ∷ []) (sym (lem-VPQ-at03243240 c4)) ▸
       at 4 2 [] (wl0204 (lit c4)) ▸ done


-- box-cP @03243240: 12 steps
lem-box-cP-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at03243240 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ CZ01 ∷ Toff123 ∷ CCZ123 ∷ CZ01 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  b1 = at 5 6 (CCZ023 ∷ []) (sym (wl1126 (lit c4))) ▸
       at 2 4 (Toff302 ∷ Toff314 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-QVQ-at03243240 c4) ▸
       at 1 2 (Toff302 ∷ Toff314 ∷ []) (lem-tP-at03243240 c4) ▸
       at 2 2 [] (wl0788 (lit c4)) ▸ done


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


-- pairs @0314203142: 4 steps
lem-pairs-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-pairs-at0314203142 c4 = run b0
  where
  b0 : Chain (Bx3-4012 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 1 (Toff312 ∷ Bx3-4012 ∷ Toff312 ∷ []) (sym (lem-P-box-at0314203142 c4)) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 4 2 [] (wl0489 (lit c4)) ▸
       at 0 4 (Bx3-1240 ∷ []) (sym (lem-box-tQ-at033440 c4)) ▸ done


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


-- SWbc-box @033440: 11 steps
lem-SWbc-box-at033440 : Ws → ⟪ (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-SWbc-box-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (CX24 ∷ Bx3-1240 ∷ CX24 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 4 1 (CX24 ∷ CX42 ∷ CX24 ∷ []) (sym (wl0405 (lit c4))) ▸
       at 2 3 (Bx3-1240 ∷ CCZ012 ∷ []) (lem-CXbc-box-at033440 c4) ▸
       at 3 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸
       at 1 3 (Bx3-1240 ∷ CCZ014 ∷ []) (lem-CXcb-box-at033440 c4) ▸
       at 4 2 (CX24 ∷ CCZ012 ∷ []) (wp0170 c4) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 2 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸ done

  b1 : Chain (CX24 ∷ Bx3-1240 ∷ CX24 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ []) (Bx3-1240 ∷ [])
  b1 = at 3 5 (CCZ012 ∷ []) (wp1024 c4) ▸
       at 0 3 (Bx3-1240 ∷ CCZ012 ∷ []) (lem-CXbc-box-at033440 c4) ▸
       at 1 2 [] (wl0341 (lit c4)) ▸ done


-- nat-SWbc @033440: 23 steps
lem-nat-SWbc-at033440 : Ws → ⟪ (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-nat-SWbc-at033440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ Sw24 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 0 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 1 2 (Toff314 ∷ Sw24 ∷ []) (wl1217 (lit c4)) ▸
       at 3 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 3 2 (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4)) ▸
       at 4 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 5 2 (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4)) ▸ done

  b1 : Chain (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ Sw24 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ Sw24 ∷ []) (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Sw24 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 7 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 8 2 (Toff314 ∷ Sw24 ∷ []) (wl1217 (lit c4)) ▸
       at 9 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 11 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 11 2 (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4)) ▸
       at 12 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸ done

  b2 : Chain (CCZ134 ∷ Toff314 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Sw24 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Sw24 ∷ []) (Bx3-1420 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw24 ∷ []) (wl1219 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 15 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx1-320 ∷ []) (refl) ▸
       at 5 6 (Bx1-320 ∷ []) (refl) ▸
       at 0 6 (Bx3-1420 ∷ []) (refl) ▸ done


-- sym-bc @033440: 2 steps
lem-sym-bc-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-sym-bc-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx3-1240 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at033440 c4)) ▸
       at 0 3 (Bx3-1420 ∷ []) (lem-nat-SWbc-at033440 c4) ▸ done


-- box-perm-3241 @0310243142: 3 steps
lem-box-perm-3241-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-3241-at0310243142 c4 = run b0
  where
  b0 : Chain (Bx3-0412 ∷ []) (Bx3-1420 ∷ [])
  b0 = at 0 1 (Bx3-4012 ∷ []) (lem-sym-ab-at0310243142 c4) ▸
       at 0 1 (Bx3-1240 ∷ []) (lem-pairs-at0314203142 c4) ▸
       at 0 1 (Bx3-1420 ∷ []) (lem-sym-bc-at033440 c4) ▸ done


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


-- box2 @03243240: 11 steps
lem-box2-at03243240 : Ws → ⟪ (Bx3-1420 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03243240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1420 ∷ Bx3-1420 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b0 = at 0 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 4 0 (Toff314 ∷ Toff314 ∷ []) (sym (wl0788 (lit c4))) ▸
       at 5 5 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) (lem-t-cP-at03243240 c4) ▸
       at 5 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 5 1 (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4) ▸
       at 4 2 [] (wl0788 (lit c4)) ▸
       at 3 2 [] (wl0204 (lit c4)) ▸ done

  b1 : Chain (Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) []
  b1 = at 2 2 [] (wl0788 (lit c4)) ▸
       at 1 2 [] (wl0204 (lit c4)) ▸
       at 0 2 [] (wl0788 (lit c4)) ▸ done


-- nf-comm-CSu-CS@0: 282 steps
lem-nf-comm-CSu-CSat0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-nf-comm-CSu-CSat0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 2 1 (CS02 ∷ []) (refl) ▸
       at 4 1 (CS02⁻ ∷ []) (refl) ▸
       at 5 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 7 1 (CS01 ∷ []) (refl) ▸
       at 9 1 (CS01⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b1 = at 5 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 8 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 8 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 7 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 8 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 11 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b2 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b2 = at 12 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 13 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 7 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 8 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 8 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 10 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b3 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b3 = at 10 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 12 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 13 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 6 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 5 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸ done

  b4 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b4 = at 6 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 11 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 5 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 6 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸ done

  b5 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b5 = at 7 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 7 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 10 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 9 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 8 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 7 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 8 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 8 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸ done

  b6 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ [])
  b6 = at 11 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 11 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 10 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 11 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 12 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 14 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 15 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸ done

  b7 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ [])
  b7 = at 16 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 10 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 11 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 9 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 11 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 13 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 13 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸ done

  b8 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ [])
  b8 = at 14 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 15 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 16 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 12 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 9 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 9 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 8 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 9 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸ done

  b9 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ [])
  b9 = at 10 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 12 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 13 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 14 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 8 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 9 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 10 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b10 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b10 = at 10 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 13 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 12 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 11 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 10 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 11 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 0 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸ done

  b11 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b11 = at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 2 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 3 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 4 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 6 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 8 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸ done

  b12 : Chain (CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b12 = at 2 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 3 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 1 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 4 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 5 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 6 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸ done

  b13 : Chain (CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b13 = at 7 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 8 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 4 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 1 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 1 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 0 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 1 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 2 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b14 : Chain (K2 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b14 = at 3 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 4 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 5 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 6 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 0 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b15 : Chain (Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b15 = at 5 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 4 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 3 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 2 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 3 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 6 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b16 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b16 = at 5 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 6 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 5 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b17 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff312 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b17 = at 6 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 6 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 8 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 7 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 9 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b18 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff312 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b18 = at 11 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 4 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 3 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 4 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b19 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02⁻ ∷ Toff312 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b19 = at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 9 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 3 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 5 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 8 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸ done

  b20 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02⁻ ∷ Toff312 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS24 ∷ Toff312 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b20 = at 7 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 6 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 5 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 6 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 6 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 10 1 (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wp1028 c4)) ▸
       at 9 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 10 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸ done

  b21 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS24 ∷ Toff312 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b21 = at 11 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 13 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 14 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 15 2 (K0⁻ ∷ Toff312 ∷ []) (sym (c₁ (K • iI) (Toffᵗ))) ▸
       at 9 7 (Toff024 ∷ []) (wp1028 c4) ▸
       at 8 2 (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1029 c4) ▸
       at 8 1 (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wp1028 c4)) ▸ done

  b22 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff024 ∷ Toff312 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b22 = at 7 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 8 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 11 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 12 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 13 2 (K0⁻ ∷ Toff312 ∷ []) (sym (c₁ (K • iI) (Toffᵗ))) ▸
       at 7 7 (Toff024 ∷ []) (wp1028 c4) ▸ done

  b23 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff024 ∷ Toff312 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ CCZ234 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b23 = at 8 2 (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) (sym (wl0497 (lit c4))) ▸
       at 6 2 (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1029 c4) ▸
       at 9 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b24 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ CCZ234 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b24 = at 8 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wl1227 (lit c4))) ▸
       at 8 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 8 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 11 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 11 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b25 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b25 = at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 10 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 9 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 9 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b26 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS01 ∷ Toff312 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b26 = at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 8 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 9 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 9 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 12 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸ done

  b27 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS01 ∷ Toff312 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS24 ∷ Toff312 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b27 = at 11 2 (CS01 ∷ CCZ034 ∷ []) (wp0001 c4) ▸
       at 10 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 9 2 (CS01 ∷ CCZ034 ∷ []) (wp0001 c4) ▸
       at 10 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 10 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 14 1 (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wp1028 c4)) ▸
       at 13 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 14 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸ done

  b28 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS24 ∷ Toff312 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b28 = at 15 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 17 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 18 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 19 2 (K0⁻ ∷ Toff312 ∷ []) (sym (c₁ (K • iI) (Toffᵗ))) ▸
       at 13 7 (Toff024 ∷ []) (wp1028 c4) ▸
       at 12 2 (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1029 c4) ▸
       at 12 1 (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wp1028 c4)) ▸ done

  b29 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff024 ∷ Toff312 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b29 = at 11 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 12 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 13 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 15 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 16 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 17 2 (K0⁻ ∷ Toff312 ∷ []) (sym (c₁ (K • iI) (Toffᵗ))) ▸
       at 11 7 (Toff024 ∷ []) (wp1028 c4) ▸ done

  b30 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff024 ∷ Toff312 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ CCZ234 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b30 = at 12 2 (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) (sym (wl0497 (lit c4))) ▸
       at 10 2 (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1029 c4) ▸
       at 13 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b31 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ CCZ234 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b31 = at 12 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 13 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 11 3 (CCZ124 ∷ []) (sym (wl1227 (lit c4))) ▸
       at 12 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 12 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 15 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 15 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 14 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b32 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b32 = at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 17 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 18 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 14 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 13 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 13 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b33 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS01⁻ ∷ Toff312 ∷ Bx3-1420 ∷ [])
  b33 = at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 12 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 13 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 13 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 16 2 (CS01⁻ ∷ Toff312 ∷ []) (sym (wl0500 (lit c4))) ▸ done

  b34 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS01⁻ ∷ Toff312 ∷ Bx3-1420 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ [])
  b34 = at 15 2 (CS01⁻ ∷ CCZ034 ∷ []) (wp0120 c4) ▸
       at 14 2 (CS01⁻ ∷ Toff312 ∷ []) (sym (wl0500 (lit c4))) ▸
       at 13 2 (CS01⁻ ∷ CCZ034 ∷ []) (wp0120 c4) ▸
       at 14 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 14 1 (Bx3-1420 ∷ []) (lem-box-perm-3241-at0310243142 c4) ▸
       at 14 2 [] (lem-box2-at03243240 c4) ▸
       at 1 3 (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp1030 c4) ▸
       at 3 2 [] (wp0161 c4) ▸ done

  b35 : Chain (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b35 = at 5 2 [] (wl0263 (lit c4)) ▸
       at 7 2 [] (wl0263 (lit c4)) ▸ done


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


-- SWbc-box @03243240: 11 steps
lem-SWbc-box-at03243240 : Ws → ⟪ (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-SWbc-box-at03243240 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (CX42 ∷ Bx3-1420 ∷ CX42 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 4 1 (CX42 ∷ CX24 ∷ CX42 ∷ []) (sym (wl0316 (lit c4))) ▸
       at 2 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03243240 c4) ▸
       at 3 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 1 3 (Bx3-1420 ∷ CCZ012 ∷ []) (lem-CXcb-box-at03243240 c4) ▸
       at 4 2 (CX42 ∷ CCZ014 ∷ []) (wp0269 c4) ▸
       at 3 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸
       at 2 2 (CX42 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp1022 c4) ▸ done

  b1 : Chain (CX42 ∷ Bx3-1420 ∷ CX42 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CCZ014 ∷ []) (Bx3-1420 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp1032 c4) ▸
       at 0 3 (Bx3-1420 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03243240 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @03243240: 23 steps
lem-nat-SWbc-at03243240 : Ws → ⟪ (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-nat-SWbc-at03243240 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ Sw24 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ Sw24 ∷ [])
  b0 = at 1 1 (CCZ134 ∷ Toff314 ∷ Bx1-320 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw24 ∷ []) (wl1231 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 2 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 3 2 (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4)) ▸
       at 4 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 5 2 (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ Sw24 ∷ CCZ123 ∷ Bx3-10 ∷ Toff314 ∷ CCZ134 ∷ Bx1-320 ∷ Sw24 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Sw24 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Sw24 ∷ [])
  b1 = at 6 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 7 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 8 2 (Toff312 ∷ Sw24 ∷ []) (wl1231 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw24 ∷ []) (sym (wl1218 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx3-10 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ []) (refl) ▸
       at 10 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 11 2 (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4)) ▸
       at 12 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Sw24 ∷ Toff123 ∷ CCZ123 ∷ Bx3-10 ∷ Sw24 ∷ []) (Bx3-1240 ∷ [])
  b2 = at 13 2 (Toff134 ∷ Sw24 ∷ []) (wl1232 (lit c4)) ▸
       at 14 2 (CCZ134 ∷ Sw24 ∷ []) (sym (wl1216 (lit c4))) ▸
       at 15 2 (Bx3-10 ∷ Sw24 ∷ []) (sym (c₂ (CZ) (Swap ↑ • Swap • Swap ↑))) ▸
       at 16 2 [] (wl0322 (lit c4)) ▸
       at 2 6 (Bx1-340 ∷ []) (refl) ▸
       at 5 6 (Bx1-340 ∷ []) (refl) ▸
       at 0 6 (Bx3-1240 ∷ []) (refl) ▸ done


-- sym-bc @03243240: 2 steps
lem-sym-bc-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-sym-bc-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 1 (Sw24 ∷ Bx3-1420 ∷ Sw24 ∷ []) (sym (lem-SWbc-box-at03243240 c4)) ▸
       at 0 3 (Bx3-1240 ∷ []) (lem-nat-SWbc-at03243240 c4) ▸ done


-- box-perm-1324 @03243240: 1 steps
lem-box-perm-1324-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-box-perm-1324-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  b0 = at 0 1 (Bx3-1240 ∷ []) (lem-sym-bc-at03243240 c4) ▸ done


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


-- QVQ @033440: 3 steps
lem-QVQ-at033440 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at033440 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 1 4 (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at033440 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @033440: 12 steps
lem-box-cP-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at033440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-1240 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff312 ∷ Bx1-340 ∷ Toff312 ∷ CCZ123 ∷ Bx1-340 ∷ []) (refl) ▸
       at 2 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff134 ∷ Bx3-10 ∷ Toff134 ∷ CCZ134 ∷ Bx3-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ134 ∷ Toff134 ∷ CZ01 ∷ Toff134 ∷ CCZ134 ∷ CZ01 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (sym (wp0733 c4)) ▸
       at 2 4 (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at033440 c4) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at033440 c4) ▸
       at 2 2 [] (wl0489 (lit c4)) ▸ done


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


-- pairs @033440: 4 steps
lem-pairs-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-pairs-at033440 c4 = run b0
  where
  b0 : Chain (Bx3-1240 ∷ []) (Bx3-4012 ∷ [])
  b0 = at 0 1 (Toff304 ∷ Bx3-1240 ∷ Toff304 ∷ []) (sym (lem-P-box-at033440 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-tQ-at0314203142 c4)) ▸ done


-- box-perm-4213 @03243240: 3 steps
lem-box-perm-4213-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-4213-at03243240 c4 = run b0
  where
  b0 : Chain (Bx3-1420 ∷ []) (Bx3-0412 ∷ [])
  b0 = at 0 1 (Bx3-1240 ∷ []) (lem-sym-bc-at03243240 c4) ▸
       at 0 1 (Bx3-4012 ∷ []) (lem-pairs-at033440 c4) ▸
       at 0 1 (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4) ▸ done


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


-- box2 @0310243142: 11 steps
lem-box2-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0412 ∷ Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 5 5 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) (lem-t-cP-at0310243142 c4) ▸
       at 5 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 5 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 3 2 [] (wl0181 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) []
  b1 = at 2 2 [] (wp0351 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸
       at 0 2 [] (wp0351 c4) ▸ done

