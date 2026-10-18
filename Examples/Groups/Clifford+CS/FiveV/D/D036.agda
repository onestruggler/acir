{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D036 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0018 ; wl0030 ; wl0031 ; wl0135 ; wl0174 ; wl0175 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0180 ; wl0181 ; wl0196 ; wl0271 ; wl0305 ; wl0420 ; wl0436 ; wl0441 ; wl0442 ; wl0443 ; wl0451 ; wl0452 ; wl0487 ; wl0488 ; wl0489 ; wl0560 ; wl0619 ; wl0671 ; wl0674 ; wl0754 ; wl0807 ; wl0808 ; wl0852 ; wl0861 ; wl0878 ; wl0879 ; wl0942 ; wl0982 ; wl1155 ; wl1180 ; wl1192 ; wl1220 ; wl1222 ; wl1233 ; wl1304 ; wl1319 ; wl1340 ; wl1358 ; wl1360 ; wl1361 ; wl1362 ; wl1363 ; wl1364 ; wl1365 ; wl1366 ; wl1367 ; wl1368 ; wl1369 ; wl1370 ; wl1371 ; wl1372 ; wl1373 ; wp0007 ; wp0013 ; wp0014 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0019 ; wp0022 ; wp0027 ; wp0028 ; wp0029 ; wp0048 ; wp0103 ; wp0111 ; wp0135 ; wp0161 ; wp0295 ; wp0296 ; wp0301 ; wp0302 ; wp0343 ; wp0344 ; wp0345 ; wp0346 ; wp0347 ; wp0348 ; wp0349 ; wp0350 ; wp0351 ; wp0352 ; wp0450 ; wp0513 ; wp0550 ; wp0663 ; wp0670 ; wp0671 ; wp0673 ; wp0694 ; wp0698 ; wp0712 ; wp0737 ; wp0768 ; wp0790 ; wp0814 ; wp0997 ; wp0998 ; wp1003 ; wp1006 ; wp1033 ; wp1034 ; wp1046 ; wp1189 ; wp1203 ; wp1204 ; wp1205 ; wp1206 ; wp1207)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-cP-at03102132 ; lem-tP-at03102132)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-box-perm-1324-at03102132 ; lem-box-tQ-at0210213443 ; lem-box-tQ-at03102132)
open import Examples.Groups.Clifford+CS.FiveV.D.D022 using (lem-box-tQ-at0310243241)
open import Examples.Groups.Clifford+CS.FiveV.D.D030 using (lem-box-tQ-at03122031)
open import Examples.Groups.Clifford+CS.FiveV.D.D033 using (lem-L-CCZ-0 ; lem-L-CX01-2)
open import Examples.Groups.Clifford+CS.FiveV.D.D034 using (lem-L-CX10-2 ; lem-Tu-box-at0314203241 ; lem-box-cP-at031031 ; lem-box-perm-2431-at0314203241 ; lem-box-perm-4132-at03102132 ; lem-box-tQ-at02142041 ; lem-box-tQ-at0314203241 ; lem-cQ-at02142041 ; lem-cQ-at0314203241 ; lem-sym-ab-at0213243041 ; lem-sym-bc-at0214233041)
open import Examples.Groups.Clifford+CS.FiveV.D.D035 using (lem-Tu-box-at02142041 ; lem-box-box-3-at03102132 ; lem-box-cP-at03122031 ; lem-box-perm-1243-at021021 ; lem-box-perm-1243-at0210213443 ; lem-box-perm-2431-at02142041 ; lem-box-perm-3241-at02142041 ; lem-box-perm-3241-at0314203241 ; lem-box-perm-4213-at02132031 ; lem-box-tQ-at03122130 ; lem-cQ-at03122130 ; lem-pairs-at021021)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd04-TOFF213 ; lem-comm-CZ04-TOFF213 ; lem-comm-TOFF204-CSd13)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS14-CCZ023 ; lem-comm-CSd04-TOFF312 ; lem-comm-CSd12-TOFF304 ; lem-comm-CSd14-CCZ023 ; lem-comm-CZ04-TOFF312 ; lem-comm-TOFF304-CSd12 ; lem-comm-TOFF312-CSd04)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CSd14-TOFF302 ; lem-comm-TOFF213-CX04 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CS14-TOFF302 ; lem-comm-CX20-CCZ134 ; lem-comm-CX20-TOFF314 ; lem-comm-TOFF314-CX02)
-- box-box-3 @021021: 105 steps
lem-box-box-3-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-box-box-3-at021021 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx2-0134 ∷ Bx3-2014 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ023 ∷ Toff314 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CCZ023 ∷ CS24 ∷ CCZ234 ∷ Toff314 ∷ [])
  b0 = at 0 1 (Bx2-0143 ∷ []) (lem-box-perm-1243-at021021 c4) ▸
       at 0 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 4 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸
       at 3 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 4 2 (Toff314 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl1360 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 5 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ023 ∷ Toff314 ∷ CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CCZ023 ∷ CS24 ∷ CCZ234 ∷ Toff314 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ [])
  b1 = at 8 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 7 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 6 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 6 3 (Toff314 ∷ CCZ234 ∷ []) (wl1361 (lit c4)) ▸
       at 3 4 (Bx3-2014 ∷ []) (sym (lem-box-cP-at03122031 c4)) ▸
       at 3 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ Toff314 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ [])
  b2 = at 2 2 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl1362 (lit c4))) ▸
       at 4 2 (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0997 c4) ▸
       at 3 1 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (sym (wl1363 (lit c4))) ▸
       at 9 2 (Toff314 ∷ K2⁻ ∷ []) (wl1364 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CS12 ∷ []) (wl0982 (lit c4)) ▸
       at 7 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS01⁻ ∷ []) (wp1203 c4) ▸
       at 5 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸ done

  b3 : Chain (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ Toff314 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ Toff314 ∷ Toff201 ∷ CCZ013 ∷ CS14 ∷ CCZ023 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff314 ∷ CCZ234 ∷ [])
  b3 = at 4 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 3 2 (Toff314 ∷ K2 ∷ []) (wl1365 (lit c4)) ▸
       at 4 7 (Toff201 ∷ []) (wl1363 (lit c4)) ▸
       at 6 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 10 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 9 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 8 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸ done

  b4 : Chain (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ Toff314 ∷ Toff201 ∷ CCZ013 ∷ CS14 ∷ CCZ023 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff314 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff314 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ [])
  b4 = at 6 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 5 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl1362 (lit c4))) ▸
       at 5 3 (Toff201 ∷ []) (wl1366 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CCZ014 ∷ []) (wp0698 c4) ▸
       at 5 1 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (sym (wl1363 (lit c4))) ▸
       at 11 2 (Toff314 ∷ K2⁻ ∷ []) (wl1364 (lit c4)) ▸ done

  b5 : Chain (Toff201 ∷ CCZ234 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ Toff314 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ234 ∷ Bx3-2014 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b5 = at 10 2 (Toff314 ∷ CS12 ∷ []) (wl0982 (lit c4)) ▸
       at 9 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CS01⁻ ∷ []) (wp1203 c4) ▸
       at 7 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 5 2 (Toff314 ∷ K2 ∷ []) (wl1365 (lit c4)) ▸
       at 6 7 (Toff201 ∷ []) (wl1363 (lit c4)) ▸
       at 2 4 (Bx3-2014 ∷ []) (sym (lem-box-cP-at03122031 c4)) ▸ done

  b6 : Chain (Toff201 ∷ CCZ234 ∷ Bx3-2014 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (Toff201 ∷ CCZ023 ∷ Toff314 ∷ CS14 ∷ CX21 ∷ CCZ023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ234 ∷ Toff314 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b6 = at 2 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸
       at 1 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 2 2 (Toff314 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl1360 (lit c4)) ▸
       at 4 2 (CCZ023 ∷ CCZ234 ∷ []) (sym (wp0550 c4)) ▸
       at 3 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 7 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 6 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸ done

  b7 : Chain (Toff201 ∷ CCZ023 ∷ Toff314 ∷ CS14 ∷ CX21 ∷ CCZ023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ234 ∷ Toff314 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff201 ∷ Toff314 ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b7 = at 4 2 (CCZ023 ∷ CX21 ∷ []) (sym (wl0674 (lit c4))) ▸
       at 3 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 4 3 (Toff314 ∷ CCZ234 ∷ []) (wl1361 (lit c4)) ▸
       at 1 4 (Bx3-2014 ∷ []) (sym (lem-box-cP-at03122031 c4)) ▸
       at 1 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03122031 c4) ▸
       at 0 2 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl1362 (lit c4))) ▸
       at 2 2 (Toff314 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0997 c4) ▸ done

  b8 : Chain (CCZ023 ∷ Toff201 ∷ Toff314 ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff314 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b8 = at 1 1 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (sym (wl1363 (lit c4))) ▸
       at 7 2 (Toff314 ∷ K2⁻ ∷ []) (wl1364 (lit c4)) ▸
       at 6 2 (Toff314 ∷ CS12 ∷ []) (wl0982 (lit c4)) ▸
       at 5 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CS01⁻ ∷ []) (wp1203 c4) ▸
       at 3 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 2 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 1 2 (Toff314 ∷ K2 ∷ []) (wl1365 (lit c4)) ▸ done

  b9 : Chain (CCZ023 ∷ Toff314 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ013 ∷ CCZ014 ∷ CCZ023 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff314 ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ014 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b9 = at 2 7 (Toff201 ∷ []) (wl1363 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 8 2 (CCZ023 ∷ CS04 ∷ []) (sym (wp0048 c4)) ▸
       at 7 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 6 2 (CCZ023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-CCZ023 (lit c4)) ▸
       at 5 2 (CCZ023 ∷ CX01 ∷ []) (sym (wl0560 (lit c4))) ▸
       at 4 2 (CCZ023 ∷ CS14 ∷ []) (lem-comm-CS14-CCZ023 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

  b10 : Chain (CCZ023 ∷ Toff314 ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ014 ∷ Toff314 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ Toff314 ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b10 = at 3 2 (CCZ023 ∷ CCZ013 ∷ []) (wl0671 (lit c4)) ▸
       at 2 2 (CCZ023 ∷ Toff201 ∷ CCZ013 ∷ []) (sym (wl1362 (lit c4))) ▸
       at 3 3 (Toff201 ∷ []) (wl1366 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CCZ014 ∷ []) (wp0698 c4) ▸
       at 3 1 (K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ []) (sym (wl1363 (lit c4))) ▸
       at 9 2 (Toff314 ∷ K2⁻ ∷ []) (wl1364 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CS12 ∷ []) (wl0982 (lit c4)) ▸
       at 7 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸ done

  b11 : Chain (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ K2 ∷ CS01 ∷ CX20 ∷ CS01⁻ ∷ Toff314 ∷ CX20 ∷ CS12 ∷ K2⁻ ∷ CCZ014 ∷ CCZ234 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx3-2014 ∷ Toff201 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CCZ234 ∷ CS04 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ [])
  b11 = at 6 2 (Toff314 ∷ CS01⁻ ∷ []) (wp1203 c4) ▸
       at 5 2 (Toff314 ∷ CX20 ∷ []) (lem-comm-CX20-TOFF314 (lit c4)) ▸
       at 4 2 (Toff314 ∷ CS01 ∷ []) (wp0029 c4) ▸
       at 3 2 (Toff314 ∷ K2 ∷ []) (wl1365 (lit c4)) ▸
       at 4 7 (Toff201 ∷ []) (wl1363 (lit c4)) ▸
       at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-cP-at03122031 c4)) ▸
       at 2 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 6 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸ done

  b12 : Chain (Bx3-2014 ∷ Toff201 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CCZ234 ∷ CS04 ∷ Toff201 ∷ CCZ014 ∷ CCZ234 ∷ []) (Bx3-2014 ∷ Bx2-0143 ∷ [])
  b12 = at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 4 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 3 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 3 2 (Toff201 ∷ CCZ014 ∷ []) (wp1189 c4) ▸
       at 4 2 [] (wp0161 c4) ▸
       at 1 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸ done

  b13 : Chain (Bx3-2014 ∷ Bx2-0143 ∷ []) (Bx3-2014 ∷ Bx2-0134 ∷ [])
  b13 = at 1 1 (Bx2-0134 ∷ []) (lem-box-perm-1243-at0210213443 c4) ▸ done


-- CXbc-box @03122031: 17 steps
lem-CXbc-box-at03122031 : Ws → ⟪ (CX01 ∷ Bx3-2014 ∷ CX01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXbc-box-at03122031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX01 ∷ Bx3-2014 ∷ CX01 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX01 ∷ CCZ034 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CCZ134 ∷ CX20 ∷ CS24 ∷ CX01 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03122031 c4) ▸
       at 0 2 (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4)) ▸
       at 1 2 (CCZ134 ∷ CX01 ∷ CCZ034 ∷ []) (sym (wp1204 c4)) ▸
       at 3 2 (Toff302 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1205 c4) ▸
       at 2 2 (Toff302 ∷ CX01 ∷ []) (wl1233 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX20 ∷ CS04⁻ ∷ CX20 ∷ CS24 ∷ []) (wp0450 c4) ▸
       at 9 2 (CCZ134 ∷ CS24 ∷ []) (sym (wl1220 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CX01 ∷ CCZ034 ∷ CS04 ∷ CX20 ∷ CS04⁻ ∷ CCZ134 ∷ CX20 ∷ CS24 ∷ CX01 ∷ []) (Bx3-2014 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ [])
  b1 = at 7 2 (CCZ134 ∷ CS04⁻ ∷ []) (sym (wp1206 c4)) ▸
       at 6 2 (CCZ134 ∷ CX20 ∷ []) (lem-comm-CX20-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0450 c4)) ▸
       at 4 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 3 2 (CCZ134 ∷ CX01 ∷ CCZ034 ∷ []) (sym (wp1204 c4)) ▸
       at 4 3 (CX01 ∷ []) (wp1207 c4) ▸
       at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-tQ-at03122031 c4)) ▸ done

  b2 : Chain (Bx3-2014 ∷ CX01 ∷ CCZ024 ∷ CX01 ∷ []) (Bx3-2014 ∷ CCZ024 ∷ [])
  b2 = at 1 3 (CCZ024 ∷ []) (sym (wp0670 c4)) ▸ done


-- CXcb-box @03122031: 18 steps
lem-CXcb-box-at03122031 : Ws → ⟪ (CX10 ∷ Bx3-2014 ∷ CX10 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at03122031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX10 ∷ Bx3-2014 ∷ CX10 ∷ []) (Toff302 ∷ CCZ134 ∷ CX10 ∷ Toff312 ∷ CS14 ∷ CX21 ∷ Toff302 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ134 ∷ CX10 ∷ [])
  b0 = at 1 1 (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03122031 c4) ▸
       at 0 2 (Toff302 ∷ CX10 ∷ Toff312 ∷ []) (wl1367 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Toff312 ∷ CCZ124 ∷ []) (sym (wl1368 (lit c4))) ▸
       at 1 2 (CCZ134 ∷ CX10 ∷ []) (sym (wp0712 c4)) ▸
       at 4 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 2 (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF302 (lit c4)) ▸ done

  b1 : Chain (Toff302 ∷ CCZ134 ∷ CX10 ∷ Toff312 ∷ CS14 ∷ CX21 ∷ Toff302 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ134 ∷ CX10 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ [])
  b1 = at 5 2 (Toff302 ∷ CX21 ∷ []) (wl1304 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF302 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 3 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CX10 ∷ Toff312 ∷ []) (wl1367 (lit c4)) ▸
       at 3 3 (CX10 ∷ []) (wl1369 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ CCZ124 ∷ []) (wl1222 (lit c4)) ▸
       at 3 2 (CCZ134 ∷ CX10 ∷ []) (sym (wp0712 c4)) ▸ done

  b2 : Chain (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ []) (Bx3-2014 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx3-2014 ∷ []) (sym (lem-box-tQ-at03122031 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸ done


-- SWbc-box @03122031: 11 steps
lem-SWbc-box-at03122031 : Ws → ⟪ (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-SWbc-box-at03122031 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (CX01 ∷ Bx3-2014 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 4 1 (CX01 ∷ CX10 ∷ CX01 ∷ []) (sym (wl0619 (lit c4))) ▸
       at 2 3 (Bx3-2014 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03122031 c4) ▸
       at 3 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 1 3 (Bx3-2014 ∷ CCZ124 ∷ []) (lem-CXcb-box-at03122031 c4) ▸
       at 4 2 (CX01 ∷ CCZ024 ∷ []) (wp0022 c4) ▸
       at 3 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸
       at 2 2 (CX01 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0671 c4) ▸ done

  b1 : Chain (CX01 ∷ Bx3-2014 ∷ CX01 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ CCZ124 ∷ CCZ024 ∷ []) (Bx3-2014 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (wp0694 c4) ▸
       at 0 3 (Bx3-2014 ∷ CCZ024 ∷ []) (lem-CXbc-box-at03122031 c4) ▸
       at 1 2 [] (wp0135 c4) ▸ done


-- nat-SWbc @03122031: 23 steps
lem-nat-SWbc-at03122031 : Ws → ⟪ (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-nat-SWbc-at03122031 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ Sw01 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ Sw01 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff302 ∷ Bx2-314 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 1 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 3 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 4 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 5 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ Sw01 ∷ CCZ123 ∷ Bx3-24 ∷ Toff302 ∷ CCZ023 ∷ Bx2-314 ∷ Sw01 ∷ []) (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Sw01 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Sw01 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 7 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 8 2 (Toff312 ∷ Sw01 ∷ []) (wl1340 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw01 ∷ []) (sym (wl0135 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff213 ∷ Bx3-24 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 11 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 12 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff312 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Toff203 ∷ CCZ023 ∷ Bx3-24 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ Bx3-24 ∷ Sw01 ∷ Toff213 ∷ CCZ123 ∷ Bx3-24 ∷ Sw01 ∷ []) (Bx3-2104 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw01 ∷ []) (wl0031 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw01 ∷ []) (sym (wl0030 (lit c4))) ▸
       at 15 2 (Bx3-24 ∷ Sw01 ∷ []) (c₂ (Swap) (Swap ↑ • CZ • Swap ↑)) ▸
       at 16 2 [] (wl0018 (lit c4)) ▸
       at 2 6 (Bx2-304 ∷ []) (refl) ▸
       at 5 6 (Bx2-304 ∷ []) (refl) ▸
       at 0 6 (Bx3-2104 ∷ []) (refl) ▸ done


-- sym-bc @03122031: 2 steps
lem-sym-bc-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-sym-bc-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 0 1 (Sw01 ∷ Bx3-2014 ∷ Sw01 ∷ []) (sym (lem-SWbc-box-at03122031 c4)) ▸
       at 0 3 (Bx3-2104 ∷ []) (lem-nat-SWbc-at03122031 c4) ▸ done


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


-- P-box @03122130: 8 steps
lem-P-box-at03122130 : Ws → ⟪ (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-P-box-at03122130 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) (Bx3-2104 ∷ [])
  b0 = at 1 1 (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at03122130 c4) ▸
       at 0 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at03122130 c4)) ▸
       at 1 2 (CCZ034 ∷ CZ04 ∷ Toff304 ∷ []) (sym (wp0344 c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (sym (lem-tP-at03122130 c4)) ▸
       at 4 3 (CCZ034 ∷ CZ04 ∷ []) (sym (wp0345 c4)) ▸
       at 2 2 (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4)) ▸
       at 3 3 (CCZ034 ∷ []) (sym (wp0346 c4)) ▸
       at 0 4 (Bx3-2104 ∷ []) (sym (lem-box-tQ-at03122130 c4)) ▸ done


-- VPQ @03122130: 14 steps
lem-VPQ-at03122130 : Ws → ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at03122130 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 3 2 (CS04⁻ ∷ S3⁻ ∷ []) (sym (wp0348 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff312 ∷ []) (lem-comm-TOFF312-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S3 ∷ []) (sym (wp0349 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS12⁻ ∷ []) (sym (wp0350 c4)) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at03122130 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS12⁻ ∷ S3 ∷ Toff304 ∷ Toff312 ∷ S3⁻ ∷ []) (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S)) ▸
       at 2 2 (Toff304 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-TOFF304 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS12⁻ ∷ []) (c₃ ((CS • CS • CS) ↑) (S • S • S)) ▸
       at 0 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸
       at 2 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸ done


-- QVQ @03122130: 3 steps
lem-QVQ-at03122130 : Ws → ⟪ (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) ⟫ʷ ≈ ⟪ (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-QVQ-at03122130 c4 = run b0
  where
  b0 : Chain (CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ034 ∷ []) (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 1 4 (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) (sym (lem-VPQ-at03122130 c4)) ▸
       at 4 2 [] (wp0007 c4) ▸ done


-- box-cP @03122130: 12 steps
lem-box-cP-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) ⟫ʷ
lem-box-cP-at03122130 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ123 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ CCZ023 ∷ Toff203 ∷ CZ24 ∷ Toff203 ∷ CCZ023 ∷ CZ24 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b1 = at 5 6 (CCZ034 ∷ []) (wp0111 c4) ▸
       at 2 4 (Toff304 ∷ Toff312 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-QVQ-at03122130 c4) ▸
       at 1 2 (Toff304 ∷ Toff312 ∷ []) (lem-tP-at03122130 c4) ▸
       at 2 2 [] (wl0489 (lit c4)) ▸ done


-- pairs @03122130: 4 steps
lem-pairs-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-pairs-at03122130 c4 = run b0
  where
  b0 : Chain (Bx3-2104 ∷ []) (Bx3-0421 ∷ [])
  b0 = at 0 1 (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) (sym (lem-P-box-at03122130 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at03122130 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 0 4 (Bx3-0421 ∷ []) (sym (lem-box-tQ-at0310243241 c4)) ▸ done


-- sym-ab @0310243241: 18 steps
lem-sym-ab-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-sym-ab-at0310243241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx3-0421 ∷ []) (CCZ034 ∷ Toff304 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff304 ∷ Bx0-321 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 2 1 (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4)) ▸
       at 4 1 (Bx3-41 ∷ []) (refl) ▸
       at 7 1 (Bx3-41 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ Toff304 ∷ CCZ034 ∷ Bx0-321 ∷ []) (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ [])
  b1 = at 2 6 (Bx4-321 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-01 ∷ Toff023 ∷ CCZ023 ∷ Bx3-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (wl1319 (lit c4)) ▸
       at 7 1 (Bx3-41 ∷ []) (refl) ▸
       at 10 1 (Bx3-41 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) (Bx3-4021 ∷ [])
  b2 = at 5 6 (Bx4-321 ∷ []) (refl) ▸
       at 0 6 (Bx3-4021 ∷ []) (refl) ▸ done


-- box-perm-4213 @03122031: 3 steps
lem-box-perm-4213-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-4213-at03122031 c4 = run b0
  where
  b0 : Chain (Bx3-2014 ∷ []) (Bx3-4021 ∷ [])
  b0 = at 0 1 (Bx3-2104 ∷ []) (lem-sym-bc-at03122031 c4) ▸
       at 0 1 (Bx3-0421 ∷ []) (lem-pairs-at03122130 c4) ▸
       at 0 1 (Bx3-4021 ∷ []) (lem-sym-ab-at0310243241 c4) ▸ done


-- box-perm-4132 @021021: 3 steps
lem-box-perm-4132-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-4132-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-4031 ∷ [])
  b0 = at 0 1 (Bx2-3401 ∷ []) (lem-pairs-at021021 c4) ▸
       at 0 1 (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4) ▸
       at 0 1 (Bx2-4031 ∷ []) (lem-sym-bc-at0214233041 c4) ▸ done


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


-- box2 @03102132: 11 steps
lem-box2-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0124 ∷ Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ [])
  b0 = at 0 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 4 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at03102132 c4) ▸
       at 4 0 (Toff301 ∷ Toff301 ∷ []) (sym (wl0443 (lit c4))) ▸
       at 5 5 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ Toff301 ∷ []) (lem-t-cP-at03102132 c4) ▸
       at 5 4 (Bx3-0124 ∷ []) (sym (lem-box-cP-at03102132 c4)) ▸
       at 5 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 4 2 [] (wl0443 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) []
  b1 = at 2 2 [] (wl0443 (lit c4)) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸
       at 0 2 [] (wl0443 (lit c4)) ▸ done


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


-- VPQ @02142041: 14 steps
lem-VPQ-at02142041 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 4 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (sym (wl0177 (lit c4))) ▸
       at 2 2 (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S2 ∷ []) (sym (wl0178 (lit c4))) ▸
       at 0 2 (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS04⁻ ∷ []) (wp0017 c4) ▸
       at 2 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4) ▸
       at 0 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸
       at 2 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸ done


-- QVQ @02142041: 3 steps
lem-QVQ-at02142041 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at02142041 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at02142041 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done


-- box-cP @02142041: 12 steps
lem-box-cP-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at02142041 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at02142041 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4) ▸
       at 2 2 [] (wp0019 c4) ▸ done


-- t-cP @02142041: 5 steps
lem-t-cP-at02142041 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-t-cP-at02142041 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 2 (CCZ024 ∷ Toff204 ∷ CZ04 ∷ []) (sym (wp0027 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4) ▸
       at 2 3 (CCZ024 ∷ Toff204 ∷ []) (sym (wp0028 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02142041 c4) ▸ done


-- box2 @02142041: 11 steps
lem-box2-at02142041 : Ws → ⟪ (Bx2-4031 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at02142041 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-4031 ∷ Bx2-4031 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02142041 c4) ▸
       at 4 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 5 5 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) (lem-t-cP-at02142041 c4) ▸
       at 5 4 (Bx2-4031 ∷ []) (sym (lem-box-cP-at02142041 c4)) ▸
       at 5 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 3 2 [] (wl0181 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) []
  b1 = at 2 2 [] (wp0019 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸
       at 0 2 [] (wp0019 c4) ▸ done


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


-- VPQ @0314203241: 14 steps
lem-VPQ-at0314203241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ []) ⟫ʷ
lem-VPQ-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S3 ∷ Toff304 ∷ S3⁻ ∷ []) (sym (wp0347 c4)) ▸
       at 4 2 (CS12⁻ ∷ S3 ∷ Toff312 ∷ S3⁻ ∷ []) (sym (wl0488 (lit c4))) ▸
       at 3 2 (CS12⁻ ∷ S3⁻ ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S • S • S))) ▸
       at 2 2 (CS12⁻ ∷ Toff304 ∷ []) (lem-comm-TOFF304-CSd12 (lit c4)) ▸
       at 1 2 (CS12⁻ ∷ S3 ∷ []) (sym (c₃ ((CS • CS • CS) ↑) (S))) ▸
       at 0 2 (CS12⁻ ∷ CS04⁻ ∷ []) (wp0350 c4) ▸
       at 4 2 [] (wl0441 (lit c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4) ▸ done

  b1 : Chain (CS12⁻ ∷ CS04⁻ ∷ S3 ∷ Toff312 ∷ Toff304 ∷ S3⁻ ∷ []) (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ [])
  b1 = at 4 0 (S3⁻ ∷ S3 ∷ []) (sym (wl0441 (lit c4))) ▸
       at 1 2 (S3 ∷ CS04⁻ ∷ []) (wp0349 c4) ▸
       at 2 2 (Toff312 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF312 (lit c4)) ▸
       at 3 2 (S3⁻ ∷ CS04⁻ ∷ []) (wp0348 c4) ▸
       at 0 4 (Toff312 ∷ CCZ123 ∷ []) (wl0488 (lit c4)) ▸
       at 2 4 (Toff304 ∷ CCZ034 ∷ []) (wp0347 c4) ▸ done


-- QVQ @0314203241: 3 steps
lem-QVQ-at0314203241 : Ws → ⟪ (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-QVQ-at0314203241 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ123 ∷ []) (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 0 0 (Toff312 ∷ Toff312 ∷ []) (sym (wl0489 (lit c4))) ▸
       at 1 4 (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at0314203241 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done


-- box-cP @0314203241: 12 steps
lem-box-cP-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0314203241 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ034 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ034 ∷ CCZ234 ∷ Toff423 ∷ CZ14 ∷ Toff423 ∷ CCZ234 ∷ CZ14 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (sym (wl1319 (lit c4))) ▸
       at 2 4 (Toff312 ∷ Toff304 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-QVQ-at0314203241 c4) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4) ▸
       at 2 2 [] (wp0351 c4) ▸ done


-- t-cP @0314203241: 5 steps
lem-t-cP-at0314203241 : Ws → ⟪ (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) ⟫ʷ
lem-t-cP-at0314203241 c4 = run b0
  where
  b0 : Chain (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ [])
  b0 = at 0 2 (CCZ034 ∷ Toff304 ∷ CZ04 ∷ []) (sym (wp1033 c4)) ▸
       at 2 2 (Toff312 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF312 (lit c4)) ▸
       at 1 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4) ▸
       at 2 3 (CCZ034 ∷ Toff304 ∷ []) (sym (wp1034 c4)) ▸
       at 3 2 (Toff312 ∷ Toff304 ∷ []) (lem-tP-at0314203241 c4) ▸ done


-- box2 @0314203241: 11 steps
lem-box2-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0314203241 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-4021 ∷ Bx3-4021 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ [])
  b0 = at 0 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 4 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4) ▸
       at 4 0 (Toff304 ∷ Toff304 ∷ []) (sym (wp0351 c4)) ▸
       at 5 5 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) (lem-t-cP-at0314203241 c4) ▸
       at 5 4 (Bx3-4021 ∷ []) (sym (lem-box-cP-at0314203241 c4)) ▸
       at 5 1 (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4) ▸
       at 4 2 [] (wp0351 c4) ▸
       at 3 2 [] (wl0181 (lit c4)) ▸ done

  b1 : Chain (Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) []
  b1 = at 2 2 [] (wp0351 c4) ▸
       at 1 2 [] (wl0181 (lit c4)) ▸
       at 0 2 [] (wp0351 c4) ▸ done


-- nf-cx-ccz@0: 265 steps
lem-nf-cx-cczat0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ []) ⟫ʷ
lem-nf-cx-cczat0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (run b33)))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b0 = at 0 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 1 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 2 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 3 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 4 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 5 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 6 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 7 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸ done

  b1 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ Toff314 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ [])
  b1 = at 4 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 4 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 7 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 5 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 7 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 6 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 7 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸ done

  b2 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ Toff314 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ [])
  b2 = at 8 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 9 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 4 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 5 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 5 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 5 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸ done

  b3 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ [])
  b3 = at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 6 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 7 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 7 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸ done

  b4 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Toff314 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ [])
  b4 = at 10 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 9 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 8 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 10 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 9 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 10 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 12 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸ done

  b5 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Toff314 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ Bx3-0124 ∷ [])
  b5 = at 13 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 9 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 7 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 8 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 8 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 6 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 7 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 7 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸ done

  b6 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ Bx3-0124 ∷ []) (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ Bx3-0124 ∷ [])
  b6 = at 8 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 7 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 7 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 8 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 7 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 7 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸ done

  b7 : Chain (Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ Bx3-0124 ∷ []) (CCZ023 ∷ Toff324 ∷ Toff314 ∷ CCZ024 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b7 = at 8 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 8 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 8 2 [] (lem-box2-at03102132 c4) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 0 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 3 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 2 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 1 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸ done

  b8 : Chain (CCZ023 ∷ Toff324 ∷ Toff314 ∷ CCZ024 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b8 = at 3 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 2 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 3 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 4 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 5 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 6 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 2 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 0 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸ done

  b9 : Chain (Toff324 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-3014 ∷ Bx3-0124 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b9 = at 1 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 1 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 1 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 3 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 2 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 2 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 3 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 2 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸ done

  b10 : Chain (Toff324 ∷ Toff234 ∷ Bx2-3014 ∷ Bx3-0124 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ Toff314 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b10 = at 2 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 3 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 3 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 6 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 4 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 5 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸ done

  b11 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ Toff314 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b11 = at 6 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 8 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 9 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 3 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 4 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 4 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸ done

  b12 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx3-0124 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ Toff314 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b12 = at 4 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 4 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 7 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 5 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 7 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 6 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 7 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸ done

  b13 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ Toff314 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b13 = at 8 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 9 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 4 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 5 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 5 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 5 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸ done

  b14 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ Bx2-4031 ∷ [])
  b14 = at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 6 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 7 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 7 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸ done

  b15 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ Toff324 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Toff314 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Bx2-4031 ∷ [])
  b15 = at 10 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 9 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 8 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 10 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 9 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 10 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 12 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸ done

  b16 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ Toff314 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ [])
  b16 = at 13 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 9 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 7 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 8 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 8 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 9 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 8 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸ done

  b17 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Bx3-0124 ∷ [])
  b17 = at 6 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 7 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 7 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 8 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 7 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 8 2 [] (lem-box2-at02142041 c4) ▸ done

  b18 : Chain (Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Bx2-0134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b18 = at 7 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 2 [] (lem-box2-at03102132 c4) ▸
       at 2 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 3 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 3 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 4 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 3 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 3 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸ done

  b19 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Bx2-0134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Bx2-4031 ∷ Toff234 ∷ Toff324 ∷ [])
  b19 = at 4 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 4 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 5 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 5 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 6 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 5 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 5 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸ done

  b20 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Bx2-4031 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ CCZ024 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ Toff213 ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff324 ∷ [])
  b20 = at 6 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02142041 c4) ▸
       at 9 2 (Toff234 ∷ Toff213 ∷ []) (wl0942 (lit c4)) ▸
       at 8 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0790 c4) ▸
       at 7 2 (Toff234 ∷ Toff213 ∷ []) (wl0942 (lit c4)) ▸
       at 9 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 8 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸ done

  b21 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ CCZ024 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ Toff213 ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ [])
  b21 = at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 12 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 8 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 6 3 (Toff234 ∷ CCZ024 ∷ []) (wp0768 c4) ▸
       at 7 4 (Bx2-4031 ∷ []) (sym (lem-box-cP-at02142041 c4)) ▸
       at 7 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 8 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 8 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸ done

  b22 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ [])
  b22 = at 9 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 8 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 8 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 9 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 8 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 9 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 8 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸ done

  b23 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Bx3-4021 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ [])
  b23 = at 9 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 5 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 6 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸ done

  b24 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Bx3-4021 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Toff312 ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Bx2-4031 ∷ Bx3-4021 ∷ [])
  b24 = at 7 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4) ▸
       at 10 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 9 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 8 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 10 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 9 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸ done

  b25 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Toff312 ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Bx2-4031 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx2-3014 ∷ Bx3-0124 ∷ Bx3-4021 ∷ [])
  b25 = at 12 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 13 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 9 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 7 3 (Toff324 ∷ CCZ034 ∷ []) (wp0737 c4) ▸
       at 8 4 (Bx3-4021 ∷ []) (sym (lem-box-cP-at0314203241 c4)) ▸
       at 8 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 9 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 8 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸ done

  b26 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ Toff324 ∷ Bx2-3014 ∷ Bx3-0124 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-2014 ∷ Bx2-0134 ∷ Bx2-4031 ∷ [])
  b26 = at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 9 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 9 2 [] (lem-box2-at0314203241 c4) ▸
       at 6 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 7 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 7 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 8 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 7 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸ done

  b27 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-2014 ∷ Bx2-0134 ∷ Bx2-4031 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ [])
  b27 = at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 8 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 8 2 [] (lem-box2-at02142041 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4) ▸
       at 6 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 4 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸ done

  b28 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ [])
  b28 = at 5 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 9 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 3 3 (Toff324 ∷ CCZ034 ∷ []) (wp0737 c4) ▸
       at 4 4 (Bx3-4021 ∷ []) (sym (lem-box-cP-at0314203241 c4)) ▸ done

  b29 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff324 ∷ Bx3-4021 ∷ [])
  b29 = at 4 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 5 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 5 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 6 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 5 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 5 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 6 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 6 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4) ▸ done

  b30 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff324 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ Toff312 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Bx3-4021 ∷ [])
  b30 = at 9 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 8 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 7 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 9 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 8 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 11 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b31 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ Toff312 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ [])
  b31 = at 12 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 8 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 6 3 (Toff324 ∷ CCZ034 ∷ []) (wp0737 c4) ▸
       at 7 4 (Bx3-4021 ∷ []) (sym (lem-box-cP-at0314203241 c4)) ▸
       at 7 2 [] (lem-box2-at0314203241 c4) ▸
       at 5 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 6 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 6 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸ done

  b32 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-4021 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ [])
  b32 = at 7 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸
       at 6 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 6 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 7 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸ done

  b33 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ [])
  b33 = at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸ done


-- F1-cx-ccz@0: 13 steps
lem-F1-cx-cczat0 : Ws → ⟪ (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F1-cx-cczat0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ []) (Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Bx2-3014 ∷ [])
  b0 = at 0 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 1 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 2 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 1 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 3 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 2 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 2 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 3 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸ done

  b1 : Chain (Toff234 ∷ Toff234 ∷ Bx3-0124 ∷ Bx2-3014 ∷ []) (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ [])
  b1 = at 2 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 2 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 3 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸
       at 0 2 (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (wl1372 (lit c4)) ▸
       at 0 8 (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (sym (lem-nf-cx-cczat0 c4)) ▸ done


-- L-CCZ013-0: 60 steps
lem-L-CCZ013-0 : Ws → ⟪ (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-L-CCZ013-0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-0214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ [])
  b0 = at 0 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 1 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 2 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 3 45 (Bx3-0124 ∷ []) (lem-L-CCZ-0 c4) ▸
       at 4 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 5 5 (Toff234 ∷ []) (lem-L-CX10-2 c4) ▸
       at 6 5 (Toff324 ∷ []) (lem-L-CX01-2 c4) ▸
       at 3 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸ done

  b1 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx3-0214 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Toff314 ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ [])
  b1 = at 3 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 6 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 4 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 5 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 6 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸ done

  b2 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ Toff314 ∷ CX02 ∷ CS04 ∷ CCZ023 ∷ Toff314 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ [])
  b2 = at 8 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 9 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 3 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 4 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 4 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 4 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 6 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸ done

  b3 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff234 ∷ Bx3-4021 ∷ Toff234 ∷ Toff324 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff324 ∷ Toff314 ∷ [])
  b3 = at 5 3 (Bx3-4021 ∷ Bx2-4031 ∷ []) (lem-Tu-box-at0314203241 c4) ▸
       at 5 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 6 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 5 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 5 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 6 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 6 1 (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4) ▸
       at 9 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸ done

  b4 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff324 ∷ Toff314 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ [])
  b4 = at 8 2 (Toff324 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp1046 c4) ▸
       at 7 2 (Toff324 ∷ Toff314 ∷ []) (wl1180 (lit c4)) ▸
       at 9 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 8 2 (CS24 ∷ Toff314 ∷ []) (sym (wl0754 (lit c4))) ▸
       at 9 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff314 ∷ []) (sym (wl1371 (lit c4))) ▸
       at 11 2 (CX02 ∷ Toff314 ∷ []) (lem-comm-TOFF314-CX02 (lit c4)) ▸
       at 12 2 (CS04 ∷ Toff314 ∷ []) (sym (wp0998 c4)) ▸ done

  b5 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Bx2-4031 ∷ CCZ023 ∷ Toff324 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-2014 ∷ Bx3-0124 ∷ [])
  b5 = at 8 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 6 3 (Toff324 ∷ CCZ023 ∷ []) (wp0814 c4) ▸
       at 7 4 (Bx3-0214 ∷ []) (sym (lem-box-cP-at031031 c4)) ▸
       at 7 1 (Bx3-0124 ∷ []) (sym (lem-box-perm-1324-at03102132 c4)) ▸
       at 5 0 (Toff324 ∷ Toff324 ∷ []) (sym (wl0442 (lit c4))) ▸
       at 6 3 (Bx2-4031 ∷ Bx3-4021 ∷ []) (lem-Tu-box-at02142041 c4) ▸
       at 6 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸
       at 7 1 (Bx3-2014 ∷ []) (lem-box-perm-3241-at0314203241 c4) ▸ done

  b6 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-0134 ∷ Bx3-2014 ∷ Bx3-0124 ∷ []) (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ Bx3-0124 ∷ [])
  b6 = at 6 2 (Bx3-2014 ∷ Bx2-0134 ∷ []) (lem-box-box-3-at021021 c4) ▸
       at 6 1 (Bx3-4021 ∷ []) (lem-box-perm-4213-at03122031 c4) ▸
       at 7 1 (Bx2-4031 ∷ []) (lem-box-perm-4132-at021021 c4) ▸
       at 6 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 1 (Bx2-3014 ∷ []) (lem-box-perm-3241-at02142041 c4) ▸
       at 6 2 (Bx2-3014 ∷ Bx3-0124 ∷ []) (lem-box-box-3-at03102132 c4) ▸
       at 6 1 (Bx2-4031 ∷ []) (lem-box-perm-4213-at02132031 c4) ▸
       at 7 1 (Bx3-4021 ∷ []) (lem-box-perm-4132-at03102132 c4) ▸ done

  b7 : Chain (Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Bx2-4031 ∷ Bx3-4021 ∷ Bx3-0124 ∷ []) (Bx2-0134 ∷ [])
  b7 = at 7 1 (Bx3-0124 ∷ []) (lem-box-perm-2431-at0314203241 c4) ▸
       at 7 2 [] (lem-box2-at03102132 c4) ▸
       at 0 6 [] (wl1373 (lit c4)) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-box-perm-2431-at02142041 c4) ▸ done

