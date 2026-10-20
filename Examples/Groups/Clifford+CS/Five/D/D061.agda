{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D061 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0207 ; wl0230 ; wl0242 ; wl0341 ; wl0415 ; wl0460 ; wl0461 ; wl0463 ; wl0618 ; wl0929 ; wl1433 ; wl1498 ; wl1499 ; wl1500 ; wl1501 ; wl1502 ; wl1503 ; wl1504 ; wl1505 ; wl1506 ; wl1507 ; wl1508 ; wl1509 ; wl1510 ; wl1511 ; wl1512 ; wl1513 ; wl1514 ; wp0053 ; wp0054 ; wp0067 ; wp0081 ; wp0090 ; wp0091 ; wp0092 ; wp0261 ; wp0265 ; wp0279 ; wp0359 ; wp0765 ; wp0896 ; wp1003 ; wp1284 ; wp1285 ; wp1328 ; wp1341 ; wp1342 ; wp1343 ; wp1344 ; wp1345 ; wp1346 ; wp1347 ; wp1348 ; wp1349 ; wl0204 ; wl0307 ; wl1516 ; wl1520 ; wl1525 ; wl1526 ; wl1528 ; wl1530 ; wl1539 ; wl1540 ; wl1541 ; wl1542 ; wl1543 ; wp0124 ; wp0155 ; wp0156 ; wp0157 ; wp1351 ; wp1352 ; wp1353 ; wp1359 ; wp1364 ; wp1365 ; wp1366 ; wp1367 ; wp1368 ; wp1369 ; wp1370 ; wp1371 ; wp1372 ; wl0155 ; wl0289 ; wl1572 ; wl1574 ; wl1575 ; wl1576 ; wl1577 ; wp0021 ; wp0032 ; wp0039 ; wp0384 ; wp1384 ; wp1393 ; wl0280 ; wl0651 ; wl0770 ; wl1131 ; wl1150 ; wl1598 ; wl1605 ; wl1606 ; wl1607 ; wl1608 ; wp0001 ; wp0002 ; wp0003 ; wp0198 ; wp0827 ; wp0919 ; wp1197 ; wp1199 ; wp1411 ; wp1412 ; wl0499 ; wl0500 ; wl0501 ; wl0525 ; wl0806 ; wl1633 ; wp0388 ; wp1143 ; wp1435 ; wl0318 ; wl0679 ; wl1190 ; wl1241 ; wl1251 ; wl1673 ; wl1674 ; wl1675 ; wl1676 ; wl1706 ; wl1707 ; wp0103 ; wp0213 ; wp0374 ; wp1006 ; wp1134 ; wp1438)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-tQ-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-tQ-at04233042)
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0310243142 ; lem-box-cP-at0314213240 ; lem-box-perm-1324-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-CSdu-box-3-at0310213442 ; lem-CSu-box-3-at0310213442 ; lem-box-cP-at02142140 ; lem-box-cP-at04122041 ; lem-box-cP-at0412213043 ; lem-box-cP-at0412233041 ; lem-box-cP-at04233042 ; lem-box-perm-3124-at0210213443 ; lem-box2-at0310213442)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-F0-R-at0410213243 ; lem-Ku-box-at0214203143 ; lem-box-perm-1324-at04122041 ; lem-box-perm-2314-at0214203143 ; lem-box-perm-3241-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-CKdu-box-2-at0214203143 ; lem-F0-B-at0410213243 ; lem-box-perm-1243-at043043 ; lem-box-perm-1243-at0440 ; lem-box-perm-1342-at0440 ; lem-box-perm-1423-at04122041 ; lem-box-perm-1423-at04203243 ; lem-box-perm-1423-at04233042 ; lem-box-perm-4213-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D034 using (lem-S2-SBOX⟨0·2·43·1⟩-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-CCZ124 ; lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-CS02-CCZ134 ; lem-comm-CSd02-CCZ134 ; lem-comm-CX40-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CK02-CCZ134 ; lem-comm-CX23-TOFF401 ; lem-comm-TOFF401-CX23)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ124-CK03 ; lem-comm-CK03-CCZ124 ; lem-comm-CX41-TOFF203 ; lem-comm-CX41-TOFF302)

-- F4-CS1-CS2 @0440: 248 steps
lem-F4-CS1-CS2-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS2-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (run b30))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 4 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 4 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CCZ024 ∷ CS13⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 5 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 5 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b3 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CCZ024 ∷ CS13⁻ ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b3 = at 6 2 (Toff413 ∷ CS13⁻ ∷ []) (wl1500 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 8 2 (Toff413 ∷ CS13⁻ ∷ []) (wl1500 (lit c4)) ▸
       at 5 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 5 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 5 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 4 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 6 2 (Toff401 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp1341 c4) ▸ done

  b4 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff302 ∷ Toff401 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b4 = at 5 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 11 2 (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4) ▸
       at 10 2 (Toff401 ∷ CS02 ∷ []) (wp1343 c4) ▸
       at 9 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4) ▸
       at 7 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 6 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 5 2 (Toff401 ∷ K3 ∷ []) (wp1345 c4) ▸ done

  b5 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ Toff302 ∷ CCZ024 ∷ CCZ234 ∷ CCZ012 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b5 = at 6 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 8 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 12 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 11 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 10 2 (CCZ234 ∷ CS02⁻ ∷ []) (sym (wp0765 c4)) ▸
       at 9 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 8 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 9 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

  b6 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ Toff302 ∷ CCZ024 ∷ CCZ234 ∷ CCZ012 ∷ Toff401 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b6 = at 7 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 7 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 8 2 (Toff401 ∷ CCZ012 ∷ []) (wp0359 c4) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 13 2 (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4) ▸
       at 12 2 (Toff401 ∷ CS02 ∷ []) (wp1343 c4) ▸
       at 11 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸ done

  b7 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ Toff401 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Bx4-2031 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b7 = at 10 2 (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4) ▸
       at 9 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 7 2 (Toff401 ∷ K3 ∷ []) (wp1345 c4) ▸
       at 8 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 4 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 4 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸ done

  b8 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Bx4-2031 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b8 = at 4 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CS13 ∷ []) (wl1502 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 6 2 (Toff413 ∷ CS13 ∷ []) (wl1502 (lit c4)) ▸
       at 3 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 3 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸ done

  b9 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b9 = at 2 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 4 2 (Toff401 ∷ CCZ024 ∷ CCZ012 ∷ []) (wp1341 c4) ▸
       at 3 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 9 2 (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4) ▸
       at 8 2 (Toff401 ∷ CS02 ∷ []) (wp1343 c4) ▸
       at 7 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 6 2 (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4) ▸
       at 5 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ Toff401 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ Toff401 ∷ Toff302 ∷ CCZ024 ∷ CS02 ∷ CCZ234 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b10 = at 4 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 3 2 (Toff401 ∷ K3 ∷ []) (wp1345 c4) ▸
       at 4 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 6 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 10 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 8 2 (CCZ234 ∷ CS02⁻ ∷ []) (sym (wp0765 c4)) ▸
       at 7 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b11 : Chain (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ Toff401 ∷ Toff302 ∷ CCZ024 ∷ CS02 ∷ CCZ234 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff401 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b11 = at 6 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 4 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 5 3 (Toff302 ∷ []) (wp1346 c4) ▸
       at 6 2 (Toff401 ∷ CCZ012 ∷ []) (wp0359 c4) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 11 2 (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4) ▸ done

  b12 : Chain (X0 ∷ Bx4-1023 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b12 = at 10 2 (Toff401 ∷ CS02 ∷ []) (wp1343 c4) ▸
       at 9 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 8 2 (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4) ▸
       at 7 2 (Toff401 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF401 (lit c4)) ▸
       at 6 2 (Toff401 ∷ CS03 ∷ []) (wp1328 c4) ▸
       at 5 2 (Toff401 ∷ K3 ∷ []) (wp1345 c4) ▸
       at 6 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 2 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸ done

  b13 : Chain (X0 ∷ Bx4-1023 ∷ Bx4-2301 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b13 = at 2 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 1 1 (Bx4-2031 ∷ []) (lem-box-perm-3241-at04203243 c4) ▸
       at 2 1 (Bx4-1023 ∷ []) (lem-box-perm-4213-at04122041 c4) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸
       at 2 2 (Toff413 ∷ CZ24 ∷ CCZ123 ∷ []) (wl1498 (lit c4)) ▸
       at 1 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff413 ∷ X0 ∷ CZ24 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff413 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b14 = at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ24 ∷ []) (sym (wp1285 c4)) ▸
       at 2 2 (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (sym (wp1284 c4)) ▸ done

  b15 : Chain (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ X0 ∷ CZ24 ∷ CZ24 ∷ CCZ123 ∷ Toff413 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b15 = at 3 3 (X0 ∷ []) (wl1433 (lit c4)) ▸
       at 4 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 3 2 (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑)) ▸
       at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b16 : Chain (Bx4-2031 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b16 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b17 : Chain (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b17 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 8 (Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) (wl1503 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b18 : Chain (Bx4-2031 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b18 = at 4 3 (CS13 ∷ Toff302 ∷ CCZ012 ∷ []) (wl1504 (lit c4)) ▸
       at 6 2 [] (wl0341 (lit c4)) ▸
       at 4 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸
       at 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b19 : Chain (Bx4-2031 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b19 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff103 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1506 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 5 2 (CX31 ∷ Toff423 ∷ []) (sym (wl1507 (lit c4))) ▸
       at 7 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸
       at 6 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 7 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸
       at 8 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸ done

  b20 : Chain (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff423 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b20 = at 9 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 10 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 11 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ Toff423 ∷ []) (sym (c₂ ((K • iI) ↑) (Toffᵗ))) ▸
       at 6 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸
       at 4 3 (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp1349 c4) ▸
       at 3 2 (CX31 ∷ Toff423 ∷ []) (sym (wl1507 (lit c4))) ▸
       at 5 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸ done

  b21 : Chain (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff423 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff103 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b21 = at 4 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 5 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸
       at 6 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 7 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 8 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 9 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 10 2 (K1⁻ ∷ Toff423 ∷ []) (sym (c₂ ((K • iI) ↑) (Toffᵗ))) ▸
       at 4 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸ done

  b22 : Chain (Bx4-2031 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff103 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b22 = at 2 3 (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp1349 c4) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 4 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸
       at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b23 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS12 ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b23 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS12 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1512 (lit c4))) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 6 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 4 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸ done

  b24 : Chain (Bx4-2031 ∷ Toff103 ∷ X0 ∷ CS12 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ [])
  b24 = at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X0 ∷ []) (sym (wl1511 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff103 ∷ X0 ∷ []) (sym (wl1505 (lit c4))) ▸
       at 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX31 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b25 = at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX31 ∷ Toff103 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1506 (lit c4))) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 7 2 (CX31 ∷ Toff423 ∷ []) (sym (wl1507 (lit c4))) ▸
       at 9 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸
       at 8 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 9 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸
       at 10 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸ done

  b26 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff423 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b26 = at 11 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 12 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 13 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 14 2 (K1⁻ ∷ Toff423 ∷ []) (sym (c₂ ((K • iI) ↑) (Toffᵗ))) ▸
       at 8 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸
       at 6 3 (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp1349 c4) ▸
       at 5 2 (CX31 ∷ Toff423 ∷ []) (sym (wl1507 (lit c4))) ▸
       at 7 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸ done

  b27 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff423 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff103 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ [])
  b27 = at 6 2 (K1 ∷ Toff423 ∷ []) (sym (c₂ (K ↑) (Toffᵗ))) ▸
       at 7 2 (CS03 ∷ Toff423 ∷ []) (sym (wp1347 c4)) ▸
       at 8 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 9 2 (CS03⁻ ∷ Toff423 ∷ []) (sym (wp1348 c4)) ▸
       at 10 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 11 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ Toff423 ∷ []) (sym (c₂ ((K • iI) ↑) (Toffᵗ))) ▸
       at 6 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸ done

  b28 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ X0 ∷ CCZ014 ∷ CX31 ∷ Toff103 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS12⁻ ∷ X0 ∷ [])
  b28 = at 4 3 (CX31 ∷ Toff103 ∷ CCZ014 ∷ []) (wp1349 c4) ▸
       at 6 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 3 (Toff103 ∷ X0 ∷ []) (sym (wl1510 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b29 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS12⁻ ∷ X0 ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b29 = at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 5 (CS12⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1514 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff423 ∷ []) (sym (wl0460 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff423 ∷ []) (sym (wl0460 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸ done

  b30 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ X0 ∷ CS12⁻ ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b30 = at 6 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X0 ∷ []) (sym (wl1513 (lit c4))) ▸
       at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done

-- F4-K2-CS1 @0440: 19 steps
lem-F4-K2-CS1-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-CS1-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (CCZ134 ∷ X0 ∷ CK02 ∷ X0 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (Bx4-1302 ∷ []) (lem-box-perm-1423-at04203243 c4) ▸
       at 3 1 (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) (lem-box-cP-at04233042 c4) ▸
       at 2 2 (CCZ134 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 1 2 (CCZ134 ∷ CK02 ∷ []) (lem-comm-CK02-CCZ134 (lit c4)) ▸
       at 0 2 (CCZ134 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸ done

  b1 : Chain (CCZ134 ∷ X0 ∷ CK02 ∷ X0 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff402 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wp1359 c4)) ▸
       at 4 2 (CCZ134 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 3 2 (CCZ134 ∷ CK02 ∷ []) (lem-comm-CK02-CCZ134 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑)) ▸
       at 3 4 (Toff402 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wp1359 c4)) ▸
       at 0 4 (Bx4-1302 ∷ []) (sym (lem-box-cP-at04233042 c4)) ▸
       at 0 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1423-at04203243 c4)) ▸
       at 1 7 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1530 (lit c4))) ▸ done

  b2 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸ done

-- F4-CS2-CS1 @0440: 254 steps
lem-F4-CS2-CS1-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS1-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (run b31)))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (X0 ∷ Sb4-2-03-1 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 4 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb4-2-03-1 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Sb4-2-03-1 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸
       at 4 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-2-03-1 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CCZ014 ∷ CS12⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wp1353 c4) ▸
       at 6 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 5 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 5 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸ done

  b3 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CCZ014 ∷ CS12⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ014 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff423 ∷ CCZ034 ∷ CCZ023 ∷ CCZ014 ∷ Toff423 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b3 = at 6 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 8 2 (Toff423 ∷ CS12⁻ ∷ []) (wl0460 (lit c4)) ▸
       at 5 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 2 (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) (sym (wp1364 c4)) ▸
       at 6 2 (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ []) (wp1365 c4) ▸
       at 5 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸ done

  b4 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ014 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff423 ∷ CCZ034 ∷ CCZ023 ∷ CCZ014 ∷ Toff423 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ034 ∷ CCZ023 ∷ CCZ014 ∷ Toff423 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b4 = at 11 2 (Toff423 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (Toffᵗ)) ▸
       at 10 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 9 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS03⁻ ∷ []) (wp1348 c4) ▸
       at 7 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS03 ∷ []) (wp1347 c4) ▸
       at 5 2 (Toff423 ∷ K1 ∷ []) (c₂ (K ↑) (Toffᵗ)) ▸
       at 6 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸ done

  b5 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ034 ∷ CCZ023 ∷ CCZ014 ∷ Toff423 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ014 ∷ CCZ034 ∷ CCZ023 ∷ Toff423 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b5 = at 8 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 12 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 9 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 7 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸ done

  b6 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ014 ∷ CCZ034 ∷ CCZ023 ∷ Toff423 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b6 = at 6 2 (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) (sym (wp1364 c4)) ▸
       at 7 3 (Toff103 ∷ []) (wp1366 c4) ▸
       at 8 2 (Toff423 ∷ CCZ023 ∷ []) (wp1367 c4) ▸
       at 7 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸
       at 13 2 (Toff423 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (Toffᵗ)) ▸
       at 12 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 11 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 10 2 (Toff423 ∷ CS03⁻ ∷ []) (wp1348 c4) ▸ done

  b7 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ014 ∷ CS12 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b7 = at 9 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS03 ∷ []) (wp1347 c4) ▸
       at 7 2 (Toff423 ∷ K1 ∷ []) (c₂ (K ↑) (Toffᵗ)) ▸
       at 8 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 3 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸ done

  b8 : Chain (X0 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ014 ∷ CS12 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ014 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff423 ∷ CCZ034 ∷ CCZ023 ∷ CCZ014 ∷ Toff423 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 6 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 3 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) (sym (wp1364 c4)) ▸
       at 4 2 (Toff423 ∷ CCZ034 ∷ CCZ023 ∷ []) (wp1365 c4) ▸
       at 3 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸ done

  b9 : Chain (X0 ∷ Bx4-2031 ∷ CCZ014 ∷ K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ Toff423 ∷ CCZ034 ∷ CCZ023 ∷ CCZ014 ∷ Toff423 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ034 ∷ CCZ023 ∷ CCZ014 ∷ Toff423 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b9 = at 9 2 (Toff423 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 7 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS03⁻ ∷ []) (wp1348 c4) ▸
       at 5 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 4 2 (Toff423 ∷ CS03 ∷ []) (wp1347 c4) ▸
       at 3 2 (Toff423 ∷ K1 ∷ []) (c₂ (K ↑) (Toffᵗ)) ▸
       at 4 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx4-2031 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ034 ∷ CCZ023 ∷ CCZ014 ∷ Toff423 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ014 ∷ CCZ034 ∷ CCZ023 ∷ Toff423 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b10 = at 6 1 (CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ []) (wl0307 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 7 5 (CCZ023 ∷ []) (sym (wl0307 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸ done

  b11 : Chain (X0 ∷ Bx4-2031 ∷ CCZ014 ∷ Toff423 ∷ Toff103 ∷ CCZ014 ∷ CCZ034 ∷ CCZ023 ∷ Toff423 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-2031 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b11 = at 4 2 (CCZ014 ∷ Toff103 ∷ CCZ034 ∷ []) (sym (wp1364 c4)) ▸
       at 5 3 (Toff103 ∷ []) (wp1366 c4) ▸
       at 6 2 (Toff423 ∷ CCZ023 ∷ []) (wp1367 c4) ▸
       at 5 1 (K1 ∷ CS03 ∷ CX10 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1508 (lit c4))) ▸
       at 11 2 (Toff423 ∷ K1⁻ ∷ []) (c₂ ((K • iI) ↑) (Toffᵗ)) ▸
       at 10 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 9 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS03⁻ ∷ []) (wp1348 c4) ▸ done

  b12 : Chain (X0 ∷ Bx4-2031 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ K1 ∷ CS03 ∷ CX10 ∷ Toff423 ∷ CS03⁻ ∷ CX10 ∷ CS13 ∷ K1⁻ ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b12 = at 7 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS03 ∷ []) (wp1347 c4) ▸
       at 5 2 (Toff423 ∷ K1 ∷ []) (c₂ (K ↑) (Toffᵗ)) ▸
       at 6 7 (Toff103 ∷ []) (wl1508 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 1 (Bx4-1023 ∷ []) (lem-box-perm-4213-at04122041 c4) ▸
       at 2 1 (Bx4-2031 ∷ []) (lem-box-perm-3241-at04203243 c4) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸ done

  b13 : Chain (X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b13 = at 0 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 2 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸
       at 1 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b14 : Chain (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ123 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b14 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 3 3 (X0 ∷ []) (wp1353 c4) ▸
       at 4 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done

  b15 : Chain (Bx4-1023 ∷ X0 ∷ CCZ123 ∷ Bx4-2031 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ024 ∷ CCZ123 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b15 = at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done

  b16 : Chain (Bx4-1023 ∷ X0 ∷ CCZ024 ∷ CCZ123 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b16 = at 3 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done

  b17 : Chain (Bx4-1023 ∷ X0 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ CCZ123 ∷ Toff413 ∷ Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b17 = at 5 2 (Toff413 ∷ CCZ123 ∷ []) (wl1499 (lit c4)) ▸
       at 2 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 3 8 (Toff103 ∷ CCZ023 ∷ CS12 ∷ Toff103 ∷ CCZ023 ∷ CS12⁻ ∷ X0 ∷ CCZ123 ∷ []) (wl1539 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸
       at 4 3 (CS12 ∷ Toff103 ∷ CCZ023 ∷ []) (wl1540 (lit c4)) ▸
       at 6 2 [] (wl0204 (lit c4)) ▸
       at 4 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸ done

  b18 : Chain (Bx4-1023 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX23 ∷ Toff302 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b18 = at 2 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 2 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX23 ∷ Toff302 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1541 (lit c4))) ▸
       at 2 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 2 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸ done

  b19 : Chain (Bx4-1023 ∷ X0 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CX23 ∷ Toff302 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX23 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b19 = at 5 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 6 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 7 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 8 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 9 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 10 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 11 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b20 : Chain (Bx4-1023 ∷ X0 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX23 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ234 ∷ CX23 ∷ K3 ∷ CS03 ∷ CX23 ∷ Toff401 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b20 = at 12 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 6 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 4 3 (CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1368 c4) ▸
       at 3 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 4 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 5 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 6 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸ done

  b21 : Chain (Bx4-1023 ∷ X0 ∷ CCZ234 ∷ CX23 ∷ K3 ∷ CS03 ∷ CX23 ∷ Toff401 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ234 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b21 = at 7 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 8 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 9 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 10 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 4 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 5 2 (CZ24 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1369 c4)) ▸
       at 7 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 5 4 (CZ24 ∷ CCZ024 ∷ []) (wp1371 c4) ▸ done

  b22 : Chain (Bx4-1023 ∷ X0 ∷ CCZ234 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Sb4-2-03-1 ∷ CS13 ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b22 = at 2 5 (CX23 ∷ Toff302 ∷ CCZ234 ∷ []) (wp1372 c4) ▸
       at 4 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 4 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 1 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸
       at 4 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸ done

  b23 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Sb4-2-03-1 ∷ CS13 ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ CCZ024 ∷ CS13 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b23 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 5 (CS13 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1542 (lit c4))) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 6 2 (CS13 ∷ Toff413 ∷ []) (sym (wl1502 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 4 2 (CS13 ∷ Toff413 ∷ []) (sym (wl1502 (lit c4))) ▸ done

  b24 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ CCZ024 ∷ CS13 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ [])
  b24 = at 3 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 4 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸ done

  b25 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX23 ∷ K3 ∷ Toff401 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b25 = at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 6 (CX23 ∷ Toff302 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1541 (lit c4))) ▸
       at 4 1 (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4) ▸
       at 4 1 (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4) ▸
       at 7 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 9 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 8 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸ done

  b26 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ CX23 ∷ K3 ∷ Toff401 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ234 ∷ Toff401 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b26 = at 9 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 10 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 11 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 12 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 13 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸
       at 14 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 8 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 6 3 (CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1368 c4) ▸ done

  b27 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ234 ∷ Toff401 ∷ CX23 ∷ Toff302 ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ234 ∷ CX23 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b27 = at 5 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 6 2 (K3 ∷ Toff401 ∷ []) (sym (wp1345 c4)) ▸
       at 7 2 (CS03 ∷ Toff401 ∷ []) (sym (wp1328 c4)) ▸
       at 8 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 9 2 (CS03⁻ ∷ Toff401 ∷ []) (sym (wp1344 c4)) ▸
       at 10 2 (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4)) ▸
       at 11 2 (CS02 ∷ Toff401 ∷ []) (sym (wp1343 c4)) ▸ done

  b28 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ234 ∷ CX23 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CZ24 ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ Toff302 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b28 = at 12 2 (K3⁻ ∷ Toff401 ∷ []) (sym (wp1342 c4)) ▸
       at 6 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 7 2 (CZ24 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1369 c4)) ▸
       at 9 2 (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (sym (wp1370 c4)) ▸
       at 7 4 (CZ24 ∷ CCZ024 ∷ []) (wp1371 c4) ▸
       at 4 5 (CX23 ∷ Toff302 ∷ CCZ234 ∷ []) (wp1372 c4) ▸
       at 6 4 (Bx4-2301 ∷ []) (sym (lem-box-cP-at0412233041 c4)) ▸
       at 6 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1324-at04122041 c4)) ▸ done

  b29 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ Toff302 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ X0 ∷ [])
  b29 = at 8 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 3 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸
       at 5 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b30 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ X0 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b30 = at 6 5 (CS13⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1543 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff413 ∷ []) (sym (wl1500 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ Toff413 ∷ []) (sym (wl1500 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 6 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 8 1 (Sb4-2-1-3 ∷ []) (refl) ▸ done

  b31 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b31 = at 10 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸ done

-- F4-K3-CS2 @0440: 19 steps
lem-F4-K3-CS2-at0440 : Ws → ⟪ (X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (CCZ124 ∷ X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (Bx4-2103 ∷ []) (lem-box-perm-1423-at04122041 c4) ▸
       at 3 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0412213043 c4) ▸
       at 2 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 1 2 (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4)) ▸
       at 0 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸ done

  b1 : Chain (CCZ124 ∷ X0 ∷ CK03 ∷ X0 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b1 = at 1 4 (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wp1384 c4)) ▸
       at 4 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 3 2 (CCZ124 ∷ CK03 ∷ []) (lem-comm-CK03-CCZ124 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ ↑ • CCZ • Swap ↑ ↑)) ▸
       at 3 4 (Toff403 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wp1384 c4)) ▸
       at 0 4 (Bx4-2103 ∷ []) (sym (lem-box-cP-at0412213043 c4)) ▸
       at 0 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1423-at04122041 c4)) ▸
       at 1 7 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (sym (wl1572 (lit c4))) ▸ done

  b2 : Chain (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ CK03 ∷ X0 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ X0 ∷ [])
  b2 = at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸ done

-- F4-CS2-K3 @0440: 21 steps
lem-F4-CS2-K3-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK03 ∷ []) (X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K3 ∷ CK03 ∷ S0 ∷ X0 ∷ []) (sym (wl1574 (lit c4))) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K3 ∷ CK03 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1575 (lit c4))) ▸
       at 1 1 (Bx4-2103 ∷ []) (lem-box-perm-1423-at04122041 c4) ▸
       at 1 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at0412213043 c4) ▸
       at 4 4 (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (sym (wp1393 c4)) ▸ done

  b1 : Chain (X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx4-2103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b1 = at 3 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 4 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 5 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 2 4 (K3 ∷ CK03 ∷ S0 ∷ Toff403 ∷ []) (sym (wp1393 c4)) ▸
       at 1 2 (K3 ∷ CCZ124 ∷ []) (wl1576 (lit c4)) ▸
       at 2 2 (CK03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CK03 (lit c4)) ▸
       at 3 2 (S0 ∷ CCZ124 ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • CCZ • Swap ↑ ↑))) ▸
       at 4 4 (Bx4-2103 ∷ []) (sym (lem-box-cP-at0412213043 c4)) ▸ done

  b2 : Chain (X0 ∷ K3 ∷ CK03 ∷ S0 ∷ Bx4-2103 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (CK03 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b2 = at 4 1 (Bx4-2031 ∷ []) (sym (lem-box-perm-1423-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 0 4 (CK03 ∷ X0 ∷ []) (sym (wl1577 (lit c4))) ▸ done

-- box-box-2 @0440: 105 steps
lem-box-box-2-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4130 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-box-box-2-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx4-1230 ∷ Bx2-4130 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ CS03 ∷ CX43 ∷ CS03⁻ ∷ CCZ124 ∷ CX43 ∷ CS04 ∷ Toff203 ∷ [])
  b0 = at 0 1 (Bx4-1302 ∷ []) (lem-box-perm-1342-at0440 c4) ▸
       at 0 1 (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ []) (lem-box-tQ-at04233042 c4) ▸
       at 4 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4) ▸
       at 3 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 4 2 (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1197 c4) ▸
       at 6 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp0198 c4) ▸
       at 10 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 9 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸ done

  b1 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ CS03 ∷ CX43 ∷ CS03⁻ ∷ CCZ124 ∷ CX43 ∷ CS04 ∷ Toff203 ∷ []) (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ [])
  b1 = at 8 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 7 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 7 5 (CCZ034 ∷ []) (sym (wp0198 c4)) ▸
       at 5 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 6 3 (Toff203 ∷ CCZ024 ∷ []) (wp1411 c4) ▸
       at 3 4 (Bx2-4130 ∷ []) (sym (lem-box-cP-at02142140 c4)) ▸
       at 3 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4) ▸ done

  b2 : Chain (Toff413 ∷ CCZ024 ∷ Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ Toff203 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ [])
  b2 = at 2 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 4 2 (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1150 (lit c4)) ▸
       at 3 1 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (sym (wl1605 (lit c4))) ▸
       at 9 2 (Toff203 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 8 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 7 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CS13⁻ ∷ []) (wl1606 (lit c4)) ▸
       at 5 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸ done

  b3 : Chain (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ Toff203 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ Toff203 ∷ Toff413 ∷ CCZ123 ∷ CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff203 ∷ CCZ024 ∷ [])
  b3 = at 4 2 (Toff203 ∷ CS13 ∷ []) (wl1607 (lit c4)) ▸
       at 3 2 (Toff203 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 4 7 (Toff413 ∷ []) (wl1605 (lit c4)) ▸
       at 6 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 10 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 9 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸ done

  b4 : Chain (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ Toff203 ∷ Toff413 ∷ CCZ123 ∷ CS03 ∷ CCZ124 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff203 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ Toff203 ∷ K4⁻ ∷ CCZ013 ∷ CCZ024 ∷ [])
  b4 = at 6 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 5 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 4 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 5 3 (Toff413 ∷ []) (wl1608 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CCZ013 ∷ []) (wl1131 (lit c4)) ▸
       at 5 1 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (sym (wl1605 (lit c4))) ▸
       at 11 2 (Toff203 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸ done

  b5 : Chain (Toff413 ∷ CCZ024 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ Toff203 ∷ K4⁻ ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ024 ∷ Bx2-4130 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b5 = at 10 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 9 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 8 2 (Toff203 ∷ CS13⁻ ∷ []) (wl1606 (lit c4)) ▸
       at 7 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 6 2 (Toff203 ∷ CS13 ∷ []) (wl1607 (lit c4)) ▸
       at 5 2 (Toff203 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 6 7 (Toff413 ∷ []) (wl1605 (lit c4)) ▸
       at 2 4 (Bx2-4130 ∷ []) (sym (lem-box-cP-at02142140 c4)) ▸ done

  b6 : Chain (Toff413 ∷ CCZ024 ∷ Bx2-4130 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ CS03 ∷ CCZ124 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ Toff203 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b6 = at 2 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 2 2 (Toff203 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1197 c4) ▸
       at 4 1 (CS03 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ []) (wp0198 c4) ▸
       at 8 2 (CCZ124 ∷ CS04 ∷ []) (sym (wp0384 c4)) ▸
       at 7 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸ done

  b7 : Chain (Toff413 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ CS03 ∷ CCZ124 ∷ CX43 ∷ CS03⁻ ∷ CX43 ∷ CS04 ∷ Toff203 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff413 ∷ Toff203 ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b7 = at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0198 c4)) ▸
       at 3 2 (CCZ124 ∷ CCZ024 ∷ []) (wp0827 c4) ▸
       at 4 3 (Toff203 ∷ CCZ024 ∷ []) (wp1411 c4) ▸
       at 1 4 (Bx2-4130 ∷ []) (sym (lem-box-cP-at02142140 c4)) ▸
       at 1 1 (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at02142140 c4) ▸
       at 0 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 2 2 (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1150 (lit c4)) ▸ done

  b8 : Chain (CCZ124 ∷ Toff413 ∷ Toff203 ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff203 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b8 = at 1 1 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (sym (wl1605 (lit c4))) ▸
       at 7 2 (Toff203 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 6 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 5 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CS13⁻ ∷ []) (wl1606 (lit c4)) ▸
       at 3 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CS13 ∷ []) (wl1607 (lit c4)) ▸
       at 1 2 (Toff203 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))) ▸ done

  b9 : Chain (CCZ124 ∷ Toff203 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ123 ∷ CCZ013 ∷ CCZ124 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff203 ∷ Toff413 ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b9 = at 2 7 (Toff413 ∷ []) (wl1605 (lit c4)) ▸
       at 4 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 8 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸ done

  b10 : Chain (CCZ124 ∷ Toff203 ∷ Toff413 ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff203 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ Toff203 ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b10 = at 3 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 2 2 (CCZ124 ∷ Toff413 ∷ CCZ123 ∷ []) (sym (wl1598 (lit c4))) ▸
       at 3 3 (Toff413 ∷ []) (wl1608 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CCZ013 ∷ []) (wl1131 (lit c4)) ▸
       at 3 1 (K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ []) (sym (wl1605 (lit c4))) ▸
       at 9 2 (Toff203 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 8 2 (Toff203 ∷ CS34 ∷ []) (wp1199 c4) ▸
       at 7 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸ done

  b11 : Chain (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ K4 ∷ CS13 ∷ CX41 ∷ CS13⁻ ∷ Toff203 ∷ CX41 ∷ CS34 ∷ K4⁻ ∷ CCZ013 ∷ CCZ024 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (Bx2-4130 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ [])
  b11 = at 6 2 (Toff203 ∷ CS13⁻ ∷ []) (wl1606 (lit c4)) ▸
       at 5 2 (Toff203 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF203 (lit c4)) ▸
       at 4 2 (Toff203 ∷ CS13 ∷ []) (wl1607 (lit c4)) ▸
       at 3 2 (Toff203 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 4 7 (Toff413 ∷ []) (wl1605 (lit c4)) ▸
       at 0 4 (Bx2-4130 ∷ []) (sym (lem-box-cP-at02142140 c4)) ▸
       at 2 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸ done

  b12 : Chain (Bx2-4130 ∷ Toff413 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CCZ024 ∷ CS01 ∷ Toff413 ∷ CCZ013 ∷ CCZ024 ∷ []) (Bx2-4130 ∷ Bx4-1302 ∷ [])
  b12 = at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 3 2 (Toff413 ∷ CCZ013 ∷ []) (wp1412 c4) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸
       at 1 4 (Bx4-1302 ∷ []) (sym (lem-box-tQ-at04233042 c4)) ▸ done

  b13 : Chain (Bx2-4130 ∷ Bx4-1302 ∷ []) (Bx2-4130 ∷ Bx4-1230 ∷ [])
  b13 = at 1 1 (Bx4-1230 ∷ []) (lem-box-perm-1423-at04233042 c4) ▸ done

-- XCKX-box-2 @0214203143: 4 steps
lem-XCKX-box-2-at0214203143 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-XCKX-box-2-at0214203143 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 3 (K2 ∷ CK02⁻ ∷ []) (sym (wl1633 (lit c4))) ▸
       at 1 2 (Bx2-4013 ∷ CK02⁻ ∷ []) (lem-CKdu-box-2-at0214203143 c4) ▸
       at 0 2 (Bx2-4013 ∷ K2 ∷ []) (lem-Ku-box-at0214203143 c4) ▸
       at 1 2 (X0 ∷ CK02 ∷ X0 ∷ []) (wl1633 (lit c4)) ▸ done

-- CXuA-S @0410213243: 44 steps
lem-CXuA-S-at0410213243 : Ws → ⟪ (CX23 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ CX23 ∷ []) ⟫ʷ
lem-CXuA-S-at0410213243 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (run b5)))))
  where
  b0 : Chain (CX23 ∷ Sb2-4-01-3 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Bx3-0142 ∷ CS34⁻ ∷ CX23 ∷ [])
  b0 = at 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 3 1 (CS34 ∷ []) (refl) ▸
       at 5 1 (CS34⁻ ∷ []) (refl) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-box-perm-2314-at0214203143 c4) ▸
       at 2 0 (CX23 ∷ CX23 ∷ []) (sym (wl0806 (lit c4))) ▸
       at 0 3 (Bx2-0143 ∷ Bx3-0142 ∷ []) (lem-F0-B-at0410213243 c4) ▸
       at 2 5 (Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ Bx3-0142 ∷ CX23 ∷ []) (lem-F0-R-at0410213243 c4) ▸
       at 5 2 (Bx3-0142 ∷ CS34⁻ ∷ []) (lem-CSdu-box-3-at0310213442 c4) ▸ done

  b1 : Chain (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ Bx3-0142 ∷ CS34⁻ ∷ CX23 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ CS34 ∷ CCZ034 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CS34⁻ ∷ CX23 ∷ [])
  b1 = at 5 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (sym (wp0388 c4)) ▸
       at 6 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 10 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸ done

  b2 : Chain (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ CS34 ∷ CCZ034 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CS34⁻ ∷ CX23 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ Bx3-0142 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ [])
  b2 = at 6 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 5 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 6 3 (CCZ034 ∷ Toff301 ∷ []) (sym (wp1435 c4)) ▸
       at 7 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 4 1 (Bx3-0142 ∷ []) (sym (lem-box-perm-1324-at0310213442 c4)) ▸
       at 3 2 (Bx3-0142 ∷ CS34 ∷ []) (lem-CSu-box-3-at0310213442 c4) ▸ done

  b3 : Chain (Bx2-0143 ∷ Bx3-0142 ∷ Toff301 ∷ Bx3-0142 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ []) (Bx2-0143 ∷ Bx3-0142 ∷ CCZ034 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ [])
  b3 = at 3 1 (Bx3-0412 ∷ []) (lem-box-perm-1324-at0310213442 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 2 2 (CCZ034 ∷ Toff301 ∷ CCZ014 ∷ []) (sym (wp0388 c4)) ▸
       at 4 1 (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp1143 c4) ▸
       at 8 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS01⁻ ∷ []) (wl0500 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸ done

  b4 : Chain (Bx2-0143 ∷ Bx3-0142 ∷ CCZ034 ∷ Toff301 ∷ CS01 ∷ Toff312 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ CCZ034 ∷ Toff312 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ []) (Bx2-0143 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ [])
  b4 = at 4 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp1143 c4)) ▸
       at 3 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 4 3 (CCZ034 ∷ Toff301 ∷ []) (sym (wp1435 c4)) ▸
       at 5 2 (Toff312 ∷ Toff301 ∷ []) (wl0525 (lit c4)) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 2 1 (Bx3-0142 ∷ []) (sym (lem-box-perm-1324-at0310213442 c4)) ▸
       at 1 2 [] (lem-box2-at0310213442 c4) ▸ done

  b5 : Chain (Bx2-0143 ∷ Toff301 ∷ CS34 ∷ Toff301 ∷ CS34⁻ ∷ CX23 ∷ []) (Sb2-4-01-3 ∷ CX23 ∷ [])
  b5 = at 0 1 (Bx2-4013 ∷ []) (lem-box-perm-3124-at0210213443 c4) ▸
       at 2 1 (Sb2-4-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-4-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-4-01-3 ∷ []) (refl) ▸ done

-- box-box-3 @0440: 105 steps
lem-box-box-3-at0440 : Ws → ⟪ (Bx4-1230 ∷ Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ Bx4-1230 ∷ []) ⟫ʷ
lem-box-box-3-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx4-1230 ∷ Bx3-4120 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CCZ134 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ [])
  b0 = at 0 1 (Bx4-1203 ∷ []) (lem-box-perm-1243-at0440 c4) ▸
       at 0 1 (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ034 ∷ []) (lem-box-tQ-at043043 c4) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 3 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 4 2 (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4) ▸
       at 6 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 5 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 9 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸ done

  b1 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CCZ134 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ []) (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 7 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 6 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 6 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 6 3 (Toff302 ∷ CCZ034 ∷ []) (wp1134 c4) ▸
       at 3 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 3 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸ done

  b2 : Chain (Toff412 ∷ CCZ034 ∷ Toff412 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ Toff302 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ [])
  b2 = at 2 2 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl1673 (lit c4))) ▸
       at 4 2 (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1241 (lit c4)) ▸
       at 3 1 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (sym (wl1674 (lit c4))) ▸
       at 9 2 (Toff302 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 8 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 5 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸ done

  b3 : Chain (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ Toff302 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ Toff412 ∷ CCZ123 ∷ CS02 ∷ CCZ134 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ034 ∷ [])
  b3 = at 4 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 3 2 (Toff302 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 4 7 (Toff412 ∷ []) (wl1674 (lit c4)) ▸
       at 6 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 10 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 9 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 8 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 7 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸ done

  b4 : Chain (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ Toff412 ∷ CCZ123 ∷ CS02 ∷ CCZ134 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ Toff302 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ K4⁻ ∷ CCZ012 ∷ CCZ034 ∷ [])
  b4 = at 6 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 4 2 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl1673 (lit c4))) ▸
       at 5 3 (Toff412 ∷ []) (wl1676 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 5 1 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (sym (wl1674 (lit c4))) ▸
       at 11 2 (Toff302 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸ done

  b5 : Chain (Toff412 ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ K4⁻ ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ034 ∷ Bx3-4120 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b5 = at 10 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 9 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 8 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 5 2 (Toff302 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 6 7 (Toff412 ∷ []) (wl1674 (lit c4)) ▸
       at 2 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸ done

  b6 : Chain (Toff412 ∷ CCZ034 ∷ Bx3-4120 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (Toff412 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ CX42 ∷ CCZ134 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b6 = at 2 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 1 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 2 2 (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4) ▸
       at 4 2 (CCZ134 ∷ CCZ034 ∷ []) (wp0103 c4) ▸
       at 3 1 (CS02 ∷ CX42 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ []) (wp0213 c4) ▸
       at 7 2 (CCZ134 ∷ CS04 ∷ []) (sym (wp1003 c4)) ▸
       at 6 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 5 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸ done

  b7 : Chain (Toff412 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ CX42 ∷ CCZ134 ∷ CS02⁻ ∷ CX42 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff412 ∷ Toff302 ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b7 = at 4 2 (CCZ134 ∷ CX42 ∷ []) (sym (wl0318 (lit c4))) ▸
       at 3 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 4 5 (CCZ024 ∷ []) (sym (wp0213 c4)) ▸
       at 4 3 (Toff302 ∷ CCZ034 ∷ []) (wp1134 c4) ▸
       at 1 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 1 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4) ▸
       at 0 2 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl1673 (lit c4))) ▸
       at 2 2 (Toff302 ∷ CCZ123 ∷ CCZ012 ∷ []) (wl1241 (lit c4)) ▸ done

  b8 : Chain (CCZ134 ∷ Toff412 ∷ Toff302 ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff302 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b8 = at 1 1 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (sym (wl1674 (lit c4))) ▸
       at 7 2 (Toff302 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 6 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 5 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 3 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 2 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 1 2 (Toff302 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))) ▸ done

  b9 : Chain (CCZ134 ∷ Toff302 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ123 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff302 ∷ Toff412 ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b9 = at 2 7 (Toff412 ∷ []) (wl1674 (lit c4)) ▸
       at 4 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 8 2 (CCZ134 ∷ CS01 ∷ []) (sym (wp0261 c4)) ▸
       at 7 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 6 2 (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4)) ▸
       at 5 2 (CCZ134 ∷ CX12 ∷ []) (sym (wl0679 (lit c4))) ▸
       at 4 2 (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸ done

  b10 : Chain (CCZ134 ∷ Toff302 ∷ Toff412 ∷ CCZ123 ∷ CCZ134 ∷ CCZ012 ∷ Toff302 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ Toff302 ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ012 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b10 = at 3 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 2 2 (CCZ134 ∷ Toff412 ∷ CCZ123 ∷ []) (sym (wl1673 (lit c4))) ▸
       at 3 3 (Toff412 ∷ []) (wl1676 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4)) ▸
       at 3 1 (K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ []) (sym (wl1674 (lit c4))) ▸
       at 9 2 (Toff302 ∷ K4⁻ ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K • iI))) ▸
       at 8 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 7 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸ done

  b11 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K4 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ Toff302 ∷ CX41 ∷ CS24 ∷ K4⁻ ∷ CCZ012 ∷ CCZ034 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx3-4120 ∷ Toff412 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CCZ034 ∷ CS01 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ [])
  b11 = at 6 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 5 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 3 2 (Toff302 ∷ K4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (K))) ▸
       at 4 7 (Toff412 ∷ []) (wl1674 (lit c4)) ▸
       at 0 4 (Bx3-4120 ∷ []) (sym (lem-box-cP-at0314213240 c4)) ▸
       at 2 1 (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS01 ∷ []) (sym (wp0001 c4)) ▸ done

  b12 : Chain (Bx3-4120 ∷ Toff412 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CCZ034 ∷ CS01 ∷ Toff412 ∷ CCZ012 ∷ CCZ034 ∷ []) (Bx3-4120 ∷ Bx4-1203 ∷ [])
  b12 = at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS02⁻ ∷ []) (sym (wp0002 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 3 5 (CCZ012 ∷ []) (sym (wl0155 (lit c4))) ▸
       at 3 2 (Toff412 ∷ CCZ012 ∷ []) (wp0374 c4) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸
       at 1 4 (Bx4-1203 ∷ []) (sym (lem-box-tQ-at043043 c4)) ▸ done

  b13 : Chain (Bx3-4120 ∷ Bx4-1203 ∷ []) (Bx3-4120 ∷ Bx4-1230 ∷ [])
  b13 = at 1 1 (Bx4-1230 ∷ []) (lem-box-perm-1243-at043043 c4) ▸ done

-- L-CX01-2 @0440: 2 steps
lem-L-CX01-2-at0440 : Ws → ⟪ (CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ []) ⟫ʷ
lem-L-CX01-2-at0440 c4 = run b0
  where
  b0 : Chain (CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) (Toff302 ∷ [])
  b0 = at 1 2 (CCZ023 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4) ▸
       at 0 4 (Toff302 ∷ []) (wl1706 (lit c4)) ▸ done

-- L-CX10-2 @0440: 2 steps
lem-L-CX10-2-at0440 : Ws → ⟪ (CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ []) ⟫ʷ
lem-L-CX10-2-at0440 c4 = run b0
  where
  b0 : Chain (CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ []) (Toff203 ∷ [])
  b0 = at 1 2 (CCZ023 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩-at0440 c4) ▸
       at 0 4 (Toff203 ∷ []) (wl1707 (lit c4)) ▸ done
