{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D134 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0181 ; wl0204 ; wl0207 ; wl0242 ; wl0307 ; wl0341 ; wl0460 ; wl0461 ; wl0463 ; wl0929 ; wl1431 ; wl1440 ; wl1446 ; wl1448 ; wl1487 ; wl1490 ; wl1499 ; wl1500 ; wl1501 ; wl1502 ; wl1508 ; wl1509 ; wl1516 ; wl1517 ; wl1518 ; wl1519 ; wl1520 ; wl1521 ; wl1522 ; wl1523 ; wl1524 ; wl1525 ; wl1526 ; wl1527 ; wl1528 ; wl1529 ; wl1530 ; wl1531 ; wl1532 ; wl1533 ; wl1534 ; wl1535 ; wl1536 ; wl1537 ; wl1538 ; wl1539 ; wl1540 ; wl1541 ; wl1542 ; wl1543 ; wp0053 ; wp0054 ; wp0060 ; wp0061 ; wp0065 ; wp0067 ; wp0081 ; wp0091 ; wp0092 ; wp0124 ; wp0155 ; wp0156 ; wp0157 ; wp0265 ; wp0311 ; wp1019 ; wp1023 ; wp1278 ; wp1302 ; wp1318 ; wp1328 ; wp1335 ; wp1342 ; wp1343 ; wp1344 ; wp1345 ; wp1347 ; wp1348 ; wp1351 ; wp1352 ; wp1353 ; wp1354 ; wp1355 ; wp1356 ; wp1357 ; wp1358 ; wp1359 ; wp1360 ; wp1361 ; wp1362 ; wp1363 ; wp1364 ; wp1365 ; wp1366 ; wp1367 ; wp1368 ; wp1369 ; wp1370 ; wp1371 ; wp1372)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.FiveV.D.D133 using (lem-box-cP-at04122041 ; lem-box-cP-at0412233041 ; lem-box-cP-at04233042 ; lem-box-perm-1324-at04122041 ; lem-box-perm-1423-at04203243 ; lem-box-perm-3241-at04203243 ; lem-box-perm-4213-at04122041)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CSd23-CCZ014 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-CK02-CCZ134 ; lem-comm-TOFF401-CX23 ; lem-comm-TOFF413-CK02)
-- F4-CS1-CS1 @0440: 286 steps
lem-F4-CS1-CS1-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS1-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 4 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸
       at 4 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CCZ014 ∷ CS13⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b2 = at 5 3 (X0 ∷ []) (wp1353 c4) ▸
       at 6 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 5 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 5 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b3 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CCZ014 ∷ CS13⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b3 = at 6 2 (Toff423 ∷ CS13⁻ ∷ []) (wl1517 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 8 2 (Toff423 ∷ CS13⁻ ∷ []) (wl1517 (lit c4)) ▸
       at 5 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸ done

  b4 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CCZ014 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 5 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 7 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b5 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b5 = at 13 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 12 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 7 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 8 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b6 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff402 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b6 = at 6 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸
       at 9 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 8 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 12 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 11 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 10 2 (Toff423 ∷ CS02⁻ ∷ []) (wp1355 c4) ▸
       at 9 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸ done

  b7 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff402 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b7 = at 9 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 7 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸
       at 8 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 3 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 4 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸ done

  b8 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ014 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b8 = at 5 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 6 2 (Toff423 ∷ CS13 ∷ []) (wl1509 (lit c4)) ▸
       at 3 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 8 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 7 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b9 : Chain (X0 ∷ Bx4-1023 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CCZ014 ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ014 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b9 = at 5 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 4 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 2 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 3 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 3 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 5 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 11 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸ done

  b10 : Chain (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ Toff402 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ CCZ014 ∷ K3⁻ ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b10 = at 10 2 (CCZ014 ∷ CS02 ∷ []) (sym (wp0155 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS03⁻ ∷ []) (sym (wp0156 c4)) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS03 ∷ []) (sym (wp0157 c4)) ▸
       at 5 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 6 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ Toff402 ∷ CCZ012 ∷ []) (sym (wp1335 c4)) ▸ done

  b11 : Chain (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ Toff423 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CCZ012 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b11 = at 7 2 (Toff423 ∷ Toff402 ∷ Toff302 ∷ []) (wp1354 c4) ▸
       at 6 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 10 2 (Toff423 ∷ CS12 ∷ []) (wl0461 (lit c4)) ▸
       at 9 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 8 2 (Toff423 ∷ CS02⁻ ∷ []) (wp1355 c4) ▸
       at 7 2 (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ)) ▸
       at 6 2 (Toff423 ∷ CS02 ∷ []) (wp0311 c4) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

  b12 : Chain (X0 ∷ Bx4-1023 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff402 ∷ Toff423 ∷ CCZ012 ∷ Toff402 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b12 = at 5 2 (Toff423 ∷ Toff402 ∷ []) (wp1318 c4) ▸
       at 6 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 2 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸
       at 1 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b13 : Chain (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff423 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b13 = at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸ done

  b14 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ X0 ∷ CZ14 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b14 = at 3 3 (X0 ∷ []) (wp1353 c4) ▸
       at 4 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b15 : Chain (Bx4-1023 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b15 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b16 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b16 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 8 (CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ123 ∷ []) (sym (wl1518 (lit c4))) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b17 : Chain (Bx4-1023 ∷ X0 ∷ Bx4-1023 ∷ CCZ012 ∷ Toff302 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b17 = at 3 3 (Toff302 ∷ CS13 ∷ CCZ012 ∷ []) (wl1519 (lit c4)) ▸
       at 5 2 [] (wl0341 (lit c4)) ▸
       at 4 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b18 : Chain (Bx4-1023 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b18 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX23 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1521 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 5 2 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (sym (wl1522 (lit c4))) ▸
       at 7 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 4 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1358 c4) ▸ done

  b19 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ CCZ014 ∷ Toff302 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b19 = at 10 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 10 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸ done

  b20 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff423 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b20 = at 9 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 3 2 (CX24 ∷ Toff423 ∷ []) (sym (wl1523 (lit c4))) ▸
       at 5 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 4 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 5 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 6 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 7 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 8 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸ done

  b21 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff423 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ CX23 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Toff423 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b21 = at 4 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 5 2 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (sym (wl1522 (lit c4))) ▸
       at 7 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 9 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 8 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 9 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 10 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 11 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸ done

  b22 : Chain (Bx4-1023 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ CX23 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ Toff423 ∷ CS12 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b22 = at 12 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 8 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 9 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸
       at 5 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 3 4 (CX23 ∷ Toff302 ∷ []) (wl1524 (lit c4)) ▸
       at 2 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b23 : Chain (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CX23 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 4 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 9 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 3 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b24 : Chain (Bx4-1023 ∷ X0 ∷ CX23 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS13 ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b24 = at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸
       at 4 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS13 ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b25 = at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS13 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1527 (lit c4))) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 6 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 2 (CS13 ∷ Toff423 ∷ []) (sym (wl1509 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done

  b26 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ [])
  b26 = at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b27 = at 5 6 (CX23 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1521 (lit c4))) ▸
       at 4 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 7 2 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (sym (wl1522 (lit c4))) ▸
       at 9 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 6 2 (CX24 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1023 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (Toff402 ∷ CCZ012 ∷ CCZ014 ∷ []) (wp1358 c4) ▸
       at 12 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸ done

  b28 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ CCZ014 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 12 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 16 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 11 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸ done

  b29 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CX24 ∷ CCZ012 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ Toff423 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b29 = at 5 2 (CX24 ∷ Toff423 ∷ []) (sym (wl1523 (lit c4))) ▸
       at 7 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 6 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 7 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 8 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 9 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 10 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done

  b30 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ Toff423 ∷ CX23 ∷ Toff402 ∷ CCZ012 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ CX23 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff423 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b30 = at 7 2 (CX24 ∷ CX23 ∷ Toff423 ∷ []) (sym (wl1522 (lit c4))) ▸
       at 9 2 (Toff402 ∷ Toff423 ∷ []) (sym (wp1318 c4)) ▸
       at 11 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 10 2 (CS02 ∷ Toff423 ∷ []) (sym (wp0311 c4)) ▸
       at 11 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 12 2 (CS02⁻ ∷ Toff423 ∷ []) (sym (wp1355 c4)) ▸
       at 13 2 (CX10 ∷ Toff423 ∷ []) (sym (c₂ (CX₁₀) (Toffᵗ))) ▸
       at 14 2 (CS12 ∷ Toff423 ∷ []) (sym (wl0461 (lit c4))) ▸ done

  b31 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CCZ014 ∷ CX24 ∷ CCZ012 ∷ CX24 ∷ CX23 ∷ Toff402 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ Toff423 ∷ Toff302 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b31 = at 10 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸
       at 11 2 (Toff402 ∷ Toff302 ∷ Toff423 ∷ []) (sym (wp1357 c4)) ▸
       at 5 3 (CCZ012 ∷ []) (sym (wp1019 c4)) ▸
       at 7 3 (CCZ012 ∷ []) (sym (wp1356 c4)) ▸
       at 5 4 (CX23 ∷ Toff302 ∷ []) (wl1524 (lit c4)) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 1 (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (sym (wl1501 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b32 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ K3 ∷ CCZ014 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ Toff302 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b32 = at 6 2 (CS03 ∷ CCZ014 ∷ []) (wp0157 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ014 ∷ []) (wp0156 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS02 ∷ CCZ014 ∷ []) (wp0155 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff302 ∷ []) (wl1501 (lit c4)) ▸
       at 6 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸ done

  b33 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ Toff302 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13⁻ ∷ X0 ∷ [])
  b33 = at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸
       at 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CS13⁻ ∷ X0 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ [])
  b34 = at 6 5 (CS13⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1529 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff423 ∷ []) (sym (wl1517 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 2 (CS13⁻ ∷ Toff423 ∷ []) (sym (wl1517 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸ done

  b35 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b35 = at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸ done


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


-- F4-K2-K2 @0440: 1 steps
lem-F4-K2-K2-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ CK02 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (sym (wl1531 (lit c4))) ▸ done


-- F4-I-K2 @0440: 1 steps
lem-F4-I-K2-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K2-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CK02 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1532 (lit c4))) ▸ done


-- F4-I-CS1 @0440: 15 steps
lem-F4-I-CS1-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS1-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 4 (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1360 c4)) ▸
       at 1 4 (Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1533 (lit c4))) ▸
       at 2 4 (CCZ014 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1360 c4)) ▸
       at 3 4 (Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1533 (lit c4))) ▸ done

  b1 : Chain (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ S0 ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b1 = at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 7 (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1534 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S0⁻ ∷ []) (wl1431 (lit c4)) ▸
       at 1 2 (X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1431 (lit c4))) ▸ done


-- F4-I-CS2 @0440: 15 steps
lem-F4-I-CS2-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS2-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 0 4 (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1278 c4)) ▸
       at 1 4 (Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1361 c4)) ▸
       at 2 4 (CCZ024 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1278 c4)) ▸
       at 3 4 (Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wp1361 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ X0 ∷ S0 ∷ X0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b1 = at 0 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 1 7 (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1535 (lit c4))) ▸
       at 2 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 1 3 (ι ∷ S0⁻ ∷ []) (wl1431 (lit c4)) ▸
       at 1 2 (X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1431 (lit c4))) ▸ done


-- F4-I-K1 @0440: 1 steps
lem-F4-I-K1-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-K1-at0440 c4 = run b0
  where
  b0 : Chain (X0 ∷ S0 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  b0 = at 0 4 (CK01 ∷ X0 ∷ S0 ∷ X0 ∷ []) (sym (wl1440 (lit c4))) ▸ done


-- F4-CS2-I @0440: 15 steps
lem-F4-CS2-I-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-I-at0440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ []) (X0 ∷ CCZ024 ∷ Toff413 ∷ ι ∷ S0⁻ ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (ι ∷ S0⁻ ∷ X0 ∷ []) (wl1446 (lit c4)) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 6 (ι ∷ S0⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (wl1536 (lit c4)) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 4 3 (ι ∷ S0⁻ ∷ Toff413 ∷ []) (wp1362 c4) ▸
       at 3 3 (ι ∷ S0⁻ ∷ CCZ024 ∷ []) (wp1302 c4) ▸ done

  b1 : Chain (X0 ∷ CCZ024 ∷ Toff413 ∷ ι ∷ S0⁻ ∷ CCZ024 ∷ Toff413 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (S0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b1 = at 2 3 (ι ∷ S0⁻ ∷ Toff413 ∷ []) (wp1362 c4) ▸
       at 1 3 (ι ∷ S0⁻ ∷ CCZ024 ∷ []) (wp1302 c4) ▸
       at 3 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 5 1 (Sb4-2-1-3 ∷ []) (refl) ▸
       at 7 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 3 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 0 3 (S0 ∷ X0 ∷ []) (sym (wl1448 (lit c4))) ▸ done


-- F4-CS2-K2 @0440: 19 steps
lem-F4-CS2-K2-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-K2-at0440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK02 ∷ []) (X0 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CK02 ∷ Toff413 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b0 = at 2 2 (K2 ∷ CK02 ∷ S0 ∷ X0 ∷ []) (sym (wl1487 (lit c4))) ▸
       at 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 2 7 (K2 ∷ CK02 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (sym (wl1537 (lit c4))) ▸
       at 1 1 (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4) ▸
       at 4 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 5 2 (CK02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CK02 (lit c4)) ▸ done

  b1 : Chain (X0 ∷ CCZ024 ∷ Toff413 ∷ CCZ024 ∷ K2 ∷ CK02 ∷ Toff413 ∷ S0 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ [])
  b1 = at 6 2 (S0 ∷ Toff413 ∷ []) (sym (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑))) ▸
       at 3 4 (K2 ∷ CK02 ∷ S0 ∷ CCZ024 ∷ []) (wp1363 c4) ▸
       at 2 2 (K2 ∷ Toff413 ∷ []) (sym (wl1538 (lit c4))) ▸
       at 3 2 (CK02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CK02 (lit c4)) ▸
       at 4 2 (S0 ∷ Toff413 ∷ []) (sym (c₁ (S) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑))) ▸
       at 1 4 (K2 ∷ CK02 ∷ S0 ∷ CCZ024 ∷ []) (wp1363 c4) ▸
       at 4 4 (Bx4-2031 ∷ []) (sym (lem-box-cP-at04122041 c4)) ▸
       at 6 1 (Sb4-2-1-3 ∷ []) (refl) ▸ done

  b2 : Chain (X0 ∷ K2 ∷ CK02 ∷ S0 ∷ Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ CS12⁻ ∷ X0 ∷ []) (CK02 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  b2 = at 8 1 (Sb⁻4-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb4-2-03-1 ∷ []) (refl) ▸
       at 0 4 (CK02 ∷ X0 ∷ []) (sym (wl1490 (lit c4))) ▸ done


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

