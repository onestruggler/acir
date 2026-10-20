{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D203 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1463 ; wl1464 ; wl0207 ; wl0228 ; wl0263 ; wl0334 ; wl0861 ; wl0871 ; wl0879 ; wl1151 ; wl1152 ; wl1190 ; wl1226 ; wl1358 ; wl1675 ; wl1689 ; wl1690 ; wl1691 ; wl1692 ; wl1693 ; wl1694 ; wl1695 ; wl1696 ; wl1697 ; wl1698 ; wl1699 ; wl1700 ; wl1701 ; wp0053 ; wp0054 ; wp0066 ; wp0108 ; wp0357 ; wp0496 ; wp1005 ; wp1006 ; wp1202 ; wp1438 ; wp1442 ; wp1443 ; wp1444 ; wp1445 ; wp1446 ; wp1447 ; wp1448 ; wp1449 ; wp1450 ; wp1451 ; wp1452 ; wp1453 ; wp1454 ; wl1713 ; wl1714 ; wl0172 ; wl0173 ; wl0181 ; wl0230 ; wl0280 ; wl0289 ; wl0463 ; wl0882 ; wl0889 ; wl1516 ; wl1520 ; wl1525 ; wl1526 ; wl1528 ; wl1720 ; wl1733 ; wl1734 ; wl1735 ; wl1736 ; wl1737 ; wl1738 ; wp0312 ; wp0313 ; wp0314 ; wp0919 ; wp1250 ; wp1351 ; wp1352 ; wp1353 ; wp1465 ; wp1483 ; wp1515 ; wp1516 ; wp1517)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D014 using (lem-box-cP-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0314203142 ; lem-box-cP-at043043)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-CSdu-box-3-at04203243 ; lem-CSu-box-3-at04203243 ; lem-box-perm-1324-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box2)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-CSdu-box-3-at0314203142)
open import Examples.Groups.Clifford+CS.Five.D.D024 using (lem-CSu-box-3-at0314203142 ; lem-CXu-box-4-at0314203142 ; lem-box-perm-1342-at04203243 ; lem-box-perm-4132-at04203243 ; lem-box2-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-box-perm-1342-at0314203142 ; lem-box-perm-1423-at0314213240 ; lem-box-perm-1423-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D036 using (lem-box-perm-2431-at0413213240)
open import Examples.Groups.Clifford+CS.Five.D.D061 using (lem-box-box-3-at0440)
open import Examples.Groups.Clifford+CS.Five.D.D066 using (lem-box-box-1-at0314213240)
open import Examples.Groups.Clifford+CS.Five.D.D147 using (lem-L-CCZ-1)
open import Examples.Groups.Clifford+CS.Five.D.D169 using (lem-F0-at0410213243 ; lem-L-CCZ-1-at0440)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS03-CCZ124 ; lem-comm-CS12-CCZ034 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CX40-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ013-CS24)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CX12-TOFF403 ; lem-comm-CX41-TOFF302 ; lem-comm-TOFF312-CX40 ; lem-comm-TOFF403-CX12)

-- ckt-TT: 5 steps
lem-ckt-TT : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-ckt-TT c4 = run b0
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) []
  b0 = at 1 45 (Bx0-1234 ∷ []) (lem-L-CCZ-1 c4) ▸
       at 5 45 (Bx0-1234 ∷ []) (lem-L-CCZ-1 c4) ▸
       at 2 3 [] (wl1463 (lit c4)) ▸
       at 1 2 [] (lem-box2 c4) ▸
       at 0 3 [] (wl1464 (lit c4)) ▸ done

-- F4-CS1-CS0 @0440: 214 steps
lem-F4-CS1-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS0-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (run b26))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ034 ∷ Toff312 ∷ X0 ∷ CZ34 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b0 = at 3 1 (Sb3-4-01-2 ∷ []) (lem-F0-at0410213243 c4) ▸
       at 3 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 5 1 (CS24 ∷ []) (refl) ▸
       at 7 1 (CS24⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 2 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (sym (wp1442 c4)) ▸
       at 4 2 (Toff312 ∷ CZ34 ∷ CCZ124 ∷ []) (wl1689 (lit c4)) ▸
       at 3 2 (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ)) ▸ done

  b1 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ034 ∷ Toff312 ∷ X0 ∷ CZ34 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Sb4-1-02-3 ∷ CCZ034 ∷ Toff312 ∷ X0 ∷ CCZ034 ∷ CZ34 ∷ CCZ124 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b1 = at 6 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 10 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 9 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 8 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CZ34 ∷ []) (sym (wp1443 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb4-1-02-3 ∷ CCZ034 ∷ Toff312 ∷ X0 ∷ CCZ034 ∷ CZ34 ∷ CCZ124 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Bx3-4012 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b2 = at 4 2 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (sym (wp1442 c4)) ▸
       at 5 3 (X0 ∷ []) (wl1690 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 5 2 (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ)) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 2 (Bx3-4012 ∷ CS13⁻ ∷ []) (lem-CSdu-box-3-at0314203142 c4) ▸ done

  b3 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Bx3-4012 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b3 = at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp1202 c4)) ▸
       at 6 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 10 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸ done

  b4 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b4 = at 7 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 5 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 6 3 (CCZ034 ∷ Toff302 ∷ []) (sym (wp1438 c4)) ▸
       at 7 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 4 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 3 2 (Bx3-4012 ∷ CS13 ∷ []) (lem-CSu-box-3-at0314203142 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸ done

  b5 : Chain (X0 ∷ Bx4-1023 ∷ Toff302 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx4-1023 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b5 = at 2 2 (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp1202 c4)) ▸
       at 4 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 8 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸ done

  b6 : Chain (X0 ∷ Bx4-1023 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Bx4-1230 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b6 = at 3 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 4 3 (CCZ034 ∷ Toff302 ∷ []) (sym (wp1438 c4)) ▸
       at 5 2 (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4)) ▸
       at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 1 1 (Bx4-1230 ∷ []) (lem-box-perm-1342-at04203243 c4) ▸
       at 2 1 (Bx3-4120 ∷ []) (lem-box-perm-1342-at0314203142 c4) ▸
       at 1 2 (Bx3-4120 ∷ Bx4-1230 ∷ []) (lem-box-box-3-at0440 c4) ▸
       at 1 1 (Bx3-4012 ∷ []) (lem-box-perm-1423-at0314213240 c4) ▸ done

  b7 : Chain (X0 ∷ Bx3-4012 ∷ Bx4-1230 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ X0 ∷ CZ34 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ034 ∷ CX41 ∷ CS24 ∷ Toff312 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b7 = at 2 1 (Bx4-1023 ∷ []) (lem-box-perm-1423-at0440 c4) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 0 2 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (sym (wp1442 c4)) ▸
       at 2 2 (Toff312 ∷ CZ34 ∷ CCZ124 ∷ []) (wl1689 (lit c4)) ▸
       at 1 2 (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ)) ▸
       at 4 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 7 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸ done

  b8 : Chain (CCZ034 ∷ Toff312 ∷ X0 ∷ CZ34 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CCZ034 ∷ CX41 ∷ CS24 ∷ Toff312 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X0 ∷ Toff312 ∷ CCZ124 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b8 = at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX41 ∷ []) (sym (wp0357 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ34 ∷ []) (sym (wp1443 c4)) ▸
       at 2 2 (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (sym (wp1442 c4)) ▸
       at 3 3 (X0 ∷ []) (wl1690 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸ done

  b9 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X0 ∷ Toff312 ∷ CCZ124 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ124 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b9 = at 3 2 (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ)) ▸
       at 0 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 2 (Toff423 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl1691 (lit c4)) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b10 : Chain (Bx3-4012 ∷ X0 ∷ CCZ014 ∷ Toff423 ∷ CCZ124 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b10 = at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 5 3 (Toff423 ∷ CCZ124 ∷ []) (wl1692 (lit c4)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸ done

  b11 : Chain (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b11 = at 7 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 6 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 5 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 4 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 3 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 4 2 (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4)) ▸
       at 5 1 (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4)) ▸ done

  b12 : Chain (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b12 = at 9 2 (Toff302 ∷ CS24 ∷ []) (wp1006 c4) ▸
       at 8 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 7 2 (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4)) ▸
       at 6 2 (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4)) ▸
       at 5 2 (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0334 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4)) ▸
       at 7 2 (X0 ∷ CCZ124 ∷ []) (wp1444 c4) ▸ done

  b13 : Chain (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CCZ124 ∷ CCZ124 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX12 ∷ Toff201 ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b13 = at 8 2 [] (wl0263 (lit c4)) ▸
       at 4 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 2 (CX12 ∷ Toff201 ∷ X0 ∷ []) (sym (wl1693 (lit c4))) ▸
       at 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸
       at 6 1 (CS13⁻ ∷ []) (refl) ▸ done

  b14 : Chain (Bx3-4012 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX12 ∷ Toff201 ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ K2 ∷ CS02 ∷ CX12 ∷ Toff403 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b14 = at 3 6 (CX12 ∷ Toff201 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1694 (lit c4))) ▸
       at 2 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 2 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 5 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 7 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 6 2 (K2 ∷ Toff403 ∷ []) (sym (wp1445 c4)) ▸
       at 7 2 (CS02 ∷ Toff403 ∷ []) (sym (wp1446 c4)) ▸
       at 8 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸ done

  b15 : Chain (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ K2 ∷ CS02 ∷ CX12 ∷ Toff403 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b15 = at 9 2 (CS02⁻ ∷ Toff403 ∷ []) (sym (wp1447 c4)) ▸
       at 10 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 11 2 (CS01 ∷ Toff403 ∷ []) (sym (wp1448 c4)) ▸
       at 12 2 (K2⁻ ∷ Toff403 ∷ []) (sym (wp1449 c4)) ▸
       at 6 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 4 3 (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp1450 c4) ▸
       at 3 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 5 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸ done

  b16 : Chain (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ Toff201 ∷ Toff403 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b16 = at 4 2 (K2 ∷ Toff403 ∷ []) (sym (wp1445 c4)) ▸
       at 5 2 (CS02 ∷ Toff403 ∷ []) (sym (wp1446 c4)) ▸
       at 6 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 7 2 (CS02⁻ ∷ Toff403 ∷ []) (sym (wp1447 c4)) ▸
       at 8 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 9 2 (CS01 ∷ Toff403 ∷ []) (sym (wp1448 c4)) ▸
       at 10 2 (K2⁻ ∷ Toff403 ∷ []) (sym (wp1449 c4)) ▸
       at 4 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸ done

  b17 : Chain (Bx3-4012 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ Toff201 ∷ Toff403 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ X0 ∷ CX12 ∷ Toff201 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b17 = at 5 2 (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) (sym (wp1451 c4)) ▸
       at 7 2 (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) (sym (wp1452 c4)) ▸
       at 5 4 (CZ14 ∷ CCZ014 ∷ []) (wp1453 c4) ▸
       at 2 5 (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) (wp1454 c4) ▸
       at 4 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 4 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b18 : Chain (Bx3-4012 ∷ X0 ∷ CX12 ∷ Toff201 ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CS24 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff201 ∷ CS24⁻ ∷ [])
  b18 = at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 1 3 (Toff201 ∷ X0 ∷ []) (sym (wl1696 (lit c4))) ▸
       at 4 2 (CS24 ∷ X0 ∷ []) (sym (wl1697 (lit c4))) ▸
       at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 7 2 (CS24 ∷ CS13⁻ ∷ []) (wl1698 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b19 : Chain (Bx3-4012 ∷ Toff201 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ CS24 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ Toff201 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ Sb4-1-02-3 ∷ CX12 ∷ Toff201 ∷ X0 ∷ CS24⁻ ∷ [])
  b19 = at 5 2 (CS24 ∷ CS13 ∷ []) (wl1699 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 3 2 (CS24 ∷ Bx4-1023 ∷ []) (sym (lem-CSu-box-3-at04203243 c4)) ▸
       at 6 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 2 2 (CS24 ∷ X0 ∷ []) (sym (wl1697 (lit c4))) ▸
       at 5 2 (CX12 ∷ Toff201 ∷ X0 ∷ []) (sym (wl1693 (lit c4))) ▸ done

  b20 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ Sb4-1-02-3 ∷ CX12 ∷ Toff201 ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ [])
  b20 = at 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX12 ∷ Toff201 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (sym (wl1694 (lit c4))) ▸
       at 4 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 4 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 7 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 9 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸ done

  b21 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ Toff201 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ [])
  b21 = at 8 2 (K2 ∷ Toff403 ∷ []) (sym (wp1445 c4)) ▸
       at 9 2 (CS02 ∷ Toff403 ∷ []) (sym (wp1446 c4)) ▸
       at 10 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 11 2 (CS02⁻ ∷ Toff403 ∷ []) (sym (wp1447 c4)) ▸
       at 12 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 13 2 (CS01 ∷ Toff403 ∷ []) (sym (wp1448 c4)) ▸
       at 14 2 (K2⁻ ∷ Toff403 ∷ []) (sym (wp1449 c4)) ▸
       at 8 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸ done

  b22 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ CX12 ∷ Toff201 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff403 ∷ CS01 ∷ K2⁻ ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ [])
  b22 = at 6 3 (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp1450 c4) ▸
       at 5 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 7 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 6 2 (K2 ∷ Toff403 ∷ []) (sym (wp1445 c4)) ▸
       at 7 2 (CS02 ∷ Toff403 ∷ []) (sym (wp1446 c4)) ▸
       at 8 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸
       at 9 2 (CS02⁻ ∷ Toff403 ∷ []) (sym (wp1447 c4)) ▸
       at 10 2 (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4)) ▸ done

  b23 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CCZ124 ∷ CX12 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff403 ∷ CS01 ∷ K2⁻ ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ Toff403 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CX12 ∷ Toff201 ∷ Bx4-1203 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ [])
  b23 = at 11 2 (CS01 ∷ Toff403 ∷ []) (sym (wp1448 c4)) ▸
       at 12 2 (K2⁻ ∷ Toff403 ∷ []) (sym (wp1449 c4)) ▸
       at 6 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 7 2 (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) (sym (wp1451 c4)) ▸
       at 9 2 (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) (sym (wp1452 c4)) ▸
       at 7 4 (CZ14 ∷ CCZ014 ∷ []) (wp1453 c4) ▸
       at 4 5 (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) (wp1454 c4) ▸
       at 6 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸ done

  b24 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ X0 ∷ CX12 ∷ Toff201 ∷ Bx4-1203 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ X0 ∷ CS24⁻ ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS24⁻ ∷ X0 ∷ [])
  b24 = at 6 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 3 3 (Toff201 ∷ X0 ∷ []) (sym (wl1696 (lit c4))) ▸
       at 6 2 (CS24⁻ ∷ X0 ∷ []) (sym (wl1700 (lit c4))) ▸
       at 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ X0 ∷ Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ CS24⁻ ∷ X0 ∷ []) (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ X0 ∷ CS24⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ [])
  b25 = at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 9 2 (CS24⁻ ∷ CS13⁻ ∷ []) (wl0228 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 7 2 (CS24⁻ ∷ CS13 ∷ []) (wl1701 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 5 2 (CS24⁻ ∷ Bx4-1023 ∷ []) (sym (lem-CSdu-box-3-at04203243 c4)) ▸
       at 8 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸ done

  b26 : Chain (Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ X0 ∷ CS24⁻ ∷ Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ X0 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  b26 = at 6 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 4 2 (CS24⁻ ∷ X0 ∷ []) (sym (wl1700 (lit c4))) ▸
       at 2 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-4-01-3 ∷ []) (sym (lem-F0-at0410213243 c4)) ▸ done

-- ckt-TT @0440: 5 steps
lem-ckt-TT-at0440 : Ws → ⟪ (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-ckt-TT-at0440 c4 = run b0
  where
  b0 : Chain (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) []
  b0 = at 1 45 (Bx4-1230 ∷ []) (lem-L-CCZ-1-at0440 c4) ▸
       at 5 45 (Bx4-1230 ∷ []) (lem-L-CCZ-1-at0440 c4) ▸
       at 2 3 [] (wl1713 (lit c4)) ▸
       at 1 2 [] (lem-box2-at0440 c4) ▸
       at 0 3 [] (wl1714 (lit c4)) ▸ done

-- F4-CS0-CS1 @0440: 232 steps
lem-F4-CS0-CS1-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS1-at0440 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (run b28))))))))))))))))))))))))))))
  where
  b0 : Chain (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (X0 ∷ Sb3-4-01-2 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Sb3-4-01-2 ∷ []) (lem-F0-at0410213243 c4) ▸
       at 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 4 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸ done

  b1 : Chain (X0 ∷ Sb3-4-01-2 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Sb3-4-01-2 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ014 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b1 = at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸ done

  b2 : Chain (X0 ∷ Sb3-4-01-2 ∷ CCZ014 ∷ Toff423 ∷ X0 ∷ CCZ014 ∷ CZ14 ∷ CCZ123 ∷ Toff423 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Bx4-1023 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b2 = at 4 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 5 3 (X0 ∷ []) (wp1353 c4) ▸
       at 6 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 5 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 2 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 5 1 (CS24⁻ ∷ []) (refl) ▸
       at 5 2 (Bx4-1023 ∷ CS24⁻ ∷ []) (lem-CSdu-box-3-at04203243 c4) ▸ done

  b3 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Bx4-1023 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff403 ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b3 = at 5 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 5 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 4 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸
       at 6 2 (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp1515 c4) ▸
       at 5 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 11 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 10 2 (Toff403 ∷ CS01 ∷ []) (wp1448 c4) ▸
       at 9 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸ done

  b4 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ Toff403 ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ Toff201 ∷ CCZ014 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ124 ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4) ▸
       at 7 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CS02 ∷ []) (wp1446 c4) ▸
       at 5 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 6 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 8 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 12 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 11 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸ done

  b5 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ Toff201 ∷ CCZ014 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CCZ124 ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff201 ∷ Toff403 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b5 = at 10 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸
       at 9 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 7 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸
       at 7 3 (Toff201 ∷ []) (wp1465 c4) ▸
       at 8 2 (Toff403 ∷ CCZ013 ∷ []) (wp1483 c4) ▸ done

  b6 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff201 ∷ Toff403 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b6 = at 7 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 13 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 12 2 (Toff403 ∷ CS01 ∷ []) (wp1448 c4) ▸
       at 11 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 10 2 (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4) ▸
       at 9 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 8 2 (Toff403 ∷ CS02 ∷ []) (wp1446 c4) ▸
       at 7 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸ done

  b7 : Chain (X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff201 ∷ CCZ014 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b7 = at 8 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 4 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 4 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸
       at 3 1 (CS24 ∷ []) (refl) ▸
       at 3 2 (Bx4-1023 ∷ CS24 ∷ []) (lem-CSu-box-3-at04203243 c4) ▸
       at 3 1 (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4) ▸
       at 3 1 (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4) ▸
       at 2 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸ done

  b8 : Chain (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff201 ∷ CCZ014 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ K2 ∷ Toff403 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp1515 c4) ▸
       at 3 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 9 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 8 2 (Toff403 ∷ CS01 ∷ []) (wp1448 c4) ▸
       at 7 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4) ▸
       at 5 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 4 2 (Toff403 ∷ CS02 ∷ []) (wp1446 c4) ▸ done

  b9 : Chain (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ K2 ∷ Toff403 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ CCZ014 ∷ CCZ013 ∷ CCZ124 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff403 ∷ Toff201 ∷ CCZ014 ∷ CCZ124 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b9 = at 3 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 4 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 6 1 (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4)) ▸
       at 10 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 9 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 8 2 (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4)) ▸
       at 7 2 (CCZ124 ∷ CX13 ∷ []) (sym (wl0280 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4)) ▸ done

  b10 : Chain (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff403 ∷ Toff201 ∷ CCZ014 ∷ CCZ124 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ Toff403 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff403 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b10 = at 7 5 (CCZ013 ∷ []) (sym (wl0289 (lit c4))) ▸
       at 5 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 4 2 (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp1250 c4)) ▸
       at 5 3 (Toff201 ∷ []) (wp1465 c4) ▸
       at 6 2 (Toff403 ∷ CCZ013 ∷ []) (wp1483 c4) ▸
       at 5 1 (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (sym (wl1695 (lit c4))) ▸
       at 11 2 (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4) ▸
       at 10 2 (Toff403 ∷ CS01 ∷ []) (wp1448 c4) ▸ done

  b11 : Chain (X0 ∷ Bx3-4012 ∷ CCZ124 ∷ Toff403 ∷ CCZ124 ∷ K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ Toff403 ∷ CS01 ∷ K2⁻ ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (X0 ∷ Bx3-4012 ∷ Bx4-1023 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b11 = at 9 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 8 2 (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4) ▸
       at 7 2 (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4)) ▸
       at 6 2 (Toff403 ∷ CS02 ∷ []) (wp1446 c4) ▸
       at 5 2 (Toff403 ∷ K2 ∷ []) (wp1445 c4) ▸
       at 6 7 (Toff201 ∷ []) (wl1695 (lit c4)) ▸
       at 2 4 (Bx4-1203 ∷ []) (sym (lem-box-cP-at043043 c4)) ▸
       at 2 1 (Bx4-1023 ∷ []) (sym (lem-box-perm-1324-at04203243 c4)) ▸ done

  b12 : Chain (X0 ∷ Bx3-4012 ∷ Bx4-1023 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ X0 ∷ Toff423 ∷ CZ14 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b12 = at 1 1 (Bx3-4120 ∷ []) (lem-box-perm-1342-at0314203142 c4) ▸
       at 2 1 (Bx4-3120 ∷ []) (lem-box-perm-4132-at04203243 c4) ▸
       at 1 2 (Bx4-3120 ∷ Bx3-4120 ∷ []) (lem-box-box-1-at0314213240 c4) ▸
       at 1 1 (Bx4-1023 ∷ []) (lem-box-perm-2431-at0413213240 c4) ▸
       at 2 1 (Bx3-4012 ∷ []) (lem-box-perm-1423-at0314213240 c4) ▸
       at 1 1 (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4) ▸
       at 0 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 2 2 (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4)) ▸ done

  b13 : Chain (CCZ014 ∷ X0 ∷ Toff423 ∷ CZ14 ∷ CCZ123 ∷ CCZ014 ∷ Toff423 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CCZ014 ∷ CCZ123 ∷ Toff423 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b13 = at 1 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

  b14 : Chain (CCZ014 ∷ Toff423 ∷ X0 ∷ CZ14 ∷ CCZ014 ∷ CCZ123 ∷ Toff423 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b14 = at 3 2 (CCZ014 ∷ CZ14 ∷ []) (sym (wp1352 c4)) ▸
       at 2 2 (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (sym (wp1351 c4)) ▸
       at 3 3 (X0 ∷ []) (wp1353 c4) ▸
       at 4 2 (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4)) ▸
       at 3 2 (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑)) ▸
       at 0 4 (Bx4-1023 ∷ []) (sym (lem-box-cP-at04203243 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b15 : Chain (Bx4-1023 ∷ X0 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ034 ∷ Toff312 ∷ CZ12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b15 = at 6 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4)) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b16 : Chain (Bx4-1023 ∷ X0 ∷ CCZ034 ∷ Toff312 ∷ CZ12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b16 = at 9 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 5 3 (Toff312 ∷ CCZ123 ∷ []) (wl0889 (lit c4)) ▸ done

  b17 : Chain (Bx4-1023 ∷ X0 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ CCZ123 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b17 = at 2 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 3 3 (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1733 (lit c4)) ▸
       at 6 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 5 2 (CS24 ∷ CCZ123 ∷ []) (wl0173 (lit c4)) ▸
       at 6 4 (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1734 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ123 ∷ []) (wl0172 (lit c4)) ▸
       at 9 2 (X0 ∷ CCZ123 ∷ []) (wl1720 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b18 : Chain (Bx4-1023 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ CCZ013 ∷ CS24 ∷ Toff201 ∷ CCZ013 ∷ CS24⁻ ∷ X0 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b18 = at 4 2 (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4)) ▸
       at 5 2 (Toff201 ∷ CCZ013 ∷ []) (wl1735 (lit c4)) ▸
       at 6 2 [] (wl0230 (lit c4)) ▸
       at 4 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 2 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 2 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸ done

  b19 : Chain (Bx4-1023 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff302 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b19 = at 4 1 (CS24 ∷ []) (refl) ▸
       at 6 1 (CS24⁻ ∷ []) (refl) ▸
       at 6 3 (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) (wp1516 c4) ▸
       at 5 3 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (sym (wl1736 (lit c4))) ▸
       at 4 3 (CX23 ∷ Toff302 ∷ CS24 ∷ []) (wp1517 c4) ▸
       at 3 3 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (sym (wl1736 (lit c4))) ▸
       at 2 2 (CX23 ∷ Bx3-4012 ∷ []) (sym (lem-CXu-box-4-at0314203142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸ done

  b20 : Chain (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff302 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff302 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b20 = at 6 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸
       at 5 2 (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4) ▸
       at 4 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸
       at 6 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 5 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 6 2 (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4)) ▸
       at 7 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 8 2 (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4)) ▸ done

  b21 : Chain (Bx4-1023 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff302 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Sb3-4-01-2 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b21 = at 9 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 3 3 (Toff302 ∷ CCZ034 ∷ []) (wp1202 c4) ▸
       at 4 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 6 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 4 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 1 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸ done

  b22 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Sb3-4-01-2 ∷ X0 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Bx3-4012 ∷ CS13 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ [])
  b22 = at 4 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 3 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 5 1 (CS24 ∷ []) (refl) ▸
       at 7 1 (CS24⁻ ∷ []) (refl) ▸
       at 7 2 (CS13 ∷ CS24⁻ ∷ []) (sym (wl1701 (lit c4))) ▸
       at 6 2 (CS13 ∷ Toff201 ∷ []) (sym (wl1737 (lit c4))) ▸
       at 5 2 (CS13 ∷ CS24 ∷ []) (sym (wl1699 (lit c4))) ▸
       at 4 2 (CS13 ∷ Toff201 ∷ []) (sym (wl1737 (lit c4))) ▸ done

  b23 : Chain (Bx4-1023 ∷ Toff302 ∷ X0 ∷ Bx3-4012 ∷ CS13 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ Toff302 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (CS13 ∷ Bx3-4012 ∷ []) (sym (lem-CSu-box-3-at0314203142 c4)) ▸
       at 6 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 4 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X0 ∷ []) (sym (wl1526 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff302 ∷ X0 ∷ []) (sym (wl1520 (lit c4))) ▸
       at 4 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 6 1 (CS24 ∷ []) (refl) ▸ done

  b24 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ CX23 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b24 = at 8 1 (CS24⁻ ∷ []) (refl) ▸
       at 8 3 (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) (wp1516 c4) ▸
       at 7 3 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (sym (wl1736 (lit c4))) ▸
       at 6 3 (CX23 ∷ Toff302 ∷ CS24 ∷ []) (wp1517 c4) ▸
       at 5 3 (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (sym (wl1736 (lit c4))) ▸
       at 4 2 (CX23 ∷ Bx3-4012 ∷ []) (sym (lem-CXu-box-4-at0314203142 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4) ▸
       at 8 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸ done

  b25 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff302 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff302 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13⁻ ∷ [])
  b25 = at 7 2 (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4) ▸
       at 6 2 (Toff302 ∷ Toff312 ∷ []) (sym (wl1358 (lit c4))) ▸
       at 8 1 (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4) ▸
       at 7 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 8 2 (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4)) ▸
       at 9 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 10 2 (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4)) ▸
       at 11 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸ done

  b26 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ X0 ∷ CX23 ∷ CCZ034 ∷ Toff302 ∷ CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ CS13⁻ ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Sb3-4-01-2 ∷ CS13⁻ ∷ X0 ∷ [])
  b26 = at 7 5 (CCZ024 ∷ []) (sym (wp0496 c4)) ▸
       at 5 3 (Toff302 ∷ CCZ034 ∷ []) (wp1202 c4) ▸
       at 6 4 (Bx3-4012 ∷ []) (sym (lem-box-cP-at0314203142 c4)) ▸
       at 8 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 6 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 3 3 (Toff302 ∷ X0 ∷ []) (sym (wl1525 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸ done

  b27 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ Sb3-4-01-2 ∷ CS13⁻ ∷ X0 ∷ []) (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ [])
  b27 = at 5 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 7 1 (CS24 ∷ []) (refl) ▸
       at 9 1 (CS24⁻ ∷ []) (refl) ▸
       at 9 2 (CS13⁻ ∷ CS24⁻ ∷ []) (sym (wl0228 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ Toff201 ∷ []) (sym (wl1738 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CS24 ∷ []) (sym (wl1698 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ Toff201 ∷ []) (sym (wl1738 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ Bx3-4012 ∷ []) (sym (lem-CSdu-box-3-at0314203142 c4)) ▸ done

  b28 : Chain (Bx4-1023 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ X0 ∷ CS13⁻ ∷ Bx3-4012 ∷ Toff201 ∷ CS24 ∷ Toff201 ∷ CS24⁻ ∷ X0 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  b28 = at 8 1 (Sb3-4-2-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻3-4-2-1 ∷ []) (refl) ▸
       at 6 5 (Sb3-4-01-2 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X0 ∷ []) (sym (wl1528 (lit c4))) ▸
       at 2 1 (Sb4-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻4-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb4-1-02-3 ∷ []) (refl) ▸
       at 2 1 (Sb2-4-01-3 ∷ []) (sym (lem-F0-at0410213243 c4)) ▸ done
