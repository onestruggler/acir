{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D203 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl1463 ; wl1464 ; wl0207 ; wl0228 ; wl0263 ; wl0334 ; wl0861 ; wl0871 ; wl0879 ; wl1151 ; wl1152 ; wl1190 ; wl1226 ; wl1358 ; wl1675 ; wl1689 ; wl1690 ; wl1691 ; wl1692 ; wl1693 ; wl1694 ; wl1695 ; wl1696 ; wl1697 ; wl1698 ; wl1699 ; wl1700 ; wl1701 ; wp0053 ; wp0054 ; wp0066 ; wp0108 ; wp0357 ; wp0496 ; wp1005 ; wp1006 ; wp1202 ; wp1438 ; wp1442 ; wp1443 ; wp1444 ; wp1445 ; wp1446 ; wp1447 ; wp1448 ; wp1449 ; wp1450 ; wp1451 ; wp1452 ; wp1453 ; wp1454 ; wl1713 ; wl1714 ; wl0172 ; wl0173 ; wl0181 ; wl0230 ; wl0280 ; wl0289 ; wl0463 ; wl0882 ; wl0889 ; wl1516 ; wl1520 ; wl1525 ; wl1526 ; wl1528 ; wl1720 ; wl1733 ; wl1734 ; wl1735 ; wl1736 ; wl1737 ; wl1738 ; wp0312 ; wp0313 ; wp0314 ; wp0919 ; wp1250 ; wp1351 ; wp1352 ; wp1353 ; wp1465 ; wp1483 ; wp1515 ; wp1516 ; wp1517)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
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

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ []) (Bx0-1234 ∷ []) (lem-L-CCZ-1 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CK41 ∷ S4 ∷ CK41 ∷ []) [] (wl1463 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx0-1234 ∷ Bx0-1234 ∷ []) [] (lem-box2 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CK41 ∷ CK41 ∷ S4 ∷ []) [] (wl1464 (lit c4))

-- ckt-TT: 5 steps
lem-ckt-TT : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-ckt-TT c4 = derive (CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) []
  (rw 1 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw 0 (q4 c4) ∷ []) Eq.refl

private
  q5 : Ws → Eqn
  q5 c4 = eqn (Sb2-4-01-3 ∷ []) (Sb3-4-01-2 ∷ []) (lem-F0-at0410213243 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Bx3-4012 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ034 ∷ X0 ∷ CZ34 ∷ []) (X0 ∷ CCZ034 ∷ []) (wp1442 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CZ34 ∷ Toff312 ∷ []) (Toff312 ∷ CZ34 ∷ CCZ124 ∷ []) (wl1689 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (X0 ∷ Toff312 ∷ []) (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ124 ∷ []) (CS12 ∷ CX41 ∷ CS12⁻ ∷ CX41 ∷ CS24 ∷ []) (wl0334 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (CCZ034 ∷ CS24 ∷ []) (CS24 ∷ CCZ034 ∷ []) (wp0108 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ034 ∷ CX41 ∷ []) (CX41 ∷ CCZ034 ∷ []) (wp0357 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q14 : Ws → Eqn
  q14 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ034 ∷ CZ34 ∷ []) (CZ34 ∷ CCZ034 ∷ []) (wp1443 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (X0 ∷ CZ34 ∷ CZ34 ∷ []) (X0 ∷ []) (wl1690 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ124 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CS13⁻ ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CS13⁻ ∷ []) (lem-CSdu-box-3-at0314203142 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ034 ∷ Toff302 ∷ CCZ024 ∷ []) (Toff302 ∷ CCZ034 ∷ []) (wp1202 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ024 ∷ []) (CS02 ∷ CX40 ∷ CS02⁻ ∷ CX40 ∷ CS24 ∷ []) (wp0496 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS24 ∷ Toff312 ∷ []) (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CX40 ∷ Toff312 ∷ []) (Toff312 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF312 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = eqn (CS02⁻ ∷ Toff312 ∷ []) (Toff312 ∷ CS02⁻ ∷ []) (wl1226 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CS02 ∷ Toff312 ∷ []) (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (Toff302 ∷ Toff312 ∷ []) (Toff312 ∷ Toff302 ∷ []) (wl1358 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CCZ034 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp1438 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS13 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CS13 ∷ []) (lem-CSu-box-3-at0314203142 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (Bx4-1023 ∷ []) (Bx4-1230 ∷ []) (lem-box-perm-1342-at04203243 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx3-4012 ∷ []) (Bx3-4120 ∷ []) (lem-box-perm-1342-at0314203142 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx4-1230 ∷ Bx3-4120 ∷ []) (Bx3-4120 ∷ Bx4-1230 ∷ []) (lem-box-box-3-at0440 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4012 ∷ []) (lem-box-perm-1423-at0314213240 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx4-1230 ∷ []) (Bx4-1023 ∷ []) (lem-box-perm-1423-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx4-1023 ∷ []) (CCZ014 ∷ Toff423 ∷ CCZ014 ∷ Toff423 ∷ []) (lem-box-cP-at04203243 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ124 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ124 ∷ CCZ123 ∷ []) (wl1691 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp0053 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ014 ∷ CX12 ∷ []) (CX12 ∷ CCZ014 ∷ []) (wp0054 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ124 ∷ CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ124 ∷ []) (wl1692 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CS24 ∷ Toff302 ∷ []) (Toff302 ∷ CS24 ∷ []) (wp1006 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CX41 ∷ Toff302 ∷ []) (Toff302 ∷ CX41 ∷ []) (lem-comm-CX41-TOFF302 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CS12⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS12⁻ ∷ []) (wl1675 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS12 ∷ Toff302 ∷ []) (Toff302 ∷ CS12 ∷ []) (wl1190 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ124 ∷ CS13 ∷ []) (CS13 ∷ CCZ124 ∷ []) (wl1152 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ124 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ124 ∷ []) (wl1151 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ124 ∷ X0 ∷ []) (X0 ∷ CCZ124 ∷ []) (wp1444 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl0263 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CX12 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ []) (wl1693 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CX12 ∷ Toff201 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ CX12 ∷ Toff201 ∷ []) (wl1694 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Bx4-1023 ∷ []) (Bx4-1203 ∷ []) (lem-box-perm-1324-at04203243 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (Bx4-1203 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) (lem-box-cP-at043043 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (Toff403 ∷ CX12 ∷ []) (CX12 ∷ Toff403 ∷ []) (lem-comm-TOFF403-CX12 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (Toff201 ∷ []) (wl1695 (lit c4))
  q56 : Ws → Eqn
  q56 c4 = eqn (K2 ∷ Toff403 ∷ []) (Toff403 ∷ K2 ∷ []) (wp1445 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CS02 ∷ Toff403 ∷ []) (Toff403 ∷ CS02 ∷ []) (wp1446 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS02⁻ ∷ Toff403 ∷ []) (Toff403 ∷ CS02⁻ ∷ []) (wp1447 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CS01 ∷ Toff403 ∷ []) (Toff403 ∷ CS01 ∷ []) (wp1448 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (K2⁻ ∷ Toff403 ∷ []) (Toff403 ∷ K2⁻ ∷ []) (wp1449 c4)
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ124 ∷ CX12 ∷ Toff201 ∷ []) (CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp1450 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CZ14 ∷ CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CZ14 ∷ []) (wp1451 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ014 ∷ CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ014 ∷ []) (wp1452 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (CZ14 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (CZ14 ∷ CCZ014 ∷ []) (wp1453 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ124 ∷ CX12 ∷ Toff201 ∷ CZ14 ∷ CCZ014 ∷ []) (CX12 ∷ Toff201 ∷ CCZ124 ∷ []) (wp1454 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff201 ∷ X0 ∷ []) (X0 ∷ CX12 ∷ Toff201 ∷ []) (wl1696 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CS24 ∷ X0 ∷ []) (X0 ∷ CS24 ∷ []) (wl1697 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CS13⁻ ∷ CS24 ∷ []) (CS24 ∷ CS13⁻ ∷ []) (wl1698 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (CS13 ∷ CS24 ∷ []) (CS24 ∷ CS13 ∷ []) (wl1699 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CS24 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ CS24 ∷ []) (lem-CSu-box-3-at04203243 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (CS24⁻ ∷ X0 ∷ []) (X0 ∷ CS24⁻ ∷ []) (wl1700 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CS13⁻ ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13⁻ ∷ []) (wl0228 (lit c4))
  q73 : Ws → Eqn
  q73 c4 = eqn (CS24⁻ ∷ Toff302 ∷ []) (Toff302 ∷ CS24⁻ ∷ []) (wp1005 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (CS13 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CS13 ∷ []) (wl1701 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CS24⁻ ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ CS24⁻ ∷ []) (lem-CSdu-box-3-at04203243 c4)

-- F4-CS1-CS0 @0440: 214 steps
lem-F4-CS1-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS0-at0440 c4 = derive (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  (rw 3 (q5 c4) ∷
   re 3 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) ∷
   re 5 1 (CS24 ∷ []) ∷
   re 7 1 (CS24⁻ ∷ []) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 3 (q9 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 10 (q11 c4) ∷
   rw⁻ 9 (q12 c4) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q10 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw 5 (q16 c4) ∷
   rw 6 (q17 c4) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   re 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 5 (q18 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 6 (q26 c4) ∷
   rw 7 (q25 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw 3 (q27 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw 5 (q22 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 5 (q25 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 1 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q6 c4) ∷
   rw⁻ 0 (q7 c4) ∷
   rw 2 (q8 c4) ∷
   rw 1 (q9 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 8 (q11 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw 3 (q16 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 0 (q6 c4) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 2 (q34 c4) ∷
   rw 3 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw 7 (q39 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw 5 (q40 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   rw 3 (q10 c4) ∷
   rw 7 (q42 c4) ∷
   rw 6 (q43 c4) ∷
   rw 5 (q44 c4) ∷
   rw 4 (q43 c4) ∷
   rw 3 (q45 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q10 c4) ∷
   rw 9 (q42 c4) ∷
   rw 8 (q43 c4) ∷
   rw 7 (q44 c4) ∷
   rw 6 (q43 c4) ∷
   rw 5 (q45 c4) ∷
   rw⁻ 6 (q10 c4) ∷
   rw 6 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw 8 (q49 c4) ∷
   re 4 1 (Sb4-1-3-2 ∷ []) ∷
   re 6 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 2 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 3 (q50 c4) ∷
   re 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 4 1 (CS13 ∷ []) ∷
   re 6 1 (CS13⁻ ∷ []) ∷
   rw⁻ 3 (q51 c4) ∷
   rw 2 (q52 c4) ∷
   rw 2 (q53 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw⁻ 7 (q57 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 11 (q59 c4) ∷
   rw⁻ 12 (q60 c4) ∷
   rw 6 (q55 c4) ∷
   rw 4 (q61 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw 6 (q54 c4) ∷
   rw⁻ 7 (q58 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q59 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw 4 (q55 c4) ∷
   rw⁻ 5 (q62 c4) ∷
   rw⁻ 7 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   re 6 1 (Sb4-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 4 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 1 (q66 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 7 (q68 c4) ∷
   rw⁻ 6 (q42 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 4 (q42 c4) ∷
   rw⁻ 3 (q70 c4) ∷
   re 6 1 (Sb4-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 4 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 2 (q67 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   re 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 6 1 (CS13 ∷ []) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q51 c4) ∷
   rw 4 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw 7 (q54 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw⁻ 8 (q56 c4) ∷
   rw⁻ 9 (q57 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 11 (q58 c4) ∷
   rw 12 (q54 c4) ∷
   rw⁻ 13 (q59 c4) ∷
   rw⁻ 14 (q60 c4) ∷
   rw 8 (q55 c4) ∷
   rw 6 (q61 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw⁻ 7 (q57 c4) ∷
   rw 8 (q54 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw 10 (q54 c4) ∷
   rw⁻ 11 (q59 c4) ∷
   rw⁻ 12 (q60 c4) ∷
   rw 6 (q55 c4) ∷
   rw⁻ 7 (q62 c4) ∷
   rw⁻ 9 (q63 c4) ∷
   rw 7 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw⁻ 6 (q52 c4) ∷
   re 8 1 (Sb4-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 6 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 3 (q66 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   re 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw 9 (q72 c4) ∷
   rw⁻ 8 (q73 c4) ∷
   rw 7 (q74 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   re 8 1 (Sb4-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 6 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 4 (q71 c4) ∷
   re 2 1 (Sb3-4-2-1 ∷ []) ∷
   re 4 1 (Sb⁻3-4-2-1 ∷ []) ∷
   re 0 5 (Sb3-4-01-2 ∷ []) ∷
   rw⁻ 0 (q5 c4) ∷ []) Eq.refl

private
  q76 : Ws → Eqn
  q76 c4 = eqn (Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ []) (Bx4-1230 ∷ []) (lem-L-CCZ-1-at0440 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CK01 ∷ S0 ∷ CK01 ∷ []) [] (wl1713 (lit c4))
  q78 : Ws → Eqn
  q78 c4 = eqn (Bx4-1230 ∷ Bx4-1230 ∷ []) [] (lem-box2-at0440 c4)
  q79 : Ws → Eqn
  q79 c4 = eqn (CK01 ∷ CK01 ∷ S0 ∷ []) [] (wl1714 (lit c4))

-- ckt-TT @0440: 5 steps
lem-ckt-TT-at0440 : Ws → ⟪ (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-ckt-TT-at0440 c4 = derive (CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) []
  (rw 1 (q76 c4) ∷
   rw 5 (q76 c4) ∷
   rw 2 (q77 c4) ∷
   rw 1 (q78 c4) ∷
   rw 0 (q79 c4) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ014 ∷ X0 ∷ CZ14 ∷ []) (X0 ∷ CCZ014 ∷ []) (wp1351 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CZ14 ∷ Toff423 ∷ []) (Toff423 ∷ CZ14 ∷ CCZ123 ∷ []) (wl1516 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (X0 ∷ Toff423 ∷ []) (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑))
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ014 ∷ CZ14 ∷ []) (CZ14 ∷ CCZ014 ∷ []) (wp1352 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (X0 ∷ CZ14 ∷ CZ14 ∷ []) (X0 ∷ []) (wp1353 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ123 ∷ Toff423 ∷ []) (Toff423 ∷ CCZ123 ∷ []) (wl0463 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ124 ∷ Toff201 ∷ CCZ014 ∷ []) (Toff201 ∷ CCZ124 ∷ []) (wp1250 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (CCZ014 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp1515 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (CX12 ∷ Toff403 ∷ []) (Toff403 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF403 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = eqn (CCZ124 ∷ CS01 ∷ []) (CS01 ∷ CCZ124 ∷ []) (wp0919 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) (wl0280 (lit c4))
  q92 : Ws → Eqn
  q92 c4 = eqn (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = eqn (CS03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4))
  q94 : Ws → Eqn
  q94 c4 = eqn (Toff201 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff201 ∷ []) (wp1465 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (CCZ013 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ013 ∷ []) (wp1483 c4)
  q96 : Ws → Eqn
  q96 c4 = eqn (Bx4-1023 ∷ []) (Bx4-3120 ∷ []) (lem-box-perm-4132-at04203243 c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx3-4120 ∷ Bx4-3120 ∷ []) (Bx4-3120 ∷ Bx3-4120 ∷ []) (lem-box-box-1-at0314213240 c4)
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx4-3120 ∷ []) (Bx4-1023 ∷ []) (lem-box-perm-2431-at0413213240 c4)
  q99 : Ws → Eqn
  q99 c4 = eqn (CCZ034 ∷ CS13 ∷ []) (CS13 ∷ CCZ034 ∷ []) (wp0312 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q101 : Ws → Eqn
  q101 c4 = eqn (CCZ034 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ034 ∷ []) (wp0313 c4)
  q102 : Ws → Eqn
  q102 c4 = eqn (CCZ034 ∷ CS23 ∷ []) (CS23 ∷ CCZ034 ∷ []) (wp0314 c4)
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4))
  q105 : Ws → Eqn
  q105 c4 = eqn (CZ12 ∷ CCZ123 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ123 ∷ []) (wl0889 (lit c4))
  q106 : Ws → Eqn
  q106 c4 = eqn (CCZ123 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1733 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CCZ013 ∷ CS24 ∷ []) (CS24 ∷ CCZ013 ∷ []) (lem-comm-CCZ013-CS24 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ123 ∷ CS24 ∷ []) (CS24 ∷ CCZ123 ∷ []) (wl0173 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = eqn (CCZ123 ∷ CCZ013 ∷ Toff201 ∷ CCZ013 ∷ []) (Toff201 ∷ CCZ013 ∷ CCZ123 ∷ []) (wl1734 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ123 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ123 ∷ []) (wl0172 (lit c4))
  q111 : Ws → Eqn
  q111 c4 = eqn (CCZ123 ∷ X0 ∷ []) (X0 ∷ CCZ123 ∷ []) (wl1720 (lit c4))
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl0181 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = eqn (CCZ013 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ013 ∷ []) (wl1735 (lit c4))
  q114 : Ws → Eqn
  q114 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl0230 (lit c4))
  q115 : Ws → Eqn
  q115 c4 = eqn (CX23 ∷ Toff302 ∷ X0 ∷ []) (X0 ∷ Toff302 ∷ []) (wl1520 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (CS24⁻ ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CS24⁻ ∷ []) (wp1516 c4)
  q117 : Ws → Eqn
  q117 c4 = eqn (CX23 ∷ Toff302 ∷ Toff201 ∷ []) (Toff201 ∷ CX23 ∷ Toff302 ∷ []) (wl1736 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CS24 ∷ CX23 ∷ Toff302 ∷ []) (CX23 ∷ Toff302 ∷ CS24 ∷ []) (wp1517 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (CX23 ∷ Bx3-4012 ∷ []) (Bx3-4012 ∷ CX23 ∷ []) (lem-CXu-box-4-at0314203142 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (Toff312 ∷ CX40 ∷ []) (CX40 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX40 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (Toff302 ∷ X0 ∷ []) (X0 ∷ CX23 ∷ Toff302 ∷ []) (wl1525 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CS13 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ []) (wl1526 (lit c4))
  q123 : Ws → Eqn
  q123 c4 = eqn (CS13 ∷ Toff201 ∷ []) (Toff201 ∷ CS13 ∷ []) (wl1737 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CS13⁻ ∷ X0 ∷ []) (X0 ∷ CS13⁻ ∷ []) (wl1528 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CS13⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS13⁻ ∷ []) (wl1738 (lit c4))

-- F4-CS0-CS1 @0440: 232 steps
lem-F4-CS0-CS1-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS1-at0440 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw 1 (q5 c4) ∷
   re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q33 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw 3 (q82 c4) ∷
   rw 6 (q36 c4) ∷
   rw⁻ 10 (q37 c4) ∷
   rw⁻ 9 (q38 c4) ∷
   rw 8 (q39 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 6 (q40 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   rw⁻ 4 (q80 c4) ∷
   rw 5 (q84 c4) ∷
   rw 6 (q85 c4) ∷
   rw 5 (q82 c4) ∷
   rw⁻ 2 (q33 c4) ∷
   re 1 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) ∷
   re 5 1 (CS24⁻ ∷ []) ∷
   rw 5 (q75 c4) ∷
   rw 5 (q52 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 6 (q87 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 11 (q60 c4) ∷
   rw 10 (q59 c4) ∷
   rw 9 (q88 c4) ∷
   rw 8 (q58 c4) ∷
   rw 7 (q88 c4) ∷
   rw 6 (q57 c4) ∷
   rw 5 (q56 c4) ∷
   rw 6 (q55 c4) ∷
   rw 8 (q89 c4) ∷
   rw⁻ 12 (q90 c4) ∷
   rw⁻ 11 (q91 c4) ∷
   rw 10 (q92 c4) ∷
   rw⁻ 9 (q91 c4) ∷
   rw 8 (q93 c4) ∷
   rw⁻ 9 (q89 c4) ∷
   rw 7 (q34 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw 7 (q94 c4) ∷
   rw 8 (q95 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 13 (q60 c4) ∷
   rw 12 (q59 c4) ∷
   rw 11 (q88 c4) ∷
   rw 10 (q58 c4) ∷
   rw 9 (q88 c4) ∷
   rw 8 (q57 c4) ∷
   rw 7 (q56 c4) ∷
   rw 8 (q55 c4) ∷
   rw⁻ 4 (q53 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   re 3 1 (CS24 ∷ []) ∷
   rw 3 (q70 c4) ∷
   rw 3 (q52 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw 4 (q87 c4) ∷
   rw⁻ 3 (q55 c4) ∷
   rw 9 (q60 c4) ∷
   rw 8 (q59 c4) ∷
   rw 7 (q88 c4) ∷
   rw 6 (q58 c4) ∷
   rw 5 (q88 c4) ∷
   rw 4 (q57 c4) ∷
   rw 3 (q56 c4) ∷
   rw 4 (q55 c4) ∷
   rw 6 (q89 c4) ∷
   rw⁻ 10 (q90 c4) ∷
   rw⁻ 9 (q91 c4) ∷
   rw 8 (q92 c4) ∷
   rw⁻ 7 (q91 c4) ∷
   rw 6 (q93 c4) ∷
   rw⁻ 7 (q89 c4) ∷
   rw 5 (q34 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 5 (q94 c4) ∷
   rw 6 (q95 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 11 (q60 c4) ∷
   rw 10 (q59 c4) ∷
   rw 9 (q88 c4) ∷
   rw 8 (q58 c4) ∷
   rw 7 (q88 c4) ∷
   rw 6 (q57 c4) ∷
   rw 5 (q56 c4) ∷
   rw 6 (q55 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw⁻ 2 (q52 c4) ∷
   rw 1 (q29 c4) ∷
   rw 2 (q96 c4) ∷
   rw 1 (q97 c4) ∷
   rw 1 (q98 c4) ∷
   rw 2 (q31 c4) ∷
   rw 1 (q33 c4) ∷
   rw⁻ 0 (q80 c4) ∷
   rw 2 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 8 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw 4 (q40 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 2 (q80 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw 3 (q82 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   rw 3 (q6 c4) ∷
   rw 2 (q36 c4) ∷
   rw⁻ 6 (q99 c4) ∷
   rw 5 (q100 c4) ∷
   rw⁻ 4 (q101 c4) ∷
   rw 3 (q100 c4) ∷
   rw⁻ 2 (q102 c4) ∷
   rw⁻ 3 (q36 c4) ∷
   rw 3 (q103 c4) ∷
   rw 5 (q36 c4) ∷
   rw⁻ 9 (q99 c4) ∷
   rw 8 (q100 c4) ∷
   rw⁻ 7 (q101 c4) ∷
   rw 6 (q100 c4) ∷
   rw⁻ 5 (q102 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 4 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 3 (q106 c4) ∷
   rw 6 (q107 c4) ∷
   rw 5 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw 8 (q110 c4) ∷
   rw 9 (q111 c4) ∷
   rw 10 (q112 c4) ∷
   rw 4 (q107 c4) ∷
   rw 5 (q113 c4) ∷
   rw 6 (q114 c4) ∷
   re 4 1 (Sb3-4-2-1 ∷ []) ∷
   re 6 1 (Sb⁻3-4-2-1 ∷ []) ∷
   re 2 5 (Sb3-4-01-2 ∷ []) ∷
   rw⁻ 3 (q115 c4) ∷
   re 2 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) ∷
   re 4 1 (CS24 ∷ []) ∷
   re 6 1 (CS24⁻ ∷ []) ∷
   rw 6 (q116 c4) ∷
   rw⁻ 5 (q117 c4) ∷
   rw 4 (q118 c4) ∷
   rw⁻ 3 (q117 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 5 (q26 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   rw 6 (q120 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 8 (q120 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   re 6 1 (Sb3-4-2-1 ∷ []) ∷
   re 8 1 (Sb⁻3-4-2-1 ∷ []) ∷
   re 4 5 (Sb3-4-01-2 ∷ []) ∷
   rw⁻ 1 (q121 c4) ∷
   rw⁻ 4 (q122 c4) ∷
   re 3 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) ∷
   re 5 1 (CS24 ∷ []) ∷
   re 7 1 (CS24⁻ ∷ []) ∷
   rw⁻ 7 (q74 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   rw⁻ 4 (q123 c4) ∷
   rw⁻ 3 (q27 c4) ∷
   re 6 1 (Sb3-4-2-1 ∷ []) ∷
   re 8 1 (Sb⁻3-4-2-1 ∷ []) ∷
   re 4 5 (Sb3-4-01-2 ∷ []) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   re 4 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) ∷
   re 6 1 (CS24 ∷ []) ∷
   re 8 1 (CS24⁻ ∷ []) ∷
   rw 8 (q116 c4) ∷
   rw⁻ 7 (q117 c4) ∷
   rw 6 (q118 c4) ∷
   rw⁻ 5 (q117 c4) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 8 (q120 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 10 (q120 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 5 (q19 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   re 8 1 (Sb3-4-2-1 ∷ []) ∷
   re 10 1 (Sb⁻3-4-2-1 ∷ []) ∷
   re 6 5 (Sb3-4-01-2 ∷ []) ∷
   rw⁻ 3 (q121 c4) ∷
   rw⁻ 6 (q124 c4) ∷
   re 5 1 (Bx3-4012 ∷ Toff201 ∷ Sb3-4-2-1 ∷ Toff201 ∷ Sb⁻3-4-2-1 ∷ []) ∷
   re 7 1 (CS24 ∷ []) ∷
   re 9 1 (CS24⁻ ∷ []) ∷
   rw⁻ 9 (q72 c4) ∷
   rw⁻ 8 (q125 c4) ∷
   rw⁻ 7 (q68 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   re 8 1 (Sb3-4-2-1 ∷ []) ∷
   re 10 1 (Sb⁻3-4-2-1 ∷ []) ∷
   re 6 5 (Sb3-4-01-2 ∷ []) ∷
   rw⁻ 4 (q124 c4) ∷
   re 2 1 (Sb4-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 2 (q5 c4) ∷ []) Eq.refl
