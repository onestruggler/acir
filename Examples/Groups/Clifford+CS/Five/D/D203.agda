{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD203 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D203 (Sᴰ : SD203) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS03-CCZ124 : Ws → St 957
  lem-comm-CS03-CCZ124 = pickᴰ 0 Sᴰ
  lem-comm-CS12-CCZ034 : Ws → St 191
  lem-comm-CS12-CCZ034 = pickᴰ 1 Sᴰ
  lem-comm-CS23-CCZ014 : Ws → St 703
  lem-comm-CS23-CCZ014 = pickᴰ 2 Sᴰ
  lem-comm-CSd03-CCZ124 : Ws → St 959
  lem-comm-CSd03-CCZ124 = pickᴰ 3 Sᴰ
  lem-comm-CSd12-CCZ034 : Ws → St 199
  lem-comm-CSd12-CCZ034 = pickᴰ 4 Sᴰ
  lem-comm-CSd23-CCZ014 : Ws → St 704
  lem-comm-CSd23-CCZ014 = pickᴰ 5 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 6 Sᴰ
  lem-comm-CZ12-CCZ034 : Ws → St 65
  lem-comm-CZ12-CCZ034 = pickᴰ 7 Sᴰ
  lem-comm-CX40-TOFF312 : Ws → St 965
  lem-comm-CX40-TOFF312 = pickᴰ 8 Sᴰ
  lem-comm-CCZ013-CS24 : Ws → St 2050
  lem-comm-CCZ013-CS24 = pickᴰ 9 Sᴰ
  lem-comm-CX12-TOFF403 : Ws → St 2051
  lem-comm-CX12-TOFF403 = pickᴰ 10 Sᴰ
  lem-comm-CX41-TOFF302 : Ws → St 1661
  lem-comm-CX41-TOFF302 = pickᴰ 11 Sᴰ
  lem-comm-TOFF312-CX40 : Ws → St 2052
  lem-comm-TOFF312-CX40 = pickᴰ 12 Sᴰ
  lem-comm-TOFF403-CX12 : Ws → St 2053
  lem-comm-TOFF403-CX12 = pickᴰ 13 Sᴰ
  lem-box-cP-at04203243 : Ws → St 919
  lem-box-cP-at04203243 = pickᴰ 14 Sᴰ
  lem-box-cP-at0314203142 : Ws → St 997
  lem-box-cP-at0314203142 = pickᴰ 15 Sᴰ
  lem-box-cP-at043043 : Ws → St 999
  lem-box-cP-at043043 = pickᴰ 16 Sᴰ
  lem-CSdu-box-3-at04203243 : Ws → St 2054
  lem-CSdu-box-3-at04203243 = pickᴰ 17 Sᴰ
  lem-CSu-box-3-at04203243 : Ws → St 2055
  lem-CSu-box-3-at04203243 = pickᴰ 18 Sᴰ
  lem-box-perm-1324-at04203243 : Ws → St 1197
  lem-box-perm-1324-at04203243 = pickᴰ 19 Sᴰ
  lem-box2 : Ws → St 1509
  lem-box2 = pickᴰ 20 Sᴰ
  lem-CSdu-box-3-at0314203142 : Ws → St 2056
  lem-CSdu-box-3-at0314203142 = pickᴰ 21 Sᴰ
  lem-CSu-box-3-at0314203142 : Ws → St 2057
  lem-CSu-box-3-at0314203142 = pickᴰ 22 Sᴰ
  lem-CXu-box-4-at0314203142 : Ws → St 2058
  lem-CXu-box-4-at0314203142 = pickᴰ 23 Sᴰ
  lem-box-perm-1342-at04203243 : Ws → St 2059
  lem-box-perm-1342-at04203243 = pickᴰ 24 Sᴰ
  lem-box-perm-4132-at04203243 : Ws → St 2060
  lem-box-perm-4132-at04203243 = pickᴰ 25 Sᴰ
  lem-box2-at0440 : Ws → St 2061
  lem-box2-at0440 = pickᴰ 26 Sᴰ
  lem-box-perm-1342-at0314203142 : Ws → St 2062
  lem-box-perm-1342-at0314203142 = pickᴰ 27 Sᴰ
  lem-box-perm-1423-at0314213240 : Ws → St 2063
  lem-box-perm-1423-at0314213240 = pickᴰ 28 Sᴰ
  lem-box-perm-1423-at0440 : Ws → St 2064
  lem-box-perm-1423-at0440 = pickᴰ 29 Sᴰ
  lem-box-perm-2431-at0413213240 : Ws → St 2065
  lem-box-perm-2431-at0413213240 = pickᴰ 30 Sᴰ
  lem-box-box-3-at0440 : Ws → St 2066
  lem-box-box-3-at0440 = pickᴰ 31 Sᴰ
  lem-box-box-1-at0314213240 : Ws → St 2067
  lem-box-box-1-at0314213240 = pickᴰ 32 Sᴰ
  lem-L-CCZ-1 : Ws → St 2068
  lem-L-CCZ-1 = pickᴰ 33 Sᴰ
  lem-F0-at0410213243 : Ws → St 2069
  lem-F0-at0410213243 = pickᴰ 34 Sᴰ
  lem-L-CCZ-1-at0440 : Ws → St 2070
  lem-L-CCZ-1-at0440 = pickᴰ 35 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 2068 (lem-L-CCZ-1 c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 1463 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1509 (lem-box2 c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 1464 (lit c4)

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
  q5 c4 = sE 2069 (lem-F0-at0410213243 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 997 (lem-box-cP-at0314203142 c4)
  q7 : Ws → Eqn
  q7 c4 = wpE 1442 c4
  q8 : Ws → Eqn
  q8 c4 = wlE 1689 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (X0 ∷ Toff312 ∷ []) (Toff312 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ))
  q10 : Ws → Eqn
  q10 c4 = wlE 334 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wpE 108 c4
  q12 : Ws → Eqn
  q12 c4 = wpE 357 c4
  q13 : Ws → Eqn
  q13 c4 = sE 199 (lem-comm-CSd12-CCZ034 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 191 (lem-comm-CS12-CCZ034 c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 1443 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 1690 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 871 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = sE 2056 (lem-CSdu-box-3-at0314203142 c4)
  q19 : Ws → Eqn
  q19 c4 = wpE 1202 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 496 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 879 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 965 (lem-comm-CX40-TOFF312 c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 1226 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 861 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 1358 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = wpE 1438 c4
  q27 : Ws → Eqn
  q27 c4 = sE 2057 (lem-CSu-box-3-at0314203142 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 2059 (lem-box-perm-1342-at04203243 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 2062 (lem-box-perm-1342-at0314203142 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 2066 (lem-box-box-3-at0440 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 2063 (lem-box-perm-1423-at0314213240 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 2064 (lem-box-perm-1423-at0440 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 919 (lem-box-cP-at04203243 c4)
  q34 : Ws → Eqn
  q34 c4 = wpE 66 c4
  q35 : Ws → Eqn
  q35 c4 = wlE 1691 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 207 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wpE 53 c4
  q38 : Ws → Eqn
  q38 c4 = wpE 54 c4
  q39 : Ws → Eqn
  q39 c4 = sE 704 (lem-comm-CSd23-CCZ014 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 703 (lem-comm-CS23-CCZ014 c4)
  q41 : Ws → Eqn
  q41 c4 = wlE 1692 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wpE 1006 c4
  q43 : Ws → Eqn
  q43 c4 = sE 1661 (lem-comm-CX41-TOFF302 c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 1675 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 1190 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 1152 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 1151 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wpE 1444 c4
  q49 : Ws → Eqn
  q49 c4 = wlE 263 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wlE 1693 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wlE 1694 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = sE 1197 (lem-box-perm-1324-at04203243 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 999 (lem-box-cP-at043043 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 2053 (lem-comm-TOFF403-CX12 c4)
  q55 : Ws → Eqn
  q55 c4 = wlE 1695 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 1445 c4
  q57 : Ws → Eqn
  q57 c4 = wpE 1446 c4
  q58 : Ws → Eqn
  q58 c4 = wpE 1447 c4
  q59 : Ws → Eqn
  q59 c4 = wpE 1448 c4
  q60 : Ws → Eqn
  q60 c4 = wpE 1449 c4
  q61 : Ws → Eqn
  q61 c4 = wpE 1450 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 1451 c4
  q63 : Ws → Eqn
  q63 c4 = wpE 1452 c4
  q64 : Ws → Eqn
  q64 c4 = wpE 1453 c4
  q65 : Ws → Eqn
  q65 c4 = wpE 1454 c4
  q66 : Ws → Eqn
  q66 c4 = wlE 1696 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = wlE 1697 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 1698 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wlE 1699 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = sE 2055 (lem-CSu-box-3-at04203243 c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 1700 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wlE 228 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = wpE 1005 c4
  q74 : Ws → Eqn
  q74 c4 = wlE 1701 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = sE 2054 (lem-CSdu-box-3-at04203243 c4)

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
  q76 c4 = sE 2070 (lem-L-CCZ-1-at0440 c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 1713 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = sE 2061 (lem-box2-at0440 c4)
  q79 : Ws → Eqn
  q79 c4 = wlE 1714 (lit c4)

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
  q80 c4 = wpE 1351 c4
  q81 : Ws → Eqn
  q81 c4 = wlE 1516 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (X0 ∷ Toff423 ∷ []) (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑))
  q83 : Ws → Eqn
  q83 c4 = wpE 1352 c4
  q84 : Ws → Eqn
  q84 c4 = wpE 1353 c4
  q85 : Ws → Eqn
  q85 c4 = wlE 463 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wpE 1250 c4
  q87 : Ws → Eqn
  q87 c4 = wpE 1515 c4
  q88 : Ws → Eqn
  q88 c4 = sE 2051 (lem-comm-CX12-TOFF403 c4)
  q89 : Ws → Eqn
  q89 c4 = wlE 289 (lit c4)
  q90 : Ws → Eqn
  q90 c4 = wpE 919 c4
  q91 : Ws → Eqn
  q91 c4 = wlE 280 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = sE 959 (lem-comm-CSd03-CCZ124 c4)
  q93 : Ws → Eqn
  q93 c4 = sE 957 (lem-comm-CS03-CCZ124 c4)
  q94 : Ws → Eqn
  q94 c4 = wpE 1465 c4
  q95 : Ws → Eqn
  q95 c4 = wpE 1483 c4
  q96 : Ws → Eqn
  q96 c4 = sE 2060 (lem-box-perm-4132-at04203243 c4)
  q97 : Ws → Eqn
  q97 c4 = sE 2067 (lem-box-box-1-at0314213240 c4)
  q98 : Ws → Eqn
  q98 c4 = sE 2065 (lem-box-perm-2431-at0413213240 c4)
  q99 : Ws → Eqn
  q99 c4 = wpE 312 c4
  q100 : Ws → Eqn
  q100 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q101 : Ws → Eqn
  q101 c4 = wpE 313 c4
  q102 : Ws → Eqn
  q102 c4 = wpE 314 c4
  q103 : Ws → Eqn
  q103 c4 = wlE 882 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = sE 65 (lem-comm-CZ12-CCZ034 c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 889 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 1733 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = sE 2050 (lem-comm-CCZ013-CS24 c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 173 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 1734 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 172 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wlE 1720 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = wlE 181 (lit c4)
  q113 : Ws → Eqn
  q113 c4 = wlE 1735 (lit c4)
  q114 : Ws → Eqn
  q114 c4 = wlE 230 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wlE 1520 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = wpE 1516 c4
  q117 : Ws → Eqn
  q117 c4 = wlE 1736 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = wpE 1517 c4
  q119 : Ws → Eqn
  q119 c4 = sE 2058 (lem-CXu-box-4-at0314203142 c4)
  q120 : Ws → Eqn
  q120 c4 = sE 2052 (lem-comm-TOFF312-CX40 c4)
  q121 : Ws → Eqn
  q121 c4 = wlE 1525 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = wlE 1526 (lit c4)
  q123 : Ws → Eqn
  q123 c4 = wlE 1737 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = wlE 1528 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wlE 1738 (lit c4)

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
