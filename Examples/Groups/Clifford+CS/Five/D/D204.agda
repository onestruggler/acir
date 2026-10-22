{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD204 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D204 (Sᴰ : SD204) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034 ; lem-comm-CX12-TOFF034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ034-CX12 ; lem-comm-CCZ134-CS02 ; lem-comm-CCZ134-CX02 ; lem-comm-CX04-TOFF312 ; lem-comm-TOFF034-CX12 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF302-CX14)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-cP-at0310243142 : Ws → St 844
  lem-box-cP-at0310243142 = pickᴰ 0 Sᴰ
  lem-box-cP-at03243240 : Ws → St 960
  lem-box-cP-at03243240 = pickᴰ 1 Sᴰ
  lem-box-cP-at243243 : Ws → St 856
  lem-box-cP-at243243 = pickᴰ 2 Sᴰ
  lem-box-cP-at3443 : Ws → St 857
  lem-box-cP-at3443 = pickᴰ 3 Sᴰ
  lem-box-perm-1324-at243243 : Ws → St 1079
  lem-box-perm-1324-at243243 = pickᴰ 4 Sᴰ
  lem-CSdu-box-3-at0310243142 : Ws → St 1790
  lem-CSdu-box-3-at0310243142 = pickᴰ 5 Sᴰ
  lem-CSdu-box-3-at243243 : Ws → St 1791
  lem-CSdu-box-3-at243243 = pickᴰ 6 Sᴰ
  lem-CSu-box-3-at0310243142 : Ws → St 1792
  lem-CSu-box-3-at0310243142 = pickᴰ 7 Sᴰ
  lem-CSu-box-3-at243243 : Ws → St 1793
  lem-CSu-box-3-at243243 = pickᴰ 8 Sᴰ
  lem-CXu-box-4-at0310243142 : Ws → St 1794
  lem-CXu-box-4-at0310243142 = pickᴰ 9 Sᴰ
  lem-box2-at03243240 : Ws → St 1150
  lem-box2-at03243240 = pickᴰ 10 Sᴰ
  lem-box-perm-1342-at0310243142 : Ws → St 1795
  lem-box-perm-1342-at0310243142 = pickᴰ 11 Sᴰ
  lem-box-perm-1342-at243243 : Ws → St 1796
  lem-box-perm-1342-at243243 = pickᴰ 12 Sᴰ
  lem-box-perm-1423 : Ws → St 1797
  lem-box-perm-1423 = pickᴰ 13 Sᴰ
  lem-box-perm-1423-at03102132 : Ws → St 1798
  lem-box-perm-1423-at03102132 = pickᴰ 14 Sᴰ
  lem-box-perm-2431-at132132 : Ws → St 1799
  lem-box-perm-2431-at132132 = pickᴰ 15 Sᴰ
  lem-box-perm-4132-at243243 : Ws → St 1800
  lem-box-perm-4132-at243243 = pickᴰ 16 Sᴰ
  lem-box-perm-3241-at0310243142 : Ws → St 1801
  lem-box-perm-3241-at0310243142 = pickᴰ 17 Sᴰ
  lem-box-box-1-at03102132 : Ws → St 1495
  lem-box-box-1-at03102132 = pickᴰ 18 Sᴰ
  lem-box-box-3 : Ws → St 1802
  lem-box-box-3 = pickᴰ 19 Sᴰ
  lem-F0-at01143043 : Ws → St 1803
  lem-F0-at01143043 = pickᴰ 20 Sᴰ
  lem-F0-at14213243 : Ws → St 1804
  lem-F0-at14213243 = pickᴰ 21 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1804 (lem-F0-at14213243 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 856 (lem-box-cP-at243243 c4)
  q3 : Ws → Eqn
  q3 c4 = wpE 52 c4
  q4 : Ws → Eqn
  q4 c4 = wlE 206 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (Toff023 ∷ X4 ∷ []) (X4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q6 : Ws → Eqn
  q6 c4 = wlE 207 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wpE 53 c4
  q8 : Ws → Eqn
  q8 c4 = wpE 54 c4
  q9 : Ws → Eqn
  q9 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = wpE 55 c4
  q12 : Ws → Eqn
  q12 c4 = wlE 208 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 209 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1791 (lem-CSdu-box-3-at243243 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1079 (lem-box-perm-1324-at243243 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 857 (lem-box-cP-at3443 c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 750 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 165 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 888 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 751 c4
  q21 : Ws → Eqn
  q21 c4 = wpE 251 c4
  q22 : Ws → Eqn
  q22 c4 = eqn (CX12 ∷ Toff034 ∷ []) (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4))
  q23 : Ws → Eqn
  q23 c4 = wpE 252 c4
  q24 : Ws → Eqn
  q24 c4 = wpE 202 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 752 c4
  q26 : Ws → Eqn
  q26 c4 = wlE 166 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 11 c4
  q28 : Ws → Eqn
  q28 c4 = wlE 167 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ012 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS • CS • CS))
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q31 : Ws → Eqn
  q31 c4 = wpE 167 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 753 c4
  q33 : Ws → Eqn
  q33 c4 = wpE 12 c4
  q34 : Ws → Eqn
  q34 c4 = sE 1793 (lem-CSu-box-3-at243243 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1795 (lem-box-perm-1342-at0310243142 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1800 (lem-box-perm-4132-at243243 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 1495 (lem-box-box-1-at03102132 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1799 (lem-box-perm-2431-at132132 c4)
  q39 : Ws → Eqn
  q39 c4 = sE 1798 (lem-box-perm-1423-at03102132 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 844 (lem-box-cP-at0310243142 c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 312 c4
  q42 : Ws → Eqn
  q42 c4 = eqn (CX12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = wpE 313 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 314 c4
  q45 : Ws → Eqn
  q45 c4 = wlE 882 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CZ12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = wlE 889 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 890 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ134 ∷ CS02 ∷ []) (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = wlE 171 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wlE 891 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = wlE 611 (lit c4)
  q53 : Ws → Eqn
  q53 c4 = wlE 892 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wlE 181 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = wlE 893 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wlE 321 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wlE 894 (lit c4)
  q58 : Ws → Eqn
  q58 c4 = wpE 754 c4
  q59 : Ws → Eqn
  q59 c4 = wlE 895 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wpE 755 c4
  q61 : Ws → Eqn
  q61 c4 = sE 1794 (lem-CXu-box-4-at0310243142 c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 852 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wpE 295 c4
  q64 : Ws → Eqn
  q64 c4 = wpE 13 c4
  q65 : Ws → Eqn
  q65 c4 = wlE 879 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff312 ∷ CX04 ∷ []) (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = wlE 878 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 861 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wpE 737 c4
  q70 : Ws → Eqn
  q70 c4 = wlE 211 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 896 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wlE 897 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = wlE 898 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = wlE 899 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = sE 1792 (lem-CSu-box-3-at0310243142 c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 900 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 901 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = wlE 902 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = wlE 903 (lit c4)
  q80 : Ws → Eqn
  q80 c4 = sE 1790 (lem-CSdu-box-3-at0310243142 c4)

-- F4-CS0-CS1: 232 steps
lem-F4-CS0-CS1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS1 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw 1 (q1 c4) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw⁻ 10 (q7 c4) ∷
   rw⁻ 9 (q8 c4) ∷
   rw 8 (q9 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q10 c4) ∷
   rw⁻ 7 (q6 c4) ∷
   rw⁻ 5 (q11 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   re 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 5 1 (CS02⁻ ∷ []) ∷
   rw 5 (q14 c4) ∷
   rw 5 (q15 c4) ∷
   rw 5 (q16 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q24 c4) ∷
   rw 5 (q25 c4) ∷
   rw 6 (q19 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   rw⁻ 11 (q28 c4) ∷
   rw⁻ 10 (q29 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 9 (q26 c4) ∷
   rw⁻ 7 (q31 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 7 (q32 c4) ∷
   rw 8 (q33 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 13 (q20 c4) ∷
   rw 12 (q21 c4) ∷
   rw 11 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 9 (q22 c4) ∷
   rw 8 (q24 c4) ∷
   rw 7 (q25 c4) ∷
   rw 8 (q19 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   re 3 1 (CS02 ∷ []) ∷
   rw 3 (q34 c4) ∷
   rw 3 (q15 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 9 (q20 c4) ∷
   rw 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw 5 (q22 c4) ∷
   rw 4 (q24 c4) ∷
   rw 3 (q25 c4) ∷
   rw 4 (q19 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw⁻ 8 (q29 c4) ∷
   rw⁻ 7 (q28 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 7 (q26 c4) ∷
   rw⁻ 5 (q31 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 5 (q32 c4) ∷
   rw 6 (q33 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 11 (q20 c4) ∷
   rw 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw 7 (q22 c4) ∷
   rw 6 (q24 c4) ∷
   rw 5 (q25 c4) ∷
   rw 6 (q19 c4) ∷
   rw⁻ 2 (q16 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw 1 (q35 c4) ∷
   rw 2 (q36 c4) ∷
   rw 1 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷
   rw 1 (q2 c4) ∷
   rw⁻ 0 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 1 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 5 (q8 c4) ∷
   rw 4 (q10 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw⁻ 3 (q11 c4) ∷
   rw⁻ 2 (q3 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 3 (q40 c4) ∷
   rw 2 (q6 c4) ∷
   rw⁻ 6 (q41 c4) ∷
   rw 5 (q42 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   rw 3 (q42 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 3 (q45 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw⁻ 7 (q43 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 4 (q46 c4) ∷
   rw 5 (q47 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   rw 3 (q48 c4) ∷
   rw 6 (q49 c4) ∷
   rw 5 (q50 c4) ∷
   rw 6 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q53 c4) ∷
   rw 10 (q54 c4) ∷
   rw 4 (q49 c4) ∷
   rw 5 (q55 c4) ∷
   rw 6 (q56 c4) ∷
   re 4 1 (Sb3-0-2-1 ∷ []) ∷
   re 6 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 2 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 3 (q57 c4) ∷
   re 2 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 4 1 (CS02 ∷ []) ∷
   re 6 1 (CS02⁻ ∷ []) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 3 (q40 c4) ∷
   rw 6 (q62 c4) ∷
   rw 5 (q63 c4) ∷
   rw 4 (q62 c4) ∷
   rw 6 (q64 c4) ∷
   rw⁻ 5 (q65 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 9 (q68 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   re 6 1 (Sb3-0-2-1 ∷ []) ∷
   re 8 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 4 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 1 (q70 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   re 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 5 1 (CS02 ∷ []) ∷
   re 7 1 (CS02⁻ ∷ []) ∷
   rw 7 (q72 c4) ∷
   rw⁻ 6 (q73 c4) ∷
   rw 5 (q74 c4) ∷
   rw⁻ 4 (q73 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   re 6 1 (Sb3-0-2-1 ∷ []) ∷
   re 8 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 4 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 2 (q71 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   re 4 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 6 1 (CS02 ∷ []) ∷
   re 8 1 (CS02⁻ ∷ []) ∷
   rw 8 (q58 c4) ∷
   rw⁻ 7 (q59 c4) ∷
   rw 6 (q60 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   rw 5 (q40 c4) ∷
   rw 8 (q62 c4) ∷
   rw 7 (q63 c4) ∷
   rw 6 (q62 c4) ∷
   rw 8 (q64 c4) ∷
   rw⁻ 7 (q65 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 9 (q67 c4) ∷
   rw 10 (q66 c4) ∷
   rw⁻ 11 (q68 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 6 (q40 c4) ∷
   re 8 1 (Sb3-0-2-1 ∷ []) ∷
   re 10 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 6 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 3 (q70 c4) ∷
   rw⁻ 6 (q76 c4) ∷
   re 5 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 7 1 (CS02 ∷ []) ∷
   re 9 1 (CS02⁻ ∷ []) ∷
   rw 9 (q77 c4) ∷
   rw⁻ 8 (q78 c4) ∷
   rw 7 (q79 c4) ∷
   rw⁻ 6 (q78 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   re 8 1 (Sb3-0-2-1 ∷ []) ∷
   re 10 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 6 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 4 (q76 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 2 (q1 c4) ∷ []) Eq.refl

private
  q81 : Ws → Eqn
  q81 c4 = wpE 796 c4
  q82 : Ws → Eqn
  q82 c4 = wlE 512 (lit c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (Toff312 ∷ X4 ∷ []) (X4 ∷ Toff312 ∷ []) (c₄ (Toffᵗ ↑) (X))
  q84 : Ws → Eqn
  q84 c4 = wlE 348 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = wpE 3 c4
  q86 : Ws → Eqn
  q86 c4 = wpE 221 c4
  q87 : Ws → Eqn
  q87 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q88 : Ws → Eqn
  q88 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q89 : Ws → Eqn
  q89 c4 = wpE 797 c4
  q90 : Ws → Eqn
  q90 c4 = wpE 798 c4
  q91 : Ws → Eqn
  q91 c4 = wlE 503 (lit c4)
  q92 : Ws → Eqn
  q92 c4 = eqn (CX04 ∷ Toff312 ∷ []) (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4))
  q93 : Ws → Eqn
  q93 c4 = sE 1796 (lem-box-perm-1342-at243243 c4)
  q94 : Ws → Eqn
  q94 c4 = sE 1802 (lem-box-box-3 c4)
  q95 : Ws → Eqn
  q95 c4 = sE 1797 (lem-box-perm-1423 c4)
  q96 : Ws → Eqn
  q96 c4 = wlE 404 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = wlE 991 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = wpE 298 c4
  q99 : Ws → Eqn
  q99 c4 = eqn (CX01 ∷ Toff324 ∷ []) (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))
  q100 : Ws → Eqn
  q100 c4 = wlE 447 (lit c4)
  q101 : Ws → Eqn
  q101 c4 = wlE 214 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 311 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = wlE 992 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 993 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 341 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 994 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 995 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = eqn (Toff034 ∷ CX12 ∷ []) (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4))
  q109 : Ws → Eqn
  q109 c4 = wpE 799 c4
  q110 : Ws → Eqn
  q110 c4 = wpE 800 c4
  q111 : Ws → Eqn
  q111 c4 = wpE 801 c4
  q112 : Ws → Eqn
  q112 c4 = wpE 802 c4
  q113 : Ws → Eqn
  q113 c4 = wpE 803 c4
  q114 : Ws → Eqn
  q114 c4 = wlE 996 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wlE 997 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = wlE 998 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = wpE 804 c4

-- F4-CS1-CS0: 214 steps
lem-F4-CS1-CS0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS0 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw 3 (q1 c4) ∷
   re 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 5 1 (CS02 ∷ []) ∷
   re 7 1 (CS02⁻ ∷ []) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 2 (q81 c4) ∷
   rw 4 (q82 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw 6 (q84 c4) ∷
   rw⁻ 10 (q85 c4) ∷
   rw⁻ 9 (q86 c4) ∷
   rw 8 (q87 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw 6 (q88 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   rw⁻ 5 (q89 c4) ∷
   rw⁻ 4 (q81 c4) ∷
   rw 5 (q90 c4) ∷
   rw 6 (q91 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 5 (q80 c4) ∷
   rw 5 (q40 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw 6 (q64 c4) ∷
   rw 10 (q68 c4) ∷
   rw 9 (q92 c4) ∷
   rw 8 (q67 c4) ∷
   rw 7 (q92 c4) ∷
   rw 6 (q65 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw⁻ 5 (q62 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw⁻ 7 (q62 c4) ∷
   rw⁻ 4 (q40 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw 3 (q75 c4) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw 4 (q64 c4) ∷
   rw 8 (q68 c4) ∷
   rw 7 (q92 c4) ∷
   rw 6 (q67 c4) ∷
   rw 5 (q92 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 5 (q64 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw⁻ 5 (q62 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   rw 1 (q93 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q94 c4) ∷
   rw 1 (q39 c4) ∷
   rw 2 (q95 c4) ∷
   rw 1 (q40 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   rw 2 (q82 c4) ∷
   rw⁻ 1 (q83 c4) ∷
   rw 4 (q84 c4) ∷
   rw⁻ 8 (q85 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw 6 (q87 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   rw⁻ 3 (q89 c4) ∷
   rw⁻ 2 (q81 c4) ∷
   rw 3 (q90 c4) ∷
   rw 4 (q91 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 0 (q40 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q31 c4) ∷
   rw 3 (q96 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 7 (q9 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q10 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 4 (q31 c4) ∷
   rw 5 (q97 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q84 c4) ∷
   rw 7 (q98 c4) ∷
   rw 6 (q99 c4) ∷
   rw 5 (q100 c4) ∷
   rw 4 (q99 c4) ∷
   rw 3 (q101 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q84 c4) ∷
   rw 9 (q98 c4) ∷
   rw 8 (q99 c4) ∷
   rw 7 (q100 c4) ∷
   rw 6 (q99 c4) ∷
   rw 5 (q101 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 6 (q103 c4) ∷
   rw 7 (q104 c4) ∷
   rw 8 (q105 c4) ∷
   re 4 1 (Sb0-1-3-2 ∷ []) ∷
   re 6 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 3 (q106 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 4 1 (CS13 ∷ []) ∷
   re 6 1 (CS13⁻ ∷ []) ∷
   rw⁻ 3 (q107 c4) ∷
   rw 2 (q15 c4) ∷
   rw 2 (q16 c4) ∷
   rw 5 (q108 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 8 (q108 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 10 (q108 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw 6 (q19 c4) ∷
   rw 4 (q109 c4) ∷
   rw 3 (q108 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw⁻ 5 (q24 c4) ∷
   rw 6 (q108 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw 8 (q108 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 10 (q20 c4) ∷
   rw 4 (q19 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw⁻ 7 (q111 c4) ∷
   rw⁻ 5 (q112 c4) ∷
   rw 2 (q113 c4) ∷
   rw⁻ 4 (q16 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 1 (q114 c4) ∷
   rw⁻ 4 (q115 c4) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 7 (q79 c4) ∷
   rw⁻ 6 (q98 c4) ∷
   rw⁻ 5 (q74 c4) ∷
   rw⁻ 4 (q98 c4) ∷
   rw⁻ 3 (q34 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 2 (q115 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 6 1 (CS13 ∷ []) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q107 c4) ∷
   rw 4 (q15 c4) ∷
   rw 4 (q16 c4) ∷
   rw 7 (q108 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 9 (q24 c4) ∷
   rw 10 (q108 c4) ∷
   rw⁻ 11 (q23 c4) ∷
   rw 12 (q108 c4) ∷
   rw⁻ 13 (q21 c4) ∷
   rw⁻ 14 (q20 c4) ∷
   rw 8 (q19 c4) ∷
   rw 6 (q109 c4) ∷
   rw 5 (q108 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw 8 (q108 c4) ∷
   rw⁻ 9 (q23 c4) ∷
   rw 10 (q108 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 12 (q20 c4) ∷
   rw 6 (q19 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw⁻ 9 (q111 c4) ∷
   rw⁻ 7 (q112 c4) ∷
   rw 4 (q113 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 3 (q114 c4) ∷
   rw⁻ 6 (q116 c4) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw⁻ 9 (q77 c4) ∷
   rw⁻ 8 (q117 c4) ∷
   rw⁻ 7 (q72 c4) ∷
   rw⁻ 6 (q117 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 4 (q116 c4) ∷
   re 2 1 (Sb3-0-2-1 ∷ []) ∷
   re 4 1 (Sb⁻3-0-2-1 ∷ []) ∷
   re 0 5 (Sb3-0-41-2 ∷ []) ∷
   rw⁻ 0 (q1 c4) ∷ []) Eq.refl

private
  q118 : Ws → Eqn
  q118 c4 = sE 1803 (lem-F0-at01143043 c4)
  q119 : Ws → Eqn
  q119 c4 = sE 960 (lem-box-cP-at03243240 c4)
  q120 : Ws → Eqn
  q120 c4 = wpE 1025 c4
  q121 : Ws → Eqn
  q121 c4 = wpE 1026 c4
  q122 : Ws → Eqn
  q122 c4 = eqn (K0 ∷ CCZ134 ∷ []) (CCZ134 ∷ K0 ∷ []) (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q123 : Ws → Eqn
  q123 c4 = wlE 1220 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ134 ∷ CX02 ∷ []) (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = wlE 1221 (lit c4)
  q126 : Ws → Eqn
  q126 c4 = wpE 1003 c4
  q127 : Ws → Eqn
  q127 c4 = eqn (K0⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))
  q128 : Ws → Eqn
  q128 c4 = wlE 1206 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wpE 1007 c4
  q130 : Ws → Eqn
  q130 c4 = wlE 220 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = wpE 1006 c4
  q132 : Ws → Eqn
  q132 c4 = eqn (Toff302 ∷ CX14 ∷ []) (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4))
  q133 : Ws → Eqn
  q133 c4 = wpE 1005 c4
  q134 : Ws → Eqn
  q134 c4 = wlE 1190 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = wpE 1008 c4
  q136 : Ws → Eqn
  q136 c4 = wlE 1222 (lit c4)
  q137 : Ws → Eqn
  q137 c4 = wlE 1223 (lit c4)
  q138 : Ws → Eqn
  q138 c4 = wpE 261 c4
  q139 : Ws → Eqn
  q139 c4 = wlE 1224 (lit c4)
  q140 : Ws → Eqn
  q140 c4 = wpE 1027 c4
  q141 : Ws → Eqn
  q141 c4 = wlE 1225 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = wpE 701 c4
  q143 : Ws → Eqn
  q143 c4 = wpE 108 c4
  q144 : Ws → Eqn
  q144 c4 = eqn (CCZ034 ∷ CX12 ∷ []) (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4))
  q145 : Ws → Eqn
  q145 c4 = wpE 107 c4
  q146 : Ws → Eqn
  q146 c4 = wpE 106 c4
  q147 : Ws → Eqn
  q147 c4 = wpE 700 c4
  q148 : Ws → Eqn
  q148 c4 = wpE 716 c4
  q149 : Ws → Eqn
  q149 c4 = wlE 779 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wpE 41 c4
  q151 : Ws → Eqn
  q151 c4 = wlE 499 (lit c4)
  q152 : Ws → Eqn
  q152 c4 = wlE 778 (lit c4)
  q153 : Ws → Eqn
  q153 c4 = wlE 501 (lit c4)
  q154 : Ws → Eqn
  q154 c4 = wlE 780 (lit c4)
  q155 : Ws → Eqn
  q155 c4 = wpE 124 c4
  q156 : Ws → Eqn
  q156 c4 = wlE 1226 (lit c4)
  q157 : Ws → Eqn
  q157 c4 = wpE 2 c4
  q158 : Ws → Eqn
  q158 c4 = wpE 1028 c4
  q159 : Ws → Eqn
  q159 c4 = eqn (K0 ∷ Toff312 ∷ []) (Toff312 ∷ K0 ∷ []) (c₁ (K) (Toffᵗ))
  q160 : Ws → Eqn
  q160 c4 = eqn (K0⁻ ∷ Toff312 ∷ []) (Toff312 ∷ K0⁻ ∷ []) (c₁ (K • iI) (Toffᵗ))
  q161 : Ws → Eqn
  q161 c4 = wpE 1029 c4
  q162 : Ws → Eqn
  q162 c4 = wlE 497 (lit c4)
  q163 : Ws → Eqn
  q163 c4 = wlE 256 (lit c4)
  q164 : Ws → Eqn
  q164 c4 = wpE 129 c4
  q165 : Ws → Eqn
  q165 c4 = wlE 1227 (lit c4)
  q166 : Ws → Eqn
  q166 c4 = wlE 871 (lit c4)
  q167 : Ws → Eqn
  q167 c4 = wpE 1 c4
  q168 : Ws → Eqn
  q168 c4 = wlE 500 (lit c4)
  q169 : Ws → Eqn
  q169 c4 = wpE 120 c4
  q170 : Ws → Eqn
  q170 c4 = sE 1801 (lem-box-perm-3241-at0310243142 c4)
  q171 : Ws → Eqn
  q171 c4 = sE 1150 (lem-box2-at03243240 c4)
  q172 : Ws → Eqn
  q172 c4 = wpE 1030 c4
  q173 : Ws → Eqn
  q173 c4 = wpE 161 c4
  q174 : Ws → Eqn
  q174 c4 = wlE 263 (lit c4)

-- nf-comm-CSu-CS@0: 282 steps
lem-nf-comm-CSu-CSat0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-nf-comm-CSu-CSat0 c4 = derive (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  (rw 0 (q1 c4) ∷
   rw 1 (q118 c4) ∷
   re 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) ∷
   re 2 1 (CS02 ∷ []) ∷
   re 4 1 (CS02⁻ ∷ []) ∷
   re 5 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) ∷
   re 7 1 (CS01 ∷ []) ∷
   re 9 1 (CS01⁻ ∷ []) ∷
   rw 5 (q119 c4) ∷
   rw⁻ 8 (q120 c4) ∷
   rw⁻ 8 (q121 c4) ∷
   rw⁻ 7 (q122 c4) ∷
   rw 8 (q123 c4) ∷
   rw 9 (q124 c4) ∷
   rw 10 (q125 c4) ∷
   rw 11 (q124 c4) ∷
   rw 12 (q126 c4) ∷
   rw⁻ 13 (q127 c4) ∷
   rw 7 (q121 c4) ∷
   rw 8 (q128 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   rw 8 (q129 c4) ∷
   rw 10 (q130 c4) ∷
   rw⁻ 9 (q131 c4) ∷
   rw 10 (q132 c4) ∷
   rw⁻ 11 (q133 c4) ∷
   rw 12 (q132 c4) ∷
   rw⁻ 13 (q134 c4) ∷
   rw⁻ 9 (q130 c4) ∷
   rw 6 (q135 c4) ∷
   rw⁻ 6 (q121 c4) ∷
   rw⁻ 5 (q122 c4) ∷
   rw 6 (q123 c4) ∷
   rw 7 (q124 c4) ∷
   rw 8 (q125 c4) ∷
   rw 9 (q124 c4) ∷
   rw 10 (q126 c4) ∷
   rw⁻ 11 (q127 c4) ∷
   rw 5 (q121 c4) ∷
   rw⁻ 6 (q136 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   rw 7 (q119 c4) ∷
   rw⁻ 10 (q137 c4) ∷
   rw 9 (q138 c4) ∷
   rw⁻ 8 (q137 c4) ∷
   rw 7 (q138 c4) ∷
   rw⁻ 8 (q119 c4) ∷
   rw 8 (q119 c4) ∷
   rw⁻ 11 (q120 c4) ∷
   rw⁻ 11 (q121 c4) ∷
   rw⁻ 10 (q122 c4) ∷
   rw 11 (q123 c4) ∷
   rw 12 (q124 c4) ∷
   rw 13 (q125 c4) ∷
   rw 14 (q124 c4) ∷
   rw 15 (q126 c4) ∷
   rw⁻ 16 (q127 c4) ∷
   rw 10 (q121 c4) ∷
   rw 11 (q128 c4) ∷
   rw⁻ 9 (q120 c4) ∷
   rw 11 (q129 c4) ∷
   rw 13 (q130 c4) ∷
   rw⁻ 12 (q131 c4) ∷
   rw 13 (q132 c4) ∷
   rw⁻ 14 (q133 c4) ∷
   rw 15 (q132 c4) ∷
   rw⁻ 16 (q134 c4) ∷
   rw⁻ 12 (q130 c4) ∷
   rw 9 (q135 c4) ∷
   rw⁻ 9 (q121 c4) ∷
   rw⁻ 8 (q122 c4) ∷
   rw 9 (q123 c4) ∷
   rw 10 (q124 c4) ∷
   rw 11 (q125 c4) ∷
   rw 12 (q124 c4) ∷
   rw 13 (q126 c4) ∷
   rw⁻ 14 (q127 c4) ∷
   rw 8 (q121 c4) ∷
   rw⁻ 9 (q136 c4) ∷
   rw⁻ 10 (q119 c4) ∷
   rw 10 (q119 c4) ∷
   rw⁻ 13 (q139 c4) ∷
   rw 12 (q140 c4) ∷
   rw⁻ 11 (q139 c4) ∷
   rw 10 (q140 c4) ∷
   rw⁻ 11 (q119 c4) ∷
   rw 0 (q40 c4) ∷
   rw⁻ 3 (q141 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 2 (q142 c4) ∷
   rw 3 (q143 c4) ∷
   rw 4 (q144 c4) ∷
   rw 5 (q145 c4) ∷
   rw 6 (q144 c4) ∷
   rw 7 (q146 c4) ∷
   rw 8 (q147 c4) ∷
   rw 2 (q19 c4) ∷
   rw 3 (q148 c4) ∷
   rw⁻ 1 (q141 c4) ∷
   rw 3 (q149 c4) ∷
   rw 5 (q150 c4) ∷
   rw⁻ 4 (q151 c4) ∷
   rw 5 (q66 c4) ∷
   rw⁻ 6 (q152 c4) ∷
   rw 7 (q66 c4) ∷
   rw⁻ 8 (q153 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 1 (q154 c4) ∷
   rw⁻ 1 (q19 c4) ∷
   rw 0 (q142 c4) ∷
   rw 1 (q143 c4) ∷
   rw 2 (q144 c4) ∷
   rw 3 (q145 c4) ∷
   rw 4 (q144 c4) ∷
   rw 5 (q146 c4) ∷
   rw 6 (q147 c4) ∷
   rw 0 (q19 c4) ∷
   rw⁻ 1 (q155 c4) ∷
   rw⁻ 2 (q40 c4) ∷
   rw 2 (q40 c4) ∷
   rw⁻ 5 (q68 c4) ∷
   rw 4 (q85 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw 2 (q85 c4) ∷
   rw⁻ 3 (q40 c4) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 6 (q141 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 5 (q142 c4) ∷
   rw 6 (q143 c4) ∷
   rw 7 (q144 c4) ∷
   rw 8 (q145 c4) ∷
   rw 9 (q144 c4) ∷
   rw 10 (q146 c4) ∷
   rw 11 (q147 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q148 c4) ∷
   rw⁻ 4 (q141 c4) ∷
   rw 6 (q149 c4) ∷
   rw 8 (q150 c4) ∷
   rw⁻ 7 (q151 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 9 (q152 c4) ∷
   rw 10 (q66 c4) ∷
   rw⁻ 11 (q153 c4) ∷
   rw⁻ 7 (q150 c4) ∷
   rw 4 (q154 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q142 c4) ∷
   rw 4 (q143 c4) ∷
   rw 5 (q144 c4) ∷
   rw 6 (q145 c4) ∷
   rw 7 (q144 c4) ∷
   rw 8 (q146 c4) ∷
   rw 9 (q147 c4) ∷
   rw 3 (q19 c4) ∷
   rw⁻ 4 (q155 c4) ∷
   rw⁻ 5 (q40 c4) ∷
   rw 5 (q40 c4) ∷
   rw⁻ 8 (q156 c4) ∷
   rw 7 (q157 c4) ∷
   rw⁻ 6 (q156 c4) ∷
   rw 5 (q157 c4) ∷
   rw⁻ 6 (q40 c4) ∷
   rw 6 (q40 c4) ∷
   rw⁻ 10 (q158 c4) ∷
   rw⁻ 9 (q159 c4) ∷
   rw⁻ 10 (q65 c4) ∷
   rw 11 (q66 c4) ∷
   rw⁻ 12 (q67 c4) ∷
   rw 13 (q66 c4) ∷
   rw⁻ 14 (q68 c4) ∷
   rw⁻ 15 (q160 c4) ∷
   rw 9 (q158 c4) ∷
   rw 8 (q161 c4) ∷
   rw⁻ 8 (q158 c4) ∷
   rw⁻ 7 (q159 c4) ∷
   rw⁻ 8 (q65 c4) ∷
   rw 9 (q66 c4) ∷
   rw⁻ 10 (q67 c4) ∷
   rw 11 (q66 c4) ∷
   rw⁻ 12 (q68 c4) ∷
   rw⁻ 13 (q160 c4) ∷
   rw 7 (q158 c4) ∷
   rw⁻ 8 (q162 c4) ∷
   rw 6 (q161 c4) ∷
   rw 9 (q163 c4) ∷
   rw 8 (q143 c4) ∷
   rw 9 (q144 c4) ∷
   rw 10 (q145 c4) ∷
   rw 11 (q144 c4) ∷
   rw 12 (q146 c4) ∷
   rw⁻ 8 (q163 c4) ∷
   rw 9 (q164 c4) ∷
   rw⁻ 7 (q165 c4) ∷
   rw⁻ 8 (q40 c4) ∷
   rw 8 (q40 c4) ∷
   rw⁻ 11 (q166 c4) ∷
   rw 11 (q163 c4) ∷
   rw 10 (q143 c4) ∷
   rw 11 (q144 c4) ∷
   rw 12 (q145 c4) ∷
   rw 13 (q144 c4) ∷
   rw 14 (q146 c4) ∷
   rw⁻ 10 (q163 c4) ∷
   rw⁻ 9 (q166 c4) ∷
   rw 9 (q163 c4) ∷
   rw 8 (q143 c4) ∷
   rw 9 (q144 c4) ∷
   rw 10 (q145 c4) ∷
   rw 11 (q144 c4) ∷
   rw 12 (q146 c4) ∷
   rw⁻ 8 (q163 c4) ∷
   rw⁻ 9 (q40 c4) ∷
   rw 9 (q40 c4) ∷
   rw⁻ 12 (q153 c4) ∷
   rw 11 (q167 c4) ∷
   rw⁻ 10 (q153 c4) ∷
   rw 9 (q167 c4) ∷
   rw⁻ 10 (q40 c4) ∷
   rw 10 (q40 c4) ∷
   rw⁻ 14 (q158 c4) ∷
   rw⁻ 13 (q159 c4) ∷
   rw⁻ 14 (q65 c4) ∷
   rw 15 (q66 c4) ∷
   rw⁻ 16 (q67 c4) ∷
   rw 17 (q66 c4) ∷
   rw⁻ 18 (q68 c4) ∷
   rw⁻ 19 (q160 c4) ∷
   rw 13 (q158 c4) ∷
   rw 12 (q161 c4) ∷
   rw⁻ 12 (q158 c4) ∷
   rw⁻ 11 (q159 c4) ∷
   rw⁻ 12 (q65 c4) ∷
   rw 13 (q66 c4) ∷
   rw⁻ 14 (q67 c4) ∷
   rw 15 (q66 c4) ∷
   rw⁻ 16 (q68 c4) ∷
   rw⁻ 17 (q160 c4) ∷
   rw 11 (q158 c4) ∷
   rw⁻ 12 (q162 c4) ∷
   rw 10 (q161 c4) ∷
   rw 13 (q163 c4) ∷
   rw 12 (q143 c4) ∷
   rw 13 (q144 c4) ∷
   rw 14 (q145 c4) ∷
   rw 15 (q144 c4) ∷
   rw 16 (q146 c4) ∷
   rw⁻ 12 (q163 c4) ∷
   rw 13 (q164 c4) ∷
   rw⁻ 11 (q165 c4) ∷
   rw⁻ 12 (q40 c4) ∷
   rw 12 (q40 c4) ∷
   rw⁻ 15 (q166 c4) ∷
   rw 15 (q163 c4) ∷
   rw 14 (q143 c4) ∷
   rw 15 (q144 c4) ∷
   rw 16 (q145 c4) ∷
   rw 17 (q144 c4) ∷
   rw 18 (q146 c4) ∷
   rw⁻ 14 (q163 c4) ∷
   rw⁻ 13 (q166 c4) ∷
   rw 13 (q163 c4) ∷
   rw 12 (q143 c4) ∷
   rw 13 (q144 c4) ∷
   rw 14 (q145 c4) ∷
   rw 15 (q144 c4) ∷
   rw 16 (q146 c4) ∷
   rw⁻ 12 (q163 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw 13 (q40 c4) ∷
   rw⁻ 16 (q168 c4) ∷
   rw 15 (q169 c4) ∷
   rw⁻ 14 (q168 c4) ∷
   rw 13 (q169 c4) ∷
   rw⁻ 14 (q40 c4) ∷
   rw 14 (q170 c4) ∷
   rw 14 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   rw 3 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw 7 (q174 c4) ∷ []) Eq.refl
