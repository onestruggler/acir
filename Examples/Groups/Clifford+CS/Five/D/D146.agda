{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD146 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D146 (Sᴰ : SD146) where

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
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 0 Sᴰ
  lem-comm-CZ13-CCZ024 : Ws → St 67
  lem-comm-CZ13-CCZ024 = pickᴰ 1 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 2 Sᴰ
  lem-comm-CCZ024-CX31 : Ws → St 1058
  lem-comm-CCZ024-CX31 = pickᴰ 3 Sᴰ
  lem-comm-CSd02-TOFF413 : Ws → St 376
  lem-comm-CSd02-TOFF413 = pickᴰ 4 Sᴰ
  lem-comm-TOFF213-CX40 : Ws → St 1174
  lem-comm-TOFF213-CX40 = pickᴰ 5 Sᴰ
  lem-comm-CS02-TOFF413 : Ws → St 381
  lem-comm-CS02-TOFF413 = pickᴰ 6 Sᴰ
  lem-box-cP-at0214203143 : Ws → St 1112
  lem-box-cP-at0214203143 = pickᴰ 7 Sᴰ
  lem-box-cP-at04122041 : Ws → St 1192
  lem-box-cP-at04122041 = pickᴰ 8 Sᴰ
  lem-CSdu-box-3-at0214203143 : Ws → St 1824
  lem-CSdu-box-3-at0214203143 = pickᴰ 9 Sᴰ
  lem-CSdu-box-3-at04122041 : Ws → St 1825
  lem-CSdu-box-3-at04122041 = pickᴰ 10 Sᴰ
  lem-CSu-box-3-at0214203143 : Ws → St 1826
  lem-CSu-box-3-at0214203143 = pickᴰ 11 Sᴰ
  lem-CSu-box-3-at04122041 : Ws → St 1827
  lem-CSu-box-3-at04122041 = pickᴰ 12 Sᴰ
  lem-box-perm-1342-at0214203143 : Ws → St 1829
  lem-box-perm-1342-at0214203143 = pickᴰ 13 Sᴰ
  lem-box-perm-1423-at02142140 : Ws → St 1830
  lem-box-perm-1423-at02142140 = pickᴰ 14 Sᴰ
  lem-box-perm-1432-at04122041 : Ws → St 1874
  lem-box-perm-1432-at04122041 = pickᴰ 15 Sᴰ
  lem-box-perm-1432-at04122140 : Ws → St 1875
  lem-box-perm-1432-at04122140 = pickᴰ 16 Sᴰ
  lem-box-box-1-at02142140 : Ws → St 1876
  lem-box-box-1-at02142140 = pickᴰ 17 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1192 (lem-box-cP-at04122041 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 1284 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 1498 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ Toff413 ∷ []) (Toff413 ∷ X0 ∷ []) (c₁ (X) (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑))
  q5 : Ws → Eqn
  q5 c4 = wlE 242 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 81 c4
  q7 : Ws → Eqn
  q7 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 91 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 92 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 1285 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 1433 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 1499 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1825 (lem-CSdu-box-3-at04122041 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1625 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 33 c4
  q16 : Ws → Eqn
  q16 c4 = wpE 39 c4
  q17 : Ws → Eqn
  q17 c4 = wpE 32 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 21 c4
  q19 : Ws → Eqn
  q19 c4 = wpE 37 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 1484 c4
  q21 : Ws → Eqn
  q21 c4 = wpE 1485 c4
  q22 : Ws → Eqn
  q22 c4 = wlE 155 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wpE 1398 c4
  q24 : Ws → Eqn
  q24 c4 = wlE 1588 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = sE 376 (lem-comm-CSd02-TOFF413 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 381 (lem-comm-CS02-TOFF413 c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 1425 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 1426 c4
  q29 : Ws → Eqn
  q29 c4 = sE 1827 (lem-CSu-box-3-at04122041 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1829 (lem-box-perm-1342-at0214203143 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1874 (lem-box-perm-1432-at04122041 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1876 (lem-box-box-1-at02142140 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1875 (lem-box-perm-1432-at04122140 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1830 (lem-box-perm-1423-at02142140 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1112 (lem-box-cP-at0214203143 c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 965 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = sE 67 (lem-comm-CZ13-CCZ024 c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 971 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 1718 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ012 ∷ CS34 ∷ []) (CS34 ∷ CCZ012 ∷ []) (c₃ (CCZ) (CS))
  q41 : Ws → Eqn
  q41 c4 = wlE 492 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 1719 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 491 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 1720 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wlE 181 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 1265 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 341 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 1505 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 1486 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 976 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wlE 1721 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = sE 1058 (lem-comm-CCZ024-CX31 c4)
  q53 : Ws → Eqn
  q53 c4 = wpE 789 c4
  q54 : Ws → Eqn
  q54 c4 = wlE 1545 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = wpE 89 c4
  q56 : Ws → Eqn
  q56 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 88 c4
  q58 : Ws → Eqn
  q58 c4 = wpE 1467 c4
  q59 : Ws → Eqn
  q59 c4 = wlE 809 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wpE 320 c4
  q61 : Ws → Eqn
  q61 c4 = wlE 196 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = sE 1174 (lem-comm-TOFF213-CX40 c4)
  q63 : Ws → Eqn
  q63 c4 = wlE 191 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wlE 808 (lit c4)
  q65 : Ws → Eqn
  q65 c4 = wlE 1338 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 978 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = wlE 1621 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 1487 c4
  q69 : Ws → Eqn
  q69 c4 = wlE 1510 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 1511 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 1631 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wlE 1384 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = wlE 1629 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = sE 1826 (lem-CSu-box-3-at0214203143 c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 1513 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 1630 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 1722 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = wlE 1628 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = sE 1824 (lem-CSdu-box-3-at0214203143 c4)

-- F4-CS0-CS2 @0440: 284 steps
lem-F4-CS0-CS2-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-CS2-at0440 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw 5 (q13 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 5 (q14 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw 11 (q7 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 9 (q20 c4) ∷
   rw 8 (q22 c4) ∷
   rw 12 (q23 c4) ∷
   rw 11 (q24 c4) ∷
   rw 10 (q25 c4) ∷
   rw 9 (q24 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 7 (q27 c4) ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 3 1 (CS34 ∷ []) ∷
   rw 3 (q29 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q7 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw⁻ 2 (q19 c4) ∷
   rw 3 (q14 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw⁻ 11 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw 9 (q7 c4) ∷
   rw⁻ 8 (q17 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q18 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 7 (q20 c4) ∷
   rw 6 (q22 c4) ∷
   rw 10 (q23 c4) ∷
   rw 9 (q24 c4) ∷
   rw 8 (q25 c4) ∷
   rw 7 (q24 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw 5 (q27 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q30 c4) ∷
   rw 2 (q31 c4) ∷
   rw 1 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw⁻ 6 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q35 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q36 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw⁻ 7 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 4 (q37 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 5 (q41 c4) ∷
   rw⁻ 6 (q42 c4) ∷
   rw 8 (q43 c4) ∷
   rw 9 (q44 c4) ∷
   rw 10 (q45 c4) ∷
   rw 3 (q46 c4) ∷
   rw 4 (q40 c4) ∷
   rw 5 (q47 c4) ∷
   re 4 1 (Sb2-4-3-1 ∷ []) ∷
   re 6 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 2 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 3 (q48 c4) ∷
   re 2 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 4 1 (CS34 ∷ []) ∷
   re 6 1 (CS34⁻ ∷ []) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 2 (q35 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw 4 (q52 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw 7 (q55 c4) ∷
   rw 8 (q18 c4) ∷
   rw 9 (q56 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q56 c4) ∷
   rw 12 (q16 c4) ∷
   rw 13 (q57 c4) ∷
   rw 7 (q54 c4) ∷
   rw 8 (q58 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   rw 7 (q62 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 9 (q62 c4) ∷
   rw⁻ 10 (q64 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw 11 (q60 c4) ∷
   rw⁻ 10 (q61 c4) ∷
   rw 11 (q62 c4) ∷
   rw⁻ 12 (q63 c4) ∷
   rw 13 (q62 c4) ∷
   rw⁻ 14 (q64 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw 3 (q66 c4) ∷
   rw 5 (q67 c4) ∷
   rw 3 (q68 c4) ∷
   rw 2 (q52 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q18 c4) ∷
   rw 5 (q56 c4) ∷
   rw 6 (q17 c4) ∷
   rw 7 (q56 c4) ∷
   rw 8 (q16 c4) ∷
   rw 9 (q57 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw⁻ 7 (q71 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw⁻ 5 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 5 (q48 c4) ∷
   re 4 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 6 1 (CS34 ∷ []) ∷
   re 8 1 (CS34⁻ ∷ []) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 7 (q50 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw 6 (q52 c4) ∷
   rw 7 (q53 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw 9 (q55 c4) ∷
   rw 10 (q18 c4) ∷
   rw 11 (q56 c4) ∷
   rw 12 (q17 c4) ∷
   rw 13 (q56 c4) ∷
   rw 14 (q16 c4) ∷
   rw 15 (q57 c4) ∷
   rw 9 (q54 c4) ∷
   rw 10 (q58 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 7 (q59 c4) ∷
   rw 9 (q60 c4) ∷
   rw⁻ 8 (q61 c4) ∷
   rw 9 (q62 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw 11 (q62 c4) ∷
   rw⁻ 12 (q64 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   rw⁻ 9 (q51 c4) ∷
   rw⁻ 11 (q65 c4) ∷
   rw 13 (q60 c4) ∷
   rw⁻ 12 (q61 c4) ∷
   rw 13 (q62 c4) ∷
   rw⁻ 14 (q63 c4) ∷
   rw 15 (q62 c4) ∷
   rw⁻ 16 (q64 c4) ∷
   rw⁻ 12 (q60 c4) ∷
   rw 5 (q66 c4) ∷
   rw 7 (q67 c4) ∷
   rw 5 (q68 c4) ∷
   rw 4 (q52 c4) ∷
   rw⁻ 6 (q54 c4) ∷
   rw 5 (q55 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q56 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q56 c4) ∷
   rw 10 (q16 c4) ∷
   rw 11 (q57 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   re 8 1 (Sb2-4-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 6 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   re 5 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 7 1 (CS34 ∷ []) ∷
   re 9 1 (CS34⁻ ∷ []) ∷
   rw⁻ 9 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   re 8 1 (Sb2-4-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 6 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 4 (q75 c4) ∷
   re 2 1 (Sb4-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 0 5 (Sb4-2-03-1 ∷ []) ∷ []) Eq.refl
