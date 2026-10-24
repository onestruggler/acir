{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD101 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D101 (Sᴰ : SD101) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CS13-CCZ024 : Ws → St 958
  lem-comm-CS13-CCZ024 = pickᴰ 0 Sᴰ
  lem-comm-CSd13-CCZ024 : Ws → St 960
  lem-comm-CSd13-CCZ024 = pickᴰ 1 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 2 Sᴰ
  lem-comm-CZ13-CCZ024 : Ws → St 67
  lem-comm-CZ13-CCZ024 = pickᴰ 3 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 4 Sᴰ
  lem-comm-CCZ034-CS12 : Ws → St 1705
  lem-comm-CCZ034-CS12 = pickᴰ 5 Sᴰ
  lem-comm-CX40-TOFF213 : Ws → St 1173
  lem-comm-CX40-TOFF213 = pickᴰ 6 Sᴰ
  lem-comm-TOFF413-CSd02 : Ws → St 380
  lem-comm-TOFF413-CSd02 = pickᴰ 7 Sᴰ
  lem-comm-TOFF413-CS02 : Ws → St 1455
  lem-comm-TOFF413-CS02 = pickᴰ 8 Sᴰ
  lem-box-cP-at0214203143 : Ws → St 1112
  lem-box-cP-at0214203143 = pickᴰ 9 Sᴰ
  lem-box-cP-at04122041 : Ws → St 1192
  lem-box-cP-at04122041 = pickᴰ 10 Sᴰ
  lem-CSdu-box-3-at0214203143 : Ws → St 1824
  lem-CSdu-box-3-at0214203143 = pickᴰ 11 Sᴰ
  lem-CSdu-box-3-at04122041 : Ws → St 1825
  lem-CSdu-box-3-at04122041 = pickᴰ 12 Sᴰ
  lem-CSu-box-3-at0214203143 : Ws → St 1826
  lem-CSu-box-3-at0214203143 = pickᴰ 13 Sᴰ
  lem-CSu-box-3-at04122041 : Ws → St 1827
  lem-CSu-box-3-at04122041 = pickᴰ 14 Sᴰ
  lem-CXAu-S-at0410213243 : Ws → St 1828
  lem-CXAu-S-at0410213243 = pickᴰ 15 Sᴰ
  lem-box-perm-1342-at0214203143 : Ws → St 1829
  lem-box-perm-1342-at0214203143 = pickᴰ 16 Sᴰ
  lem-box-perm-1423-at02142140 : Ws → St 1830
  lem-box-perm-1423-at02142140 = pickᴰ 17 Sᴰ
  lem-box-perm-2431-at0440 : Ws → St 1831
  lem-box-perm-2431-at0440 = pickᴰ 18 Sᴰ
  lem-box-perm-4132-at04122041 : Ws → St 1679
  lem-box-perm-4132-at04122041 = pickᴰ 19 Sᴰ
  lem-CXuA-S-at0410213243 : Ws → St 1832
  lem-CXuA-S-at0410213243 = pickᴰ 20 Sᴰ
  lem-XCKX-box-2-at0214203143 : Ws → St 1833
  lem-XCKX-box-2-at0214203143 = pickᴰ 21 Sᴰ
  lem-box-box-2-at0440 : Ws → St 1834
  lem-box-box-2-at0440 = pickᴰ 22 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1112 (lem-box-cP-at0214203143 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 1284 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 1432 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (ℓ "与亦") (ℓ "亦与") (c₁ (X) (K ↑ • CCZ • K ↑ • iI))
  q5 : Ws → Eqn
  q5 c4 = wlE 617 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 36 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 285 c4
  q8 : Ws → Eqn
  q8 c4 = sE 960 (lem-comm-CSd13-CCZ024 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 958 (lem-comm-CS13-CCZ024 c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 1285 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 1433 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 954 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1824 (lem-CSdu-box-3-at0214203143 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1545 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 88 c4
  q16 : Ws → Eqn
  q16 c4 = wpE 39 c4
  q17 : Ws → Eqn
  q17 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 32 c4
  q19 : Ws → Eqn
  q19 c4 = wpE 21 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 89 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 1620 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 1192 c4
  q23 : Ws → Eqn
  q23 c4 = wpE 320 c4
  q24 : Ws → Eqn
  q24 c4 = wlE 808 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1173 (lem-comm-CX40-TOFF213 c4)
  q26 : Ws → Eqn
  q26 c4 = wlE 191 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 196 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 1338 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wlE 1621 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1826 (lem-CSu-box-3-at0214203143 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1679 (lem-box-perm-4132-at04122041 c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1829 (lem-box-perm-1342-at0214203143 c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1834 (lem-box-box-2-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1830 (lem-box-perm-1423-at02142140 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1831 (lem-box-perm-2431-at0440 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1192 (lem-box-cP-at04122041 c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 1616 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = sE 67 (lem-comm-CZ13-CCZ024 c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 1622 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 1419 c4
  q41 : Ws → Eqn
  q41 c4 = sE 1705 (lem-comm-CCZ034-CS12 c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 393 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wpE 1420 c4
  q44 : Ws → Eqn
  q44 c4 = wlE 392 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 1421 c4
  q46 : Ws → Eqn
  q46 c4 = wlE 321 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 1422 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 7 c4
  q49 : Ws → Eqn
  q49 c4 = wlE 1434 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wlE 1623 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wlE 1624 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1423 c4
  q53 : Ws → Eqn
  q53 c4 = wpE 729 c4
  q54 : Ws → Eqn
  q54 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q55 : Ws → Eqn
  q55 c4 = wpE 1424 c4
  q56 : Ws → Eqn
  q56 c4 = wlE 1625 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 37 c4
  q58 : Ws → Eqn
  q58 c4 = wpE 33 c4
  q59 : Ws → Eqn
  q59 c4 = wlE 1626 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wlE 155 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = sE 1455 (lem-comm-TOFF413-CS02 c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 1588 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = sE 380 (lem-comm-TOFF413-CSd02 c4)
  q64 : Ws → Eqn
  q64 c4 = wpE 1398 c4
  q65 : Ws → Eqn
  q65 c4 = wpE 1425 c4
  q66 : Ws → Eqn
  q66 c4 = wpE 728 c4
  q67 : Ws → Eqn
  q67 c4 = wpE 1426 c4
  q68 : Ws → Eqn
  q68 c4 = wlE 1627 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wlE 1436 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 1437 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = wlE 1628 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wpE 1427 c4
  q73 : Ws → Eqn
  q73 c4 = wlE 1629 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = sE 1827 (lem-CSu-box-3-at04122041 c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 1438 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 1630 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wpE 1428 c4
  q78 : Ws → Eqn
  q78 c4 = wlE 1631 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = sE 1825 (lem-CSdu-box-3-at04122041 c4)

-- F4-CS2-CS0 @0440: 284 steps
lem-F4-CS2-CS0-at0440 : Ws → ⟪ (ℓ "与俵与俊") ⟫ʷ ≈ ⟪ (ℓ "俊与俵与") ⟫ʷ
lem-F4-CS2-CS0-at0440 c4 = derive (ℓ "与俵与俊") (ℓ "俊与俵与")
  (re 3 1 (ℓ "佔亓俈亓俉") ∷
   re 5 1 (ℓ "乹") ∷
   re 7 1 (ℓ "乺") ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 5 (q10 c4) ∷
   rw⁻ 4 (q2 c4) ∷
   rw 5 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "么") ∷
   rw 5 (q13 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 8 (q17 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 6 (q17 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q14 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw 10 (q17 c4) ∷
   rw⁻ 9 (q18 c4) ∷
   rw 8 (q17 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw 7 (q14 c4) ∷
   rw 9 (q23 c4) ∷
   rw 13 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 11 (q26 c4) ∷
   rw 10 (q25 c4) ∷
   rw 9 (q27 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw 8 (q28 c4) ∷
   rw 7 (q21 c4) ∷
   rw 8 (q29 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 3 1 (ℓ "乇") ∷
   rw 3 (q30 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw 6 (q17 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q14 c4) ∷
   rw 3 (q21 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw⁻ 4 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw 8 (q17 c4) ∷
   rw⁻ 7 (q18 c4) ∷
   rw 6 (q17 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw⁻ 4 (q20 c4) ∷
   rw 5 (q14 c4) ∷
   rw 7 (q23 c4) ∷
   rw 11 (q24 c4) ∷
   rw 10 (q25 c4) ∷
   rw 9 (q26 c4) ∷
   rw 8 (q25 c4) ∷
   rw 7 (q27 c4) ∷
   rw⁻ 8 (q23 c4) ∷
   rw 6 (q28 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q29 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q32 c4) ∷
   rw 1 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw 2 (q35 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw⁻ 3 (q10 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 3 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q36 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q37 c4) ∷
   rw 5 (q5 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw⁻ 8 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw⁻ 6 (q7 c4) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 6 (q5 c4) ∷
   rw 4 (q38 c4) ∷
   rw 5 (q39 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q40 c4) ∷
   rw 6 (q41 c4) ∷
   rw 5 (q42 c4) ∷
   rw 6 (q43 c4) ∷
   rw 8 (q44 c4) ∷
   rw 9 (q45 c4) ∷
   rw 10 (q46 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   re 4 1 (ℓ "俳") ∷
   re 6 1 (ℓ "俴") ∷
   re 2 5 (ℓ "俵") ∷
   rw⁻ 3 (q49 c4) ∷
   re 2 1 (ℓ "侗互俳互俴") ∷
   re 4 1 (ℓ "乇") ∷
   re 6 1 (ℓ "么") ∷
   rw⁻ 3 (q50 c4) ∷
   rw 2 (q36 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw⁻ 7 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw 6 (q54 c4) ∷
   rw 7 (q55 c4) ∷
   rw⁻ 10 (q56 c4) ∷
   rw 9 (q57 c4) ∷
   rw 10 (q19 c4) ∷
   rw 11 (q54 c4) ∷
   rw 12 (q18 c4) ∷
   rw 13 (q54 c4) ∷
   rw 14 (q16 c4) ∷
   rw 15 (q58 c4) ∷
   rw 9 (q56 c4) ∷
   rw⁻ 3 (q59 c4) ∷
   rw 5 (q60 c4) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 5 (q62 c4) ∷
   rw 6 (q63 c4) ∷
   rw⁻ 7 (q62 c4) ∷
   rw⁻ 8 (q64 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw⁻ 7 (q65 c4) ∷
   rw 9 (q60 c4) ∷
   rw 8 (q61 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   rw 10 (q63 c4) ∷
   rw⁻ 11 (q62 c4) ∷
   rw⁻ 12 (q64 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   rw⁻ 9 (q52 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw 3 (q68 c4) ∷
   rw 2 (q54 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw 3 (q57 c4) ∷
   rw 4 (q19 c4) ∷
   rw 5 (q54 c4) ∷
   rw 6 (q18 c4) ∷
   rw 7 (q54 c4) ∷
   rw 8 (q16 c4) ∷
   rw 9 (q58 c4) ∷
   rw 3 (q56 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   re 6 1 (ℓ "俳") ∷
   re 8 1 (ℓ "俴") ∷
   re 4 5 (ℓ "俵") ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 3 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 7 (q71 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 6 1 (ℓ "俳") ∷
   re 8 1 (ℓ "俴") ∷
   re 4 5 (ℓ "俵") ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   re 4 1 (ℓ "侗互俳互俴") ∷
   re 6 1 (ℓ "乇") ∷
   re 8 1 (ℓ "么") ∷
   rw⁻ 5 (q50 c4) ∷
   rw 4 (q36 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 9 (q52 c4) ∷
   rw 6 (q53 c4) ∷
   rw 8 (q54 c4) ∷
   rw 9 (q55 c4) ∷
   rw⁻ 12 (q56 c4) ∷
   rw 11 (q57 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q54 c4) ∷
   rw 14 (q18 c4) ∷
   rw 15 (q54 c4) ∷
   rw 16 (q16 c4) ∷
   rw 17 (q58 c4) ∷
   rw 11 (q56 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 7 (q60 c4) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 7 (q62 c4) ∷
   rw 8 (q63 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   rw⁻ 10 (q64 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw⁻ 7 (q51 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw 11 (q60 c4) ∷
   rw 10 (q61 c4) ∷
   rw⁻ 11 (q62 c4) ∷
   rw 12 (q63 c4) ∷
   rw⁻ 13 (q62 c4) ∷
   rw⁻ 14 (q64 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw 5 (q68 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw 5 (q57 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q54 c4) ∷
   rw 8 (q18 c4) ∷
   rw 9 (q54 c4) ∷
   rw 10 (q16 c4) ∷
   rw 11 (q58 c4) ∷
   rw 5 (q56 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   re 8 1 (ℓ "俳") ∷
   re 10 1 (ℓ "俴") ∷
   re 6 5 (ℓ "俵") ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   re 5 1 (ℓ "侗互俳互俴") ∷
   re 7 1 (ℓ "乇") ∷
   re 9 1 (ℓ "么") ∷
   rw 9 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw 7 (q78 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   re 8 1 (ℓ "俳") ∷
   re 10 1 (ℓ "俴") ∷
   re 6 5 (ℓ "俵") ∷
   rw⁻ 4 (q75 c4) ∷
   re 2 1 (ℓ "俈") ∷
   re 4 1 (ℓ "俉") ∷
   re 0 5 (ℓ "俊") ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = sE 1833 (lem-XCKX-box-2-at0214203143 c4)
  q81 : Ws → Eqn
  q81 c4 = wlE 1634 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wpE 1431 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 1432 c4

-- F4-K2-CS0 @0440: 11 steps
lem-F4-K2-CS0-at0440 : Ws → ⟪ (ℓ "与临与俊") ⟫ʷ ≈ ⟪ (ℓ "俊与临与") ⟫ʷ
lem-F4-K2-CS0-at0440 c4 = derive (ℓ "与临与俊") (ℓ "俊与临与")
  (re 3 1 (ℓ "佔亓俈亓俉") ∷
   re 5 1 (ℓ "乹") ∷
   re 7 1 (ℓ "乺") ∷
   rw 0 (q80 c4) ∷
   rw⁻ 1 (q81 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   re 2 1 (ℓ "俈") ∷
   re 4 1 (ℓ "俉") ∷
   re 0 5 (ℓ "俊") ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = wlE 258 (lit c4)
  q85 : Ws → Eqn
  q85 c4 = sE 1832 (lem-CXuA-S-at0410213243 c4)
  q86 : Ws → Eqn
  q86 c4 = sE 1828 (lem-CXAu-S-at0410213243 c4)

-- SW-S @0410213243: 5 steps
lem-SW-S-at0410213243 : Ws → ⟪ (ℓ "乥俊") ⟫ʷ ≈ ⟪ (ℓ "俊乥") ⟫ʷ
lem-SW-S-at0410213243 c4 = derive (ℓ "乥俊") (ℓ "俊乥")
  (rw⁻ 0 (q84 c4) ∷
   rw 2 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q84 c4) ∷ []) Eq.refl
