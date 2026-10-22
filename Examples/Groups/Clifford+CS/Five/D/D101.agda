{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD101 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D101 (Sᴰ : SD101) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-CCZ034-CS12)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX40-TOFF213 ; lem-comm-TOFF413-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-TOFF413-CS02)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-cP-at0214203143 : Ws → St 948
  lem-box-cP-at0214203143 = pickᴰ 0 Sᴰ
  lem-box-cP-at04122041 : Ws → St 1019
  lem-box-cP-at04122041 = pickᴰ 1 Sᴰ
  lem-CSdu-box-3-at0214203143 : Ws → St 1588
  lem-CSdu-box-3-at0214203143 = pickᴰ 2 Sᴰ
  lem-CSdu-box-3-at04122041 : Ws → St 1589
  lem-CSdu-box-3-at04122041 = pickᴰ 3 Sᴰ
  lem-CSu-box-3-at0214203143 : Ws → St 1590
  lem-CSu-box-3-at0214203143 = pickᴰ 4 Sᴰ
  lem-CSu-box-3-at04122041 : Ws → St 1591
  lem-CSu-box-3-at04122041 = pickᴰ 5 Sᴰ
  lem-CXAu-S-at0410213243 : Ws → St 1592
  lem-CXAu-S-at0410213243 = pickᴰ 6 Sᴰ
  lem-box-perm-1342-at0214203143 : Ws → St 1593
  lem-box-perm-1342-at0214203143 = pickᴰ 7 Sᴰ
  lem-box-perm-1423-at02142140 : Ws → St 1594
  lem-box-perm-1423-at02142140 = pickᴰ 8 Sᴰ
  lem-box-perm-2431-at0440 : Ws → St 1595
  lem-box-perm-2431-at0440 = pickᴰ 9 Sᴰ
  lem-box-perm-4132-at04122041 : Ws → St 1451
  lem-box-perm-4132-at04122041 = pickᴰ 10 Sᴰ
  lem-CXuA-S-at0410213243 : Ws → St 1596
  lem-CXuA-S-at0410213243 = pickᴰ 11 Sᴰ
  lem-XCKX-box-2-at0214203143 : Ws → St 1597
  lem-XCKX-box-2-at0214203143 = pickᴰ 12 Sᴰ
  lem-box-box-2-at0440 : Ws → St 1598
  lem-box-box-2-at0440 = pickᴰ 13 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx2-4013 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (CCZ024 ∷ X0 ∷ CZ24 ∷ []) (X0 ∷ CCZ024 ∷ []) (wp 1284 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CZ24 ∷ Toff213 ∷ []) (Toff213 ∷ CZ24 ∷ CCZ134 ∷ []) (wl 1432 (lit c4))
  q4 : Ws → Eqn
  q4 c4 = eqn (X0 ∷ Toff213 ∷ []) (Toff213 ∷ X0 ∷ []) (c₁ (X) (K ↑ • CCZ • K ↑ • iI))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ134 ∷ []) (CS13 ∷ CX41 ∷ CS13⁻ ∷ CX41 ∷ CS34 ∷ []) (wl 617 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ024 ∷ CX41 ∷ []) (CX41 ∷ CCZ024 ∷ []) (wp 285 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ CZ24 ∷ []) (CZ24 ∷ CCZ024 ∷ []) (wp 1285 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (X0 ∷ CZ24 ∷ CZ24 ∷ []) (X0 ∷ []) (wl 1433 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ134 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ134 ∷ []) (wl 954 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS12⁻ ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CS12⁻ ∷ []) (lem-CSdu-box-3-at0214203143 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (Toff103 ∷ []) (wl 1545 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp 88 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q17 : Ws → Eqn
  q17 c4 = eqn (CX13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp 89 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (Toff103 ∷ Toff213 ∷ []) (Toff213 ∷ Toff103 ∷ Toff203 ∷ []) (wl 1620 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ Toff203 ∷ CCZ034 ∷ []) (Toff203 ∷ CCZ024 ∷ []) (wp 1192 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ034 ∷ []) (CS03 ∷ CX40 ∷ CS03⁻ ∷ CX40 ∷ CS34 ∷ []) (wp 320 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS34 ∷ Toff213 ∷ []) (Toff213 ∷ CS34 ∷ []) (wl 808 (lit c4))
  q25 : Ws → Eqn
  q25 c4 = eqn (CX40 ∷ Toff213 ∷ []) (Toff213 ∷ CX40 ∷ []) (lem-comm-CX40-TOFF213 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) (wl 191 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl 196 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (Toff203 ∷ Toff213 ∷ []) (Toff213 ∷ Toff203 ∷ []) (wl 1338 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (Toff103 ∷ Toff203 ∷ Toff203 ∷ []) (Toff103 ∷ []) (wl 1621 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CS12 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ CS12 ∷ []) (lem-CSu-box-3-at0214203143 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx4-2031 ∷ []) (Bx4-1230 ∷ []) (lem-box-perm-4132-at04122041 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx2-4013 ∷ []) (Bx2-4130 ∷ []) (lem-box-perm-1342-at0214203143 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (Bx4-1230 ∷ Bx2-4130 ∷ []) (Bx2-4130 ∷ Bx4-1230 ∷ []) (lem-box-box-2-at0440 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (Bx2-4130 ∷ []) (Bx2-4013 ∷ []) (lem-box-perm-1423-at02142140 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (Bx4-1230 ∷ []) (Bx4-2031 ∷ []) (lem-box-perm-2431-at0440 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (Bx4-2031 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CZ13 ∷ CCZ134 ∷ []) (wl 1616 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CZ13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CZ13 ∷ CCZ134 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ134 ∷ []) (wl 1622 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ134 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ CCZ034 ∷ []) (wp 1419 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ034 ∷ CS12 ∷ []) (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ134 ∷ CS12 ∷ []) (CS12 ∷ CCZ134 ∷ []) (wl 393 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ134 ∷ CCZ034 ∷ Toff103 ∷ CCZ034 ∷ []) (Toff103 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp 1420 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ134 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ134 ∷ []) (wl 392 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CCZ134 ∷ X0 ∷ []) (X0 ∷ CCZ134 ∷ []) (wp 1421 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ134 ∷ CCZ134 ∷ []) [] (wl 321 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ034 ∷ Toff103 ∷ []) (Toff103 ∷ CCZ034 ∷ []) (wp 1422 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp 7 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CX13 ∷ Toff301 ∷ X0 ∷ []) (X0 ∷ Toff301 ∷ []) (wl 1434 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CX13 ∷ Toff301 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CX13 ∷ Toff301 ∷ []) (wl 1623 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CX14 ∷ CX13 ∷ Toff413 ∷ []) (Toff413 ∷ CX13 ∷ []) (wl 1624 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff401 ∷ Toff301 ∷ Toff413 ∷ []) (Toff413 ∷ Toff301 ∷ []) (wp 1423 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ024 ∷ CX14 ∷ []) (CX14 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp 729 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ024 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ012 ∷ CCZ024 ∷ []) (wp 1424 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (K3 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K3⁻ ∷ []) (Toff301 ∷ []) (wl 1625 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp 37 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp 33 c4)
  q59 : Ws → Eqn
  q59 c4 = eqn (CX14 ∷ Toff413 ∷ []) (Toff413 ∷ CX14 ∷ []) (wl 1626 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl 155 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (Toff413 ∷ CS02 ∷ []) (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (CX12 ∷ Toff413 ∷ []) (Toff413 ∷ CX12 ∷ []) (wl 1588 (lit c4))
  q63 : Ws → Eqn
  q63 c4 = eqn (Toff413 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ []) (wp 1398 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Toff401 ∷ Toff413 ∷ []) (Toff413 ∷ Toff401 ∷ []) (wp 1425 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ012 ∷ []) (CX14 ∷ CCZ012 ∷ CX14 ∷ []) (wp 728 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ012 ∷ []) (Toff401 ∷ CCZ012 ∷ Toff401 ∷ []) (wp 1426 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ012 ∷ CX13 ∷ CCZ012 ∷ Toff301 ∷ []) (CX13 ∷ Toff301 ∷ []) (wl 1627 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff301 ∷ X0 ∷ []) (X0 ∷ CX13 ∷ Toff301 ∷ []) (wl 1436 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CS34 ∷ X0 ∷ []) (X0 ∷ CS34 ∷ []) (wl 1437 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CS12⁻ ∷ CS34 ∷ []) (CS34 ∷ CS12⁻ ∷ []) (wl 1628 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CS34 ∷ Toff103 ∷ []) (Toff103 ∷ CS34 ∷ []) (wp 1427 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CS12 ∷ CS34 ∷ []) (CS34 ∷ CS12 ∷ []) (wl 1629 (lit c4))
  q74 : Ws → Eqn
  q74 c4 = eqn (CS34 ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ CS34 ∷ []) (lem-CSu-box-3-at04122041 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CS34⁻ ∷ X0 ∷ []) (X0 ∷ CS34⁻ ∷ []) (wl 1438 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CS12⁻ ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12⁻ ∷ []) (wl 1630 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (CS34⁻ ∷ Toff103 ∷ []) (Toff103 ∷ CS34⁻ ∷ []) (wp 1428 c4)
  q78 : Ws → Eqn
  q78 c4 = eqn (CS12 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CS12 ∷ []) (wl 1631 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CS34⁻ ∷ Bx4-2031 ∷ []) (Bx4-2031 ∷ CS34⁻ ∷ []) (lem-CSdu-box-3-at04122041 c4)

-- F4-CS2-CS0 @0440: 284 steps
lem-F4-CS2-CS0-at0440 : Ws → ⟪ (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS2-CS0-at0440 c4 = derive (X0 ∷ Sb4-2-03-1 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
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
   re 1 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
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
   re 3 1 (CS12 ∷ []) ∷
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
   re 4 1 (Sb4-2-1-3 ∷ []) ∷
   re 6 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 2 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 3 (q49 c4) ∷
   re 2 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 6 1 (CS12⁻ ∷ []) ∷
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
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 1 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 7 (q71 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q73 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw⁻ 3 (q74 c4) ∷
   re 6 1 (Sb4-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 4 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 2 (q70 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   re 4 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 6 1 (CS12 ∷ []) ∷
   re 8 1 (CS12⁻ ∷ []) ∷
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
   re 8 1 (Sb4-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 6 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 6 (q75 c4) ∷
   re 5 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw 9 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw 7 (q78 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw⁻ 5 (q79 c4) ∷
   re 8 1 (Sb4-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 6 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 4 (q75 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q80 : Ws → Eqn
  q80 c4 = eqn (X0 ∷ CK02 ∷ X0 ∷ Bx2-4013 ∷ []) (Bx2-4013 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (lem-XCKX-box-2-at0214203143 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (Toff301 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ Toff301 ∷ []) (wl 1634 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CS34 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS34 ∷ []) (wp 1431 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CS34⁻ ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS34⁻ ∷ []) (wp 1432 c4)

-- F4-K2-CS0 @0440: 11 steps
lem-F4-K2-CS0-at0440 : Ws → ⟪ (X0 ∷ CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K2-CS0-at0440 c4 = derive (X0 ∷ CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ X0 ∷ [])
  (re 3 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 5 1 (CS34 ∷ []) ∷
   re 7 1 (CS34⁻ ∷ []) ∷
   rw 0 (q80 c4) ∷
   rw⁻ 1 (q81 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 4 (q83 c4) ∷
   re 2 1 (Sb2-4-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 0 5 (Sb2-4-01-3 ∷ []) ∷ []) Eq.refl

private
  q84 : Ws → Eqn
  q84 c4 = eqn (CX23 ∷ CX32 ∷ CX23 ∷ []) (Sw23 ∷ []) (wl 258 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (CX23 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ CX23 ∷ []) (lem-CXuA-S-at0410213243 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (CX32 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ CX32 ∷ []) (lem-CXAu-S-at0410213243 c4)

-- SW-S @0410213243: 5 steps
lem-SW-S-at0410213243 : Ws → ⟪ (Sw23 ∷ Sb2-4-01-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-4-01-3 ∷ Sw23 ∷ []) ⟫ʷ
lem-SW-S-at0410213243 c4 = derive (Sw23 ∷ Sb2-4-01-3 ∷ []) (Sb2-4-01-3 ∷ Sw23 ∷ [])
  (rw⁻ 0 (q84 c4) ∷
   rw 2 (q85 c4) ∷
   rw 1 (q86 c4) ∷
   rw 0 (q85 c4) ∷
   rw 1 (q84 c4) ∷ []) Eq.refl
