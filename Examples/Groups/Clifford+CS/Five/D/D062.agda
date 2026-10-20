{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D062 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0155 ; wl0289 ; wl0415 ; wl0929 ; wl1270 ; wl1500 ; wl1501 ; wl1538 ; wl1544 ; wl1545 ; wl1546 ; wl1547 ; wl1588 ; wl1695 ; wl1709 ; wl1710 ; wp0021 ; wp0032 ; wp0038 ; wp0039 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0109 ; wp0142 ; wp0279 ; wp0669 ; wp0765 ; wp1288 ; wp1328 ; wp1342 ; wp1343 ; wp1344 ; wp1345 ; wp1346 ; wp1370 ; wp1375 ; wp1376 ; wp1377 ; wp1378 ; wp1379 ; wp1381 ; wp1398 ; wp1412 ; wp1464 ; wp1465 ; wp1466 ; wp1467 ; wp1468 ; wp1469 ; wl0230 ; wl0341 ; wl1131 ; wl1251 ; wl1712)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at04122041 ; lem-box-cP-at0412233041 ; lem-box2-at04203243)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-box-perm-1324-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.D033 using (lem-box-perm-4132-at04122041 ; lem-box-perm-4213-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CSd13 ; lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-TOFF401-CX23 ; lem-comm-TOFF413-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-TOFF413-CS02 ; lem-comm-TOFF413-CX20)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (K3⁻ ∷ Toff401 ∷ []) (Toff401 ∷ K3⁻ ∷ []) (wp1342 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (Toff302 ∷ []) (wl1501 (lit c4))
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ []) (wp1370 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp1466 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ234 ∷ CS02 ∷ []) (CS02 ∷ CCZ234 ∷ []) (wp0279 c4)
  q8 : Ws → Eqn
  q8 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ234 ∷ []) (wp0765 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) (wl0415 (lit c4))
  q11 : Ws → Eqn
  q11 c4 = eqn (Toff302 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff302 ∷ []) (wp1346 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Bx4-2301 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4)
  q13 : Ws → Eqn
  q13 c4 = eqn (Bx4-2031 ∷ []) (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Bx4-2031 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4)
  q15 : Ws → Eqn
  q15 c4 = eqn (CS13⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS13⁻ ∷ []) (wl1500 (lit c4))
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl0155 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (Toff413 ∷ CS02 ∷ []) (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = eqn (CX12 ∷ Toff413 ∷ []) (Toff413 ∷ CX12 ∷ []) (wl1588 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (Toff413 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = eqn (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ []) (wp1398 c4)
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) (wp0142 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (K3 ∷ Toff401 ∷ []) (Toff401 ∷ K3 ∷ []) (wp1345 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (CS03 ∷ Toff401 ∷ []) (Toff401 ∷ CS03 ∷ []) (wp1328 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Toff401 ∷ CX23 ∷ []) (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = eqn (CS03⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS03⁻ ∷ []) (wp1344 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CS02 ∷ Toff401 ∷ []) (Toff401 ∷ CS02 ∷ []) (wp1343 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ013 ∷ []) (wp1412 c4)
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl0289 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp0021 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp0032 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp0039 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl1710 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (K2 ∷ Toff413 ∷ []) (Toff413 ∷ K2 ∷ []) (wl1538 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS03 ∷ Toff413 ∷ []) (Toff413 ∷ CS03 ∷ []) (wp1376 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff413 ∷ CX20 ∷ []) (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS03⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS03⁻ ∷ []) (wp1375 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CS23 ∷ Toff413 ∷ []) (Toff413 ∷ CS23 ∷ []) (wl1546 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (K2⁻ ∷ Toff413 ∷ []) (Toff413 ∷ K2⁻ ∷ []) (wl1709 (lit c4))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp1467 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ []) (wp1468 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (Toff203 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff203 ∷ []) (wp1469 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx4-2031 ∷ []) (Bx4-1023 ∷ []) (lem-box-perm-4213-at04122041 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Bx4-1023 ∷ Bx4-1023 ∷ []) [] (lem-box2-at04203243 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (Toff403 ∷ Toff103 ∷ Toff413 ∷ []) (Toff413 ∷ Toff103 ∷ []) (wp1379 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ024 ∷ Toff403 ∷ []) (Toff403 ∷ CCZ023 ∷ CCZ024 ∷ []) (wp1381 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (K1 ∷ CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ K1⁻ ∷ []) (Toff103 ∷ []) (wl1545 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp0089 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (Toff403 ∷ Toff413 ∷ []) (Toff413 ∷ Toff403 ∷ []) (wp1377 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ023 ∷ []) (CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ []) (wl1270 (lit c4))
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ023 ∷ []) (Toff403 ∷ CCZ023 ∷ Toff403 ∷ []) (wp1378 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ023 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ023 ∷ []) (wp0669 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CS12 ∷ Toff413 ∷ []) (Toff413 ∷ CS12 ∷ []) (wl1547 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp0081 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CS12⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS12⁻ ∷ []) (wl1544 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (K2 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K2⁻ ∷ []) (Toff201 ∷ []) (wl1695 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ024 ∷ Toff201 ∷ []) (Toff201 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp1288 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ014 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ014 ∷ []) (wp1464 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Toff201 ∷ CCZ014 ∷ CCZ014 ∷ []) (Toff201 ∷ []) (wp1465 c4)

-- L-CCZ-1 @0440 part1: 500 steps
lem-L-CCZ-1-at0440-part1 : Ws → ⟪ (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) ⟫ʷ
lem-L-CCZ-1-at0440-part1 c4 = derive (Bx4-2031 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ CCZ234 ∷ K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ Toff401 ∷ K3⁻ ∷ CCZ024 ∷ CCZ234 ∷ Toff401 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ013 ∷ Toff203 ∷ CCZ012 ∷ Toff302 ∷ Bx4-1023 ∷ []) (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ [])
  (rw⁻ 33 (q1 c4) ∷
   rw 27 (q2 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw 26 (q4 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw 30 (q6 c4) ∷
   rw 29 (q7 c4) ∷
   rw⁻ 30 (q8 c4) ∷
   rw 31 (q9 c4) ∷
   rw⁻ 32 (q8 c4) ∷
   rw 33 (q10 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw 26 (q11 c4) ∷
   rw⁻ 28 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw 28 (q14 c4) ∷
   rw⁻ 31 (q15 c4) ∷
   rw 30 (q16 c4) ∷
   rw⁻ 29 (q15 c4) ∷
   rw 28 (q16 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw 29 (q14 c4) ∷
   rw 33 (q17 c4) ∷
   rw 32 (q18 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw 34 (q20 c4) ∷
   rw⁻ 35 (q19 c4) ∷
   rw⁻ 36 (q21 c4) ∷
   rw⁻ 32 (q17 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw 31 (q17 c4) ∷
   rw 30 (q18 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw 32 (q20 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 34 (q21 c4) ∷
   rw⁻ 30 (q17 c4) ∷
   rw⁻ 29 (q22 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw 30 (q13 c4) ∷
   rw 30 (q12 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 33 (q23 c4) ∷
   rw⁻ 34 (q24 c4) ∷
   rw 35 (q25 c4) ∷
   rw⁻ 36 (q26 c4) ∷
   rw 37 (q25 c4) ∷
   rw⁻ 38 (q27 c4) ∷
   rw⁻ 39 (q1 c4) ∷
   rw 33 (q2 c4) ∷
   rw 32 (q4 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 31 (q23 c4) ∷
   rw⁻ 32 (q24 c4) ∷
   rw 33 (q25 c4) ∷
   rw⁻ 34 (q26 c4) ∷
   rw 35 (q25 c4) ∷
   rw⁻ 36 (q27 c4) ∷
   rw⁻ 37 (q1 c4) ∷
   rw 31 (q2 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw 30 (q4 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw 34 (q6 c4) ∷
   rw 33 (q7 c4) ∷
   rw⁻ 34 (q8 c4) ∷
   rw 35 (q9 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw 37 (q10 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw 30 (q11 c4) ∷
   rw⁻ 32 (q12 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw 32 (q14 c4) ∷
   rw⁻ 35 (q28 c4) ∷
   rw 35 (q29 c4) ∷
   rw 34 (q30 c4) ∷
   rw 35 (q31 c4) ∷
   rw 36 (q32 c4) ∷
   rw 37 (q31 c4) ∷
   rw 38 (q33 c4) ∷
   rw⁻ 34 (q29 c4) ∷
   rw⁻ 33 (q28 c4) ∷
   rw 33 (q29 c4) ∷
   rw 32 (q30 c4) ∷
   rw 33 (q31 c4) ∷
   rw 34 (q32 c4) ∷
   rw 35 (q31 c4) ∷
   rw 36 (q33 c4) ∷
   rw⁻ 32 (q29 c4) ∷
   rw⁻ 33 (q14 c4) ∷
   rw 33 (q14 c4) ∷
   rw⁻ 37 (q34 c4) ∷
   rw⁻ 36 (q35 c4) ∷
   rw⁻ 37 (q36 c4) ∷
   rw 38 (q37 c4) ∷
   rw⁻ 39 (q38 c4) ∷
   rw 40 (q37 c4) ∷
   rw⁻ 41 (q39 c4) ∷
   rw⁻ 42 (q40 c4) ∷
   rw 36 (q34 c4) ∷
   rw 35 (q41 c4) ∷
   rw⁻ 35 (q34 c4) ∷
   rw⁻ 34 (q35 c4) ∷
   rw⁻ 35 (q36 c4) ∷
   rw 36 (q37 c4) ∷
   rw⁻ 37 (q38 c4) ∷
   rw 38 (q37 c4) ∷
   rw⁻ 39 (q39 c4) ∷
   rw⁻ 40 (q40 c4) ∷
   rw 34 (q34 c4) ∷
   rw⁻ 35 (q42 c4) ∷
   rw 33 (q41 c4) ∷
   rw 35 (q43 c4) ∷
   rw 37 (q29 c4) ∷
   rw 36 (q30 c4) ∷
   rw 37 (q31 c4) ∷
   rw 38 (q32 c4) ∷
   rw 39 (q31 c4) ∷
   rw 40 (q33 c4) ∷
   rw⁻ 36 (q29 c4) ∷
   rw 33 (q44 c4) ∷
   rw⁻ 35 (q14 c4) ∷
   rw 35 (q14 c4) ∷
   rw 39 (q17 c4) ∷
   rw 38 (q18 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   rw 40 (q20 c4) ∷
   rw⁻ 41 (q19 c4) ∷
   rw⁻ 42 (q21 c4) ∷
   rw⁻ 38 (q17 c4) ∷
   rw⁻ 37 (q22 c4) ∷
   rw 37 (q17 c4) ∷
   rw 36 (q18 c4) ∷
   rw⁻ 37 (q19 c4) ∷
   rw 38 (q20 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   rw⁻ 40 (q21 c4) ∷
   rw⁻ 36 (q17 c4) ∷
   rw⁻ 35 (q22 c4) ∷
   rw⁻ 36 (q14 c4) ∷
   rw 36 (q13 c4) ∷
   rw 36 (q12 c4) ∷
   rw⁻ 40 (q2 c4) ∷
   rw⁻ 39 (q23 c4) ∷
   rw⁻ 40 (q24 c4) ∷
   rw 41 (q25 c4) ∷
   rw⁻ 42 (q26 c4) ∷
   rw 43 (q25 c4) ∷
   rw⁻ 44 (q27 c4) ∷
   rw⁻ 45 (q1 c4) ∷
   rw 39 (q2 c4) ∷
   rw 38 (q4 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 37 (q23 c4) ∷
   rw⁻ 38 (q24 c4) ∷
   rw 39 (q25 c4) ∷
   rw⁻ 40 (q26 c4) ∷
   rw 41 (q25 c4) ∷
   rw⁻ 42 (q27 c4) ∷
   rw⁻ 43 (q1 c4) ∷
   rw 37 (q2 c4) ∷
   rw⁻ 38 (q3 c4) ∷
   rw 36 (q4 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw 40 (q6 c4) ∷
   rw 39 (q7 c4) ∷
   rw⁻ 40 (q8 c4) ∷
   rw 41 (q9 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw 43 (q10 c4) ∷
   rw⁻ 39 (q6 c4) ∷
   rw 36 (q11 c4) ∷
   rw⁻ 38 (q12 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw 38 (q45 c4) ∷
   rw 38 (q46 c4) ∷
   rw 0 (q14 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 4 (q50 c4) ∷
   rw 5 (q30 c4) ∷
   rw 6 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw 8 (q31 c4) ∷
   rw 9 (q33 c4) ∷
   rw 10 (q51 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 5 (q37 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw⁻ 0 (q55 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 1 (q50 c4) ∷
   rw 2 (q30 c4) ∷
   rw 3 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw 5 (q31 c4) ∷
   rw 6 (q33 c4) ∷
   rw 7 (q51 c4) ∷
   rw 1 (q49 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 2 (q14 c4) ∷
   rw⁻ 5 (q56 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw 5 (q48 c4) ∷
   rw⁻ 8 (q49 c4) ∷
   rw 7 (q50 c4) ∷
   rw 8 (q30 c4) ∷
   rw 9 (q31 c4) ∷
   rw 10 (q32 c4) ∷
   rw 11 (q31 c4) ∷
   rw 12 (q33 c4) ∷
   rw 13 (q51 c4) ∷
   rw 7 (q49 c4) ∷
   rw⁻ 4 (q52 c4) ∷
   rw 6 (q53 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 8 (q37 c4) ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 5 (q53 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw⁻ 3 (q55 c4) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 4 (q50 c4) ∷
   rw 5 (q30 c4) ∷
   rw 6 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw 8 (q31 c4) ∷
   rw 9 (q33 c4) ∷
   rw 10 (q51 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw 7 (q59 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 5 (q59 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw⁻ 9 (q35 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw⁻ 15 (q40 c4) ∷
   rw 9 (q60 c4) ∷
   rw 8 (q61 c4) ∷
   rw⁻ 8 (q60 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw⁻ 13 (q40 c4) ∷
   rw 7 (q60 c4) ∷
   rw⁻ 8 (q62 c4) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw 10 (q29 c4) ∷
   rw 9 (q30 c4) ∷
   rw 10 (q31 c4) ∷
   rw 11 (q32 c4) ∷
   rw 12 (q31 c4) ∷
   rw 13 (q33 c4) ∷
   rw⁻ 9 (q29 c4) ∷
   rw 6 (q64 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 12 (q53 c4) ∷
   rw⁻ 11 (q36 c4) ∷
   rw 12 (q37 c4) ∷
   rw⁻ 13 (q38 c4) ∷
   rw 14 (q37 c4) ∷
   rw⁻ 15 (q39 c4) ∷
   rw⁻ 11 (q53 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw 10 (q53 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   rw 10 (q37 c4) ∷
   rw⁻ 11 (q38 c4) ∷
   rw 12 (q37 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 13 (q53 c4) ∷
   rw⁻ 12 (q36 c4) ∷
   rw 13 (q37 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 15 (q37 c4) ∷
   rw⁻ 16 (q39 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw⁻ 11 (q55 c4) ∷
   rw 11 (q53 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw 11 (q37 c4) ∷
   rw⁻ 12 (q38 c4) ∷
   rw 13 (q37 c4) ∷
   rw⁻ 14 (q39 c4) ∷
   rw⁻ 10 (q53 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw⁻ 13 (q47 c4) ∷
   rw 12 (q48 c4) ∷
   rw⁻ 15 (q49 c4) ∷
   rw 14 (q50 c4) ∷
   rw 15 (q30 c4) ∷
   rw 16 (q31 c4) ∷
   rw 17 (q32 c4) ∷
   rw 18 (q31 c4) ∷
   rw 19 (q33 c4) ∷
   rw 20 (q51 c4) ∷
   rw 14 (q49 c4) ∷
   rw⁻ 11 (q52 c4) ∷
   rw 13 (q53 c4) ∷
   rw⁻ 12 (q36 c4) ∷
   rw 13 (q37 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 15 (q37 c4) ∷
   rw⁻ 16 (q39 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw⁻ 13 (q47 c4) ∷
   rw⁻ 11 (q54 c4) ∷
   rw⁻ 10 (q55 c4) ∷
   rw⁻ 12 (q49 c4) ∷
   rw 11 (q50 c4) ∷
   rw 12 (q30 c4) ∷
   rw 13 (q31 c4) ∷
   rw 14 (q32 c4) ∷
   rw 15 (q31 c4) ∷
   rw 16 (q33 c4) ∷
   rw 17 (q51 c4) ∷
   rw 11 (q49 c4) ∷
   rw⁻ 12 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw⁻ 15 (q56 c4) ∷
   rw 14 (q57 c4) ∷
   rw⁻ 13 (q56 c4) ∷
   rw 12 (q57 c4) ∷
   rw⁻ 13 (q14 c4) ∷
   rw 13 (q14 c4) ∷
   rw 17 (q53 c4) ∷
   rw⁻ 16 (q36 c4) ∷
   rw 17 (q37 c4) ∷
   rw⁻ 18 (q38 c4) ∷
   rw 19 (q37 c4) ∷
   rw⁻ 20 (q39 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw⁻ 15 (q55 c4) ∷
   rw 15 (q53 c4) ∷
   rw⁻ 14 (q36 c4) ∷
   rw 15 (q37 c4) ∷
   rw⁻ 16 (q38 c4) ∷
   rw 17 (q37 c4) ∷
   rw⁻ 18 (q39 c4) ∷
   rw⁻ 14 (q53 c4) ∷
   rw⁻ 13 (q55 c4) ∷
   rw⁻ 14 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw⁻ 17 (q47 c4) ∷
   rw 16 (q48 c4) ∷
   rw⁻ 19 (q49 c4) ∷
   rw 18 (q50 c4) ∷
   rw 19 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw 21 (q32 c4) ∷
   rw 22 (q31 c4) ∷
   rw 23 (q33 c4) ∷
   rw 24 (q51 c4) ∷
   rw 18 (q49 c4) ∷
   rw⁻ 15 (q52 c4) ∷
   rw 17 (q53 c4) ∷
   rw⁻ 16 (q36 c4) ∷
   rw 17 (q37 c4) ∷
   rw⁻ 18 (q38 c4) ∷
   rw 19 (q37 c4) ∷
   rw⁻ 20 (q39 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw⁻ 17 (q47 c4) ∷
   rw⁻ 15 (q54 c4) ∷
   rw⁻ 14 (q55 c4) ∷
   rw⁻ 16 (q49 c4) ∷
   rw 15 (q50 c4) ∷
   rw 16 (q30 c4) ∷
   rw 17 (q31 c4) ∷
   rw 18 (q32 c4) ∷
   rw 19 (q31 c4) ∷
   rw 20 (q33 c4) ∷
   rw 21 (q51 c4) ∷
   rw 15 (q49 c4) ∷
   rw⁻ 16 (q14 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 19 (q58 c4) ∷
   rw 18 (q59 c4) ∷
   rw⁻ 17 (q58 c4) ∷
   rw 16 (q59 c4) ∷
   rw⁻ 17 (q14 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 21 (q60 c4) ∷
   rw⁻ 20 (q35 c4) ∷
   rw 21 (q18 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw 23 (q20 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 26 (q40 c4) ∷
   rw 20 (q60 c4) ∷
   rw 19 (q61 c4) ∷
   rw⁻ 19 (q60 c4) ∷
   rw⁻ 18 (q35 c4) ∷
   rw 19 (q18 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw 21 (q20 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw⁻ 24 (q40 c4) ∷
   rw 18 (q60 c4) ∷
   rw⁻ 19 (q62 c4) ∷
   rw 17 (q61 c4) ∷
   rw⁻ 19 (q63 c4) ∷
   rw 21 (q29 c4) ∷
   rw 20 (q30 c4) ∷
   rw 21 (q31 c4) ∷
   rw 22 (q32 c4) ∷
   rw 23 (q31 c4) ∷
   rw 24 (q33 c4) ∷
   rw⁻ 20 (q29 c4) ∷
   rw 17 (q64 c4) ∷
   rw⁻ 19 (q14 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 22 (q28 c4) ∷
   rw 22 (q29 c4) ∷
   rw 21 (q30 c4) ∷
   rw 22 (q31 c4) ∷
   rw 23 (q32 c4) ∷
   rw 24 (q31 c4) ∷
   rw 25 (q33 c4) ∷
   rw⁻ 21 (q29 c4) ∷
   rw⁻ 20 (q28 c4) ∷
   rw 20 (q29 c4) ∷
   rw 19 (q30 c4) ∷
   rw 20 (q31 c4) ∷
   rw 21 (q32 c4) ∷
   rw 22 (q31 c4) ∷
   rw 23 (q33 c4) ∷
   rw⁻ 19 (q29 c4) ∷
   rw⁻ 20 (q14 c4) ∷
   rw 20 (q13 c4) ∷
   rw 20 (q12 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw⁻ 23 (q23 c4) ∷
   rw⁻ 24 (q24 c4) ∷
   rw 25 (q25 c4) ∷
   rw⁻ 26 (q26 c4) ∷
   rw 27 (q25 c4) ∷
   rw⁻ 28 (q27 c4) ∷
   rw⁻ 29 (q1 c4) ∷
   rw 23 (q2 c4) ∷
   rw 22 (q4 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 21 (q23 c4) ∷
   rw⁻ 22 (q24 c4) ∷
   rw 23 (q25 c4) ∷
   rw⁻ 24 (q26 c4) ∷
   rw 25 (q25 c4) ∷
   rw⁻ 26 (q27 c4) ∷
   rw⁻ 27 (q1 c4) ∷
   rw 21 (q2 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw 20 (q4 c4) ∷
   rw⁻ 22 (q5 c4) ∷
   rw 24 (q6 c4) ∷
   rw 23 (q7 c4) ∷
   rw⁻ 24 (q8 c4) ∷
   rw 25 (q9 c4) ∷
   rw⁻ 26 (q8 c4) ∷
   rw 27 (q10 c4) ∷
   rw⁻ 23 (q6 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = eqn (CCZ013 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ013 ∷ []) (wl1131 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl0230 (lit c4))
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ012 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ012 ∷ []) (wl1251 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl0341 (lit c4))
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ []) [] (wl1712 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx4-2031 ∷ []) (Bx4-1230 ∷ []) (lem-box-perm-4132-at04122041 c4)

-- L-CCZ-1 @0440 part3: 6 steps
lem-L-CCZ-1-at0440-part3 : Ws → ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-L-CCZ-1-at0440-part3 c4 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) (Bx4-1230 ∷ [])
  (rw 21 (q65 c4) ∷
   rw 22 (q66 c4) ∷
   rw 23 (q67 c4) ∷
   rw 24 (q68 c4) ∷
   rw 0 (q69 c4) ∷
   rw 0 (q70 c4) ∷ []) Eq.refl
