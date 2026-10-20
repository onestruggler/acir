{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D035 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.D017 using (lem-box-cP-at04122041 ; lem-box-cP-at0412233041)
open import Examples.Groups.Clifford+CS.Five.D.D023 using (lem-box-perm-1324-at04122041)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-TOFF401-CX23 ; lem-comm-TOFF413-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-TOFF413-CS02 ; lem-comm-TOFF413-CX20)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Toff302 ∷ CCZ024 ∷ CCZ024 ∷ []) (Toff302 ∷ []) (wp 1346 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Bx4-2301 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) (lem-box-cP-at0412233041 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (Bx4-2031 ∷ []) (Bx4-2301 ∷ []) (lem-box-perm-1324-at04122041 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Bx4-2031 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) (lem-box-cP-at04122041 c4)
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl 155 (lit c4))
  q6 : Ws → Eqn
  q6 c4 = eqn (Toff413 ∷ CS02 ∷ []) (CS02 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CS02 (lit c4))
  q7 : Ws → Eqn
  q7 c4 = eqn (CX12 ∷ Toff413 ∷ []) (Toff413 ∷ CX12 ∷ []) (wl 1588 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (Toff413 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff413 ∷ []) (lem-comm-TOFF413-CSd02 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = eqn (CS01 ∷ Toff413 ∷ []) (Toff413 ∷ CS01 ∷ []) (wp 1398 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ012 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ012 ∷ []) (wp 142 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (K2 ∷ CS03 ∷ CX20 ∷ CS03⁻ ∷ CX20 ∷ CS23 ∷ K2⁻ ∷ []) (Toff203 ∷ []) (wl 1710 (lit c4))
  q12 : Ws → Eqn
  q12 c4 = eqn (K2 ∷ Toff413 ∷ []) (Toff413 ∷ K2 ∷ []) (wl 1538 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS03 ∷ Toff413 ∷ []) (Toff413 ∷ CS03 ∷ []) (wp 1376 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Toff413 ∷ CX20 ∷ []) (CX20 ∷ Toff413 ∷ []) (lem-comm-TOFF413-CX20 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS03⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS03⁻ ∷ []) (wp 1375 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS23 ∷ Toff413 ∷ []) (Toff413 ∷ CS23 ∷ []) (wl 1546 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (K2⁻ ∷ Toff413 ∷ []) (Toff413 ∷ K2⁻ ∷ []) (wl 1709 (lit c4))
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp 1467 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CCZ034 ∷ CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ034 ∷ []) (wp 1468 c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ024 ∷ CCZ034 ∷ []) (CCZ034 ∷ CCZ024 ∷ []) (wp 109 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl 289 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff203 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff203 ∷ []) (wp 1469 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ013 ∷ Toff413 ∷ []) (Toff413 ∷ CCZ013 ∷ []) (wp 1412 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (K3 ∷ CS03 ∷ CX23 ∷ CS03⁻ ∷ CX23 ∷ CS02 ∷ K3⁻ ∷ []) (Toff302 ∷ []) (wl 1501 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (K3 ∷ Toff401 ∷ []) (Toff401 ∷ K3 ∷ []) (wp 1345 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CS03 ∷ Toff401 ∷ []) (Toff401 ∷ CS03 ∷ []) (wp 1328 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff401 ∷ CX23 ∷ []) (CX23 ∷ Toff401 ∷ []) (lem-comm-TOFF401-CX23 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CS03⁻ ∷ Toff401 ∷ []) (Toff401 ∷ CS03⁻ ∷ []) (wp 1344 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CS02 ∷ Toff401 ∷ []) (Toff401 ∷ CS02 ∷ []) (wp 1343 c4)
  q34 : Ws → Eqn
  q34 c4 = eqn (K3⁻ ∷ Toff401 ∷ []) (Toff401 ∷ K3⁻ ∷ []) (wp 1342 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ234 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp 1466 c4)
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ024 ∷ CCZ012 ∷ Toff401 ∷ []) (Toff401 ∷ CCZ024 ∷ []) (wp 1370 c4)
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl 929 (lit c4))
  q39 : Ws → Eqn
  q39 c4 = eqn (CCZ234 ∷ CS02 ∷ []) (CS02 ∷ CCZ234 ∷ []) (wp 279 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (CX10 ∷ CCZ234 ∷ []) (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ))
  q41 : Ws → Eqn
  q41 c4 = eqn (CCZ234 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ234 ∷ []) (wp 765 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) (wl 415 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS13 ∷ Toff413 ∷ []) (Toff413 ∷ CS13 ∷ []) (wl 1502 (lit c4))
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ024 ∷ CS13 ∷ []) (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4))
  q45 : Ws → Eqn
  q45 c4 = eqn (CS13⁻ ∷ Toff413 ∷ []) (Toff413 ∷ CS13⁻ ∷ []) (wl 1500 (lit c4))
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ023 ∷ Toff103 ∷ CS12 ∷ []) (Toff103 ∷ CS12 ∷ CCZ023 ∷ []) (wl 1549 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ023 ∷ CCZ023 ∷ []) [] (wl 204 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ []) (CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ []) (wl 1711 (lit c4))
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wl 341 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ012 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ012 ∷ []) (wl 1251 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) (wl 311 (lit c4))

-- L-CCZ-1 @0440 part2: 500 steps
lem-L-CCZ-1-at0440-part2 : Ws → ⟪ (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ []) ⟫ʷ
lem-L-CCZ-1-at0440-part2 c4 = derive (CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ023 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ CCZ013 ∷ Toff302 ∷ CCZ024 ∷ CCZ024 ∷ CCZ012 ∷ CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ CCZ012 ∷ Toff203 ∷ CCZ013 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CS13⁻ ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ Toff103 ∷ CS12 ∷ CCZ023 ∷ Toff103 ∷ CS12⁻ ∷ Toff201 ∷ CCZ013 ∷ Toff302 ∷ Toff203 ∷ Toff302 ∷ Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ Toff302 ∷ CCZ012 ∷ CCZ013 ∷ Toff203 ∷ CCZ013 ∷ CCZ013 ∷ CCZ012 ∷ Toff302 ∷ CCZ012 ∷ CCZ012 ∷ Bx4-2031 ∷ [])
  (rw 20 (q1 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 22 (q3 c4) ∷
   rw 22 (q4 c4) ∷
   rw 26 (q5 c4) ∷
   rw 25 (q6 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw 27 (q8 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw⁻ 29 (q9 c4) ∷
   rw⁻ 25 (q5 c4) ∷
   rw⁻ 24 (q10 c4) ∷
   rw 24 (q5 c4) ∷
   rw 23 (q6 c4) ∷
   rw⁻ 24 (q7 c4) ∷
   rw 25 (q8 c4) ∷
   rw⁻ 26 (q7 c4) ∷
   rw⁻ 27 (q9 c4) ∷
   rw⁻ 23 (q5 c4) ∷
   rw⁻ 22 (q10 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw 23 (q4 c4) ∷
   rw⁻ 27 (q11 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 27 (q13 c4) ∷
   rw 28 (q14 c4) ∷
   rw⁻ 29 (q15 c4) ∷
   rw 30 (q14 c4) ∷
   rw⁻ 31 (q16 c4) ∷
   rw⁻ 32 (q17 c4) ∷
   rw 26 (q11 c4) ∷
   rw 25 (q18 c4) ∷
   rw⁻ 25 (q11 c4) ∷
   rw⁻ 24 (q12 c4) ∷
   rw⁻ 25 (q13 c4) ∷
   rw 26 (q14 c4) ∷
   rw⁻ 27 (q15 c4) ∷
   rw 28 (q14 c4) ∷
   rw⁻ 29 (q16 c4) ∷
   rw⁻ 30 (q17 c4) ∷
   rw 24 (q11 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw 23 (q18 c4) ∷
   rw 25 (q20 c4) ∷
   rw 27 (q21 c4) ∷
   rw 26 (q22 c4) ∷
   rw 27 (q23 c4) ∷
   rw 28 (q24 c4) ∷
   rw 29 (q23 c4) ∷
   rw 30 (q25 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw 23 (q26 c4) ∷
   rw⁻ 25 (q4 c4) ∷
   rw 25 (q4 c4) ∷
   rw⁻ 28 (q27 c4) ∷
   rw 28 (q21 c4) ∷
   rw 27 (q22 c4) ∷
   rw 28 (q23 c4) ∷
   rw 29 (q24 c4) ∷
   rw 30 (q23 c4) ∷
   rw 31 (q25 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 26 (q27 c4) ∷
   rw 26 (q21 c4) ∷
   rw 25 (q22 c4) ∷
   rw 26 (q23 c4) ∷
   rw 27 (q24 c4) ∷
   rw 28 (q23 c4) ∷
   rw 29 (q25 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw 26 (q3 c4) ∷
   rw 26 (q2 c4) ∷
   rw⁻ 30 (q28 c4) ∷
   rw⁻ 29 (q29 c4) ∷
   rw⁻ 30 (q30 c4) ∷
   rw 31 (q31 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw 33 (q31 c4) ∷
   rw⁻ 34 (q33 c4) ∷
   rw⁻ 35 (q34 c4) ∷
   rw 29 (q28 c4) ∷
   rw 28 (q35 c4) ∷
   rw⁻ 28 (q28 c4) ∷
   rw⁻ 27 (q29 c4) ∷
   rw⁻ 28 (q30 c4) ∷
   rw 29 (q31 c4) ∷
   rw⁻ 30 (q32 c4) ∷
   rw 31 (q31 c4) ∷
   rw⁻ 32 (q33 c4) ∷
   rw⁻ 33 (q34 c4) ∷
   rw 27 (q28 c4) ∷
   rw⁻ 28 (q36 c4) ∷
   rw 26 (q35 c4) ∷
   rw⁻ 28 (q37 c4) ∷
   rw 30 (q38 c4) ∷
   rw 29 (q39 c4) ∷
   rw⁻ 30 (q40 c4) ∷
   rw 31 (q41 c4) ∷
   rw⁻ 32 (q40 c4) ∷
   rw 33 (q42 c4) ∷
   rw⁻ 29 (q38 c4) ∷
   rw 26 (q1 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw 28 (q4 c4) ∷
   rw 32 (q5 c4) ∷
   rw 31 (q6 c4) ∷
   rw⁻ 32 (q7 c4) ∷
   rw 33 (q8 c4) ∷
   rw⁻ 34 (q7 c4) ∷
   rw⁻ 35 (q9 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q10 c4) ∷
   rw 30 (q5 c4) ∷
   rw 29 (q6 c4) ∷
   rw⁻ 30 (q7 c4) ∷
   rw 31 (q8 c4) ∷
   rw⁻ 32 (q7 c4) ∷
   rw⁻ 33 (q9 c4) ∷
   rw⁻ 29 (q5 c4) ∷
   rw⁻ 28 (q10 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw 29 (q4 c4) ∷
   rw 33 (q5 c4) ∷
   rw 32 (q6 c4) ∷
   rw⁻ 33 (q7 c4) ∷
   rw 34 (q8 c4) ∷
   rw⁻ 35 (q7 c4) ∷
   rw⁻ 36 (q9 c4) ∷
   rw⁻ 32 (q5 c4) ∷
   rw⁻ 31 (q10 c4) ∷
   rw 31 (q5 c4) ∷
   rw 30 (q6 c4) ∷
   rw⁻ 31 (q7 c4) ∷
   rw 32 (q8 c4) ∷
   rw⁻ 33 (q7 c4) ∷
   rw⁻ 34 (q9 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 29 (q10 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw 30 (q3 c4) ∷
   rw 30 (q2 c4) ∷
   rw⁻ 34 (q28 c4) ∷
   rw⁻ 33 (q29 c4) ∷
   rw⁻ 34 (q30 c4) ∷
   rw 35 (q31 c4) ∷
   rw⁻ 36 (q32 c4) ∷
   rw 37 (q31 c4) ∷
   rw⁻ 38 (q33 c4) ∷
   rw⁻ 39 (q34 c4) ∷
   rw 33 (q28 c4) ∷
   rw 32 (q35 c4) ∷
   rw⁻ 32 (q28 c4) ∷
   rw⁻ 31 (q29 c4) ∷
   rw⁻ 32 (q30 c4) ∷
   rw 33 (q31 c4) ∷
   rw⁻ 34 (q32 c4) ∷
   rw 35 (q31 c4) ∷
   rw⁻ 36 (q33 c4) ∷
   rw⁻ 37 (q34 c4) ∷
   rw 31 (q28 c4) ∷
   rw⁻ 32 (q36 c4) ∷
   rw 30 (q35 c4) ∷
   rw⁻ 32 (q37 c4) ∷
   rw 34 (q38 c4) ∷
   rw 33 (q39 c4) ∷
   rw⁻ 34 (q40 c4) ∷
   rw 35 (q41 c4) ∷
   rw⁻ 36 (q40 c4) ∷
   rw 37 (q42 c4) ∷
   rw⁻ 33 (q38 c4) ∷
   rw 30 (q1 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw 32 (q4 c4) ∷
   rw 36 (q5 c4) ∷
   rw 35 (q6 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw 37 (q8 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 39 (q9 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw 34 (q5 c4) ∷
   rw 33 (q6 c4) ∷
   rw⁻ 34 (q7 c4) ∷
   rw 35 (q8 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw⁻ 37 (q9 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 32 (q10 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw 33 (q4 c4) ∷
   rw⁻ 36 (q43 c4) ∷
   rw 35 (q44 c4) ∷
   rw⁻ 34 (q43 c4) ∷
   rw 33 (q44 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw 34 (q4 c4) ∷
   rw 38 (q5 c4) ∷
   rw 37 (q6 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw 39 (q8 c4) ∷
   rw⁻ 40 (q7 c4) ∷
   rw⁻ 41 (q9 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw 36 (q5 c4) ∷
   rw 35 (q6 c4) ∷
   rw⁻ 36 (q7 c4) ∷
   rw 37 (q8 c4) ∷
   rw⁻ 38 (q7 c4) ∷
   rw⁻ 39 (q9 c4) ∷
   rw⁻ 35 (q5 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw 35 (q3 c4) ∷
   rw 35 (q2 c4) ∷
   rw⁻ 39 (q28 c4) ∷
   rw⁻ 38 (q29 c4) ∷
   rw⁻ 39 (q30 c4) ∷
   rw 40 (q31 c4) ∷
   rw⁻ 41 (q32 c4) ∷
   rw 42 (q31 c4) ∷
   rw⁻ 43 (q33 c4) ∷
   rw⁻ 44 (q34 c4) ∷
   rw 38 (q28 c4) ∷
   rw 37 (q35 c4) ∷
   rw⁻ 37 (q28 c4) ∷
   rw⁻ 36 (q29 c4) ∷
   rw⁻ 37 (q30 c4) ∷
   rw 38 (q31 c4) ∷
   rw⁻ 39 (q32 c4) ∷
   rw 40 (q31 c4) ∷
   rw⁻ 41 (q33 c4) ∷
   rw⁻ 42 (q34 c4) ∷
   rw 36 (q28 c4) ∷
   rw⁻ 37 (q36 c4) ∷
   rw 35 (q35 c4) ∷
   rw⁻ 37 (q37 c4) ∷
   rw 39 (q38 c4) ∷
   rw 38 (q39 c4) ∷
   rw⁻ 39 (q40 c4) ∷
   rw 40 (q41 c4) ∷
   rw⁻ 41 (q40 c4) ∷
   rw 42 (q42 c4) ∷
   rw⁻ 38 (q38 c4) ∷
   rw 35 (q1 c4) ∷
   rw⁻ 37 (q2 c4) ∷
   rw⁻ 37 (q3 c4) ∷
   rw 37 (q4 c4) ∷
   rw 41 (q5 c4) ∷
   rw 40 (q6 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw 42 (q8 c4) ∷
   rw⁻ 43 (q7 c4) ∷
   rw⁻ 44 (q9 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw 39 (q5 c4) ∷
   rw 38 (q6 c4) ∷
   rw⁻ 39 (q7 c4) ∷
   rw 40 (q8 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw⁻ 38 (q5 c4) ∷
   rw⁻ 37 (q10 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw 38 (q4 c4) ∷
   rw⁻ 41 (q45 c4) ∷
   rw 40 (q46 c4) ∷
   rw⁻ 39 (q45 c4) ∷
   rw 38 (q46 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw 39 (q4 c4) ∷
   rw 43 (q5 c4) ∷
   rw 42 (q6 c4) ∷
   rw⁻ 43 (q7 c4) ∷
   rw 44 (q8 c4) ∷
   rw⁻ 45 (q7 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw⁻ 42 (q5 c4) ∷
   rw⁻ 41 (q10 c4) ∷
   rw 41 (q5 c4) ∷
   rw 40 (q6 c4) ∷
   rw⁻ 41 (q7 c4) ∷
   rw 42 (q8 c4) ∷
   rw⁻ 43 (q7 c4) ∷
   rw⁻ 44 (q9 c4) ∷
   rw⁻ 40 (q5 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 40 (q4 c4) ∷
   rw 40 (q3 c4) ∷
   rw 40 (q2 c4) ∷
   rw⁻ 44 (q28 c4) ∷
   rw⁻ 43 (q29 c4) ∷
   rw⁻ 44 (q30 c4) ∷
   rw 45 (q31 c4) ∷
   rw⁻ 46 (q32 c4) ∷
   rw 47 (q31 c4) ∷
   rw⁻ 48 (q33 c4) ∷
   rw⁻ 49 (q34 c4) ∷
   rw 43 (q28 c4) ∷
   rw 42 (q35 c4) ∷
   rw⁻ 42 (q28 c4) ∷
   rw⁻ 41 (q29 c4) ∷
   rw⁻ 42 (q30 c4) ∷
   rw 43 (q31 c4) ∷
   rw⁻ 44 (q32 c4) ∷
   rw 45 (q31 c4) ∷
   rw⁻ 46 (q33 c4) ∷
   rw⁻ 47 (q34 c4) ∷
   rw 41 (q28 c4) ∷
   rw⁻ 42 (q36 c4) ∷
   rw 40 (q35 c4) ∷
   rw⁻ 42 (q37 c4) ∷
   rw 44 (q38 c4) ∷
   rw 43 (q39 c4) ∷
   rw⁻ 44 (q40 c4) ∷
   rw 45 (q41 c4) ∷
   rw⁻ 46 (q40 c4) ∷
   rw 47 (q42 c4) ∷
   rw⁻ 43 (q38 c4) ∷
   rw 40 (q1 c4) ∷
   rw⁻ 42 (q2 c4) ∷
   rw⁻ 42 (q3 c4) ∷
   rw 42 (q4 c4) ∷
   rw 46 (q5 c4) ∷
   rw 45 (q6 c4) ∷
   rw⁻ 46 (q7 c4) ∷
   rw 47 (q8 c4) ∷
   rw⁻ 48 (q7 c4) ∷
   rw⁻ 49 (q9 c4) ∷
   rw⁻ 45 (q5 c4) ∷
   rw⁻ 44 (q10 c4) ∷
   rw 44 (q5 c4) ∷
   rw 43 (q6 c4) ∷
   rw⁻ 44 (q7 c4) ∷
   rw 45 (q8 c4) ∷
   rw⁻ 46 (q7 c4) ∷
   rw⁻ 47 (q9 c4) ∷
   rw⁻ 43 (q5 c4) ∷
   rw⁻ 42 (q10 c4) ∷
   rw⁻ 43 (q4 c4) ∷
   rw 43 (q4 c4) ∷
   rw⁻ 46 (q27 c4) ∷
   rw 46 (q21 c4) ∷
   rw 45 (q22 c4) ∷
   rw 46 (q23 c4) ∷
   rw 47 (q24 c4) ∷
   rw 48 (q23 c4) ∷
   rw 49 (q25 c4) ∷
   rw⁻ 45 (q21 c4) ∷
   rw⁻ 44 (q27 c4) ∷
   rw 44 (q21 c4) ∷
   rw 43 (q22 c4) ∷
   rw 44 (q23 c4) ∷
   rw 45 (q24 c4) ∷
   rw 46 (q23 c4) ∷
   rw 47 (q25 c4) ∷
   rw⁻ 43 (q21 c4) ∷
   rw⁻ 44 (q4 c4) ∷
   rw 44 (q4 c4) ∷
   rw⁻ 48 (q11 c4) ∷
   rw⁻ 47 (q12 c4) ∷
   rw⁻ 48 (q13 c4) ∷
   rw 49 (q14 c4) ∷
   rw⁻ 50 (q15 c4) ∷
   rw 51 (q14 c4) ∷
   rw⁻ 52 (q16 c4) ∷
   rw⁻ 53 (q17 c4) ∷
   rw 47 (q11 c4) ∷
   rw 46 (q18 c4) ∷
   rw⁻ 46 (q11 c4) ∷
   rw⁻ 45 (q12 c4) ∷
   rw⁻ 46 (q13 c4) ∷
   rw 47 (q14 c4) ∷
   rw⁻ 48 (q15 c4) ∷
   rw 49 (q14 c4) ∷
   rw⁻ 50 (q16 c4) ∷
   rw⁻ 51 (q17 c4) ∷
   rw 45 (q11 c4) ∷
   rw⁻ 46 (q19 c4) ∷
   rw 44 (q18 c4) ∷
   rw 46 (q20 c4) ∷
   rw 48 (q21 c4) ∷
   rw 47 (q22 c4) ∷
   rw 48 (q23 c4) ∷
   rw 49 (q24 c4) ∷
   rw 50 (q23 c4) ∷
   rw 51 (q25 c4) ∷
   rw⁻ 47 (q21 c4) ∷
   rw 44 (q26 c4) ∷
   rw⁻ 46 (q4 c4) ∷
   rw 46 (q4 c4) ∷
   rw⁻ 49 (q27 c4) ∷
   rw 49 (q21 c4) ∷
   rw 48 (q22 c4) ∷
   rw 49 (q23 c4) ∷
   rw 50 (q24 c4) ∷
   rw 51 (q23 c4) ∷
   rw 52 (q25 c4) ∷
   rw⁻ 48 (q21 c4) ∷
   rw⁻ 47 (q27 c4) ∷
   rw 47 (q21 c4) ∷
   rw 46 (q22 c4) ∷
   rw 47 (q23 c4) ∷
   rw 48 (q24 c4) ∷
   rw 49 (q23 c4) ∷
   rw 50 (q25 c4) ∷
   rw⁻ 46 (q21 c4) ∷
   rw⁻ 47 (q4 c4) ∷
   rw 47 (q4 c4) ∷
   rw 51 (q5 c4) ∷
   rw 50 (q6 c4) ∷
   rw⁻ 51 (q7 c4) ∷
   rw 52 (q8 c4) ∷
   rw⁻ 53 (q7 c4) ∷
   rw⁻ 54 (q9 c4) ∷
   rw⁻ 50 (q5 c4) ∷
   rw⁻ 49 (q10 c4) ∷
   rw 49 (q5 c4) ∷
   rw 48 (q6 c4) ∷
   rw⁻ 49 (q7 c4) ∷
   rw 50 (q8 c4) ∷
   rw⁻ 51 (q7 c4) ∷
   rw⁻ 52 (q9 c4) ∷
   rw⁻ 48 (q5 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 48 (q4 c4) ∷
   rw 48 (q3 c4) ∷
   rw 48 (q2 c4) ∷
   rw⁻ 52 (q28 c4) ∷
   rw⁻ 51 (q29 c4) ∷
   rw⁻ 52 (q30 c4) ∷
   rw 53 (q31 c4) ∷
   rw⁻ 54 (q32 c4) ∷
   rw 55 (q31 c4) ∷
   rw⁻ 56 (q33 c4) ∷
   rw⁻ 57 (q34 c4) ∷
   rw 51 (q28 c4) ∷
   rw 50 (q35 c4) ∷
   rw⁻ 50 (q28 c4) ∷
   rw⁻ 49 (q29 c4) ∷
   rw⁻ 50 (q30 c4) ∷
   rw 51 (q31 c4) ∷
   rw⁻ 52 (q32 c4) ∷
   rw 53 (q31 c4) ∷
   rw⁻ 54 (q33 c4) ∷
   rw⁻ 55 (q34 c4) ∷
   rw 49 (q28 c4) ∷
   rw⁻ 50 (q36 c4) ∷
   rw 48 (q35 c4) ∷
   rw⁻ 50 (q37 c4) ∷
   rw 52 (q38 c4) ∷
   rw 51 (q39 c4) ∷
   rw⁻ 52 (q40 c4) ∷
   rw 53 (q41 c4) ∷
   rw⁻ 54 (q40 c4) ∷
   rw 55 (q42 c4) ∷
   rw⁻ 51 (q38 c4) ∷
   rw 48 (q1 c4) ∷
   rw⁻ 50 (q2 c4) ∷
   rw⁻ 50 (q3 c4) ∷
   rw 50 (q4 c4) ∷
   rw 54 (q5 c4) ∷
   rw 53 (q6 c4) ∷
   rw⁻ 54 (q7 c4) ∷
   rw 55 (q8 c4) ∷
   rw⁻ 56 (q7 c4) ∷
   rw⁻ 57 (q9 c4) ∷
   rw⁻ 53 (q5 c4) ∷
   rw⁻ 52 (q10 c4) ∷
   rw 52 (q5 c4) ∷
   rw 51 (q6 c4) ∷
   rw⁻ 52 (q7 c4) ∷
   rw 53 (q8 c4) ∷
   rw⁻ 54 (q7 c4) ∷
   rw⁻ 55 (q9 c4) ∷
   rw⁻ 51 (q5 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw⁻ 51 (q4 c4) ∷
   rw 0 (q47 c4) ∷
   rw 2 (q48 c4) ∷
   rw 5 (q49 c4) ∷
   rw 15 (q50 c4) ∷
   rw 5 (q48 c4) ∷
   rw 5 (q47 c4) ∷
   rw 7 (q48 c4) ∷
   rw 13 (q51 c4) ∷
   rw 14 (q50 c4) ∷
   rw 15 (q51 c4) ∷
   rw 15 (q52 c4) ∷
   rw 16 (q51 c4) ∷
   rw 16 (q53 c4) ∷
   rw 17 (q51 c4) ∷
   rw 18 (q51 c4) ∷
   rw 19 (q52 c4) ∷
   rw 20 (q51 c4) ∷ []) Eq.refl
