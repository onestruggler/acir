{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD045 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D045 (Sᴰ : SD045) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CSd13 ; lem-comm-CCZ024-CX13 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF014-CX23)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-CCZ023-CX14)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-cP-at12233441 : Ws → St 902
  lem-box-cP-at12233441 = pickᴰ 0 Sᴰ
  lem-box-cP-at122441 : Ws → St 850
  lem-box-cP-at122441 = pickᴰ 1 Sᴰ
  lem-box-perm-1324-at122441 : Ws → St 1078
  lem-box-perm-1324-at122441 = pickᴰ 2 Sᴰ
  lem-box2-at243243 : Ws → St 1083
  lem-box2-at243243 = pickᴰ 3 Sᴰ
  lem-box-perm-4132-at122441 : Ws → St 1350
  lem-box-perm-4132-at122441 = pickᴰ 4 Sᴰ
  lem-box-perm-4213-at122441 : Ws → St 1310
  lem-box-perm-4213-at122441 = pickᴰ 5 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wpE 816 c4
  q2 : Ws → Eqn
  q2 c4 = wlE 217 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = wpE 839 c4
  q4 : Ws → Eqn
  q4 c4 = wpE 1046 c4
  q5 : Ws → Eqn
  q5 c4 = wpE 669 c4
  q6 : Ws → Eqn
  q6 c4 = wlE 220 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = wpE 513 c4
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ023 ∷ CX14 ∷ []) (CX14 ∷ CCZ023 ∷ []) (lem-comm-CCZ023-CX14 (lit c4))
  q9 : Ws → Eqn
  q9 c4 = wpE 820 c4
  q10 : Ws → Eqn
  q10 c4 = wlE 621 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = wpE 821 c4
  q12 : Ws → Eqn
  q12 c4 = sE 902 (lem-box-cP-at12233441 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1078 (lem-box-perm-1324-at122441 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 850 (lem-box-cP-at122441 c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 907 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CCZ024 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = wlE 256 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (Toff013 ∷ CS24 ∷ []) (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4))
  q19 : Ws → Eqn
  q19 c4 = wlE 872 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = eqn (Toff013 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4))
  q21 : Ws → Eqn
  q21 c4 = wpE 785 c4
  q22 : Ws → Eqn
  q22 c4 = wpE 827 c4
  q23 : Ws → Eqn
  q23 c4 = wpE 819 c4
  q24 : Ws → Eqn
  q24 c4 = wpE 546 c4
  q25 : Ws → Eqn
  q25 c4 = eqn (Toff014 ∷ CX23 ∷ []) (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4))
  q26 : Ws → Eqn
  q26 c4 = wpE 818 c4
  q27 : Ws → Eqn
  q27 c4 = wpE 817 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 293 c4
  q29 : Ws → Eqn
  q29 c4 = wlE 166 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 36 c4
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = wpE 35 c4
  q33 : Ws → Eqn
  q33 c4 = wpE 34 c4
  q34 : Ws → Eqn
  q34 c4 = wlE 1376 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 743 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wpE 95 c4
  q37 : Ws → Eqn
  q37 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = wpE 94 c4
  q39 : Ws → Eqn
  q39 c4 = wlE 246 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wlE 1375 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = wpE 790 c4
  q42 : Ws → Eqn
  q42 c4 = wpE 1214 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 109 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 1215 c4
  q45 : Ws → Eqn
  q45 c4 = sE 1310 (lem-box-perm-4213-at122441 c4)
  q46 : Ws → Eqn
  q46 c4 = sE 1083 (lem-box2-at243243 c4)
  q47 : Ws → Eqn
  q47 c4 = wpE 843 c4
  q48 : Ws → Eqn
  q48 c4 = wpE 845 c4
  q49 : Ws → Eqn
  q49 c4 = wlE 241 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 89 c4
  q51 : Ws → Eqn
  q51 c4 = wpE 88 c4
  q52 : Ws → Eqn
  q52 c4 = wpE 97 c4
  q53 : Ws → Eqn
  q53 c4 = wlE 245 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 842 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 90 c4
  q56 : Ws → Eqn
  q56 c4 = wlE 247 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 81 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 244 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = wpE 87 c4
  q60 : Ws → Eqn
  q60 c4 = wlE 888 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 654 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 1213 c4
  q63 : Ws → Eqn
  q63 c4 = wpE 38 c4
  q64 : Ws → Eqn
  q64 c4 = wpE 753 c4

-- L-CCZ-1 part1: 500 steps
lem-L-CCZ-1-part1 : Ws → ⟪ (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ134 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ []) ⟫ʷ
lem-L-CCZ-1-part1 c4 = derive (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ134 ∷ Toff234 ∷ CCZ124 ∷ Toff324 ∷ Bx0-1423 ∷ []) (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ234 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ CCZ134 ∷ Toff324 ∷ CCZ024 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ124 ∷ Toff234 ∷ CCZ134 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ [])
  (rw⁻ 33 (q1 c4) ∷
   rw 27 (q2 c4) ∷
   rw⁻ 28 (q3 c4) ∷
   rw 26 (q4 c4) ∷
   rw 28 (q5 c4) ∷
   rw 30 (q6 c4) ∷
   rw 29 (q7 c4) ∷
   rw 30 (q8 c4) ∷
   rw 31 (q9 c4) ∷
   rw 32 (q8 c4) ∷
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
   rw 31 (q22 c4) ∷
   rw 31 (q17 c4) ∷
   rw 30 (q18 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw 32 (q20 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 34 (q21 c4) ∷
   rw⁻ 30 (q17 c4) ∷
   rw 29 (q22 c4) ∷
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
   rw 32 (q5 c4) ∷
   rw 34 (q6 c4) ∷
   rw 33 (q7 c4) ∷
   rw 34 (q8 c4) ∷
   rw 35 (q9 c4) ∷
   rw 36 (q8 c4) ∷
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
   rw 37 (q22 c4) ∷
   rw 37 (q17 c4) ∷
   rw 36 (q18 c4) ∷
   rw⁻ 37 (q19 c4) ∷
   rw 38 (q20 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   rw⁻ 40 (q21 c4) ∷
   rw⁻ 36 (q17 c4) ∷
   rw 35 (q22 c4) ∷
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
   rw 38 (q5 c4) ∷
   rw 40 (q6 c4) ∷
   rw 39 (q7 c4) ∷
   rw 40 (q8 c4) ∷
   rw 41 (q9 c4) ∷
   rw 42 (q8 c4) ∷
   rw 43 (q10 c4) ∷
   rw⁻ 39 (q6 c4) ∷
   rw 36 (q11 c4) ∷
   rw⁻ 38 (q12 c4) ∷
   rw⁻ 38 (q13 c4) ∷
   rw 38 (q45 c4) ∷
   rw 38 (q46 c4) ∷
   rw 0 (q14 c4) ∷
   rw 3 (q47 c4) ∷
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
   rw 1 (q52 c4) ∷
   rw 3 (q53 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 5 (q37 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 1 (q54 c4) ∷
   rw 0 (q55 c4) ∷
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
   rw 6 (q47 c4) ∷
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
   rw 4 (q52 c4) ∷
   rw 6 (q53 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   rw 6 (q37 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 8 (q37 c4) ∷
   rw⁻ 9 (q39 c4) ∷
   rw⁻ 5 (q53 c4) ∷
   rw 6 (q47 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 3 (q55 c4) ∷
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
   rw 10 (q55 c4) ∷
   rw 10 (q53 c4) ∷
   rw⁻ 9 (q36 c4) ∷
   rw 10 (q37 c4) ∷
   rw⁻ 11 (q38 c4) ∷
   rw 12 (q37 c4) ∷
   rw⁻ 13 (q39 c4) ∷
   rw⁻ 9 (q53 c4) ∷
   rw 8 (q55 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 13 (q53 c4) ∷
   rw⁻ 12 (q36 c4) ∷
   rw 13 (q37 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 15 (q37 c4) ∷
   rw⁻ 16 (q39 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw 11 (q55 c4) ∷
   rw 11 (q53 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw 11 (q37 c4) ∷
   rw⁻ 12 (q38 c4) ∷
   rw 13 (q37 c4) ∷
   rw⁻ 14 (q39 c4) ∷
   rw⁻ 10 (q53 c4) ∷
   rw 9 (q55 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 13 (q47 c4) ∷
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
   rw 11 (q52 c4) ∷
   rw 13 (q53 c4) ∷
   rw⁻ 12 (q36 c4) ∷
   rw 13 (q37 c4) ∷
   rw⁻ 14 (q38 c4) ∷
   rw 15 (q37 c4) ∷
   rw⁻ 16 (q39 c4) ∷
   rw⁻ 12 (q53 c4) ∷
   rw 13 (q47 c4) ∷
   rw⁻ 11 (q54 c4) ∷
   rw 10 (q55 c4) ∷
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
   rw 15 (q55 c4) ∷
   rw 15 (q53 c4) ∷
   rw⁻ 14 (q36 c4) ∷
   rw 15 (q37 c4) ∷
   rw⁻ 16 (q38 c4) ∷
   rw 17 (q37 c4) ∷
   rw⁻ 18 (q39 c4) ∷
   rw⁻ 14 (q53 c4) ∷
   rw 13 (q55 c4) ∷
   rw⁻ 14 (q14 c4) ∷
   rw 14 (q14 c4) ∷
   rw 17 (q47 c4) ∷
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
   rw 15 (q52 c4) ∷
   rw 17 (q53 c4) ∷
   rw⁻ 16 (q36 c4) ∷
   rw 17 (q37 c4) ∷
   rw⁻ 18 (q38 c4) ∷
   rw 19 (q37 c4) ∷
   rw⁻ 20 (q39 c4) ∷
   rw⁻ 16 (q53 c4) ∷
   rw 17 (q47 c4) ∷
   rw⁻ 15 (q54 c4) ∷
   rw 14 (q55 c4) ∷
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
   rw 22 (q5 c4) ∷
   rw 24 (q6 c4) ∷
   rw 23 (q7 c4) ∷
   rw 24 (q8 c4) ∷
   rw 25 (q9 c4) ∷
   rw 26 (q8 c4) ∷
   rw 27 (q10 c4) ∷
   rw⁻ 23 (q6 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wlE 431 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 321 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = wlE 450 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 263 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wlE 1378 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = sE 1350 (lem-box-perm-4132-at122441 c4)

-- L-CCZ-1 part3: 6 steps
lem-L-CCZ-1-part3 : Ws → ⟪ (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-L-CCZ-1-part3 c4 = derive (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Toff214 ∷ CCZ134 ∷ Toff324 ∷ Toff234 ∷ Toff324 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CCZ124 ∷ CCZ134 ∷ Toff234 ∷ CCZ134 ∷ CCZ134 ∷ CCZ124 ∷ Toff324 ∷ CCZ124 ∷ CCZ124 ∷ Bx0-2431 ∷ []) (Bx0-1234 ∷ [])
  (rw 21 (q65 c4) ∷
   rw 22 (q66 c4) ∷
   rw 23 (q67 c4) ∷
   rw 24 (q68 c4) ∷
   rw 0 (q69 c4) ∷
   rw 0 (q70 c4) ∷ []) Eq.refl
