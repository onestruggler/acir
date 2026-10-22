{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD020 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D020 (Sᴰ : SD020) where

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
  lem-comm-CS13-CCZ024 : Ws → St 958
  lem-comm-CS13-CCZ024 = pickᴰ 0 Sᴰ
  lem-comm-CS23-CCZ014 : Ws → St 703
  lem-comm-CS23-CCZ014 = pickᴰ 1 Sᴰ
  lem-comm-CS24-CCZ013 : Ws → St 194
  lem-comm-CS24-CCZ013 = pickᴰ 2 Sᴰ
  lem-comm-CSd13-CCZ024 : Ws → St 960
  lem-comm-CSd13-CCZ024 = pickᴰ 3 Sᴰ
  lem-comm-CSd23-CCZ014 : Ws → St 704
  lem-comm-CSd23-CCZ014 = pickᴰ 4 Sᴰ
  lem-comm-CSd24-CCZ013 : Ws → St 204
  lem-comm-CSd24-CCZ013 = pickᴰ 5 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 6 Sᴰ
  lem-comm-CX14-TOFF023 : Ws → St 1056
  lem-comm-CX14-TOFF023 = pickᴰ 7 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 8 Sᴰ
  lem-comm-CX24-TOFF013 : Ws → St 1057
  lem-comm-CX24-TOFF013 = pickᴰ 9 Sᴰ
  lem-comm-CCZ014-CX23 : Ws → St 893
  lem-comm-CCZ014-CX23 = pickᴰ 10 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 11 Sᴰ
  lem-comm-CCZ024-CX31 : Ws → St 1058
  lem-comm-CCZ024-CX31 = pickᴰ 12 Sᴰ
  lem-comm-TOFF013-CX24 : Ws → St 1059
  lem-comm-TOFF013-CX24 = pickᴰ 13 Sᴰ
  lem-comm-TOFF213-CX04 : Ws → St 1028
  lem-comm-TOFF213-CX04 = pickᴰ 14 Sᴰ
  lem-comm-TOFF023-CX14 : Ws → St 1060
  lem-comm-TOFF023-CX14 = pickᴰ 15 Sᴰ
  lem-sym-ab-at132132 : Ws → St 1061
  lem-sym-ab-at132132 = pickᴰ 16 Sᴰ
  lem-box-tQ-at12233441 : Ws → St 312
  lem-box-tQ-at12233441 = pickᴰ 17 Sᴰ
  lem-box-tQ-at132132 : Ws → St 258
  lem-box-tQ-at132132 = pickᴰ 18 Sᴰ
  lem-box-tQ-at14213243 : Ws → St 313
  lem-box-tQ-at14213243 = pickᴰ 19 Sᴰ
  lem-P-box-at12233441 : Ws → St 1062
  lem-P-box-at12233441 = pickᴰ 20 Sᴰ
  lem-P-box-at122441 : Ws → St 1063
  lem-P-box-at122441 = pickᴰ 21 Sᴰ
  lem-P-box-at14213243 : Ws → St 1064
  lem-P-box-at14213243 = pickᴰ 22 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 994
  lem-box-cP-at0210243143 = pickᴰ 23 Sᴰ
  lem-box-cP-at12233441 : Ws → St 1065
  lem-box-cP-at12233441 = pickᴰ 24 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 25 Sᴰ
  lem-box-cP-at14213243 : Ws → St 1066
  lem-box-cP-at14213243 = pickᴰ 26 Sᴰ
  lem-box-cP-at2332 : Ws → St 1007
  lem-box-cP-at2332 = pickᴰ 27 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 28 Sᴰ
  lem-box-perm-1324-at03102132 : Ws → St 1067
  lem-box-perm-1324-at03102132 = pickᴰ 29 Sᴰ
  lem-sym-bc-at0330 : Ws → St 1015
  lem-sym-bc-at0330 = pickᴰ 30 Sᴰ
  lem-sym-bc-at2332 : Ws → St 1068
  lem-sym-bc-at2332 = pickᴰ 31 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 52 c4
  q3 : Ws → Eqn
  q3 c4 = wlE 206 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (Toff023 ∷ X4 ∷ []) (X4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q5 : Ws → Eqn
  q5 c4 = wlE 207 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = wpE 53 c4
  q7 : Ws → Eqn
  q7 c4 = wpE 54 c4
  q8 : Ws → Eqn
  q8 c4 = sE 704 (lem-comm-CSd23-CCZ014 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 703 (lem-comm-CS23-CCZ014 c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 55 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 208 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 209 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 60 c4
  q14 : Ws → Eqn
  q14 c4 = wlE 219 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 217 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = wpE 61 c4
  q17 : Ws → Eqn
  q17 c4 = wpE 62 c4
  q18 : Ws → Eqn
  q18 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
  q19 : Ws → Eqn
  q19 c4 = wpE 63 c4
  q20 : Ws → Eqn
  q20 c4 = wpE 64 c4
  q21 : Ws → Eqn
  q21 c4 = wpE 65 c4
  q22 : Ws → Eqn
  q22 c4 = wpE 68 c4
  q23 : Ws → Eqn
  q23 c4 = wpE 71 c4
  q24 : Ws → Eqn
  q24 c4 = wlE 220 (lit c4)
  q25 : Ws → Eqn
  q25 c4 = wlE 221 (lit c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1056 (lem-comm-CX14-TOFF023 c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 69 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 70 c4
  q29 : Ws → Eqn
  q29 c4 = wpE 72 c4
  q30 : Ws → Eqn
  q30 c4 = wpE 74 c4
  q31 : Ws → Eqn
  q31 c4 = wlE 222 (lit c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 999 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = wlE 181 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = wlE 1000 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 263 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 894 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 1001 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 1002 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 805 c4
  q40 : Ws → Eqn
  q40 c4 = wpE 381 c4
  q41 : Ws → Eqn
  q41 c4 = sE 893 (lem-comm-CCZ014-CX23 c4)
  q42 : Ws → Eqn
  q42 c4 = wpE 806 c4
  q43 : Ws → Eqn
  q43 c4 = wlE 1003 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = sE 1060 (lem-comm-TOFF023-CX14 c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 380 c4
  q46 : Ws → Eqn
  q46 c4 = wlE 1004 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 211 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 896 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wlE 1005 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = wlE 900 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wlE 1006 (lit c4)

-- F4-CS1-CS1: 286 steps
lem-F4-CS1-CS1 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS1 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
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
   rw⁻ 5 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw⁻ 4 (q21 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw⁻ 13 (q16 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw 11 (q18 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw 9 (q18 c4) ∷
   rw⁻ 8 (q20 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 8 (q15 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 8 (q24 c4) ∷
   rw 12 (q25 c4) ∷
   rw 11 (q26 c4) ∷
   rw 10 (q27 c4) ∷
   rw 9 (q26 c4) ∷
   rw 8 (q28 c4) ∷
   rw⁻ 9 (q24 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw⁻ 8 (q30 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw 4 (q31 c4) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 6 (q31 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 2 (q15 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 3 (q22 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q18 c4) ∷
   rw⁻ 8 (q19 c4) ∷
   rw 7 (q18 c4) ∷
   rw⁻ 6 (q20 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 6 (q15 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw 6 (q24 c4) ∷
   rw 10 (q25 c4) ∷
   rw 9 (q26 c4) ∷
   rw 8 (q27 c4) ∷
   rw 7 (q26 c4) ∷
   rw 6 (q28 c4) ∷
   rw⁻ 7 (q24 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw⁻ 6 (q30 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 1 (q4 c4) ∷
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
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 2 (q5 c4) ∷
   rw⁻ 6 (q6 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw⁻ 3 (q7 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 3 (q5 c4) ∷
   rw 3 (q12 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 8 (q6 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw⁻ 5 (q7 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 5 (q5 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 3 (q32 c4) ∷
   rw 10 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw 5 (q35 c4) ∷
   re 4 1 (Sb0-1-3-2 ∷ []) ∷
   re 6 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 2 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 3 (q36 c4) ∷
   re 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 4 1 (CS13 ∷ []) ∷
   re 6 1 (CS13⁻ ∷ []) ∷
   rw⁻ 3 (q37 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw 7 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw 6 (q41 c4) ∷
   rw 7 (q42 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 9 (q21 c4) ∷
   rw 10 (q20 c4) ∷
   rw 11 (q41 c4) ∷
   rw 12 (q19 c4) ∷
   rw 13 (q41 c4) ∷
   rw 14 (q17 c4) ∷
   rw 15 (q16 c4) ∷
   rw 9 (q15 c4) ∷
   rw⁻ 3 (q43 c4) ∷
   rw 5 (q24 c4) ∷
   rw⁻ 4 (q28 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 6 (q27 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q25 c4) ∷
   rw⁻ 4 (q24 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw 7 (q29 c4) ∷
   rw 9 (q24 c4) ∷
   rw⁻ 8 (q28 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw 9 (q39 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw 3 (q46 c4) ∷
   rw 2 (q41 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 3 (q21 c4) ∷
   rw 4 (q20 c4) ∷
   rw 5 (q41 c4) ∷
   rw 6 (q19 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q17 c4) ∷
   rw 9 (q16 c4) ∷
   rw 3 (q15 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 1 (q47 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 2 (q48 c4) ∷
   rw⁻ 5 (q36 c4) ∷
   re 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 6 1 (CS13 ∷ []) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q37 c4) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 9 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 8 (q41 c4) ∷
   rw 9 (q42 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 11 (q21 c4) ∷
   rw 12 (q20 c4) ∷
   rw 13 (q41 c4) ∷
   rw 14 (q19 c4) ∷
   rw 15 (q41 c4) ∷
   rw 16 (q17 c4) ∷
   rw 17 (q16 c4) ∷
   rw 11 (q15 c4) ∷
   rw⁻ 5 (q43 c4) ∷
   rw 7 (q24 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 9 (q29 c4) ∷
   rw 11 (q24 c4) ∷
   rw⁻ 10 (q28 c4) ∷
   rw 11 (q44 c4) ∷
   rw⁻ 12 (q27 c4) ∷
   rw 13 (q44 c4) ∷
   rw⁻ 14 (q25 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw 11 (q39 c4) ∷
   rw⁻ 5 (q45 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw 5 (q46 c4) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q20 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q41 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q16 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 3 (q47 c4) ∷
   rw⁻ 6 (q50 c4) ∷
   re 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q51 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw 7 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw 5 (q13 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   re 8 1 (Sb0-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 6 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 4 (q50 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = sE 1064 (lem-P-box-at14213243 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 1066 (lem-box-cP-at14213243 c4)
  q54 : Ws → Eqn
  q54 c4 = wlE 203 (lit c4)
  q55 : Ws → Eqn
  q55 c4 = sE 312 (lem-box-tQ-at12233441 c4)

-- pairs @14213243: 4 steps
lem-pairs-at14213243 : Ws → ⟪ (Bx0-4123 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2341 ∷ []) ⟫ʷ
lem-pairs-at14213243 c4 = derive (Bx0-4123 ∷ []) (Bx0-2341 ∷ [])
  (rw⁻ 0 (q52 c4) ∷
   rw 1 (q53 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 0 (q55 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = sE 1062 (lem-P-box-at12233441 c4)
  q57 : Ws → Eqn
  q57 c4 = sE 1065 (lem-box-cP-at12233441 c4)
  q58 : Ws → Eqn
  q58 c4 = wpE 51 c4
  q59 : Ws → Eqn
  q59 c4 = sE 313 (lem-box-tQ-at14213243 c4)

-- pairs @12233441: 4 steps
lem-pairs-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-pairs-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-4123 ∷ [])
  (rw⁻ 0 (q56 c4) ∷
   rw 1 (q57 c4) ∷
   rw 4 (q58 c4) ∷
   rw⁻ 0 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = sE 1063 (lem-P-box-at122441 c4)
  q61 : Ws → Eqn
  q61 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 229 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = sE 258 (lem-box-tQ-at132132 c4)

-- pairs @122441: 4 steps
lem-pairs-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3124 ∷ []) ⟫ʷ
lem-pairs-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-3124 ∷ [])
  (rw⁻ 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 4 (q62 c4) ∷
   rw⁻ 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = wpE 20 c4
  q65 : Ws → Eqn
  q65 c4 = wlE 232 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (Toff013 ∷ X4 ∷ []) (X4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))
  q67 : Ws → Eqn
  q67 c4 = wlE 242 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 81 c4
  q69 : Ws → Eqn
  q69 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q70 : Ws → Eqn
  q70 c4 = wpE 91 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 92 c4
  q72 : Ws → Eqn
  q72 c4 = wpE 23 c4
  q73 : Ws → Eqn
  q73 c4 = wlE 185 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = wlE 234 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = wpE 87 c4
  q76 : Ws → Eqn
  q76 c4 = wlE 244 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 241 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = wpE 88 c4
  q79 : Ws → Eqn
  q79 c4 = wpE 34 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 35 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 36 c4
  q82 : Ws → Eqn
  q82 c4 = wpE 89 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 93 c4
  q84 : Ws → Eqn
  q84 c4 = wpE 96 c4
  q85 : Ws → Eqn
  q85 c4 = wlE 245 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 246 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = sE 1057 (lem-comm-CX24-TOFF013 c4)
  q88 : Ws → Eqn
  q88 c4 = wpE 94 c4
  q89 : Ws → Eqn
  q89 c4 = wpE 95 c4
  q90 : Ws → Eqn
  q90 c4 = wpE 97 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 842 c4
  q92 : Ws → Eqn
  q92 c4 = wlE 247 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = wlE 1036 (lit c4)
  q94 : Ws → Eqn
  q94 c4 = wlE 1037 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = wlE 305 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = wlE 975 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = wlE 1038 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = wlE 1039 (lit c4)
  q99 : Ws → Eqn
  q99 c4 = wpE 843 c4
  q100 : Ws → Eqn
  q100 c4 = wpE 844 c4
  q101 : Ws → Eqn
  q101 c4 = sE 1058 (lem-comm-CCZ024-CX31 c4)
  q102 : Ws → Eqn
  q102 c4 = wpE 845 c4
  q103 : Ws → Eqn
  q103 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 1040 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = sE 1059 (lem-comm-TOFF013-CX24 c4)
  q106 : Ws → Eqn
  q106 c4 = wpE 846 c4
  q107 : Ws → Eqn
  q107 c4 = wlE 1041 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 235 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 980 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 1042 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wlE 984 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = wlE 1043 (lit c4)

-- F4-CS2-CS2: 286 steps
lem-F4-CS2-CS2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS2 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 10 (q68 c4) ∷
   rw 9 (q69 c4) ∷
   rw⁻ 8 (q70 c4) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 6 (q71 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw⁻ 5 (q72 c4) ∷
   rw⁻ 4 (q64 c4) ∷
   rw 5 (q73 c4) ∷
   rw 6 (q74 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 6 (q61 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   rw 6 (q76 c4) ∷
   rw⁻ 7 (q75 c4) ∷
   rw 8 (q76 c4) ∷
   rw⁻ 5 (q61 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 4 (q77 c4) ∷
   rw⁻ 10 (q78 c4) ∷
   rw⁻ 9 (q79 c4) ∷
   rw 8 (q69 c4) ∷
   rw⁻ 7 (q80 c4) ∷
   rw 6 (q69 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 5 (q77 c4) ∷
   rw⁻ 5 (q83 c4) ∷
   rw⁻ 7 (q77 c4) ∷
   rw⁻ 13 (q78 c4) ∷
   rw⁻ 12 (q79 c4) ∷
   rw 11 (q69 c4) ∷
   rw⁻ 10 (q80 c4) ∷
   rw 9 (q69 c4) ∷
   rw⁻ 8 (q81 c4) ∷
   rw⁻ 7 (q82 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   rw 8 (q85 c4) ∷
   rw 12 (q86 c4) ∷
   rw 11 (q87 c4) ∷
   rw 10 (q88 c4) ∷
   rw 9 (q87 c4) ∷
   rw 8 (q89 c4) ∷
   rw⁻ 9 (q85 c4) ∷
   rw⁻ 7 (q90 c4) ∷
   rw⁻ 8 (q91 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   re 3 1 (CS12 ∷ []) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw 4 (q92 c4) ∷
   rw⁻ 5 (q68 c4) ∷
   rw 6 (q92 c4) ∷
   rw⁻ 3 (q61 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 2 (q77 c4) ∷
   rw⁻ 8 (q78 c4) ∷
   rw⁻ 7 (q79 c4) ∷
   rw 6 (q69 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   rw 4 (q69 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 2 (q82 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 5 (q77 c4) ∷
   rw⁻ 11 (q78 c4) ∷
   rw⁻ 10 (q79 c4) ∷
   rw 9 (q69 c4) ∷
   rw⁻ 8 (q80 c4) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 6 (q81 c4) ∷
   rw⁻ 5 (q82 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw⁻ 7 (q83 c4) ∷
   rw 6 (q85 c4) ∷
   rw 10 (q86 c4) ∷
   rw 9 (q87 c4) ∷
   rw 8 (q88 c4) ∷
   rw 7 (q87 c4) ∷
   rw 6 (q89 c4) ∷
   rw⁻ 7 (q85 c4) ∷
   rw⁻ 5 (q90 c4) ∷
   rw⁻ 6 (q91 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 1 (q61 c4) ∷
   rw⁻ 0 (q64 c4) ∷
   rw 2 (q65 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw⁻ 3 (q72 c4) ∷
   rw⁻ 2 (q64 c4) ∷
   rw 3 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw⁻ 0 (q61 c4) ∷
   rw 3 (q61 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 2 (q71 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   rw 3 (q74 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 8 (q68 c4) ∷
   rw 7 (q69 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 4 (q71 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw 5 (q74 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 3 (q93 c4) ∷
   rw 10 (q33 c4) ∷
   rw 3 (q94 c4) ∷
   rw 5 (q95 c4) ∷
   re 4 1 (Sb0-2-1-3 ∷ []) ∷
   re 6 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 2 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 3 (q96 c4) ∷
   re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 6 1 (CS12⁻ ∷ []) ∷
   rw⁻ 3 (q97 c4) ∷
   rw 2 (q61 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   rw 7 (q99 c4) ∷
   rw 4 (q100 c4) ∷
   rw 6 (q101 c4) ∷
   rw 7 (q102 c4) ∷
   rw⁻ 10 (q77 c4) ∷
   rw 9 (q82 c4) ∷
   rw 10 (q81 c4) ∷
   rw 11 (q103 c4) ∷
   rw 12 (q80 c4) ∷
   rw 13 (q103 c4) ∷
   rw 14 (q79 c4) ∷
   rw 15 (q78 c4) ∷
   rw 9 (q77 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 5 (q85 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 5 (q105 c4) ∷
   rw⁻ 6 (q88 c4) ∷
   rw 7 (q105 c4) ∷
   rw⁻ 8 (q86 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   rw 7 (q90 c4) ∷
   rw 9 (q85 c4) ∷
   rw⁻ 8 (q89 c4) ∷
   rw 9 (q105 c4) ∷
   rw⁻ 10 (q88 c4) ∷
   rw 11 (q105 c4) ∷
   rw⁻ 12 (q86 c4) ∷
   rw⁻ 8 (q85 c4) ∷
   rw 9 (q99 c4) ∷
   rw⁻ 3 (q106 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw 3 (q107 c4) ∷
   rw 2 (q101 c4) ∷
   rw⁻ 4 (q77 c4) ∷
   rw 3 (q82 c4) ∷
   rw 4 (q81 c4) ∷
   rw 5 (q103 c4) ∷
   rw 6 (q80 c4) ∷
   rw 7 (q103 c4) ∷
   rw 8 (q79 c4) ∷
   rw 9 (q78 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 1 (q108 c4) ∷
   rw⁻ 4 (q109 c4) ∷
   re 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw⁻ 4 (q110 c4) ∷
   rw 3 (q61 c4) ∷
   rw⁻ 6 (q92 c4) ∷
   rw 5 (q68 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw 3 (q68 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 2 (q109 c4) ∷
   rw⁻ 5 (q96 c4) ∷
   re 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 6 1 (CS12 ∷ []) ∷
   re 8 1 (CS12⁻ ∷ []) ∷
   rw⁻ 5 (q97 c4) ∷
   rw 4 (q61 c4) ∷
   rw⁻ 7 (q98 c4) ∷
   rw 9 (q99 c4) ∷
   rw 6 (q100 c4) ∷
   rw 8 (q101 c4) ∷
   rw 9 (q102 c4) ∷
   rw⁻ 12 (q77 c4) ∷
   rw 11 (q82 c4) ∷
   rw 12 (q81 c4) ∷
   rw 13 (q103 c4) ∷
   rw 14 (q80 c4) ∷
   rw 15 (q103 c4) ∷
   rw 16 (q79 c4) ∷
   rw 17 (q78 c4) ∷
   rw 11 (q77 c4) ∷
   rw⁻ 5 (q104 c4) ∷
   rw 7 (q85 c4) ∷
   rw⁻ 6 (q89 c4) ∷
   rw 7 (q105 c4) ∷
   rw⁻ 8 (q88 c4) ∷
   rw 9 (q105 c4) ∷
   rw⁻ 10 (q86 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw⁻ 7 (q98 c4) ∷
   rw 9 (q90 c4) ∷
   rw 11 (q85 c4) ∷
   rw⁻ 10 (q89 c4) ∷
   rw 11 (q105 c4) ∷
   rw⁻ 12 (q88 c4) ∷
   rw 13 (q105 c4) ∷
   rw⁻ 14 (q86 c4) ∷
   rw⁻ 10 (q85 c4) ∷
   rw 11 (q99 c4) ∷
   rw⁻ 5 (q106 c4) ∷
   rw⁻ 7 (q91 c4) ∷
   rw 5 (q107 c4) ∷
   rw 4 (q101 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw 5 (q82 c4) ∷
   rw 6 (q81 c4) ∷
   rw 7 (q103 c4) ∷
   rw 8 (q80 c4) ∷
   rw 9 (q103 c4) ∷
   rw 10 (q79 c4) ∷
   rw 11 (q78 c4) ∷
   rw 5 (q77 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 3 (q108 c4) ∷
   rw⁻ 6 (q111 c4) ∷
   re 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 7 1 (CS12 ∷ []) ∷
   re 9 1 (CS12⁻ ∷ []) ∷
   rw⁻ 6 (q112 c4) ∷
   rw 5 (q61 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw 7 (q75 c4) ∷
   rw⁻ 6 (q76 c4) ∷
   rw 5 (q75 c4) ∷
   rw⁻ 6 (q61 c4) ∷
   re 8 1 (Sb0-2-1-3 ∷ []) ∷
   re 10 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 6 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 4 (q111 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = sE 994 (lem-box-cP-at0210243143 c4)
  q114 : Ws → Eqn
  q114 c4 = wpE 617 c4
  q115 : Ws → Eqn
  q115 c4 = wlE 727 (lit c4)
  q116 : Ws → Eqn
  q116 c4 = wpE 849 c4

-- F2-I-CS0: 13 steps
lem-F2-I-CS0 : Ws → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS0 c4 = derive (S4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 1 (q113 c4) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 1 (q115 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 3 (q115 c4) ∷
   rw⁻ 0 (q113 c4) ∷
   rw 1 (q116 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = wpE 633 c4
  q118 : Ws → Eqn
  q118 c4 = wpE 632 c4
  q119 : Ws → Eqn
  q119 c4 = wlE 1050 (lit c4)

-- F2-I-CS1: 13 steps
lem-F2-I-CS1 : Ws → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS1 c4 = derive (S4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q117 c4) ∷
   rw 1 (q118 c4) ∷
   rw⁻ 2 (q117 c4) ∷
   rw 3 (q118 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q119 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q120 : Ws → Eqn
  q120 c4 = wpE 647 c4
  q121 : Ws → Eqn
  q121 c4 = wlE 1051 (lit c4)

-- F2-I-CS2: 13 steps
lem-F2-I-CS2 : Ws → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS2 c4 = derive (S4 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 1 (q61 c4) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 1 (q120 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 3 (q120 c4) ∷
   rw⁻ 0 (q61 c4) ∷
   rw 1 (q121 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = wpE 785 c4
  q123 : Ws → Eqn
  q123 c4 = wlE 1056 (lit c4)

-- F2-S1-CS2: 13 steps
lem-F2-S1-CS2 : Ws → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-CS2 c4 = derive (CS14 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 1 (q61 c4) ∷
   rw⁻ 0 (q79 c4) ∷
   rw 1 (q122 c4) ∷
   rw⁻ 2 (q79 c4) ∷
   rw 3 (q122 c4) ∷
   rw⁻ 0 (q61 c4) ∷
   rw 1 (q123 c4) ∷
   re 2 1 (Sb0-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 0 5 (Sb0-2-43-1 ∷ []) ∷ []) Eq.refl

private
  q124 : Ws → Eqn
  q124 c4 = wlE 808 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wpE 866 c4

-- F2-S3-CS0: 13 steps
lem-F2-S3-CS0 : Ws → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-CS0 c4 = derive (CS34 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 1 (q113 c4) ∷
   rw⁻ 0 (q81 c4) ∷
   rw 1 (q124 c4) ∷
   rw⁻ 2 (q81 c4) ∷
   rw 3 (q124 c4) ∷
   rw⁻ 0 (q113 c4) ∷
   rw 1 (q125 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = wpE 725 c4
  q127 : Ws → Eqn
  q127 c4 = wlE 1062 (lit c4)

-- F2-S3-CS1: 13 steps
lem-F2-S3-CS1 : Ws → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-CS1 c4 = derive (CS34 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw⁻ 0 (q20 c4) ∷
   rw 1 (q126 c4) ∷
   rw⁻ 2 (q20 c4) ∷
   rw 3 (q126 c4) ∷
   rw⁻ 0 (q1 c4) ∷
   rw 1 (q127 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = wpE 39 c4
  q129 : Ws → Eqn
  q129 c4 = wlE 1081 (lit c4)
  q130 : Ws → Eqn
  q130 c4 = wlE 905 (lit c4)
  q131 : Ws → Eqn
  q131 c4 = wpE 756 c4
  q132 : Ws → Eqn
  q132 c4 = sE 960 (lem-comm-CSd13-CCZ024 c4)
  q133 : Ws → Eqn
  q133 c4 = sE 958 (lem-comm-CS13-CCZ024 c4)
  q134 : Ws → Eqn
  q134 c4 = wlE 906 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = wlE 910 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wlE 1082 (lit c4)

-- CSu-box-4 @122441: 17 steps
lem-CSu-box-4-at122441 : Ws → ⟪ (CS01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS01 ∷ []) ⟫ʷ
lem-CSu-box-4-at122441 c4 = derive (CS01 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS01 ∷ [])
  (rw 1 (q61 c4) ∷
   rw⁻ 0 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw 4 (q130 c4) ∷
   rw⁻ 8 (q128 c4) ∷
   rw⁻ 7 (q131 c4) ∷
   rw 6 (q132 c4) ∷
   rw⁻ 5 (q131 c4) ∷
   rw 4 (q133 c4) ∷
   rw⁻ 5 (q130 c4) ∷
   rw 3 (q133 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   rw 5 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw 3 (q129 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 0 (q61 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = sE 1015 (lem-sym-bc-at0330 c4)

-- box-perm-1324 @0330: 1 steps
lem-box-perm-1324-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-1324-at0330 c4 = derive (Bx3-1204 ∷ []) (Bx3-1024 ∷ [])
  (rw 0 (q137 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = sE 1061 (lem-sym-ab-at132132 c4)
  q139 : Ws → Eqn
  q139 c4 = sE 1068 (lem-sym-bc-at2332 c4)

-- box-perm-2314 @132132: 2 steps
lem-box-perm-2314-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-2314-at132132 c4 = derive (Bx0-3124 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q138 c4) ∷
   rw 0 (q139 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = sE 1007 (lem-box-cP-at2332 c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 1086 (lit c4)
  q142 : Ws → Eqn
  q142 c4 = wpE 886 c4
  q143 : Ws → Eqn
  q143 c4 = wpE 887 c4
  q144 : Ws → Eqn
  q144 c4 = wlE 256 (lit c4)
  q145 : Ws → Eqn
  q145 c4 = wpE 299 c4
  q146 : Ws → Eqn
  q146 c4 = wlE 448 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = sE 204 (lem-comm-CSd24-CCZ013 c4)
  q148 : Ws → Eqn
  q148 c4 = sE 194 (lem-comm-CS24-CCZ013 c4)
  q149 : Ws → Eqn
  q149 c4 = wlE 1087 (lit c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 1088 (lit c4)
  q151 : Ws → Eqn
  q151 c4 = wpE 743 c4
  q152 : Ws → Eqn
  q152 c4 = wlE 1089 (lit c4)

-- Xb-box @2332: 18 steps
lem-Xb-box-at2332 : Ws → ⟪ (X3 ∷ Bx0-1324 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ
lem-Xb-box-at2332 c4 = derive (X3 ∷ Bx0-1324 ∷ X3 ∷ []) (Bx0-1324 ∷ CCZ124 ∷ [])
  (rw 1 (q140 c4) ∷
   rw⁻ 0 (q141 c4) ∷
   rw 2 (q142 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   rw 4 (q144 c4) ∷
   rw⁻ 8 (q145 c4) ∷
   rw⁻ 7 (q146 c4) ∷
   rw 6 (q147 c4) ∷
   rw⁻ 5 (q146 c4) ∷
   rw 4 (q148 c4) ∷
   rw⁻ 5 (q144 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw⁻ 2 (q141 c4) ∷
   rw 3 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 3 (q143 c4) ∷
   rw⁻ 0 (q140 c4) ∷
   rw⁻ 1 (q152 c4) ∷ []) Eq.refl

-- box-perm-1324 @2332: 1 steps
lem-box-perm-1324-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1324-at2332 c4 = derive (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q139 c4) ∷ []) Eq.refl

private
  q153 : Ws → Eqn
  q153 c4 = sE 1067 (lem-box-perm-1324-at03102132 c4)
  q154 : Ws → Eqn
  q154 c4 = wpE 901 c4

-- S-sym-ty: 8 steps
lem-S-sym-ty : Ws → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-21-4 ∷ []) ⟫ʷ
lem-S-sym-ty c4 = derive (Sb3-0-12-4 ∷ []) (Sb3-0-21-4 ∷ [])
  (re 0 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) ∷
   re 2 1 (CS04 ∷ []) ∷
   re 4 1 (CS04⁻ ∷ []) ∷
   rw 0 (q153 c4) ∷
   rw 1 (q154 c4) ∷
   re 2 1 (Sb3-0-4-1 ∷ []) ∷
   re 4 1 (Sb⁻3-0-4-1 ∷ []) ∷
   re 0 5 (Sb3-0-21-4 ∷ []) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = wlE 747 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = wpE 654 c4
  q157 : Ws → Eqn
  q157 c4 = wlE 190 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = wpE 37 c4
  q159 : Ws → Eqn
  q159 c4 = wpE 33 c4
  q160 : Ws → Eqn
  q160 c4 = wlE 197 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = wpE 41 c4
  q162 : Ws → Eqn
  q162 c4 = wlE 195 (lit c4)
  q163 : Ws → Eqn
  q163 c4 = sE 1028 (lem-comm-TOFF213-CX04 c4)
  q164 : Ws → Eqn
  q164 c4 = wlE 194 (lit c4)
  q165 : Ws → Eqn
  q165 c4 = wlE 193 (lit c4)
  q166 : Ws → Eqn
  q166 c4 = wpE 44 c4
  q167 : Ws → Eqn
  q167 c4 = wpE 38 c4
  q168 : Ws → Eqn
  q168 c4 = wlE 196 (lit c4)
  q169 : Ws → Eqn
  q169 c4 = wpE 21 c4
  q170 : Ws → Eqn
  q170 c4 = wlE 191 (lit c4)
  q171 : Ws → Eqn
  q171 c4 = wpE 32 c4
  q172 : Ws → Eqn
  q172 c4 = wpE 651 c4
  q173 : Ws → Eqn
  q173 c4 = wpE 161 c4

-- nf-comm-CS-S0@0: 83 steps
lem-nf-comm-CS-S0at0 : Ws → ⟪ (CS04 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-nf-comm-CS-S0at0 c4 = derive (CS04 ∷ Sb2-0-41-3 ∷ []) (CS04 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 1 (q113 c4) ∷
   rw 4 (q155 c4) ∷
   rw 3 (q156 c4) ∷
   rw⁻ 6 (q157 c4) ∷
   rw 5 (q158 c4) ∷
   rw 6 (q81 c4) ∷
   rw 7 (q103 c4) ∷
   rw 8 (q80 c4) ∷
   rw 9 (q103 c4) ∷
   rw 10 (q79 c4) ∷
   rw 11 (q159 c4) ∷
   rw 5 (q157 c4) ∷
   rw 2 (q160 c4) ∷
   rw 4 (q161 c4) ∷
   rw⁻ 3 (q162 c4) ∷
   rw 4 (q163 c4) ∷
   rw⁻ 5 (q164 c4) ∷
   rw 6 (q163 c4) ∷
   rw⁻ 7 (q165 c4) ∷
   rw⁻ 3 (q161 c4) ∷
   rw 4 (q155 c4) ∷
   rw⁻ 2 (q166 c4) ∷
   rw⁻ 1 (q167 c4) ∷
   rw⁻ 3 (q157 c4) ∷
   rw 2 (q158 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q103 c4) ∷
   rw 5 (q80 c4) ∷
   rw 6 (q103 c4) ∷
   rw 7 (q79 c4) ∷
   rw 8 (q159 c4) ∷
   rw 2 (q157 c4) ∷
   rw⁻ 3 (q113 c4) ∷
   rw 3 (q113 c4) ∷
   rw⁻ 6 (q168 c4) ∷
   rw 5 (q169 c4) ∷
   rw⁻ 4 (q168 c4) ∷
   rw 3 (q169 c4) ∷
   rw⁻ 4 (q113 c4) ∷
   rw 4 (q113 c4) ∷
   rw 7 (q155 c4) ∷
   rw 6 (q156 c4) ∷
   rw⁻ 9 (q157 c4) ∷
   rw 8 (q158 c4) ∷
   rw 9 (q81 c4) ∷
   rw 10 (q103 c4) ∷
   rw 11 (q80 c4) ∷
   rw 12 (q103 c4) ∷
   rw 13 (q79 c4) ∷
   rw 14 (q159 c4) ∷
   rw 8 (q157 c4) ∷
   rw 5 (q160 c4) ∷
   rw 7 (q161 c4) ∷
   rw⁻ 6 (q162 c4) ∷
   rw 7 (q163 c4) ∷
   rw⁻ 8 (q164 c4) ∷
   rw 9 (q163 c4) ∷
   rw⁻ 10 (q165 c4) ∷
   rw⁻ 6 (q161 c4) ∷
   rw 7 (q155 c4) ∷
   rw⁻ 5 (q166 c4) ∷
   rw⁻ 4 (q167 c4) ∷
   rw⁻ 6 (q157 c4) ∷
   rw 5 (q158 c4) ∷
   rw 6 (q81 c4) ∷
   rw 7 (q103 c4) ∷
   rw 8 (q80 c4) ∷
   rw 9 (q103 c4) ∷
   rw 10 (q79 c4) ∷
   rw 11 (q159 c4) ∷
   rw 5 (q157 c4) ∷
   rw⁻ 6 (q113 c4) ∷
   rw 6 (q113 c4) ∷
   rw⁻ 9 (q170 c4) ∷
   rw 8 (q171 c4) ∷
   rw⁻ 7 (q170 c4) ∷
   rw 6 (q171 c4) ∷
   rw⁻ 7 (q113 c4) ∷
   rw 1 (q172 c4) ∷
   rw 3 (q173 c4) ∷ []) Eq.refl

private
  q174 : Ws → Eqn
  q174 c4 = wpE 66 c4

-- nf-comm-CS-S0@1: 83 steps
lem-nf-comm-CS-S0at1 : Ws → ⟪ (CS14 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-nf-comm-CS-S0at1 c4 = derive (CS14 ∷ Sb0-1-42-3 ∷ []) (CS14 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw 4 (q39 c4) ∷
   rw 3 (q42 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q20 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q41 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q16 c4) ∷
   rw 5 (q15 c4) ∷
   rw 2 (q29 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw 4 (q44 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 6 (q44 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 2 (q30 c4) ∷
   rw 1 (q174 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw 2 (q21 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q41 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q41 c4) ∷
   rw 7 (q17 c4) ∷
   rw 8 (q16 c4) ∷
   rw 2 (q15 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   rw 5 (q6 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw 3 (q6 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 7 (q39 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 8 (q21 c4) ∷
   rw 9 (q20 c4) ∷
   rw 10 (q41 c4) ∷
   rw 11 (q19 c4) ∷
   rw 12 (q41 c4) ∷
   rw 13 (q17 c4) ∷
   rw 14 (q16 c4) ∷
   rw 8 (q15 c4) ∷
   rw 5 (q29 c4) ∷
   rw 7 (q24 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 7 (q44 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 9 (q44 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw⁻ 6 (q24 c4) ∷
   rw 7 (q39 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw 4 (q174 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 5 (q21 c4) ∷
   rw 6 (q20 c4) ∷
   rw 7 (q41 c4) ∷
   rw 8 (q19 c4) ∷
   rw 9 (q41 c4) ∷
   rw 10 (q17 c4) ∷
   rw 11 (q16 c4) ∷
   rw 5 (q15 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 9 (q14 c4) ∷
   rw 8 (q13 c4) ∷
   rw⁻ 7 (q14 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 1 (q34 c4) ∷
   rw 3 (q35 c4) ∷ []) Eq.refl
