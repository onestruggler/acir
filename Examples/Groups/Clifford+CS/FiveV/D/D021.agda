{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D021 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.FiveV.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.FiveV.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-sym-ab-at0210243143 ; lem-sym-ab-at0214203143 ; lem-sym-ab-at03102132 ; lem-sym-ab-at0314203142 ; lem-sym-ab-at13243142 ; lem-sym-ab-at14233142 ; lem-sym-ab-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-sym-ab-at0213243041 ; lem-sym-ab-at0214233041 ; lem-sym-ab-at03122031 ; lem-sym-ab-at03122130 ; lem-sym-ab-at0312243041 ; lem-sym-ab-at0314213240 ; lem-sym-ab-at03143041 ; lem-sym-ab-at03243240 ; lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-sym-ab-at02132031 ; lem-sym-ab-at02132130)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-tQ-at03102132 ; lem-box-tQ-at14233241)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-tQ-at0310213442)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-tQ-at0214203143 ; lem-box-tQ-at0310243142 ; lem-box-tQ-at0314203142 ; lem-box-tQ-at0314213042 ; lem-box-tQ-at033440 ; lem-box-tQ-at13213442 ; lem-box-tQ-at1331 ; lem-box-tQ-at143143)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-box-tQ-at02102441 ; lem-box-tQ-at02132130 ; lem-box-tQ-at02142041 ; lem-box-tQ-at02233440 ; lem-box-tQ-at0310243241 ; lem-box-tQ-at031031 ; lem-box-tQ-at03103441 ; lem-box-tQ-at03122031 ; lem-box-tQ-at0312203441 ; lem-box-tQ-at03122130 ; lem-box-tQ-at0314203241 ; lem-box-tQ-at0314213240 ; lem-box-tQ-at03143140 ; lem-box-tQ-at03243042 ; lem-box-tQ-at03243240 ; lem-box-tQ-at142142)
open import Examples.Groups.Clifford+CS.FiveV.D.D010 using (lem-P-box-at0214203143)
open import Examples.Groups.Clifford+CS.FiveV.D.D011 using (lem-P-box-at02233440 ; lem-P-box-at03103441 ; lem-P-box-at0312203441 ; lem-P-box-at0314203142 ; lem-P-box-at0314213042 ; lem-P-box-at0314213240 ; lem-P-box-at03243240 ; lem-P-box-at033440 ; lem-P-box-at12213443 ; lem-P-box-at1441 ; lem-P-box-at233442 ; lem-t-cP-at0310243142 ; lem-t-cP-at03143140 ; lem-t-cP-at03243240)
open import Examples.Groups.Clifford+CS.FiveV.D.D012 using (lem-P-box-at02102441 ; lem-P-box-at02132130 ; lem-P-box-at0310243241 ; lem-P-box-at031031 ; lem-P-box-at03122130 ; lem-P-box-at0312243041 ; lem-P-box-at03143041 ; lem-P-box-at03243042 ; lem-P-box-at2442 ; lem-t-cP-at02142041 ; lem-t-cP-at0314203241 ; lem-t-cP-at033440 ; lem-t-cP-at142142)
open import Examples.Groups.Clifford+CS.FiveV.D.D015 using (lem-sym-bc-at0210213443 ; lem-sym-bc-at0214233041)
open import Examples.Groups.Clifford+CS.FiveV.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at02102441 ; lem-box-cP-at02132130 ; lem-box-cP-at0214203143 ; lem-box-cP-at02233440 ; lem-box-cP-at022440 ; lem-box-cP-at0310243142 ; lem-box-cP-at0310243241 ; lem-box-cP-at031031 ; lem-box-cP-at03103441 ; lem-box-cP-at0312203441 ; lem-box-cP-at03122130 ; lem-box-cP-at0312243041 ; lem-box-cP-at0314203142 ; lem-box-cP-at0314213042 ; lem-box-cP-at0314213240 ; lem-box-cP-at03143041 ; lem-box-cP-at03143140 ; lem-box-cP-at03243240 ; lem-box-cP-at033440 ; lem-box-cP-at12213443 ; lem-box-cP-at12243143 ; lem-box-cP-at122441 ; lem-box-cP-at13213442 ; lem-box-cP-at1441 ; lem-box-cP-at233442 ; lem-box-cP-at243243 ; lem-box-cP-at2442 ; lem-pairs-at021021 ; lem-pairs-at0210213443 ; lem-pairs-at0213243041 ; lem-pairs-at0214233041 ; lem-pairs-at03102132 ; lem-pairs-at0310213442 ; lem-pairs-at13243142 ; lem-pairs-at14233142 ; lem-sym-bc-at0210233441 ; lem-sym-bc-at0210243143 ; lem-sym-bc-at02102441 ; lem-sym-bc-at02142041 ; lem-sym-bc-at022330 ; lem-sym-bc-at02233440 ; lem-sym-bc-at022440 ; lem-sym-bc-at0310243142 ; lem-sym-bc-at0310243241 ; lem-sym-bc-at031031 ; lem-sym-bc-at03103441 ; lem-sym-bc-at0312203441 ; lem-sym-bc-at0312243041 ; lem-sym-bc-at0314203241 ; lem-sym-bc-at0314213240 ; lem-sym-bc-at03143041 ; lem-sym-bc-at03143140 ; lem-sym-bc-at03243240 ; lem-sym-bc-at0330 ; lem-sym-bc-at033440 ; lem-sym-bc-at12213443 ; lem-sym-bc-at12233441 ; lem-sym-bc-at12243143 ; lem-sym-bc-at13213442 ; lem-sym-bc-at14213243 ; lem-sym-bc-at143143 ; lem-sym-bc-at233442 ; lem-sym-bc-at2442 ; lem-sym-bc-at3443)
open import Examples.Groups.Clifford+CS.FiveV.D.D017 using (lem-box-cP-at02142041 ; lem-box-cP-at0314203241 ; lem-box-cP-at03243042 ; lem-box-cP-at142142 ; lem-sym-bc-at02102331 ; lem-sym-bc-at142142)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS03-CCZ124 ; lem-comm-CS12-CCZ034 ; lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CS24-CCZ013 ; lem-comm-CSd03-CCZ124 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX14-CCZ023 ; lem-comm-CX14-TOFF023)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX13 ; lem-comm-CS02-CCZ134 ; lem-comm-CSd02-CCZ134 ; lem-comm-CX31-TOFF024 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.FiveV.D.R009 using (lem-comm-TOFF023-CX14)

private
  q1 : Ws → Eqn
  q1 c4 = eqn (Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4)
  q2 : Ws → Eqn
  q2 c4 = eqn (Toff013 ∷ Toff134 ∷ []) (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp 843 c4)
  q3 : Ws → Eqn
  q3 c4 = eqn (CCZ024 ∷ Toff034 ∷ []) (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp 845 c4)
  q4 : Ws → Eqn
  q4 c4 = eqn (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (Toff134 ∷ []) (wl 241 (lit c4))
  q5 : Ws → Eqn
  q5 c4 = eqn (CCZ024 ∷ K1 ∷ []) (K1 ∷ CCZ024 ∷ []) (wp 89 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (CCZ024 ∷ CS34 ∷ []) (CS34 ∷ CCZ024 ∷ []) (wp 36 c4)
  q7 : Ws → Eqn
  q7 c4 = eqn (CCZ024 ∷ CX13 ∷ []) (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4))
  q8 : Ws → Eqn
  q8 c4 = eqn (CCZ024 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ024 ∷ []) (wp 35 c4)
  q9 : Ws → Eqn
  q9 c4 = eqn (CCZ024 ∷ CS14 ∷ []) (CS14 ∷ CCZ024 ∷ []) (wp 34 c4)
  q10 : Ws → Eqn
  q10 c4 = eqn (CCZ024 ∷ K1⁻ ∷ []) (K1⁻ ∷ CCZ024 ∷ []) (wp 88 c4)
  q11 : Ws → Eqn
  q11 c4 = eqn (Toff013 ∷ Toff034 ∷ []) (Toff034 ∷ Toff013 ∷ []) (wp 97 c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (CCZ234 ∷ []) (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl 245 (lit c4))
  q13 : Ws → Eqn
  q13 c4 = eqn (CS34 ∷ Toff013 ∷ []) (Toff013 ∷ CS34 ∷ []) (wp 95 c4)
  q14 : Ws → Eqn
  q14 c4 = eqn (Toff013 ∷ CX24 ∷ []) (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4))
  q15 : Ws → Eqn
  q15 c4 = eqn (CS34⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS34⁻ ∷ []) (wp 94 c4)
  q16 : Ws → Eqn
  q16 c4 = eqn (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ []) (wl 246 (lit c4))
  q17 : Ws → Eqn
  q17 c4 = eqn (CCZ234 ∷ []) (Toff034 ∷ CCZ234 ∷ Toff034 ∷ []) (wp 842 c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (CCZ024 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ024 ∷ []) (wp 90 c4)
  q19 : Ws → Eqn
  q19 c4 = eqn (CS12 ∷ Toff013 ∷ []) (Toff013 ∷ CS12 ∷ []) (wl 247 (lit c4))
  q20 : Ws → Eqn
  q20 c4 = eqn (CCZ024 ∷ CS12 ∷ []) (CS12 ∷ CCZ024 ∷ []) (wp 81 c4)
  q21 : Ws → Eqn
  q21 c4 = eqn (CS12⁻ ∷ Toff013 ∷ []) (Toff013 ∷ CS12⁻ ∷ []) (wl 244 (lit c4))
  q22 : Ws → Eqn
  q22 c4 = eqn (CCZ024 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ024 ∷ []) (wp 87 c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl 1037 (lit c4))
  q24 : Ws → Eqn
  q24 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))

-- nf-comm-CS-S0@2: 83 steps
lem-nf-comm-CS-S0at2 : Ws → ⟪ (CS24 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-nf-comm-CS-S0at2 c4 = derive (CS24 ∷ Sb0-2-43-1 ∷ []) (CS24 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw 2 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q10 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 7 (q2 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 8 (q4 c4) ∷
   rw 5 (q11 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 1 (q23 c4) ∷
   rw 3 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff213 ∷ Toff314 ∷ []) (Toff214 ∷ Toff314 ∷ Toff213 ∷ []) (wl 747 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ024 ∷ Toff214 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp 654 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl 190 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ024 ∷ K3 ∷ []) (K3 ∷ CCZ024 ∷ []) (wp 37 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ024 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ024 ∷ []) (wp 33 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Toff213 ∷ Toff214 ∷ []) (Toff214 ∷ Toff213 ∷ []) (wl 197 (lit c4))
  q32 : Ws → Eqn
  q32 c4 = eqn (CCZ014 ∷ []) (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp 41 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CS14 ∷ Toff213 ∷ []) (Toff213 ∷ CS14 ∷ []) (wl 195 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (Toff213 ∷ CX04 ∷ []) (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CS14⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS14⁻ ∷ []) (wl 194 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CS01 ∷ Toff213 ∷ []) (Toff213 ∷ CS01 ∷ []) (wl 193 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CCZ014 ∷ []) (Toff214 ∷ CCZ014 ∷ Toff214 ∷ []) (wp 44 c4)
  q38 : Ws → Eqn
  q38 c4 = eqn (CCZ014 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ014 ∷ []) (wp 38 c4)
  q39 : Ws → Eqn
  q39 c4 = eqn (CS03 ∷ Toff213 ∷ []) (Toff213 ∷ CS03 ∷ []) (wl 196 (lit c4))
  q40 : Ws → Eqn
  q40 c4 = eqn (CCZ024 ∷ CS03 ∷ []) (CS03 ∷ CCZ024 ∷ []) (wp 21 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (CS03⁻ ∷ Toff213 ∷ []) (Toff213 ∷ CS03⁻ ∷ []) (wl 191 (lit c4))
  q42 : Ws → Eqn
  q42 c4 = eqn (CCZ024 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ024 ∷ []) (wp 32 c4)
  q43 : Ws → Eqn
  q43 c4 = eqn (CCZ014 ∷ Toff314 ∷ CS03 ∷ []) (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp 651 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)

-- nf-comm-CS-S1@0: 83 steps
lem-nf-comm-CS-S1at0 : Ws → ⟪ (CS14 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at0 c4 = derive (CS14 ∷ Sb2-0-41-3 ∷ []) (CS14 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ Bx2-0413 ∷ [])
  (re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 1 (q25 c4) ∷
   rw 4 (q26 c4) ∷
   rw 3 (q27 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q30 c4) ∷
   rw 5 (q28 c4) ∷
   rw 2 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw⁻ 3 (q33 c4) ∷
   rw 4 (q34 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw 6 (q34 c4) ∷
   rw⁻ 7 (q36 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw 2 (q29 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q30 c4) ∷
   rw 2 (q28 c4) ∷
   rw⁻ 3 (q25 c4) ∷
   rw 3 (q25 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q40 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q40 c4) ∷
   rw⁻ 4 (q25 c4) ∷
   rw 4 (q25 c4) ∷
   rw 7 (q26 c4) ∷
   rw 6 (q27 c4) ∷
   rw⁻ 9 (q28 c4) ∷
   rw 8 (q29 c4) ∷
   rw 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q30 c4) ∷
   rw 8 (q28 c4) ∷
   rw 5 (q31 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 6 (q33 c4) ∷
   rw 7 (q34 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw 9 (q34 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q30 c4) ∷
   rw 5 (q28 c4) ∷
   rw⁻ 6 (q25 c4) ∷
   rw 6 (q25 c4) ∷
   rw⁻ 9 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw⁻ 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw 1 (q43 c4) ∷
   rw 3 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = eqn (Bx0-1423 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (Toff023 ∷ Toff324 ∷ []) (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp 805 c4)
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ014 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 806 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (Toff324 ∷ []) (wl 217 (lit c4))
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ014 ∷ K3 ∷ []) (K3 ∷ CCZ014 ∷ []) (wp 65 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ014 ∷ CS34 ∷ []) (CS34 ∷ CCZ014 ∷ []) (wp 64 c4)
  q51 : Ws → Eqn
  q51 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q52 : Ws → Eqn
  q52 c4 = eqn (CCZ014 ∷ CS34⁻ ∷ []) (CS34⁻ ∷ CCZ014 ∷ []) (wp 63 c4)
  q53 : Ws → Eqn
  q53 c4 = eqn (CCZ014 ∷ CS24 ∷ []) (CS24 ∷ CCZ014 ∷ []) (wp 62 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CCZ014 ∷ K3⁻ ∷ []) (K3⁻ ∷ CCZ014 ∷ []) (wp 61 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (Toff023 ∷ Toff024 ∷ []) (Toff024 ∷ Toff023 ∷ []) (wp 72 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ124 ∷ []) (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl 220 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CS24 ∷ Toff023 ∷ []) (Toff023 ∷ CS24 ∷ []) (wp 70 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (Toff023 ∷ CX14 ∷ []) (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CS24⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS24⁻ ∷ []) (wp 69 c4)
  q60 : Ws → Eqn
  q60 c4 = eqn (CS12 ∷ Toff023 ∷ []) (Toff023 ∷ CS12 ∷ []) (wl 221 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ124 ∷ []) (Toff024 ∷ CCZ124 ∷ Toff024 ∷ []) (wp 74 c4)
  q62 : Ws → Eqn
  q62 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp 66 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ []) (wl 222 (lit c4))
  q64 : Ws → Eqn
  q64 c4 = eqn (CCZ014 ∷ CS13 ∷ []) (CS13 ∷ CCZ014 ∷ []) (wp 53 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (CS13⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS13⁻ ∷ []) (wl 219 (lit c4))
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ014 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ014 ∷ []) (wp 60 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ124 ∷ Toff324 ∷ CS13 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl 1000 (lit c4))
  q68 : Ws → Eqn
  q68 c4 = eqn (CCZ124 ∷ CCZ124 ∷ []) [] (wl 263 (lit c4))

-- nf-comm-CS-S1@1: 83 steps
lem-nf-comm-CS-S1at1 : Ws → ⟪ (CS24 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at1 c4 = derive (CS24 ∷ Sb0-1-42-3 ∷ []) (CS24 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Bx0-1423 ∷ [])
  (re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 1 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw 5 (q49 c4) ∷
   rw 6 (q50 c4) ∷
   rw 7 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q51 c4) ∷
   rw 10 (q53 c4) ∷
   rw 11 (q54 c4) ∷
   rw 5 (q48 c4) ∷
   rw 2 (q55 c4) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw 4 (q58 c4) ∷
   rw⁻ 5 (q59 c4) ∷
   rw 6 (q58 c4) ∷
   rw⁻ 7 (q60 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw 1 (q62 c4) ∷
   rw⁻ 3 (q48 c4) ∷
   rw 2 (q49 c4) ∷
   rw 3 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw 5 (q52 c4) ∷
   rw 6 (q51 c4) ∷
   rw 7 (q53 c4) ∷
   rw 8 (q54 c4) ∷
   rw 2 (q48 c4) ∷
   rw⁻ 3 (q45 c4) ∷
   rw 3 (q45 c4) ∷
   rw⁻ 6 (q63 c4) ∷
   rw 5 (q64 c4) ∷
   rw⁻ 4 (q63 c4) ∷
   rw 3 (q64 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw 4 (q45 c4) ∷
   rw 7 (q46 c4) ∷
   rw 6 (q47 c4) ∷
   rw⁻ 9 (q48 c4) ∷
   rw 8 (q49 c4) ∷
   rw 9 (q50 c4) ∷
   rw 10 (q51 c4) ∷
   rw 11 (q52 c4) ∷
   rw 12 (q51 c4) ∷
   rw 13 (q53 c4) ∷
   rw 14 (q54 c4) ∷
   rw 8 (q48 c4) ∷
   rw 5 (q55 c4) ∷
   rw 7 (q56 c4) ∷
   rw⁻ 6 (q57 c4) ∷
   rw 7 (q58 c4) ∷
   rw⁻ 8 (q59 c4) ∷
   rw 9 (q58 c4) ∷
   rw⁻ 10 (q60 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw 7 (q46 c4) ∷
   rw⁻ 5 (q61 c4) ∷
   rw 4 (q62 c4) ∷
   rw⁻ 6 (q48 c4) ∷
   rw 5 (q49 c4) ∷
   rw 6 (q50 c4) ∷
   rw 7 (q51 c4) ∷
   rw 8 (q52 c4) ∷
   rw 9 (q51 c4) ∷
   rw 10 (q53 c4) ∷
   rw 11 (q54 c4) ∷
   rw 5 (q48 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw 6 (q45 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 7 (q65 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 7 (q45 c4) ∷
   rw 1 (q67 c4) ∷
   rw 3 (q68 c4) ∷ []) Eq.refl

-- nf-comm-CS-S1@2: 83 steps
lem-nf-comm-CS-S1at2 : Ws → ⟪ (CS34 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-nf-comm-CS-S1at2 c4 = derive (CS34 ∷ Sb0-2-43-1 ∷ []) (CS34 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  (re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw 1 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw 3 (q3 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw 2 (q11 c4) ∷
   rw 4 (q12 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 4 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q16 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw 2 (q5 c4) ∷
   rw 3 (q6 c4) ∷
   rw 4 (q7 c4) ∷
   rw 5 (q8 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q9 c4) ∷
   rw 8 (q10 c4) ∷
   rw 2 (q4 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 4 (q19 c4) ∷
   rw 3 (q20 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw 7 (q2 c4) ∷
   rw 6 (q3 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw 8 (q5 c4) ∷
   rw 9 (q6 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q8 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q9 c4) ∷
   rw 14 (q10 c4) ∷
   rw 8 (q4 c4) ∷
   rw 5 (q11 c4) ∷
   rw 7 (q12 c4) ∷
   rw⁻ 6 (q13 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 8 (q15 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q16 c4) ∷
   rw⁻ 6 (q12 c4) ∷
   rw 7 (q2 c4) ∷
   rw⁻ 5 (q17 c4) ∷
   rw 4 (q18 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q8 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q9 c4) ∷
   rw 11 (q10 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q1 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 1 (q23 c4) ∷
   rw 3 (q24 c4) ∷ []) Eq.refl

private
  q69 : Ws → Eqn
  q69 c4 = eqn (Toff213 ∷ Bx2-4013 ∷ Toff213 ∷ []) (Bx2-4013 ∷ []) (lem-P-box-at0214203143 c4)
  q70 : Ws → Eqn
  q70 c4 = eqn (Bx2-4013 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0214203143 c4)
  q71 : Ws → Eqn
  q71 c4 = eqn (Toff213 ∷ Toff213 ∷ []) [] (wl 180 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (Bx2-1340 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4)

-- pairs @0214203143: 4 steps
lem-pairs-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-pairs-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-1340 ∷ [])
  (rw⁻ 0 (q69 c4) ∷
   rw 1 (q70 c4) ∷
   rw 4 (q71 c4) ∷
   rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = eqn (Bx2-1340 ∷ []) (Bx2-1430 ∷ []) (lem-sym-bc-at02233440 c4)

-- box-perm-1324 @02233440: 1 steps
lem-box-perm-1324-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ []) ⟫ʷ
lem-box-perm-1324-at02233440 c4 = derive (Bx2-1340 ∷ []) (Bx2-1430 ∷ [])
  (rw 0 (q73 c4) ∷ []) Eq.refl

private
  q74 : Ws → Eqn
  q74 c4 = eqn (Bx2-1430 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) (lem-box-cP-at022440 c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ124 ∷ X4 ∷ CZ12 ∷ []) (X4 ∷ CCZ124 ∷ []) (wl 1127 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CZ12 ∷ Toff203 ∷ []) (Toff203 ∷ CZ12 ∷ CCZ013 ∷ []) (wl 1128 (lit c4))
  q77 : Ws → Eqn
  q77 c4 = eqn (Toff203 ∷ X4 ∷ []) (X4 ∷ Toff203 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • (K ↑ • CCZ • K ↑ • iI) • Swap ↑ ↑) • Swap ↑) (X))
  q78 : Ws → Eqn
  q78 c4 = eqn (CCZ013 ∷ []) (CS03 ∷ CX13 ∷ CS03⁻ ∷ CX13 ∷ CS01 ∷ []) (wl 289 (lit c4))
  q79 : Ws → Eqn
  q79 c4 = eqn (CCZ124 ∷ CS01 ∷ []) (CS01 ∷ CCZ124 ∷ []) (wp 919 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (CCZ124 ∷ CX13 ∷ []) (CX13 ∷ CCZ124 ∷ []) (wl 280 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = eqn (CS03⁻ ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03⁻ ∷ []) (lem-comm-CSd03-CCZ124 (lit c4))
  q82 : Ws → Eqn
  q82 c4 = eqn (CS03 ∷ CCZ124 ∷ []) (CCZ124 ∷ CS03 ∷ []) (lem-comm-CS03-CCZ124 (lit c4))
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ124 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ124 ∷ []) (wl 1129 (lit c4))
  q84 : Ws → Eqn
  q84 c4 = eqn (X4 ∷ CZ12 ∷ CZ12 ∷ []) (X4 ∷ []) (wl 1130 (lit c4))
  q85 : Ws → Eqn
  q85 c4 = eqn (CCZ013 ∷ Toff203 ∷ []) (Toff203 ∷ CCZ013 ∷ []) (wl 1131 (lit c4))
  q86 : Ws → Eqn
  q86 c4 = eqn (CCZ013 ∷ []) (X4 ∷ CCZ013 ∷ X4 ∷ []) (wp 24 c4)

-- Xb-box @022440: 18 steps
lem-Xb-box-at022440 : Ws → ⟪ (X4 ∷ Bx2-1430 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1430 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at022440 c4 = derive (X4 ∷ Bx2-1430 ∷ X4 ∷ []) (Bx2-1430 ∷ CCZ013 ∷ [])
  (rw 1 (q74 c4) ∷
   rw⁻ 0 (q75 c4) ∷
   rw 2 (q76 c4) ∷
   rw⁻ 1 (q77 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 8 (q79 c4) ∷
   rw⁻ 7 (q80 c4) ∷
   rw 6 (q81 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   rw 4 (q82 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw⁻ 3 (q83 c4) ∷
   rw⁻ 2 (q75 c4) ∷
   rw 3 (q84 c4) ∷
   rw 4 (q85 c4) ∷
   rw⁻ 3 (q77 c4) ∷
   rw⁻ 0 (q74 c4) ∷
   rw⁻ 1 (q86 c4) ∷ []) Eq.refl

private
  q87 : Ws → Eqn
  q87 c4 = eqn (Bx2-1430 ∷ []) (Bx2-1340 ∷ []) (lem-sym-bc-at022440 c4)

-- box-perm-1324 @022440: 1 steps
lem-box-perm-1324-at022440 : Ws → ⟪ (Bx2-1430 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-1324-at022440 c4 = derive (Bx2-1430 ∷ []) (Bx2-1340 ∷ [])
  (rw 0 (q87 c4) ∷ []) Eq.refl

private
  q88 : Ws → Eqn
  q88 c4 = eqn (Toff204 ∷ Bx2-1340 ∷ Toff204 ∷ []) (Bx2-1340 ∷ []) (lem-P-box-at02233440 c4)
  q89 : Ws → Eqn
  q89 c4 = eqn (Bx2-1340 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02233440 c4)
  q90 : Ws → Eqn
  q90 c4 = eqn (Toff204 ∷ Toff204 ∷ []) [] (wp 19 c4)
  q91 : Ws → Eqn
  q91 c4 = eqn (Bx2-4013 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0214203143 c4)

-- pairs @02233440: 4 steps
lem-pairs-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-pairs-at02233440 c4 = derive (Bx2-1340 ∷ []) (Bx2-4013 ∷ [])
  (rw⁻ 0 (q88 c4) ∷
   rw 1 (q89 c4) ∷
   rw 4 (q90 c4) ∷
   rw⁻ 0 (q91 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = eqn (Bx0-2341 ∷ []) (Bx0-2431 ∷ []) (lem-sym-bc-at12233441 c4)

-- box-perm-1324 @12233441: 1 steps
lem-box-perm-1324-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1324-at12233441 c4 = derive (Bx0-2341 ∷ []) (Bx0-2431 ∷ [])
  (rw 0 (q92 c4) ∷ []) Eq.refl

private
  q93 : Ws → Eqn
  q93 c4 = eqn (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) (Bx0-4231 ∷ []) (lem-P-box-at1441 c4)
  q94 : Ws → Eqn
  q94 c4 = eqn (Bx0-4231 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at1441 c4)
  q95 : Ws → Eqn
  q95 c4 = eqn (Toff013 ∷ Toff013 ∷ []) [] (wl 229 (lit c4))
  q96 : Ws → Eqn
  q96 c4 = eqn (Bx0-3142 ∷ []) (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4)

-- pairs @1441: 4 steps
lem-pairs-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-pairs-at1441 c4 = derive (Bx0-4231 ∷ []) (Bx0-3142 ∷ [])
  (rw⁻ 0 (q93 c4) ∷
   rw 1 (q94 c4) ∷
   rw 4 (q95 c4) ∷
   rw⁻ 0 (q96 c4) ∷ []) Eq.refl

private
  q97 : Ws → Eqn
  q97 c4 = eqn (Bx0-3142 ∷ []) (Bx0-3412 ∷ []) (lem-sym-bc-at13213442 c4)

-- box-perm-1324 @13213442: 1 steps
lem-box-perm-1324-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-1324-at13213442 c4 = derive (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  (rw 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = eqn (Bx2-0341 ∷ []) (Bx2-0431 ∷ []) (lem-sym-bc-at0210233441 c4)

-- box-perm-1324 @0210233441: 1 steps
lem-box-perm-1324-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-box-perm-1324-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  (rw 0 (q98 c4) ∷ []) Eq.refl

private
  q99 : Ws → Eqn
  q99 c4 = eqn (Bx2-0431 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02102441 c4)
  q100 : Ws → Eqn
  q100 c4 = eqn (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (X4 ∷ CCZ024 ∷ []) (wp 20 c4)
  q101 : Ws → Eqn
  q101 c4 = eqn (CZ02 ∷ Toff213 ∷ []) (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl 183 (lit c4))
  q102 : Ws → Eqn
  q102 c4 = eqn (Toff213 ∷ X4 ∷ []) (X4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))
  q103 : Ws → Eqn
  q103 c4 = eqn (CCZ013 ∷ []) (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl 905 (lit c4))
  q104 : Ws → Eqn
  q104 c4 = eqn (CCZ024 ∷ CS01 ∷ []) (CS01 ∷ CCZ024 ∷ []) (wp 39 c4)
  q105 : Ws → Eqn
  q105 c4 = eqn (CCZ024 ∷ CX03 ∷ []) (CX03 ∷ CCZ024 ∷ []) (wp 756 c4)
  q106 : Ws → Eqn
  q106 c4 = eqn (CS13⁻ ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4))
  q107 : Ws → Eqn
  q107 c4 = eqn (CS13 ∷ CCZ024 ∷ []) (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4))
  q108 : Ws → Eqn
  q108 c4 = eqn (CCZ024 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ024 ∷ []) (wp 23 c4)
  q109 : Ws → Eqn
  q109 c4 = eqn (X4 ∷ CZ02 ∷ CZ02 ∷ []) (X4 ∷ []) (wl 185 (lit c4))
  q110 : Ws → Eqn
  q110 c4 = eqn (CCZ013 ∷ Toff213 ∷ []) (Toff213 ∷ CCZ013 ∷ []) (wl 186 (lit c4))

-- Xb-box @02102441: 18 steps
lem-Xb-box-at02102441 : Ws → ⟪ (X4 ∷ Bx2-0431 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at02102441 c4 = derive (X4 ∷ Bx2-0431 ∷ X4 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  (rw 1 (q99 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw 2 (q101 c4) ∷
   rw⁻ 1 (q102 c4) ∷
   rw 4 (q103 c4) ∷
   rw⁻ 8 (q104 c4) ∷
   rw⁻ 7 (q105 c4) ∷
   rw 6 (q106 c4) ∷
   rw⁻ 5 (q105 c4) ∷
   rw 4 (q107 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw⁻ 2 (q100 c4) ∷
   rw 3 (q109 c4) ∷
   rw 4 (q110 c4) ∷
   rw⁻ 3 (q102 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw⁻ 1 (q86 c4) ∷ []) Eq.refl

private
  q111 : Ws → Eqn
  q111 c4 = eqn (Bx2-0431 ∷ []) (Bx2-0341 ∷ []) (lem-sym-bc-at02102441 c4)

-- box-perm-1324 @02102441: 1 steps
lem-box-perm-1324-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-box-perm-1324-at02102441 c4 = derive (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  (rw 0 (q111 c4) ∷ []) Eq.refl

private
  q112 : Ws → Eqn
  q112 c4 = eqn (Bx0-1342 ∷ []) (Bx0-1432 ∷ []) (lem-sym-bc-at233442 c4)

-- box-perm-1324 @233442: 1 steps
lem-box-perm-1324-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ []) ⟫ʷ
lem-box-perm-1324-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-1432 ∷ [])
  (rw 0 (q112 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = eqn (Bx0-1432 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at2442 c4)
  q114 : Ws → Eqn
  q114 c4 = eqn (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (X4 ∷ CCZ014 ∷ []) (wp 52 c4)
  q115 : Ws → Eqn
  q115 c4 = eqn (CZ01 ∷ Toff023 ∷ []) (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl 206 (lit c4))
  q116 : Ws → Eqn
  q116 c4 = eqn (Toff023 ∷ X4 ∷ []) (X4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))
  q117 : Ws → Eqn
  q117 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl 242 (lit c4))
  q118 : Ws → Eqn
  q118 c4 = eqn (CCZ014 ∷ CS12 ∷ []) (CS12 ∷ CCZ014 ∷ []) (wp 67 c4)
  q119 : Ws → Eqn
  q119 c4 = eqn (CCZ014 ∷ CX13 ∷ []) (CX13 ∷ CCZ014 ∷ []) (wp 795 c4)
  q120 : Ws → Eqn
  q120 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q121 : Ws → Eqn
  q121 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q122 : Ws → Eqn
  q122 c4 = eqn (CCZ014 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ014 ∷ []) (wp 55 c4)
  q123 : Ws → Eqn
  q123 c4 = eqn (X4 ∷ CZ01 ∷ CZ01 ∷ []) (X4 ∷ []) (wl 208 (lit c4))
  q124 : Ws → Eqn
  q124 c4 = eqn (CCZ123 ∷ Toff023 ∷ []) (Toff023 ∷ CCZ123 ∷ []) (wl 209 (lit c4))
  q125 : Ws → Eqn
  q125 c4 = eqn (CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ X4 ∷ []) (wl 210 (lit c4))

-- Xb-box @2442: 18 steps
lem-Xb-box-at2442 : Ws → ⟪ (X4 ∷ Bx0-1432 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1432 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at2442 c4 = derive (X4 ∷ Bx0-1432 ∷ X4 ∷ []) (Bx0-1432 ∷ CCZ123 ∷ [])
  (rw 1 (q113 c4) ∷
   rw⁻ 0 (q114 c4) ∷
   rw 2 (q115 c4) ∷
   rw⁻ 1 (q116 c4) ∷
   rw 4 (q117 c4) ∷
   rw⁻ 8 (q118 c4) ∷
   rw⁻ 7 (q119 c4) ∷
   rw 6 (q120 c4) ∷
   rw⁻ 5 (q119 c4) ∷
   rw 4 (q121 c4) ∷
   rw⁻ 5 (q117 c4) ∷
   rw⁻ 3 (q122 c4) ∷
   rw⁻ 2 (q114 c4) ∷
   rw 3 (q123 c4) ∷
   rw 4 (q124 c4) ∷
   rw⁻ 3 (q116 c4) ∷
   rw⁻ 0 (q113 c4) ∷
   rw⁻ 1 (q125 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = eqn (Bx0-1432 ∷ []) (Bx0-1342 ∷ []) (lem-sym-bc-at2442 c4)

-- box-perm-1324 @2442: 1 steps
lem-box-perm-1324-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1342 ∷ []) ⟫ʷ
lem-box-perm-1324-at2442 c4 = derive (Bx0-1432 ∷ []) (Bx0-1342 ∷ [])
  (rw 0 (q126 c4) ∷ []) Eq.refl

private
  q127 : Ws → Eqn
  q127 c4 = eqn (Toff024 ∷ Bx0-1342 ∷ Toff024 ∷ []) (Bx0-1342 ∷ []) (lem-P-box-at233442 c4)
  q128 : Ws → Eqn
  q128 c4 = eqn (Bx0-1342 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at233442 c4)
  q129 : Ws → Eqn
  q129 c4 = eqn (Toff024 ∷ Toff024 ∷ []) [] (wp 80 c4)
  q130 : Ws → Eqn
  q130 c4 = eqn (Bx0-4213 ∷ []) (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at143143 c4)

-- pairs @233442: 4 steps
lem-pairs-at233442 : Ws → ⟪ (Bx0-1342 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-pairs-at233442 c4 = derive (Bx0-1342 ∷ []) (Bx0-4213 ∷ [])
  (rw⁻ 0 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 4 (q129 c4) ∷
   rw⁻ 0 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2413 ∷ []) (lem-sym-bc-at12213443 c4)

-- box-perm-1324 @12213443: 1 steps
lem-box-perm-1324-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ []) ⟫ʷ
lem-box-perm-1324-at12213443 c4 = derive (Bx0-2143 ∷ []) (Bx0-2413 ∷ [])
  (rw 0 (q131 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = eqn (Bx0-2413 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at12243143 c4)
  q133 : Ws → Eqn
  q133 c4 = eqn (CZ02 ∷ Toff013 ∷ []) (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl 232 (lit c4))
  q134 : Ws → Eqn
  q134 c4 = eqn (Toff013 ∷ X4 ∷ []) (X4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))
  q135 : Ws → Eqn
  q135 c4 = eqn (CCZ123 ∷ []) (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl 326 (lit c4))
  q136 : Ws → Eqn
  q136 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp 92 c4)
  q137 : Ws → Eqn
  q137 c4 = eqn (CCZ024 ∷ CX21 ∷ []) (CX21 ∷ CCZ024 ∷ []) (wp 749 c4)
  q138 : Ws → Eqn
  q138 c4 = eqn (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) (wl 234 (lit c4))

-- Xb-box @12243143: 18 steps
lem-Xb-box-at12243143 : Ws → ⟪ (X4 ∷ Bx0-2413 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2413 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at12243143 c4 = derive (X4 ∷ Bx0-2413 ∷ X4 ∷ []) (Bx0-2413 ∷ CCZ123 ∷ [])
  (rw 1 (q132 c4) ∷
   rw⁻ 0 (q100 c4) ∷
   rw 2 (q133 c4) ∷
   rw⁻ 1 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw⁻ 8 (q136 c4) ∷
   rw⁻ 7 (q137 c4) ∷
   rw 6 (q106 c4) ∷
   rw⁻ 5 (q137 c4) ∷
   rw 4 (q107 c4) ∷
   rw⁻ 5 (q135 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw⁻ 2 (q100 c4) ∷
   rw 3 (q109 c4) ∷
   rw 4 (q138 c4) ∷
   rw⁻ 3 (q134 c4) ∷
   rw⁻ 0 (q132 c4) ∷
   rw⁻ 1 (q125 c4) ∷ []) Eq.refl

private
  q139 : Ws → Eqn
  q139 c4 = eqn (Bx0-2413 ∷ []) (Bx0-2143 ∷ []) (lem-sym-bc-at12243143 c4)

-- box-perm-1324 @12243143: 1 steps
lem-box-perm-1324-at12243143 : Ws → ⟪ (Bx0-2413 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2143 ∷ []) ⟫ʷ
lem-box-perm-1324-at12243143 c4 = derive (Bx0-2413 ∷ []) (Bx0-2143 ∷ [])
  (rw 0 (q139 c4) ∷ []) Eq.refl

private
  q140 : Ws → Eqn
  q140 c4 = eqn (Toff034 ∷ Bx0-2143 ∷ Toff034 ∷ []) (Bx0-2143 ∷ []) (lem-P-box-at12213443 c4)
  q141 : Ws → Eqn
  q141 c4 = eqn (Bx0-2143 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at12213443 c4)
  q142 : Ws → Eqn
  q142 c4 = eqn (Toff034 ∷ Toff034 ∷ []) [] (wp 6 c4)
  q143 : Ws → Eqn
  q143 c4 = eqn (Bx0-4321 ∷ []) (Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ []) (lem-box-tQ-at14233241 c4)

-- pairs @12213443: 4 steps
lem-pairs-at12213443 : Ws → ⟪ (Bx0-2143 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4321 ∷ []) ⟫ʷ
lem-pairs-at12213443 c4 = derive (Bx0-2143 ∷ []) (Bx0-4321 ∷ [])
  (rw⁻ 0 (q140 c4) ∷
   rw 1 (q141 c4) ∷
   rw 4 (q142 c4) ∷
   rw⁻ 0 (q143 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = eqn (Bx0-1423 ∷ []) (Bx0-4123 ∷ []) (lem-sym-ab-at243243 c4)
  q145 : Ws → Eqn
  q145 c4 = eqn (Bx0-4123 ∷ []) (Bx0-4213 ∷ []) (lem-sym-bc-at14213243 c4)

-- box-perm-2314 @243243: 2 steps
lem-box-perm-2314-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4213 ∷ []) ⟫ʷ
lem-box-perm-2314-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-4213 ∷ [])
  (rw 0 (q144 c4) ∷
   rw 0 (q145 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = eqn (Bx3-4210 ∷ []) (Bx3-4120 ∷ []) (lem-sym-bc-at03143140 c4)

-- box-perm-1324 @03143140: 1 steps
lem-box-perm-1324-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-box-perm-1324-at03143140 c4 = derive (Bx3-4210 ∷ []) (Bx3-4120 ∷ [])
  (rw 0 (q146 c4) ∷ []) Eq.refl

private
  q147 : Ws → Eqn
  q147 c4 = eqn (Bx3-4120 ∷ []) (Bx3-1420 ∷ []) (lem-sym-ab-at0314213240 c4)

-- box-perm-3124 @03143140: 2 steps
lem-box-perm-3124-at03143140 : Ws → ⟪ (Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-3124-at03143140 c4 = derive (Bx3-4210 ∷ []) (Bx3-1420 ∷ [])
  (rw 0 (q146 c4) ∷
   rw 0 (q147 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = eqn (Bx3-1420 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243240 c4)
  q149 : Ws → Eqn
  q149 c4 = eqn (Bx0-3142 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at13213442 c4)
  q150 : Ws → Eqn
  q150 c4 = eqn (CCZ013 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ013 ∷ []) (wl 671 (lit c4))
  q151 : Ws → Eqn
  q151 c4 = eqn (CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ234 ∷ CCZ023 ∷ []) (wp 993 c4)
  q152 : Ws → Eqn
  q152 c4 = eqn (CCZ234 ∷ []) (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl 293 (lit c4))
  q153 : Ws → Eqn
  q153 c4 = eqn (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) (wl 324 (lit c4))
  q154 : Ws → Eqn
  q154 c4 = eqn (CCZ013 ∷ CX34 ∷ []) (CX34 ∷ CCZ013 ∷ []) (wp 523 c4)
  q155 : Ws → Eqn
  q155 c4 = eqn (CS24⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4))
  q156 : Ws → Eqn
  q156 c4 = eqn (CS24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4))
  q157 : Ws → Eqn
  q157 c4 = eqn (CCZ234 ∷ CCZ023 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ023 ∷ []) (wp 994 c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (CCZ013 ∷ Toff314 ∷ CCZ014 ∷ []) (Toff314 ∷ CCZ013 ∷ []) (wp 990 c4)
  q159 : Ws → Eqn
  q159 c4 = eqn (K3 ∷ CS14 ∷ CX31 ∷ CS14⁻ ∷ CX31 ∷ CS34 ∷ K3⁻ ∷ []) (Toff314 ∷ []) (wl 1182 (lit c4))
  q160 : Ws → Eqn
  q160 c4 = eqn (K3⁻ ∷ Toff024 ∷ []) (Toff024 ∷ K3⁻ ∷ []) (wp 740 c4)
  q161 : Ws → Eqn
  q161 c4 = eqn (CS34 ∷ Toff024 ∷ []) (Toff024 ∷ CS34 ∷ []) (wp 970 c4)
  q162 : Ws → Eqn
  q162 c4 = eqn (CX31 ∷ Toff024 ∷ []) (Toff024 ∷ CX31 ∷ []) (lem-comm-CX31-TOFF024 (lit c4))
  q163 : Ws → Eqn
  q163 c4 = eqn (CS14⁻ ∷ Toff024 ∷ []) (Toff024 ∷ CS14⁻ ∷ []) (wp 995 c4)
  q164 : Ws → Eqn
  q164 c4 = eqn (CS14 ∷ Toff024 ∷ []) (Toff024 ∷ CS14 ∷ []) (wp 590 c4)
  q165 : Ws → Eqn
  q165 c4 = eqn (K3 ∷ Toff024 ∷ []) (Toff024 ∷ K3 ∷ []) (wp 742 c4)
  q166 : Ws → Eqn
  q166 c4 = eqn (CCZ013 ∷ CCZ014 ∷ []) (CCZ014 ∷ CCZ013 ∷ []) (wp 394 c4)
  q167 : Ws → Eqn
  q167 c4 = eqn (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ []) (wl 645 (lit c4))
  q168 : Ws → Eqn
  q168 c4 = eqn (CCZ013 ∷ CX14 ∷ []) (CX14 ∷ CCZ013 ∷ []) (wp 189 c4)
  q169 : Ws → Eqn
  q169 c4 = eqn (CCZ014 ∷ CCZ124 ∷ CCZ014 ∷ []) (CCZ124 ∷ []) (wp 996 c4)
  q170 : Ws → Eqn
  q170 c4 = eqn (CCZ124 ∷ Toff024 ∷ []) (Toff024 ∷ CCZ124 ∷ []) (wp 743 c4)
  q171 : Ws → Eqn
  q171 c4 = eqn (CCZ023 ∷ CS12 ∷ []) (CS12 ∷ CCZ023 ∷ []) (wl 621 (lit c4))
  q172 : Ws → Eqn
  q172 c4 = eqn (CX14 ∷ CCZ023 ∷ []) (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4))
  q173 : Ws → Eqn
  q173 c4 = eqn (CCZ023 ∷ CS24⁻ ∷ []) (CS24⁻ ∷ CCZ023 ∷ []) (wp 820 c4)
  q174 : Ws → Eqn
  q174 c4 = eqn (CCZ023 ∷ CS24 ∷ []) (CS24 ∷ CCZ023 ∷ []) (wp 513 c4)
  q175 : Ws → Eqn
  q175 c4 = eqn (CCZ124 ∷ Toff314 ∷ []) (Toff314 ∷ CCZ124 ∷ []) (wl 974 (lit c4))

-- box-box-4 @03243240: 103 steps
lem-box-box-4-at03243240 : Ws → ⟪ (Bx3-1420 ∷ Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ Bx3-1420 ∷ []) ⟫ʷ
lem-box-box-4-at03243240 c4 = derive (Bx3-1420 ∷ Bx0-3142 ∷ []) (Bx0-3142 ∷ Bx3-1420 ∷ [])
  (rw 0 (q148 c4) ∷
   rw 4 (q149 c4) ∷
   rw⁻ 3 (q150 c4) ∷
   rw 4 (q151 c4) ∷
   rw⁻ 6 (q150 c4) ∷
   rw 5 (q152 c4) ∷
   rw⁻ 9 (q153 c4) ∷
   rw⁻ 8 (q154 c4) ∷
   rw 7 (q155 c4) ∷
   rw⁻ 6 (q154 c4) ∷
   rw 5 (q156 c4) ∷
   rw⁻ 6 (q152 c4) ∷
   rw 6 (q157 c4) ∷
   rw⁻ 3 (q149 c4) ∷
   rw 3 (q149 c4) ∷
   rw⁻ 2 (q158 c4) ∷
   rw 4 (q47 c4) ∷
   rw⁻ 3 (q159 c4) ∷
   rw 9 (q160 c4) ∷
   rw 8 (q161 c4) ∷
   rw 7 (q162 c4) ∷
   rw 6 (q163 c4) ∷
   rw 5 (q162 c4) ∷
   rw 4 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q159 c4) ∷
   rw⁻ 6 (q166 c4) ∷
   rw 5 (q56 c4) ∷
   rw⁻ 9 (q167 c4) ∷
   rw⁻ 8 (q168 c4) ∷
   rw 7 (q155 c4) ∷
   rw⁻ 6 (q168 c4) ∷
   rw 5 (q156 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw⁻ 4 (q158 c4) ∷
   rw 6 (q169 c4) ∷
   rw 6 (q170 c4) ∷
   rw⁻ 5 (q159 c4) ∷
   rw 11 (q160 c4) ∷
   rw 10 (q161 c4) ∷
   rw 9 (q162 c4) ∷
   rw 8 (q163 c4) ∷
   rw 7 (q162 c4) ∷
   rw 6 (q164 c4) ∷
   rw 5 (q165 c4) ∷
   rw 6 (q159 c4) ∷
   rw⁻ 2 (q149 c4) ∷
   rw 2 (q149 c4) ∷
   rw⁻ 1 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw⁻ 4 (q150 c4) ∷
   rw 3 (q152 c4) ∷
   rw⁻ 7 (q153 c4) ∷
   rw⁻ 6 (q154 c4) ∷
   rw 5 (q155 c4) ∷
   rw⁻ 4 (q154 c4) ∷
   rw 3 (q156 c4) ∷
   rw⁻ 4 (q152 c4) ∷
   rw 4 (q157 c4) ∷
   rw⁻ 1 (q149 c4) ∷
   rw 1 (q149 c4) ∷
   rw⁻ 0 (q158 c4) ∷
   rw 2 (q47 c4) ∷
   rw⁻ 1 (q159 c4) ∷
   rw 7 (q160 c4) ∷
   rw 6 (q161 c4) ∷
   rw 5 (q162 c4) ∷
   rw 4 (q163 c4) ∷
   rw 3 (q162 c4) ∷
   rw 2 (q164 c4) ∷
   rw 1 (q165 c4) ∷
   rw 2 (q159 c4) ∷
   rw⁻ 4 (q166 c4) ∷
   rw 3 (q56 c4) ∷
   rw⁻ 7 (q167 c4) ∷
   rw⁻ 6 (q168 c4) ∷
   rw 5 (q155 c4) ∷
   rw⁻ 4 (q168 c4) ∷
   rw 3 (q156 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   rw⁻ 2 (q158 c4) ∷
   rw 4 (q169 c4) ∷
   rw 4 (q170 c4) ∷
   rw⁻ 3 (q159 c4) ∷
   rw 9 (q160 c4) ∷
   rw 8 (q161 c4) ∷
   rw 7 (q162 c4) ∷
   rw 6 (q163 c4) ∷
   rw 5 (q162 c4) ∷
   rw 4 (q164 c4) ∷
   rw 3 (q165 c4) ∷
   rw 4 (q159 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw 2 (q56 c4) ∷
   rw⁻ 6 (q171 c4) ∷
   rw 5 (q172 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q172 c4) ∷
   rw⁻ 2 (q174 c4) ∷
   rw⁻ 3 (q56 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q68 c4) ∷
   rw⁻ 1 (q148 c4) ∷ []) Eq.refl

private
  q176 : Ws → Eqn
  q176 c4 = eqn (Bx3-1420 ∷ []) (Bx3-4120 ∷ []) (lem-sym-ab-at03243240 c4)
  q177 : Ws → Eqn
  q177 c4 = eqn (Bx3-4120 ∷ []) (Bx3-4210 ∷ []) (lem-sym-bc-at0314213240 c4)

-- box-perm-2314 @03243240: 2 steps
lem-box-perm-2314-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ []) ⟫ʷ
lem-box-perm-2314-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-4210 ∷ [])
  (rw 0 (q176 c4) ∷
   rw 0 (q177 c4) ∷ []) Eq.refl

private
  q178 : Ws → Eqn
  q178 c4 = eqn (Bx3-4210 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143140 c4)
  q179 : Ws → Eqn
  q179 c4 = eqn (CCZ234 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ234 ∷ []) (wl 432 (lit c4))
  q180 : Ws → Eqn
  q180 c4 = eqn (CS13⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ []) (wl 1191 (lit c4))
  q181 : Ws → Eqn
  q181 c4 = eqn (CCZ013 ∷ []) (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl 323 (lit c4))
  q182 : Ws → Eqn
  q182 c4 = eqn (CCZ234 ∷ CS03 ∷ []) (CS03 ∷ CCZ234 ∷ []) (wp 294 c4)
  q183 : Ws → Eqn
  q183 c4 = eqn (CCZ234 ∷ CX31 ∷ []) (CX31 ∷ CCZ234 ∷ []) (wl 336 (lit c4))
  q184 : Ws → Eqn
  q184 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))
  q185 : Ws → Eqn
  q185 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))
  q186 : Ws → Eqn
  q186 c4 = eqn (CCZ013 ∷ Toff301 ∷ []) (Toff301 ∷ CZ01 ∷ CCZ013 ∷ []) (wl 1192 (lit c4))
  q187 : Ws → Eqn
  q187 c4 = eqn (CS01⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS01⁻ ∷ []) (wl 1193 (lit c4))
  q188 : Ws → Eqn
  q188 c4 = eqn (CS13⁻ ∷ CS01⁻ ∷ CCZ013 ∷ CS01⁻ ∷ CZ01 ∷ CCZ013 ∷ []) (CS13⁻ ∷ []) (wl 1194 (lit c4))

-- CSdu-box-3 @03143140: 17 steps
lem-CSdu-box-3-at03143140 : Ws → ⟪ (CS13⁻ ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at03143140 c4 = derive (CS13⁻ ∷ Bx3-4210 ∷ []) (Bx3-4210 ∷ CS13⁻ ∷ [])
  (rw 1 (q178 c4) ∷
   rw⁻ 0 (q179 c4) ∷
   rw 1 (q180 c4) ∷
   rw 4 (q181 c4) ∷
   rw⁻ 8 (q182 c4) ∷
   rw⁻ 7 (q183 c4) ∷
   rw 6 (q184 c4) ∷
   rw⁻ 5 (q183 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 5 (q181 c4) ∷
   rw 3 (q184 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw 5 (q186 c4) ∷
   rw 4 (q187 c4) ∷
   rw 3 (q180 c4) ∷
   rw 4 (q188 c4) ∷
   rw⁻ 0 (q178 c4) ∷ []) Eq.refl

private
  q189 : Ws → Eqn
  q189 c4 = eqn (CCZ234 ∷ CS13 ∷ []) (CS13 ∷ CCZ234 ∷ []) (wl 433 (lit c4))
  q190 : Ws → Eqn
  q190 c4 = eqn (CS13 ∷ Toff301 ∷ []) (Toff301 ∷ CS13 ∷ CS01 ∷ CCZ013 ∷ []) (wl 1200 (lit c4))
  q191 : Ws → Eqn
  q191 c4 = eqn (CS01 ∷ Toff301 ∷ []) (Toff301 ∷ CS01 ∷ []) (wl 1201 (lit c4))
  q192 : Ws → Eqn
  q192 c4 = eqn (CS13 ∷ CS01 ∷ CCZ013 ∷ CS01 ∷ CZ01 ∷ CCZ013 ∷ []) (CS13 ∷ []) (wl 1202 (lit c4))

-- CSu-box-3 @03143140: 17 steps
lem-CSu-box-3-at03143140 : Ws → ⟪ (CS13 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4210 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at03143140 c4 = derive (CS13 ∷ Bx3-4210 ∷ []) (Bx3-4210 ∷ CS13 ∷ [])
  (rw 1 (q178 c4) ∷
   rw⁻ 0 (q189 c4) ∷
   rw 1 (q190 c4) ∷
   rw 4 (q181 c4) ∷
   rw⁻ 8 (q182 c4) ∷
   rw⁻ 7 (q183 c4) ∷
   rw 6 (q184 c4) ∷
   rw⁻ 5 (q183 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 5 (q181 c4) ∷
   rw 3 (q185 c4) ∷
   rw⁻ 2 (q189 c4) ∷
   rw 5 (q186 c4) ∷
   rw 4 (q191 c4) ∷
   rw 3 (q190 c4) ∷
   rw 4 (q192 c4) ∷
   rw⁻ 0 (q178 c4) ∷ []) Eq.refl

private
  q193 : Ws → Eqn
  q193 c4 = eqn (Bx3-4210 ∷ []) (Toff324 ∷ CCZ013 ∷ Toff324 ∷ CCZ013 ∷ []) (lem-box-tQ-at03143140 c4)
  q194 : Ws → Eqn
  q194 c4 = eqn (Toff324 ∷ Toff324 ∷ []) [] (wl 442 (lit c4))
  q195 : Ws → Eqn
  q195 c4 = eqn (Toff324 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ Toff324 ∷ []) (lem-t-cP-at03143140 c4)
  q196 : Ws → Eqn
  q196 c4 = eqn (CCZ013 ∷ CCZ013 ∷ []) [] (wl 230 (lit c4))

-- box2 @03143140: 11 steps
lem-box2-at03143140 : Ws → ⟪ (Bx3-4210 ∷ Bx3-4210 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03143140 c4 = derive (Bx3-4210 ∷ Bx3-4210 ∷ []) []
  (rw 0 (q193 c4) ∷
   rw 4 (q178 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw 5 (q193 c4) ∷
   rw 4 (q194 c4) ∷
   rw 3 (q196 c4) ∷
   rw 2 (q194 c4) ∷
   rw 1 (q196 c4) ∷
   rw 0 (q194 c4) ∷ []) Eq.refl

private
  q197 : Ws → Eqn
  q197 c4 = eqn (Bx0-4213 ∷ []) (Bx0-4123 ∷ []) (lem-sym-bc-at143143 c4)
  q198 : Ws → Eqn
  q198 c4 = eqn (Bx0-4123 ∷ []) (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4)

-- box-perm-3124 @143143: 2 steps
lem-box-perm-3124-at143143 : Ws → ⟪ (Bx0-4213 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-3124-at143143 c4 = derive (Bx0-4213 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q197 c4) ∷
   rw 0 (q198 c4) ∷ []) Eq.refl

private
  q199 : Ws → Eqn
  q199 c4 = eqn (CCZ014 ∷ CX30 ∷ CCZ134 ∷ []) (CX30 ∷ CCZ014 ∷ []) (wp 1010 c4)
  q200 : Ws → Eqn
  q200 c4 = eqn (CCZ134 ∷ []) (CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ []) (wl 698 (lit c4))
  q201 : Ws → Eqn
  q201 c4 = eqn (CX14 ∷ Toff023 ∷ []) (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4))
  q202 : Ws → Eqn
  q202 c4 = eqn (CS34⁻ ∷ Toff023 ∷ []) (Toff023 ∷ CS34⁻ ∷ []) (wp 823 c4)
  q203 : Ws → Eqn
  q203 c4 = eqn (CS34 ∷ Toff023 ∷ []) (Toff023 ∷ CS34 ∷ []) (wp 725 c4)
  q204 : Ws → Eqn
  q204 c4 = eqn (CX30 ∷ Toff023 ∷ []) (Toff023 ∷ CX30 ∷ []) (wl 1207 (lit c4))
  q205 : Ws → Eqn
  q205 c4 = eqn (CCZ014 ∷ CCZ134 ∷ []) (CCZ134 ∷ CCZ014 ∷ []) (wp 272 c4)
  q206 : Ws → Eqn
  q206 c4 = eqn (CX30 ∷ CCZ134 ∷ CCZ134 ∷ []) (CX30 ∷ []) (wp 1011 c4)

-- CXu-box-4 @243243: 15 steps
lem-CXu-box-4-at243243 : Ws → ⟪ (CX30 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CX30 ∷ []) ⟫ʷ
lem-CXu-box-4-at243243 c4 = derive (CX30 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CX30 ∷ [])
  (rw 1 (q45 c4) ∷
   rw⁻ 0 (q199 c4) ∷
   rw 2 (q200 c4) ∷
   rw 6 (q63 c4) ∷
   rw 5 (q201 c4) ∷
   rw 4 (q202 c4) ∷
   rw 3 (q201 c4) ∷
   rw 2 (q203 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw 1 (q204 c4) ∷
   rw⁻ 3 (q205 c4) ∷
   rw⁻ 2 (q199 c4) ∷
   rw 3 (q206 c4) ∷
   rw 3 (q204 c4) ∷
   rw⁻ 0 (q45 c4) ∷ []) Eq.refl

private
  q207 : Ws → Eqn
  q207 c4 = eqn (Toff312 ∷ Bx3-4012 ∷ Toff312 ∷ []) (Bx3-4012 ∷ []) (lem-P-box-at0314203142 c4)
  q208 : Ws → Eqn
  q208 c4 = eqn (Bx3-4012 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203142 c4)
  q209 : Ws → Eqn
  q209 c4 = eqn (Toff312 ∷ Toff312 ∷ []) [] (wl 489 (lit c4))
  q210 : Ws → Eqn
  q210 c4 = eqn (Bx3-1240 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at033440 c4)

-- pairs @0314203142: 4 steps
lem-pairs-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-pairs-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-1240 ∷ [])
  (rw⁻ 0 (q207 c4) ∷
   rw 1 (q208 c4) ∷
   rw 4 (q209 c4) ∷
   rw⁻ 0 (q210 c4) ∷ []) Eq.refl

private
  q211 : Ws → Eqn
  q211 c4 = eqn (Bx3-1420 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4)
  q212 : Ws → Eqn
  q212 c4 = eqn (Toff314 ∷ Toff314 ∷ []) [] (wl 788 (lit c4))
  q213 : Ws → Eqn
  q213 c4 = eqn (Toff314 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff314 ∷ []) (lem-t-cP-at03243240 c4)
  q214 : Ws → Eqn
  q214 c4 = eqn (CCZ023 ∷ CCZ023 ∷ []) [] (wl 204 (lit c4))

-- box2 @03243240: 11 steps
lem-box2-at03243240 : Ws → ⟪ (Bx3-1420 ∷ Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03243240 c4 = derive (Bx3-1420 ∷ Bx3-1420 ∷ []) []
  (rw 0 (q148 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 4 (q212 c4) ∷
   rw 5 (q213 c4) ∷
   rw⁻ 5 (q211 c4) ∷
   rw 5 (q148 c4) ∷
   rw 4 (q212 c4) ∷
   rw 3 (q214 c4) ∷
   rw 2 (q212 c4) ∷
   rw 1 (q214 c4) ∷
   rw 0 (q212 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = eqn (Bx3-1420 ∷ []) (Bx3-1240 ∷ []) (lem-sym-bc-at03243240 c4)

-- box-perm-1324 @03243240: 1 steps
lem-box-perm-1324-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-box-perm-1324-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-1240 ∷ [])
  (rw 0 (q215 c4) ∷ []) Eq.refl

private
  q216 : Ws → Eqn
  q216 c4 = eqn (Toff304 ∷ Bx3-1240 ∷ Toff304 ∷ []) (Bx3-1240 ∷ []) (lem-P-box-at033440 c4)
  q217 : Ws → Eqn
  q217 c4 = eqn (Bx3-1240 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4)
  q218 : Ws → Eqn
  q218 c4 = eqn (Toff304 ∷ Toff304 ∷ []) [] (wp 351 c4)
  q219 : Ws → Eqn
  q219 c4 = eqn (Bx3-4012 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203142 c4)

-- pairs @033440: 4 steps
lem-pairs-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-pairs-at033440 c4 = derive (Bx3-1240 ∷ []) (Bx3-4012 ∷ [])
  (rw⁻ 0 (q216 c4) ∷
   rw 1 (q217 c4) ∷
   rw 4 (q218 c4) ∷
   rw⁻ 0 (q219 c4) ∷ []) Eq.refl

private
  q220 : Ws → Eqn
  q220 c4 = eqn (Bx3-0412 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243142 c4)
  q221 : Ws → Eqn
  q221 c4 = eqn (Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4)
  q222 : Ws → Eqn
  q222 c4 = eqn (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) (lem-t-cP-at0310243142 c4)
  q223 : Ws → Eqn
  q223 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))

-- box2 @0310243142: 11 steps
lem-box2-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0310243142 c4 = derive (Bx3-0412 ∷ Bx3-0412 ∷ []) []
  (rw 0 (q220 c4) ∷
   rw 4 (q221 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw 5 (q222 c4) ∷
   rw⁻ 5 (q221 c4) ∷
   rw 5 (q220 c4) ∷
   rw 4 (q218 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q223 c4) ∷
   rw 0 (q218 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = eqn (Toff302 ∷ Bx3-4102 ∷ Toff302 ∷ []) (Bx3-4102 ∷ []) (lem-P-box-at0314213042 c4)
  q225 : Ws → Eqn
  q225 c4 = eqn (Bx3-4102 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213042 c4)
  q226 : Ws → Eqn
  q226 c4 = eqn (Toff302 ∷ Toff302 ∷ []) [] (wl 787 (lit c4))
  q227 : Ws → Eqn
  q227 c4 = eqn (Bx3-0241 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03103441 c4)

-- pairs @0314213042: 4 steps
lem-pairs-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-pairs-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-0241 ∷ [])
  (rw⁻ 0 (q224 c4) ∷
   rw 1 (q225 c4) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 0 (q227 c4) ∷ []) Eq.refl

private
  q228 : Ws → Eqn
  q228 c4 = eqn (Bx3-0241 ∷ []) (Bx3-0421 ∷ []) (lem-sym-bc-at03103441 c4)

-- box-perm-1324 @03103441: 1 steps
lem-box-perm-1324-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-box-perm-1324-at03103441 c4 = derive (Bx3-0241 ∷ []) (Bx3-0421 ∷ [])
  (rw 0 (q228 c4) ∷ []) Eq.refl

private
  q229 : Ws → Eqn
  q229 c4 = eqn (Bx3-0421 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243241 c4)
  q230 : Ws → Eqn
  q230 c4 = eqn (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (X4 ∷ CCZ034 ∷ []) (wp 796 c4)
  q231 : Ws → Eqn
  q231 c4 = eqn (CZ03 ∷ Toff312 ∷ []) (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (wl 512 (lit c4))
  q232 : Ws → Eqn
  q232 c4 = eqn (Toff312 ∷ X4 ∷ []) (X4 ∷ Toff312 ∷ []) (c₄ (Toffᵗ ↑) (X))
  q233 : Ws → Eqn
  q233 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (wl 391 (lit c4))
  q234 : Ws → Eqn
  q234 c4 = eqn (CCZ034 ∷ CS01 ∷ []) (CS01 ∷ CCZ034 ∷ []) (wp 1 c4)
  q235 : Ws → Eqn
  q235 c4 = eqn (CCZ034 ∷ CX02 ∷ []) (CX02 ∷ CCZ034 ∷ []) (wp 333 c4)
  q236 : Ws → Eqn
  q236 c4 = eqn (CS12⁻ ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4))
  q237 : Ws → Eqn
  q237 c4 = eqn (CS12 ∷ CCZ034 ∷ []) (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4))
  q238 : Ws → Eqn
  q238 c4 = eqn (CCZ034 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ034 ∷ []) (wp 797 c4)
  q239 : Ws → Eqn
  q239 c4 = eqn (X4 ∷ CZ03 ∷ CZ03 ∷ []) (X4 ∷ []) (wp 798 c4)
  q240 : Ws → Eqn
  q240 c4 = eqn (CCZ012 ∷ Toff312 ∷ []) (Toff312 ∷ CCZ012 ∷ []) (wl 503 (lit c4))
  q241 : Ws → Eqn
  q241 c4 = eqn (CCZ012 ∷ []) (X4 ∷ CCZ012 ∷ X4 ∷ []) (wl 1243 (lit c4))

-- Xb-box @0310243241: 18 steps
lem-Xb-box-at0310243241 : Ws → ⟪ (X4 ∷ Bx3-0421 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0310243241 c4 = derive (X4 ∷ Bx3-0421 ∷ X4 ∷ []) (Bx3-0421 ∷ CCZ012 ∷ [])
  (rw 1 (q229 c4) ∷
   rw⁻ 0 (q230 c4) ∷
   rw 2 (q231 c4) ∷
   rw⁻ 1 (q232 c4) ∷
   rw 4 (q233 c4) ∷
   rw⁻ 8 (q234 c4) ∷
   rw⁻ 7 (q235 c4) ∷
   rw 6 (q236 c4) ∷
   rw⁻ 5 (q235 c4) ∷
   rw 4 (q237 c4) ∷
   rw⁻ 5 (q233 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw⁻ 2 (q230 c4) ∷
   rw 3 (q239 c4) ∷
   rw 4 (q240 c4) ∷
   rw⁻ 3 (q232 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q242 : Ws → Eqn
  q242 c4 = eqn (Bx3-0421 ∷ []) (Bx3-0241 ∷ []) (lem-sym-bc-at0310243241 c4)

-- box-perm-1324 @0310243241: 1 steps
lem-box-perm-1324-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0241 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310243241 c4 = derive (Bx3-0421 ∷ []) (Bx3-0241 ∷ [])
  (rw 0 (q242 c4) ∷ []) Eq.refl

private
  q243 : Ws → Eqn
  q243 c4 = eqn (Toff314 ∷ Bx3-0241 ∷ Toff314 ∷ []) (Bx3-0241 ∷ []) (lem-P-box-at03103441 c4)
  q244 : Ws → Eqn
  q244 c4 = eqn (Bx3-0241 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at03103441 c4)
  q245 : Ws → Eqn
  q245 c4 = eqn (Bx3-4102 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213042 c4)

-- pairs @03103441: 4 steps
lem-pairs-at03103441 : Ws → ⟪ (Bx3-0241 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-pairs-at03103441 c4 = derive (Bx3-0241 ∷ []) (Bx3-4102 ∷ [])
  (rw⁻ 0 (q243 c4) ∷
   rw 1 (q244 c4) ∷
   rw 4 (q212 c4) ∷
   rw⁻ 0 (q245 c4) ∷ []) Eq.refl

private
  q246 : Ws → Eqn
  q246 c4 = eqn (Bx3-0412 ∷ []) (Bx3-0142 ∷ []) (lem-sym-bc-at0310243142 c4)

-- box-perm-1324 @0310243142: 1 steps
lem-box-perm-1324-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-box-perm-1324-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-0142 ∷ [])
  (rw 0 (q246 c4) ∷ []) Eq.refl

private
  q247 : Ws → Eqn
  q247 c4 = eqn (CCZ012 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl 348 (lit c4))
  q248 : Ws → Eqn
  q248 c4 = eqn (CCZ034 ∷ CS02 ∷ []) (CS02 ∷ CCZ034 ∷ []) (wp 3 c4)
  q249 : Ws → Eqn
  q249 c4 = eqn (CCZ034 ∷ CX01 ∷ []) (CX01 ∷ CCZ034 ∷ []) (wp 221 c4)

-- Xb-box @0310243142: 18 steps
lem-Xb-box-at0310243142 : Ws → ⟪ (X4 ∷ Bx3-0412 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0310243142 c4 = derive (X4 ∷ Bx3-0412 ∷ X4 ∷ []) (Bx3-0412 ∷ CCZ012 ∷ [])
  (rw 1 (q221 c4) ∷
   rw⁻ 0 (q230 c4) ∷
   rw 2 (q231 c4) ∷
   rw⁻ 1 (q232 c4) ∷
   rw 4 (q247 c4) ∷
   rw⁻ 8 (q248 c4) ∷
   rw⁻ 7 (q249 c4) ∷
   rw 6 (q236 c4) ∷
   rw⁻ 5 (q249 c4) ∷
   rw 4 (q237 c4) ∷
   rw⁻ 5 (q247 c4) ∷
   rw⁻ 3 (q238 c4) ∷
   rw⁻ 2 (q230 c4) ∷
   rw 3 (q239 c4) ∷
   rw 4 (q240 c4) ∷
   rw⁻ 3 (q232 c4) ∷
   rw⁻ 0 (q221 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q250 : Ws → Eqn
  q250 c4 = eqn (Toff302 ∷ Bx3-4120 ∷ Toff302 ∷ []) (Bx3-4120 ∷ []) (lem-P-box-at0314213240 c4)
  q251 : Ws → Eqn
  q251 c4 = eqn (Bx3-4120 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at0314213240 c4)
  q252 : Ws → Eqn
  q252 c4 = eqn (Bx3-2041 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at0312203441 c4)

-- pairs @0314213240: 4 steps
lem-pairs-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-pairs-at0314213240 c4 = derive (Bx3-4120 ∷ []) (Bx3-2041 ∷ [])
  (rw⁻ 0 (q250 c4) ∷
   rw 1 (q251 c4) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 0 (q252 c4) ∷ []) Eq.refl

private
  q253 : Ws → Eqn
  q253 c4 = eqn (Bx3-2041 ∷ []) (Bx3-2401 ∷ []) (lem-sym-bc-at0312203441 c4)

-- box-perm-1324 @0312203441: 1 steps
lem-box-perm-1324-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-1324-at0312203441 c4 = derive (Bx3-2041 ∷ []) (Bx3-2401 ∷ [])
  (rw 0 (q253 c4) ∷ []) Eq.refl

private
  q254 : Ws → Eqn
  q254 c4 = eqn (Bx3-2401 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at0312243041 c4)
  q255 : Ws → Eqn
  q255 c4 = eqn (CCZ234 ∷ X4 ∷ CZ23 ∷ []) (X4 ∷ CCZ234 ∷ []) (wl 1274 (lit c4))
  q256 : Ws → Eqn
  q256 c4 = eqn (CZ23 ∷ Toff301 ∷ []) (Toff301 ∷ CZ23 ∷ CCZ012 ∷ []) (wl 1275 (lit c4))
  q257 : Ws → Eqn
  q257 c4 = eqn (Toff301 ∷ X4 ∷ []) (X4 ∷ Toff301 ∷ []) (c₄ (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) (X))
  q258 : Ws → Eqn
  q258 c4 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wl 1273 (lit c4))
  q259 : Ws → Eqn
  q259 c4 = eqn (CCZ234 ∷ CS12 ∷ []) (CS12 ∷ CCZ234 ∷ []) (wl 415 (lit c4))
  q260 : Ws → Eqn
  q260 c4 = eqn (CCZ234 ∷ CX20 ∷ []) (CX20 ∷ CCZ234 ∷ []) (wp 366 c4)
  q261 : Ws → Eqn
  q261 c4 = eqn (CCZ234 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ234 ∷ []) (wl 1071 (lit c4))
  q262 : Ws → Eqn
  q262 c4 = eqn (X4 ∷ CZ23 ∷ CZ23 ∷ []) (X4 ∷ []) (wl 1276 (lit c4))
  q263 : Ws → Eqn
  q263 c4 = eqn (CCZ012 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ012 ∷ []) (wl 1265 (lit c4))

-- Xb-box @0312243041: 18 steps
lem-Xb-box-at0312243041 : Ws → ⟪ (X4 ∷ Bx3-2401 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at0312243041 c4 = derive (X4 ∷ Bx3-2401 ∷ X4 ∷ []) (Bx3-2401 ∷ CCZ012 ∷ [])
  (rw 1 (q254 c4) ∷
   rw⁻ 0 (q255 c4) ∷
   rw 2 (q256 c4) ∷
   rw⁻ 1 (q257 c4) ∷
   rw 4 (q258 c4) ∷
   rw⁻ 8 (q259 c4) ∷
   rw⁻ 7 (q260 c4) ∷
   rw 6 (q184 c4) ∷
   rw⁻ 5 (q260 c4) ∷
   rw 4 (q185 c4) ∷
   rw⁻ 5 (q258 c4) ∷
   rw⁻ 3 (q261 c4) ∷
   rw⁻ 2 (q255 c4) ∷
   rw 3 (q262 c4) ∷
   rw 4 (q263 c4) ∷
   rw⁻ 3 (q257 c4) ∷
   rw⁻ 0 (q254 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q264 : Ws → Eqn
  q264 c4 = eqn (Bx3-2401 ∷ []) (Bx3-2041 ∷ []) (lem-sym-bc-at0312243041 c4)

-- box-perm-1324 @0312243041: 1 steps
lem-box-perm-1324-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2041 ∷ []) ⟫ʷ
lem-box-perm-1324-at0312243041 c4 = derive (Bx3-2401 ∷ []) (Bx3-2041 ∷ [])
  (rw 0 (q264 c4) ∷ []) Eq.refl

private
  q265 : Ws → Eqn
  q265 c4 = eqn (Toff314 ∷ Bx3-2041 ∷ Toff314 ∷ []) (Bx3-2041 ∷ []) (lem-P-box-at0312203441 c4)
  q266 : Ws → Eqn
  q266 c4 = eqn (Bx3-2041 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at0312203441 c4)
  q267 : Ws → Eqn
  q267 c4 = eqn (Bx3-4120 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at0314213240 c4)

-- pairs @0312203441: 4 steps
lem-pairs-at0312203441 : Ws → ⟪ (Bx3-2041 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4120 ∷ []) ⟫ʷ
lem-pairs-at0312203441 c4 = derive (Bx3-2041 ∷ []) (Bx3-4120 ∷ [])
  (rw⁻ 0 (q265 c4) ∷
   rw 1 (q266 c4) ∷
   rw 4 (q212 c4) ∷
   rw⁻ 0 (q267 c4) ∷ []) Eq.refl

private
  q268 : Ws → Eqn
  q268 c4 = eqn (Bx3-1240 ∷ []) (Bx3-1420 ∷ []) (lem-sym-bc-at033440 c4)

-- box-perm-1324 @033440: 1 steps
lem-box-perm-1324-at033440 : Ws → ⟪ (Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ []) ⟫ʷ
lem-box-perm-1324-at033440 c4 = derive (Bx3-1240 ∷ []) (Bx3-1420 ∷ [])
  (rw 0 (q268 c4) ∷ []) Eq.refl

private
  q269 : Ws → Eqn
  q269 c4 = eqn (CCZ134 ∷ X4 ∷ CZ13 ∷ []) (X4 ∷ CCZ134 ∷ []) (wl 1279 (lit c4))
  q270 : Ws → Eqn
  q270 c4 = eqn (CZ13 ∷ Toff302 ∷ []) (Toff302 ∷ CZ13 ∷ CCZ012 ∷ []) (wl 1280 (lit c4))
  q271 : Ws → Eqn
  q271 c4 = eqn (Toff302 ∷ X4 ∷ []) (X4 ∷ Toff302 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toffᵗ • Swap ↑ ↑) • Swap ↑) (X))
  q272 : Ws → Eqn
  q272 c4 = eqn (CCZ012 ∷ []) (CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ []) (wl 155 (lit c4))
  q273 : Ws → Eqn
  q273 c4 = eqn (CCZ134 ∷ CS01 ∷ []) (CS01 ∷ CCZ134 ∷ []) (wp 261 c4)
  q274 : Ws → Eqn
  q274 c4 = eqn (CCZ134 ∷ CX12 ∷ []) (CX12 ∷ CCZ134 ∷ []) (wl 679 (lit c4))
  q275 : Ws → Eqn
  q275 c4 = eqn (CS02⁻ ∷ CCZ134 ∷ []) (CCZ134 ∷ CS02⁻ ∷ []) (lem-comm-CSd02-CCZ134 (lit c4))
  q276 : Ws → Eqn
  q276 c4 = eqn (CS02 ∷ CCZ134 ∷ []) (CCZ134 ∷ CS02 ∷ []) (lem-comm-CS02-CCZ134 (lit c4))
  q277 : Ws → Eqn
  q277 c4 = eqn (CCZ134 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ134 ∷ []) (wl 1281 (lit c4))
  q278 : Ws → Eqn
  q278 c4 = eqn (X4 ∷ CZ13 ∷ CZ13 ∷ []) (X4 ∷ []) (wl 1282 (lit c4))
  q279 : Ws → Eqn
  q279 c4 = eqn (CCZ012 ∷ Toff302 ∷ []) (Toff302 ∷ CCZ012 ∷ []) (wl 1251 (lit c4))

-- Xb-box @03243240: 18 steps
lem-Xb-box-at03243240 : Ws → ⟪ (X4 ∷ Bx3-1420 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ CCZ012 ∷ []) ⟫ʷ
lem-Xb-box-at03243240 c4 = derive (X4 ∷ Bx3-1420 ∷ X4 ∷ []) (Bx3-1420 ∷ CCZ012 ∷ [])
  (rw 1 (q211 c4) ∷
   rw⁻ 0 (q269 c4) ∷
   rw 2 (q270 c4) ∷
   rw⁻ 1 (q271 c4) ∷
   rw 4 (q272 c4) ∷
   rw⁻ 8 (q273 c4) ∷
   rw⁻ 7 (q274 c4) ∷
   rw 6 (q275 c4) ∷
   rw⁻ 5 (q274 c4) ∷
   rw 4 (q276 c4) ∷
   rw⁻ 5 (q272 c4) ∷
   rw⁻ 3 (q277 c4) ∷
   rw⁻ 2 (q269 c4) ∷
   rw 3 (q278 c4) ∷
   rw 4 (q279 c4) ∷
   rw⁻ 3 (q271 c4) ∷
   rw⁻ 0 (q211 c4) ∷
   rw⁻ 1 (q241 c4) ∷ []) Eq.refl

private
  q280 : Ws → Eqn
  q280 c4 = eqn (Bx0-1243 ∷ []) (Bx0-1423 ∷ []) (lem-sym-bc-at3443 c4)

-- box-perm-1324 @3443: 1 steps
lem-box-perm-1324-at3443 : Ws → ⟪ (Bx0-1243 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-1324-at3443 c4 = derive (Bx0-1243 ∷ []) (Bx0-1423 ∷ [])
  (rw 0 (q280 c4) ∷ []) Eq.refl

private
  q281 : Ws → Eqn
  q281 c4 = eqn (Toff302 ∷ Bx3-1420 ∷ Toff302 ∷ []) (Bx3-1420 ∷ []) (lem-P-box-at03243240 c4)
  q282 : Ws → Eqn
  q282 c4 = eqn (Bx3-2014 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at03122031 c4)

-- pairs @03243240: 4 steps
lem-pairs-at03243240 : Ws → ⟪ (Bx3-1420 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-pairs-at03243240 c4 = derive (Bx3-1420 ∷ []) (Bx3-2014 ∷ [])
  (rw⁻ 0 (q281 c4) ∷
   rw 1 (q211 c4) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 0 (q282 c4) ∷ []) Eq.refl

private
  q283 : Ws → Eqn
  q283 c4 = eqn (Bx3-0124 ∷ []) (Bx3-2401 ∷ []) (lem-pairs-at03102132 c4)
  q284 : Ws → Eqn
  q284 c4 = eqn (Bx3-2401 ∷ []) (Bx3-4201 ∷ []) (lem-sym-ab-at0312243041 c4)
  q285 : Ws → Eqn
  q285 c4 = eqn (Bx3-4201 ∷ []) (Bx3-4021 ∷ []) (lem-sym-bc-at03143041 c4)

-- box-perm-4132 @03102132: 3 steps
lem-box-perm-4132-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-4132-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-4021 ∷ [])
  (rw 0 (q283 c4) ∷
   rw 0 (q284 c4) ∷
   rw 0 (q285 c4) ∷ []) Eq.refl

private
  q286 : Ws → Eqn
  q286 c4 = eqn (Bx2-4031 ∷ []) (Bx2-4301 ∷ []) (lem-sym-bc-at02142041 c4)

-- box-perm-1324 @02142041: 1 steps
lem-box-perm-1324-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4301 ∷ []) ⟫ʷ
lem-box-perm-1324-at02142041 c4 = derive (Bx2-4031 ∷ []) (Bx2-4301 ∷ [])
  (rw 0 (q286 c4) ∷ []) Eq.refl

private
  q287 : Ws → Eqn
  q287 c4 = eqn (Bx2-4301 ∷ []) (Bx2-3401 ∷ []) (lem-sym-ab-at0214233041 c4)

-- box-perm-3124 @02142041: 2 steps
lem-box-perm-3124-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-box-perm-3124-at02142041 c4 = derive (Bx2-4031 ∷ []) (Bx2-3401 ∷ [])
  (rw 0 (q286 c4) ∷
   rw 0 (q287 c4) ∷ []) Eq.refl

private
  q288 : Ws → Eqn
  q288 c4 = eqn (Bx3-4021 ∷ []) (Bx3-4201 ∷ []) (lem-sym-bc-at0314203241 c4)
  q289 : Ws → Eqn
  q289 c4 = eqn (Bx3-4201 ∷ []) (Bx3-2401 ∷ []) (lem-sym-ab-at03143041 c4)

-- box-perm-3124 @0314203241: 2 steps
lem-box-perm-3124-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-3124-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-2401 ∷ [])
  (rw 0 (q288 c4) ∷
   rw 0 (q289 c4) ∷ []) Eq.refl

private
  q290 : Ws → Eqn
  q290 c4 = eqn (Bx2-3401 ∷ []) (Bx2-4301 ∷ []) (lem-sym-ab-at0213243041 c4)
  q291 : Ws → Eqn
  q291 c4 = eqn (Bx2-4301 ∷ []) (Bx2-0143 ∷ []) (lem-pairs-at0214233041 c4)
  q292 : Ws → Eqn
  q292 c4 = eqn (Bx2-0143 ∷ []) (Bx2-0413 ∷ []) (lem-sym-bc-at0210213443 c4)
  q293 : Ws → Eqn
  q293 c4 = eqn (Bx2-0413 ∷ []) (Bx2-4013 ∷ []) (lem-sym-ab-at0210243143 c4)

-- box-perm-2341 @0213243041: 4 steps
lem-box-perm-2341-at0213243041 : Ws → ⟪ (Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-2341-at0213243041 c4 = derive (Bx2-3401 ∷ []) (Bx2-4013 ∷ [])
  (rw 0 (q290 c4) ∷
   rw 0 (q291 c4) ∷
   rw 0 (q292 c4) ∷
   rw 0 (q293 c4) ∷ []) Eq.refl

private
  q294 : Ws → Eqn
  q294 c4 = eqn (Bx2-4013 ∷ []) (Bx2-0413 ∷ []) (lem-sym-ab-at0214203143 c4)
  q295 : Ws → Eqn
  q295 c4 = eqn (Bx2-0413 ∷ []) (Bx2-0143 ∷ []) (lem-sym-bc-at0210243143 c4)
  q296 : Ws → Eqn
  q296 c4 = eqn (Bx2-0143 ∷ []) (Bx2-4301 ∷ []) (lem-pairs-at0210213443 c4)

-- box-perm-4123 @0214203143: 4 steps
lem-box-perm-4123-at0214203143 : Ws → ⟪ (Bx2-4013 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ []) ⟫ʷ
lem-box-perm-4123-at0214203143 c4 = derive (Bx2-4013 ∷ []) (Bx2-3401 ∷ [])
  (rw 0 (q294 c4) ∷
   rw 0 (q295 c4) ∷
   rw 0 (q296 c4) ∷
   rw 0 (q287 c4) ∷ []) Eq.refl

-- box-perm-2314 @0312243041: 2 steps
lem-box-perm-2314-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4021 ∷ []) ⟫ʷ
lem-box-perm-2314-at0312243041 c4 = derive (Bx3-2401 ∷ []) (Bx3-4021 ∷ [])
  (rw 0 (q284 c4) ∷
   rw 0 (q285 c4) ∷ []) Eq.refl

private
  q297 : Ws → Eqn
  q297 c4 = eqn (Toff301 ∷ Bx3-2401 ∷ Toff301 ∷ []) (Bx3-2401 ∷ []) (lem-P-box-at0312243041 c4)
  q298 : Ws → Eqn
  q298 c4 = eqn (Toff301 ∷ Toff301 ∷ []) [] (wl 443 (lit c4))
  q299 : Ws → Eqn
  q299 c4 = eqn (Bx3-0124 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4)

-- pairs @0312243041: 4 steps
lem-pairs-at0312243041 : Ws → ⟪ (Bx3-2401 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-pairs-at0312243041 c4 = derive (Bx3-2401 ∷ []) (Bx3-0124 ∷ [])
  (rw⁻ 0 (q297 c4) ∷
   rw 1 (q254 c4) ∷
   rw 4 (q298 c4) ∷
   rw⁻ 0 (q299 c4) ∷ []) Eq.refl

private
  q300 : Ws → Eqn
  q300 c4 = eqn (Toff213 ∷ Bx2-0431 ∷ Toff213 ∷ []) (Bx2-0431 ∷ []) (lem-P-box-at02102441 c4)
  q301 : Ws → Eqn
  q301 c4 = eqn (Bx2-3104 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02132130 c4)

-- pairs @02102441: 4 steps
lem-pairs-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-pairs-at02102441 c4 = derive (Bx2-0431 ∷ []) (Bx2-3104 ∷ [])
  (rw⁻ 0 (q300 c4) ∷
   rw 1 (q99 c4) ∷
   rw 4 (q71 c4) ∷
   rw⁻ 0 (q301 c4) ∷ []) Eq.refl

private
  q302 : Ws → Eqn
  q302 c4 = eqn (Toff301 ∷ Bx3-4201 ∷ Toff301 ∷ []) (Bx3-4201 ∷ []) (lem-P-box-at03143041 c4)
  q303 : Ws → Eqn
  q303 c4 = eqn (Bx3-4201 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143041 c4)
  q304 : Ws → Eqn
  q304 c4 = eqn (Bx3-0142 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at0310213442 c4)

-- pairs @03143041: 4 steps
lem-pairs-at03143041 : Ws → ⟪ (Bx3-4201 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ []) ⟫ʷ
lem-pairs-at03143041 c4 = derive (Bx3-4201 ∷ []) (Bx3-0142 ∷ [])
  (rw⁻ 0 (q302 c4) ∷
   rw 1 (q303 c4) ∷
   rw 4 (q298 c4) ∷
   rw⁻ 0 (q304 c4) ∷ []) Eq.refl

private
  q305 : Ws → Eqn
  q305 c4 = eqn (Toff204 ∷ Bx2-3104 ∷ Toff204 ∷ []) (Bx2-3104 ∷ []) (lem-P-box-at02132130 c4)
  q306 : Ws → Eqn
  q306 c4 = eqn (Bx2-3104 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at02132130 c4)
  q307 : Ws → Eqn
  q307 c4 = eqn (Bx2-0431 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4)

-- pairs @02132130: 4 steps
lem-pairs-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-pairs-at02132130 c4 = derive (Bx2-3104 ∷ []) (Bx2-0431 ∷ [])
  (rw⁻ 0 (q305 c4) ∷
   rw 1 (q306 c4) ∷
   rw 4 (q90 c4) ∷
   rw⁻ 0 (q307 c4) ∷ []) Eq.refl

-- box-perm-1324 @0314203241: 1 steps
lem-box-perm-1324-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4201 ∷ []) ⟫ʷ
lem-box-perm-1324-at0314203241 c4 = derive (Bx3-4021 ∷ []) (Bx3-4201 ∷ [])
  (rw 0 (q288 c4) ∷ []) Eq.refl

private
  q308 : Ws → Eqn
  q308 c4 = eqn (Bx3-4012 ∷ []) (Bx3-0412 ∷ []) (lem-sym-ab-at0314203142 c4)
  q309 : Ws → Eqn
  q309 c4 = eqn (Bx3-0142 ∷ []) (Bx3-4201 ∷ []) (lem-pairs-at0310213442 c4)

-- box-perm-4123 @0314203142: 4 steps
lem-box-perm-4123-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2401 ∷ []) ⟫ʷ
lem-box-perm-4123-at0314203142 c4 = derive (Bx3-4012 ∷ []) (Bx3-2401 ∷ [])
  (rw 0 (q308 c4) ∷
   rw 0 (q246 c4) ∷
   rw 0 (q309 c4) ∷
   rw 0 (q289 c4) ∷ []) Eq.refl

private
  q310 : Ws → Eqn
  q310 c4 = eqn (Bx2-3401 ∷ []) (Bx2-0134 ∷ []) (lem-pairs-at0213243041 c4)

-- box-perm-2431 @02142041: 3 steps
lem-box-perm-2431-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2431-at02142041 c4 = derive (Bx2-4031 ∷ []) (Bx2-0134 ∷ [])
  (rw 0 (q286 c4) ∷
   rw 0 (q287 c4) ∷
   rw 0 (q310 c4) ∷ []) Eq.refl

private
  q311 : Ws → Eqn
  q311 c4 = eqn (Toff312 ∷ Bx3-0421 ∷ Toff312 ∷ []) (Bx3-0421 ∷ []) (lem-P-box-at0310243241 c4)
  q312 : Ws → Eqn
  q312 c4 = eqn (Bx3-2104 ∷ []) (Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ []) (lem-box-tQ-at03122130 c4)

-- pairs @0310243241: 4 steps
lem-pairs-at0310243241 : Ws → ⟪ (Bx3-0421 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-pairs-at0310243241 c4 = derive (Bx3-0421 ∷ []) (Bx3-2104 ∷ [])
  (rw⁻ 0 (q311 c4) ∷
   rw 1 (q229 c4) ∷
   rw 4 (q209 c4) ∷
   rw⁻ 0 (q312 c4) ∷ []) Eq.refl

private
  q313 : Ws → Eqn
  q313 c4 = eqn (Bx2-0134 ∷ []) (Bx2-3401 ∷ []) (lem-pairs-at021021 c4)

-- box-perm-1243 @021021: 3 steps
lem-box-perm-1243-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0143 ∷ []) ⟫ʷ
lem-box-perm-1243-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-0143 ∷ [])
  (rw 0 (q313 c4) ∷
   rw 0 (q290 c4) ∷
   rw 0 (q291 c4) ∷ []) Eq.refl

-- box-perm-1243 @0210213443: 3 steps
lem-box-perm-1243-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-1243-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Bx2-0134 ∷ [])
  (rw 0 (q296 c4) ∷
   rw 0 (q287 c4) ∷
   rw 0 (q310 c4) ∷ []) Eq.refl

private
  q314 : Ws → Eqn
  q314 c4 = eqn (Toff304 ∷ Bx3-2104 ∷ Toff304 ∷ []) (Bx3-2104 ∷ []) (lem-P-box-at03122130 c4)
  q315 : Ws → Eqn
  q315 c4 = eqn (Bx3-2104 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at03122130 c4)
  q316 : Ws → Eqn
  q316 c4 = eqn (Bx3-0421 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0310243241 c4)

-- pairs @03122130: 4 steps
lem-pairs-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0421 ∷ []) ⟫ʷ
lem-pairs-at03122130 c4 = derive (Bx3-2104 ∷ []) (Bx3-0421 ∷ [])
  (rw⁻ 0 (q314 c4) ∷
   rw 1 (q315 c4) ∷
   rw 4 (q218 c4) ∷
   rw⁻ 0 (q316 c4) ∷ []) Eq.refl

private
  q317 : Ws → Eqn
  q317 c4 = eqn (Bx2-4301 ∷ []) (Bx2-4031 ∷ []) (lem-sym-bc-at0214233041 c4)

-- box-perm-4132 @021021: 3 steps
lem-box-perm-4132-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ []) ⟫ʷ
lem-box-perm-4132-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-4031 ∷ [])
  (rw 0 (q313 c4) ∷
   rw 0 (q290 c4) ∷
   rw 0 (q317 c4) ∷ []) Eq.refl

private
  q318 : Ws → Eqn
  q318 c4 = eqn (Bx2-4031 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4)
  q319 : Ws → Eqn
  q319 c4 = eqn (Bx2-4031 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02142041 c4)
  q320 : Ws → Eqn
  q320 c4 = eqn (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff204 ∷ []) (lem-t-cP-at02142041 c4)

-- box2 @02142041: 11 steps
lem-box2-at02142041 : Ws → ⟪ (Bx2-4031 ∷ Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at02142041 c4 = derive (Bx2-4031 ∷ Bx2-4031 ∷ []) []
  (rw 0 (q318 c4) ∷
   rw 4 (q319 c4) ∷
   rw⁻ 4 (q90 c4) ∷
   rw 5 (q320 c4) ∷
   rw⁻ 5 (q319 c4) ∷
   rw 5 (q318 c4) ∷
   rw 4 (q90 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q90 c4) ∷
   rw 1 (q223 c4) ∷
   rw 0 (q90 c4) ∷ []) Eq.refl

private
  q321 : Ws → Eqn
  q321 c4 = eqn (Bx3-4021 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4)
  q322 : Ws → Eqn
  q322 c4 = eqn (Bx3-4021 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0314203241 c4)
  q323 : Ws → Eqn
  q323 c4 = eqn (Toff304 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff304 ∷ []) (lem-t-cP-at0314203241 c4)

-- box2 @0314203241: 11 steps
lem-box2-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0314203241 c4 = derive (Bx3-4021 ∷ Bx3-4021 ∷ []) []
  (rw 0 (q321 c4) ∷
   rw 4 (q322 c4) ∷
   rw⁻ 4 (q218 c4) ∷
   rw 5 (q323 c4) ∷
   rw⁻ 5 (q322 c4) ∷
   rw 5 (q321 c4) ∷
   rw 4 (q218 c4) ∷
   rw 3 (q223 c4) ∷
   rw 2 (q218 c4) ∷
   rw 1 (q223 c4) ∷
   rw 0 (q218 c4) ∷ []) Eq.refl

private
  q324 : Ws → Eqn
  q324 c4 = eqn (Bx2-3104 ∷ []) (Bx2-1304 ∷ []) (lem-sym-ab-at02132130 c4)
  q325 : Ws → Eqn
  q325 c4 = eqn (Bx2-1304 ∷ []) (Bx2-1034 ∷ []) (lem-sym-bc-at022330 c4)

-- box-perm-2314 @02132130: 2 steps
lem-box-perm-2314-at02132130 : Ws → ⟪ (Bx2-3104 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-box-perm-2314-at02132130 c4 = derive (Bx2-3104 ∷ []) (Bx2-1034 ∷ [])
  (rw 0 (q324 c4) ∷
   rw 0 (q325 c4) ∷ []) Eq.refl

private
  q326 : Ws → Eqn
  q326 c4 = eqn (Bx3-2104 ∷ []) (Bx3-1204 ∷ []) (lem-sym-ab-at03122130 c4)
  q327 : Ws → Eqn
  q327 c4 = eqn (Bx3-1204 ∷ []) (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4)

-- box-perm-2314 @03122130: 2 steps
lem-box-perm-2314-at03122130 : Ws → ⟪ (Bx3-2104 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2314-at03122130 c4 = derive (Bx3-2104 ∷ []) (Bx3-1024 ∷ [])
  (rw 0 (q326 c4) ∷
   rw 0 (q327 c4) ∷ []) Eq.refl

private
  q328 : Ws → Eqn
  q328 c4 = eqn (Bx3-2014 ∷ []) (Bx3-0214 ∷ []) (lem-sym-ab-at03122031 c4)
  q329 : Ws → Eqn
  q329 c4 = eqn (Bx3-0214 ∷ []) (Bx3-0124 ∷ []) (lem-sym-bc-at031031 c4)
  q330 : Ws → Eqn
  q330 c4 = eqn (Bx3-0124 ∷ []) (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4)

-- box-perm-3214 @03122031: 3 steps
lem-box-perm-3214-at03122031 : Ws → ⟪ (Bx3-2014 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-3214-at03122031 c4 = derive (Bx3-2014 ∷ []) (Bx3-1024 ∷ [])
  (rw 0 (q328 c4) ∷
   rw 0 (q329 c4) ∷
   rw 0 (q330 c4) ∷ []) Eq.refl

private
  q331 : Ws → Eqn
  q331 c4 = eqn (Toff314 ∷ Bx3-0214 ∷ Toff314 ∷ []) (Bx3-0214 ∷ []) (lem-P-box-at031031 c4)
  q332 : Ws → Eqn
  q332 c4 = eqn (Bx3-0214 ∷ []) (CCZ023 ∷ Toff314 ∷ CCZ023 ∷ Toff314 ∷ []) (lem-box-cP-at031031 c4)
  q333 : Ws → Eqn
  q333 c4 = eqn (Bx3-1402 ∷ []) (Toff314 ∷ CCZ023 ∷ Toff314 ∷ CCZ023 ∷ []) (lem-box-tQ-at03243042 c4)

-- pairs @031031: 4 steps
lem-pairs-at031031 : Ws → ⟪ (Bx3-0214 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1402 ∷ []) ⟫ʷ
lem-pairs-at031031 c4 = derive (Bx3-0214 ∷ []) (Bx3-1402 ∷ [])
  (rw⁻ 0 (q331 c4) ∷
   rw 1 (q332 c4) ∷
   rw 4 (q212 c4) ∷
   rw⁻ 0 (q333 c4) ∷ []) Eq.refl

private
  q334 : Ws → Eqn
  q334 c4 = eqn (Bx0-4132 ∷ []) (Bx0-4312 ∷ []) (lem-sym-bc-at142142 c4)

-- box-perm-1324 @142142: 1 steps
lem-box-perm-1324-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-box-perm-1324-at142142 c4 = derive (Bx0-4132 ∷ []) (Bx0-4312 ∷ [])
  (rw 0 (q334 c4) ∷ []) Eq.refl

private
  q335 : Ws → Eqn
  q335 c4 = eqn (Bx0-4312 ∷ []) (Bx0-3412 ∷ []) (lem-sym-ab-at14233142 c4)

-- box-perm-3124 @142142: 2 steps
lem-box-perm-3124-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-3124-at142142 c4 = derive (Bx0-4132 ∷ []) (Bx0-3412 ∷ [])
  (rw 0 (q334 c4) ∷
   rw 0 (q335 c4) ∷ []) Eq.refl

private
  q336 : Ws → Eqn
  q336 c4 = eqn (Bx0-3412 ∷ []) (Bx0-4312 ∷ []) (lem-sym-ab-at13243142 c4)
  q337 : Ws → Eqn
  q337 c4 = eqn (Bx0-4312 ∷ []) (Bx0-1243 ∷ []) (lem-pairs-at14233142 c4)

-- box-perm-2341 @13243142: 4 steps
lem-box-perm-2341-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4123 ∷ []) ⟫ʷ
lem-box-perm-2341-at13243142 c4 = derive (Bx0-3412 ∷ []) (Bx0-4123 ∷ [])
  (rw 0 (q336 c4) ∷
   rw 0 (q337 c4) ∷
   rw 0 (q280 c4) ∷
   rw 0 (q144 c4) ∷ []) Eq.refl

private
  q338 : Ws → Eqn
  q338 c4 = eqn (Toff302 ∷ Bx3-1402 ∷ Toff302 ∷ []) (Bx3-1402 ∷ []) (lem-P-box-at03243042 c4)
  q339 : Ws → Eqn
  q339 c4 = eqn (Bx3-1402 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243042 c4)
  q340 : Ws → Eqn
  q340 c4 = eqn (Bx3-0214 ∷ []) (Toff302 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ []) (lem-box-tQ-at031031 c4)

-- pairs @03243042: 4 steps
lem-pairs-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-pairs-at03243042 c4 = derive (Bx3-1402 ∷ []) (Bx3-0214 ∷ [])
  (rw⁻ 0 (q338 c4) ∷
   rw 1 (q339 c4) ∷
   rw 4 (q226 c4) ∷
   rw⁻ 0 (q340 c4) ∷ []) Eq.refl

private
  q341 : Ws → Eqn
  q341 c4 = eqn (Toff023 ∷ Bx0-1432 ∷ Toff023 ∷ []) (Bx0-1432 ∷ []) (lem-P-box-at2442 c4)
  q342 : Ws → Eqn
  q342 c4 = eqn (Toff023 ∷ Toff023 ∷ []) [] (wl 203 (lit c4))
  q343 : Ws → Eqn
  q343 c4 = eqn (Bx0-3214 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at1331 c4)

-- pairs @2442: 4 steps
lem-pairs-at2442 : Ws → ⟪ (Bx0-1432 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3214 ∷ []) ⟫ʷ
lem-pairs-at2442 c4 = derive (Bx0-1432 ∷ []) (Bx0-3214 ∷ [])
  (rw⁻ 0 (q341 c4) ∷
   rw 1 (q113 c4) ∷
   rw 4 (q342 c4) ∷
   rw⁻ 0 (q343 c4) ∷ []) Eq.refl

private
  q344 : Ws → Eqn
  q344 c4 = eqn (Bx2-3014 ∷ []) (Bx2-0314 ∷ []) (lem-sym-ab-at02132031 c4)
  q345 : Ws → Eqn
  q345 c4 = eqn (Bx2-0314 ∷ []) (Bx2-0134 ∷ []) (lem-sym-bc-at02102331 c4)

-- box-perm-2314 @02132031: 2 steps
lem-box-perm-2314-at02132031 : Ws → ⟪ (Bx2-3014 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-2314-at02132031 c4 = derive (Bx2-3014 ∷ []) (Bx2-0134 ∷ [])
  (rw 0 (q344 c4) ∷
   rw 0 (q345 c4) ∷ []) Eq.refl

private
  q346 : Ws → Eqn
  q346 c4 = eqn (Bx0-4132 ∷ []) (Toff014 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ []) (lem-box-tQ-at142142 c4)
  q347 : Ws → Eqn
  q347 c4 = eqn (Bx0-4132 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at142142 c4)
  q348 : Ws → Eqn
  q348 c4 = eqn (Toff014 ∷ Toff014 ∷ []) [] (wp 51 c4)
  q349 : Ws → Eqn
  q349 c4 = eqn (Toff014 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff014 ∷ []) (lem-t-cP-at142142 c4)

-- box2 @142142: 11 steps
lem-box2-at142142 : Ws → ⟪ (Bx0-4132 ∷ Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at142142 c4 = derive (Bx0-4132 ∷ Bx0-4132 ∷ []) []
  (rw 0 (q346 c4) ∷
   rw 4 (q347 c4) ∷
   rw⁻ 4 (q348 c4) ∷
   rw 5 (q349 c4) ∷
   rw⁻ 5 (q347 c4) ∷
   rw 5 (q346 c4) ∷
   rw 4 (q348 c4) ∷
   rw 3 (q214 c4) ∷
   rw 2 (q348 c4) ∷
   rw 1 (q214 c4) ∷
   rw 0 (q348 c4) ∷ []) Eq.refl

private
  q350 : Ws → Eqn
  q350 c4 = eqn (Bx0-3412 ∷ []) (Bx0-1234 ∷ []) (lem-pairs-at13243142 c4)

-- box-perm-2431 @142142: 3 steps
lem-box-perm-2431-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-2431-at142142 c4 = derive (Bx0-4132 ∷ []) (Bx0-1234 ∷ [])
  (rw 0 (q334 c4) ∷
   rw 0 (q335 c4) ∷
   rw 0 (q350 c4) ∷ []) Eq.refl

private
  q351 : Ws → Eqn
  q351 c4 = eqn (Toff312 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff312 ∷ []) (lem-t-cP-at033440 c4)
  q352 : Ws → Eqn
  q352 c4 = eqn (CCZ034 ∷ CCZ034 ∷ []) [] (wp 7 c4)

-- box2 @033440: 11 steps
lem-box2-at033440 : Ws → ⟪ (Bx3-1240 ∷ Bx3-1240 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at033440 c4 = derive (Bx3-1240 ∷ Bx3-1240 ∷ []) []
  (rw 0 (q210 c4) ∷
   rw 4 (q217 c4) ∷
   rw⁻ 4 (q209 c4) ∷
   rw 5 (q351 c4) ∷
   rw⁻ 5 (q217 c4) ∷
   rw 5 (q210 c4) ∷
   rw 4 (q209 c4) ∷
   rw 3 (q352 c4) ∷
   rw 2 (q209 c4) ∷
   rw 1 (q352 c4) ∷
   rw 0 (q209 c4) ∷ []) Eq.refl
