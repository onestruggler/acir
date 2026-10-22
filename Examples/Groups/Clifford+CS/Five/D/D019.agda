{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD019 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D019 (Sᴰ : SD019) where

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
  lem-comm-CS12-CCZ034 : Ws → St 191
  lem-comm-CS12-CCZ034 = pickᴰ 0 Sᴰ
  lem-comm-CS13-CCZ024 : Ws → St 958
  lem-comm-CS13-CCZ024 = pickᴰ 1 Sᴰ
  lem-comm-CS23-CCZ014 : Ws → St 703
  lem-comm-CS23-CCZ014 = pickᴰ 2 Sᴰ
  lem-comm-CSd12-CCZ034 : Ws → St 199
  lem-comm-CSd12-CCZ034 = pickᴰ 3 Sᴰ
  lem-comm-CSd13-CCZ024 : Ws → St 960
  lem-comm-CSd13-CCZ024 = pickᴰ 4 Sᴰ
  lem-comm-CSd23-CCZ014 : Ws → St 704
  lem-comm-CSd23-CCZ014 = pickᴰ 5 Sᴰ
  lem-comm-CX04-CCZ123 : Ws → St 1
  lem-comm-CX04-CCZ123 = pickᴰ 6 Sᴰ
  lem-comm-CX04-TOFF213 : Ws → St 1023
  lem-comm-CX04-TOFF213 = pickᴰ 7 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 8 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 9 Sᴰ
  lem-comm-CS02-CCZ134 : Ws → St 431
  lem-comm-CS02-CCZ134 = pickᴰ 10 Sᴰ
  lem-comm-CS14-CCZ023 : Ws → St 219
  lem-comm-CS14-CCZ023 = pickᴰ 11 Sᴰ
  lem-comm-CSd02-CCZ134 : Ws → St 432
  lem-comm-CSd02-CCZ134 = pickᴰ 12 Sᴰ
  lem-comm-CSd14-CCZ023 : Ws → St 224
  lem-comm-CSd14-CCZ023 = pickᴰ 13 Sᴰ
  lem-comm-CX04-TOFF312 : Ws → St 1025
  lem-comm-CX04-TOFF312 = pickᴰ 14 Sᴰ
  lem-comm-CX30-TOFF214 : Ws → St 1026
  lem-comm-CX30-TOFF214 = pickᴰ 15 Sᴰ
  lem-comm-TOFF013-CK42 : Ws → St 1027
  lem-comm-TOFF013-CK42 = pickᴰ 16 Sᴰ
  lem-comm-TOFF213-CX04 : Ws → St 1028
  lem-comm-TOFF213-CX04 = pickᴰ 17 Sᴰ
  lem-sym-ab-at0210243143 : Ws → St 53
  lem-sym-ab-at0210243143 = pickᴰ 18 Sᴰ
  lem-sym-ab-at0214203143 : Ws → St 1029
  lem-sym-ab-at0214203143 = pickᴰ 19 Sᴰ
  lem-sym-ab-at03102132 : Ws → St 40
  lem-sym-ab-at03102132 = pickᴰ 20 Sᴰ
  lem-sym-ab-at0310243142 : Ws → St 894
  lem-sym-ab-at0310243142 = pickᴰ 21 Sᴰ
  lem-sym-ab-at0312213440 : Ws → St 1030
  lem-sym-ab-at0312213440 = pickᴰ 22 Sᴰ
  lem-sym-ab-at0314203142 : Ws → St 1031
  lem-sym-ab-at0314203142 = pickᴰ 23 Sᴰ
  lem-sym-ab-at122441 : Ws → St 972
  lem-sym-ab-at122441 = pickᴰ 24 Sᴰ
  lem-sym-ab-at021021 : Ws → St 59
  lem-sym-ab-at021021 = pickᴰ 25 Sᴰ
  lem-sym-ab-at0213213440 : Ws → St 1032
  lem-sym-ab-at0213213440 = pickᴰ 26 Sᴰ
  lem-sym-ab-at0220 : Ws → St 60
  lem-sym-ab-at0220 = pickᴰ 27 Sᴰ
  lem-sym-ab-at02233440 : Ws → St 1033
  lem-sym-ab-at02233440 = pickᴰ 28 Sᴰ
  lem-sym-ab-at14233241 : Ws → St 1034
  lem-sym-ab-at14233241 = pickᴰ 29 Sᴰ
  lem-box-tQ-at032032 : Ws → St 83
  lem-box-tQ-at032032 = pickᴰ 30 Sᴰ
  lem-box-tQ-at0210243143 : Ws → St 248
  lem-box-tQ-at0210243143 = pickᴰ 31 Sᴰ
  lem-box-tQ-at0214213043 : Ws → St 250
  lem-box-tQ-at0214213043 = pickᴰ 32 Sᴰ
  lem-box-tQ-at022330 : Ws → St 307
  lem-box-tQ-at022330 = pickᴰ 33 Sᴰ
  lem-box-tQ-at0310243142 : Ws → St 251
  lem-box-tQ-at0310243142 = pickᴰ 34 Sᴰ
  lem-box-tQ-at0314213042 : Ws → St 311
  lem-box-tQ-at0314213042 = pickᴰ 35 Sᴰ
  lem-box-tQ-at122331 : Ws → St 255
  lem-box-tQ-at122331 = pickᴰ 36 Sᴰ
  lem-P-box-at0210233441 : Ws → St 1035
  lem-P-box-at0210233441 = pickᴰ 37 Sᴰ
  lem-P-box-at0210243143 : Ws → St 1036
  lem-P-box-at0210243143 = pickᴰ 38 Sᴰ
  lem-P-box-at022330 : Ws → St 1037
  lem-P-box-at022330 = pickᴰ 39 Sᴰ
  lem-P-box-at0312243140 : Ws → St 1038
  lem-P-box-at0312243140 = pickᴰ 40 Sᴰ
  lem-P-box-at243243 : Ws → St 1039
  lem-P-box-at243243 = pickᴰ 41 Sᴰ
  lem-t-cP-at0314213042 : Ws → St 1040
  lem-t-cP-at0314213042 = pickᴰ 42 Sᴰ
  lem-sym-bc-at0213243140 : Ws → St 1041
  lem-sym-bc-at0213243140 = pickᴰ 43 Sᴰ
  lem-box-cP-at0210233441 : Ws → St 1042
  lem-box-cP-at0210233441 = pickᴰ 44 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 994
  lem-box-cP-at0210243143 = pickᴰ 45 Sᴰ
  lem-box-cP-at0213203441 : Ws → St 1043
  lem-box-cP-at0213203441 = pickᴰ 46 Sᴰ
  lem-box-cP-at022330 : Ws → St 1044
  lem-box-cP-at022330 = pickᴰ 47 Sᴰ
  lem-box-cP-at0310243142 : Ws → St 996
  lem-box-cP-at0310243142 = pickᴰ 48 Sᴰ
  lem-box-cP-at0312243140 : Ws → St 1045
  lem-box-cP-at0312243140 = pickᴰ 49 Sᴰ
  lem-box-cP-at0314213042 : Ws → St 1046
  lem-box-cP-at0314213042 = pickᴰ 50 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 51 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 52 Sᴰ
  lem-pairs-at0213243140 : Ws → St 1047
  lem-pairs-at0213243140 = pickᴰ 53 Sᴰ
  lem-pairs-at0220 : Ws → St 1048
  lem-pairs-at0220 = pickᴰ 54 Sᴰ
  lem-pairs-at032032 : Ws → St 1049
  lem-pairs-at032032 = pickᴰ 55 Sᴰ
  lem-pairs-at13243241 : Ws → St 1011
  lem-pairs-at13243241 = pickᴰ 56 Sᴰ
  lem-sym-bc-at0213213440 : Ws → St 1050
  lem-sym-bc-at0213213440 = pickᴰ 57 Sᴰ
  lem-sym-bc-at0214203143 : Ws → St 1051
  lem-sym-bc-at0214203143 = pickᴰ 58 Sᴰ
  lem-sym-bc-at0214213043 : Ws → St 1052
  lem-sym-bc-at0214213043 = pickᴰ 59 Sᴰ
  lem-sym-bc-at0312243140 : Ws → St 1053
  lem-sym-bc-at0312243140 = pickᴰ 60 Sᴰ
  lem-sym-bc-at0314203142 : Ws → St 1054
  lem-sym-bc-at0314203142 = pickᴰ 61 Sᴰ
  lem-sym-bc-at0314213042 : Ws → St 1055
  lem-sym-bc-at0314213042 = pickᴰ 62 Sᴰ
  lem-sym-bc-at1441 : Ws → St 1021
  lem-sym-bc-at1441 = pickᴰ 63 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = wlE 725 (lit c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 742 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q4 : Ws → Eqn
  q4 c4 = wlE 743 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1027 (lem-comm-TOFF013-CK42 c4)
  q6 : Ws → Eqn
  q6 c4 = eqn (Toff013 ∷ S4 ∷ []) (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S))
  q7 : Ws → Eqn
  q7 c4 = wpE 649 c4
  q8 : Ws → Eqn
  q8 c4 = wlE 728 (lit c4)

-- F4-CS2-K2: 19 steps
lem-F4-CS2-K2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K2 c4 = derive (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  (rw⁻ 2 (q1 c4) ∷
   re 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 3 1 (CS12 ∷ []) ∷
   re 5 1 (CS12⁻ ∷ []) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 1 (q3 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 6 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 1 (q7 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   re 6 1 (Sb0-2-1-3 ∷ []) ∷
   re 8 1 (Sb⁻0-2-1-3 ∷ []) ∷
   re 4 5 (Sb0-2-43-1 ∷ []) ∷
   rw⁻ 0 (q8 c4) ∷ []) Eq.refl

private
  q9 : Ws → Eqn
  q9 c4 = sE 994 (lem-box-cP-at0210243143 c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 20 c4
  q11 : Ws → Eqn
  q11 c4 = wlE 183 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = eqn (Toff213 ∷ X4 ∷ []) (X4 ∷ Toff213 ∷ []) (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))
  q13 : Ws → Eqn
  q13 c4 = wlE 184 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wpE 21 c4
  q15 : Ws → Eqn
  q15 c4 = wpE 22 c4
  q16 : Ws → Eqn
  q16 c4 = sE 960 (lem-comm-CSd13-CCZ024 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 958 (lem-comm-CS13-CCZ024 c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 23 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 185 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 186 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 32 c4
  q22 : Ws → Eqn
  q22 c4 = wlE 191 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = wlE 190 (lit c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 33 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 34 c4
  q26 : Ws → Eqn
  q26 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 35 c4
  q28 : Ws → Eqn
  q28 c4 = wpE 36 c4
  q29 : Ws → Eqn
  q29 c4 = wpE 37 c4
  q30 : Ws → Eqn
  q30 c4 = wlE 192 (lit c4)
  q31 : Ws → Eqn
  q31 c4 = wpE 42 c4
  q32 : Ws → Eqn
  q32 c4 = wpE 41 c4
  q33 : Ws → Eqn
  q33 c4 = wlE 193 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1023 (lem-comm-CX04-TOFF213 c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 194 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 195 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 197 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wpE 44 c4
  q39 : Ws → Eqn
  q39 c4 = wlE 196 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 650 c4
  q41 : Ws → Eqn
  q41 c4 = wlE 230 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wpE 651 c4
  q43 : Ws → Eqn
  q43 c4 = wpE 161 c4
  q44 : Ws → Eqn
  q44 c4 = wlE 745 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 652 c4
  q46 : Ws → Eqn
  q46 c4 = wlE 746 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 747 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wpE 653 c4
  q49 : Ws → Eqn
  q49 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 654 c4
  q51 : Ws → Eqn
  q51 c4 = wlE 748 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = sE 1028 (lem-comm-TOFF213-CX04 c4)
  q53 : Ws → Eqn
  q53 c4 = wpE 655 c4
  q54 : Ws → Eqn
  q54 c4 = wpE 656 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 187 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 657 c4
  q57 : Ws → Eqn
  q57 c4 = wpE 658 c4
  q58 : Ws → Eqn
  q58 c4 = wpE 659 c4
  q59 : Ws → Eqn
  q59 c4 = wpE 660 c4

-- F4-CS0-CS0: 286 steps
lem-F4-CS0-CS0 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS0 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 4 (q11 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 10 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 8 (q16 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 6 (q17 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw⁻ 5 (q18 c4) ∷
   rw⁻ 4 (q10 c4) ∷
   rw 5 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw 6 (q9 c4) ∷
   rw⁻ 5 (q21 c4) ∷
   rw 6 (q22 c4) ∷
   rw⁻ 7 (q21 c4) ∷
   rw 8 (q22 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw⁻ 10 (q24 c4) ∷
   rw⁻ 9 (q25 c4) ∷
   rw 8 (q26 c4) ∷
   rw⁻ 7 (q27 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw⁻ 4 (q29 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 5 (q30 c4) ∷
   rw⁻ 7 (q23 c4) ∷
   rw⁻ 13 (q24 c4) ∷
   rw⁻ 12 (q25 c4) ∷
   rw 11 (q26 c4) ∷
   rw⁻ 10 (q27 c4) ∷
   rw 9 (q26 c4) ∷
   rw⁻ 8 (q28 c4) ∷
   rw⁻ 7 (q29 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 6 (q31 c4) ∷
   rw⁻ 9 (q30 c4) ∷
   rw 8 (q32 c4) ∷
   rw 12 (q33 c4) ∷
   rw 11 (q34 c4) ∷
   rw 10 (q35 c4) ∷
   rw 9 (q34 c4) ∷
   rw 8 (q36 c4) ∷
   rw⁻ 9 (q32 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw⁻ 8 (q38 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 3 1 (CS03 ∷ []) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 3 (q14 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 5 (q14 c4) ∷
   rw 6 (q39 c4) ∷
   rw⁻ 3 (q9 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   rw⁻ 8 (q24 c4) ∷
   rw⁻ 7 (q25 c4) ∷
   rw 6 (q26 c4) ∷
   rw⁻ 5 (q27 c4) ∷
   rw 4 (q26 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 3 (q30 c4) ∷
   rw⁻ 5 (q23 c4) ∷
   rw⁻ 11 (q24 c4) ∷
   rw⁻ 10 (q25 c4) ∷
   rw 9 (q26 c4) ∷
   rw⁻ 8 (q27 c4) ∷
   rw 7 (q26 c4) ∷
   rw⁻ 6 (q28 c4) ∷
   rw⁻ 5 (q29 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 4 (q31 c4) ∷
   rw⁻ 7 (q30 c4) ∷
   rw 6 (q32 c4) ∷
   rw 10 (q33 c4) ∷
   rw 9 (q34 c4) ∷
   rw 8 (q35 c4) ∷
   rw 7 (q34 c4) ∷
   rw 6 (q36 c4) ∷
   rw⁻ 7 (q32 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw⁻ 6 (q38 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 1 (q9 c4) ∷
   rw⁻ 0 (q10 c4) ∷
   rw 2 (q11 c4) ∷
   rw⁻ 1 (q12 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw⁻ 3 (q18 c4) ∷
   rw⁻ 2 (q10 c4) ∷
   rw 3 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q12 c4) ∷
   rw⁻ 0 (q9 c4) ∷
   rw 3 (q9 c4) ∷
   rw 2 (q13 c4) ∷
   rw⁻ 6 (q14 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 4 (q16 c4) ∷
   rw⁻ 3 (q15 c4) ∷
   rw 2 (q17 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw 3 (q20 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 8 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q15 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 5 (q20 c4) ∷
   rw⁻ 2 (q9 c4) ∷
   rw 3 (q40 c4) ∷
   rw 10 (q41 c4) ∷
   rw 3 (q42 c4) ∷
   rw 5 (q43 c4) ∷
   re 4 1 (Sb2-0-3-1 ∷ []) ∷
   re 6 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 2 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q44 c4) ∷
   re 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 4 1 (CS03 ∷ []) ∷
   re 6 1 (CS03⁻ ∷ []) ∷
   rw⁻ 3 (q45 c4) ∷
   rw 2 (q9 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw 7 (q47 c4) ∷
   rw 4 (q48 c4) ∷
   rw 6 (q49 c4) ∷
   rw 7 (q50 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw 9 (q29 c4) ∷
   rw 10 (q28 c4) ∷
   rw 11 (q49 c4) ∷
   rw 12 (q27 c4) ∷
   rw 13 (q49 c4) ∷
   rw 14 (q25 c4) ∷
   rw 15 (q24 c4) ∷
   rw 9 (q23 c4) ∷
   rw⁻ 3 (q51 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 5 (q52 c4) ∷
   rw⁻ 6 (q35 c4) ∷
   rw 7 (q52 c4) ∷
   rw⁻ 8 (q33 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw⁻ 5 (q46 c4) ∷
   rw 7 (q37 c4) ∷
   rw 9 (q32 c4) ∷
   rw⁻ 8 (q36 c4) ∷
   rw 9 (q52 c4) ∷
   rw⁻ 10 (q35 c4) ∷
   rw 11 (q52 c4) ∷
   rw⁻ 12 (q33 c4) ∷
   rw⁻ 8 (q32 c4) ∷
   rw 9 (q47 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw 3 (q54 c4) ∷
   rw 2 (q49 c4) ∷
   rw⁻ 4 (q23 c4) ∷
   rw 3 (q29 c4) ∷
   rw 4 (q28 c4) ∷
   rw 5 (q49 c4) ∷
   rw 6 (q27 c4) ∷
   rw 7 (q49 c4) ∷
   rw 8 (q25 c4) ∷
   rw 9 (q24 c4) ∷
   rw 3 (q23 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 1 (q55 c4) ∷
   rw⁻ 4 (q56 c4) ∷
   re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw⁻ 4 (q57 c4) ∷
   rw 3 (q9 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 4 (q39 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q9 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 2 (q56 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   re 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 6 1 (CS03 ∷ []) ∷
   re 8 1 (CS03⁻ ∷ []) ∷
   rw⁻ 5 (q45 c4) ∷
   rw 4 (q9 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 9 (q47 c4) ∷
   rw 6 (q48 c4) ∷
   rw 8 (q49 c4) ∷
   rw 9 (q50 c4) ∷
   rw⁻ 12 (q23 c4) ∷
   rw 11 (q29 c4) ∷
   rw 12 (q28 c4) ∷
   rw 13 (q49 c4) ∷
   rw 14 (q27 c4) ∷
   rw 15 (q49 c4) ∷
   rw 16 (q25 c4) ∷
   rw 17 (q24 c4) ∷
   rw 11 (q23 c4) ∷
   rw⁻ 5 (q51 c4) ∷
   rw 7 (q32 c4) ∷
   rw⁻ 6 (q36 c4) ∷
   rw 7 (q52 c4) ∷
   rw⁻ 8 (q35 c4) ∷
   rw 9 (q52 c4) ∷
   rw⁻ 10 (q33 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw⁻ 7 (q46 c4) ∷
   rw 9 (q37 c4) ∷
   rw 11 (q32 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw 11 (q52 c4) ∷
   rw⁻ 12 (q35 c4) ∷
   rw 13 (q52 c4) ∷
   rw⁻ 14 (q33 c4) ∷
   rw⁻ 10 (q32 c4) ∷
   rw 11 (q47 c4) ∷
   rw⁻ 5 (q53 c4) ∷
   rw⁻ 7 (q38 c4) ∷
   rw 5 (q54 c4) ∷
   rw 4 (q49 c4) ∷
   rw⁻ 6 (q23 c4) ∷
   rw 5 (q29 c4) ∷
   rw 6 (q28 c4) ∷
   rw 7 (q49 c4) ∷
   rw 8 (q27 c4) ∷
   rw 9 (q49 c4) ∷
   rw 10 (q25 c4) ∷
   rw 11 (q24 c4) ∷
   rw 5 (q23 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 3 (q55 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   re 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 7 1 (CS03 ∷ []) ∷
   re 9 1 (CS03⁻ ∷ []) ∷
   rw⁻ 6 (q59 c4) ∷
   rw 5 (q9 c4) ∷
   rw⁻ 8 (q22 c4) ∷
   rw 7 (q21 c4) ∷
   rw⁻ 6 (q22 c4) ∷
   rw 5 (q21 c4) ∷
   rw⁻ 6 (q9 c4) ∷
   re 8 1 (Sb2-0-3-1 ∷ []) ∷
   re 10 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 6 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 4 (q58 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = sE 53 (lem-sym-ab-at0210243143 c4)
  q61 : Ws → Eqn
  q61 c4 = sE 1051 (lem-sym-bc-at0214203143 c4)

-- box-perm-2314 @0210243143: 2 steps
lem-box-perm-2314-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-box-perm-2314-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-4103 ∷ [])
  (rw 0 (q60 c4) ∷
   rw 0 (q61 c4) ∷ []) Eq.refl

private
  q62 : Ws → Eqn
  q62 c4 = sE 1055 (lem-sym-bc-at0314213042 c4)

-- box-perm-1324 @0314213042: 1 steps
lem-box-perm-1324-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-1324-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-4012 ∷ [])
  (rw 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = sE 1031 (lem-sym-ab-at0314203142 c4)

-- box-perm-3124 @0314213042: 2 steps
lem-box-perm-3124-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ []) ⟫ʷ
lem-box-perm-3124-at0314213042 c4 = derive (Bx3-4102 ∷ []) (Bx3-0412 ∷ [])
  (rw 0 (q62 c4) ∷
   rw 0 (q63 c4) ∷ []) Eq.refl

private
  q64 : Ws → Eqn
  q64 c4 = sE 251 (lem-box-tQ-at0310243142 c4)
  q65 : Ws → Eqn
  q65 c4 = sE 1043 (lem-box-cP-at0213203441 c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 613 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = wlE 758 (lit c4)
  q68 : Ws → Eqn
  q68 c4 = wlE 310 (lit c4)
  q69 : Ws → Eqn
  q69 c4 = wlE 670 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wpE 680 c4
  q71 : Ws → Eqn
  q71 c4 = sE 224 (lem-comm-CSd14-CCZ023 c4)
  q72 : Ws → Eqn
  q72 c4 = sE 219 (lem-comm-CS14-CCZ023 c4)
  q73 : Ws → Eqn
  q73 c4 = wlE 759 (lit c4)
  q74 : Ws → Eqn
  q74 c4 = wpE 665 c4
  q75 : Ws → Eqn
  q75 c4 = wpE 681 c4
  q76 : Ws → Eqn
  q76 c4 = wlE 760 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 761 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = sE 1026 (lem-comm-CX30-TOFF214 c4)
  q79 : Ws → Eqn
  q79 c4 = wpE 682 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 683 c4
  q81 : Ws → Eqn
  q81 c4 = wlE 762 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wpE 669 c4
  q83 : Ws → Eqn
  q83 c4 = wlE 199 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = wpE 684 c4
  q85 : Ws → Eqn
  q85 c4 = wpE 685 c4
  q86 : Ws → Eqn
  q86 c4 = wpE 686 c4
  q87 : Ws → Eqn
  q87 c4 = wlE 763 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = sE 1 (lem-comm-CX04-CCZ123 c4)
  q89 : Ws → Eqn
  q89 c4 = wlE 764 (lit c4)
  q90 : Ws → Eqn
  q90 c4 = wlE 765 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wpE 687 c4

-- box-box-4 @0310243142: 103 steps
lem-box-box-4-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ Bx2-3041 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3041 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-box-box-4-at0310243142 c4 = derive (Bx3-0412 ∷ Bx2-3041 ∷ []) (Bx2-3041 ∷ Bx3-0412 ∷ [])
  (rw 0 (q64 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 3 (q66 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 6 (q66 c4) ∷
   rw 5 (q68 c4) ∷
   rw⁻ 9 (q69 c4) ∷
   rw⁻ 8 (q70 c4) ∷
   rw 7 (q71 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 6 (q73 c4) ∷
   rw⁻ 3 (q65 c4) ∷
   rw 3 (q65 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   rw 4 (q50 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw 9 (q76 c4) ∷
   rw 8 (q77 c4) ∷
   rw 7 (q78 c4) ∷
   rw 6 (q79 c4) ∷
   rw 5 (q78 c4) ∷
   rw 4 (q80 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 6 (q82 c4) ∷
   rw 5 (q32 c4) ∷
   rw⁻ 9 (q83 c4) ∷
   rw⁻ 8 (q84 c4) ∷
   rw 7 (q71 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 5 (q72 c4) ∷
   rw⁻ 6 (q32 c4) ∷
   rw⁻ 4 (q74 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 5 (q75 c4) ∷
   rw 11 (q76 c4) ∷
   rw 10 (q77 c4) ∷
   rw 9 (q78 c4) ∷
   rw 8 (q79 c4) ∷
   rw 7 (q78 c4) ∷
   rw 6 (q80 c4) ∷
   rw 5 (q81 c4) ∷
   rw 6 (q75 c4) ∷
   rw⁻ 2 (q65 c4) ∷
   rw 2 (q65 c4) ∷
   rw⁻ 1 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 4 (q66 c4) ∷
   rw 3 (q68 c4) ∷
   rw⁻ 7 (q69 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 5 (q71 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 4 (q73 c4) ∷
   rw⁻ 1 (q65 c4) ∷
   rw 1 (q65 c4) ∷
   rw⁻ 0 (q74 c4) ∷
   rw 2 (q50 c4) ∷
   rw⁻ 1 (q75 c4) ∷
   rw 7 (q76 c4) ∷
   rw 6 (q77 c4) ∷
   rw 5 (q78 c4) ∷
   rw 4 (q79 c4) ∷
   rw 3 (q78 c4) ∷
   rw 2 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 2 (q75 c4) ∷
   rw⁻ 4 (q82 c4) ∷
   rw 3 (q32 c4) ∷
   rw⁻ 7 (q83 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 5 (q71 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 3 (q72 c4) ∷
   rw⁻ 4 (q32 c4) ∷
   rw⁻ 2 (q74 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw 4 (q86 c4) ∷
   rw⁻ 3 (q75 c4) ∷
   rw 9 (q76 c4) ∷
   rw 8 (q77 c4) ∷
   rw 7 (q78 c4) ∷
   rw 6 (q79 c4) ∷
   rw 5 (q78 c4) ∷
   rw 4 (q80 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q75 c4) ∷
   rw⁻ 0 (q65 c4) ∷
   rw 2 (q32 c4) ∷
   rw⁻ 6 (q87 c4) ∷
   rw 5 (q88 c4) ∷
   rw⁻ 4 (q89 c4) ∷
   rw 3 (q88 c4) ∷
   rw⁻ 2 (q90 c4) ∷
   rw⁻ 3 (q32 c4) ∷
   rw 3 (q91 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 1 (q64 c4) ∷ []) Eq.refl

private
  q92 : Ws → Eqn
  q92 c4 = sE 1035 (lem-P-box-at0210233441 c4)
  q93 : Ws → Eqn
  q93 c4 = sE 1042 (lem-box-cP-at0210233441 c4)
  q94 : Ws → Eqn
  q94 c4 = wlE 636 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = sE 250 (lem-box-tQ-at0214213043 c4)

-- pairs @0210233441: 4 steps
lem-pairs-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4103 ∷ []) ⟫ʷ
lem-pairs-at0210233441 c4 = derive (Bx2-0341 ∷ []) (Bx2-4103 ∷ [])
  (rw⁻ 0 (q92 c4) ∷
   rw 1 (q93 c4) ∷
   rw 4 (q94 c4) ∷
   rw⁻ 0 (q95 c4) ∷ []) Eq.refl

private
  q96 : Ws → Eqn
  q96 c4 = sE 894 (lem-sym-ab-at0310243142 c4)
  q97 : Ws → Eqn
  q97 c4 = sE 1054 (lem-sym-bc-at0314203142 c4)

-- box-perm-2314 @0310243142: 2 steps
lem-box-perm-2314-at0310243142 : Ws → ⟪ (Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ []) ⟫ʷ
lem-box-perm-2314-at0310243142 c4 = derive (Bx3-0412 ∷ []) (Bx3-4102 ∷ [])
  (rw 0 (q96 c4) ∷
   rw 0 (q97 c4) ∷ []) Eq.refl

private
  q98 : Ws → Eqn
  q98 c4 = sE 1046 (lem-box-cP-at0314213042 c4)
  q99 : Ws → Eqn
  q99 c4 = wpE 704 c4
  q100 : Ws → Eqn
  q100 c4 = wlE 789 (lit c4)
  q101 : Ws → Eqn
  q101 c4 = wlE 757 (lit c4)
  q102 : Ws → Eqn
  q102 c4 = wlE 790 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = wpE 705 c4
  q104 : Ws → Eqn
  q104 c4 = sE 432 (lem-comm-CSd02-CCZ134 c4)
  q105 : Ws → Eqn
  q105 c4 = sE 431 (lem-comm-CS02-CCZ134 c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 791 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 792 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 793 (lit c4)

-- CSdu-box-3 @0314213042: 17 steps
lem-CSdu-box-3-at0314213042 : Ws → ⟪ (CS03⁻ ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0314213042 c4 = derive (CS03⁻ ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CS03⁻ ∷ [])
  (rw 1 (q98 c4) ∷
   rw⁻ 0 (q99 c4) ∷
   rw 1 (q100 c4) ∷
   rw 4 (q101 c4) ∷
   rw⁻ 8 (q102 c4) ∷
   rw⁻ 7 (q103 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 5 (q101 c4) ∷
   rw 3 (q104 c4) ∷
   rw⁻ 2 (q99 c4) ∷
   rw 5 (q106 c4) ∷
   rw 4 (q107 c4) ∷
   rw 3 (q100 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 0 (q98 c4) ∷ []) Eq.refl

private
  q109 : Ws → Eqn
  q109 c4 = wpE 706 c4
  q110 : Ws → Eqn
  q110 c4 = wlE 800 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = wlE 801 (lit c4)
  q112 : Ws → Eqn
  q112 c4 = wlE 802 (lit c4)

-- CSu-box-3 @0314213042: 17 steps
lem-CSu-box-3-at0314213042 : Ws → ⟪ (CS03 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4102 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3-at0314213042 c4 = derive (CS03 ∷ Bx3-4102 ∷ []) (Bx3-4102 ∷ CS03 ∷ [])
  (rw 1 (q98 c4) ∷
   rw⁻ 0 (q109 c4) ∷
   rw 1 (q110 c4) ∷
   rw 4 (q101 c4) ∷
   rw⁻ 8 (q102 c4) ∷
   rw⁻ 7 (q103 c4) ∷
   rw 6 (q104 c4) ∷
   rw⁻ 5 (q103 c4) ∷
   rw 4 (q105 c4) ∷
   rw⁻ 5 (q101 c4) ∷
   rw 3 (q105 c4) ∷
   rw⁻ 2 (q109 c4) ∷
   rw 5 (q106 c4) ∷
   rw 4 (q111 c4) ∷
   rw 3 (q110 c4) ∷
   rw 4 (q112 c4) ∷
   rw⁻ 0 (q98 c4) ∷ []) Eq.refl

private
  q113 : Ws → Eqn
  q113 c4 = sE 311 (lem-box-tQ-at0314213042 c4)
  q114 : Ws → Eqn
  q114 c4 = wlE 788 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = sE 1040 (lem-t-cP-at0314213042 c4)
  q116 : Ws → Eqn
  q116 c4 = wlE 204 (lit c4)

-- box2 @0314213042: 11 steps
lem-box2-at0314213042 : Ws → ⟪ (Bx3-4102 ∷ Bx3-4102 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0314213042 c4 = derive (Bx3-4102 ∷ Bx3-4102 ∷ []) []
  (rw 0 (q113 c4) ∷
   rw 4 (q98 c4) ∷
   rw⁻ 4 (q114 c4) ∷
   rw 5 (q115 c4) ∷
   rw⁻ 5 (q98 c4) ∷
   rw 5 (q113 c4) ∷
   rw 4 (q114 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q114 c4) ∷
   rw 1 (q116 c4) ∷
   rw 0 (q114 c4) ∷ []) Eq.refl

private
  q117 : Ws → Eqn
  q117 c4 = sE 1052 (lem-sym-bc-at0214213043 c4)
  q118 : Ws → Eqn
  q118 c4 = sE 1029 (lem-sym-ab-at0214203143 c4)

-- box-perm-3124 @0214213043: 2 steps
lem-box-perm-3124-at0214213043 : Ws → ⟪ (Bx2-4103 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-3124-at0214213043 c4 = derive (Bx2-4103 ∷ []) (Bx2-0413 ∷ [])
  (rw 0 (q117 c4) ∷
   rw 0 (q118 c4) ∷ []) Eq.refl

private
  q119 : Ws → Eqn
  q119 c4 = wpE 717 c4
  q120 : Ws → Eqn
  q120 c4 = wpE 352 c4
  q121 : Ws → Eqn
  q121 c4 = wlE 807 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = wlE 808 (lit c4)
  q123 : Ws → Eqn
  q123 c4 = wlE 809 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = wpE 109 c4
  q125 : Ws → Eqn
  q125 c4 = wpE 718 c4

-- CXu-box-4 @0210243143: 15 steps
lem-CXu-box-4-at0210243143 : Ws → ⟪ (CX32 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CX32 ∷ []) ⟫ʷ
lem-CXu-box-4-at0210243143 c4 = derive (CX32 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CX32 ∷ [])
  (rw 1 (q9 c4) ∷
   rw⁻ 0 (q119 c4) ∷
   rw 2 (q120 c4) ∷
   rw 6 (q39 c4) ∷
   rw 5 (q34 c4) ∷
   rw 4 (q121 c4) ∷
   rw 3 (q34 c4) ∷
   rw 2 (q122 c4) ∷
   rw⁻ 3 (q120 c4) ∷
   rw 1 (q123 c4) ∷
   rw⁻ 3 (q124 c4) ∷
   rw⁻ 2 (q119 c4) ∷
   rw 3 (q125 c4) ∷
   rw 3 (q123 c4) ∷
   rw⁻ 0 (q9 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q127 : Ws → Eqn
  q127 c4 = wpE 215 c4
  q128 : Ws → Eqn
  q128 c4 = wlE 818 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wlE 458 (lit c4)
  q130 : Ws → Eqn
  q130 c4 = wpE 157 c4
  q131 : Ws → Eqn
  q131 c4 = wpE 308 c4
  q132 : Ws → Eqn
  q132 c4 = sE 704 (lem-comm-CSd23-CCZ014 c4)
  q133 : Ws → Eqn
  q133 c4 = sE 703 (lem-comm-CS23-CCZ014 c4)
  q134 : Ws → Eqn
  q134 c4 = wlE 819 (lit c4)
  q135 : Ws → Eqn
  q135 c4 = wlE 820 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wlE 821 (lit c4)

-- CSdu-box-3 @243243: 17 steps
lem-CSdu-box-3-at243243 : Ws → ⟪ (CS02⁻ ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at243243 c4 = derive (CS02⁻ ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS02⁻ ∷ [])
  (rw 1 (q126 c4) ∷
   rw⁻ 0 (q127 c4) ∷
   rw 1 (q128 c4) ∷
   rw 4 (q129 c4) ∷
   rw⁻ 8 (q130 c4) ∷
   rw⁻ 7 (q131 c4) ∷
   rw 6 (q132 c4) ∷
   rw⁻ 5 (q131 c4) ∷
   rw 4 (q133 c4) ∷
   rw⁻ 5 (q129 c4) ∷
   rw 3 (q132 c4) ∷
   rw⁻ 2 (q127 c4) ∷
   rw 5 (q134 c4) ∷
   rw 4 (q135 c4) ∷
   rw 3 (q128 c4) ∷
   rw 4 (q136 c4) ∷
   rw⁻ 0 (q126 c4) ∷ []) Eq.refl

private
  q137 : Ws → Eqn
  q137 c4 = wpE 155 c4
  q138 : Ws → Eqn
  q138 c4 = wlE 822 (lit c4)
  q139 : Ws → Eqn
  q139 c4 = wlE 823 (lit c4)
  q140 : Ws → Eqn
  q140 c4 = wlE 824 (lit c4)

-- CSu-box-3 @243243: 17 steps
lem-CSu-box-3-at243243 : Ws → ⟪ (CS02 ∷ Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ CS02 ∷ []) ⟫ʷ
lem-CSu-box-3-at243243 c4 = derive (CS02 ∷ Bx0-1423 ∷ []) (Bx0-1423 ∷ CS02 ∷ [])
  (rw 1 (q126 c4) ∷
   rw⁻ 0 (q137 c4) ∷
   rw 1 (q138 c4) ∷
   rw 4 (q129 c4) ∷
   rw⁻ 8 (q130 c4) ∷
   rw⁻ 7 (q131 c4) ∷
   rw 6 (q132 c4) ∷
   rw⁻ 5 (q131 c4) ∷
   rw 4 (q133 c4) ∷
   rw⁻ 5 (q129 c4) ∷
   rw 3 (q133 c4) ∷
   rw⁻ 2 (q137 c4) ∷
   rw 5 (q134 c4) ∷
   rw 4 (q139 c4) ∷
   rw 3 (q138 c4) ∷
   rw 4 (q140 c4) ∷
   rw⁻ 0 (q126 c4) ∷ []) Eq.refl

private
  q141 : Ws → Eqn
  q141 c4 = sE 1039 (lem-P-box-at243243 c4)
  q142 : Ws → Eqn
  q142 c4 = wlE 203 (lit c4)
  q143 : Ws → Eqn
  q143 c4 = sE 255 (lem-box-tQ-at122331 c4)

-- pairs @243243: 4 steps
lem-pairs-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-pairs-at243243 c4 = derive (Bx0-1423 ∷ []) (Bx0-2314 ∷ [])
  (rw⁻ 0 (q141 c4) ∷
   rw 1 (q126 c4) ∷
   rw 4 (q142 c4) ∷
   rw⁻ 0 (q143 c4) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = sE 40 (lem-sym-ab-at03102132 c4)
  q145 : Ws → Eqn
  q145 c4 = sE 1049 (lem-pairs-at032032 c4)
  q146 : Ws → Eqn
  q146 c4 = sE 1053 (lem-sym-bc-at0312243140 c4)
  q147 : Ws → Eqn
  q147 c4 = sE 1030 (lem-sym-ab-at0312213440 c4)

-- box-perm-2341 @03102132: 4 steps
lem-box-perm-2341-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1240 ∷ []) ⟫ʷ
lem-box-perm-2341-at03102132 c4 = derive (Bx3-0124 ∷ []) (Bx3-1240 ∷ [])
  (rw 0 (q144 c4) ∷
   rw 0 (q145 c4) ∷
   rw 0 (q146 c4) ∷
   rw 0 (q147 c4) ∷ []) Eq.refl

private
  q148 : Ws → Eqn
  q148 c4 = sE 1038 (lem-P-box-at0312243140 c4)
  q149 : Ws → Eqn
  q149 c4 = sE 1045 (lem-box-cP-at0312243140 c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 443 (lit c4)
  q151 : Ws → Eqn
  q151 c4 = sE 83 (lem-box-tQ-at032032 c4)

-- pairs @0312243140: 4 steps
lem-pairs-at0312243140 : Ws → ⟪ (Bx3-2410 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-pairs-at0312243140 c4 = derive (Bx3-2410 ∷ []) (Bx3-1024 ∷ [])
  (rw⁻ 0 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw 4 (q150 c4) ∷
   rw⁻ 0 (q151 c4) ∷ []) Eq.refl

private
  q152 : Ws → Eqn
  q152 c4 = sE 996 (lem-box-cP-at0310243142 c4)
  q153 : Ws → Eqn
  q153 c4 = wpE 104 c4
  q154 : Ws → Eqn
  q154 c4 = wpE 13 c4
  q155 : Ws → Eqn
  q155 c4 = wlE 861 (lit c4)
  q156 : Ws → Eqn
  q156 c4 = sE 1025 (lem-comm-CX04-TOFF312 c4)
  q157 : Ws → Eqn
  q157 c4 = wlE 878 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = wlE 879 (lit c4)
  q159 : Ws → Eqn
  q159 c4 = wlE 880 (lit c4)
  q160 : Ws → Eqn
  q160 c4 = wpE 110 c4

-- CXu-box-4 @0310243142: 15 steps
lem-CXu-box-4-at0310243142 : Ws → ⟪ (CX23 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CX23 ∷ []) ⟫ʷ
lem-CXu-box-4-at0310243142 c4 = derive (CX23 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CX23 ∷ [])
  (rw 1 (q152 c4) ∷
   rw⁻ 0 (q153 c4) ∷
   rw 2 (q154 c4) ∷
   rw 6 (q155 c4) ∷
   rw 5 (q156 c4) ∷
   rw 4 (q157 c4) ∷
   rw 3 (q156 c4) ∷
   rw 2 (q158 c4) ∷
   rw⁻ 3 (q154 c4) ∷
   rw 1 (q159 c4) ∷
   rw 3 (q124 c4) ∷
   rw⁻ 2 (q153 c4) ∷
   rw 3 (q160 c4) ∷
   rw 3 (q159 c4) ∷
   rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q161 : Ws → Eqn
  q161 c4 = wpE 312 c4
  q162 : Ws → Eqn
  q162 c4 = wlE 881 (lit c4)
  q163 : Ws → Eqn
  q163 c4 = wlE 297 (lit c4)
  q164 : Ws → Eqn
  q164 c4 = wpE 314 c4
  q165 : Ws → Eqn
  q165 c4 = wpE 127 c4
  q166 : Ws → Eqn
  q166 c4 = sE 199 (lem-comm-CSd12-CCZ034 c4)
  q167 : Ws → Eqn
  q167 c4 = sE 191 (lem-comm-CS12-CCZ034 c4)
  q168 : Ws → Eqn
  q168 c4 = wlE 882 (lit c4)
  q169 : Ws → Eqn
  q169 c4 = wlE 883 (lit c4)
  q170 : Ws → Eqn
  q170 c4 = wlE 884 (lit c4)

-- CSu-box-3 @0310243142: 17 steps
lem-CSu-box-3-at0310243142 : Ws → ⟪ (CS13 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at0310243142 c4 = derive (CS13 ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CS13 ∷ [])
  (rw 1 (q152 c4) ∷
   rw⁻ 0 (q161 c4) ∷
   rw 1 (q162 c4) ∷
   rw 4 (q163 c4) ∷
   rw⁻ 8 (q164 c4) ∷
   rw⁻ 7 (q165 c4) ∷
   rw 6 (q166 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 5 (q163 c4) ∷
   rw 3 (q167 c4) ∷
   rw⁻ 2 (q161 c4) ∷
   rw 5 (q168 c4) ∷
   rw 4 (q169 c4) ∷
   rw 3 (q162 c4) ∷
   rw 4 (q170 c4) ∷
   rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = wpE 734 c4
  q172 : Ws → Eqn
  q172 c4 = wlE 885 (lit c4)
  q173 : Ws → Eqn
  q173 c4 = wlE 886 (lit c4)
  q174 : Ws → Eqn
  q174 c4 = wlE 887 (lit c4)

-- CSdu-box-3 @0310243142: 17 steps
lem-CSdu-box-3-at0310243142 : Ws → ⟪ (CS13⁻ ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0310243142 c4 = derive (CS13⁻ ∷ Bx3-0412 ∷ []) (Bx3-0412 ∷ CS13⁻ ∷ [])
  (rw 1 (q152 c4) ∷
   rw⁻ 0 (q171 c4) ∷
   rw 1 (q172 c4) ∷
   rw 4 (q163 c4) ∷
   rw⁻ 8 (q164 c4) ∷
   rw⁻ 7 (q165 c4) ∷
   rw 6 (q166 c4) ∷
   rw⁻ 5 (q165 c4) ∷
   rw 4 (q167 c4) ∷
   rw⁻ 5 (q163 c4) ∷
   rw 3 (q166 c4) ∷
   rw⁻ 2 (q171 c4) ∷
   rw 5 (q168 c4) ∷
   rw 4 (q173 c4) ∷
   rw 3 (q172 c4) ∷
   rw 4 (q174 c4) ∷
   rw⁻ 0 (q152 c4) ∷ []) Eq.refl

private
  q175 : Ws → Eqn
  q175 c4 = wlE 904 (lit c4)
  q176 : Ws → Eqn
  q176 c4 = wlE 905 (lit c4)
  q177 : Ws → Eqn
  q177 c4 = wpE 39 c4
  q178 : Ws → Eqn
  q178 c4 = wpE 756 c4
  q179 : Ws → Eqn
  q179 c4 = wlE 906 (lit c4)
  q180 : Ws → Eqn
  q180 c4 = wlE 907 (lit c4)
  q181 : Ws → Eqn
  q181 c4 = wlE 908 (lit c4)

-- CSdu-box-3 @122441: 17 steps
lem-CSdu-box-3-at122441 : Ws → ⟪ (CS03⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at122441 c4 = derive (CS03⁻ ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS03⁻ ∷ [])
  (rw 1 (q3 c4) ∷
   rw⁻ 0 (q21 c4) ∷
   rw 1 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 8 (q177 c4) ∷
   rw⁻ 7 (q178 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q176 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw 5 (q179 c4) ∷
   rw 4 (q180 c4) ∷
   rw 3 (q175 c4) ∷
   rw 4 (q181 c4) ∷
   rw⁻ 0 (q3 c4) ∷ []) Eq.refl

private
  q182 : Ws → Eqn
  q182 c4 = wlE 909 (lit c4)
  q183 : Ws → Eqn
  q183 c4 = wlE 910 (lit c4)
  q184 : Ws → Eqn
  q184 c4 = wlE 911 (lit c4)

-- CSu-box-3 @122441: 17 steps
lem-CSu-box-3-at122441 : Ws → ⟪ (CS03 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3-at122441 c4 = derive (CS03 ∷ Bx0-2431 ∷ []) (Bx0-2431 ∷ CS03 ∷ [])
  (rw 1 (q3 c4) ∷
   rw⁻ 0 (q14 c4) ∷
   rw 1 (q182 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 8 (q177 c4) ∷
   rw⁻ 7 (q178 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q178 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q176 c4) ∷
   rw 3 (q17 c4) ∷
   rw⁻ 2 (q14 c4) ∷
   rw 5 (q179 c4) ∷
   rw 4 (q183 c4) ∷
   rw 3 (q182 c4) ∷
   rw 4 (q184 c4) ∷
   rw⁻ 0 (q3 c4) ∷ []) Eq.refl

private
  q185 : Ws → Eqn
  q185 c4 = sE 1036 (lem-P-box-at0210243143 c4)
  q186 : Ws → Eqn
  q186 c4 = wlE 180 (lit c4)
  q187 : Ws → Eqn
  q187 c4 = sE 307 (lem-box-tQ-at022330 c4)

-- pairs @0210243143: 4 steps
lem-pairs-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-pairs-at0210243143 c4 = derive (Bx2-0413 ∷ []) (Bx2-1304 ∷ [])
  (rw⁻ 0 (q185 c4) ∷
   rw 1 (q9 c4) ∷
   rw 4 (q186 c4) ∷
   rw⁻ 0 (q187 c4) ∷ []) Eq.refl

private
  q188 : Ws → Eqn
  q188 c4 = sE 972 (lem-sym-ab-at122441 c4)
  q189 : Ws → Eqn
  q189 c4 = sE 1021 (lem-sym-bc-at1441 c4)
  q190 : Ws → Eqn
  q190 c4 = sE 1034 (lem-sym-ab-at14233241 c4)
  q191 : Ws → Eqn
  q191 c4 = sE 1011 (lem-pairs-at13243241 c4)

-- box-perm-1432 @122441: 4 steps
lem-box-perm-1432-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-box-perm-1432-at122441 c4 = derive (Bx0-2431 ∷ []) (Bx0-2134 ∷ [])
  (rw 0 (q188 c4) ∷
   rw 0 (q189 c4) ∷
   rw 0 (q190 c4) ∷
   rw 0 (q191 c4) ∷ []) Eq.refl

private
  q192 : Ws → Eqn
  q192 c4 = sE 59 (lem-sym-ab-at021021 c4)
  q193 : Ws → Eqn
  q193 c4 = sE 1048 (lem-pairs-at0220 c4)
  q194 : Ws → Eqn
  q194 c4 = sE 1041 (lem-sym-bc-at0213243140 c4)
  q195 : Ws → Eqn
  q195 c4 = sE 1032 (lem-sym-ab-at0213213440 c4)

-- box-perm-2341 @021021: 4 steps
lem-box-perm-2341-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-2341-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-1340 ∷ [])
  (rw 0 (q192 c4) ∷
   rw 0 (q193 c4) ∷
   rw 0 (q194 c4) ∷
   rw 0 (q195 c4) ∷ []) Eq.refl

private
  q196 : Ws → Eqn
  q196 c4 = sE 1033 (lem-sym-ab-at02233440 c4)
  q197 : Ws → Eqn
  q197 c4 = sE 1050 (lem-sym-bc-at0213213440 c4)
  q198 : Ws → Eqn
  q198 c4 = sE 1047 (lem-pairs-at0213243140 c4)
  q199 : Ws → Eqn
  q199 c4 = sE 60 (lem-sym-ab-at0220 c4)

-- box-perm-4123 @02233440: 4 steps
lem-box-perm-4123-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-4123-at02233440 c4 = derive (Bx2-1340 ∷ []) (Bx2-0134 ∷ [])
  (rw 0 (q196 c4) ∷
   rw 0 (q197 c4) ∷
   rw 0 (q198 c4) ∷
   rw 0 (q199 c4) ∷ []) Eq.refl

private
  q200 : Ws → Eqn
  q200 c4 = sE 1037 (lem-P-box-at022330 c4)
  q201 : Ws → Eqn
  q201 c4 = sE 1044 (lem-box-cP-at022330 c4)
  q202 : Ws → Eqn
  q202 c4 = wpE 19 c4
  q203 : Ws → Eqn
  q203 c4 = sE 248 (lem-box-tQ-at0210243143 c4)

-- pairs @022330: 4 steps
lem-pairs-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-pairs-at022330 c4 = derive (Bx2-1304 ∷ []) (Bx2-0413 ∷ [])
  (rw⁻ 0 (q200 c4) ∷
   rw 1 (q201 c4) ∷
   rw 4 (q202 c4) ∷
   rw⁻ 0 (q203 c4) ∷ []) Eq.refl

private
  q204 : Ws → Eqn
  q204 c4 = wpE 81 c4
  q205 : Ws → Eqn
  q205 c4 = wlE 964 (lit c4)
  q206 : Ws → Eqn
  q206 c4 = wlE 326 (lit c4)
  q207 : Ws → Eqn
  q207 c4 = wpE 92 c4
  q208 : Ws → Eqn
  q208 c4 = wpE 749 c4
  q209 : Ws → Eqn
  q209 c4 = wlE 965 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = wlE 966 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = wlE 967 (lit c4)

-- CSu-box-3 @0210243143: 17 steps
lem-CSu-box-3-at0210243143 : Ws → ⟪ (CS12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12 ∷ []) ⟫ʷ
lem-CSu-box-3-at0210243143 c4 = derive (CS12 ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12 ∷ [])
  (rw 1 (q9 c4) ∷
   rw⁻ 0 (q204 c4) ∷
   rw 1 (q205 c4) ∷
   rw 4 (q206 c4) ∷
   rw⁻ 8 (q207 c4) ∷
   rw⁻ 7 (q208 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q208 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q206 c4) ∷
   rw 3 (q17 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw 5 (q209 c4) ∷
   rw 4 (q210 c4) ∷
   rw 3 (q205 c4) ∷
   rw 4 (q211 c4) ∷
   rw⁻ 0 (q9 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = wpE 87 c4
  q213 : Ws → Eqn
  q213 c4 = wlE 968 (lit c4)
  q214 : Ws → Eqn
  q214 c4 = wlE 969 (lit c4)
  q215 : Ws → Eqn
  q215 c4 = wlE 970 (lit c4)

-- CSdu-box-3 @0210243143: 17 steps
lem-CSdu-box-3-at0210243143 : Ws → ⟪ (CS12⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0210243143 c4 = derive (CS12⁻ ∷ Bx2-0413 ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ [])
  (rw 1 (q9 c4) ∷
   rw⁻ 0 (q212 c4) ∷
   rw 1 (q213 c4) ∷
   rw 4 (q206 c4) ∷
   rw⁻ 8 (q207 c4) ∷
   rw⁻ 7 (q208 c4) ∷
   rw 6 (q16 c4) ∷
   rw⁻ 5 (q208 c4) ∷
   rw 4 (q17 c4) ∷
   rw⁻ 5 (q206 c4) ∷
   rw 3 (q16 c4) ∷
   rw⁻ 2 (q212 c4) ∷
   rw 5 (q209 c4) ∷
   rw 4 (q214 c4) ∷
   rw 3 (q213 c4) ∷
   rw 4 (q215 c4) ∷
   rw⁻ 0 (q9 c4) ∷ []) Eq.refl
