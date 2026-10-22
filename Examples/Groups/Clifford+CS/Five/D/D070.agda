{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD070 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D070 (Sᴰ : SD070) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-CX40-CCZ123 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CX21-TOFF304 ; lem-comm-CX24-TOFF301)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-tQ-at02142041 : Ws → St 226
  lem-box-tQ-at02142041 = pickᴰ 0 Sᴰ
  lem-box-tQ-at0314203241 : Ws → St 266
  lem-box-tQ-at0314203241 = pickᴰ 1 Sᴰ
  lem-box-cP-at03143041 : Ws → St 958
  lem-box-cP-at03143041 = pickᴰ 2 Sᴰ
  lem-box-cP-at122441 : Ws → St 850
  lem-box-cP-at122441 = pickᴰ 3 Sᴰ
  lem-box-perm-2314-at0213243041 : Ws → St 1340
  lem-box-perm-2314-at0213243041 = pickᴰ 4 Sᴰ
  lem-box-perm-1423-at122441 : Ws → St 1080
  lem-box-perm-1423-at122441 = pickᴰ 5 Sᴰ
  lem-box2-at122441 : Ws → St 1082
  lem-box2-at122441 = pickᴰ 6 Sᴰ
  lem-box-perm-1324-at0314203241 : Ws → St 1514
  lem-box-perm-1324-at0314203241 = pickᴰ 7 Sᴰ
  lem-box-perm-2314-at0312243041 : Ws → St 1342
  lem-box-perm-2314-at0312243041 = pickᴰ 8 Sᴰ
  lem-box-perm-3124-at02142041 : Ws → St 1343
  lem-box-perm-3124-at02142041 = pickᴰ 9 Sᴰ
  lem-box-perm-3124-at0314203241 : Ws → St 1344
  lem-box-perm-3124-at0314203241 = pickᴰ 10 Sᴰ
  lem-CKc-box-at12213443 : Ws → St 1322
  lem-CKc-box-at12213443 = pickᴰ 11 Sᴰ
  lem-CKc-box-at13213442 : Ws → St 1324
  lem-CKc-box-at13213442 = pickᴰ 12 Sᴰ
  lem-box-perm-1342-at12213443 : Ws → St 1327
  lem-box-perm-1342-at12213443 = pickᴰ 13 Sᴰ
  lem-box-perm-3421-at122441 : Ws → St 1330
  lem-box-perm-3421-at122441 = pickᴰ 14 Sᴰ
  lem-box-perm-4312-at13213442 : Ws → St 1335
  lem-box-perm-4312-at13213442 = pickᴰ 15 Sᴰ
  lem-nf-CS-K0at2 : Ws → St 1515
  lem-nf-CS-K0at2 = pickᴰ 16 Sᴰ
  lem-nf-CS-K1at2 : Ws → St 1516
  lem-nf-CS-K1at2 = pickᴰ 17 Sᴰ
  lem-box-box-1-at0312243041 : Ws → St 1517
  lem-box-box-1-at0312243041 = pickᴰ 18 Sᴰ

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
  q23 c4 = eqn (Bx0-2431 ∷ []) (Bx0-3142 ∷ []) (lem-box-perm-3421-at122441 c4)
  q24 : Ws → Eqn
  q24 c4 = eqn (Bx0-3142 ∷ CK42 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) (lem-CKc-box-at13213442 c4)
  q25 : Ws → Eqn
  q25 c4 = eqn (Bx0-3142 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-4312-at13213442 c4)
  q26 : Ws → Eqn
  q26 c4 = eqn (Toff013 ∷ CS24 ∷ []) (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4))
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ024 ∷ CS24 ∷ []) (CS24 ∷ CCZ024 ∷ []) (wp 909 c4)
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ []) (wl 234 (lit c4))
  q29 : Ws → Eqn
  q29 c4 = eqn (CCZ123 ∷ []) (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl 242 (lit c4))
  q30 : Ws → Eqn
  q30 c4 = eqn (CCZ024 ∷ CS23 ∷ []) (CS23 ∷ CCZ024 ∷ []) (wp 92 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (CCZ024 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ024 ∷ []) (wp 91 c4)
  q32 : Ws → Eqn
  q32 c4 = eqn (Bx0-2431 ∷ Bx0-2431 ∷ []) [] (lem-box2-at122441 c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl 1037 (lit c4))
  q34 : Ws → Eqn
  q34 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ123 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl 1297 (lit c4))
  q36 : Ws → Eqn
  q36 c4 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wl 181 (lit c4))
  q37 : Ws → Eqn
  q37 c4 = eqn (CS24 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ []) (wl 1298 (lit c4))
  q38 : Ws → Eqn
  q38 c4 = eqn (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CS24 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lem-nf-CS-K0at2 c4)

-- F1-CS-K0@2: 343 steps
lem-F1-CS-K0at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-CS-K0at2 c4 = derive (Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ []) (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ [])
  (re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   re 6 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 8 1 (CS12 ∷ []) ∷
   re 10 1 (CS12⁻ ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw 9 (q2 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q8 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 10 (q4 c4) ∷
   rw 7 (q11 c4) ∷
   rw 9 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 11 (q14 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 12 (q2 c4) ∷
   rw 11 (q3 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw 13 (q5 c4) ∷
   rw 14 (q6 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q8 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 13 (q4 c4) ∷
   rw 10 (q11 c4) ∷
   rw 12 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 12 (q14 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw 14 (q14 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q18 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q8 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 10 (q4 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw 13 (q22 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw 11 (q22 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 12 (q23 c4) ∷
   rw 12 (q24 c4) ∷
   rw 15 (q25 c4) ∷
   rw 15 (q1 c4) ∷
   rw 18 (q26 c4) ∷
   rw 17 (q27 c4) ∷
   rw 16 (q26 c4) ∷
   rw 15 (q27 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 0 (q1 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 1 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw 7 (q4 c4) ∷
   rw 4 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q23 c4) ∷
   rw 6 (q24 c4) ∷
   rw 9 (q25 c4) ∷
   rw 9 (q1 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw 11 (q18 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw 9 (q18 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 13 (q2 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw 14 (q5 c4) ∷
   rw 15 (q6 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q8 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 14 (q4 c4) ∷
   rw 11 (q11 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw 13 (q2 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q6 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q8 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 11 (q4 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 15 (q18 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 13 (q18 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 17 (q2 c4) ∷
   rw 16 (q3 c4) ∷
   rw⁻ 19 (q4 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q6 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q8 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 18 (q4 c4) ∷
   rw 15 (q11 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 17 (q2 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw 14 (q18 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 15 (q4 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 17 (q21 c4) ∷
   rw 16 (q22 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw⁻ 20 (q28 c4) ∷
   rw 20 (q29 c4) ∷
   rw 19 (q30 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q31 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q20 c4) ∷
   rw⁻ 19 (q29 c4) ∷
   rw⁻ 18 (q28 c4) ∷
   rw 18 (q29 c4) ∷
   rw 17 (q30 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q31 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q20 c4) ∷
   rw⁻ 17 (q29 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw 18 (q23 c4) ∷
   rw 18 (q24 c4) ∷
   rw 21 (q25 c4) ∷
   rw 21 (q1 c4) ∷
   rw⁻ 24 (q28 c4) ∷
   rw 24 (q29 c4) ∷
   rw 23 (q30 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q31 c4) ∷
   rw 26 (q7 c4) ∷
   rw 27 (q20 c4) ∷
   rw⁻ 23 (q29 c4) ∷
   rw⁻ 22 (q28 c4) ∷
   rw 22 (q29 c4) ∷
   rw 21 (q30 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q31 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q20 c4) ∷
   rw⁻ 21 (q29 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw 25 (q26 c4) ∷
   rw 24 (q27 c4) ∷
   rw 23 (q26 c4) ∷
   rw 22 (q27 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw 23 (q32 c4) ∷
   rw 0 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 14 (q36 c4) ∷
   rw 6 (q34 c4) ∷
   rw 8 (q34 c4) ∷
   rw 12 (q36 c4) ∷
   rw⁻ 0 (q37 c4) ∷
   rw⁻ 0 (q38 c4) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4)
  q40 : Ws → Eqn
  q40 c4 = eqn (Bx0-2143 ∷ CK43 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) (lem-CKc-box-at12213443 c4)
  q41 : Ws → Eqn
  q41 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-1342-at12213443 c4)
  q42 : Ws → Eqn
  q42 c4 = eqn (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CS34 ∷ []) (wl 1299 (lit c4))
  q43 : Ws → Eqn
  q43 c4 = eqn (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (lem-nf-CS-K1at2 c4)

-- F1-CS-K1@2: 343 steps
lem-F1-CS-K1at2 : Ws → ⟪ (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-F1-CS-K1at2 c4 = derive (Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ CS34 ∷ []) (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ [])
  (re 0 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 2 1 (CS12 ∷ []) ∷
   re 4 1 (CS12⁻ ∷ []) ∷
   re 6 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 8 1 (CS12 ∷ []) ∷
   re 10 1 (CS12⁻ ∷ []) ∷
   rw 6 (q1 c4) ∷
   rw 9 (q2 c4) ∷
   rw 8 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q8 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 10 (q4 c4) ∷
   rw 7 (q11 c4) ∷
   rw 9 (q12 c4) ∷
   rw⁻ 8 (q13 c4) ∷
   rw 9 (q14 c4) ∷
   rw⁻ 10 (q15 c4) ∷
   rw 11 (q14 c4) ∷
   rw⁻ 12 (q16 c4) ∷
   rw⁻ 8 (q12 c4) ∷
   rw 9 (q2 c4) ∷
   rw⁻ 7 (q17 c4) ∷
   rw 6 (q18 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw 7 (q4 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 8 (q1 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw 8 (q20 c4) ∷
   rw⁻ 9 (q1 c4) ∷
   rw 9 (q1 c4) ∷
   rw 12 (q2 c4) ∷
   rw 11 (q3 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw 13 (q5 c4) ∷
   rw 14 (q6 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q8 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 13 (q4 c4) ∷
   rw 10 (q11 c4) ∷
   rw 12 (q12 c4) ∷
   rw⁻ 11 (q13 c4) ∷
   rw 12 (q14 c4) ∷
   rw⁻ 13 (q15 c4) ∷
   rw 14 (q14 c4) ∷
   rw⁻ 15 (q16 c4) ∷
   rw⁻ 11 (q12 c4) ∷
   rw 12 (q2 c4) ∷
   rw⁻ 10 (q17 c4) ∷
   rw 9 (q18 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw 10 (q5 c4) ∷
   rw 11 (q6 c4) ∷
   rw 12 (q7 c4) ∷
   rw 13 (q8 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q9 c4) ∷
   rw 16 (q10 c4) ∷
   rw 10 (q4 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw 13 (q22 c4) ∷
   rw⁻ 12 (q21 c4) ∷
   rw 11 (q22 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 12 (q39 c4) ∷
   rw 12 (q40 c4) ∷
   rw 15 (q41 c4) ∷
   rw 15 (q1 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 17 (q6 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 15 (q6 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 0 (q1 c4) ∷
   rw 3 (q2 c4) ∷
   rw 2 (q3 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw 1 (q11 c4) ∷
   rw 3 (q12 c4) ∷
   rw⁻ 2 (q13 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q16 c4) ∷
   rw⁻ 2 (q12 c4) ∷
   rw 3 (q2 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw⁻ 2 (q4 c4) ∷
   rw 1 (q5 c4) ∷
   rw 2 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw 4 (q8 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q9 c4) ∷
   rw 7 (q10 c4) ∷
   rw 1 (q4 c4) ∷
   rw⁻ 2 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw 2 (q20 c4) ∷
   rw⁻ 3 (q1 c4) ∷
   rw 3 (q1 c4) ∷
   rw 6 (q2 c4) ∷
   rw 5 (q3 c4) ∷
   rw⁻ 8 (q4 c4) ∷
   rw 7 (q5 c4) ∷
   rw 8 (q6 c4) ∷
   rw 9 (q7 c4) ∷
   rw 10 (q8 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q9 c4) ∷
   rw 13 (q10 c4) ∷
   rw 7 (q4 c4) ∷
   rw 4 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw⁻ 5 (q13 c4) ∷
   rw 6 (q14 c4) ∷
   rw⁻ 7 (q15 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 9 (q16 c4) ∷
   rw⁻ 5 (q12 c4) ∷
   rw 6 (q2 c4) ∷
   rw⁻ 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw⁻ 5 (q4 c4) ∷
   rw 4 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 6 (q7 c4) ∷
   rw 7 (q8 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 4 (q4 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 6 (q21 c4) ∷
   rw 5 (q22 c4) ∷
   rw⁻ 6 (q1 c4) ∷
   rw 6 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw 9 (q1 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw 11 (q18 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw 9 (q18 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw 13 (q2 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw 14 (q5 c4) ∷
   rw 15 (q6 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q8 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q9 c4) ∷
   rw 20 (q10 c4) ∷
   rw 14 (q4 c4) ∷
   rw 11 (q11 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw 13 (q2 c4) ∷
   rw⁻ 11 (q17 c4) ∷
   rw 10 (q18 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw 11 (q5 c4) ∷
   rw 12 (q6 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q8 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q9 c4) ∷
   rw 17 (q10 c4) ∷
   rw 11 (q4 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 15 (q18 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 13 (q18 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw 17 (q2 c4) ∷
   rw 16 (q3 c4) ∷
   rw⁻ 19 (q4 c4) ∷
   rw 18 (q5 c4) ∷
   rw 19 (q6 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q8 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q9 c4) ∷
   rw 24 (q10 c4) ∷
   rw 18 (q4 c4) ∷
   rw 15 (q11 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 17 (q2 c4) ∷
   rw⁻ 15 (q17 c4) ∷
   rw 14 (q18 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 15 (q4 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 17 (q21 c4) ∷
   rw 16 (q22 c4) ∷
   rw⁻ 17 (q1 c4) ∷
   rw 17 (q1 c4) ∷
   rw⁻ 20 (q28 c4) ∷
   rw 20 (q29 c4) ∷
   rw 19 (q30 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q31 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q20 c4) ∷
   rw⁻ 19 (q29 c4) ∷
   rw⁻ 18 (q28 c4) ∷
   rw 18 (q29 c4) ∷
   rw 17 (q30 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q31 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q20 c4) ∷
   rw⁻ 17 (q29 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw 18 (q39 c4) ∷
   rw 18 (q40 c4) ∷
   rw 21 (q41 c4) ∷
   rw 21 (q1 c4) ∷
   rw⁻ 24 (q28 c4) ∷
   rw 24 (q29 c4) ∷
   rw 23 (q30 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q31 c4) ∷
   rw 26 (q7 c4) ∷
   rw 27 (q20 c4) ∷
   rw⁻ 23 (q29 c4) ∷
   rw⁻ 22 (q28 c4) ∷
   rw 22 (q29 c4) ∷
   rw 21 (q30 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q31 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q20 c4) ∷
   rw⁻ 21 (q29 c4) ∷
   rw⁻ 22 (q1 c4) ∷
   rw 22 (q1 c4) ∷
   rw⁻ 25 (q13 c4) ∷
   rw 24 (q6 c4) ∷
   rw⁻ 23 (q13 c4) ∷
   rw 22 (q6 c4) ∷
   rw⁻ 23 (q1 c4) ∷
   rw 23 (q32 c4) ∷
   rw 0 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 6 (q35 c4) ∷
   rw 14 (q36 c4) ∷
   rw 6 (q34 c4) ∷
   rw 8 (q34 c4) ∷
   rw 12 (q36 c4) ∷
   rw⁻ 0 (q42 c4) ∷
   rw⁻ 0 (q43 c4) ∷ []) Eq.refl

private
  q44 : Ws → Eqn
  q44 c4 = eqn (Bx2-4031 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02142041 c4)
  q45 : Ws → Eqn
  q45 c4 = eqn (Toff204 ∷ Toff304 ∷ Toff324 ∷ []) (Toff324 ∷ Toff204 ∷ []) (wp 1200 c4)
  q46 : Ws → Eqn
  q46 c4 = eqn (CCZ123 ∷ CCZ124 ∷ Toff324 ∷ []) (Toff324 ∷ CCZ123 ∷ []) (wl 215 (lit c4))
  q47 : Ws → Eqn
  q47 c4 = eqn (CCZ123 ∷ CCZ124 ∷ []) (Toff324 ∷ CCZ123 ∷ Toff324 ∷ []) (wl 1355 (lit c4))
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ124 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp 946 c4)
  q49 : Ws → Eqn
  q49 c4 = eqn (CCZ014 ∷ Toff304 ∷ []) (Toff304 ∷ CCZ014 ∷ []) (wp 687 c4)
  q50 : Ws → Eqn
  q50 c4 = eqn (CCZ124 ∷ []) (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl 271 (lit c4))
  q51 : Ws → Eqn
  q51 c4 = eqn (CS24 ∷ Toff304 ∷ []) (Toff304 ∷ CS24 ∷ []) (wp 691 c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (CX21 ∷ Toff304 ∷ []) (Toff304 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF304 (lit c4))
  q53 : Ws → Eqn
  q53 c4 = eqn (CS14⁻ ∷ Toff304 ∷ []) (Toff304 ∷ CS14⁻ ∷ []) (wp 1201 c4)
  q54 : Ws → Eqn
  q54 c4 = eqn (CS14 ∷ Toff304 ∷ []) (Toff304 ∷ CS14 ∷ []) (wp 1037 c4)
  q55 : Ws → Eqn
  q55 c4 = eqn (CCZ014 ∷ CCZ124 ∷ []) (CCZ124 ∷ CCZ014 ∷ []) (wp 66 c4)
  q56 : Ws → Eqn
  q56 c4 = eqn (CCZ123 ∷ []) (CCZ124 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl 462 (lit c4))
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ014 ∷ []) (CS01 ∷ CX40 ∷ CS01⁻ ∷ CX40 ∷ CS14 ∷ []) (wp 1143 c4)
  q58 : Ws → Eqn
  q58 c4 = eqn (CCZ123 ∷ CS14 ∷ []) (CS14 ∷ CCZ123 ∷ []) (wl 765 (lit c4))
  q59 : Ws → Eqn
  q59 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q60 : Ws → Eqn
  q60 c4 = eqn (CCZ123 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ123 ∷ []) (wl 1321 (lit c4))
  q61 : Ws → Eqn
  q61 c4 = eqn (CCZ123 ∷ CS01 ∷ []) (CS01 ∷ CCZ123 ∷ []) (wl 763 (lit c4))
  q62 : Ws → Eqn
  q62 c4 = eqn (Toff204 ∷ Toff304 ∷ []) (Toff304 ∷ Toff204 ∷ []) (wp 1184 c4)
  q63 : Ws → Eqn
  q63 c4 = eqn (Bx3-4021 ∷ []) (Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ []) (lem-box-tQ-at0314203241 c4)
  q64 : Ws → Eqn
  q64 c4 = eqn (Bx3-4021 ∷ []) (Bx3-4201 ∷ []) (lem-box-perm-1324-at0314203241 c4)
  q65 : Ws → Eqn
  q65 c4 = eqn (Bx3-4201 ∷ []) (CCZ234 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ []) (lem-box-cP-at03143041 c4)
  q66 : Ws → Eqn
  q66 c4 = eqn (CCZ234 ∷ Toff204 ∷ CCZ034 ∷ []) (Toff204 ∷ CCZ234 ∷ []) (wp 1166 c4)
  q67 : Ws → Eqn
  q67 c4 = eqn (CCZ034 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp 377 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (K2 ∷ CS04 ∷ CX24 ∷ CS04⁻ ∷ CX24 ∷ CS02 ∷ K2⁻ ∷ []) (Toff204 ∷ []) (wp 1169 c4)
  q69 : Ws → Eqn
  q69 c4 = eqn (K2⁻ ∷ Toff301 ∷ []) (Toff301 ∷ K2⁻ ∷ []) (wl 1331 (lit c4))
  q70 : Ws → Eqn
  q70 c4 = eqn (CS02 ∷ Toff301 ∷ []) (Toff301 ∷ CS02 ∷ []) (wl 1260 (lit c4))
  q71 : Ws → Eqn
  q71 c4 = eqn (CX24 ∷ Toff301 ∷ []) (Toff301 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF301 (lit c4))
  q72 : Ws → Eqn
  q72 c4 = eqn (CS04⁻ ∷ Toff301 ∷ []) (Toff301 ∷ CS04⁻ ∷ []) (wp 1170 c4)
  q73 : Ws → Eqn
  q73 c4 = eqn (CS04 ∷ Toff301 ∷ []) (Toff301 ∷ CS04 ∷ []) (wp 897 c4)
  q74 : Ws → Eqn
  q74 c4 = eqn (K2 ∷ Toff301 ∷ []) (Toff301 ∷ K2 ∷ []) (wl 1266 (lit c4))
  q75 : Ws → Eqn
  q75 c4 = eqn (CCZ234 ∷ CS14 ∷ []) (CS14 ∷ CCZ234 ∷ []) (wl 452 (lit c4))
  q76 : Ws → Eqn
  q76 c4 = eqn (CCZ234 ∷ CX40 ∷ []) (CX40 ∷ CCZ234 ∷ []) (wp 1171 c4)
  q77 : Ws → Eqn
  q77 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))
  q78 : Ws → Eqn
  q78 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))
  q79 : Ws → Eqn
  q79 c4 = eqn (CCZ034 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ034 ∷ []) (wp 129 c4)
  q80 : Ws → Eqn
  q80 c4 = eqn (Toff204 ∷ CCZ034 ∷ CCZ034 ∷ []) (Toff204 ∷ []) (wp 1172 c4)
  q81 : Ws → Eqn
  q81 c4 = eqn (CCZ014 ∷ Toff301 ∷ []) (Toff301 ∷ CCZ014 ∷ []) (wp 1173 c4)
  q82 : Ws → Eqn
  q82 c4 = eqn (CCZ014 ∷ Toff204 ∷ []) (Toff204 ∷ CCZ014 ∷ []) (wp 1174 c4)
  q83 : Ws → Eqn
  q83 c4 = eqn (CCZ014 ∷ CCZ014 ∷ []) [] (wp 161 c4)
  q84 : Ws → Eqn
  q84 c4 = eqn (Bx3-4021 ∷ []) (Bx3-2401 ∷ []) (lem-box-perm-3124-at0314203241 c4)
  q85 : Ws → Eqn
  q85 c4 = eqn (Bx2-4031 ∷ []) (Bx2-3401 ∷ []) (lem-box-perm-3124-at02142041 c4)
  q86 : Ws → Eqn
  q86 c4 = eqn (Bx3-2401 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-2401 ∷ []) (lem-box-box-1-at0312243041 c4)
  q87 : Ws → Eqn
  q87 c4 = eqn (Bx2-3401 ∷ []) (Bx2-4031 ∷ []) (lem-box-perm-2314-at0213243041 c4)
  q88 : Ws → Eqn
  q88 c4 = eqn (Bx3-2401 ∷ []) (Bx3-4021 ∷ []) (lem-box-perm-2314-at0312243041 c4)

-- Tu-box @02142041: 83 steps
lem-Tu-box-at02142041 : Ws → ⟪ (Toff324 ∷ Bx2-4031 ∷ Toff324 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4031 ∷ Bx3-4021 ∷ []) ⟫ʷ
lem-Tu-box-at02142041 c4 = derive (Toff324 ∷ Bx2-4031 ∷ Toff324 ∷ []) (Bx2-4031 ∷ Bx3-4021 ∷ [])
  (rw 1 (q44 c4) ∷
   rw⁻ 0 (q45 c4) ∷
   rw⁻ 2 (q46 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 6 (q47 c4) ∷
   rw 3 (q48 c4) ∷
   rw 5 (q49 c4) ∷
   rw 4 (q50 c4) ∷
   rw 8 (q51 c4) ∷
   rw 7 (q52 c4) ∷
   rw 6 (q53 c4) ∷
   rw 5 (q52 c4) ∷
   rw 4 (q54 c4) ∷
   rw⁻ 5 (q50 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw⁻ 6 (q56 c4) ∷
   rw 5 (q57 c4) ∷
   rw⁻ 9 (q58 c4) ∷
   rw 8 (q59 c4) ∷
   rw⁻ 7 (q60 c4) ∷
   rw 6 (q59 c4) ∷
   rw⁻ 5 (q61 c4) ∷
   rw⁻ 6 (q57 c4) ∷
   rw 3 (q62 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw⁻ 1 (q63 c4) ∷
   rw 1 (q64 c4) ∷
   rw 1 (q65 c4) ∷
   rw⁻ 0 (q66 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 1 (q68 c4) ∷
   rw 7 (q69 c4) ∷
   rw 6 (q70 c4) ∷
   rw 5 (q71 c4) ∷
   rw 4 (q72 c4) ∷
   rw 3 (q71 c4) ∷
   rw 2 (q73 c4) ∷
   rw 1 (q74 c4) ∷
   rw 2 (q68 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 8 (q75 c4) ∷
   rw⁻ 7 (q76 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 5 (q76 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw 3 (q79 c4) ∷
   rw⁻ 2 (q66 c4) ∷
   rw 3 (q80 c4) ∷
   rw 4 (q81 c4) ∷
   rw⁻ 3 (q68 c4) ∷
   rw 9 (q69 c4) ∷
   rw 8 (q70 c4) ∷
   rw 7 (q71 c4) ∷
   rw 6 (q72 c4) ∷
   rw 5 (q71 c4) ∷
   rw 4 (q73 c4) ∷
   rw 3 (q74 c4) ∷
   rw 4 (q68 c4) ∷
   rw⁻ 0 (q65 c4) ∷
   rw⁻ 0 (q64 c4) ∷
   rw 2 (q57 c4) ∷
   rw⁻ 6 (q58 c4) ∷
   rw 5 (q59 c4) ∷
   rw⁻ 4 (q60 c4) ∷
   rw 3 (q59 c4) ∷
   rw⁻ 2 (q61 c4) ∷
   rw⁻ 3 (q57 c4) ∷
   rw 3 (q82 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 8 (q58 c4) ∷
   rw 7 (q59 c4) ∷
   rw⁻ 6 (q60 c4) ∷
   rw 5 (q59 c4) ∷
   rw⁻ 4 (q61 c4) ∷
   rw⁻ 5 (q57 c4) ∷
   rw 5 (q83 c4) ∷
   rw⁻ 1 (q44 c4) ∷
   rw 0 (q84 c4) ∷
   rw 1 (q85 c4) ∷
   rw 0 (q86 c4) ∷
   rw 0 (q87 c4) ∷
   rw 1 (q88 c4) ∷ []) Eq.refl
