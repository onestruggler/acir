{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD042 ; pickᴰ)

module Examples.Groups.Clifford+CS.Five.D.D042 (Sᴰ : SD042) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CX13 ; lem-comm-TOFF013-CX24)

-- The lemmas of other derivation modules (DSig).
private
  lem-box-cP-at122441 : Ws → St 850
  lem-box-cP-at122441 = pickᴰ 0 Sᴰ
  lem-box-perm-1423-at122441 : Ws → St 1080
  lem-box-perm-1423-at122441 = pickᴰ 1 Sᴰ
  lem-box2-at122441 : Ws → St 1082
  lem-box2-at122441 = pickᴰ 2 Sᴰ
  lem-S2-SBOX⟨0·1·42·3⟩ : Ws → St 1313
  lem-S2-SBOX⟨0·1·42·3⟩ = pickᴰ 3 Sᴰ
  lem-S2-SBOX⟨2·0·41·3⟩ : Ws → St 1315
  lem-S2-SBOX⟨2·0·41·3⟩ = pickᴰ 4 Sᴰ
  lem-CKc-box-at12213443 : Ws → St 1322
  lem-CKc-box-at12213443 = pickᴰ 5 Sᴰ
  lem-CKc-box-at13213442 : Ws → St 1324
  lem-CKc-box-at13213442 = pickᴰ 6 Sᴰ
  lem-box-perm-1342-at12213443 : Ws → St 1327
  lem-box-perm-1342-at12213443 = pickᴰ 7 Sᴰ
  lem-box-perm-3421-at122441 : Ws → St 1330
  lem-box-perm-3421-at122441 = pickᴰ 8 Sᴰ
  lem-box-perm-4312-at13213442 : Ws → St 1335
  lem-box-perm-4312-at13213442 = pickᴰ 9 Sᴰ

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
  q26 c4 = eqn (Bx0-2431 ∷ Bx0-2431 ∷ []) [] (lem-box2-at122441 c4)
  q27 : Ws → Eqn
  q27 c4 = eqn (CCZ234 ∷ Toff134 ∷ CS12 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl 1037 (lit c4))
  q28 : Ws → Eqn
  q28 c4 = eqn (CCZ234 ∷ CCZ234 ∷ []) [] (wl 305 (lit c4))

-- nf-CS-K0@2: 284 steps
lem-nf-CS-K0at2 : Ws → ⟪ (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-nf-CS-K0at2 c4 = derive (CS24 ∷ CK42 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-2-43-1 ∷ []) (CS24 ∷ CK42 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  (re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 6 1 (CS12⁻ ∷ []) ∷
   re 8 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 10 1 (CS12 ∷ []) ∷
   re 12 1 (CS12⁻ ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw 11 (q2 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 12 (q4 c4) ∷
   rw 9 (q11 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 14 (q2 c4) ∷
   rw 13 (q3 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 15 (q4 c4) ∷
   rw 12 (q11 c4) ∷
   rw 14 (q12 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw 14 (q14 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw 14 (q2 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw 11 (q18 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 12 (q4 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw⁻ 16 (q21 c4) ∷
   rw 15 (q22 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw 13 (q22 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw 5 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 6 (q4 c4) ∷
   rw 3 (q11 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q10 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 8 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 9 (q4 c4) ∷
   rw 6 (q11 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q14 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 8 (q23 c4) ∷
   rw 8 (q24 c4) ∷
   rw 11 (q25 c4) ∷
   rw 11 (q1 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 13 (q18 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw 11 (q18 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 15 (q2 c4) ∷
   rw 14 (q3 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q6 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q8 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 16 (q4 c4) ∷
   rw 13 (q11 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 15 (q2 c4) ∷
   rw⁻ 13 (q17 c4) ∷
   rw 12 (q18 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw 13 (q5 c4) ∷
   rw 14 (q6 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q8 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 13 (q4 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 16 (q20 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 19 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw 17 (q18 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 15 (q18 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 19 (q2 c4) ∷
   rw 18 (q3 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw 20 (q5 c4) ∷
   rw 21 (q6 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw 20 (q4 c4) ∷
   rw 17 (q11 c4) ∷
   rw 19 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw 19 (q2 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 16 (q18 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q6 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q8 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 17 (q4 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw 20 (q22 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 19 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 4 (q28 c4) ∷
   rw 9 (q28 c4) ∷
   rw 11 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = eqn (Bx0-2431 ∷ []) (Bx0-2143 ∷ []) (lem-box-perm-1423-at122441 c4)
  q30 : Ws → Eqn
  q30 c4 = eqn (Bx0-2143 ∷ CK43 ∷ []) (CCZ123 ∷ CK43 ∷ CCZ123 ∷ Bx0-2143 ∷ []) (lem-CKc-box-at12213443 c4)
  q31 : Ws → Eqn
  q31 c4 = eqn (Bx0-2143 ∷ []) (Bx0-2431 ∷ []) (lem-box-perm-1342-at12213443 c4)

-- nf-CS-K1@2: 284 steps
lem-nf-CS-K1at2 : Ws → ⟪ (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-nf-CS-K1at2 c4 = derive (CS34 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ []) (CS34 ∷ CK43 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK43 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  (re 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 4 1 (CS12 ∷ []) ∷
   re 6 1 (CS12⁻ ∷ []) ∷
   re 8 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) ∷
   re 10 1 (CS12 ∷ []) ∷
   re 12 1 (CS12⁻ ∷ []) ∷
   rw 8 (q1 c4) ∷
   rw 11 (q2 c4) ∷
   rw 10 (q3 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 12 (q4 c4) ∷
   rw 9 (q11 c4) ∷
   rw 11 (q12 c4) ∷
   rw⁻ 10 (q13 c4) ∷
   rw 11 (q14 c4) ∷
   rw⁻ 12 (q15 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q16 c4) ∷
   rw⁻ 10 (q12 c4) ∷
   rw 11 (q2 c4) ∷
   rw⁻ 9 (q17 c4) ∷
   rw 8 (q18 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 9 (q4 c4) ∷
   rw⁻ 10 (q1 c4) ∷
   rw 10 (q1 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw 10 (q20 c4) ∷
   rw⁻ 11 (q1 c4) ∷
   rw 11 (q1 c4) ∷
   rw 14 (q2 c4) ∷
   rw 13 (q3 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw 15 (q5 c4) ∷
   rw 16 (q6 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q8 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q9 c4) ∷
   rw 21 (q10 c4) ∷
   rw 15 (q4 c4) ∷
   rw 12 (q11 c4) ∷
   rw 14 (q12 c4) ∷
   rw⁻ 13 (q13 c4) ∷
   rw 14 (q14 c4) ∷
   rw⁻ 15 (q15 c4) ∷
   rw 16 (q14 c4) ∷
   rw⁻ 17 (q16 c4) ∷
   rw⁻ 13 (q12 c4) ∷
   rw 14 (q2 c4) ∷
   rw⁻ 12 (q17 c4) ∷
   rw 11 (q18 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw 13 (q6 c4) ∷
   rw 14 (q7 c4) ∷
   rw 15 (q8 c4) ∷
   rw 16 (q7 c4) ∷
   rw 17 (q9 c4) ∷
   rw 18 (q10 c4) ∷
   rw 12 (q4 c4) ∷
   rw⁻ 13 (q1 c4) ∷
   rw 13 (q1 c4) ∷
   rw⁻ 16 (q21 c4) ∷
   rw 15 (q22 c4) ∷
   rw⁻ 14 (q21 c4) ∷
   rw 13 (q22 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 2 (q1 c4) ∷
   rw 5 (q2 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 6 (q4 c4) ∷
   rw 3 (q11 c4) ∷
   rw 5 (q12 c4) ∷
   rw⁻ 4 (q13 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 8 (q16 c4) ∷
   rw⁻ 4 (q12 c4) ∷
   rw 5 (q2 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 2 (q18 c4) ∷
   rw⁻ 4 (q4 c4) ∷
   rw 3 (q5 c4) ∷
   rw 4 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw 6 (q8 c4) ∷
   rw 7 (q7 c4) ∷
   rw 8 (q9 c4) ∷
   rw 9 (q10 c4) ∷
   rw 3 (q4 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw 4 (q1 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 5 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 5 (q1 c4) ∷
   rw 5 (q1 c4) ∷
   rw 8 (q2 c4) ∷
   rw 7 (q3 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw 9 (q5 c4) ∷
   rw 10 (q6 c4) ∷
   rw 11 (q7 c4) ∷
   rw 12 (q8 c4) ∷
   rw 13 (q7 c4) ∷
   rw 14 (q9 c4) ∷
   rw 15 (q10 c4) ∷
   rw 9 (q4 c4) ∷
   rw 6 (q11 c4) ∷
   rw 8 (q12 c4) ∷
   rw⁻ 7 (q13 c4) ∷
   rw 8 (q14 c4) ∷
   rw⁻ 9 (q15 c4) ∷
   rw 10 (q14 c4) ∷
   rw⁻ 11 (q16 c4) ∷
   rw⁻ 7 (q12 c4) ∷
   rw 8 (q2 c4) ∷
   rw⁻ 6 (q17 c4) ∷
   rw 5 (q18 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw 6 (q5 c4) ∷
   rw 7 (q6 c4) ∷
   rw 8 (q7 c4) ∷
   rw 9 (q8 c4) ∷
   rw 10 (q7 c4) ∷
   rw 11 (q9 c4) ∷
   rw 12 (q10 c4) ∷
   rw 6 (q4 c4) ∷
   rw⁻ 7 (q1 c4) ∷
   rw 7 (q1 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw 9 (q22 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw 7 (q22 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw 8 (q29 c4) ∷
   rw 8 (q30 c4) ∷
   rw 11 (q31 c4) ∷
   rw 11 (q1 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 13 (q18 c4) ∷
   rw 13 (q12 c4) ∷
   rw⁻ 12 (q13 c4) ∷
   rw 13 (q14 c4) ∷
   rw⁻ 14 (q15 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q16 c4) ∷
   rw⁻ 12 (q12 c4) ∷
   rw 11 (q18 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw 12 (q1 c4) ∷
   rw 15 (q2 c4) ∷
   rw 14 (q3 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   rw 16 (q5 c4) ∷
   rw 17 (q6 c4) ∷
   rw 18 (q7 c4) ∷
   rw 19 (q8 c4) ∷
   rw 20 (q7 c4) ∷
   rw 21 (q9 c4) ∷
   rw 22 (q10 c4) ∷
   rw 16 (q4 c4) ∷
   rw 13 (q11 c4) ∷
   rw 15 (q12 c4) ∷
   rw⁻ 14 (q13 c4) ∷
   rw 15 (q14 c4) ∷
   rw⁻ 16 (q15 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q16 c4) ∷
   rw⁻ 14 (q12 c4) ∷
   rw 15 (q2 c4) ∷
   rw⁻ 13 (q17 c4) ∷
   rw 12 (q18 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw 13 (q5 c4) ∷
   rw 14 (q6 c4) ∷
   rw 15 (q7 c4) ∷
   rw 16 (q8 c4) ∷
   rw 17 (q7 c4) ∷
   rw 18 (q9 c4) ∷
   rw 19 (q10 c4) ∷
   rw 13 (q4 c4) ∷
   rw⁻ 14 (q1 c4) ∷
   rw 14 (q1 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw 16 (q20 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw 14 (q20 c4) ∷
   rw⁻ 15 (q1 c4) ∷
   rw 15 (q1 c4) ∷
   rw 19 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw 17 (q18 c4) ∷
   rw 17 (q12 c4) ∷
   rw⁻ 16 (q13 c4) ∷
   rw 17 (q14 c4) ∷
   rw⁻ 18 (q15 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q16 c4) ∷
   rw⁻ 16 (q12 c4) ∷
   rw 15 (q18 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw 16 (q1 c4) ∷
   rw 19 (q2 c4) ∷
   rw 18 (q3 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw 20 (q5 c4) ∷
   rw 21 (q6 c4) ∷
   rw 22 (q7 c4) ∷
   rw 23 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw 25 (q9 c4) ∷
   rw 26 (q10 c4) ∷
   rw 20 (q4 c4) ∷
   rw 17 (q11 c4) ∷
   rw 19 (q12 c4) ∷
   rw⁻ 18 (q13 c4) ∷
   rw 19 (q14 c4) ∷
   rw⁻ 20 (q15 c4) ∷
   rw 21 (q14 c4) ∷
   rw⁻ 22 (q16 c4) ∷
   rw⁻ 18 (q12 c4) ∷
   rw 19 (q2 c4) ∷
   rw⁻ 17 (q17 c4) ∷
   rw 16 (q18 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw 17 (q5 c4) ∷
   rw 18 (q6 c4) ∷
   rw 19 (q7 c4) ∷
   rw 20 (q8 c4) ∷
   rw 21 (q7 c4) ∷
   rw 22 (q9 c4) ∷
   rw 23 (q10 c4) ∷
   rw 17 (q4 c4) ∷
   rw⁻ 18 (q1 c4) ∷
   rw 18 (q1 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw 20 (q22 c4) ∷
   rw⁻ 19 (q21 c4) ∷
   rw 18 (q22 c4) ∷
   rw⁻ 19 (q1 c4) ∷
   rw 19 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw 4 (q28 c4) ∷
   rw 9 (q28 c4) ∷
   rw 11 (q28 c4) ∷ []) Eq.refl

private
  q32 : Ws → Eqn
  q32 c4 = eqn (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (CCZ014 ∷ []) (lem-S2-SBOX⟨2·0·41·3⟩ c4)
  q33 : Ws → Eqn
  q33 c4 = eqn (CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ []) (wp 1127 c4)

-- L-CX01-0: 2 steps
lem-L-CX01-0 : Ws → ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff104 ∷ []) ⟫ʷ
lem-L-CX01-0 c4 = derive (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ []) (Toff104 ∷ [])
  (rw 1 (q32 c4) ∷
   rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = eqn (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CK42 ∷ CCZ124 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ []) (wl 1301 (lit c4))

-- L-CX01-1: 2 steps
lem-L-CX01-1 : Ws → ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ []) ⟫ʷ
lem-L-CX01-1 c4 = derive (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Toff214 ∷ [])
  (rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = eqn (CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ []) (wl 1302 (lit c4))

-- L-CX10-1: 2 steps
lem-L-CX10-1 : Ws → ⟪ (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Toff124 ∷ []) ⟫ʷ
lem-L-CX10-1 c4 = derive (CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ []) (Toff124 ∷ [])
  (rw 1 (q34 c4) ∷
   rw 0 (q36 c4) ∷ []) Eq.refl
