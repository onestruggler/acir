{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD070 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D070 (Sᴰ : SD070) where

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
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 0 Sᴰ
  lem-comm-CX40-CCZ123 : Ws → St 20
  lem-comm-CX40-CCZ123 = pickᴰ 1 Sᴰ
  lem-comm-TOFF013-CS24 : Ws → St 1286
  lem-comm-TOFF013-CS24 = pickᴰ 2 Sᴰ
  lem-comm-TOFF013-CX24 : Ws → St 1059
  lem-comm-TOFF013-CX24 = pickᴰ 3 Sᴰ
  lem-comm-CX21-TOFF304 : Ws → St 1748
  lem-comm-CX21-TOFF304 = pickᴰ 4 Sᴰ
  lem-comm-CX24-TOFF301 : Ws → St 1363
  lem-comm-CX24-TOFF301 = pickᴰ 5 Sᴰ
  lem-box-tQ-at02142041 : Ws → St 349
  lem-box-tQ-at02142041 = pickᴰ 6 Sᴰ
  lem-box-tQ-at0314203241 : Ws → St 400
  lem-box-tQ-at0314203241 = pickᴰ 7 Sᴰ
  lem-box-cP-at03143041 : Ws → St 1122
  lem-box-cP-at03143041 = pickᴰ 8 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 9 Sᴰ
  lem-box-perm-2314-at0213243041 : Ws → St 1553
  lem-box-perm-2314-at0213243041 = pickᴰ 10 Sᴰ
  lem-box-perm-1423-at122441 : Ws → St 1257
  lem-box-perm-1423-at122441 = pickᴰ 11 Sᴰ
  lem-box2-at122441 : Ws → St 1259
  lem-box2-at122441 = pickᴰ 12 Sᴰ
  lem-box-perm-1324-at0314203241 : Ws → St 1749
  lem-box-perm-1324-at0314203241 = pickᴰ 13 Sᴰ
  lem-box-perm-2314-at0312243041 : Ws → St 1555
  lem-box-perm-2314-at0312243041 = pickᴰ 14 Sᴰ
  lem-box-perm-3124-at02142041 : Ws → St 1556
  lem-box-perm-3124-at02142041 = pickᴰ 15 Sᴰ
  lem-box-perm-3124-at0314203241 : Ws → St 1557
  lem-box-perm-3124-at0314203241 = pickᴰ 16 Sᴰ
  lem-CKc-box-at12213443 : Ws → St 1532
  lem-CKc-box-at12213443 = pickᴰ 17 Sᴰ
  lem-CKc-box-at13213442 : Ws → St 1534
  lem-CKc-box-at13213442 = pickᴰ 18 Sᴰ
  lem-box-perm-1342-at12213443 : Ws → St 1537
  lem-box-perm-1342-at12213443 = pickᴰ 19 Sᴰ
  lem-box-perm-3421-at122441 : Ws → St 1540
  lem-box-perm-3421-at122441 = pickᴰ 20 Sᴰ
  lem-box-perm-4312-at13213442 : Ws → St 1545
  lem-box-perm-4312-at13213442 = pickᴰ 21 Sᴰ
  lem-nf-CS-K0at2 : Ws → St 1750
  lem-nf-CS-K0at2 = pickᴰ 22 Sᴰ
  lem-nf-CS-K1at2 : Ws → St 1751
  lem-nf-CS-K1at2 = pickᴰ 23 Sᴰ
  lem-box-box-1-at0312243041 : Ws → St 1752
  lem-box-box-1-at0312243041 = pickᴰ 24 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q2 : Ws → Eqn
  q2 c4 = wpE 843 c4
  q3 : Ws → Eqn
  q3 c4 = wpE 845 c4
  q4 : Ws → Eqn
  q4 c4 = wlE 241 (lit c4)
  q5 : Ws → Eqn
  q5 c4 = wpE 89 c4
  q6 : Ws → Eqn
  q6 c4 = wpE 36 c4
  q7 : Ws → Eqn
  q7 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 35 c4
  q9 : Ws → Eqn
  q9 c4 = wpE 34 c4
  q10 : Ws → Eqn
  q10 c4 = wpE 88 c4
  q11 : Ws → Eqn
  q11 c4 = wpE 97 c4
  q12 : Ws → Eqn
  q12 c4 = wlE 245 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wpE 95 c4
  q14 : Ws → Eqn
  q14 c4 = sE 1059 (lem-comm-TOFF013-CX24 c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 94 c4
  q16 : Ws → Eqn
  q16 c4 = wlE 246 (lit c4)
  q17 : Ws → Eqn
  q17 c4 = wpE 842 c4
  q18 : Ws → Eqn
  q18 c4 = wpE 90 c4
  q19 : Ws → Eqn
  q19 c4 = wlE 247 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 81 c4
  q21 : Ws → Eqn
  q21 c4 = wlE 244 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wpE 87 c4
  q23 : Ws → Eqn
  q23 c4 = sE 1540 (lem-box-perm-3421-at122441 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1534 (lem-CKc-box-at13213442 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1545 (lem-box-perm-4312-at13213442 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1286 (lem-comm-TOFF013-CS24 c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 909 c4
  q28 : Ws → Eqn
  q28 c4 = wlE 234 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wlE 242 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = wpE 92 c4
  q31 : Ws → Eqn
  q31 c4 = wpE 91 c4
  q32 : Ws → Eqn
  q32 c4 = sE 1259 (lem-box2-at122441 c4)
  q33 : Ws → Eqn
  q33 c4 = wlE 1037 (lit c4)
  q34 : Ws → Eqn
  q34 c4 = wlE 305 (lit c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 1297 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wlE 181 (lit c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 1298 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = sE 1750 (lem-nf-CS-K0at2 c4)

-- F1-CS-K0@2: 343 steps
lem-F1-CS-K0at2 : Ws → ⟪ (ℓ "侬亇侬亇乩") ⟫ʷ ≈ ⟪ (ℓ "乩亇侬亇侬") ⟫ʷ
lem-F1-CS-K0at2 c4 = derive (ℓ "侬亇侬亇乩") (ℓ "乩亇侬亇侬")
  (re 0 1 (ℓ "仞亭侪亭侫") ∷
   re 2 1 (ℓ "乇") ∷
   re 4 1 (ℓ "么") ∷
   re 6 1 (ℓ "仞亭侪亭侫") ∷
   re 8 1 (ℓ "乇") ∷
   re 10 1 (ℓ "么") ∷
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
  q39 c4 = sE 1257 (lem-box-perm-1423-at122441 c4)
  q40 : Ws → Eqn
  q40 c4 = sE 1532 (lem-CKc-box-at12213443 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1537 (lem-box-perm-1342-at12213443 c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 1299 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1751 (lem-nf-CS-K1at2 c4)

-- F1-CS-K1@2: 343 steps
lem-F1-CS-K1at2 : Ws → ⟪ (ℓ "侬亊侬亊乹") ⟫ʷ ≈ ⟪ (ℓ "乹亊侬亊侬") ⟫ʷ
lem-F1-CS-K1at2 c4 = derive (ℓ "侬亊侬亊乹") (ℓ "乹亊侬亊侬")
  (re 0 1 (ℓ "仞亭侪亭侫") ∷
   re 2 1 (ℓ "乇") ∷
   re 4 1 (ℓ "么") ∷
   re 6 1 (ℓ "仞亭侪亭侫") ∷
   re 8 1 (ℓ "乇") ∷
   re 10 1 (ℓ "么") ∷
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
  q44 c4 = sE 349 (lem-box-tQ-at02142041 c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 1200 c4
  q46 : Ws → Eqn
  q46 c4 = wlE 215 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = wlE 1355 (lit c4)
  q48 : Ws → Eqn
  q48 c4 = wpE 946 c4
  q49 : Ws → Eqn
  q49 c4 = wpE 687 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 271 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wpE 691 c4
  q52 : Ws → Eqn
  q52 c4 = sE 1748 (lem-comm-CX21-TOFF304 c4)
  q53 : Ws → Eqn
  q53 c4 = wpE 1201 c4
  q54 : Ws → Eqn
  q54 c4 = wpE 1037 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 66 c4
  q56 : Ws → Eqn
  q56 c4 = wlE 462 (lit c4)
  q57 : Ws → Eqn
  q57 c4 = wpE 1143 c4
  q58 : Ws → Eqn
  q58 c4 = wlE 765 (lit c4)
  q59 : Ws → Eqn
  q59 c4 = sE 20 (lem-comm-CX40-CCZ123 c4)
  q60 : Ws → Eqn
  q60 c4 = wlE 1321 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = wlE 763 (lit c4)
  q62 : Ws → Eqn
  q62 c4 = wpE 1184 c4
  q63 : Ws → Eqn
  q63 c4 = sE 400 (lem-box-tQ-at0314203241 c4)
  q64 : Ws → Eqn
  q64 c4 = sE 1749 (lem-box-perm-1324-at0314203241 c4)
  q65 : Ws → Eqn
  q65 c4 = sE 1122 (lem-box-cP-at03143041 c4)
  q66 : Ws → Eqn
  q66 c4 = wpE 1166 c4
  q67 : Ws → Eqn
  q67 c4 = wpE 377 c4
  q68 : Ws → Eqn
  q68 c4 = wpE 1169 c4
  q69 : Ws → Eqn
  q69 c4 = wlE 1331 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wlE 1260 (lit c4)
  q71 : Ws → Eqn
  q71 c4 = sE 1363 (lem-comm-CX24-TOFF301 c4)
  q72 : Ws → Eqn
  q72 c4 = wpE 1170 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 897 c4
  q74 : Ws → Eqn
  q74 c4 = wlE 1266 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 452 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wpE 1171 c4
  q77 : Ws → Eqn
  q77 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))
  q78 : Ws → Eqn
  q78 c4 = eqn (ℓ "丨亰") (ℓ "亰丨") (c₂ (CS) (CCZ))
  q79 : Ws → Eqn
  q79 c4 = wpE 129 c4
  q80 : Ws → Eqn
  q80 c4 = wpE 1172 c4
  q81 : Ws → Eqn
  q81 c4 = wpE 1173 c4
  q82 : Ws → Eqn
  q82 c4 = wpE 1174 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 161 c4
  q84 : Ws → Eqn
  q84 c4 = sE 1557 (lem-box-perm-3124-at0314203241 c4)
  q85 : Ws → Eqn
  q85 c4 = sE 1556 (lem-box-perm-3124-at02142041 c4)
  q86 : Ws → Eqn
  q86 c4 = sE 1752 (lem-box-box-1-at0312243041 c4)
  q87 : Ws → Eqn
  q87 c4 = sE 1553 (lem-box-perm-2314-at0213243041 c4)
  q88 : Ws → Eqn
  q88 c4 = sE 1555 (lem-box-perm-2314-at0312243041 c4)

-- Tu-box @02142041: 83 steps
lem-Tu-box-at02142041 : Ws → ⟪ (ℓ "亲余亲") ⟫ʷ ≈ ⟪ (ℓ "余佾") ⟫ʷ
lem-Tu-box-at02142041 c4 = derive (ℓ "亲余亲") (ℓ "余佾")
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
