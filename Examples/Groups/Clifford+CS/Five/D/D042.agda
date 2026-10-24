{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD042 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D042 (Sᴰ : SD042) where

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
  lem-comm-TOFF013-CX24 : Ws → St 1059
  lem-comm-TOFF013-CX24 = pickᴰ 1 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 2 Sᴰ
  lem-box-perm-1423-at122441 : Ws → St 1257
  lem-box-perm-1423-at122441 = pickᴰ 3 Sᴰ
  lem-box2-at122441 : Ws → St 1259
  lem-box2-at122441 = pickᴰ 4 Sᴰ
  lem-S2-SBOX⟨0·1·42·3⟩ : Ws → St 1523
  lem-S2-SBOX⟨0·1·42·3⟩ = pickᴰ 5 Sᴰ
  lem-S2-SBOX⟨2·0·41·3⟩ : Ws → St 1525
  lem-S2-SBOX⟨2·0·41·3⟩ = pickᴰ 6 Sᴰ
  lem-CKc-box-at12213443 : Ws → St 1532
  lem-CKc-box-at12213443 = pickᴰ 7 Sᴰ
  lem-CKc-box-at13213442 : Ws → St 1534
  lem-CKc-box-at13213442 = pickᴰ 8 Sᴰ
  lem-box-perm-1342-at12213443 : Ws → St 1537
  lem-box-perm-1342-at12213443 = pickᴰ 9 Sᴰ
  lem-box-perm-3421-at122441 : Ws → St 1540
  lem-box-perm-3421-at122441 = pickᴰ 10 Sᴰ
  lem-box-perm-4312-at13213442 : Ws → St 1545
  lem-box-perm-4312-at13213442 = pickᴰ 11 Sᴰ

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
  q26 c4 = sE 1259 (lem-box2-at122441 c4)
  q27 : Ws → Eqn
  q27 c4 = wlE 1037 (lit c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 305 (lit c4)

-- nf-CS-K0@2: 284 steps
lem-nf-CS-K0at2 : Ws → ⟪ (ℓ "乩亇侬亇侬") ⟫ʷ ≈ ⟪ (ℓ "乩亇亭乇亭么交亇交亭乇亭么") ⟫ʷ
lem-nf-CS-K0at2 c4 = derive (ℓ "乩亇侬亇侬") (ℓ "乩亇亭乇亭么交亇交亭乇亭么")
  (re 2 1 (ℓ "仞亭侪亭侫") ∷
   re 4 1 (ℓ "乇") ∷
   re 6 1 (ℓ "么") ∷
   re 8 1 (ℓ "仞亭侪亭侫") ∷
   re 10 1 (ℓ "乇") ∷
   re 12 1 (ℓ "么") ∷
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
  q29 c4 = sE 1257 (lem-box-perm-1423-at122441 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1532 (lem-CKc-box-at12213443 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 1537 (lem-box-perm-1342-at12213443 c4)

-- nf-CS-K1@2: 284 steps
lem-nf-CS-K1at2 : Ws → ⟪ (ℓ "乹亊侬亊侬") ⟫ʷ ≈ ⟪ (ℓ "乹亊亭乇亭么交亊交亭乇亭么") ⟫ʷ
lem-nf-CS-K1at2 c4 = derive (ℓ "乹亊侬亊侬") (ℓ "乹亊亭乇亭么交亊交亭乇亭么")
  (re 2 1 (ℓ "仞亭侪亭侫") ∷
   re 4 1 (ℓ "乇") ∷
   re 6 1 (ℓ "么") ∷
   re 8 1 (ℓ "仞亭侪亭侫") ∷
   re 10 1 (ℓ "乇") ∷
   re 12 1 (ℓ "么") ∷
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
  q32 c4 = sE 1525 (lem-S2-SBOX⟨2·0·41·3⟩ c4)
  q33 : Ws → Eqn
  q33 c4 = wpE 1127 c4

-- L-CX01-0: 2 steps
lem-L-CX01-0 : Ws → ⟪ (ℓ "亄俄俄亄丢") ⟫ʷ ≈ ⟪ (ℓ "亖") ⟫ʷ
lem-L-CX01-0 c4 = derive (ℓ "亄俄俄亄丢") (ℓ "亖")
  (rw 1 (q32 c4) ∷
   rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = sE 1523 (lem-S2-SBOX⟨0·1·42·3⟩ c4)
  q35 : Ws → Eqn
  q35 c4 = wlE 1301 (lit c4)

-- L-CX01-1: 2 steps
lem-L-CX01-1 : Ws → ⟪ (ℓ "亇侧侧亇丢") ⟫ʷ ≈ ⟪ (ℓ "亪") ⟫ʷ
lem-L-CX01-1 c4 = derive (ℓ "亇侧侧亇丢") (ℓ "亪")
  (rw 1 (q34 c4) ∷
   rw 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wlE 1302 (lit c4)

-- L-CX10-1: 2 steps
lem-L-CX10-1 : Ws → ⟪ (ℓ "亄侧侧亄丢") ⟫ʷ ≈ ⟪ (ℓ "亩") ⟫ʷ
lem-L-CX10-1 c4 = derive (ℓ "亄侧侧亄丢") (ℓ "亩")
  (rw 1 (q34 c4) ∷
   rw 0 (q36 c4) ∷ []) Eq.refl
