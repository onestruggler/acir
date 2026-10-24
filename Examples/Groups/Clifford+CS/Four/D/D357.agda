{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D357 (W : Ws) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

private
  q1 : Eqn
  q1 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q2 : Eqn
  q2 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丈乊") (ℓ "乊丈") (low₁-comm (S) (((CS • CS • CS) ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q6 : Eqn
  q6 = eqn (ℓ "两乊") (ℓ "乊两") (low-comm (CK₀₁) ((CS • CS • CS)))
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q9 : Eqn
  q9 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q10 : Eqn
  q10 = wE 6 W
  q11 : Eqn
  q11 = wE 686 W
  q12 : Eqn
  q12 = wE 39 W
  q13 : Eqn
  q13 = wE 31 W
  q14 : Eqn
  q14 = wE 973 W
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q20 : Eqn
  q20 = wE 535 W
  q21 : Eqn
  q21 = wE 21 W
  q22 : Eqn
  q22 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q23 : Eqn
  q23 = wE 51 W
  q24 : Eqn
  q24 = wE 360 W
  q25 : Eqn
  q25 = eqn (ℓ "丳乘") (ℓ "乘丳") (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q26 : Eqn
  q26 = wE 362 W
  q27 : Eqn
  q27 = wE 974 W
  q28 : Eqn
  q28 = wE 975 W
  q29 : Eqn
  q29 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q30 : Eqn
  q30 = eqn (ℓ "丈乌") (ℓ "乌丈") (low₁-comm (S) ((CX₀₁ ↑)))
  q31 : Eqn
  q31 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];2,0->1) passes white iX via V2 conjugates 3 part0: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0 : ⟪ (ℓ "乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丘乌丘丠丠丠两丈丠丠丠丠丠丠举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0 = derive (ℓ "乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丘乌丘丠丠丠两丈丠丠丠丠丠丠举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘")
  (rw 73 q1 ∷
   rw 74 q2 ∷
   rw 75 q1 ∷
   rw 72 q1 ∷
   rw 73 q2 ∷
   rw 74 q1 ∷
   rw 71 q1 ∷
   rw 72 q2 ∷
   rw 73 q1 ∷
   rw 70 q1 ∷
   rw 71 q2 ∷
   rw 72 q1 ∷
   rw 69 q1 ∷
   rw 70 q2 ∷
   rw 71 q1 ∷
   rw 68 q1 ∷
   rw 69 q2 ∷
   rw 70 q1 ∷
   rw 67 q3 ∷
   rw 68 q4 ∷
   rw 69 q3 ∷
   rw 66 q5 ∷
   rw 67 q6 ∷
   rw 68 q5 ∷
   rw 65 q1 ∷
   rw 66 q2 ∷
   rw 67 q1 ∷
   rw 64 q1 ∷
   rw 65 q2 ∷
   rw 66 q1 ∷
   rw 63 q1 ∷
   rw 64 q2 ∷
   rw 65 q1 ∷
   rw 62 q3 ∷
   rw 63 q4 ∷
   rw 64 q3 ∷
   rw 61 q5 ∷
   rw 62 q6 ∷
   rw 63 q5 ∷
   rw 60 q3 ∷
   rw 61 q4 ∷
   rw 62 q3 ∷
   rw 59 q5 ∷
   rw 60 q6 ∷
   rw 61 q5 ∷
   rw 62 q7 ∷
   rw⁻ 61 q8 ∷
   rw⁻ 60 q9 ∷
   rw⁻ 59 q8 ∷
   rw 58 q10 ∷
   rw 59 q11 ∷
   rw 58 q8 ∷
   rw 59 q9 ∷
   rw 60 q8 ∷
   rw 61 q12 ∷
   rw 62 q13 ∷
   rw 57 q3 ∷
   rw 58 q4 ∷
   rw 59 q3 ∷
   rw 56 q5 ∷
   rw 57 q6 ∷
   rw 58 q5 ∷
   rw 55 q3 ∷
   rw 56 q4 ∷
   rw 57 q3 ∷
   rw 54 q3 ∷
   rw 55 q4 ∷
   rw 56 q3 ∷
   rw 53 q3 ∷
   rw 54 q4 ∷
   rw 55 q3 ∷
   rw 52 q3 ∷
   rw 53 q4 ∷
   rw 54 q3 ∷
   rw 51 q5 ∷
   rw 52 q6 ∷
   rw 53 q5 ∷
   rw 50 q3 ∷
   rw 51 q4 ∷
   rw 52 q3 ∷
   rw 49 q3 ∷
   rw 50 q4 ∷
   rw 51 q3 ∷
   rw 48 q3 ∷
   rw 49 q4 ∷
   rw 50 q3 ∷
   rw 47 q1 ∷
   rw 48 q2 ∷
   rw 49 q1 ∷
   rw 46 q1 ∷
   rw 47 q2 ∷
   rw 48 q1 ∷
   rw 45 q1 ∷
   rw 46 q2 ∷
   rw 47 q1 ∷
   rw 44 q1 ∷
   rw 45 q2 ∷
   rw 46 q1 ∷
   rw 43 q1 ∷
   rw 44 q2 ∷
   rw 45 q1 ∷
   rw 42 q1 ∷
   rw 43 q2 ∷
   rw 44 q1 ∷
   rw 41 q1 ∷
   rw 42 q2 ∷
   rw 43 q1 ∷
   rw 40 q1 ∷
   rw 41 q2 ∷
   rw 42 q1 ∷
   rw 39 q1 ∷
   rw 40 q2 ∷
   rw 41 q1 ∷
   rw 38 q3 ∷
   rw 39 q4 ∷
   rw 40 q3 ∷
   rw 37 q5 ∷
   rw 38 q6 ∷
   rw 39 q5 ∷
   rw 36 q3 ∷
   rw 37 q4 ∷
   rw 38 q3 ∷
   rw 35 q3 ∷
   rw 36 q4 ∷
   rw 37 q3 ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q3 ∷
   rw 33 q1 ∷
   rw 34 q2 ∷
   rw 35 q1 ∷
   rw 32 q1 ∷
   rw 33 q2 ∷
   rw 34 q1 ∷
   rw 31 q1 ∷
   rw 32 q2 ∷
   rw 33 q1 ∷
   rw 30 q1 ∷
   rw 31 q2 ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   rw 30 q2 ∷
   rw 31 q1 ∷
   rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   rw 27 q2 ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q1 ∷
   rw 25 q2 ∷
   rw 26 q1 ∷
   rw 23 q1 ∷
   rw 24 q2 ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   rw 23 q2 ∷
   rw 24 q1 ∷
   rw 21 q1 ∷
   rw 22 q2 ∷
   rw 23 q1 ∷
   rw 20 q1 ∷
   rw 21 q2 ∷
   rw 22 q1 ∷
   rw 19 q1 ∷
   rw 20 q2 ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   rw 18 q2 ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   rw 17 q2 ∷
   rw 18 q1 ∷
   rw 19 q7 ∷
   rw⁻ 18 q8 ∷
   rw⁻ 17 q9 ∷
   rw⁻ 16 q8 ∷
   rw 15 q10 ∷
   rw 16 q11 ∷
   rw 15 q8 ∷
   rw 16 q9 ∷
   rw 17 q8 ∷
   rw 18 q12 ∷
   rw 19 q13 ∷
   rw 0 q14 ∷
   rw 81 q15 ∷
   re 80 1 (ℓ "乏丷乏") ∷
   rw 82 q16 ∷
   re 79 1 (ℓ "乏丷乏") ∷
   rw 81 q16 ∷
   re 78 1 (ℓ "乏么乏") ∷
   rw 80 q16 ∷
   re 77 1 (ℓ "乏丷乏") ∷
   rw 79 q16 ∷
   rw 76 q17 ∷
   rw 75 q17 ∷
   rw 74 q17 ∷
   rw 73 q17 ∷
   rw 72 q17 ∷
   rw 71 q17 ∷
   rw 70 q18 ∷
   rw 69 q19 ∷
   rw 68 q17 ∷
   rw 67 q17 ∷
   rw 66 q17 ∷
   rw 65 q18 ∷
   rw 64 q19 ∷
   rw 63 q18 ∷
   rw 62 q19 ∷
   rw 63 q20 ∷
   rw 64 q15 ∷
   re 62 3 (ℓ "举") ∷
   rw 65 q15 ∷
   re 63 3 (ℓ "乕") ∷
   rw 66 q15 ∷
   re 64 3 (ℓ "举") ∷
   rw 67 q15 ∷
   re 65 3 (ℓ "举") ∷
   rw⁻ 66 q19 ∷
   rw⁻ 67 q18 ∷
   rw⁻ 68 q19 ∷
   rw⁻ 69 q18 ∷
   rw⁻ 70 q17 ∷
   rw⁻ 71 q17 ∷
   rw⁻ 72 q17 ∷
   rw⁻ 73 q19 ∷
   rw⁻ 74 q18 ∷
   rw⁻ 75 q17 ∷
   rw⁻ 76 q17 ∷
   rw⁻ 77 q17 ∷
   rw⁻ 78 q17 ∷
   rw⁻ 79 q17 ∷
   rw⁻ 80 q17 ∷
   rw 81 q16 ∷
   re 62 1 (ℓ "乏丷乏") ∷
   rw 61 q15 ∷
   re 62 3 (ℓ "乐") ∷
   re 62 1 (ℓ "乏丼丳丼乏") ∷
   rw 68 q15 ∷
   re 66 3 (ℓ "举") ∷
   rw 65 q21 ∷
   rw 64 q22 ∷
   rw 63 q23 ∷
   re 63 1 (ℓ "乏丷乏") ∷
   rw 62 q16 ∷
   re 63 5 (ℓ "乐") ∷
   re 63 1 (ℓ "乏乃乏") ∷
   rw 65 q16 ∷
   re 61 3 (ℓ "举") ∷
   re 63 1 (ℓ "乏么乏") ∷
   rw 62 q15 ∷
   re 63 3 (ℓ "乐") ∷
   re 63 1 (ℓ "乏丼丳丼乏") ∷
   rw 69 q15 ∷
   re 67 3 (ℓ "乕") ∷
   rw 66 q24 ∷
   rw 65 q25 ∷
   rw 64 q26 ∷
   re 64 1 (ℓ "乏么乏") ∷
   rw 63 q16 ∷
   re 64 5 (ℓ "乐") ∷
   re 64 1 (ℓ "乏乃乏") ∷
   rw 66 q16 ∷
   re 62 3 (ℓ "乕") ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 63 q15 ∷
   re 64 3 (ℓ "乐") ∷
   re 64 1 (ℓ "乏丼丳丼乏") ∷
   rw 70 q15 ∷
   re 68 3 (ℓ "举") ∷
   rw 67 q21 ∷
   rw 66 q22 ∷
   rw 65 q23 ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q16 ∷
   re 65 5 (ℓ "乐") ∷
   re 65 1 (ℓ "乏乃乏") ∷
   rw 67 q16 ∷
   re 63 3 (ℓ "举") ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q15 ∷
   re 65 3 (ℓ "乐") ∷
   re 65 1 (ℓ "乏丼丳丼乏") ∷
   rw 71 q15 ∷
   re 69 3 (ℓ "举") ∷
   rw 68 q21 ∷
   rw 67 q22 ∷
   rw 66 q23 ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q16 ∷
   re 66 5 (ℓ "乐") ∷
   re 66 1 (ℓ "乏乃乏") ∷
   rw 68 q16 ∷
   re 64 3 (ℓ "举") ∷
   rw 65 q15 ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 66 q16 ∷
   re 63 1 (ℓ "乏丷乏") ∷
   rw 65 q16 ∷
   re 62 1 (ℓ "乏么乏") ∷
   rw 64 q16 ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 63 q16 ∷
   rw 60 q18 ∷
   rw 59 q19 ∷
   rw 58 q18 ∷
   rw 57 q18 ∷
   rw 56 q18 ∷
   rw 55 q18 ∷
   rw 54 q19 ∷
   rw 53 q18 ∷
   rw 52 q18 ∷
   rw 51 q18 ∷
   rw 50 q17 ∷
   rw 49 q17 ∷
   rw 48 q17 ∷
   rw 47 q17 ∷
   rw 46 q17 ∷
   rw 45 q17 ∷
   rw 44 q17 ∷
   rw 43 q17 ∷
   rw 42 q17 ∷
   rw 41 q18 ∷
   rw 40 q19 ∷
   rw 39 q18 ∷
   rw 38 q18 ∷
   rw 37 q18 ∷
   rw 36 q17 ∷
   rw 35 q17 ∷
   rw 34 q17 ∷
   rw 33 q17 ∷
   rw 32 q17 ∷
   rw 31 q17 ∷
   rw 30 q17 ∷
   rw 29 q17 ∷
   rw 28 q17 ∷
   rw 27 q17 ∷
   rw 26 q17 ∷
   rw 25 q17 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   rw 22 q17 ∷
   rw 21 q17 ∷
   rw 20 q17 ∷
   rw 19 q17 ∷
   rw 20 q27 ∷
   rw 21 q15 ∷
   re 19 3 (ℓ "举") ∷
   rw 22 q15 ∷
   re 20 3 (ℓ "乕") ∷
   rw 23 q15 ∷
   re 21 3 (ℓ "举") ∷
   rw 24 q15 ∷
   re 22 3 (ℓ "举") ∷
   rw⁻ 23 q17 ∷
   rw⁻ 24 q17 ∷
   rw⁻ 25 q17 ∷
   rw⁻ 26 q17 ∷
   rw⁻ 27 q17 ∷
   rw⁻ 28 q17 ∷
   rw⁻ 29 q17 ∷
   rw⁻ 30 q17 ∷
   rw⁻ 31 q17 ∷
   rw⁻ 32 q17 ∷
   rw⁻ 33 q17 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 35 q17 ∷
   rw⁻ 36 q17 ∷
   rw⁻ 37 q17 ∷
   rw⁻ 38 q17 ∷
   rw⁻ 39 q17 ∷
   rw⁻ 40 q17 ∷
   rw⁻ 41 q18 ∷
   rw⁻ 42 q18 ∷
   rw⁻ 43 q18 ∷
   rw⁻ 44 q19 ∷
   rw⁻ 45 q18 ∷
   rw⁻ 46 q17 ∷
   rw⁻ 47 q17 ∷
   rw⁻ 48 q17 ∷
   rw⁻ 49 q17 ∷
   rw⁻ 50 q17 ∷
   rw⁻ 51 q17 ∷
   rw⁻ 52 q17 ∷
   rw⁻ 53 q17 ∷
   rw⁻ 54 q17 ∷
   rw⁻ 55 q18 ∷
   rw⁻ 56 q18 ∷
   rw⁻ 57 q18 ∷
   rw⁻ 58 q19 ∷
   rw⁻ 59 q18 ∷
   rw⁻ 60 q18 ∷
   rw⁻ 61 q18 ∷
   rw⁻ 62 q18 ∷
   rw⁻ 63 q19 ∷
   rw⁻ 64 q18 ∷
   rw 65 q16 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q15 ∷
   re 19 3 (ℓ "乐") ∷
   re 19 1 (ℓ "乏丼丳丼乏") ∷
   rw 25 q15 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q21 ∷
   rw 21 q22 ∷
   rw 20 q23 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q16 ∷
   re 20 5 (ℓ "乐") ∷
   re 20 1 (ℓ "乏乃乏") ∷
   rw 22 q16 ∷
   re 18 3 (ℓ "举") ∷
   re 20 1 (ℓ "乏么乏") ∷
   rw 19 q15 ∷
   re 20 3 (ℓ "乐") ∷
   re 20 1 (ℓ "乏丼丳丼乏") ∷
   rw 26 q15 ∷
   re 24 3 (ℓ "乕") ∷
   rw 23 q24 ∷
   rw 22 q25 ∷
   rw 21 q26 ∷
   re 21 1 (ℓ "乏么乏") ∷
   rw 20 q16 ∷
   re 21 5 (ℓ "乐") ∷
   re 21 1 (ℓ "乏乃乏") ∷
   rw 23 q16 ∷
   re 19 3 (ℓ "乕") ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q15 ∷
   re 21 3 (ℓ "乐") ∷
   re 21 1 (ℓ "乏丼丳丼乏") ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q21 ∷
   rw 23 q22 ∷
   rw 22 q23 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q16 ∷
   re 22 5 (ℓ "乐") ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw 24 q16 ∷
   re 20 3 (ℓ "举") ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q15 ∷
   re 22 3 (ℓ "乐") ∷
   re 22 1 (ℓ "乏丼丳丼乏") ∷
   rw 28 q15 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q21 ∷
   rw 24 q22 ∷
   rw 23 q23 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q16 ∷
   re 23 5 (ℓ "乐") ∷
   re 23 1 (ℓ "乏乃乏") ∷
   rw 25 q16 ∷
   re 21 3 (ℓ "举") ∷
   rw 3 q28 ∷
   rw 80 q1 ∷
   rw 81 q29 ∷
   rw 82 q1 ∷
   rw 79 q1 ∷
   rw 80 q29 ∷
   rw 81 q1 ∷
   rw 78 q1 ∷
   rw 79 q29 ∷
   rw 80 q1 ∷
   rw 77 q1 ∷
   rw 78 q29 ∷
   rw 79 q1 ∷
   rw 76 q1 ∷
   rw 77 q29 ∷
   rw 78 q1 ∷
   rw 75 q1 ∷
   rw 76 q29 ∷
   rw 77 q1 ∷
   rw 74 q3 ∷
   rw 75 q30 ∷
   rw 76 q3 ∷
   rw 73 q5 ∷
   rw 74 q31 ∷
   rw 75 q5 ∷
   rw 72 q1 ∷
   rw 73 q29 ∷
   rw 74 q1 ∷
   rw 71 q1 ∷
   rw 72 q29 ∷
   rw 73 q1 ∷
   rw 70 q1 ∷
   rw 71 q29 ∷
   rw 72 q1 ∷ []) Eq.refl
