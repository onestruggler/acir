{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D358 (W : Ws) where

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
  q1 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q2 : Eqn
  q2 = eqn (ℓ "丈乌") (ℓ "乌丈") (low₁-comm (S) ((CX₀₁ ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q4 : Eqn
  q4 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q7 : Eqn
  q7 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q8 : Eqn
  q8 = wE 6 W
  q9 : Eqn
  q9 = wE 612 W
  q10 : Eqn
  q10 = wE 39 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q13 : Eqn
  q13 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q14 : Eqn
  q14 = wE 976 W
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = wE 689 W
  q18 : Eqn
  q18 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q19 : Eqn
  q19 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q20 : Eqn
  q20 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q21 : Eqn
  q21 = wE 541 W
  q22 : Eqn
  q22 = wE 153 W
  q23 : Eqn
  q23 = wE 21 W
  q24 : Eqn
  q24 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q25 : Eqn
  q25 = wE 51 W
  q26 : Eqn
  q26 = eqn (ℓ "乃丛") (ℓ "丛乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q27 : Eqn
  q27 = wE 360 W
  q28 : Eqn
  q28 = eqn (ℓ "丳乘") (ℓ "乘丳") (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q29 : Eqn
  q29 = wE 362 W
  q30 : Eqn
  q30 = wE 977 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];2,0->1) passes white iX via V2 conjugates 3 part1: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1 : ⟪ (ℓ "丘乊丘举乕举举乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丘乌丘丠丠丠两丈丠丠丠丠丠丠举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举丘乌丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃举举举举举举丛乕举举举丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠乏丠丠丠丠丠丈丈丈两丈丈丈丈两丈乏乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1 = derive (ℓ "丘乊丘举乕举举乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丘乌丘丠丠丠两丈丠丠丠丠丠丠举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举丘乌丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃举举举举举举丛乕举举举丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠乏丠丠丠丠丠丈丈丈两丈丈丈丈两丈乏乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘")
  (rw 69 q1 ∷
   rw 70 q2 ∷
   rw 71 q1 ∷
   rw 68 q3 ∷
   rw 69 q4 ∷
   rw 70 q3 ∷
   rw 67 q1 ∷
   rw 68 q2 ∷
   rw 69 q1 ∷
   rw 66 q3 ∷
   rw 67 q4 ∷
   rw 68 q3 ∷
   rw 69 q5 ∷
   rw⁻ 68 q6 ∷
   rw⁻ 67 q7 ∷
   rw⁻ 66 q6 ∷
   rw 65 q8 ∷
   rw 66 q9 ∷
   rw 65 q6 ∷
   rw 66 q7 ∷
   rw 67 q6 ∷
   rw 68 q10 ∷
   rw 69 q11 ∷
   rw 64 q1 ∷
   rw 65 q2 ∷
   rw 66 q1 ∷
   rw 63 q3 ∷
   rw 64 q4 ∷
   rw 65 q3 ∷
   rw 62 q1 ∷
   rw 63 q2 ∷
   rw 64 q1 ∷
   rw 61 q1 ∷
   rw 62 q2 ∷
   rw 63 q1 ∷
   rw 60 q1 ∷
   rw 61 q2 ∷
   rw 62 q1 ∷
   rw 59 q1 ∷
   rw 60 q2 ∷
   rw 61 q1 ∷
   rw 58 q3 ∷
   rw 59 q4 ∷
   rw 60 q3 ∷
   rw 57 q1 ∷
   rw 58 q2 ∷
   rw 59 q1 ∷
   rw 56 q1 ∷
   rw 57 q2 ∷
   rw 58 q1 ∷
   rw 55 q1 ∷
   rw 56 q2 ∷
   rw 57 q1 ∷
   rw 54 q12 ∷
   rw 55 q13 ∷
   rw 56 q12 ∷
   rw 53 q12 ∷
   rw 54 q13 ∷
   rw 55 q12 ∷
   rw 52 q12 ∷
   rw 53 q13 ∷
   rw 54 q12 ∷
   rw 51 q12 ∷
   rw 52 q13 ∷
   rw 53 q12 ∷
   rw 50 q12 ∷
   rw 51 q13 ∷
   rw 52 q12 ∷
   rw 49 q12 ∷
   rw 50 q13 ∷
   rw 51 q12 ∷
   rw 48 q12 ∷
   rw 49 q13 ∷
   rw 50 q12 ∷
   rw 47 q12 ∷
   rw 48 q13 ∷
   rw 49 q12 ∷
   rw 46 q12 ∷
   rw 47 q13 ∷
   rw 48 q12 ∷
   rw 45 q1 ∷
   rw 46 q2 ∷
   rw 47 q1 ∷
   rw 44 q3 ∷
   rw 45 q4 ∷
   rw 46 q3 ∷
   rw 43 q1 ∷
   rw 44 q2 ∷
   rw 45 q1 ∷
   rw 42 q1 ∷
   rw 43 q2 ∷
   rw 44 q1 ∷
   rw 41 q1 ∷
   rw 42 q2 ∷
   rw 43 q1 ∷
   rw 40 q12 ∷
   rw 41 q13 ∷
   rw 42 q12 ∷
   rw 39 q12 ∷
   rw 40 q13 ∷
   rw 41 q12 ∷
   rw 38 q12 ∷
   rw 39 q13 ∷
   rw 40 q12 ∷
   rw 37 q12 ∷
   rw 38 q13 ∷
   rw 39 q12 ∷
   rw 36 q12 ∷
   rw 37 q13 ∷
   rw 38 q12 ∷
   rw 35 q12 ∷
   rw 36 q13 ∷
   rw 37 q12 ∷
   rw 34 q12 ∷
   rw 35 q13 ∷
   rw 36 q12 ∷
   rw 33 q12 ∷
   rw 34 q13 ∷
   rw 35 q12 ∷
   rw 32 q12 ∷
   rw 33 q13 ∷
   rw 34 q12 ∷
   rw 31 q12 ∷
   rw 32 q13 ∷
   rw 33 q12 ∷
   rw 30 q12 ∷
   rw 31 q13 ∷
   rw 32 q12 ∷
   rw 29 q12 ∷
   rw 30 q13 ∷
   rw 31 q12 ∷
   rw 28 q12 ∷
   rw 29 q13 ∷
   rw 30 q12 ∷
   rw 27 q12 ∷
   rw 28 q13 ∷
   rw 29 q12 ∷
   rw 26 q12 ∷
   rw 27 q13 ∷
   rw 28 q12 ∷
   rw 25 q12 ∷
   rw 26 q13 ∷
   rw 27 q12 ∷
   rw 24 q12 ∷
   rw 25 q13 ∷
   rw 26 q12 ∷
   rw 23 q12 ∷
   rw 24 q13 ∷
   rw 25 q12 ∷
   rw 26 q5 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 23 q6 ∷
   rw 22 q8 ∷
   rw 23 q9 ∷
   rw 22 q6 ∷
   rw 23 q7 ∷
   rw 24 q6 ∷
   rw 25 q10 ∷
   rw 26 q11 ∷
   rw 7 q14 ∷
   rw 95 q15 ∷
   re 94 1 (ℓ "乏丷乏") ∷
   rw 96 q16 ∷
   re 93 1 (ℓ "乏丷乏") ∷
   rw 95 q16 ∷
   re 92 1 (ℓ "乏丷乏") ∷
   rw 94 q16 ∷
   re 91 1 (ℓ "乏么乏") ∷
   rw 93 q16 ∷
   rw 90 q17 ∷
   re 89 1 (ℓ "乏丷乏") ∷
   rw 91 q16 ∷
   re 88 1 (ℓ "乏丷乏") ∷
   rw 90 q16 ∷
   re 87 1 (ℓ "乏丷乏") ∷
   rw 89 q16 ∷
   re 86 1 (ℓ "乏丷乏") ∷
   rw 88 q16 ∷
   re 85 1 (ℓ "乏丷乏") ∷
   rw 87 q16 ∷
   re 84 1 (ℓ "乏丷乏") ∷
   rw 86 q16 ∷
   rw 83 q18 ∷
   rw 82 q18 ∷
   rw 81 q18 ∷
   rw 80 q18 ∷
   rw 79 q18 ∷
   rw 78 q18 ∷
   rw 77 q19 ∷
   rw 76 q20 ∷
   rw 75 q18 ∷
   rw 74 q18 ∷
   rw 73 q18 ∷
   rw 72 q19 ∷
   rw 71 q20 ∷
   rw 70 q19 ∷
   rw 69 q20 ∷
   rw 70 q21 ∷
   rw 71 q15 ∷
   re 69 3 (ℓ "举") ∷
   rw 72 q15 ∷
   re 70 3 (ℓ "举") ∷
   rw 73 q15 ∷
   re 71 3 (ℓ "举") ∷
   rw 74 q15 ∷
   re 72 3 (ℓ "举") ∷
   rw 75 q15 ∷
   re 73 3 (ℓ "举") ∷
   rw 76 q15 ∷
   re 74 3 (ℓ "举") ∷
   rw 75 q22 ∷
   rw 78 q15 ∷
   re 76 3 (ℓ "乕") ∷
   rw 79 q15 ∷
   re 77 3 (ℓ "举") ∷
   rw 80 q15 ∷
   re 78 3 (ℓ "举") ∷
   rw 81 q15 ∷
   re 79 3 (ℓ "举") ∷
   rw⁻ 80 q20 ∷
   rw⁻ 81 q19 ∷
   rw⁻ 82 q20 ∷
   rw⁻ 83 q19 ∷
   rw⁻ 84 q18 ∷
   rw⁻ 85 q18 ∷
   rw⁻ 86 q18 ∷
   rw⁻ 87 q20 ∷
   rw⁻ 88 q19 ∷
   rw⁻ 89 q18 ∷
   rw⁻ 90 q18 ∷
   rw⁻ 91 q18 ∷
   rw⁻ 92 q18 ∷
   rw⁻ 93 q18 ∷
   rw⁻ 94 q18 ∷
   rw 95 q16 ∷
   re 69 1 (ℓ "乏丷乏") ∷
   rw 68 q15 ∷
   re 69 3 (ℓ "乐") ∷
   re 69 1 (ℓ "乏丼丳丼乏") ∷
   rw 75 q15 ∷
   re 73 3 (ℓ "举") ∷
   rw 72 q23 ∷
   rw 71 q24 ∷
   rw 70 q25 ∷
   re 70 1 (ℓ "乏丷乏") ∷
   rw 69 q16 ∷
   re 70 5 (ℓ "乐") ∷
   re 70 1 (ℓ "乏乃乏") ∷
   rw 72 q16 ∷
   re 68 3 (ℓ "举") ∷
   re 70 1 (ℓ "乏丷乏") ∷
   rw 69 q15 ∷
   re 70 3 (ℓ "乐") ∷
   re 70 1 (ℓ "乏丼丳丼乏") ∷
   rw 76 q15 ∷
   re 74 3 (ℓ "举") ∷
   rw 73 q23 ∷
   rw 72 q24 ∷
   rw 71 q25 ∷
   re 71 1 (ℓ "乏丷乏") ∷
   rw 70 q16 ∷
   re 71 5 (ℓ "乐") ∷
   re 71 1 (ℓ "乏乃乏") ∷
   rw 73 q16 ∷
   re 69 3 (ℓ "举") ∷
   re 71 1 (ℓ "乏丷乏") ∷
   rw 70 q15 ∷
   re 71 3 (ℓ "乐") ∷
   re 71 1 (ℓ "乏丼丳丼乏") ∷
   rw 77 q15 ∷
   re 75 3 (ℓ "举") ∷
   rw 74 q23 ∷
   rw 73 q24 ∷
   rw 72 q25 ∷
   re 72 1 (ℓ "乏丷乏") ∷
   rw 71 q16 ∷
   re 72 5 (ℓ "乐") ∷
   re 72 1 (ℓ "乏乃乏") ∷
   rw 74 q16 ∷
   re 70 3 (ℓ "举") ∷
   re 72 1 (ℓ "乏丷乏") ∷
   rw 71 q15 ∷
   re 72 3 (ℓ "乐") ∷
   re 72 1 (ℓ "乏丼丳丼乏") ∷
   rw 78 q15 ∷
   re 76 3 (ℓ "举") ∷
   rw 75 q23 ∷
   rw 74 q24 ∷
   rw 73 q25 ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 72 q16 ∷
   re 73 5 (ℓ "乐") ∷
   re 73 1 (ℓ "乏乃乏") ∷
   rw 75 q16 ∷
   re 71 3 (ℓ "举") ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 72 q15 ∷
   re 73 3 (ℓ "乐") ∷
   re 73 1 (ℓ "乏丼丳丼乏") ∷
   rw 79 q15 ∷
   re 77 3 (ℓ "举") ∷
   rw 76 q23 ∷
   rw 75 q24 ∷
   rw 74 q25 ∷
   re 74 1 (ℓ "乏丷乏") ∷
   rw 73 q16 ∷
   re 74 5 (ℓ "乐") ∷
   re 74 1 (ℓ "乏乃乏") ∷
   rw 76 q16 ∷
   re 72 3 (ℓ "举") ∷
   re 74 1 (ℓ "乏丷乏") ∷
   rw 73 q15 ∷
   re 74 3 (ℓ "乐") ∷
   re 74 1 (ℓ "乏丼丳丼乏") ∷
   rw 80 q15 ∷
   re 78 3 (ℓ "举") ∷
   rw 77 q23 ∷
   rw 76 q24 ∷
   rw 75 q25 ∷
   re 75 1 (ℓ "乏丷乏") ∷
   rw 74 q16 ∷
   re 75 5 (ℓ "乐") ∷
   re 75 1 (ℓ "乏乃乏") ∷
   rw 77 q16 ∷
   re 73 3 (ℓ "举") ∷
   rw 74 q26 ∷
   re 76 1 (ℓ "乏么乏") ∷
   rw 75 q15 ∷
   re 76 3 (ℓ "乐") ∷
   re 76 1 (ℓ "乏丼丳丼乏") ∷
   rw 82 q15 ∷
   re 80 3 (ℓ "乕") ∷
   rw 79 q27 ∷
   rw 78 q28 ∷
   rw 77 q29 ∷
   re 77 1 (ℓ "乏么乏") ∷
   rw 76 q16 ∷
   re 77 5 (ℓ "乐") ∷
   re 77 1 (ℓ "乏乃乏") ∷
   rw 79 q16 ∷
   re 75 3 (ℓ "乕") ∷
   re 77 1 (ℓ "乏丷乏") ∷
   rw 76 q15 ∷
   re 77 3 (ℓ "乐") ∷
   re 77 1 (ℓ "乏丼丳丼乏") ∷
   rw 83 q15 ∷
   re 81 3 (ℓ "举") ∷
   rw 80 q23 ∷
   rw 79 q24 ∷
   rw 78 q25 ∷
   re 78 1 (ℓ "乏丷乏") ∷
   rw 77 q16 ∷
   re 78 5 (ℓ "乐") ∷
   re 78 1 (ℓ "乏乃乏") ∷
   rw 80 q16 ∷
   re 76 3 (ℓ "举") ∷
   re 78 1 (ℓ "乏丷乏") ∷
   rw 77 q15 ∷
   re 78 3 (ℓ "乐") ∷
   re 78 1 (ℓ "乏丼丳丼乏") ∷
   rw 84 q15 ∷
   re 82 3 (ℓ "举") ∷
   rw 81 q23 ∷
   rw 80 q24 ∷
   rw 79 q25 ∷
   re 79 1 (ℓ "乏丷乏") ∷
   rw 78 q16 ∷
   re 79 5 (ℓ "乐") ∷
   re 79 1 (ℓ "乏乃乏") ∷
   rw 81 q16 ∷
   re 77 3 (ℓ "举") ∷
   re 79 1 (ℓ "乏丷乏") ∷
   rw 78 q15 ∷
   re 79 3 (ℓ "乐") ∷
   re 79 1 (ℓ "乏丼丳丼乏") ∷
   rw 85 q15 ∷
   re 83 3 (ℓ "举") ∷
   rw 82 q23 ∷
   rw 81 q24 ∷
   rw 80 q25 ∷
   re 80 1 (ℓ "乏丷乏") ∷
   rw 79 q16 ∷
   re 80 5 (ℓ "乐") ∷
   re 80 1 (ℓ "乏乃乏") ∷
   rw 82 q16 ∷
   re 78 3 (ℓ "举") ∷
   rw 79 q15 ∷
   re 78 1 (ℓ "乏丷乏") ∷
   rw 80 q16 ∷
   re 77 1 (ℓ "乏丷乏") ∷
   rw 79 q16 ∷
   re 76 1 (ℓ "乏丷乏") ∷
   rw 78 q16 ∷
   re 75 1 (ℓ "乏么乏") ∷
   rw 77 q16 ∷
   rw 74 q17 ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 75 q16 ∷
   re 72 1 (ℓ "乏丷乏") ∷
   rw 74 q16 ∷
   re 71 1 (ℓ "乏丷乏") ∷
   rw 73 q16 ∷
   re 70 1 (ℓ "乏丷乏") ∷
   rw 72 q16 ∷
   re 69 1 (ℓ "乏丷乏") ∷
   rw 71 q16 ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 70 q16 ∷
   rw 67 q19 ∷
   rw 66 q20 ∷
   rw 65 q19 ∷
   rw 64 q19 ∷
   rw 63 q19 ∷
   rw 62 q19 ∷
   rw 61 q20 ∷
   rw 60 q19 ∷
   rw 59 q19 ∷
   rw 58 q19 ∷
   rw 57 q18 ∷
   rw 56 q18 ∷
   rw 55 q18 ∷
   rw 54 q18 ∷
   rw 53 q18 ∷
   rw 52 q18 ∷
   rw 51 q18 ∷
   rw 50 q18 ∷
   rw 49 q18 ∷
   rw 48 q19 ∷
   rw 47 q20 ∷
   rw 46 q19 ∷
   rw 45 q19 ∷
   rw 44 q19 ∷
   rw 43 q18 ∷
   rw 42 q18 ∷
   rw 41 q18 ∷
   rw 40 q18 ∷
   rw 39 q18 ∷
   rw 38 q18 ∷
   rw 37 q18 ∷
   rw 36 q18 ∷
   rw 35 q18 ∷
   rw 34 q18 ∷
   rw 33 q18 ∷
   rw 32 q18 ∷
   rw 31 q18 ∷
   rw 30 q18 ∷
   rw 29 q18 ∷
   rw 28 q18 ∷
   rw 27 q18 ∷
   rw 26 q18 ∷
   rw 27 q30 ∷
   rw 28 q15 ∷
   re 26 3 (ℓ "举") ∷
   rw 29 q15 ∷
   re 27 3 (ℓ "举") ∷
   rw 30 q15 ∷
   re 28 3 (ℓ "举") ∷
   rw 31 q15 ∷
   re 29 3 (ℓ "举") ∷
   rw 32 q15 ∷
   re 30 3 (ℓ "举") ∷
   rw 33 q15 ∷
   re 31 3 (ℓ "举") ∷
   rw 32 q22 ∷
   rw 35 q15 ∷
   re 33 3 (ℓ "乕") ∷
   rw 36 q15 ∷
   re 34 3 (ℓ "举") ∷
   rw 37 q15 ∷
   re 35 3 (ℓ "举") ∷
   rw 38 q15 ∷
   re 36 3 (ℓ "举") ∷
   rw⁻ 37 q18 ∷
   rw⁻ 38 q18 ∷
   rw⁻ 39 q18 ∷
   rw⁻ 40 q18 ∷
   rw⁻ 41 q18 ∷
   rw⁻ 42 q18 ∷
   rw⁻ 43 q18 ∷
   rw⁻ 44 q18 ∷
   rw⁻ 45 q18 ∷
   rw⁻ 46 q18 ∷
   rw⁻ 47 q18 ∷
   rw⁻ 48 q18 ∷
   rw⁻ 49 q18 ∷
   rw⁻ 50 q18 ∷
   rw⁻ 51 q18 ∷
   rw⁻ 52 q18 ∷
   rw⁻ 53 q18 ∷
   rw⁻ 54 q18 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q19 ∷
   rw⁻ 57 q19 ∷
   rw⁻ 58 q20 ∷
   rw⁻ 59 q19 ∷
   rw⁻ 60 q18 ∷
   rw⁻ 61 q18 ∷
   rw⁻ 62 q18 ∷
   rw⁻ 63 q18 ∷ []) Eq.refl
