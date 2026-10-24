{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D359 (W : Ws) where

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
  q1 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q2 : Eqn
  q2 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 21 W
  q7 : Eqn
  q7 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 51 W
  q9 : Eqn
  q9 = eqn (ℓ "乃丛") (ℓ "丛乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q10 : Eqn
  q10 = wE 360 W
  q11 : Eqn
  q11 = eqn (ℓ "丳乘") (ℓ "乘丳") (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q12 : Eqn
  q12 = wE 362 W
  q13 : Eqn
  q13 = wE 978 W
  q14 : Eqn
  q14 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q15 : Eqn
  q15 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q16 : Eqn
  q16 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "丈乌") (ℓ "乌丈") (low₁-comm (S) ((CX₀₁ ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q19 : Eqn
  q19 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))
  q20 : Eqn
  q20 = wE 5 W
  q21 : Eqn
  q21 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q22 : Eqn
  q22 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q23 : Eqn
  q23 = wE 6 W
  q24 : Eqn
  q24 = wE 612 W
  q25 : Eqn
  q25 = wE 39 W
  q26 : Eqn
  q26 = wE 31 W
  q27 : Eqn
  q27 = wE 976 W
  q28 : Eqn
  q28 = wE 979 W
  q29 : Eqn
  q29 = wE 980 W
  q30 : Eqn
  q30 = wE 535 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];2,0->1) passes white iX via V2 conjugates 3 part2: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2 : ⟪ (ℓ "丘乊丘举乕举举丘乌丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃举举举举举举丛乕举举举丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠乏丠丠丠丠丠丈丈丈两丈丈丈丈两丈乏乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠乏丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈丷么丷丷乏乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2 = derive (ℓ "丘乊丘举乕举举丘乌丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃举举举举举举丛乕举举举丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠乏丠丠丠丠丠丈丈丈两丈丈丈丈两丈乏乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠乏丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈丷么丷丷乏乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘")
  (rw⁻ 64 q1 ∷
   rw⁻ 65 q1 ∷
   rw⁻ 66 q1 ∷
   rw⁻ 67 q1 ∷
   rw⁻ 68 q1 ∷
   rw⁻ 69 q2 ∷
   rw⁻ 70 q2 ∷
   rw⁻ 71 q2 ∷
   rw⁻ 72 q3 ∷
   rw⁻ 73 q2 ∷
   rw⁻ 74 q2 ∷
   rw⁻ 75 q2 ∷
   rw⁻ 76 q2 ∷
   rw⁻ 77 q3 ∷
   rw⁻ 78 q2 ∷
   rw 79 q4 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q5 ∷
   re 26 3 (ℓ "乐") ∷
   re 26 1 (ℓ "乏丼丳丼乏") ∷
   rw 32 q5 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q6 ∷
   rw 28 q7 ∷
   rw 27 q8 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q4 ∷
   re 27 5 (ℓ "乐") ∷
   re 27 1 (ℓ "乏乃乏") ∷
   rw 29 q4 ∷
   re 25 3 (ℓ "举") ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q5 ∷
   re 27 3 (ℓ "乐") ∷
   re 27 1 (ℓ "乏丼丳丼乏") ∷
   rw 33 q5 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q6 ∷
   rw 29 q7 ∷
   rw 28 q8 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q4 ∷
   re 28 5 (ℓ "乐") ∷
   re 28 1 (ℓ "乏乃乏") ∷
   rw 30 q4 ∷
   re 26 3 (ℓ "举") ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q5 ∷
   re 28 3 (ℓ "乐") ∷
   re 28 1 (ℓ "乏丼丳丼乏") ∷
   rw 34 q5 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q6 ∷
   rw 30 q7 ∷
   rw 29 q8 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q4 ∷
   re 29 5 (ℓ "乐") ∷
   re 29 1 (ℓ "乏乃乏") ∷
   rw 31 q4 ∷
   re 27 3 (ℓ "举") ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q5 ∷
   re 29 3 (ℓ "乐") ∷
   re 29 1 (ℓ "乏丼丳丼乏") ∷
   rw 35 q5 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q6 ∷
   rw 31 q7 ∷
   rw 30 q8 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q4 ∷
   re 30 5 (ℓ "乐") ∷
   re 30 1 (ℓ "乏乃乏") ∷
   rw 32 q4 ∷
   re 28 3 (ℓ "举") ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q5 ∷
   re 30 3 (ℓ "乐") ∷
   re 30 1 (ℓ "乏丼丳丼乏") ∷
   rw 36 q5 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q6 ∷
   rw 32 q7 ∷
   rw 31 q8 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q4 ∷
   re 31 5 (ℓ "乐") ∷
   re 31 1 (ℓ "乏乃乏") ∷
   rw 33 q4 ∷
   re 29 3 (ℓ "举") ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q5 ∷
   re 31 3 (ℓ "乐") ∷
   re 31 1 (ℓ "乏丼丳丼乏") ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "举") ∷
   rw 34 q6 ∷
   rw 33 q7 ∷
   rw 32 q8 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q4 ∷
   re 32 5 (ℓ "乐") ∷
   re 32 1 (ℓ "乏乃乏") ∷
   rw 34 q4 ∷
   re 30 3 (ℓ "举") ∷
   rw 31 q9 ∷
   re 33 1 (ℓ "乏么乏") ∷
   rw 32 q5 ∷
   re 33 3 (ℓ "乐") ∷
   re 33 1 (ℓ "乏丼丳丼乏") ∷
   rw 39 q5 ∷
   re 37 3 (ℓ "乕") ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   rw 34 q12 ∷
   re 34 1 (ℓ "乏么乏") ∷
   rw 33 q4 ∷
   re 34 5 (ℓ "乐") ∷
   re 34 1 (ℓ "乏乃乏") ∷
   rw 36 q4 ∷
   re 32 3 (ℓ "乕") ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 33 q5 ∷
   re 34 3 (ℓ "乐") ∷
   re 34 1 (ℓ "乏丼丳丼乏") ∷
   rw 40 q5 ∷
   re 38 3 (ℓ "举") ∷
   rw 37 q6 ∷
   rw 36 q7 ∷
   rw 35 q8 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 34 q4 ∷
   re 35 5 (ℓ "乐") ∷
   re 35 1 (ℓ "乏乃乏") ∷
   rw 37 q4 ∷
   re 33 3 (ℓ "举") ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 34 q5 ∷
   re 35 3 (ℓ "乐") ∷
   re 35 1 (ℓ "乏丼丳丼乏") ∷
   rw 41 q5 ∷
   re 39 3 (ℓ "举") ∷
   rw 38 q6 ∷
   rw 37 q7 ∷
   rw 36 q8 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q4 ∷
   re 36 5 (ℓ "乐") ∷
   re 36 1 (ℓ "乏乃乏") ∷
   rw 38 q4 ∷
   re 34 3 (ℓ "举") ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q5 ∷
   re 36 3 (ℓ "乐") ∷
   re 36 1 (ℓ "乏丼丳丼乏") ∷
   rw 42 q5 ∷
   re 40 3 (ℓ "举") ∷
   rw 39 q6 ∷
   rw 38 q7 ∷
   rw 37 q8 ∷
   re 37 1 (ℓ "乏丷乏") ∷
   rw 36 q4 ∷
   re 37 5 (ℓ "乐") ∷
   re 37 1 (ℓ "乏乃乏") ∷
   rw 39 q4 ∷
   re 35 3 (ℓ "举") ∷
   rw 10 q13 ∷
   rw 94 q14 ∷
   rw 95 q15 ∷
   rw 96 q14 ∷
   rw 93 q14 ∷
   rw 94 q15 ∷
   rw 95 q14 ∷
   rw 92 q14 ∷
   rw 93 q15 ∷
   rw 94 q14 ∷
   rw 91 q14 ∷
   rw 92 q15 ∷
   rw 93 q14 ∷
   rw 90 q14 ∷
   rw 91 q15 ∷
   rw 92 q14 ∷
   rw 89 q14 ∷
   rw 90 q15 ∷
   rw 91 q14 ∷
   rw 88 q16 ∷
   rw 89 q17 ∷
   rw 90 q16 ∷
   rw 87 q18 ∷
   rw 88 q19 ∷
   rw 89 q18 ∷
   rw 86 q14 ∷
   rw 87 q15 ∷
   rw 88 q14 ∷
   rw 85 q14 ∷
   rw 86 q15 ∷
   rw 87 q14 ∷
   rw 84 q14 ∷
   rw 85 q15 ∷
   rw 86 q14 ∷
   rw 83 q16 ∷
   rw 84 q17 ∷
   rw 85 q16 ∷
   rw 82 q18 ∷
   rw 83 q19 ∷
   rw 84 q18 ∷
   rw 81 q16 ∷
   rw 82 q17 ∷
   rw 83 q16 ∷
   rw 80 q18 ∷
   rw 81 q19 ∷
   rw 82 q18 ∷
   rw 83 q20 ∷
   rw⁻ 82 q21 ∷
   rw⁻ 81 q22 ∷
   rw⁻ 80 q21 ∷
   rw 79 q23 ∷
   rw 80 q24 ∷
   rw 79 q21 ∷
   rw 80 q22 ∷
   rw 81 q21 ∷
   rw 82 q25 ∷
   rw 83 q26 ∷
   rw 78 q16 ∷
   rw 79 q17 ∷
   rw 80 q16 ∷
   rw 77 q18 ∷
   rw 78 q19 ∷
   rw 79 q18 ∷
   rw 76 q16 ∷
   rw 77 q17 ∷
   rw 78 q16 ∷
   rw 75 q16 ∷
   rw 76 q17 ∷
   rw 77 q16 ∷
   rw 74 q16 ∷
   rw 75 q17 ∷
   rw 76 q16 ∷
   rw 73 q16 ∷
   rw 74 q17 ∷
   rw 75 q16 ∷
   rw 72 q18 ∷
   rw 73 q19 ∷
   rw 74 q18 ∷
   rw 71 q16 ∷
   rw 72 q17 ∷
   rw 73 q16 ∷
   rw 70 q16 ∷
   rw 71 q17 ∷
   rw 72 q16 ∷
   rw 69 q16 ∷
   rw 70 q17 ∷
   rw 71 q16 ∷
   rw 68 q14 ∷
   rw 69 q15 ∷
   rw 70 q14 ∷
   rw 67 q14 ∷
   rw 68 q15 ∷
   rw 69 q14 ∷
   rw 66 q14 ∷
   rw 67 q15 ∷
   rw 68 q14 ∷
   rw 65 q14 ∷
   rw 66 q15 ∷
   rw 67 q14 ∷
   rw 64 q14 ∷
   rw 65 q15 ∷
   rw 66 q14 ∷
   rw 63 q14 ∷
   rw 64 q15 ∷
   rw 65 q14 ∷
   rw 62 q14 ∷
   rw 63 q15 ∷
   rw 64 q14 ∷
   rw 61 q14 ∷
   rw 62 q15 ∷
   rw 63 q14 ∷
   rw 60 q14 ∷
   rw 61 q15 ∷
   rw 62 q14 ∷
   rw 59 q16 ∷
   rw 60 q17 ∷
   rw 61 q16 ∷
   rw 58 q18 ∷
   rw 59 q19 ∷
   rw 60 q18 ∷
   rw 57 q16 ∷
   rw 58 q17 ∷
   rw 59 q16 ∷
   rw 56 q16 ∷
   rw 57 q17 ∷
   rw 58 q16 ∷
   rw 55 q16 ∷
   rw 56 q17 ∷
   rw 57 q16 ∷
   rw 54 q14 ∷
   rw 55 q15 ∷
   rw 56 q14 ∷
   rw 53 q14 ∷
   rw 54 q15 ∷
   rw 55 q14 ∷
   rw 52 q14 ∷
   rw 53 q15 ∷
   rw 54 q14 ∷
   rw 51 q14 ∷
   rw 52 q15 ∷
   rw 53 q14 ∷
   rw 50 q14 ∷
   rw 51 q15 ∷
   rw 52 q14 ∷
   rw 49 q14 ∷
   rw 50 q15 ∷
   rw 51 q14 ∷
   rw 48 q14 ∷
   rw 49 q15 ∷
   rw 50 q14 ∷
   rw 47 q14 ∷
   rw 48 q15 ∷
   rw 49 q14 ∷
   rw 46 q14 ∷
   rw 47 q15 ∷
   rw 48 q14 ∷
   rw 45 q14 ∷
   rw 46 q15 ∷
   rw 47 q14 ∷
   rw 44 q14 ∷
   rw 45 q15 ∷
   rw 46 q14 ∷
   rw 43 q14 ∷
   rw 44 q15 ∷
   rw 45 q14 ∷
   rw 42 q14 ∷
   rw 43 q15 ∷
   rw 44 q14 ∷
   rw 41 q14 ∷
   rw 42 q15 ∷
   rw 43 q14 ∷
   rw 40 q14 ∷
   rw 41 q15 ∷
   rw 42 q14 ∷
   rw 39 q14 ∷
   rw 40 q15 ∷
   rw 41 q14 ∷
   rw 38 q14 ∷
   rw 39 q15 ∷
   rw 40 q14 ∷
   rw 37 q14 ∷
   rw 38 q15 ∷
   rw 39 q14 ∷
   rw 40 q20 ∷
   rw⁻ 39 q21 ∷
   rw⁻ 38 q22 ∷
   rw⁻ 37 q21 ∷
   rw 36 q23 ∷
   rw 37 q24 ∷
   rw 36 q21 ∷
   rw 37 q22 ∷
   rw 38 q21 ∷
   rw 39 q25 ∷
   rw 40 q26 ∷
   rw 21 q27 ∷
   rw 24 q28 ∷
   rw 30 q29 ∷
   rw 113 q5 ∷
   re 112 1 (ℓ "乏丷乏") ∷
   rw 114 q4 ∷
   re 111 1 (ℓ "乏丷乏") ∷
   rw 113 q4 ∷
   re 110 1 (ℓ "乏么乏") ∷
   rw 112 q4 ∷
   re 109 1 (ℓ "乏丷乏") ∷
   rw 111 q4 ∷
   rw 108 q1 ∷
   rw 107 q1 ∷
   rw 106 q1 ∷
   rw 105 q1 ∷
   rw 104 q1 ∷
   rw 103 q1 ∷
   rw 102 q2 ∷
   rw 101 q3 ∷
   rw 100 q1 ∷
   rw 99 q1 ∷
   rw 98 q1 ∷
   rw 97 q2 ∷
   rw 96 q3 ∷
   rw 95 q2 ∷
   rw 94 q3 ∷
   rw 95 q30 ∷
   rw 96 q5 ∷
   re 94 3 (ℓ "举") ∷
   rw 97 q5 ∷
   re 95 3 (ℓ "乕") ∷
   rw 98 q5 ∷
   re 96 3 (ℓ "举") ∷
   rw 99 q5 ∷
   re 97 3 (ℓ "举") ∷
   rw⁻ 98 q3 ∷
   rw⁻ 99 q2 ∷
   rw⁻ 100 q3 ∷
   rw⁻ 101 q2 ∷
   rw⁻ 102 q1 ∷
   rw⁻ 103 q1 ∷
   rw⁻ 104 q1 ∷
   rw⁻ 105 q3 ∷
   rw⁻ 106 q2 ∷
   rw⁻ 107 q1 ∷
   rw⁻ 108 q1 ∷
   rw⁻ 109 q1 ∷
   rw⁻ 110 q1 ∷
   rw⁻ 111 q1 ∷
   rw⁻ 112 q1 ∷
   rw 113 q4 ∷
   re 94 1 (ℓ "乏丷乏") ∷
   rw 93 q5 ∷
   re 94 3 (ℓ "乐") ∷
   re 94 1 (ℓ "乏丼丳丼乏") ∷
   rw 100 q5 ∷
   re 98 3 (ℓ "举") ∷
   rw 97 q6 ∷
   rw 96 q7 ∷
   rw 95 q8 ∷
   re 95 1 (ℓ "乏丷乏") ∷
   rw 94 q4 ∷
   re 95 5 (ℓ "乐") ∷
   re 95 1 (ℓ "乏乃乏") ∷
   rw 97 q4 ∷
   re 93 3 (ℓ "举") ∷
   re 95 1 (ℓ "乏么乏") ∷
   rw 94 q5 ∷
   re 95 3 (ℓ "乐") ∷
   re 95 1 (ℓ "乏丼丳丼乏") ∷
   rw 101 q5 ∷
   re 99 3 (ℓ "乕") ∷
   rw 98 q10 ∷
   rw 97 q11 ∷
   rw 96 q12 ∷
   re 96 1 (ℓ "乏么乏") ∷
   rw 95 q4 ∷
   re 96 5 (ℓ "乐") ∷
   re 96 1 (ℓ "乏乃乏") ∷
   rw 98 q4 ∷
   re 94 3 (ℓ "乕") ∷
   re 96 1 (ℓ "乏丷乏") ∷
   rw 95 q5 ∷
   re 96 3 (ℓ "乐") ∷
   re 96 1 (ℓ "乏丼丳丼乏") ∷
   rw 102 q5 ∷
   re 100 3 (ℓ "举") ∷
   rw 99 q6 ∷
   rw 98 q7 ∷
   rw 97 q8 ∷
   re 97 1 (ℓ "乏丷乏") ∷
   rw 96 q4 ∷
   re 97 5 (ℓ "乐") ∷
   re 97 1 (ℓ "乏乃乏") ∷
   rw 99 q4 ∷
   re 95 3 (ℓ "举") ∷
   re 97 1 (ℓ "乏丷乏") ∷
   rw 96 q5 ∷
   re 97 3 (ℓ "乐") ∷
   re 97 1 (ℓ "乏丼丳丼乏") ∷
   rw 103 q5 ∷
   re 101 3 (ℓ "举") ∷
   rw 100 q6 ∷
   rw 99 q7 ∷
   rw 98 q8 ∷
   re 98 1 (ℓ "乏丷乏") ∷
   rw 97 q4 ∷
   re 98 5 (ℓ "乐") ∷
   re 98 1 (ℓ "乏乃乏") ∷
   rw 100 q4 ∷
   re 96 3 (ℓ "举") ∷
   rw 97 q5 ∷
   re 96 1 (ℓ "乏丷乏") ∷
   rw 98 q4 ∷
   re 95 1 (ℓ "乏丷乏") ∷
   rw 97 q4 ∷
   re 94 1 (ℓ "乏么乏") ∷
   rw 96 q4 ∷
   re 93 1 (ℓ "乏丷乏") ∷
   rw 95 q4 ∷
   rw 92 q2 ∷
   rw 91 q3 ∷
   rw 90 q2 ∷
   rw 89 q2 ∷
   rw 88 q2 ∷
   rw 87 q2 ∷
   rw 86 q3 ∷
   rw 85 q2 ∷
   rw 84 q2 ∷
   rw 83 q2 ∷
   rw 82 q1 ∷
   rw 81 q1 ∷
   rw 80 q1 ∷
   rw 79 q1 ∷
   rw 78 q1 ∷
   rw 77 q1 ∷
   rw 76 q1 ∷
   rw 75 q1 ∷ []) Eq.refl
