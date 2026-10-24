{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D143 (W : Ws) where

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
  q4 = wE 535 W
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 21 W
  q8 : Eqn
  q8 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q9 : Eqn
  q9 = wE 51 W
  q10 : Eqn
  q10 = wE 360 W
  q11 : Eqn
  q11 = eqn (ℓ "丳乘") (ℓ "乘丳") (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q12 : Eqn
  q12 = wE 362 W
  q13 : Eqn
  q13 = wE 688 W
  q14 : Eqn
  q14 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q15 : Eqn
  q15 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))
  q16 : Eqn
  q16 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q17 : Eqn
  q17 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q20 : Eqn
  q20 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q21 : Eqn
  q21 = wE 6 W
  q22 : Eqn
  q22 = wE 612 W
  q23 : Eqn
  q23 = wE 39 W
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q26 : Eqn
  q26 = eqn (ℓ "丈乌") (ℓ "乌丈") (low₁-comm (S) ((CX₀₁ ↑)))
  q27 : Eqn
  q27 = wE 613 W
  q28 : Eqn
  q28 = wE 689 W
  q29 : Eqn
  q29 = wE 539 W
  q30 : Eqn
  q30 = wE 153 W
  q31 : Eqn
  q31 = eqn (ℓ "乃丛") (ℓ "丛乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q32 : Eqn
  q32 = wE 541 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];2,0->1) passes white iX via V2 conjugates 3 part2: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2 : ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠乏丠丠丠丠丷么丷丷乏乃丠丠两丠两两丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘丶丶乇丶乇乇举举乏乏丼丳丼乏丷乏举举举丛乕举举举两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part2 = derive (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠乏丠丠丠丠丷么丷丷乏乃丠丠两丠两两丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘丶丶乇丶乇乇举举乏乏丼丳丼乏丷乏举举举丛乕举举举两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乌丘丘丷么丷丷丘丘丷丷丷丘")
  (rw 52 q1 ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   rw 49 q3 ∷
   rw 48 q1 ∷
   rw 47 q1 ∷
   rw 46 q1 ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q2 ∷
   rw 42 q3 ∷
   rw 43 q4 ∷
   rw 44 q5 ∷
   re 42 3 (ℓ "举") ∷
   rw 45 q5 ∷
   re 43 3 (ℓ "乕") ∷
   rw 46 q5 ∷
   re 44 3 (ℓ "举") ∷
   rw 47 q5 ∷
   re 45 3 (ℓ "举") ∷
   rw⁻ 46 q3 ∷
   rw⁻ 47 q2 ∷
   rw⁻ 48 q3 ∷
   rw⁻ 49 q2 ∷
   rw⁻ 50 q1 ∷
   rw⁻ 51 q1 ∷
   rw⁻ 52 q1 ∷
   rw⁻ 53 q3 ∷
   rw⁻ 54 q2 ∷
   rw⁻ 55 q1 ∷
   rw⁻ 56 q1 ∷
   rw⁻ 57 q1 ∷
   rw⁻ 58 q1 ∷
   rw⁻ 59 q1 ∷
   rw⁻ 60 q1 ∷
   rw 61 q6 ∷
   re 42 1 (ℓ "乏丷乏") ∷
   rw 41 q5 ∷
   re 42 3 (ℓ "乐") ∷
   re 42 1 (ℓ "乏丼丳丼乏") ∷
   rw 48 q5 ∷
   re 46 3 (ℓ "举") ∷
   rw 45 q7 ∷
   rw 44 q8 ∷
   rw 43 q9 ∷
   re 43 1 (ℓ "乏丷乏") ∷
   rw 42 q6 ∷
   re 43 5 (ℓ "乐") ∷
   re 43 1 (ℓ "乏乃乏") ∷
   rw 45 q6 ∷
   re 41 3 (ℓ "举") ∷
   re 43 1 (ℓ "乏么乏") ∷
   rw 42 q5 ∷
   re 43 3 (ℓ "乐") ∷
   re 43 1 (ℓ "乏丼丳丼乏") ∷
   rw 49 q5 ∷
   re 47 3 (ℓ "乕") ∷
   rw 46 q10 ∷
   rw 45 q11 ∷
   rw 44 q12 ∷
   re 44 1 (ℓ "乏么乏") ∷
   rw 43 q6 ∷
   re 44 5 (ℓ "乐") ∷
   re 44 1 (ℓ "乏乃乏") ∷
   rw 46 q6 ∷
   re 42 3 (ℓ "乕") ∷
   re 44 1 (ℓ "乏丷乏") ∷
   rw 43 q5 ∷
   re 44 3 (ℓ "乐") ∷
   re 44 1 (ℓ "乏丼丳丼乏") ∷
   rw 50 q5 ∷
   re 48 3 (ℓ "举") ∷
   rw 47 q7 ∷
   rw 46 q8 ∷
   rw 45 q9 ∷
   re 45 1 (ℓ "乏丷乏") ∷
   rw 44 q6 ∷
   re 45 5 (ℓ "乐") ∷
   re 45 1 (ℓ "乏乃乏") ∷
   rw 47 q6 ∷
   re 43 3 (ℓ "举") ∷
   re 45 1 (ℓ "乏丷乏") ∷
   rw 44 q5 ∷
   re 45 3 (ℓ "乐") ∷
   re 45 1 (ℓ "乏丼丳丼乏") ∷
   rw 51 q5 ∷
   re 49 3 (ℓ "举") ∷
   rw 48 q7 ∷
   rw 47 q8 ∷
   rw 46 q9 ∷
   re 46 1 (ℓ "乏丷乏") ∷
   rw 45 q6 ∷
   re 46 5 (ℓ "乐") ∷
   re 46 1 (ℓ "乏乃乏") ∷
   rw 48 q6 ∷
   re 44 3 (ℓ "举") ∷
   rw 35 q13 ∷
   rw 67 q14 ∷
   rw 68 q15 ∷
   rw 69 q14 ∷
   rw 66 q14 ∷
   rw 67 q15 ∷
   rw 68 q14 ∷
   rw 65 q16 ∷
   rw 66 q17 ∷
   rw 67 q16 ∷
   rw 64 q14 ∷
   rw 65 q15 ∷
   rw 66 q14 ∷
   rw 63 q16 ∷
   rw 64 q17 ∷
   rw 65 q16 ∷
   rw 62 q16 ∷
   rw 63 q17 ∷
   rw 64 q16 ∷
   rw 65 q18 ∷
   rw⁻ 64 q19 ∷
   rw⁻ 63 q20 ∷
   rw⁻ 62 q19 ∷
   rw 61 q21 ∷
   rw 62 q22 ∷
   rw 61 q19 ∷
   rw 62 q20 ∷
   rw 63 q19 ∷
   rw 64 q23 ∷
   rw 65 q24 ∷
   rw 60 q16 ∷
   rw 61 q17 ∷
   rw 62 q16 ∷
   rw 59 q16 ∷
   rw 60 q17 ∷
   rw 61 q16 ∷
   rw 58 q16 ∷
   rw 59 q17 ∷
   rw 60 q16 ∷
   rw 57 q16 ∷
   rw 58 q17 ∷
   rw 59 q16 ∷
   rw 56 q16 ∷
   rw 57 q17 ∷
   rw 58 q16 ∷
   rw 55 q16 ∷
   rw 56 q17 ∷
   rw 57 q16 ∷
   rw 54 q25 ∷
   rw 55 q26 ∷
   rw 56 q25 ∷
   rw 53 q14 ∷
   rw 54 q15 ∷
   rw 55 q14 ∷
   rw 52 q16 ∷
   rw 53 q17 ∷
   rw 54 q16 ∷
   rw 51 q16 ∷
   rw 52 q17 ∷
   rw 53 q16 ∷
   rw 50 q16 ∷
   rw 51 q17 ∷
   rw 52 q16 ∷
   rw 49 q25 ∷
   rw 50 q26 ∷
   rw 51 q25 ∷
   rw 48 q14 ∷
   rw 49 q15 ∷
   rw 50 q14 ∷
   rw 47 q25 ∷
   rw 48 q26 ∷
   rw 49 q25 ∷
   rw 46 q14 ∷
   rw 47 q15 ∷
   rw 48 q14 ∷
   rw 49 q18 ∷
   rw⁻ 48 q19 ∷
   rw⁻ 47 q20 ∷
   rw⁻ 46 q19 ∷
   rw 45 q21 ∷
   rw 46 q22 ∷
   rw 45 q19 ∷
   rw 46 q20 ∷
   rw 47 q19 ∷
   rw 48 q23 ∷
   rw 49 q24 ∷
   rw 39 q27 ∷
   rw 82 q5 ∷
   re 81 1 (ℓ "乏丷乏") ∷
   rw 83 q6 ∷
   re 80 1 (ℓ "乏丷乏") ∷
   rw 82 q6 ∷
   re 79 1 (ℓ "乏丷乏") ∷
   rw 81 q6 ∷
   re 78 1 (ℓ "乏么乏") ∷
   rw 80 q6 ∷
   rw 77 q28 ∷
   re 76 1 (ℓ "乏丷乏") ∷
   rw 78 q6 ∷
   re 75 1 (ℓ "乏丷乏") ∷
   rw 77 q6 ∷
   re 74 1 (ℓ "乏丷乏") ∷
   rw 76 q6 ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 75 q6 ∷
   re 72 1 (ℓ "乏丷乏") ∷
   rw 74 q6 ∷
   re 71 1 (ℓ "乏丷乏") ∷
   rw 73 q6 ∷
   rw 70 q3 ∷
   rw 69 q3 ∷
   rw 68 q1 ∷
   rw 67 q3 ∷
   rw 66 q1 ∷
   rw 65 q1 ∷
   rw 66 q29 ∷
   rw 67 q5 ∷
   re 65 3 (ℓ "举") ∷
   rw 68 q5 ∷
   re 66 3 (ℓ "举") ∷
   rw 69 q5 ∷
   re 67 3 (ℓ "举") ∷
   rw 70 q5 ∷
   re 68 3 (ℓ "举") ∷
   rw 71 q5 ∷
   re 69 3 (ℓ "举") ∷
   rw 72 q5 ∷
   re 70 3 (ℓ "举") ∷
   rw 71 q30 ∷
   rw 74 q5 ∷
   re 72 3 (ℓ "乕") ∷
   rw 75 q5 ∷
   re 73 3 (ℓ "举") ∷
   rw 76 q5 ∷
   re 74 3 (ℓ "举") ∷
   rw 77 q5 ∷
   re 75 3 (ℓ "举") ∷
   rw⁻ 76 q1 ∷
   rw⁻ 77 q1 ∷
   rw⁻ 78 q3 ∷
   rw⁻ 79 q1 ∷
   rw⁻ 80 q3 ∷
   rw⁻ 81 q3 ∷
   rw 82 q6 ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q5 ∷
   re 65 3 (ℓ "乐") ∷
   re 65 1 (ℓ "乏丼丳丼乏") ∷
   rw 71 q5 ∷
   re 69 3 (ℓ "举") ∷
   rw 68 q7 ∷
   rw 67 q8 ∷
   rw 66 q9 ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q6 ∷
   re 66 5 (ℓ "乐") ∷
   re 66 1 (ℓ "乏乃乏") ∷
   rw 68 q6 ∷
   re 64 3 (ℓ "举") ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q5 ∷
   re 66 3 (ℓ "乐") ∷
   re 66 1 (ℓ "乏丼丳丼乏") ∷
   rw 72 q5 ∷
   re 70 3 (ℓ "举") ∷
   rw 69 q7 ∷
   rw 68 q8 ∷
   rw 67 q9 ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 66 q6 ∷
   re 67 5 (ℓ "乐") ∷
   re 67 1 (ℓ "乏乃乏") ∷
   rw 69 q6 ∷
   re 65 3 (ℓ "举") ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 66 q5 ∷
   re 67 3 (ℓ "乐") ∷
   re 67 1 (ℓ "乏丼丳丼乏") ∷
   rw 73 q5 ∷
   re 71 3 (ℓ "举") ∷
   rw 70 q7 ∷
   rw 69 q8 ∷
   rw 68 q9 ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 67 q6 ∷
   re 68 5 (ℓ "乐") ∷
   re 68 1 (ℓ "乏乃乏") ∷
   rw 70 q6 ∷
   re 66 3 (ℓ "举") ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 67 q5 ∷
   re 68 3 (ℓ "乐") ∷
   re 68 1 (ℓ "乏丼丳丼乏") ∷
   rw 74 q5 ∷
   re 72 3 (ℓ "举") ∷
   rw 71 q7 ∷
   rw 70 q8 ∷
   rw 69 q9 ∷
   re 69 1 (ℓ "乏丷乏") ∷
   rw 68 q6 ∷
   re 69 5 (ℓ "乐") ∷
   re 69 1 (ℓ "乏乃乏") ∷
   rw 71 q6 ∷
   re 67 3 (ℓ "举") ∷
   re 69 1 (ℓ "乏丷乏") ∷
   rw 68 q5 ∷
   re 69 3 (ℓ "乐") ∷
   re 69 1 (ℓ "乏丼丳丼乏") ∷
   rw 75 q5 ∷
   re 73 3 (ℓ "举") ∷
   rw 72 q7 ∷
   rw 71 q8 ∷
   rw 70 q9 ∷
   re 70 1 (ℓ "乏丷乏") ∷
   rw 69 q6 ∷
   re 70 5 (ℓ "乐") ∷
   re 70 1 (ℓ "乏乃乏") ∷
   rw 72 q6 ∷
   re 68 3 (ℓ "举") ∷
   re 70 1 (ℓ "乏丷乏") ∷
   rw 69 q5 ∷
   re 70 3 (ℓ "乐") ∷
   re 70 1 (ℓ "乏丼丳丼乏") ∷
   rw 76 q5 ∷
   re 74 3 (ℓ "举") ∷
   rw 73 q7 ∷
   rw 72 q8 ∷
   rw 71 q9 ∷
   re 71 1 (ℓ "乏丷乏") ∷
   rw 70 q6 ∷
   re 71 5 (ℓ "乐") ∷
   re 71 1 (ℓ "乏乃乏") ∷
   rw 73 q6 ∷
   re 69 3 (ℓ "举") ∷
   rw 70 q31 ∷
   re 72 1 (ℓ "乏么乏") ∷
   rw 71 q5 ∷
   re 72 3 (ℓ "乐") ∷
   re 72 1 (ℓ "乏丼丳丼乏") ∷
   rw 78 q5 ∷
   re 76 3 (ℓ "乕") ∷
   rw 75 q10 ∷
   rw 74 q11 ∷
   rw 73 q12 ∷
   re 73 1 (ℓ "乏么乏") ∷
   rw 72 q6 ∷
   re 73 5 (ℓ "乐") ∷
   re 73 1 (ℓ "乏乃乏") ∷
   rw 75 q6 ∷
   re 71 3 (ℓ "乕") ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 72 q5 ∷
   re 73 3 (ℓ "乐") ∷
   re 73 1 (ℓ "乏丼丳丼乏") ∷
   rw 79 q5 ∷
   re 77 3 (ℓ "举") ∷
   rw 76 q7 ∷
   rw 75 q8 ∷
   rw 74 q9 ∷
   re 74 1 (ℓ "乏丷乏") ∷
   rw 73 q6 ∷
   re 74 5 (ℓ "乐") ∷
   re 74 1 (ℓ "乏乃乏") ∷
   rw 76 q6 ∷
   re 72 3 (ℓ "举") ∷
   re 74 1 (ℓ "乏丷乏") ∷
   rw 73 q5 ∷
   re 74 3 (ℓ "乐") ∷
   re 74 1 (ℓ "乏丼丳丼乏") ∷
   rw 80 q5 ∷
   re 78 3 (ℓ "举") ∷
   rw 77 q7 ∷
   rw 76 q8 ∷
   rw 75 q9 ∷
   re 75 1 (ℓ "乏丷乏") ∷
   rw 74 q6 ∷
   re 75 5 (ℓ "乐") ∷
   re 75 1 (ℓ "乏乃乏") ∷
   rw 77 q6 ∷
   re 73 3 (ℓ "举") ∷
   re 75 1 (ℓ "乏丷乏") ∷
   rw 74 q5 ∷
   re 75 3 (ℓ "乐") ∷
   re 75 1 (ℓ "乏丼丳丼乏") ∷
   rw 81 q5 ∷
   re 79 3 (ℓ "举") ∷
   rw 78 q7 ∷
   rw 77 q8 ∷
   rw 76 q9 ∷
   re 76 1 (ℓ "乏丷乏") ∷
   rw 75 q6 ∷
   re 76 5 (ℓ "乐") ∷
   re 76 1 (ℓ "乏乃乏") ∷
   rw 78 q6 ∷
   re 74 3 (ℓ "举") ∷
   rw 75 q5 ∷
   re 74 1 (ℓ "乏丷乏") ∷
   rw 76 q6 ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 75 q6 ∷
   re 72 1 (ℓ "乏丷乏") ∷
   rw 74 q6 ∷
   re 71 1 (ℓ "乏么乏") ∷
   rw 73 q6 ∷
   rw 70 q28 ∷
   re 69 1 (ℓ "乏丷乏") ∷
   rw 71 q6 ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 70 q6 ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 69 q6 ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 68 q6 ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 67 q6 ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 66 q6 ∷
   rw 63 q1 ∷
   rw 62 q1 ∷
   rw 61 q1 ∷
   rw 60 q1 ∷
   rw 59 q1 ∷
   rw 58 q1 ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 55 q1 ∷
   rw 54 q1 ∷
   rw 53 q1 ∷
   rw 52 q2 ∷
   rw 51 q3 ∷
   rw 50 q2 ∷
   rw 49 q3 ∷
   rw 50 q32 ∷
   rw 51 q5 ∷
   re 49 3 (ℓ "举") ∷
   rw 52 q5 ∷
   re 50 3 (ℓ "举") ∷
   rw 53 q5 ∷
   re 51 3 (ℓ "举") ∷
   rw 54 q5 ∷
   re 52 3 (ℓ "举") ∷
   rw 55 q5 ∷
   re 53 3 (ℓ "举") ∷
   rw 56 q5 ∷
   re 54 3 (ℓ "举") ∷
   rw 55 q30 ∷
   rw 58 q5 ∷
   re 56 3 (ℓ "乕") ∷
   rw 59 q5 ∷
   re 57 3 (ℓ "举") ∷
   rw 60 q5 ∷
   re 58 3 (ℓ "举") ∷
   rw 61 q5 ∷
   re 59 3 (ℓ "举") ∷
   rw⁻ 60 q3 ∷
   rw⁻ 61 q2 ∷
   rw⁻ 62 q3 ∷
   rw⁻ 63 q2 ∷
   rw⁻ 64 q1 ∷
   rw⁻ 65 q1 ∷
   rw⁻ 66 q1 ∷
   rw⁻ 67 q3 ∷
   rw⁻ 68 q2 ∷
   rw⁻ 69 q1 ∷
   rw⁻ 70 q1 ∷
   rw⁻ 71 q1 ∷
   rw⁻ 72 q1 ∷
   rw⁻ 73 q1 ∷
   rw⁻ 74 q1 ∷
   rw 75 q6 ∷
   re 49 1 (ℓ "乏丷乏") ∷
   rw 48 q5 ∷
   re 49 3 (ℓ "乐") ∷
   re 49 1 (ℓ "乏丼丳丼乏") ∷
   rw 55 q5 ∷
   re 53 3 (ℓ "举") ∷
   rw 52 q7 ∷
   rw 51 q8 ∷
   rw 50 q9 ∷
   re 50 1 (ℓ "乏丷乏") ∷
   rw 49 q6 ∷
   re 50 5 (ℓ "乐") ∷
   re 50 1 (ℓ "乏乃乏") ∷
   rw 52 q6 ∷
   re 48 3 (ℓ "举") ∷
   re 50 1 (ℓ "乏丷乏") ∷
   rw 49 q5 ∷
   re 50 3 (ℓ "乐") ∷
   re 50 1 (ℓ "乏丼丳丼乏") ∷
   rw 56 q5 ∷
   re 54 3 (ℓ "举") ∷
   rw 53 q7 ∷
   rw 52 q8 ∷
   rw 51 q9 ∷
   re 51 1 (ℓ "乏丷乏") ∷
   rw 50 q6 ∷
   re 51 5 (ℓ "乐") ∷
   re 51 1 (ℓ "乏乃乏") ∷
   rw 53 q6 ∷
   re 49 3 (ℓ "举") ∷
   re 51 1 (ℓ "乏丷乏") ∷
   rw 50 q5 ∷
   re 51 3 (ℓ "乐") ∷
   re 51 1 (ℓ "乏丼丳丼乏") ∷ []) Eq.refl
