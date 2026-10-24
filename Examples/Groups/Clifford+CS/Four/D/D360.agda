{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D360 (W : Ws) where

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
  q4 = wE 974 W
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
  q13 = wE 975 W
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
  q28 = wE 689 W
  q29 : Eqn
  q29 = wE 541 W
  q30 : Eqn
  q30 = wE 153 W
  q31 : Eqn
  q31 = eqn (ℓ "乃丛") (ℓ "丛乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];2,0->1) passes white iX via V2 conjugates 3 part3: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part3 : ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠乏丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈丷么丷丷乏乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈举举举举举举丛乏乐么乏举举举两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part3 = derive (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠乏丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈丷么丷丷乏乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈举举举举举举丛乏乐么乏举举举两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘丘丷么丷丷丘丘丷丷丷丘")
  (rw 74 q1 ∷
   rw 73 q2 ∷
   rw 72 q3 ∷
   rw 71 q2 ∷
   rw 70 q2 ∷
   rw 69 q2 ∷
   rw 68 q1 ∷
   rw 67 q1 ∷
   rw 66 q1 ∷
   rw 65 q1 ∷
   rw 64 q1 ∷
   rw 63 q1 ∷
   rw 62 q1 ∷
   rw 61 q1 ∷
   rw 60 q1 ∷
   rw 59 q1 ∷
   rw 58 q1 ∷
   rw 57 q1 ∷
   rw 56 q1 ∷
   rw 55 q1 ∷
   rw 54 q1 ∷
   rw 53 q1 ∷
   rw 52 q1 ∷
   rw 51 q1 ∷
   rw 52 q4 ∷
   rw 53 q5 ∷
   re 51 3 (ℓ "举") ∷
   rw 54 q5 ∷
   re 52 3 (ℓ "乕") ∷
   rw 55 q5 ∷
   re 53 3 (ℓ "举") ∷
   rw 56 q5 ∷
   re 54 3 (ℓ "举") ∷
   rw⁻ 55 q1 ∷
   rw⁻ 56 q1 ∷
   rw⁻ 57 q1 ∷
   rw⁻ 58 q1 ∷
   rw⁻ 59 q1 ∷
   rw⁻ 60 q1 ∷
   rw⁻ 61 q1 ∷
   rw⁻ 62 q1 ∷
   rw⁻ 63 q1 ∷
   rw⁻ 64 q1 ∷
   rw⁻ 65 q1 ∷
   rw⁻ 66 q1 ∷
   rw⁻ 67 q1 ∷
   rw⁻ 68 q1 ∷
   rw⁻ 69 q1 ∷
   rw⁻ 70 q1 ∷
   rw⁻ 71 q1 ∷
   rw⁻ 72 q1 ∷
   rw⁻ 73 q2 ∷
   rw⁻ 74 q2 ∷
   rw⁻ 75 q2 ∷
   rw⁻ 76 q3 ∷
   rw⁻ 77 q2 ∷
   rw⁻ 78 q1 ∷
   rw⁻ 79 q1 ∷
   rw⁻ 80 q1 ∷
   rw⁻ 81 q1 ∷
   rw⁻ 82 q1 ∷
   rw⁻ 83 q1 ∷
   rw⁻ 84 q1 ∷
   rw⁻ 85 q1 ∷
   rw⁻ 86 q1 ∷
   rw⁻ 87 q2 ∷
   rw⁻ 88 q2 ∷
   rw⁻ 89 q2 ∷
   rw⁻ 90 q3 ∷
   rw⁻ 91 q2 ∷
   rw⁻ 92 q2 ∷
   rw⁻ 93 q2 ∷
   rw⁻ 94 q2 ∷
   rw⁻ 95 q3 ∷
   rw⁻ 96 q2 ∷
   rw 97 q6 ∷
   re 51 1 (ℓ "乏丷乏") ∷
   rw 50 q5 ∷
   re 51 3 (ℓ "乐") ∷
   re 51 1 (ℓ "乏丼丳丼乏") ∷
   rw 57 q5 ∷
   re 55 3 (ℓ "举") ∷
   rw 54 q7 ∷
   rw 53 q8 ∷
   rw 52 q9 ∷
   re 52 1 (ℓ "乏丷乏") ∷
   rw 51 q6 ∷
   re 52 5 (ℓ "乐") ∷
   re 52 1 (ℓ "乏乃乏") ∷
   rw 54 q6 ∷
   re 50 3 (ℓ "举") ∷
   re 52 1 (ℓ "乏么乏") ∷
   rw 51 q5 ∷
   re 52 3 (ℓ "乐") ∷
   re 52 1 (ℓ "乏丼丳丼乏") ∷
   rw 58 q5 ∷
   re 56 3 (ℓ "乕") ∷
   rw 55 q10 ∷
   rw 54 q11 ∷
   rw 53 q12 ∷
   re 53 1 (ℓ "乏么乏") ∷
   rw 52 q6 ∷
   re 53 5 (ℓ "乐") ∷
   re 53 1 (ℓ "乏乃乏") ∷
   rw 55 q6 ∷
   re 51 3 (ℓ "乕") ∷
   re 53 1 (ℓ "乏丷乏") ∷
   rw 52 q5 ∷
   re 53 3 (ℓ "乐") ∷
   re 53 1 (ℓ "乏丼丳丼乏") ∷
   rw 59 q5 ∷
   re 57 3 (ℓ "举") ∷
   rw 56 q7 ∷
   rw 55 q8 ∷
   rw 54 q9 ∷
   re 54 1 (ℓ "乏丷乏") ∷
   rw 53 q6 ∷
   re 54 5 (ℓ "乐") ∷
   re 54 1 (ℓ "乏乃乏") ∷
   rw 56 q6 ∷
   re 52 3 (ℓ "举") ∷
   re 54 1 (ℓ "乏丷乏") ∷
   rw 53 q5 ∷
   re 54 3 (ℓ "乐") ∷
   re 54 1 (ℓ "乏丼丳丼乏") ∷
   rw 60 q5 ∷
   re 58 3 (ℓ "举") ∷
   rw 57 q7 ∷
   rw 56 q8 ∷
   rw 55 q9 ∷
   re 55 1 (ℓ "乏丷乏") ∷
   rw 54 q6 ∷
   re 55 5 (ℓ "乐") ∷
   re 55 1 (ℓ "乏乃乏") ∷
   rw 57 q6 ∷
   re 53 3 (ℓ "举") ∷
   rw 35 q13 ∷
   rw 112 q14 ∷
   rw 113 q15 ∷
   rw 114 q14 ∷
   rw 111 q14 ∷
   rw 112 q15 ∷
   rw 113 q14 ∷
   rw 110 q14 ∷
   rw 111 q15 ∷
   rw 112 q14 ∷
   rw 109 q14 ∷
   rw 110 q15 ∷
   rw 111 q14 ∷
   rw 108 q14 ∷
   rw 109 q15 ∷
   rw 110 q14 ∷
   rw 107 q14 ∷
   rw 108 q15 ∷
   rw 109 q14 ∷
   rw 106 q16 ∷
   rw 107 q17 ∷
   rw 108 q16 ∷
   rw 105 q18 ∷
   rw 106 q19 ∷
   rw 107 q18 ∷
   rw 104 q14 ∷
   rw 105 q15 ∷
   rw 106 q14 ∷
   rw 103 q14 ∷
   rw 104 q15 ∷
   rw 105 q14 ∷
   rw 102 q14 ∷
   rw 103 q15 ∷
   rw 104 q14 ∷
   rw 101 q16 ∷
   rw 102 q17 ∷
   rw 103 q16 ∷
   rw 100 q18 ∷
   rw 101 q19 ∷
   rw 102 q18 ∷
   rw 99 q16 ∷
   rw 100 q17 ∷
   rw 101 q16 ∷
   rw 98 q18 ∷
   rw 99 q19 ∷
   rw 100 q18 ∷
   rw 101 q20 ∷
   rw⁻ 100 q21 ∷
   rw⁻ 99 q22 ∷
   rw⁻ 98 q21 ∷
   rw 97 q23 ∷
   rw 98 q24 ∷
   rw 97 q21 ∷
   rw 98 q22 ∷
   rw 99 q21 ∷
   rw 100 q25 ∷
   rw 101 q26 ∷
   rw 96 q16 ∷
   rw 97 q17 ∷
   rw 98 q16 ∷
   rw 95 q18 ∷
   rw 96 q19 ∷
   rw 97 q18 ∷
   rw 94 q16 ∷
   rw 95 q17 ∷
   rw 96 q16 ∷
   rw 93 q16 ∷
   rw 94 q17 ∷
   rw 95 q16 ∷
   rw 92 q16 ∷
   rw 93 q17 ∷
   rw 94 q16 ∷
   rw 91 q16 ∷
   rw 92 q17 ∷
   rw 93 q16 ∷
   rw 90 q18 ∷
   rw 91 q19 ∷
   rw 92 q18 ∷
   rw 89 q16 ∷
   rw 90 q17 ∷
   rw 91 q16 ∷
   rw 88 q16 ∷
   rw 89 q17 ∷
   rw 90 q16 ∷
   rw 87 q16 ∷
   rw 88 q17 ∷
   rw 89 q16 ∷
   rw 86 q14 ∷
   rw 87 q15 ∷
   rw 88 q14 ∷
   rw 85 q14 ∷
   rw 86 q15 ∷
   rw 87 q14 ∷
   rw 84 q14 ∷
   rw 85 q15 ∷
   rw 86 q14 ∷
   rw 83 q14 ∷
   rw 84 q15 ∷
   rw 85 q14 ∷
   rw 82 q14 ∷
   rw 83 q15 ∷
   rw 84 q14 ∷
   rw 81 q14 ∷
   rw 82 q15 ∷
   rw 83 q14 ∷
   rw 80 q14 ∷
   rw 81 q15 ∷
   rw 82 q14 ∷
   rw 79 q14 ∷
   rw 80 q15 ∷
   rw 81 q14 ∷
   rw 78 q14 ∷
   rw 79 q15 ∷
   rw 80 q14 ∷
   rw 77 q16 ∷
   rw 78 q17 ∷
   rw 79 q16 ∷
   rw 76 q18 ∷
   rw 77 q19 ∷
   rw 78 q18 ∷
   rw 75 q16 ∷
   rw 76 q17 ∷
   rw 77 q16 ∷
   rw 74 q16 ∷
   rw 75 q17 ∷
   rw 76 q16 ∷
   rw 73 q16 ∷
   rw 74 q17 ∷
   rw 75 q16 ∷
   rw 72 q14 ∷
   rw 73 q15 ∷
   rw 74 q14 ∷
   rw 71 q14 ∷
   rw 72 q15 ∷
   rw 73 q14 ∷
   rw 70 q14 ∷
   rw 71 q15 ∷
   rw 72 q14 ∷
   rw 69 q14 ∷
   rw 70 q15 ∷
   rw 71 q14 ∷
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
   rw 59 q14 ∷
   rw 60 q15 ∷
   rw 61 q14 ∷
   rw 58 q14 ∷
   rw 59 q15 ∷
   rw 60 q14 ∷
   rw 57 q14 ∷
   rw 58 q15 ∷
   rw 59 q14 ∷
   rw 56 q14 ∷
   rw 57 q15 ∷
   rw 58 q14 ∷
   rw 55 q14 ∷
   rw 56 q15 ∷
   rw 57 q14 ∷
   rw 58 q20 ∷
   rw⁻ 57 q21 ∷
   rw⁻ 56 q22 ∷
   rw⁻ 55 q21 ∷
   rw 54 q23 ∷
   rw 55 q24 ∷
   rw 54 q21 ∷
   rw 55 q22 ∷
   rw 56 q21 ∷
   rw 57 q25 ∷
   rw 58 q26 ∷
   rw 39 q27 ∷
   rw 127 q5 ∷
   re 126 1 (ℓ "乏丷乏") ∷
   rw 128 q6 ∷
   re 125 1 (ℓ "乏丷乏") ∷
   rw 127 q6 ∷
   re 124 1 (ℓ "乏丷乏") ∷
   rw 126 q6 ∷
   re 123 1 (ℓ "乏么乏") ∷
   rw 125 q6 ∷
   rw 122 q28 ∷
   re 121 1 (ℓ "乏丷乏") ∷
   rw 123 q6 ∷
   re 120 1 (ℓ "乏丷乏") ∷
   rw 122 q6 ∷
   re 119 1 (ℓ "乏丷乏") ∷
   rw 121 q6 ∷
   re 118 1 (ℓ "乏丷乏") ∷
   rw 120 q6 ∷
   re 117 1 (ℓ "乏丷乏") ∷
   rw 119 q6 ∷
   re 116 1 (ℓ "乏丷乏") ∷
   rw 118 q6 ∷
   rw 115 q1 ∷
   rw 114 q1 ∷
   rw 113 q1 ∷
   rw 112 q1 ∷
   rw 111 q1 ∷
   rw 110 q1 ∷
   rw 109 q2 ∷
   rw 108 q3 ∷
   rw 107 q1 ∷
   rw 106 q1 ∷
   rw 105 q1 ∷
   rw 104 q2 ∷
   rw 103 q3 ∷
   rw 102 q2 ∷
   rw 101 q3 ∷
   rw 102 q29 ∷
   rw 103 q5 ∷
   re 101 3 (ℓ "举") ∷
   rw 104 q5 ∷
   re 102 3 (ℓ "举") ∷
   rw 105 q5 ∷
   re 103 3 (ℓ "举") ∷
   rw 106 q5 ∷
   re 104 3 (ℓ "举") ∷
   rw 107 q5 ∷
   re 105 3 (ℓ "举") ∷
   rw 108 q5 ∷
   re 106 3 (ℓ "举") ∷
   rw 107 q30 ∷
   rw 110 q5 ∷
   re 108 3 (ℓ "乕") ∷
   rw 111 q5 ∷
   re 109 3 (ℓ "举") ∷
   rw 112 q5 ∷
   re 110 3 (ℓ "举") ∷
   rw 113 q5 ∷
   re 111 3 (ℓ "举") ∷
   rw⁻ 112 q3 ∷
   rw⁻ 113 q2 ∷
   rw⁻ 114 q3 ∷
   rw⁻ 115 q2 ∷
   rw⁻ 116 q1 ∷
   rw⁻ 117 q1 ∷
   rw⁻ 118 q1 ∷
   rw⁻ 119 q3 ∷
   rw⁻ 120 q2 ∷
   rw⁻ 121 q1 ∷
   rw⁻ 122 q1 ∷
   rw⁻ 123 q1 ∷
   rw⁻ 124 q1 ∷
   rw⁻ 125 q1 ∷
   rw⁻ 126 q1 ∷
   rw 127 q6 ∷
   re 101 1 (ℓ "乏丷乏") ∷
   rw 100 q5 ∷
   re 101 3 (ℓ "乐") ∷
   re 101 1 (ℓ "乏丼丳丼乏") ∷
   rw 107 q5 ∷
   re 105 3 (ℓ "举") ∷
   rw 104 q7 ∷
   rw 103 q8 ∷
   rw 102 q9 ∷
   re 102 1 (ℓ "乏丷乏") ∷
   rw 101 q6 ∷
   re 102 5 (ℓ "乐") ∷
   re 102 1 (ℓ "乏乃乏") ∷
   rw 104 q6 ∷
   re 100 3 (ℓ "举") ∷
   re 102 1 (ℓ "乏丷乏") ∷
   rw 101 q5 ∷
   re 102 3 (ℓ "乐") ∷
   re 102 1 (ℓ "乏丼丳丼乏") ∷
   rw 108 q5 ∷
   re 106 3 (ℓ "举") ∷
   rw 105 q7 ∷
   rw 104 q8 ∷
   rw 103 q9 ∷
   re 103 1 (ℓ "乏丷乏") ∷
   rw 102 q6 ∷
   re 103 5 (ℓ "乐") ∷
   re 103 1 (ℓ "乏乃乏") ∷
   rw 105 q6 ∷
   re 101 3 (ℓ "举") ∷
   re 103 1 (ℓ "乏丷乏") ∷
   rw 102 q5 ∷
   re 103 3 (ℓ "乐") ∷
   re 103 1 (ℓ "乏丼丳丼乏") ∷
   rw 109 q5 ∷
   re 107 3 (ℓ "举") ∷
   rw 106 q7 ∷
   rw 105 q8 ∷
   rw 104 q9 ∷
   re 104 1 (ℓ "乏丷乏") ∷
   rw 103 q6 ∷
   re 104 5 (ℓ "乐") ∷
   re 104 1 (ℓ "乏乃乏") ∷
   rw 106 q6 ∷
   re 102 3 (ℓ "举") ∷
   re 104 1 (ℓ "乏丷乏") ∷
   rw 103 q5 ∷
   re 104 3 (ℓ "乐") ∷
   re 104 1 (ℓ "乏丼丳丼乏") ∷
   rw 110 q5 ∷
   re 108 3 (ℓ "举") ∷
   rw 107 q7 ∷
   rw 106 q8 ∷
   rw 105 q9 ∷
   re 105 1 (ℓ "乏丷乏") ∷
   rw 104 q6 ∷
   re 105 5 (ℓ "乐") ∷
   re 105 1 (ℓ "乏乃乏") ∷
   rw 107 q6 ∷
   re 103 3 (ℓ "举") ∷
   re 105 1 (ℓ "乏丷乏") ∷
   rw 104 q5 ∷
   re 105 3 (ℓ "乐") ∷
   re 105 1 (ℓ "乏丼丳丼乏") ∷
   rw 111 q5 ∷
   re 109 3 (ℓ "举") ∷
   rw 108 q7 ∷
   rw 107 q8 ∷
   rw 106 q9 ∷
   re 106 1 (ℓ "乏丷乏") ∷
   rw 105 q6 ∷
   re 106 5 (ℓ "乐") ∷
   re 106 1 (ℓ "乏乃乏") ∷
   rw 108 q6 ∷
   re 104 3 (ℓ "举") ∷
   re 106 1 (ℓ "乏丷乏") ∷
   rw 105 q5 ∷
   re 106 3 (ℓ "乐") ∷
   re 106 1 (ℓ "乏丼丳丼乏") ∷
   rw 112 q5 ∷
   re 110 3 (ℓ "举") ∷
   rw 109 q7 ∷
   rw 108 q8 ∷
   rw 107 q9 ∷
   re 107 1 (ℓ "乏丷乏") ∷
   rw 106 q6 ∷
   re 107 5 (ℓ "乐") ∷
   re 107 1 (ℓ "乏乃乏") ∷
   rw 109 q6 ∷
   re 105 3 (ℓ "举") ∷
   rw 106 q31 ∷
   re 108 1 (ℓ "乏么乏") ∷
   rw 107 q5 ∷
   re 108 3 (ℓ "乐") ∷ []) Eq.refl
