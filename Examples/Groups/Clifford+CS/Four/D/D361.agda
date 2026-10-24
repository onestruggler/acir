{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D361 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 360 W
  q3 : Eqn
  q3 = eqn (ℓ "丳乘") (ℓ "乘丳") (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q4 : Eqn
  q4 = wE 362 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 21 W
  q7 : Eqn
  q7 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 51 W
  q9 : Eqn
  q9 = wE 689 W
  q10 : Eqn
  q10 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q11 : Eqn
  q11 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q12 : Eqn
  q12 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q13 : Eqn
  q13 = wE 977 W
  q14 : Eqn
  q14 = wE 153 W
  q15 : Eqn
  q15 = eqn (ℓ "乃丛") (ℓ "丛乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q16 : Eqn
  q16 = wE 978 W
  q17 : Eqn
  q17 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q18 : Eqn
  q18 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q19 : Eqn
  q19 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q20 : Eqn
  q20 = eqn (ℓ "丈乌") (ℓ "乌丈") (low₁-comm (S) ((CX₀₁ ↑)))
  q21 : Eqn
  q21 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q22 : Eqn
  q22 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))
  q23 : Eqn
  q23 = wE 5 W
  q24 : Eqn
  q24 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q25 : Eqn
  q25 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q26 : Eqn
  q26 = wE 6 W
  q27 : Eqn
  q27 = wE 612 W
  q28 : Eqn
  q28 = wE 39 W
  q29 : Eqn
  q29 = wE 31 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];2,0->1) passes white iX via V2 conjugates 3 part4: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part4 : ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈举举举举举举丛乏乐么乏举举举两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丘丠乌丘丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part4 = derive (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈举举举举举举丛乏乐么乏举举举两丈两丈丠丠丠两丈丠丠丠丠丠丠丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举乇且乇且丶丶丶乇且丶丶丶丶丶丶乃丠丠丠丠丠丠丘丠乌丘丠丠丠丠丠丠丠丠丠丠丠丈丈丈两丈丠丠丠丠丠丠丠丠丠丈丈丈两丈丈丈丈两丈乃两丈两丈丠丠丠两丈丠丠丠丠丠丠丘丷么丷丷丘丘丷丷丷丘")
  (re 108 1 (ℓ "乏丼丳丼乏") ∷
   rw 114 q1 ∷
   re 112 3 (ℓ "乕") ∷
   rw 111 q2 ∷
   rw 110 q3 ∷
   rw 109 q4 ∷
   re 109 1 (ℓ "乏么乏") ∷
   rw 108 q5 ∷
   re 109 5 (ℓ "乐") ∷
   re 109 1 (ℓ "乏乃乏") ∷
   rw 111 q5 ∷
   re 107 3 (ℓ "乕") ∷
   re 109 1 (ℓ "乏丷乏") ∷
   rw 108 q1 ∷
   re 109 3 (ℓ "乐") ∷
   re 109 1 (ℓ "乏丼丳丼乏") ∷
   rw 115 q1 ∷
   re 113 3 (ℓ "举") ∷
   rw 112 q6 ∷
   rw 111 q7 ∷
   rw 110 q8 ∷
   re 110 1 (ℓ "乏丷乏") ∷
   rw 109 q5 ∷
   re 110 5 (ℓ "乐") ∷
   re 110 1 (ℓ "乏乃乏") ∷
   rw 112 q5 ∷
   re 108 3 (ℓ "举") ∷
   re 110 1 (ℓ "乏丷乏") ∷
   rw 109 q1 ∷
   re 110 3 (ℓ "乐") ∷
   re 110 1 (ℓ "乏丼丳丼乏") ∷
   rw 116 q1 ∷
   re 114 3 (ℓ "举") ∷
   rw 113 q6 ∷
   rw 112 q7 ∷
   rw 111 q8 ∷
   re 111 1 (ℓ "乏丷乏") ∷
   rw 110 q5 ∷
   re 111 5 (ℓ "乐") ∷
   re 111 1 (ℓ "乏乃乏") ∷
   rw 113 q5 ∷
   re 109 3 (ℓ "举") ∷
   re 111 1 (ℓ "乏丷乏") ∷
   rw 110 q1 ∷
   re 111 3 (ℓ "乐") ∷
   re 111 1 (ℓ "乏丼丳丼乏") ∷
   rw 117 q1 ∷
   re 115 3 (ℓ "举") ∷
   rw 114 q6 ∷
   rw 113 q7 ∷
   rw 112 q8 ∷
   re 112 1 (ℓ "乏丷乏") ∷
   rw 111 q5 ∷
   re 112 5 (ℓ "乐") ∷
   re 112 1 (ℓ "乏乃乏") ∷
   rw 114 q5 ∷
   re 110 3 (ℓ "举") ∷
   rw 111 q1 ∷
   re 110 1 (ℓ "乏丷乏") ∷
   rw 112 q5 ∷
   re 109 1 (ℓ "乏丷乏") ∷
   rw 111 q5 ∷
   re 108 1 (ℓ "乏丷乏") ∷
   rw 110 q5 ∷
   re 107 1 (ℓ "乏么乏") ∷
   rw 109 q5 ∷
   rw 106 q9 ∷
   re 105 1 (ℓ "乏丷乏") ∷
   rw 107 q5 ∷
   re 104 1 (ℓ "乏丷乏") ∷
   rw 106 q5 ∷
   re 103 1 (ℓ "乏丷乏") ∷
   rw 105 q5 ∷
   re 102 1 (ℓ "乏丷乏") ∷
   rw 104 q5 ∷
   re 101 1 (ℓ "乏丷乏") ∷
   rw 103 q5 ∷
   re 100 1 (ℓ "乏丷乏") ∷
   rw 102 q5 ∷
   rw 99 q10 ∷
   rw 98 q11 ∷
   rw 97 q10 ∷
   rw 96 q10 ∷
   rw 95 q10 ∷
   rw 94 q10 ∷
   rw 93 q11 ∷
   rw 92 q10 ∷
   rw 91 q10 ∷
   rw 90 q10 ∷
   rw 89 q12 ∷
   rw 88 q12 ∷
   rw 87 q12 ∷
   rw 86 q12 ∷
   rw 85 q12 ∷
   rw 84 q12 ∷
   rw 83 q12 ∷
   rw 82 q12 ∷
   rw 81 q12 ∷
   rw 80 q10 ∷
   rw 79 q11 ∷
   rw 78 q10 ∷
   rw 77 q10 ∷
   rw 76 q10 ∷
   rw 75 q12 ∷
   rw 74 q12 ∷
   rw 73 q12 ∷
   rw 72 q12 ∷
   rw 71 q12 ∷
   rw 70 q12 ∷
   rw 69 q12 ∷
   rw 68 q12 ∷
   rw 67 q12 ∷
   rw 66 q12 ∷
   rw 65 q12 ∷
   rw 64 q12 ∷
   rw 63 q12 ∷
   rw 62 q12 ∷
   rw 61 q12 ∷
   rw 60 q12 ∷
   rw 59 q12 ∷
   rw 58 q12 ∷
   rw 59 q13 ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "举") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "举") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "举") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "举") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "举") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "举") ∷
   rw 64 q14 ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "乕") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "举") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "举") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "举") ∷
   rw⁻ 69 q12 ∷
   rw⁻ 70 q12 ∷
   rw⁻ 71 q12 ∷
   rw⁻ 72 q12 ∷
   rw⁻ 73 q12 ∷
   rw⁻ 74 q12 ∷
   rw⁻ 75 q12 ∷
   rw⁻ 76 q12 ∷
   rw⁻ 77 q12 ∷
   rw⁻ 78 q12 ∷
   rw⁻ 79 q12 ∷
   rw⁻ 80 q12 ∷
   rw⁻ 81 q12 ∷
   rw⁻ 82 q12 ∷
   rw⁻ 83 q12 ∷
   rw⁻ 84 q12 ∷
   rw⁻ 85 q12 ∷
   rw⁻ 86 q12 ∷
   rw⁻ 87 q10 ∷
   rw⁻ 88 q10 ∷
   rw⁻ 89 q10 ∷
   rw⁻ 90 q11 ∷
   rw⁻ 91 q10 ∷
   rw⁻ 92 q12 ∷
   rw⁻ 93 q12 ∷
   rw⁻ 94 q12 ∷
   rw⁻ 95 q12 ∷
   rw⁻ 96 q12 ∷
   rw⁻ 97 q12 ∷
   rw⁻ 98 q12 ∷
   rw⁻ 99 q12 ∷
   rw⁻ 100 q12 ∷
   rw⁻ 101 q10 ∷
   rw⁻ 102 q10 ∷
   rw⁻ 103 q10 ∷
   rw⁻ 104 q11 ∷
   rw⁻ 105 q10 ∷
   rw⁻ 106 q10 ∷
   rw⁻ 107 q10 ∷
   rw⁻ 108 q10 ∷
   rw⁻ 109 q11 ∷
   rw⁻ 110 q10 ∷
   rw 111 q5 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "乐") ∷
   re 58 1 (ℓ "乏丼丳丼乏") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "举") ∷
   rw 61 q6 ∷
   rw 60 q7 ∷
   rw 59 q8 ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 58 q5 ∷
   re 59 5 (ℓ "乐") ∷
   re 59 1 (ℓ "乏乃乏") ∷
   rw 61 q5 ∷
   re 57 3 (ℓ "举") ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "乐") ∷
   re 59 1 (ℓ "乏丼丳丼乏") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "举") ∷
   rw 62 q6 ∷
   rw 61 q7 ∷
   rw 60 q8 ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q5 ∷
   re 60 5 (ℓ "乐") ∷
   re 60 1 (ℓ "乏乃乏") ∷
   rw 62 q5 ∷
   re 58 3 (ℓ "举") ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q1 ∷
   re 60 3 (ℓ "乐") ∷
   re 60 1 (ℓ "乏丼丳丼乏") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "举") ∷
   rw 63 q6 ∷
   rw 62 q7 ∷
   rw 61 q8 ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q5 ∷
   re 61 5 (ℓ "乐") ∷
   re 61 1 (ℓ "乏乃乏") ∷
   rw 63 q5 ∷
   re 59 3 (ℓ "举") ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q1 ∷
   re 61 3 (ℓ "乐") ∷
   re 61 1 (ℓ "乏丼丳丼乏") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "举") ∷
   rw 64 q6 ∷
   rw 63 q7 ∷
   rw 62 q8 ∷
   re 62 1 (ℓ "乏丷乏") ∷
   rw 61 q5 ∷
   re 62 5 (ℓ "乐") ∷
   re 62 1 (ℓ "乏乃乏") ∷
   rw 64 q5 ∷
   re 60 3 (ℓ "举") ∷
   re 62 1 (ℓ "乏丷乏") ∷
   rw 61 q1 ∷
   re 62 3 (ℓ "乐") ∷
   re 62 1 (ℓ "乏丼丳丼乏") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "举") ∷
   rw 65 q6 ∷
   rw 64 q7 ∷
   rw 63 q8 ∷
   re 63 1 (ℓ "乏丷乏") ∷
   rw 62 q5 ∷
   re 63 5 (ℓ "乐") ∷
   re 63 1 (ℓ "乏乃乏") ∷
   rw 65 q5 ∷
   re 61 3 (ℓ "举") ∷
   re 63 1 (ℓ "乏丷乏") ∷
   rw 62 q1 ∷
   re 63 3 (ℓ "乐") ∷
   re 63 1 (ℓ "乏丼丳丼乏") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "举") ∷
   rw 66 q6 ∷
   rw 65 q7 ∷
   rw 64 q8 ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 63 q5 ∷
   re 64 5 (ℓ "乐") ∷
   re 64 1 (ℓ "乏乃乏") ∷
   rw 66 q5 ∷
   re 62 3 (ℓ "举") ∷
   rw 63 q15 ∷
   re 65 1 (ℓ "乏么乏") ∷
   rw 64 q1 ∷
   re 65 3 (ℓ "乐") ∷
   re 65 1 (ℓ "乏丼丳丼乏") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乕") ∷
   rw 68 q2 ∷
   rw 67 q3 ∷
   rw 66 q4 ∷
   re 66 1 (ℓ "乏么乏") ∷
   rw 65 q5 ∷
   re 66 5 (ℓ "乐") ∷
   re 66 1 (ℓ "乏乃乏") ∷
   rw 68 q5 ∷
   re 64 3 (ℓ "乕") ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q1 ∷
   re 66 3 (ℓ "乐") ∷
   re 66 1 (ℓ "乏丼丳丼乏") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "举") ∷
   rw 69 q6 ∷
   rw 68 q7 ∷
   rw 67 q8 ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 66 q5 ∷
   re 67 5 (ℓ "乐") ∷
   re 67 1 (ℓ "乏乃乏") ∷
   rw 69 q5 ∷
   re 65 3 (ℓ "举") ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 66 q1 ∷
   re 67 3 (ℓ "乐") ∷
   re 67 1 (ℓ "乏丼丳丼乏") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "举") ∷
   rw 70 q6 ∷
   rw 69 q7 ∷
   rw 68 q8 ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 67 q5 ∷
   re 68 5 (ℓ "乐") ∷
   re 68 1 (ℓ "乏乃乏") ∷
   rw 70 q5 ∷
   re 66 3 (ℓ "举") ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 67 q1 ∷
   re 68 3 (ℓ "乐") ∷
   re 68 1 (ℓ "乏丼丳丼乏") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "举") ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   rw 69 q8 ∷
   re 69 1 (ℓ "乏丷乏") ∷
   rw 68 q5 ∷
   re 69 5 (ℓ "乐") ∷
   re 69 1 (ℓ "乏乃乏") ∷
   rw 71 q5 ∷
   re 67 3 (ℓ "举") ∷
   rw 42 q16 ∷
   rw 126 q17 ∷
   rw 127 q18 ∷
   rw 128 q17 ∷
   rw 125 q17 ∷
   rw 126 q18 ∷
   rw 127 q17 ∷
   rw 124 q17 ∷
   rw 125 q18 ∷
   rw 126 q17 ∷
   rw 123 q17 ∷
   rw 124 q18 ∷
   rw 125 q17 ∷
   rw 122 q17 ∷
   rw 123 q18 ∷
   rw 124 q17 ∷
   rw 121 q17 ∷
   rw 122 q18 ∷
   rw 123 q17 ∷
   rw 120 q19 ∷
   rw 121 q20 ∷
   rw 122 q19 ∷
   rw 119 q21 ∷
   rw 120 q22 ∷
   rw 121 q21 ∷
   rw 118 q17 ∷
   rw 119 q18 ∷
   rw 120 q17 ∷
   rw 117 q17 ∷
   rw 118 q18 ∷
   rw 119 q17 ∷
   rw 116 q17 ∷
   rw 117 q18 ∷
   rw 118 q17 ∷
   rw 115 q19 ∷
   rw 116 q20 ∷
   rw 117 q19 ∷
   rw 114 q21 ∷
   rw 115 q22 ∷
   rw 116 q21 ∷
   rw 113 q19 ∷
   rw 114 q20 ∷
   rw 115 q19 ∷
   rw 112 q21 ∷
   rw 113 q22 ∷
   rw 114 q21 ∷
   rw 115 q23 ∷
   rw⁻ 114 q24 ∷
   rw⁻ 113 q25 ∷
   rw⁻ 112 q24 ∷
   rw 111 q26 ∷
   rw 112 q27 ∷
   rw 111 q24 ∷
   rw 112 q25 ∷
   rw 113 q24 ∷
   rw 114 q28 ∷
   rw 115 q29 ∷
   rw 110 q19 ∷
   rw 111 q20 ∷
   rw 112 q19 ∷
   rw 109 q21 ∷
   rw 110 q22 ∷
   rw 111 q21 ∷
   rw 108 q19 ∷
   rw 109 q20 ∷
   rw 110 q19 ∷
   rw 107 q19 ∷
   rw 108 q20 ∷
   rw 109 q19 ∷
   rw 106 q19 ∷
   rw 107 q20 ∷
   rw 108 q19 ∷
   rw 105 q19 ∷
   rw 106 q20 ∷
   rw 107 q19 ∷
   rw 104 q21 ∷
   rw 105 q22 ∷
   rw 106 q21 ∷
   rw 103 q19 ∷
   rw 104 q20 ∷
   rw 105 q19 ∷
   rw 102 q19 ∷
   rw 103 q20 ∷
   rw 104 q19 ∷
   rw 101 q19 ∷
   rw 102 q20 ∷
   rw 103 q19 ∷
   rw 100 q17 ∷
   rw 101 q18 ∷
   rw 102 q17 ∷
   rw 99 q17 ∷
   rw 100 q18 ∷
   rw 101 q17 ∷
   rw 98 q17 ∷
   rw 99 q18 ∷
   rw 100 q17 ∷
   rw 97 q17 ∷
   rw 98 q18 ∷
   rw 99 q17 ∷
   rw 96 q17 ∷
   rw 97 q18 ∷
   rw 98 q17 ∷
   rw 95 q17 ∷
   rw 96 q18 ∷
   rw 97 q17 ∷
   rw 94 q17 ∷
   rw 95 q18 ∷
   rw 96 q17 ∷
   rw 93 q17 ∷
   rw 94 q18 ∷
   rw 95 q17 ∷
   rw 92 q17 ∷
   rw 93 q18 ∷
   rw 94 q17 ∷
   rw 91 q19 ∷
   rw 92 q20 ∷
   rw 93 q19 ∷
   rw 90 q21 ∷
   rw 91 q22 ∷
   rw 92 q21 ∷
   rw 89 q19 ∷
   rw 90 q20 ∷
   rw 91 q19 ∷
   rw 88 q19 ∷
   rw 89 q20 ∷
   rw 90 q19 ∷
   rw 87 q19 ∷
   rw 88 q20 ∷
   rw 89 q19 ∷
   rw 86 q17 ∷
   rw 87 q18 ∷
   rw 88 q17 ∷
   rw 85 q17 ∷
   rw 86 q18 ∷
   rw 87 q17 ∷
   rw 84 q17 ∷
   rw 85 q18 ∷
   rw 86 q17 ∷
   rw 83 q17 ∷
   rw 84 q18 ∷
   rw 85 q17 ∷
   rw 82 q17 ∷
   rw 83 q18 ∷
   rw 84 q17 ∷
   rw 81 q17 ∷
   rw 82 q18 ∷
   rw 83 q17 ∷
   rw 80 q17 ∷
   rw 81 q18 ∷
   rw 82 q17 ∷
   rw 79 q17 ∷
   rw 80 q18 ∷
   rw 81 q17 ∷
   rw 78 q17 ∷
   rw 79 q18 ∷
   rw 80 q17 ∷
   rw 77 q17 ∷
   rw 78 q18 ∷
   rw 79 q17 ∷
   rw 76 q17 ∷
   rw 77 q18 ∷
   rw 78 q17 ∷
   rw 75 q17 ∷ []) Eq.refl
