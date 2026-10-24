{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D141 (W : Ws) where

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
  q1 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q2 : Eqn
  q2 = eqn (ℓ "两乊") (ℓ "乊两") (low-comm (CK₀₁) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q4 : Eqn
  q4 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q7 : Eqn
  q7 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 6 W
  q9 : Eqn
  q9 = wE 686 W
  q10 : Eqn
  q10 = wE 39 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "丈乊") (ℓ "乊丈") (low₁-comm (S) (((CS • CS • CS) ↑)))
  q14 : Eqn
  q14 = wE 687 W
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q18 : Eqn
  q18 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q19 : Eqn
  q19 = wE 534 W
  q20 : Eqn
  q20 = wE 21 W
  q21 : Eqn
  q21 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q22 : Eqn
  q22 = wE 51 W
  q23 : Eqn
  q23 = wE 360 W
  q24 : Eqn
  q24 = eqn (ℓ "丳乘") (ℓ "乘丳") (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q25 : Eqn
  q25 = wE 362 W
  q26 : Eqn
  q26 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q27 : Eqn
  q27 = wE 535 W
  q28 : Eqn
  q28 = wE 688 W
  q29 : Eqn
  q29 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))
  q30 : Eqn
  q30 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q31 : Eqn
  q31 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q32 : Eqn
  q32 = wE 612 W
  q33 : Eqn
  q33 = eqn (ℓ "丈乌") (ℓ "乌丈") (low₁-comm (S) ((CX₀₁ ↑)))
  q34 : Eqn
  q34 = wE 613 W
  q35 : Eqn
  q35 = wE 689 W
  q36 : Eqn
  q36 = wE 539 W
  q37 : Eqn
  q37 = wE 153 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];2,0->1) passes white iX via V2 conjugates 3 part0: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0 : ⟪ (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举丘乌丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠举举举举乏乏乏丷乏丼丳丼乏乏举丛乕举举举丠丠两丠两两丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part0 = derive (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举丘乌丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠举举举举乏乏乏丷乏丼丳丼乏乏举丛乕举举举丠丠两丠两两丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘")
  (rw 28 q1 ∷
   rw 29 q2 ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   rw 28 q2 ∷
   rw 29 q1 ∷
   rw 26 q3 ∷
   rw 27 q4 ∷
   rw 28 q3 ∷
   rw 25 q1 ∷
   rw 26 q2 ∷
   rw 27 q1 ∷
   rw 24 q3 ∷
   rw 25 q4 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q4 ∷
   rw 25 q3 ∷
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
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q3 ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   rw 15 q12 ∷
   rw 16 q13 ∷
   rw 17 q12 ∷
   rw 14 q1 ∷
   rw 15 q2 ∷
   rw 16 q1 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   rw 11 q3 ∷
   rw 12 q4 ∷
   rw 13 q3 ∷
   rw 10 q12 ∷
   rw 11 q13 ∷
   rw 12 q12 ∷
   rw 9 q1 ∷
   rw 10 q2 ∷
   rw 11 q1 ∷
   rw 8 q12 ∷
   rw 9 q13 ∷
   rw 10 q12 ∷
   rw 7 q1 ∷
   rw 8 q2 ∷
   rw 9 q1 ∷
   rw 10 q5 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q6 ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   rw 9 q10 ∷
   rw 10 q11 ∷
   rw 0 q14 ∷
   rw 36 q15 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 37 q16 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 36 q16 ∷
   re 33 1 (ℓ "乏么乏") ∷
   rw 35 q16 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 34 q16 ∷
   rw 31 q17 ∷
   rw 30 q17 ∷
   rw 29 q18 ∷
   rw 28 q17 ∷
   rw 27 q18 ∷
   rw 26 q18 ∷
   rw 27 q19 ∷
   rw 28 q15 ∷
   re 26 3 (ℓ "举") ∷
   rw 29 q15 ∷
   re 27 3 (ℓ "乕") ∷
   rw 30 q15 ∷
   re 28 3 (ℓ "举") ∷
   rw 31 q15 ∷
   re 29 3 (ℓ "举") ∷
   rw⁻ 30 q18 ∷
   rw⁻ 31 q18 ∷
   rw⁻ 32 q17 ∷
   rw⁻ 33 q18 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 35 q17 ∷
   rw 36 q16 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q15 ∷
   re 26 3 (ℓ "乐") ∷
   re 26 1 (ℓ "乏丼丳丼乏") ∷
   rw 32 q15 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q20 ∷
   rw 28 q21 ∷
   rw 27 q22 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q16 ∷
   re 27 5 (ℓ "乐") ∷
   re 27 1 (ℓ "乏乃乏") ∷
   rw 29 q16 ∷
   re 25 3 (ℓ "举") ∷
   re 27 1 (ℓ "乏么乏") ∷
   rw 26 q15 ∷
   re 27 3 (ℓ "乐") ∷
   re 27 1 (ℓ "乏丼丳丼乏") ∷
   rw 33 q15 ∷
   re 31 3 (ℓ "乕") ∷
   rw 30 q23 ∷
   rw 29 q24 ∷
   rw 28 q25 ∷
   re 28 1 (ℓ "乏么乏") ∷
   rw 27 q16 ∷
   re 28 5 (ℓ "乐") ∷
   re 28 1 (ℓ "乏乃乏") ∷
   rw 30 q16 ∷
   re 26 3 (ℓ "乕") ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q15 ∷
   re 28 3 (ℓ "乐") ∷
   re 28 1 (ℓ "乏丼丳丼乏") ∷
   rw 34 q15 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q20 ∷
   rw 30 q21 ∷
   rw 29 q22 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q16 ∷
   re 29 5 (ℓ "乐") ∷
   re 29 1 (ℓ "乏乃乏") ∷
   rw 31 q16 ∷
   re 27 3 (ℓ "举") ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q15 ∷
   re 29 3 (ℓ "乐") ∷
   re 29 1 (ℓ "乏丼丳丼乏") ∷
   rw 35 q15 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q20 ∷
   rw 31 q21 ∷
   rw 30 q22 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q16 ∷
   re 30 5 (ℓ "乐") ∷
   re 30 1 (ℓ "乏乃乏") ∷
   rw 32 q16 ∷
   re 28 3 (ℓ "举") ∷
   rw 29 q15 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 30 q16 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 29 q16 ∷
   re 26 1 (ℓ "乏么乏") ∷
   rw 28 q16 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 27 q16 ∷
   rw 24 q18 ∷
   rw 23 q18 ∷
   rw 22 q18 ∷
   rw 21 q18 ∷
   rw 20 q18 ∷
   rw 19 q18 ∷
   rw 18 q26 ∷
   rw 17 q17 ∷
   rw 16 q18 ∷
   rw 15 q18 ∷
   rw 14 q18 ∷
   rw 13 q26 ∷
   rw 12 q17 ∷
   rw 11 q26 ∷
   rw 10 q17 ∷
   rw 11 q27 ∷
   rw 12 q15 ∷
   re 10 3 (ℓ "举") ∷
   rw 13 q15 ∷
   re 11 3 (ℓ "乕") ∷
   rw 14 q15 ∷
   re 12 3 (ℓ "举") ∷
   rw 15 q15 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q17 ∷
   rw⁻ 15 q26 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q26 ∷
   rw⁻ 18 q18 ∷
   rw⁻ 19 q18 ∷
   rw⁻ 20 q18 ∷
   rw⁻ 21 q17 ∷
   rw⁻ 22 q26 ∷
   rw⁻ 23 q18 ∷
   rw⁻ 24 q18 ∷
   rw⁻ 25 q18 ∷
   rw⁻ 26 q18 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 28 q18 ∷
   rw 29 q16 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q15 ∷
   re 10 3 (ℓ "乐") ∷
   re 10 1 (ℓ "乏丼丳丼乏") ∷
   rw 16 q15 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   rw 11 q22 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q16 ∷
   re 11 5 (ℓ "乐") ∷
   re 11 1 (ℓ "乏乃乏") ∷
   rw 13 q16 ∷
   re 9 3 (ℓ "举") ∷
   re 11 1 (ℓ "乏么乏") ∷
   rw 10 q15 ∷
   re 11 3 (ℓ "乐") ∷
   re 11 1 (ℓ "乏丼丳丼乏") ∷
   rw 17 q15 ∷
   re 15 3 (ℓ "乕") ∷
   rw 14 q23 ∷
   rw 13 q24 ∷
   rw 12 q25 ∷
   re 12 1 (ℓ "乏么乏") ∷
   rw 11 q16 ∷
   re 12 5 (ℓ "乐") ∷
   re 12 1 (ℓ "乏乃乏") ∷
   rw 14 q16 ∷
   re 10 3 (ℓ "乕") ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q15 ∷
   re 12 3 (ℓ "乐") ∷
   re 12 1 (ℓ "乏丼丳丼乏") ∷
   rw 18 q15 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q20 ∷
   rw 14 q21 ∷
   rw 13 q22 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q16 ∷
   re 13 5 (ℓ "乐") ∷
   re 13 1 (ℓ "乏乃乏") ∷
   rw 15 q16 ∷
   re 11 3 (ℓ "举") ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q15 ∷
   re 13 3 (ℓ "乐") ∷
   re 13 1 (ℓ "乏丼丳丼乏") ∷
   rw 19 q15 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q20 ∷
   rw 15 q21 ∷
   rw 14 q22 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q16 ∷
   re 14 5 (ℓ "乐") ∷
   re 14 1 (ℓ "乏乃乏") ∷
   rw 16 q16 ∷
   re 12 3 (ℓ "举") ∷
   rw 3 q28 ∷
   rw 35 q1 ∷
   rw 36 q29 ∷
   rw 37 q1 ∷
   rw 34 q1 ∷
   rw 35 q29 ∷
   rw 36 q1 ∷
   rw 33 q3 ∷
   rw 34 q30 ∷
   rw 35 q3 ∷
   rw 32 q1 ∷
   rw 33 q29 ∷
   rw 34 q1 ∷
   rw 31 q3 ∷
   rw 32 q30 ∷
   rw 33 q3 ∷
   rw 30 q3 ∷
   rw 31 q30 ∷
   rw 32 q3 ∷
   rw 33 q5 ∷
   rw⁻ 32 q6 ∷
   rw⁻ 31 q31 ∷
   rw⁻ 30 q6 ∷
   rw 29 q8 ∷
   rw 30 q32 ∷
   rw 29 q6 ∷
   rw 30 q31 ∷
   rw 31 q6 ∷
   rw 32 q10 ∷
   rw 33 q11 ∷
   rw 28 q3 ∷
   rw 29 q30 ∷
   rw 30 q3 ∷
   rw 27 q3 ∷
   rw 28 q30 ∷
   rw 29 q3 ∷
   rw 26 q3 ∷
   rw 27 q30 ∷
   rw 28 q3 ∷
   rw 25 q3 ∷
   rw 26 q30 ∷
   rw 27 q3 ∷
   rw 24 q3 ∷
   rw 25 q30 ∷
   rw 26 q3 ∷
   rw 23 q3 ∷
   rw 24 q30 ∷
   rw 25 q3 ∷
   rw 22 q12 ∷
   rw 23 q33 ∷
   rw 24 q12 ∷
   rw 21 q1 ∷
   rw 22 q29 ∷
   rw 23 q1 ∷
   rw 20 q3 ∷
   rw 21 q30 ∷
   rw 22 q3 ∷
   rw 19 q3 ∷
   rw 20 q30 ∷
   rw 21 q3 ∷
   rw 18 q3 ∷
   rw 19 q30 ∷
   rw 20 q3 ∷
   rw 17 q12 ∷
   rw 18 q33 ∷
   rw 19 q12 ∷
   rw 16 q1 ∷
   rw 17 q29 ∷
   rw 18 q1 ∷
   rw 15 q12 ∷
   rw 16 q33 ∷
   rw 17 q12 ∷
   rw 14 q1 ∷
   rw 15 q29 ∷
   rw 16 q1 ∷
   rw 17 q5 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q31 ∷
   rw⁻ 14 q6 ∷
   rw 13 q8 ∷
   rw 14 q32 ∷
   rw 13 q6 ∷
   rw 14 q31 ∷
   rw 15 q6 ∷
   rw 16 q10 ∷
   rw 17 q11 ∷
   rw 7 q34 ∷
   rw 50 q15 ∷
   re 49 1 (ℓ "乏丷乏") ∷
   rw 51 q16 ∷
   re 48 1 (ℓ "乏丷乏") ∷
   rw 50 q16 ∷
   re 47 1 (ℓ "乏丷乏") ∷
   rw 49 q16 ∷
   re 46 1 (ℓ "乏么乏") ∷
   rw 48 q16 ∷
   rw 45 q35 ∷
   re 44 1 (ℓ "乏丷乏") ∷
   rw 46 q16 ∷
   re 43 1 (ℓ "乏丷乏") ∷
   rw 45 q16 ∷
   re 42 1 (ℓ "乏丷乏") ∷
   rw 44 q16 ∷
   re 41 1 (ℓ "乏丷乏") ∷
   rw 43 q16 ∷
   re 40 1 (ℓ "乏丷乏") ∷
   rw 42 q16 ∷
   re 39 1 (ℓ "乏丷乏") ∷
   rw 41 q16 ∷
   rw 38 q17 ∷
   rw 37 q17 ∷
   rw 36 q18 ∷
   rw 35 q17 ∷
   rw 34 q18 ∷
   rw 33 q18 ∷
   rw 34 q36 ∷
   rw 35 q15 ∷
   re 33 3 (ℓ "举") ∷
   rw 36 q15 ∷
   re 34 3 (ℓ "举") ∷
   rw 37 q15 ∷
   re 35 3 (ℓ "举") ∷
   rw 38 q15 ∷
   re 36 3 (ℓ "举") ∷
   rw 39 q15 ∷
   re 37 3 (ℓ "举") ∷
   rw 40 q15 ∷
   re 38 3 (ℓ "举") ∷
   rw 39 q37 ∷
   rw 42 q15 ∷
   re 40 3 (ℓ "乕") ∷
   rw 43 q15 ∷
   re 41 3 (ℓ "举") ∷
   rw 44 q15 ∷
   re 42 3 (ℓ "举") ∷
   rw 45 q15 ∷
   re 43 3 (ℓ "举") ∷
   rw⁻ 44 q18 ∷
   rw⁻ 45 q18 ∷
   rw⁻ 46 q17 ∷
   rw⁻ 47 q18 ∷
   rw⁻ 48 q17 ∷
   rw⁻ 49 q17 ∷
   rw 50 q16 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 32 q15 ∷
   re 33 3 (ℓ "乐") ∷
   re 33 1 (ℓ "乏丼丳丼乏") ∷
   rw 39 q15 ∷
   re 37 3 (ℓ "举") ∷
   rw 36 q20 ∷
   rw 35 q21 ∷
   rw 34 q22 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 33 q16 ∷
   re 34 5 (ℓ "乐") ∷
   re 34 1 (ℓ "乏乃乏") ∷
   rw 36 q16 ∷
   re 32 3 (ℓ "举") ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 33 q15 ∷
   re 34 3 (ℓ "乐") ∷
   re 34 1 (ℓ "乏丼丳丼乏") ∷
   rw 40 q15 ∷
   re 38 3 (ℓ "举") ∷
   rw 37 q20 ∷
   rw 36 q21 ∷
   rw 35 q22 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 34 q16 ∷
   re 35 5 (ℓ "乐") ∷
   re 35 1 (ℓ "乏乃乏") ∷
   rw 37 q16 ∷
   re 33 3 (ℓ "举") ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 34 q15 ∷
   re 35 3 (ℓ "乐") ∷
   re 35 1 (ℓ "乏丼丳丼乏") ∷
   rw 41 q15 ∷
   re 39 3 (ℓ "举") ∷
   rw 38 q20 ∷
   rw 37 q21 ∷
   rw 36 q22 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q16 ∷
   re 36 5 (ℓ "乐") ∷
   re 36 1 (ℓ "乏乃乏") ∷
   rw 38 q16 ∷
   re 34 3 (ℓ "举") ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q15 ∷
   re 36 3 (ℓ "乐") ∷
   re 36 1 (ℓ "乏丼丳丼乏") ∷
   rw 42 q15 ∷
   re 40 3 (ℓ "举") ∷
   rw 39 q20 ∷
   rw 38 q21 ∷
   rw 37 q22 ∷
   re 37 1 (ℓ "乏丷乏") ∷
   rw 36 q16 ∷
   re 37 5 (ℓ "乐") ∷
   re 37 1 (ℓ "乏乃乏") ∷
   rw 39 q16 ∷
   re 35 3 (ℓ "举") ∷
   re 37 1 (ℓ "乏丷乏") ∷
   rw 36 q15 ∷
   re 37 3 (ℓ "乐") ∷
   re 37 1 (ℓ "乏丼丳丼乏") ∷
   rw 43 q15 ∷
   re 41 3 (ℓ "举") ∷
   rw 40 q20 ∷
   rw 39 q21 ∷
   rw 38 q22 ∷
   re 38 1 (ℓ "乏丷乏") ∷ []) Eq.refl
