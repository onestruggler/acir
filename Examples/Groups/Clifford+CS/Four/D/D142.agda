{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D142 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 21 W
  q4 : Eqn
  q4 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 51 W
  q6 : Eqn
  q6 = eqn (ℓ "乃丛") (ℓ "丛乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) ((S • S • S)))
  q7 : Eqn
  q7 = wE 360 W
  q8 : Eqn
  q8 = eqn (ℓ "丳乘") (ℓ "乘丳") (low-comm (CX₁₀) ((S ↑ • CK₁₀)))
  q9 : Eqn
  q9 = wE 362 W
  q10 : Eqn
  q10 = wE 689 W
  q11 : Eqn
  q11 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q12 : Eqn
  q12 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "两乏") (ℓ "乏两") (low-comm (CK₀₁) (Swap))
  q14 : Eqn
  q14 = wE 541 W
  q15 : Eqn
  q15 = wE 153 W
  q16 : Eqn
  q16 = wE 690 W
  q17 : Eqn
  q17 = eqn (ℓ "两丘") (ℓ "丘两") (low-comm (CK₀₁) (X))
  q18 : Eqn
  q18 = eqn (ℓ "两乌") (ℓ "乌两") (low-comm (CK₀₁) (CX₀₁))
  q19 : Eqn
  q19 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q20 : Eqn
  q20 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q21 : Eqn
  q21 = wE 5 W
  q22 : Eqn
  q22 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q23 : Eqn
  q23 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q24 : Eqn
  q24 = wE 6 W
  q25 : Eqn
  q25 = wE 612 W
  q26 : Eqn
  q26 = wE 39 W
  q27 : Eqn
  q27 = wE 31 W
  q28 : Eqn
  q28 = eqn (ℓ "丈丘") (ℓ "丘丈") (low₁-comm (S) ((X ↑)))
  q29 : Eqn
  q29 = eqn (ℓ "丈乌") (ℓ "乌丈") (low₁-comm (S) ((CX₀₁ ↑)))
  q30 : Eqn
  q30 = wE 613 W
  q31 : Eqn
  q31 = wE 543 W
  q32 : Eqn
  q32 = wE 544 W
  q33 : Eqn
  q33 = wE 534 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];2,0->1) passes white iX via V2 conjugates 3 part1: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1 : ⟪ (ℓ "丘乊丘举乕举举丘乌丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠举举举举乏乏乏丷乏丼丳丼乏乏举丛乕举举举丠丠两丠两两丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ ≈ ⟪ (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠乏丠丠丠丠丷么丷丷乏乃丠丠两丠两两丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-white-iX-via-V2-conjugates-3-part1 = derive (ℓ "丘乊丘举乕举举丘乌丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠举举举举乏乏乏丷乏丼丳丼乏乏举丛乕举举举丠丠两丠两两丘乌丘丘丷么丷丷丘丘丶丶丶丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘") (ℓ "丘乊丘举乕举举丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丶丶丶丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠乏丠丠丠丠丷么丷丷乏乃丠丠两丠两两丘乌丘举举举举举举丛乕举举举丘乌丘丘丷么丷丷丘丘丷丷丷丘")
  (rw 37 q1 ∷
   re 38 5 (ℓ "乐") ∷
   re 38 1 (ℓ "乏乃乏") ∷
   rw 40 q1 ∷
   re 36 3 (ℓ "举") ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 37 q2 ∷
   re 38 3 (ℓ "乐") ∷
   re 38 1 (ℓ "乏丼丳丼乏") ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "举") ∷
   rw 41 q3 ∷
   rw 40 q4 ∷
   rw 39 q5 ∷
   re 39 1 (ℓ "乏丷乏") ∷
   rw 38 q1 ∷
   re 39 5 (ℓ "乐") ∷
   re 39 1 (ℓ "乏乃乏") ∷
   rw 41 q1 ∷
   re 37 3 (ℓ "举") ∷
   rw 38 q6 ∷
   re 40 1 (ℓ "乏么乏") ∷
   rw 39 q2 ∷
   re 40 3 (ℓ "乐") ∷
   re 40 1 (ℓ "乏丼丳丼乏") ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "乕") ∷
   rw 43 q7 ∷
   rw 42 q8 ∷
   rw 41 q9 ∷
   re 41 1 (ℓ "乏么乏") ∷
   rw 40 q1 ∷
   re 41 5 (ℓ "乐") ∷
   re 41 1 (ℓ "乏乃乏") ∷
   rw 43 q1 ∷
   re 39 3 (ℓ "乕") ∷
   re 41 1 (ℓ "乏丷乏") ∷
   rw 40 q2 ∷
   re 41 3 (ℓ "乐") ∷
   re 41 1 (ℓ "乏丼丳丼乏") ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "举") ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   re 42 1 (ℓ "乏丷乏") ∷
   rw 41 q1 ∷
   re 42 5 (ℓ "乐") ∷
   re 42 1 (ℓ "乏乃乏") ∷
   rw 44 q1 ∷
   re 40 3 (ℓ "举") ∷
   re 42 1 (ℓ "乏丷乏") ∷
   rw 41 q2 ∷
   re 42 3 (ℓ "乐") ∷
   re 42 1 (ℓ "乏丼丳丼乏") ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "举") ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   rw 43 q5 ∷
   re 43 1 (ℓ "乏丷乏") ∷
   rw 42 q1 ∷
   re 43 5 (ℓ "乐") ∷
   re 43 1 (ℓ "乏乃乏") ∷
   rw 45 q1 ∷
   re 41 3 (ℓ "举") ∷
   re 43 1 (ℓ "乏丷乏") ∷
   rw 42 q2 ∷
   re 43 3 (ℓ "乐") ∷
   re 43 1 (ℓ "乏丼丳丼乏") ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "举") ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   re 44 1 (ℓ "乏丷乏") ∷
   rw 43 q1 ∷
   re 44 5 (ℓ "乐") ∷
   re 44 1 (ℓ "乏乃乏") ∷
   rw 46 q1 ∷
   re 42 3 (ℓ "举") ∷
   rw 43 q2 ∷
   re 42 1 (ℓ "乏丷乏") ∷
   rw 44 q1 ∷
   re 41 1 (ℓ "乏丷乏") ∷
   rw 43 q1 ∷
   re 40 1 (ℓ "乏丷乏") ∷
   rw 42 q1 ∷
   re 39 1 (ℓ "乏么乏") ∷
   rw 41 q1 ∷
   rw 38 q10 ∷
   re 37 1 (ℓ "乏丷乏") ∷
   rw 39 q1 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 38 q1 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 37 q1 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 36 q1 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 35 q1 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 34 q1 ∷
   rw 31 q11 ∷
   rw 30 q11 ∷
   rw 29 q11 ∷
   rw 28 q11 ∷
   rw 27 q11 ∷
   rw 26 q11 ∷
   rw 25 q12 ∷
   rw 24 q13 ∷
   rw 23 q11 ∷
   rw 22 q11 ∷
   rw 21 q11 ∷
   rw 20 q12 ∷
   rw 19 q13 ∷
   rw 18 q12 ∷
   rw 17 q13 ∷
   rw 18 q14 ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "举") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "举") ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "举") ∷
   rw 22 q2 ∷
   re 20 3 (ℓ "举") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "举") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "举") ∷
   rw 23 q15 ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "乕") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "举") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "举") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "举") ∷
   rw⁻ 28 q13 ∷
   rw⁻ 29 q12 ∷
   rw⁻ 30 q13 ∷
   rw⁻ 31 q12 ∷
   rw⁻ 32 q11 ∷
   rw⁻ 33 q11 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 35 q13 ∷
   rw⁻ 36 q12 ∷
   rw⁻ 37 q11 ∷
   rw⁻ 38 q11 ∷
   rw⁻ 39 q11 ∷
   rw⁻ 40 q11 ∷
   rw⁻ 41 q11 ∷
   rw⁻ 42 q11 ∷
   rw 43 q1 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q2 ∷
   re 17 3 (ℓ "乐") ∷
   re 17 1 (ℓ "乏丼丳丼乏") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   rw 18 q5 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q1 ∷
   re 18 5 (ℓ "乐") ∷
   re 18 1 (ℓ "乏乃乏") ∷
   rw 20 q1 ∷
   re 16 3 (ℓ "举") ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "乐") ∷
   re 18 1 (ℓ "乏丼丳丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q1 ∷
   re 19 5 (ℓ "乐") ∷
   re 19 1 (ℓ "乏乃乏") ∷
   rw 21 q1 ∷
   re 17 3 (ℓ "举") ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "乐") ∷
   re 19 1 (ℓ "乏丼丳丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q1 ∷
   re 20 5 (ℓ "乐") ∷
   re 20 1 (ℓ "乏乃乏") ∷
   rw 22 q1 ∷
   re 18 3 (ℓ "举") ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "乐") ∷
   re 20 1 (ℓ "乏丼丳丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q1 ∷
   re 21 5 (ℓ "乐") ∷
   re 21 1 (ℓ "乏乃乏") ∷
   rw 23 q1 ∷
   re 19 3 (ℓ "举") ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "乐") ∷
   re 21 1 (ℓ "乏丼丳丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q1 ∷
   re 22 5 (ℓ "乐") ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw 24 q1 ∷
   re 20 3 (ℓ "举") ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "乐") ∷
   re 22 1 (ℓ "乏丼丳丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q1 ∷
   re 23 5 (ℓ "乐") ∷
   re 23 1 (ℓ "乏乃乏") ∷
   rw 25 q1 ∷
   re 21 3 (ℓ "举") ∷
   rw 22 q6 ∷
   re 24 1 (ℓ "乏么乏") ∷
   rw 23 q2 ∷
   re 24 3 (ℓ "乐") ∷
   re 24 1 (ℓ "乏丼丳丼乏") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "乕") ∷
   rw 27 q7 ∷
   rw 26 q8 ∷
   rw 25 q9 ∷
   re 25 1 (ℓ "乏么乏") ∷
   rw 24 q1 ∷
   re 25 5 (ℓ "乐") ∷
   re 25 1 (ℓ "乏乃乏") ∷
   rw 27 q1 ∷
   re 23 3 (ℓ "乕") ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "乐") ∷
   re 25 1 (ℓ "乏丼丳丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q1 ∷
   re 26 5 (ℓ "乐") ∷
   re 26 1 (ℓ "乏乃乏") ∷
   rw 28 q1 ∷
   re 24 3 (ℓ "举") ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "乐") ∷
   re 26 1 (ℓ "乏丼丳丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q1 ∷
   re 27 5 (ℓ "乐") ∷
   re 27 1 (ℓ "乏乃乏") ∷
   rw 29 q1 ∷
   re 25 3 (ℓ "举") ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "乐") ∷
   re 27 1 (ℓ "乏丼丳丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q1 ∷
   re 28 5 (ℓ "乐") ∷
   re 28 1 (ℓ "乏乃乏") ∷
   rw 30 q1 ∷
   re 26 3 (ℓ "举") ∷
   rw 10 q16 ∷
   rw 49 q17 ∷
   rw 50 q18 ∷
   rw 51 q17 ∷
   rw 48 q17 ∷
   rw 49 q18 ∷
   rw 50 q17 ∷
   rw 47 q19 ∷
   rw 48 q20 ∷
   rw 49 q19 ∷
   rw 46 q17 ∷
   rw 47 q18 ∷
   rw 48 q17 ∷
   rw 45 q19 ∷
   rw 46 q20 ∷
   rw 47 q19 ∷
   rw 44 q19 ∷
   rw 45 q20 ∷
   rw 46 q19 ∷
   rw 47 q21 ∷
   rw⁻ 46 q22 ∷
   rw⁻ 45 q23 ∷
   rw⁻ 44 q22 ∷
   rw 43 q24 ∷
   rw 44 q25 ∷
   rw 43 q22 ∷
   rw 44 q23 ∷
   rw 45 q22 ∷
   rw 46 q26 ∷
   rw 47 q27 ∷
   rw 42 q19 ∷
   rw 43 q20 ∷
   rw 44 q19 ∷
   rw 41 q19 ∷
   rw 42 q20 ∷
   rw 43 q19 ∷
   rw 40 q19 ∷
   rw 41 q20 ∷
   rw 42 q19 ∷
   rw 39 q19 ∷
   rw 40 q20 ∷
   rw 41 q19 ∷
   rw 38 q19 ∷
   rw 39 q20 ∷
   rw 40 q19 ∷
   rw 37 q19 ∷
   rw 38 q20 ∷
   rw 39 q19 ∷
   rw 36 q28 ∷
   rw 37 q29 ∷
   rw 38 q28 ∷
   rw 35 q17 ∷
   rw 36 q18 ∷
   rw 37 q17 ∷
   rw 34 q19 ∷
   rw 35 q20 ∷
   rw 36 q19 ∷
   rw 33 q19 ∷
   rw 34 q20 ∷
   rw 35 q19 ∷
   rw 32 q19 ∷
   rw 33 q20 ∷
   rw 34 q19 ∷
   rw 31 q28 ∷
   rw 32 q29 ∷
   rw 33 q28 ∷
   rw 30 q17 ∷
   rw 31 q18 ∷
   rw 32 q17 ∷
   rw 29 q28 ∷
   rw 30 q29 ∷
   rw 31 q28 ∷
   rw 28 q17 ∷
   rw 29 q18 ∷
   rw 30 q17 ∷
   rw 31 q21 ∷
   rw⁻ 30 q22 ∷
   rw⁻ 29 q23 ∷
   rw⁻ 28 q22 ∷
   rw 27 q24 ∷
   rw 28 q25 ∷
   rw 27 q22 ∷
   rw 28 q23 ∷
   rw 29 q22 ∷
   rw 30 q26 ∷
   rw 31 q27 ∷
   rw 21 q30 ∷
   rw 24 q31 ∷
   rw 30 q32 ∷
   rw 68 q2 ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 69 q1 ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 68 q1 ∷
   re 65 1 (ℓ "乏么乏") ∷
   rw 67 q1 ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 66 q1 ∷
   rw 63 q13 ∷
   rw 62 q13 ∷
   rw 61 q11 ∷
   rw 60 q13 ∷
   rw 59 q11 ∷
   rw 58 q11 ∷
   rw 59 q33 ∷
   rw 60 q2 ∷
   re 58 3 (ℓ "举") ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "乕") ∷
   rw 62 q2 ∷
   re 60 3 (ℓ "举") ∷
   rw 63 q2 ∷
   re 61 3 (ℓ "举") ∷
   rw⁻ 62 q11 ∷
   rw⁻ 63 q11 ∷
   rw⁻ 64 q13 ∷
   rw⁻ 65 q11 ∷
   rw⁻ 66 q13 ∷
   rw⁻ 67 q13 ∷
   rw 68 q1 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q2 ∷
   re 58 3 (ℓ "乐") ∷
   re 58 1 (ℓ "乏丼丳丼乏") ∷
   rw 64 q2 ∷
   re 62 3 (ℓ "举") ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   rw 59 q5 ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 58 q1 ∷
   re 59 5 (ℓ "乐") ∷
   re 59 1 (ℓ "乏乃乏") ∷
   rw 61 q1 ∷
   re 57 3 (ℓ "举") ∷
   re 59 1 (ℓ "乏么乏") ∷
   rw 58 q2 ∷
   re 59 3 (ℓ "乐") ∷
   re 59 1 (ℓ "乏丼丳丼乏") ∷
   rw 65 q2 ∷
   re 63 3 (ℓ "乕") ∷
   rw 62 q7 ∷
   rw 61 q8 ∷
   rw 60 q9 ∷
   re 60 1 (ℓ "乏么乏") ∷
   rw 59 q1 ∷
   re 60 5 (ℓ "乐") ∷
   re 60 1 (ℓ "乏乃乏") ∷
   rw 62 q1 ∷
   re 58 3 (ℓ "乕") ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q2 ∷
   re 60 3 (ℓ "乐") ∷
   re 60 1 (ℓ "乏丼丳丼乏") ∷
   rw 66 q2 ∷
   re 64 3 (ℓ "举") ∷
   rw 63 q3 ∷
   rw 62 q4 ∷
   rw 61 q5 ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q1 ∷
   re 61 5 (ℓ "乐") ∷
   re 61 1 (ℓ "乏乃乏") ∷
   rw 63 q1 ∷
   re 59 3 (ℓ "举") ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q2 ∷
   re 61 3 (ℓ "乐") ∷
   re 61 1 (ℓ "乏丼丳丼乏") ∷
   rw 67 q2 ∷
   re 65 3 (ℓ "举") ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   rw 62 q5 ∷
   re 62 1 (ℓ "乏丷乏") ∷
   rw 61 q1 ∷
   re 62 5 (ℓ "乐") ∷
   re 62 1 (ℓ "乏乃乏") ∷
   rw 64 q1 ∷
   re 60 3 (ℓ "举") ∷
   rw 61 q2 ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 62 q1 ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 61 q1 ∷
   re 58 1 (ℓ "乏么乏") ∷
   rw 60 q1 ∷
   re 57 1 (ℓ "乏丷乏") ∷
   rw 59 q1 ∷
   rw 56 q11 ∷
   rw 55 q11 ∷
   rw 54 q11 ∷
   rw 53 q11 ∷ []) Eq.refl
