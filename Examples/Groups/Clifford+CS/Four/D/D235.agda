{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D235 (W : Ws) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : Eqn
  q1 = wE 31 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 629 W
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 1 W
  q9 : Eqn
  q9 = wE 113 W
  q10 : Eqn
  q10 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = wE 114 W
  q12 : Eqn
  q12 = wE 3 W
  q13 : Eqn
  q13 = wE 673 W
  q14 : Eqn
  q14 = wE 557 W
  q15 : Eqn
  q15 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q16 : Eqn
  q16 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q17 : Eqn
  q17 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q18 : Eqn
  q18 = wE 566 W
  q19 : Eqn
  q19 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q20 : Eqn
  q20 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q21 : Eqn
  q21 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q22 : Eqn
  q22 = wE 464 W
  q23 : Eqn
  q23 = wE 567 W
  q24 : Eqn
  q24 = wE 151 W
  q25 : Eqn
  q25 = wE 140 W
  q26 : Eqn
  q26 = wE 630 W
  q27 : Eqn
  q27 = wE 142 W
  q28 : Eqn
  q28 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSSKSS;2,3->0) passes groups of WBar(SSKSKK;~2,1->0) part2: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part2 : ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part2 = derive (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (re 21 3 (CS03 ∷ []) ∷
   rw 22 q1 ∷
   rw 19 q2 ∷
   rw⁻ 18 q3 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q4 ∷
   rw 18 q5 ∷
   rw⁻ 17 q4 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q6 ∷
   rw 17 q3 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw 19 q7 ∷
   rw 20 q4 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q1 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q8 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   rw 19 q11 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   re 19 5 (CS03 ∷ []) ∷
   rw 21 q2 ∷
   rw⁻ 20 q3 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q4 ∷
   rw 20 q5 ∷
   rw⁻ 19 q4 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q6 ∷
   rw 19 q3 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   rw 21 q7 ∷
   rw 22 q4 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q1 ∷
   rw 18 q2 ∷
   rw⁻ 17 q3 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q4 ∷
   rw 17 q5 ∷
   rw⁻ 16 q4 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q6 ∷
   rw 16 q3 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   rw 18 q7 ∷
   rw 19 q4 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q1 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q8 ∷
   re 21 3 (CX31 ∷ []) ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q11 ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q2 ∷
   rw⁻ 19 q3 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q4 ∷
   rw 19 q5 ∷
   rw⁻ 18 q4 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q6 ∷
   rw 18 q3 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   rw 20 q7 ∷
   rw 21 q4 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q1 ∷
   rw 17 q2 ∷
   rw⁻ 16 q3 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q4 ∷
   rw 16 q5 ∷
   rw⁻ 15 q4 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 16 q6 ∷
   rw 15 q3 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw 17 q7 ∷
   rw 18 q4 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q1 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q8 ∷
   re 20 3 (CX31 ∷ []) ∷
   rw 19 q9 ∷
   rw 18 q10 ∷
   rw 17 q11 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q12 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 19 q2 ∷
   rw⁻ 18 q3 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q4 ∷
   rw 18 q5 ∷
   rw⁻ 17 q4 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q6 ∷
   rw 17 q3 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw 19 q7 ∷
   rw 20 q4 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q1 ∷
   rw 14 q13 ∷
   rw 8 q14 ∷
   rw 57 q8 ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q15 ∷
   rw 51 q15 ∷
   rw 50 q16 ∷
   rw 49 q17 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw 45 q16 ∷
   rw 44 q17 ∷
   rw 43 q16 ∷
   rw 42 q17 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q12 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q12 ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 41 q12 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   rw 37 q18 ∷
   rw⁻ 36 q17 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 38 q17 ∷
   rw⁻ 39 q16 ∷
   rw⁻ 40 q15 ∷
   rw⁻ 41 q15 ∷
   rw⁻ 42 q15 ∷
   rw⁻ 43 q17 ∷
   rw⁻ 44 q16 ∷
   rw⁻ 45 q15 ∷
   rw⁻ 46 q15 ∷
   rw⁻ 47 q15 ∷
   rw⁻ 48 q15 ∷
   rw⁻ 49 q15 ∷
   rw⁻ 50 q15 ∷
   rw 53 q8 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 54 q8 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 55 q8 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 56 q8 ∷
   re 54 3 (CK30 ∷ []) ∷
   rw 57 q8 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 58 q8 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q12 ∷
   rw⁻ 35 q19 ∷
   rw⁻ 36 q20 ∷
   rw⁻ 37 q19 ∷
   rw⁻ 38 q20 ∷
   rw⁻ 39 q21 ∷
   rw⁻ 40 q21 ∷
   rw⁻ 41 q21 ∷
   rw⁻ 42 q19 ∷
   rw⁻ 43 q20 ∷
   rw⁻ 44 q21 ∷
   rw⁻ 45 q21 ∷
   rw⁻ 46 q21 ∷
   rw⁻ 47 q21 ∷
   rw⁻ 48 q21 ∷
   rw⁻ 49 q21 ∷
   rw 50 q8 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw 43 q16 ∷
   rw 42 q17 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw 38 q16 ∷
   rw 37 q17 ∷
   rw 36 q16 ∷
   rw 35 q17 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q12 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q12 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q12 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q12 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   rw 25 q22 ∷
   re 24 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q12 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q12 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q12 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   rw 19 q23 ∷
   rw⁻ 18 q17 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 20 q17 ∷
   rw⁻ 21 q16 ∷
   rw⁻ 22 q15 ∷
   rw⁻ 23 q15 ∷
   rw⁻ 24 q15 ∷
   rw⁻ 25 q17 ∷
   rw⁻ 26 q16 ∷
   rw⁻ 27 q15 ∷
   rw⁻ 28 q15 ∷
   rw⁻ 29 q15 ∷
   rw⁻ 30 q15 ∷
   rw⁻ 31 q15 ∷
   rw⁻ 32 q15 ∷
   rw 35 q8 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q8 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q8 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q8 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q8 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q8 ∷
   re 39 3 (CK30 ∷ []) ∷
   rw 40 q24 ∷
   rw 43 q8 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q8 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q8 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q8 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q8 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q8 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q8 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q8 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q8 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q12 ∷
   rw⁻ 17 q19 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q20 ∷
   rw⁻ 21 q21 ∷
   rw⁻ 22 q21 ∷
   rw⁻ 23 q21 ∷
   rw⁻ 24 q19 ∷
   rw⁻ 25 q20 ∷
   rw⁻ 26 q21 ∷
   rw⁻ 27 q21 ∷
   rw⁻ 28 q21 ∷
   rw⁻ 29 q21 ∷
   rw⁻ 30 q21 ∷
   rw⁻ 31 q21 ∷
   rw 11 q18 ∷
   rw 58 q2 ∷
   rw⁻ 57 q3 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q4 ∷
   rw 57 q5 ∷
   rw⁻ 56 q4 ∷
   re 57 3 (CS13 ∷ []) ∷
   rw 57 q6 ∷
   rw 56 q3 ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q4 ∷
   rw 58 q7 ∷
   rw 59 q4 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 58 q1 ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q8 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 60 q9 ∷
   rw 59 q10 ∷
   rw 58 q11 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q12 ∷
   re 58 5 (CS03 ∷ []) ∷
   rw 60 q2 ∷
   rw⁻ 59 q3 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q4 ∷
   rw 59 q5 ∷
   rw⁻ 58 q4 ∷
   re 59 3 (CS13 ∷ []) ∷
   rw 59 q6 ∷
   rw 58 q3 ∷
   re 60 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   rw 60 q7 ∷
   rw 61 q4 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 60 q1 ∷
   rw 57 q2 ∷
   rw⁻ 56 q3 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q4 ∷
   rw 56 q5 ∷
   rw⁻ 55 q4 ∷
   re 56 3 (CS13 ∷ []) ∷
   rw 56 q6 ∷
   rw 55 q3 ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   rw 57 q7 ∷
   rw 58 q4 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q1 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q8 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 59 q9 ∷
   rw 58 q10 ∷
   rw 57 q11 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q12 ∷
   re 57 5 (CS03 ∷ []) ∷
   rw 59 q2 ∷
   rw⁻ 58 q3 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q4 ∷
   rw 58 q5 ∷
   rw⁻ 57 q4 ∷
   re 58 3 (CS13 ∷ []) ∷
   rw 58 q6 ∷
   rw 57 q3 ∷
   re 59 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   rw 59 q7 ∷
   rw 60 q4 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q1 ∷
   rw 56 q2 ∷
   rw⁻ 55 q3 ∷
   re 54 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q4 ∷
   rw 55 q25 ∷
   rw⁻ 54 q4 ∷
   re 55 3 (CK31 ∷ []) ∷
   rw 55 q26 ∷
   rw 54 q3 ∷
   re 56 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 55 q4 ∷
   rw 56 q27 ∷
   rw 57 q4 ∷
   re 55 3 (CK30 ∷ []) ∷
   rw 56 q1 ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q8 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 58 q9 ∷
   rw 57 q28 ∷
   rw 56 q11 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q12 ∷
   re 56 5 (CK30 ∷ []) ∷
   rw 58 q2 ∷
   rw⁻ 57 q3 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q4 ∷
   rw 57 q25 ∷
   rw⁻ 56 q4 ∷
   re 57 3 (CK31 ∷ []) ∷
   rw 57 q26 ∷
   rw 56 q3 ∷
   re 58 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 57 q4 ∷
   rw 58 q27 ∷
   rw 59 q4 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 58 q1 ∷
   rw 55 q2 ∷
   rw⁻ 54 q3 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q4 ∷
   rw 54 q5 ∷
   rw⁻ 53 q4 ∷
   re 54 3 (CS13 ∷ []) ∷
   rw 54 q6 ∷
   rw 53 q3 ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q4 ∷
   rw 55 q7 ∷
   rw 56 q4 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 55 q1 ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q8 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 57 q9 ∷
   rw 56 q10 ∷
   rw 55 q11 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q12 ∷
   re 55 5 (CS03 ∷ []) ∷
   rw 57 q2 ∷
   rw⁻ 56 q3 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q4 ∷
   rw 56 q5 ∷
   rw⁻ 55 q4 ∷
   re 56 3 (CS13 ∷ []) ∷
   rw 56 q6 ∷
   rw 55 q3 ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   rw 57 q7 ∷
   rw 58 q4 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q1 ∷
   rw 54 q2 ∷
   rw⁻ 53 q3 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q4 ∷
   rw 53 q5 ∷
   rw⁻ 52 q4 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 53 q6 ∷
   rw 52 q3 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q4 ∷
   rw 54 q7 ∷
   rw 55 q4 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 54 q1 ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q8 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 56 q9 ∷
   rw 55 q10 ∷
   rw 54 q11 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q12 ∷
   re 54 5 (CS03 ∷ []) ∷
   rw 56 q2 ∷
   rw⁻ 55 q3 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q4 ∷
   rw 55 q5 ∷
   rw⁻ 54 q4 ∷
   re 55 3 (CS13 ∷ []) ∷
   rw 55 q6 ∷
   rw 54 q3 ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q4 ∷
   rw 56 q7 ∷ []) Eq.refl
