{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D237 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 629 W
  q5 : Eqn
  q5 = wE 27 W
  q6 : Eqn
  q6 = wE 31 W
  q7 : Eqn
  q7 = wE 5 W
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
  q15 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q16 : Eqn
  q16 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q17 : Eqn
  q17 = wE 568 W
  q18 : Eqn
  q18 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q19 : Eqn
  q19 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q20 : Eqn
  q20 = wE 464 W
  q21 : Eqn
  q21 = wE 569 W
  q22 : Eqn
  q22 = wE 151 W

-- Bar(SSSKSS;2,3->0) passes groups of WBar(SSKSKK;~2,1->0) part4: 305 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part4 : ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part4 = derive (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw⁻ 40 q1 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q2 ∷
   rw 40 q3 ∷
   rw⁻ 39 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q4 ∷
   rw 39 q1 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   rw 41 q5 ∷
   rw 42 q2 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q6 ∷
   rw 38 q7 ∷
   rw⁻ 37 q1 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q2 ∷
   rw 37 q3 ∷
   rw⁻ 36 q2 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q4 ∷
   rw 36 q1 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 38 q5 ∷
   rw 39 q2 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q6 ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q8 ∷
   re 41 3 (CX31 ∷ []) ∷
   rw 40 q9 ∷
   rw 39 q10 ∷
   rw 38 q11 ∷
   re 38 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q12 ∷
   re 38 5 (CS03 ∷ []) ∷
   rw 40 q7 ∷
   rw⁻ 39 q1 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q2 ∷
   rw 39 q3 ∷
   rw⁻ 38 q2 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q4 ∷
   rw 38 q1 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q5 ∷
   rw 41 q2 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q6 ∷
   rw 37 q7 ∷
   rw⁻ 36 q1 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q2 ∷
   rw 36 q3 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q4 ∷
   rw 35 q1 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q5 ∷
   rw 38 q2 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q6 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q8 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q9 ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   re 37 5 (CS03 ∷ []) ∷
   rw 39 q7 ∷
   rw⁻ 38 q1 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q2 ∷
   rw 38 q3 ∷
   rw⁻ 37 q2 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q4 ∷
   rw 37 q1 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   rw 39 q5 ∷
   rw 40 q2 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q6 ∷
   rw 36 q7 ∷
   rw⁻ 35 q1 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q2 ∷
   rw 35 q3 ∷
   rw⁻ 34 q2 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 35 q4 ∷
   rw 34 q1 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q5 ∷
   rw 37 q2 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q6 ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q8 ∷
   re 39 3 (CX31 ∷ []) ∷
   rw 38 q9 ∷
   rw 37 q10 ∷
   rw 36 q11 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q12 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 38 q7 ∷
   rw⁻ 37 q1 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q2 ∷
   rw 37 q3 ∷
   rw⁻ 36 q2 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q4 ∷
   rw 36 q1 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 38 q5 ∷
   rw 39 q2 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 38 q6 ∷
   rw 35 q7 ∷
   rw⁻ 34 q1 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q2 ∷
   rw 34 q3 ∷
   rw⁻ 33 q2 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q4 ∷
   rw 33 q1 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   rw 35 q5 ∷
   rw 36 q2 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q6 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q8 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q9 ∷
   rw 36 q10 ∷
   rw 35 q11 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 37 q7 ∷
   rw⁻ 36 q1 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q2 ∷
   rw 36 q3 ∷
   rw⁻ 35 q2 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 36 q4 ∷
   rw 35 q1 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q5 ∷
   rw 38 q2 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q6 ∷
   rw 32 q13 ∷
   rw 26 q14 ∷
   rw 66 q8 ∷
   rw 65 q15 ∷
   rw 64 q15 ∷
   rw 63 q16 ∷
   rw 62 q15 ∷
   rw 61 q16 ∷
   rw 60 q16 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q12 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q12 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 59 q12 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q12 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q12 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q12 ∷
   rw 55 q17 ∷
   rw⁻ 54 q16 ∷
   rw⁻ 55 q16 ∷
   rw⁻ 56 q15 ∷
   rw⁻ 57 q16 ∷
   rw⁻ 58 q15 ∷
   rw⁻ 59 q15 ∷
   rw 62 q8 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q8 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q8 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q8 ∷
   re 63 3 (CK30 ∷ []) ∷
   rw 66 q8 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q8 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 66 q12 ∷
   rw⁻ 53 q18 ∷
   rw⁻ 54 q18 ∷
   rw⁻ 55 q19 ∷
   rw⁻ 56 q18 ∷
   rw⁻ 57 q19 ∷
   rw⁻ 58 q19 ∷
   rw 59 q8 ∷
   rw 58 q15 ∷
   rw 57 q15 ∷
   rw 56 q16 ∷
   rw 55 q15 ∷
   rw 54 q16 ∷
   rw 53 q16 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q12 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q12 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q12 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q12 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q12 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q12 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q12 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q12 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q12 ∷
   rw 43 q20 ∷
   re 42 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 44 q12 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q12 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q12 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q12 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   rw 37 q21 ∷
   rw⁻ 36 q16 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 38 q15 ∷
   rw⁻ 39 q16 ∷
   rw⁻ 40 q15 ∷
   rw⁻ 41 q15 ∷
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
   re 48 3 (CK30 ∷ []) ∷
   rw 49 q22 ∷
   rw 52 q8 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q8 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 54 q8 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 55 q8 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 56 q8 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 57 q8 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 58 q8 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 59 q8 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 60 q8 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q12 ∷
   rw⁻ 35 q18 ∷
   rw⁻ 36 q18 ∷
   rw⁻ 37 q19 ∷
   rw⁻ 38 q18 ∷
   rw⁻ 39 q19 ∷
   rw⁻ 40 q19 ∷
   rw 29 q17 ∷ []) Eq.refl
