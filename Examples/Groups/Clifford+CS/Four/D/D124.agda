{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D124 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 629 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q4 : Eqn
  q4 = wE 27 W
  q5 : Eqn
  q5 = wE 31 W
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 113 W
  q8 : Eqn
  q8 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q9 : Eqn
  q9 = wE 114 W
  q10 : Eqn
  q10 = wE 3 W
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 630 W
  q17 : Eqn
  q17 = wE 142 W
  q18 : Eqn
  q18 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q19 : Eqn
  q19 = wE 673 W
  q20 : Eqn
  q20 = wE 488 W
  q21 : Eqn
  q21 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q23 : Eqn
  q23 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q24 : Eqn
  q24 = wE 678 W
  q25 : Eqn
  q25 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))

-- Bar(SSKSKK;2,3->0) passes groups of WBar(SSSKSS;~2,1->0) part1: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part1 : ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX23 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part1 = derive (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CX21 ∷ X2 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX23 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw⁻ 28 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 30 q4 ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q5 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q7 ∷
   rw 31 q8 ∷
   rw 30 q9 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q10 ∷
   re 30 5 (CS03 ∷ []) ∷
   rw 32 q11 ∷
   rw⁻ 31 q3 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q1 ∷
   rw 31 q12 ∷
   rw⁻ 30 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   rw 32 q4 ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q5 ∷
   rw 29 q11 ∷
   rw⁻ 28 q3 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q1 ∷
   rw 28 q12 ∷
   rw⁻ 27 q1 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   rw 29 q4 ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q5 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 31 q7 ∷
   rw 30 q8 ∷
   rw 29 q9 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q10 ∷
   re 29 5 (CS03 ∷ []) ∷
   rw 31 q11 ∷
   rw⁻ 30 q3 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q1 ∷
   rw 30 q12 ∷
   rw⁻ 29 q1 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   rw 31 q4 ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 31 q5 ∷
   rw 28 q11 ∷
   rw⁻ 27 q3 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q1 ∷
   rw 27 q12 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   rw 28 q4 ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q5 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 30 q7 ∷
   rw 29 q8 ∷
   rw 28 q9 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q10 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 30 q11 ∷
   rw⁻ 29 q3 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q1 ∷
   rw 29 q12 ∷
   rw⁻ 28 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 30 q4 ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q5 ∷
   rw 27 q11 ∷
   rw⁻ 26 q3 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q1 ∷
   rw 26 q12 ∷
   rw⁻ 25 q1 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q2 ∷
   rw 25 q3 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   rw 27 q4 ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q5 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 29 q7 ∷
   rw 28 q8 ∷
   rw 27 q9 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q10 ∷
   re 27 5 (CS03 ∷ []) ∷
   rw 29 q11 ∷
   rw⁻ 28 q3 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q1 ∷
   rw 28 q12 ∷
   rw⁻ 27 q1 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   rw 29 q4 ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q5 ∷
   rw 26 q11 ∷
   rw⁻ 25 q3 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q1 ∷
   rw 25 q12 ∷
   rw⁻ 24 q1 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   rw 26 q4 ∷
   rw 27 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q5 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 28 q7 ∷
   rw 27 q8 ∷
   rw 26 q9 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q10 ∷
   re 26 5 (CS03 ∷ []) ∷
   rw 28 q11 ∷
   rw⁻ 27 q3 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q1 ∷
   rw 27 q12 ∷
   rw⁻ 26 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   rw 28 q4 ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q5 ∷
   rw⁻ 23 q13 ∷
   rw⁻ 24 q14 ∷
   rw⁻ 25 q13 ∷
   rw 24 q11 ∷
   rw⁻ 23 q3 ∷
   re 22 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q1 ∷
   rw 23 q15 ∷
   rw⁻ 22 q1 ∷
   re 23 3 (CK31 ∷ []) ∷
   rw 23 q16 ∷
   rw 22 q3 ∷
   re 24 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   rw 24 q17 ∷
   rw 25 q1 ∷
   re 23 3 (CK30 ∷ []) ∷
   rw 24 q5 ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw 26 q7 ∷
   rw 25 q18 ∷
   rw 24 q9 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q10 ∷
   re 24 5 (CK30 ∷ []) ∷
   rw 26 q11 ∷
   rw⁻ 25 q3 ∷
   re 24 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q1 ∷
   rw 25 q15 ∷
   rw⁻ 24 q1 ∷
   re 25 3 (CK31 ∷ []) ∷
   rw 25 q16 ∷
   rw 24 q3 ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   rw 26 q17 ∷
   rw 27 q1 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 26 q5 ∷
   rw 23 q11 ∷
   rw⁻ 22 q3 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q1 ∷
   rw 22 q12 ∷
   rw⁻ 21 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   rw 23 q4 ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q5 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 25 q7 ∷
   rw 24 q8 ∷
   rw 23 q9 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q10 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 25 q11 ∷
   rw⁻ 24 q3 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q1 ∷
   rw 24 q12 ∷
   rw⁻ 23 q1 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 25 q4 ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q5 ∷
   rw 22 q11 ∷
   rw⁻ 21 q3 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q1 ∷
   rw 21 q12 ∷
   rw⁻ 20 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   rw 22 q4 ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q5 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 24 q7 ∷
   rw 23 q8 ∷
   rw 22 q9 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q10 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q11 ∷
   rw⁻ 23 q3 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q1 ∷
   rw 23 q12 ∷
   rw⁻ 22 q1 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q2 ∷
   rw 22 q3 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   rw 24 q4 ∷
   rw 25 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q5 ∷
   rw 21 q11 ∷
   rw⁻ 20 q3 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q1 ∷
   rw 20 q12 ∷
   rw⁻ 19 q1 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   rw 21 q4 ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q5 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 23 q7 ∷
   rw 22 q8 ∷
   rw 21 q9 ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q10 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q11 ∷
   rw⁻ 22 q3 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q1 ∷
   rw 22 q12 ∷
   rw⁻ 21 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   rw 23 q4 ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q5 ∷
   rw⁻ 18 q13 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 20 q13 ∷
   rw 19 q11 ∷
   rw⁻ 18 q3 ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q1 ∷
   rw 18 q15 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (CK31 ∷ []) ∷
   rw 18 q16 ∷
   rw 17 q3 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   rw 19 q17 ∷
   rw 20 q1 ∷
   re 18 3 (CK30 ∷ []) ∷
   rw 19 q5 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 21 q7 ∷
   rw 20 q18 ∷
   rw 19 q9 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q10 ∷
   re 19 5 (CK30 ∷ []) ∷
   rw 21 q11 ∷
   rw⁻ 20 q3 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q1 ∷
   rw 20 q15 ∷
   rw⁻ 19 q1 ∷
   re 20 3 (CK31 ∷ []) ∷
   rw 20 q16 ∷
   rw 19 q3 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   rw 21 q17 ∷
   rw 22 q1 ∷
   re 20 3 (CK30 ∷ []) ∷
   rw 21 q5 ∷
   rw⁻ 16 q13 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 18 q13 ∷
   rw 17 q11 ∷
   rw⁻ 16 q3 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q1 ∷
   rw 16 q15 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (CK31 ∷ []) ∷
   rw 16 q16 ∷
   rw 15 q3 ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   rw 17 q17 ∷
   rw 18 q1 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q5 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 20 3 (CX31 ∷ []) ∷
   rw 19 q7 ∷
   rw 18 q18 ∷
   rw 17 q9 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q10 ∷
   re 17 5 (CK30 ∷ []) ∷
   rw 19 q11 ∷
   rw⁻ 18 q3 ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q1 ∷
   rw 18 q15 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (CK31 ∷ []) ∷
   rw 18 q16 ∷
   rw 17 q3 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   rw 19 q17 ∷
   rw 20 q1 ∷
   re 18 3 (CK30 ∷ []) ∷
   rw 19 q5 ∷
   rw 14 q19 ∷
   rw 8 q20 ∷
   rw 57 q6 ∷
   rw 56 q21 ∷
   rw 55 q21 ∷
   rw 54 q21 ∷
   rw 53 q21 ∷
   rw 52 q21 ∷
   rw 51 q21 ∷
   rw 50 q21 ∷
   rw 49 q21 ∷
   rw 48 q21 ∷
   rw 47 q22 ∷
   rw 46 q23 ∷
   rw 45 q21 ∷
   rw 44 q21 ∷
   rw 43 q21 ∷
   rw 42 q21 ∷
   rw 41 q21 ∷
   rw 40 q21 ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 41 q10 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 40 q10 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q10 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 38 q10 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q10 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q10 ∷
   rw 35 q24 ∷
   rw⁻ 34 q21 ∷
   rw⁻ 35 q21 ∷
   rw⁻ 36 q21 ∷
   rw⁻ 37 q21 ∷
   rw⁻ 38 q21 ∷
   rw⁻ 39 q21 ∷
   rw⁻ 40 q23 ∷
   rw⁻ 41 q22 ∷
   rw⁻ 42 q21 ∷
   rw⁻ 43 q21 ∷
   rw⁻ 44 q21 ∷
   rw⁻ 45 q21 ∷
   rw⁻ 46 q21 ∷
   rw⁻ 47 q21 ∷
   rw⁻ 48 q21 ∷
   rw⁻ 49 q21 ∷
   rw⁻ 50 q21 ∷
   rw 53 q6 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 54 q6 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 55 q6 ∷
   re 53 3 (CK30 ∷ []) ∷
   rw 56 q6 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 57 q6 ∷
   re 55 3 (CK30 ∷ []) ∷
   rw 58 q6 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 57 q10 ∷
   rw⁻ 33 q25 ∷
   rw⁻ 34 q25 ∷
   rw⁻ 35 q25 ∷
   rw⁻ 36 q25 ∷ []) Eq.refl
