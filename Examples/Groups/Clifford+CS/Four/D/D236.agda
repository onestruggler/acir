{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D236 (W : Ws) where

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
  q2 = wE 31 W
  q3 : Eqn
  q3 = wE 5 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
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
  q14 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q15 : Eqn
  q15 = eqn (CX21 ∷ S3 ∷ []) (S3 ∷ CX21 ∷ []) (low₃-comm ((CX₁₀ ↑)) (S))
  q16 : Eqn
  q16 = wE 140 W
  q17 : Eqn
  q17 = wE 630 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))

-- Bar(SSSKSS;2,3->0) passes groups of WBar(SSKSKK;~2,1->0) part3: 500 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part3 : ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part3 = derive (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ Sw23 ∷ CS02 ∷ Sw01 ∷ Sw23 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ X2 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 57 q1 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 56 q2 ∷
   rw 53 q3 ∷
   rw⁻ 52 q4 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q1 ∷
   rw 52 q5 ∷
   rw⁻ 51 q1 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 52 q6 ∷
   rw 51 q4 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   rw 53 q7 ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q2 ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q8 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 55 q9 ∷
   rw 54 q10 ∷
   rw 53 q11 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q12 ∷
   re 53 5 (CS03 ∷ []) ∷
   rw 55 q3 ∷
   rw⁻ 54 q4 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q1 ∷
   rw 54 q5 ∷
   rw⁻ 53 q1 ∷
   re 54 3 (CS13 ∷ []) ∷
   rw 54 q6 ∷
   rw 53 q4 ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   rw 55 q7 ∷
   rw 56 q1 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 55 q2 ∷
   rw 50 q13 ∷
   rw 51 q3 ∷
   rw⁻ 50 q4 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q1 ∷
   rw 50 q5 ∷
   rw⁻ 49 q1 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 50 q6 ∷
   rw 49 q4 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   rw 51 q7 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q2 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q8 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 53 q9 ∷
   rw 52 q10 ∷
   rw 51 q11 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q12 ∷
   re 51 5 (CS03 ∷ []) ∷
   rw 53 q3 ∷
   rw⁻ 52 q4 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q1 ∷
   rw 52 q5 ∷
   rw⁻ 51 q1 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 52 q6 ∷
   rw 51 q4 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   rw 53 q7 ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q2 ∷
   rw 50 q3 ∷
   rw⁻ 49 q4 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q1 ∷
   rw 49 q5 ∷
   rw⁻ 48 q1 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 49 q6 ∷
   rw 48 q4 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   rw 50 q7 ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q2 ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q8 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 52 q9 ∷
   rw 51 q10 ∷
   rw 50 q11 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q12 ∷
   re 50 5 (CS03 ∷ []) ∷
   rw 52 q3 ∷
   rw⁻ 51 q4 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q1 ∷
   rw 51 q5 ∷
   rw⁻ 50 q1 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 51 q6 ∷
   rw 50 q4 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   rw 52 q7 ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q2 ∷
   rw 49 q3 ∷
   rw⁻ 48 q4 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q1 ∷
   rw 48 q5 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 48 q6 ∷
   rw 47 q4 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   rw 49 q7 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q2 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q8 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 51 q9 ∷
   rw 50 q10 ∷
   rw 49 q11 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q12 ∷
   re 49 5 (CS03 ∷ []) ∷
   rw 51 q3 ∷
   rw⁻ 50 q4 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q1 ∷
   rw 50 q5 ∷
   rw⁻ 49 q1 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 50 q6 ∷
   rw 49 q4 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   rw 51 q7 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q2 ∷
   rw 48 q3 ∷
   rw⁻ 47 q4 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q1 ∷
   rw 47 q5 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q6 ∷
   rw 46 q4 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   rw 48 q7 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q2 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q8 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 50 q9 ∷
   rw 49 q10 ∷
   rw 48 q11 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q12 ∷
   re 48 5 (CS03 ∷ []) ∷
   rw 50 q3 ∷
   rw⁻ 49 q4 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q1 ∷
   rw 49 q5 ∷
   rw⁻ 48 q1 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 49 q6 ∷
   rw 48 q4 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   rw 50 q7 ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q2 ∷
   rw 47 q3 ∷
   rw⁻ 46 q4 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q1 ∷
   rw 46 q5 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 46 q6 ∷
   rw 45 q4 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   rw 47 q7 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q2 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q8 ∷
   re 50 3 (CX31 ∷ []) ∷
   rw 49 q9 ∷
   rw 48 q10 ∷
   rw 47 q11 ∷
   re 47 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 46 q12 ∷
   re 47 5 (CS03 ∷ []) ∷
   rw 49 q3 ∷
   rw⁻ 48 q4 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q1 ∷
   rw 48 q5 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 48 q6 ∷
   rw 47 q4 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   rw 49 q7 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q2 ∷
   rw 46 q3 ∷
   rw⁻ 45 q4 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q1 ∷
   rw 45 q5 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 45 q6 ∷
   rw 44 q4 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   rw 46 q7 ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q2 ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q8 ∷
   re 49 3 (CX31 ∷ []) ∷
   rw 48 q9 ∷
   rw 47 q10 ∷
   rw 46 q11 ∷
   re 46 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 45 q12 ∷
   re 46 5 (CS03 ∷ []) ∷
   rw 48 q3 ∷
   rw⁻ 47 q4 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q1 ∷
   rw 47 q5 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q6 ∷
   rw 46 q4 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   rw 48 q7 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q2 ∷
   rw 45 q3 ∷
   rw⁻ 44 q4 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q1 ∷
   rw 44 q5 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q6 ∷
   rw 43 q4 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 45 q7 ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q2 ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q8 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw 47 q9 ∷
   rw 46 q10 ∷
   rw 45 q11 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 44 q12 ∷
   re 45 5 (CS03 ∷ []) ∷
   rw 47 q3 ∷
   rw⁻ 46 q4 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q1 ∷
   rw 46 q5 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 46 q6 ∷
   rw 45 q4 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   rw 47 q7 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q2 ∷
   rw 44 q3 ∷
   rw⁻ 43 q4 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q1 ∷
   rw 43 q5 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q6 ∷
   rw 42 q4 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   rw 44 q7 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q2 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q8 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw 46 q9 ∷
   rw 45 q10 ∷
   rw 44 q11 ∷
   re 44 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 43 q12 ∷
   re 44 5 (CS03 ∷ []) ∷
   rw 46 q3 ∷
   rw⁻ 45 q4 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q1 ∷
   rw 45 q5 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 45 q6 ∷
   rw 44 q4 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   rw 46 q7 ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q2 ∷
   rw 43 q3 ∷
   rw⁻ 42 q4 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q1 ∷
   rw 42 q5 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q6 ∷
   rw 41 q4 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   rw 43 q7 ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q2 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q8 ∷
   re 46 3 (CX31 ∷ []) ∷
   rw 45 q9 ∷
   rw 44 q10 ∷
   rw 43 q11 ∷
   re 43 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 42 q12 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 45 q3 ∷
   rw⁻ 44 q4 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q1 ∷
   rw 44 q5 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q6 ∷
   rw 43 q4 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   rw 45 q7 ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q2 ∷
   rw⁻ 40 q14 ∷
   rw⁻ 41 q15 ∷
   rw⁻ 42 q14 ∷
   rw 41 q3 ∷
   rw⁻ 40 q4 ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q1 ∷
   rw 40 q16 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (CK31 ∷ []) ∷
   rw 40 q17 ∷
   rw 39 q4 ∷
   re 41 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   rw 41 q18 ∷
   rw 42 q1 ∷
   re 40 3 (CK30 ∷ []) ∷
   rw 41 q2 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q8 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 43 q9 ∷
   rw 42 q19 ∷
   rw 41 q11 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   re 41 5 (CK30 ∷ []) ∷
   rw 43 q3 ∷
   rw⁻ 42 q4 ∷
   re 41 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q1 ∷
   rw 42 q16 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (CK31 ∷ []) ∷
   rw 42 q17 ∷
   rw 41 q4 ∷
   re 43 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   rw 43 q18 ∷
   rw 44 q1 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 43 q2 ∷
   rw 40 q3 ∷
   rw⁻ 39 q4 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q1 ∷
   rw 39 q5 ∷
   rw⁻ 38 q1 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q6 ∷
   rw 38 q4 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   rw 40 q7 ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q2 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q8 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 42 q9 ∷
   rw 41 q10 ∷
   rw 40 q11 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q3 ∷
   rw⁻ 41 q4 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q1 ∷
   rw 41 q5 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q6 ∷
   rw 40 q4 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   rw 42 q7 ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q2 ∷
   rw 39 q3 ∷
   rw⁻ 38 q4 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q1 ∷
   rw 38 q5 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q6 ∷
   rw 37 q4 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   rw 39 q7 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q2 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q8 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 41 q9 ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q3 ∷ []) Eq.refl
