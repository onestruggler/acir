{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D130 (W : Ws) where

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
  q21 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q22 : Eqn
  q22 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q23 : Eqn
  q23 = wE 507 W
  q24 : Eqn
  q24 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q25 : Eqn
  q25 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q26 : Eqn
  q26 = wE 464 W
  q27 : Eqn
  q27 = wE 508 W
  q28 : Eqn
  q28 = wE 151 W

-- Bar(SSKSKK;2,3->0) passes groups of WBar(SSKSKK;~2,1->0) part3: 445 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part3 : ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~21-⟶0⟩-part3 = derive (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ X2 ∷ CS03 ∷ Sw01 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 48 q1 ∷
   rw 45 q2 ∷
   rw⁻ 44 q3 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q4 ∷
   rw 44 q5 ∷
   rw⁻ 43 q4 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q6 ∷
   rw 43 q3 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q4 ∷
   rw 45 q7 ∷
   rw 46 q4 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q1 ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q8 ∷
   re 48 3 (CX31 ∷ []) ∷
   rw 47 q9 ∷
   rw 46 q10 ∷
   rw 45 q11 ∷
   re 45 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 44 q12 ∷
   re 45 5 (CS03 ∷ []) ∷
   rw 47 q2 ∷
   rw⁻ 46 q3 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q4 ∷
   rw 46 q5 ∷
   rw⁻ 45 q4 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 46 q6 ∷
   rw 45 q3 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q4 ∷
   rw 47 q7 ∷
   rw 48 q4 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q3 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q4 ∷
   rw 43 q5 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q6 ∷
   rw 42 q3 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   rw 44 q7 ∷
   rw 45 q4 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q8 ∷
   re 47 3 (CX31 ∷ []) ∷
   rw 46 q9 ∷
   rw 45 q10 ∷
   rw 44 q11 ∷
   re 44 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 43 q12 ∷
   re 44 5 (CS03 ∷ []) ∷
   rw 46 q2 ∷
   rw⁻ 45 q3 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q4 ∷
   rw 45 q5 ∷
   rw⁻ 44 q4 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 45 q6 ∷
   rw 44 q3 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q4 ∷
   rw 46 q7 ∷
   rw 47 q4 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q1 ∷
   rw⁻ 41 q13 ∷
   rw⁻ 42 q14 ∷
   rw⁻ 43 q13 ∷
   rw 42 q2 ∷
   rw⁻ 41 q3 ∷
   re 40 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q4 ∷
   rw 41 q15 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (CK31 ∷ []) ∷
   rw 41 q16 ∷
   rw 40 q3 ∷
   re 42 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   rw 42 q17 ∷
   rw 43 q4 ∷
   re 41 3 (CK30 ∷ []) ∷
   rw 42 q1 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q8 ∷
   re 45 3 (CX31 ∷ []) ∷
   rw 44 q9 ∷
   rw 43 q18 ∷
   rw 42 q11 ∷
   re 42 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 41 q12 ∷
   re 42 5 (CK30 ∷ []) ∷
   rw 44 q2 ∷
   rw⁻ 43 q3 ∷
   re 42 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q4 ∷
   rw 43 q15 ∷
   rw⁻ 42 q4 ∷
   re 43 3 (CK31 ∷ []) ∷
   rw 43 q16 ∷
   rw 42 q3 ∷
   re 44 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   rw 44 q17 ∷
   rw 45 q4 ∷
   re 43 3 (CK30 ∷ []) ∷
   rw 44 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q3 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   rw 41 q7 ∷
   rw 42 q4 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q8 ∷
   re 44 3 (CX31 ∷ []) ∷
   rw 43 q9 ∷
   rw 42 q10 ∷
   rw 41 q11 ∷
   re 41 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   re 41 5 (CS03 ∷ []) ∷
   rw 43 q2 ∷
   rw⁻ 42 q3 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q4 ∷
   rw 42 q5 ∷
   rw⁻ 41 q4 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q6 ∷
   rw 41 q3 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q4 ∷
   rw 43 q7 ∷
   rw 44 q4 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q3 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q4 ∷
   rw 39 q5 ∷
   rw⁻ 38 q4 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw 39 q6 ∷
   rw 38 q3 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   rw 40 q7 ∷
   rw 41 q4 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q1 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q8 ∷
   re 43 3 (CX31 ∷ []) ∷
   rw 42 q9 ∷
   rw 41 q10 ∷
   rw 40 q11 ∷
   re 40 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   re 40 5 (CS03 ∷ []) ∷
   rw 42 q2 ∷
   rw⁻ 41 q3 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q4 ∷
   rw 41 q5 ∷
   rw⁻ 40 q4 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q6 ∷
   rw 40 q3 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   rw 42 q7 ∷
   rw 43 q4 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   rw 39 q2 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q4 ∷
   rw 38 q5 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (CS13 ∷ []) ∷
   rw 38 q6 ∷
   rw 37 q3 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   rw 39 q7 ∷
   rw 40 q4 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 39 q1 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q8 ∷
   re 42 3 (CX31 ∷ []) ∷
   rw 41 q9 ∷
   rw 40 q10 ∷
   rw 39 q11 ∷
   re 39 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw 41 q2 ∷
   rw⁻ 40 q3 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q4 ∷
   rw 40 q5 ∷
   rw⁻ 39 q4 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q6 ∷
   rw 39 q3 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   rw 41 q7 ∷
   rw 42 q4 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   rw⁻ 36 q13 ∷
   rw⁻ 37 q14 ∷
   rw⁻ 38 q13 ∷
   rw 37 q2 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q4 ∷
   rw 36 q15 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 36 q16 ∷
   rw 35 q3 ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   rw 37 q17 ∷
   rw 38 q4 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q1 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q8 ∷
   re 40 3 (CX31 ∷ []) ∷
   rw 39 q9 ∷
   rw 38 q18 ∷
   rw 37 q11 ∷
   re 37 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   re 37 5 (CK30 ∷ []) ∷
   rw 39 q2 ∷
   rw⁻ 38 q3 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q4 ∷
   rw 38 q15 ∷
   rw⁻ 37 q4 ∷
   re 38 3 (CK31 ∷ []) ∷
   rw 38 q16 ∷
   rw 37 q3 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   rw 39 q17 ∷
   rw 40 q4 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q1 ∷
   rw⁻ 34 q13 ∷
   rw⁻ 35 q14 ∷
   rw⁻ 36 q13 ∷
   rw 35 q2 ∷
   rw⁻ 34 q3 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q4 ∷
   rw 34 q15 ∷
   rw⁻ 33 q4 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw 34 q16 ∷
   rw 33 q3 ∷
   re 35 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 34 q4 ∷
   rw 35 q17 ∷
   rw 36 q4 ∷
   re 34 3 (CK30 ∷ []) ∷
   rw 35 q1 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q8 ∷
   re 38 3 (CX31 ∷ []) ∷
   rw 37 q9 ∷
   rw 36 q18 ∷
   rw 35 q11 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 35 5 (CK30 ∷ []) ∷
   rw 37 q2 ∷
   rw⁻ 36 q3 ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q4 ∷
   rw 36 q15 ∷
   rw⁻ 35 q4 ∷
   re 36 3 (CK31 ∷ []) ∷
   rw 36 q16 ∷
   rw 35 q3 ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q4 ∷
   rw 37 q17 ∷
   rw 38 q4 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q1 ∷
   rw 32 q19 ∷
   rw 26 q20 ∷
   rw 64 q8 ∷
   rw 63 q21 ∷
   rw 62 q21 ∷
   rw 61 q22 ∷
   rw 60 q21 ∷
   rw 59 q22 ∷
   rw 58 q22 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 59 q12 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q12 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q12 ∷
   re 54 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 56 q12 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q12 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q12 ∷
   rw 53 q23 ∷
   rw⁻ 52 q22 ∷
   rw⁻ 53 q22 ∷
   rw⁻ 54 q21 ∷
   rw⁻ 55 q22 ∷
   rw⁻ 56 q21 ∷
   rw⁻ 57 q21 ∷
   rw 60 q8 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 61 q8 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 62 q8 ∷
   re 60 3 (CK30 ∷ []) ∷
   rw 63 q8 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q8 ∷
   re 62 3 (CK30 ∷ []) ∷
   rw 65 q8 ∷
   re 63 3 (CK30 ∷ []) ∷
   rw 64 q12 ∷
   rw⁻ 51 q24 ∷
   rw⁻ 52 q24 ∷
   rw⁻ 53 q25 ∷
   rw⁻ 54 q24 ∷
   rw⁻ 55 q25 ∷
   rw⁻ 56 q25 ∷
   rw 57 q8 ∷
   rw 56 q21 ∷
   rw 55 q21 ∷
   rw 54 q22 ∷
   rw 53 q21 ∷
   rw 52 q22 ∷
   rw 51 q22 ∷
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
   rw 44 q26 ∷
   re 43 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 45 q12 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q12 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q12 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q12 ∷
   rw 39 q26 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   rw 37 q26 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 38 q12 ∷
   rw 37 q27 ∷
   rw⁻ 36 q22 ∷
   rw⁻ 37 q22 ∷
   rw⁻ 38 q21 ∷
   rw⁻ 39 q22 ∷
   rw⁻ 40 q21 ∷
   rw⁻ 41 q21 ∷
   rw 44 q8 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 43 q28 ∷
   rw 46 q8 ∷
   re 44 3 (CK30 ∷ []) ∷
   rw 45 q28 ∷
   rw 48 q8 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q8 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q8 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q8 ∷
   re 49 3 (CK30 ∷ []) ∷
   rw 50 q28 ∷
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
   rw 57 q12 ∷
   rw⁻ 35 q24 ∷
   rw⁻ 36 q24 ∷
   rw⁻ 37 q25 ∷
   rw⁻ 38 q24 ∷
   rw⁻ 39 q25 ∷
   rw⁻ 40 q25 ∷
   rw 29 q23 ∷ []) Eq.refl
