{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D125 (W : Ws) where

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
  q1 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q2 : Eqn
  q2 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q3 : Eqn
  q3 = eqn (S1 ∷ CX23 ∷ []) (CX23 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₀₁))
  q4 : Eqn
  q4 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q8 : Eqn
  q8 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q9 : Eqn
  q9 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q10 : Eqn
  q10 = eqn (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) (wn 679 W)
  q11 : Eqn
  q11 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)
  q12 : Eqn
  q12 = eqn (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ []) (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 678 W)
  q13 : Eqn
  q13 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q17 : Eqn
  q17 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q20 : Eqn
  q20 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q21 : Eqn
  q21 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q22 : Eqn
  q22 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q23 : Eqn
  q23 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q24 : Eqn
  q24 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q26 : Eqn
  q26 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q27 : Eqn
  q27 = eqn (CX23 ∷ X2 ∷ CX21 ∷ X2 ∷ []) (X2 ∷ CX21 ∷ X2 ∷ CX23 ∷ []) (wn 673 W)

-- Bar(SSKSKK;2,3->0) passes groups of WBar(SSSKSS;~2,1->0) part2: 500 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part2 : ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX23 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-groups-of-WBar⟨SSSKSS~21-⟶0⟩-part2 = derive (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX23 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ X2 ∷ X2 ∷ CX21 ∷ X2 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ X2 ∷ CX21 ∷ CS03 ∷ Sw01 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw⁻ 37 q1 ∷
   rw⁻ 38 q1 ∷
   rw⁻ 39 q2 ∷
   rw⁻ 40 q3 ∷
   rw⁻ 41 q1 ∷
   rw⁻ 42 q1 ∷
   rw⁻ 43 q1 ∷
   rw⁻ 44 q1 ∷
   rw⁻ 45 q1 ∷
   rw⁻ 46 q1 ∷
   rw⁻ 47 q1 ∷
   rw⁻ 48 q1 ∷
   rw⁻ 49 q1 ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   rw 48 q5 ∷
   rw 47 q5 ∷
   rw 46 q5 ∷
   rw 45 q5 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw 41 q5 ∷
   rw 40 q6 ∷
   rw 39 q7 ∷
   rw 38 q5 ∷
   rw 37 q5 ∷
   rw 36 q5 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw 33 q5 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q8 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q8 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q8 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q8 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q8 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q8 ∷
   rw 26 q9 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q8 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q8 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q8 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q8 ∷
   rw 21 q9 ∷
   re 20 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 22 q8 ∷
   rw 19 q9 ∷
   re 18 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   rw 19 q10 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q5 ∷
   rw⁻ 33 q5 ∷
   rw⁻ 34 q5 ∷
   rw 37 q4 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 36 q11 ∷
   rw 39 q4 ∷
   re 37 3 (CK30 ∷ []) ∷
   rw 38 q11 ∷
   rw 41 q4 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q4 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q4 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q4 ∷
   re 42 3 (CK30 ∷ []) ∷
   rw 43 q11 ∷
   rw 46 q4 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q4 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q4 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q4 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q4 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q4 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q8 ∷
   rw⁻ 17 q1 ∷
   rw⁻ 18 q1 ∷
   rw⁻ 19 q1 ∷
   rw⁻ 20 q1 ∷
   rw⁻ 21 q1 ∷
   rw⁻ 22 q1 ∷
   rw⁻ 23 q2 ∷
   rw⁻ 24 q3 ∷
   rw⁻ 25 q1 ∷
   rw⁻ 26 q1 ∷
   rw⁻ 27 q1 ∷
   rw⁻ 28 q1 ∷
   rw⁻ 29 q1 ∷
   rw⁻ 30 q1 ∷
   rw⁻ 31 q1 ∷
   rw⁻ 32 q1 ∷
   rw⁻ 33 q1 ∷
   rw 11 q12 ∷
   rw 58 q13 ∷
   rw⁻ 57 q14 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q15 ∷
   rw 57 q16 ∷
   rw⁻ 56 q15 ∷
   re 57 3 (CK31 ∷ []) ∷
   rw 57 q17 ∷
   rw 56 q14 ∷
   re 58 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 57 q15 ∷
   rw 58 q18 ∷
   rw 59 q15 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 58 q19 ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   re 61 3 (CX31 ∷ []) ∷
   rw 60 q20 ∷
   rw 59 q21 ∷
   rw 58 q22 ∷
   re 58 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 57 q8 ∷
   re 58 5 (CK30 ∷ []) ∷
   rw 60 q13 ∷
   rw⁻ 59 q14 ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q15 ∷
   rw 59 q16 ∷
   rw⁻ 58 q15 ∷
   re 59 3 (CK31 ∷ []) ∷
   rw 59 q17 ∷
   rw 58 q14 ∷
   re 60 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 59 q15 ∷
   rw 60 q18 ∷
   rw 61 q15 ∷
   re 59 3 (CK30 ∷ []) ∷
   rw 60 q19 ∷
   rw 57 q13 ∷
   rw⁻ 56 q14 ∷
   re 55 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q15 ∷
   rw 56 q16 ∷
   rw⁻ 55 q15 ∷
   re 56 3 (CK31 ∷ []) ∷
   rw 56 q17 ∷
   rw 55 q14 ∷
   re 57 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 56 q15 ∷
   rw 57 q18 ∷
   rw 58 q15 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 57 q19 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q4 ∷
   re 60 3 (CX31 ∷ []) ∷
   rw 59 q20 ∷
   rw 58 q21 ∷
   rw 57 q22 ∷
   re 57 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 56 q8 ∷
   re 57 5 (CK30 ∷ []) ∷
   rw 59 q13 ∷
   rw⁻ 58 q14 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q15 ∷
   rw 58 q16 ∷
   rw⁻ 57 q15 ∷
   re 58 3 (CK31 ∷ []) ∷
   rw 58 q17 ∷
   rw 57 q14 ∷
   re 59 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 58 q15 ∷
   rw 59 q18 ∷
   rw 60 q15 ∷
   re 58 3 (CK30 ∷ []) ∷
   rw 59 q19 ∷
   rw 56 q13 ∷
   rw⁻ 55 q14 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q15 ∷
   rw 55 q23 ∷
   rw⁻ 54 q15 ∷
   re 55 3 (CS13 ∷ []) ∷
   rw 55 q24 ∷
   rw 54 q14 ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q15 ∷
   rw 56 q25 ∷
   rw 57 q15 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 56 q19 ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 58 q20 ∷
   rw 57 q26 ∷
   rw 56 q22 ∷
   re 56 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 55 q8 ∷
   re 56 5 (CS03 ∷ []) ∷
   rw 58 q13 ∷
   rw⁻ 57 q14 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q15 ∷
   rw 57 q23 ∷
   rw⁻ 56 q15 ∷
   re 57 3 (CS13 ∷ []) ∷
   rw 57 q24 ∷
   rw 56 q14 ∷
   re 58 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 57 q15 ∷
   rw 58 q25 ∷
   rw 59 q15 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 58 q19 ∷
   rw 55 q13 ∷
   rw⁻ 54 q14 ∷
   re 53 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q15 ∷
   rw 54 q16 ∷
   rw⁻ 53 q15 ∷
   re 54 3 (CK31 ∷ []) ∷
   rw 54 q17 ∷
   rw 53 q14 ∷
   re 55 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 54 q15 ∷
   rw 55 q18 ∷
   rw 56 q15 ∷
   re 54 3 (CK30 ∷ []) ∷
   rw 55 q19 ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q4 ∷
   re 58 3 (CX31 ∷ []) ∷
   rw 57 q20 ∷
   rw 56 q21 ∷
   rw 55 q22 ∷
   re 55 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 54 q8 ∷
   re 55 5 (CK30 ∷ []) ∷
   rw 57 q13 ∷
   rw⁻ 56 q14 ∷
   re 55 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q15 ∷
   rw 56 q16 ∷
   rw⁻ 55 q15 ∷
   re 56 3 (CK31 ∷ []) ∷
   rw 56 q17 ∷
   rw 55 q14 ∷
   re 57 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 56 q15 ∷
   rw 57 q18 ∷
   rw 58 q15 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 57 q19 ∷
   rw 54 q13 ∷
   rw⁻ 53 q14 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q15 ∷
   rw 53 q23 ∷
   rw⁻ 52 q15 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 53 q24 ∷
   rw 52 q14 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q15 ∷
   rw 54 q25 ∷
   rw 55 q15 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 54 q19 ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   re 57 3 (CX31 ∷ []) ∷
   rw 56 q20 ∷
   rw 55 q26 ∷
   rw 54 q22 ∷
   re 54 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 53 q8 ∷
   re 54 5 (CS03 ∷ []) ∷
   rw 56 q13 ∷
   rw⁻ 55 q14 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q15 ∷
   rw 55 q23 ∷
   rw⁻ 54 q15 ∷
   re 55 3 (CS13 ∷ []) ∷
   rw 55 q24 ∷
   rw 54 q14 ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q15 ∷
   rw 56 q25 ∷
   rw 57 q15 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 56 q19 ∷
   rw 53 q13 ∷
   rw⁻ 52 q14 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q15 ∷
   rw 52 q23 ∷
   rw⁻ 51 q15 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 52 q24 ∷
   rw 51 q14 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q15 ∷
   rw 53 q25 ∷
   rw 54 q15 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q19 ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q4 ∷
   re 56 3 (CX31 ∷ []) ∷
   rw 55 q20 ∷
   rw 54 q26 ∷
   rw 53 q22 ∷
   re 53 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 52 q8 ∷
   re 53 5 (CS03 ∷ []) ∷
   rw 55 q13 ∷
   rw⁻ 54 q14 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q15 ∷
   rw 54 q23 ∷
   rw⁻ 53 q15 ∷
   re 54 3 (CS13 ∷ []) ∷
   rw 54 q24 ∷
   rw 53 q14 ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q15 ∷
   rw 55 q25 ∷
   rw 56 q15 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 55 q19 ∷
   rw 50 q27 ∷
   rw 51 q13 ∷
   rw⁻ 50 q14 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q15 ∷
   rw 50 q23 ∷
   rw⁻ 49 q15 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 50 q24 ∷
   rw 49 q14 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q15 ∷
   rw 51 q25 ∷
   rw 52 q15 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q19 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q4 ∷
   re 54 3 (CX31 ∷ []) ∷
   rw 53 q20 ∷
   rw 52 q26 ∷
   rw 51 q22 ∷
   re 51 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 50 q8 ∷
   re 51 5 (CS03 ∷ []) ∷
   rw 53 q13 ∷
   rw⁻ 52 q14 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q15 ∷
   rw 52 q23 ∷
   rw⁻ 51 q15 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 52 q24 ∷
   rw 51 q14 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q15 ∷
   rw 53 q25 ∷
   rw 54 q15 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q19 ∷
   rw 50 q13 ∷
   rw⁻ 49 q14 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q15 ∷
   rw 49 q23 ∷
   rw⁻ 48 q15 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 49 q24 ∷
   rw 48 q14 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q15 ∷
   rw 50 q25 ∷
   rw 51 q15 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q19 ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q4 ∷
   re 53 3 (CX31 ∷ []) ∷
   rw 52 q20 ∷
   rw 51 q26 ∷
   rw 50 q22 ∷
   re 50 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 49 q8 ∷
   re 50 5 (CS03 ∷ []) ∷
   rw 52 q13 ∷
   rw⁻ 51 q14 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q15 ∷
   rw 51 q23 ∷
   rw⁻ 50 q15 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 51 q24 ∷
   rw 50 q14 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q15 ∷
   rw 52 q25 ∷
   rw 53 q15 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q19 ∷
   rw 49 q13 ∷
   rw⁻ 48 q14 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q15 ∷
   rw 48 q23 ∷
   rw⁻ 47 q15 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 48 q24 ∷
   rw 47 q14 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q15 ∷
   rw 49 q25 ∷
   rw 50 q15 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q19 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q4 ∷
   re 52 3 (CX31 ∷ []) ∷
   rw 51 q20 ∷
   rw 50 q26 ∷
   rw 49 q22 ∷
   re 49 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 48 q8 ∷
   re 49 5 (CS03 ∷ []) ∷
   rw 51 q13 ∷
   rw⁻ 50 q14 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q15 ∷
   rw 50 q23 ∷
   rw⁻ 49 q15 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 50 q24 ∷
   rw 49 q14 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q15 ∷
   rw 51 q25 ∷
   rw 52 q15 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q19 ∷
   rw 48 q13 ∷
   rw⁻ 47 q14 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q15 ∷
   rw 47 q23 ∷
   rw⁻ 46 q15 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q24 ∷
   rw 46 q14 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q15 ∷
   rw 48 q25 ∷
   rw 49 q15 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q19 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q4 ∷
   re 51 3 (CX31 ∷ []) ∷
   rw 50 q20 ∷
   rw 49 q26 ∷
   rw 48 q22 ∷
   re 48 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 47 q8 ∷
   re 48 5 (CS03 ∷ []) ∷
   rw 50 q13 ∷
   rw⁻ 49 q14 ∷ []) Eq.refl
