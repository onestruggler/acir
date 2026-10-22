{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D461 (W : Ws) where

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
  q1 = wE 27 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 142 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q5 : Eqn
  q5 = wE 31 W
  q6 : Eqn
  q6 = wE 36 W
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 37 W
  q9 : Eqn
  q9 = wE 883 W
  q10 : Eqn
  q10 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q11 : Eqn
  q11 = wE 665 W
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q14 : Eqn
  q14 = wE 3 W
  q15 : Eqn
  q15 = wE 880 W
  q16 : Eqn
  q16 = wE 157 W
  q17 : Eqn
  q17 = wE 158 W
  q18 : Eqn
  q18 = wE 879 W
  q19 : Eqn
  q19 = wE 881 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part2: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part2 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part2 = derive (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ X1 ∷ Sw23 ∷ CX12 ∷ X1 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 34 q1 ∷
   rw 35 q2 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   rw 35 q1 ∷
   rw 36 q2 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q1 ∷
   rw 37 q2 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q1 ∷
   rw 38 q2 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 38 q1 ∷
   rw 39 q2 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   rw 39 q1 ∷
   rw 40 q2 ∷
   re 38 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q3 ∷
   rw 41 q2 ∷
   re 39 3 (CK30 ∷ []) ∷
   rw 40 q4 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw 42 q1 ∷
   rw 43 q2 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw 43 q1 ∷
   rw 44 q2 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw 44 q1 ∷
   rw 45 q2 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   rw 45 q1 ∷
   rw 46 q2 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   rw 46 q1 ∷
   rw 47 q2 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw 47 q1 ∷
   rw 48 q2 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw 48 q1 ∷
   rw 49 q2 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   rw 49 q1 ∷
   rw 50 q2 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   rw 50 q1 ∷
   rw 51 q2 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q5 ∷
   re 18 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 17 q6 ∷
   rw⁻ 18 q7 ∷
   rw 19 q8 ∷
   re 17 3 (CK20 ∷ []) ∷
   rw 18 q9 ∷
   re 20 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 19 q6 ∷
   rw⁻ 20 q7 ∷
   rw 21 q8 ∷
   re 19 3 (CK20 ∷ []) ∷
   rw 20 q9 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q6 ∷
   rw⁻ 22 q10 ∷
   rw 23 q8 ∷
   re 21 3 (CS02 ∷ []) ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q6 ∷
   rw⁻ 23 q10 ∷
   rw 24 q8 ∷
   re 22 3 (CS02 ∷ []) ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q6 ∷
   rw⁻ 24 q10 ∷
   rw 25 q8 ∷
   re 23 3 (CS02 ∷ []) ∷
   re 25 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 24 q6 ∷
   rw⁻ 25 q7 ∷
   rw 26 q8 ∷
   re 24 3 (CK20 ∷ []) ∷
   rw 25 q9 ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q6 ∷
   rw⁻ 27 q10 ∷
   rw 28 q8 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q6 ∷
   rw⁻ 28 q10 ∷
   rw 29 q8 ∷
   re 27 3 (CS02 ∷ []) ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q6 ∷
   rw⁻ 29 q10 ∷
   rw 30 q8 ∷
   re 28 3 (CS02 ∷ []) ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 29 q6 ∷
   rw⁻ 30 q10 ∷
   rw 31 q8 ∷
   re 29 3 (CS02 ∷ []) ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q6 ∷
   rw⁻ 31 q10 ∷
   rw 32 q8 ∷
   re 30 3 (CS02 ∷ []) ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q6 ∷
   rw⁻ 32 q10 ∷
   rw 33 q8 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 11 q11 ∷
   rw 58 q12 ∷
   rw 57 q13 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q14 ∷
   rw 57 q15 ∷
   rw⁻ 56 q13 ∷
   rw 59 q12 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 58 q14 ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q12 ∷
   re 61 3 (CX13 ∷ []) ∷
   rw 60 q16 ∷
   rw 59 q10 ∷
   rw 58 q17 ∷
   re 58 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 57 q14 ∷
   re 58 5 (CS03 ∷ []) ∷
   rw 60 q12 ∷
   rw 59 q13 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q14 ∷
   rw 59 q15 ∷
   rw⁻ 58 q13 ∷
   rw 61 q12 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 60 q14 ∷
   rw 57 q12 ∷
   rw 56 q13 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q14 ∷
   rw 56 q15 ∷
   rw⁻ 55 q13 ∷
   rw 58 q12 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q14 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q12 ∷
   re 60 3 (CX13 ∷ []) ∷
   rw 59 q16 ∷
   rw 58 q10 ∷
   rw 57 q17 ∷
   re 57 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 56 q14 ∷
   re 57 5 (CS03 ∷ []) ∷
   rw 59 q12 ∷
   rw 58 q13 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q14 ∷
   rw 58 q15 ∷
   rw⁻ 57 q13 ∷
   rw 60 q12 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 59 q14 ∷
   rw 56 q12 ∷
   rw 55 q13 ∷
   re 54 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 56 q14 ∷
   rw 55 q18 ∷
   rw⁻ 54 q13 ∷
   rw 57 q12 ∷
   re 55 3 (CK30 ∷ []) ∷
   rw 56 q14 ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q12 ∷
   re 59 3 (CX13 ∷ []) ∷
   rw 58 q16 ∷
   rw 57 q7 ∷
   rw 56 q17 ∷
   re 56 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 55 q14 ∷
   re 56 5 (CK30 ∷ []) ∷
   rw 58 q12 ∷
   rw 57 q13 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q14 ∷
   rw 57 q18 ∷
   rw⁻ 56 q13 ∷
   rw 59 q12 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 58 q14 ∷
   rw 55 q12 ∷
   rw 54 q13 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q14 ∷
   rw 54 q15 ∷
   rw⁻ 53 q13 ∷
   rw 56 q12 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 55 q14 ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q12 ∷
   re 58 3 (CX13 ∷ []) ∷
   rw 57 q16 ∷
   rw 56 q10 ∷
   rw 55 q17 ∷
   re 55 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 54 q14 ∷
   re 55 5 (CS03 ∷ []) ∷
   rw 57 q12 ∷
   rw 56 q13 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q14 ∷
   rw 56 q15 ∷
   rw⁻ 55 q13 ∷
   rw 58 q12 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q14 ∷
   rw 54 q12 ∷
   rw 53 q13 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q14 ∷
   rw 53 q15 ∷
   rw⁻ 52 q13 ∷
   rw 55 q12 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 54 q14 ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q12 ∷
   re 57 3 (CX13 ∷ []) ∷
   rw 56 q16 ∷
   rw 55 q10 ∷
   rw 54 q17 ∷
   re 54 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 53 q14 ∷
   re 54 5 (CS03 ∷ []) ∷
   rw 56 q12 ∷
   rw 55 q13 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q14 ∷
   rw 55 q15 ∷
   rw⁻ 54 q13 ∷
   rw 57 q12 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 56 q14 ∷
   rw 53 q12 ∷
   rw 52 q13 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q14 ∷
   rw 52 q15 ∷
   rw⁻ 51 q13 ∷
   rw 54 q12 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q14 ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q12 ∷
   re 56 3 (CX13 ∷ []) ∷
   rw 55 q16 ∷
   rw 54 q10 ∷
   rw 53 q17 ∷
   re 53 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 52 q14 ∷
   re 53 5 (CS03 ∷ []) ∷
   rw 55 q12 ∷
   rw 54 q13 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q14 ∷
   rw 54 q15 ∷
   rw⁻ 53 q13 ∷
   rw 56 q12 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 55 q14 ∷
   rw 50 q19 ∷
   rw 51 q12 ∷
   rw 50 q13 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q14 ∷
   rw 50 q15 ∷
   rw⁻ 49 q13 ∷
   rw 52 q12 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q14 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q12 ∷
   re 54 3 (CX13 ∷ []) ∷
   rw 53 q16 ∷
   rw 52 q10 ∷
   rw 51 q17 ∷
   re 51 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 50 q14 ∷
   re 51 5 (CS03 ∷ []) ∷
   rw 53 q12 ∷
   rw 52 q13 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q14 ∷
   rw 52 q15 ∷
   rw⁻ 51 q13 ∷
   rw 54 q12 ∷
   re 52 3 (CS03 ∷ []) ∷
   rw 53 q14 ∷
   rw 50 q12 ∷
   rw 49 q13 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q14 ∷
   rw 49 q15 ∷
   rw⁻ 48 q13 ∷
   rw 51 q12 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q14 ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q12 ∷
   re 53 3 (CX13 ∷ []) ∷
   rw 52 q16 ∷
   rw 51 q10 ∷
   rw 50 q17 ∷
   re 50 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q14 ∷
   re 50 5 (CS03 ∷ []) ∷
   rw 52 q12 ∷
   rw 51 q13 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q14 ∷
   rw 51 q15 ∷
   rw⁻ 50 q13 ∷
   rw 53 q12 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q14 ∷
   rw 49 q12 ∷
   rw 48 q13 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q14 ∷
   rw 48 q15 ∷
   rw⁻ 47 q13 ∷
   rw 50 q12 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q14 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q12 ∷
   re 52 3 (CX13 ∷ []) ∷
   rw 51 q16 ∷
   rw 50 q10 ∷
   rw 49 q17 ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q14 ∷
   re 49 5 (CS03 ∷ []) ∷
   rw 51 q12 ∷
   rw 50 q13 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q14 ∷
   rw 50 q15 ∷
   rw⁻ 49 q13 ∷
   rw 52 q12 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q14 ∷
   rw 48 q12 ∷
   rw 47 q13 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q14 ∷
   rw 47 q15 ∷
   rw⁻ 46 q13 ∷
   rw 49 q12 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q14 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q12 ∷
   re 51 3 (CX13 ∷ []) ∷
   rw 50 q16 ∷
   rw 49 q10 ∷
   rw 48 q17 ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q14 ∷
   re 48 5 (CS03 ∷ []) ∷
   rw 50 q12 ∷
   rw 49 q13 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q14 ∷
   rw 49 q15 ∷
   rw⁻ 48 q13 ∷
   rw 51 q12 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q14 ∷
   rw 47 q12 ∷
   rw 46 q13 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q14 ∷
   rw 46 q15 ∷
   rw⁻ 45 q13 ∷
   rw 48 q12 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q14 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q12 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 49 q16 ∷
   rw 48 q10 ∷
   rw 47 q17 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q14 ∷
   re 47 5 (CS03 ∷ []) ∷
   rw 49 q12 ∷
   rw 48 q13 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q14 ∷
   rw 48 q15 ∷
   rw⁻ 47 q13 ∷
   rw 50 q12 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q14 ∷
   rw 46 q12 ∷
   rw 45 q13 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q14 ∷
   rw 45 q15 ∷
   rw⁻ 44 q13 ∷
   rw 47 q12 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q14 ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q12 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 48 q16 ∷
   rw 47 q10 ∷
   rw 46 q17 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q14 ∷
   re 46 5 (CS03 ∷ []) ∷
   rw 48 q12 ∷
   rw 47 q13 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q14 ∷
   rw 47 q15 ∷
   rw⁻ 46 q13 ∷
   rw 49 q12 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q14 ∷
   rw 45 q12 ∷
   rw 44 q13 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q14 ∷
   rw 44 q15 ∷
   rw⁻ 43 q13 ∷
   rw 46 q12 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q14 ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q12 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 47 q16 ∷
   rw 46 q10 ∷
   rw 45 q17 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q14 ∷
   re 45 5 (CS03 ∷ []) ∷
   rw 47 q12 ∷
   rw 46 q13 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q14 ∷
   rw 46 q15 ∷
   rw⁻ 45 q13 ∷
   rw 48 q12 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q14 ∷
   rw 44 q12 ∷
   rw 43 q13 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q14 ∷ []) Eq.refl
