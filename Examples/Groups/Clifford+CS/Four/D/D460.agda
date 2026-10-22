{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D460 (W : Ws) where

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
  q1 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 880 W
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 157 W
  q6 : Eqn
  q6 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q7 : Eqn
  q7 = wE 158 W
  q8 : Eqn
  q8 = eqn (X1 ∷ S3 ∷ []) (S3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((S ↑)))
  q9 : Eqn
  q9 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q10 : Eqn
  q10 = wE 879 W
  q11 : Eqn
  q11 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 881 W
  q13 : Eqn
  q13 = wE 946 W
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q17 : Eqn
  q17 = wE 140 W
  q18 : Eqn
  q18 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 799 W
  q20 : Eqn
  q20 = wE 142 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 31 W
  q23 : Eqn
  q23 = wE 36 W
  q24 : Eqn
  q24 = wE 37 W
  q25 : Eqn
  q25 = wE 883 W
  q26 : Eqn
  q26 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q27 : Eqn
  q27 = wE 948 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(SSKSKK;~1,2->0) part1: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part1 : ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ X1 ∷ CX12 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~12-⟶0⟩-part1 = derive (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ X1 ∷ CX12 ∷ CS03 ∷ X1 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X1 ∷ X1 ∷ CX12 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CX12 ∷ X1 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 27 q1 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw⁻ 26 q1 ∷
   rw 29 q4 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q2 ∷
   rw 25 q4 ∷
   rw 24 q1 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw⁻ 23 q1 ∷
   rw 26 q4 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q2 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q7 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 5 (CS03 ∷ []) ∷
   rw 27 q4 ∷
   rw 26 q1 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw⁻ 25 q1 ∷
   rw 28 q4 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q2 ∷
   rw⁻ 22 q8 ∷
   rw⁻ 23 q9 ∷
   rw⁻ 24 q8 ∷
   rw 23 q4 ∷
   rw 22 q1 ∷
   re 21 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw 22 q10 ∷
   rw⁻ 21 q1 ∷
   rw 24 q4 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 23 q2 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 26 3 (CX13 ∷ []) ∷
   rw 25 q5 ∷
   rw 24 q11 ∷
   rw 23 q7 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 5 (CK30 ∷ []) ∷
   rw 25 q4 ∷
   rw 24 q1 ∷
   re 23 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   rw 24 q10 ∷
   rw⁻ 23 q1 ∷
   rw 26 q4 ∷
   re 24 3 (CK30 ∷ []) ∷
   rw 25 q2 ∷
   rw 22 q4 ∷
   rw 21 q1 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   rw⁻ 20 q1 ∷
   rw 23 q4 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q2 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 24 q5 ∷
   rw 23 q6 ∷
   rw 22 q7 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q4 ∷
   rw 23 q1 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   rw⁻ 22 q1 ∷
   rw 25 q4 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q2 ∷
   rw 21 q4 ∷
   rw 20 q1 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   rw⁻ 19 q1 ∷
   rw 22 q4 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q2 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 24 3 (CX13 ∷ []) ∷
   rw 23 q5 ∷
   rw 22 q6 ∷
   rw 21 q7 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q4 ∷
   rw 22 q1 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q1 ∷
   rw 24 q4 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q2 ∷
   rw 20 q4 ∷
   rw 19 q1 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   rw⁻ 18 q1 ∷
   rw 21 q4 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q2 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 22 q5 ∷
   rw 21 q6 ∷
   rw 20 q7 ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 5 (CS03 ∷ []) ∷
   rw 22 q4 ∷
   rw 21 q1 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   rw⁻ 20 q1 ∷
   rw 23 q4 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q2 ∷
   rw 19 q4 ∷
   rw 18 q1 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw 18 q3 ∷
   rw⁻ 17 q1 ∷
   rw 20 q4 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q2 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   rw 19 q7 ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 5 (CS03 ∷ []) ∷
   rw 21 q4 ∷
   rw 20 q1 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   rw⁻ 19 q1 ∷
   rw 22 q4 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q2 ∷
   rw 18 q4 ∷
   rw 17 q1 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   rw 17 q3 ∷
   rw⁻ 16 q1 ∷
   rw 19 q4 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q2 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 21 3 (CX13 ∷ []) ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q7 ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q4 ∷
   rw 19 q1 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   rw⁻ 18 q1 ∷
   rw 21 q4 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q2 ∷
   rw 17 q4 ∷
   rw 16 q1 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw⁻ 15 q1 ∷
   rw 18 q4 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q2 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 20 3 (CX13 ∷ []) ∷
   rw 19 q5 ∷
   rw 18 q6 ∷
   rw 17 q7 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 19 q4 ∷
   rw 18 q1 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw 18 q3 ∷
   rw⁻ 17 q1 ∷
   rw 20 q4 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q2 ∷
   rw 14 q12 ∷
   rw 8 q13 ∷
   rw 57 q14 ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q15 ∷
   rw 51 q15 ∷
   rw⁻ 50 q16 ∷
   rw 49 q17 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw⁻ 45 q16 ∷
   rw 44 q17 ∷
   rw⁻ 43 q16 ∷
   rw 42 q17 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q18 ∷
   rw 42 q15 ∷
   rw⁻ 41 q18 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q18 ∷
   rw 41 q15 ∷
   rw⁻ 40 q18 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q18 ∷
   rw 40 q17 ∷
   rw⁻ 39 q18 ∷
   re 40 3 (CK31 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q18 ∷
   rw 39 q15 ∷
   rw⁻ 38 q18 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q18 ∷
   rw 38 q15 ∷
   rw⁻ 37 q18 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q18 ∷
   rw 37 q15 ∷
   rw⁻ 36 q18 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 37 q19 ∷
   rw 36 q20 ∷
   rw 37 q16 ∷
   rw 38 q20 ∷
   rw 39 q16 ∷
   rw 40 q21 ∷
   rw 41 q21 ∷
   rw 42 q21 ∷
   rw 43 q20 ∷
   rw 44 q16 ∷
   rw 45 q21 ∷
   rw 46 q21 ∷
   rw 47 q21 ∷
   rw 48 q21 ∷
   rw 49 q21 ∷
   rw 50 q21 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q18 ∷
   rw 52 q21 ∷
   rw 53 q18 ∷
   re 51 3 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q18 ∷
   rw 53 q21 ∷
   rw 54 q18 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q18 ∷
   rw 54 q21 ∷
   rw 55 q18 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 54 q18 ∷
   rw 55 q20 ∷
   rw 56 q18 ∷
   re 54 3 (CK30 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q18 ∷
   rw 56 q21 ∷
   rw 57 q18 ∷
   re 55 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 56 q18 ∷
   rw 57 q21 ∷
   rw 58 q18 ∷
   re 56 3 (CS03 ∷ []) ∷
   rw 57 q22 ∷
   re 36 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 35 q23 ∷
   rw⁻ 36 q11 ∷
   rw 37 q24 ∷
   re 35 3 (CK20 ∷ []) ∷
   rw 36 q25 ∷
   re 38 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 37 q23 ∷
   rw⁻ 38 q11 ∷
   rw 39 q24 ∷
   re 37 3 (CK20 ∷ []) ∷
   rw 38 q25 ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q23 ∷
   rw⁻ 40 q6 ∷
   rw 41 q24 ∷
   re 39 3 (CS02 ∷ []) ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q23 ∷
   rw⁻ 41 q6 ∷
   rw 42 q24 ∷
   re 40 3 (CS02 ∷ []) ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q23 ∷
   rw⁻ 42 q6 ∷
   rw 43 q24 ∷
   re 41 3 (CS02 ∷ []) ∷
   re 43 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 42 q23 ∷
   rw⁻ 43 q11 ∷
   rw 44 q24 ∷
   re 42 3 (CK20 ∷ []) ∷
   rw 43 q25 ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q23 ∷
   rw⁻ 45 q6 ∷
   rw 46 q24 ∷
   re 44 3 (CS02 ∷ []) ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q23 ∷
   rw⁻ 46 q6 ∷
   rw 47 q24 ∷
   re 45 3 (CS02 ∷ []) ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q23 ∷
   rw⁻ 47 q6 ∷
   rw 48 q24 ∷
   re 46 3 (CS02 ∷ []) ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q23 ∷
   rw⁻ 48 q6 ∷
   rw 49 q24 ∷
   re 47 3 (CS02 ∷ []) ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q23 ∷
   rw⁻ 49 q6 ∷
   rw 50 q24 ∷
   re 48 3 (CS02 ∷ []) ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q23 ∷
   rw⁻ 50 q6 ∷
   rw 51 q24 ∷
   re 49 3 (CS02 ∷ []) ∷
   rw 50 q14 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw⁻ 43 q16 ∷
   rw 42 q17 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw⁻ 38 q16 ∷
   rw 37 q17 ∷
   rw⁻ 36 q16 ∷
   rw 35 q17 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q18 ∷
   rw 35 q15 ∷
   rw⁻ 34 q18 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q18 ∷
   rw 34 q15 ∷
   rw⁻ 33 q18 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q18 ∷
   rw 33 q15 ∷
   rw⁻ 32 q18 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q18 ∷
   rw 32 q15 ∷
   rw⁻ 31 q18 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q18 ∷
   rw 31 q15 ∷
   rw⁻ 30 q18 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q18 ∷
   rw 30 q15 ∷
   rw⁻ 29 q18 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q18 ∷
   rw 29 q15 ∷
   rw⁻ 28 q18 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q18 ∷
   rw 28 q15 ∷
   rw⁻ 27 q18 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q18 ∷
   rw 27 q15 ∷
   rw⁻ 26 q18 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw⁻ 25 q26 ∷
   re 24 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q18 ∷
   rw 25 q17 ∷
   rw⁻ 24 q18 ∷
   re 25 3 (CK31 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q18 ∷
   rw 24 q15 ∷
   rw⁻ 23 q18 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q18 ∷
   rw 23 q15 ∷
   rw⁻ 22 q18 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q18 ∷
   rw 22 q15 ∷
   rw⁻ 21 q18 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q18 ∷
   rw 21 q15 ∷
   rw⁻ 20 q18 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q18 ∷
   rw 20 q15 ∷
   rw⁻ 19 q18 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q18 ∷
   rw 19 q15 ∷
   rw⁻ 18 q18 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q27 ∷
   rw 18 q20 ∷
   rw 19 q16 ∷
   rw 20 q20 ∷
   rw 21 q16 ∷
   rw 22 q21 ∷
   rw 23 q21 ∷
   rw 24 q21 ∷
   rw 25 q20 ∷
   rw 26 q16 ∷
   rw 27 q21 ∷
   rw 28 q21 ∷
   rw 29 q21 ∷
   rw 30 q21 ∷
   rw 31 q21 ∷
   rw 32 q21 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q18 ∷ []) Eq.refl
