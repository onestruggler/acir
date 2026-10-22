{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D395 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q6 : Eqn
  q6 = wE 140 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 1120 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = wE 36 W
  q14 : Eqn
  q14 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q15 : Eqn
  q15 = wE 37 W
  q16 : Eqn
  q16 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q17 : Eqn
  q17 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q18 : Eqn
  q18 = wE 464 W
  q19 : Eqn
  q19 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q20 : Eqn
  q20 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = wE 1121 W
  q22 : Eqn
  q22 = wE 151 W
  q23 : Eqn
  q23 = wE 157 W
  q24 : Eqn
  q24 = wE 158 W
  q25 : Eqn
  q25 = wE 624 W
  q26 : Eqn
  q26 = wE 625 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03] part1: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX13 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CX13 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ [])
  (re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 37 5 (CS03 ∷ []) ∷
   rw 38 q2 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q3 ∷
   rw 38 q4 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q3 ∷
   rw 37 q4 ∷
   rw⁻ 36 q3 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q3 ∷
   rw 35 q4 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q3 ∷
   rw 34 q4 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw⁻ 31 q5 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q6 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CK31 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw⁻ 20 q7 ∷
   rw 19 q6 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw⁻ 15 q7 ∷
   rw 14 q6 ∷
   rw⁻ 13 q7 ∷
   rw 12 q6 ∷
   rw 13 q8 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 14 q3 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q9 ∷
   rw 15 q3 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 15 q9 ∷
   rw 16 q3 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 16 q10 ∷
   rw 17 q3 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q5 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 18 q9 ∷
   rw 19 q3 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 19 q9 ∷
   rw 20 q3 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 20 q9 ∷
   rw 21 q3 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 21 q9 ∷
   rw 22 q3 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   rw 22 q9 ∷
   rw 23 q3 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   rw 23 q9 ∷
   rw 24 q3 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q10 ∷
   rw 24 q7 ∷
   rw 25 q10 ∷
   rw 26 q7 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q10 ∷
   rw 31 q7 ∷
   rw 32 q9 ∷
   rw 33 q9 ∷
   rw 34 q9 ∷
   rw 35 q9 ∷
   rw 36 q9 ∷
   rw 37 q9 ∷
   rw 38 q11 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   re 12 3 (CX13 ∷ []) ∷
   rw 12 q13 ∷
   rw⁻ 13 q14 ∷
   rw 14 q15 ∷
   re 15 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   re 13 3 (CX13 ∷ []) ∷
   rw 13 q13 ∷
   rw⁻ 14 q14 ∷
   rw 15 q15 ∷
   re 16 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   re 14 3 (CX13 ∷ []) ∷
   rw 14 q13 ∷
   rw⁻ 15 q14 ∷
   rw 16 q15 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   re 15 3 (CX13 ∷ []) ∷
   rw 15 q13 ∷
   rw⁻ 16 q16 ∷
   rw 17 q15 ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 14 5 (CK30 ∷ []) ∷
   rw 15 q17 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q12 ∷
   re 17 3 (CX13 ∷ []) ∷
   rw 17 q13 ∷
   rw⁻ 18 q14 ∷
   rw 19 q15 ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   re 18 3 (CX13 ∷ []) ∷
   rw 18 q13 ∷
   rw⁻ 19 q14 ∷
   rw 20 q15 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   re 19 3 (CX13 ∷ []) ∷
   rw 19 q13 ∷
   rw⁻ 20 q14 ∷
   rw 21 q15 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q12 ∷
   re 20 3 (CX13 ∷ []) ∷
   rw 20 q13 ∷
   rw⁻ 21 q14 ∷
   rw 22 q15 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   re 21 3 (CX13 ∷ []) ∷
   rw 21 q13 ∷
   rw⁻ 22 q14 ∷
   rw 23 q15 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q12 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 22 q13 ∷
   rw⁻ 23 q14 ∷
   rw 24 q15 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 22 q12 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   rw 15 q18 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q1 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q1 ∷
   rw 10 q19 ∷
   rw 9 q19 ∷
   rw 8 q20 ∷
   rw 7 q19 ∷
   rw 6 q20 ∷
   rw 5 q20 ∷
   rw 6 q21 ∷
   rw 7 q12 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 10 q12 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q22 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 13 q12 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q12 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q12 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q12 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q12 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q20 ∷
   rw⁻ 17 q20 ∷
   rw⁻ 18 q19 ∷
   rw⁻ 19 q20 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw 22 q1 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q12 ∷
   re 45 3 (CK30 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q12 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 48 q23 ∷
   rw 47 q16 ∷
   rw 46 q24 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 46 5 (CK30 ∷ []) ∷
   re 46 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 44 3 (CX13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q12 ∷
   re 44 3 (CK30 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q12 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 47 q23 ∷
   rw 46 q16 ∷
   rw 45 q24 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 45 5 (CK30 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 43 3 (CX13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q12 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q12 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 46 q23 ∷
   rw 45 q14 ∷
   rw 44 q24 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 42 3 (CX13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q12 ∷
   re 42 3 (CK30 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q12 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 45 q23 ∷
   rw 44 q16 ∷
   rw 43 q24 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 43 5 (CK30 ∷ []) ∷
   re 43 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 41 3 (CX13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q12 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 44 q23 ∷
   rw 43 q14 ∷
   rw 42 q24 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 40 3 (CX13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q12 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 43 q23 ∷
   rw 42 q14 ∷
   rw 41 q24 ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q25 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q12 ∷
   re 38 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q12 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 41 q23 ∷
   rw 40 q14 ∷
   rw 39 q24 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 37 3 (CX13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q12 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 40 q23 ∷
   rw 39 q14 ∷
   rw 38 q24 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 36 3 (CX13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q12 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q12 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q23 ∷
   rw 38 q14 ∷
   rw 37 q24 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 35 3 (CX13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q12 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q23 ∷
   rw 37 q14 ∷
   rw 36 q24 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 34 3 (CX13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q12 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q12 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q23 ∷
   rw 36 q14 ∷
   rw 35 q24 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 33 3 (CX13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q12 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q12 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 36 q23 ∷
   rw 35 q14 ∷
   rw 34 q24 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q26 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 31 3 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q12 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 34 q23 ∷
   rw 33 q16 ∷
   rw 32 q24 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 32 5 (CK30 ∷ []) ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 30 3 (CX13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 33 q23 ∷
   rw 32 q14 ∷
   rw 31 q24 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 29 3 (CX13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷ []) Eq.refl
