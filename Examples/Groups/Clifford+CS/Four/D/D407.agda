{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D407 (W : Ws) where

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
  q2 = wE 7 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 885 W
  q6 : Eqn
  q6 = wE 142 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 36 W
  q11 : Eqn
  q11 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q12 : Eqn
  q12 = wE 37 W
  q13 : Eqn
  q13 = wE 883 W
  q14 : Eqn
  q14 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q15 : Eqn
  q15 = wE 617 W
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = wE 157 W
  q18 : Eqn
  q18 = wE 158 W
  q19 : Eqn
  q19 = wE 3 W
  q20 : Eqn
  q20 = wE 589 W
  q21 : Eqn
  q21 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q22 : Eqn
  q22 = wE 1115 W
  q23 : Eqn
  q23 = wE 5 W
  q24 : Eqn
  q24 = wE 766 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] part1: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-part1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-part1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ Sw23 ∷ CS02 ∷ Sw23 ∷ Sw01 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ Sw23 ∷ CK20 ∷ Sw01 ∷ Sw23 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw⁻ 20 q1 ∷
   rw 19 q2 ∷
   rw⁻ 18 q1 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw⁻ 17 q3 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q1 ∷
   rw 17 q4 ∷
   rw⁻ 16 q1 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw⁻ 15 q3 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q1 ∷
   rw 15 q4 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 15 q5 ∷
   rw 14 q6 ∷
   rw 15 q7 ∷
   rw 16 q6 ∷
   rw 17 q7 ∷
   rw 18 q8 ∷
   rw 19 q8 ∷
   rw 20 q8 ∷
   rw 21 q6 ∷
   rw 22 q7 ∷
   rw 23 q8 ∷
   rw 24 q8 ∷
   rw 25 q8 ∷
   rw 26 q8 ∷
   rw 27 q8 ∷
   rw 28 q8 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 30 q6 ∷
   rw 31 q1 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q3 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   rw 32 q6 ∷
   rw 33 q1 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q3 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   rw 34 q8 ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   rw 35 q8 ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   rw 36 q8 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   rw 37 q6 ∷
   rw 38 q1 ∷
   re 36 3 (CK30 ∷ []) ∷
   rw 37 q3 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   rw 39 q8 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   rw 40 q8 ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   rw 41 q8 ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   rw 42 q8 ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   rw 43 q8 ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   rw 44 q8 ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q9 ∷
   re 14 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 13 q10 ∷
   rw⁻ 14 q11 ∷
   rw 15 q12 ∷
   re 13 3 (CK20 ∷ []) ∷
   rw 14 q13 ∷
   re 16 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 15 q10 ∷
   rw⁻ 16 q11 ∷
   rw 17 q12 ∷
   re 15 3 (CK20 ∷ []) ∷
   rw 16 q13 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q10 ∷
   rw⁻ 18 q14 ∷
   rw 19 q12 ∷
   re 17 3 (CS02 ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q10 ∷
   rw⁻ 19 q14 ∷
   rw 20 q12 ∷
   re 18 3 (CS02 ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q10 ∷
   rw⁻ 20 q14 ∷
   rw 21 q12 ∷
   re 19 3 (CS02 ∷ []) ∷
   re 21 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 20 q10 ∷
   rw⁻ 21 q11 ∷
   rw 22 q12 ∷
   re 20 3 (CK20 ∷ []) ∷
   rw 21 q13 ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q10 ∷
   rw⁻ 23 q14 ∷
   rw 24 q12 ∷
   re 22 3 (CS02 ∷ []) ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q10 ∷
   rw⁻ 24 q14 ∷
   rw 25 q12 ∷
   re 23 3 (CS02 ∷ []) ∷
   re 25 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 24 q10 ∷
   rw⁻ 25 q14 ∷
   rw 26 q12 ∷
   re 24 3 (CS02 ∷ []) ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q10 ∷
   rw⁻ 26 q14 ∷
   rw 27 q12 ∷
   re 25 3 (CS02 ∷ []) ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q10 ∷
   rw⁻ 27 q14 ∷
   rw 28 q12 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q10 ∷
   rw⁻ 28 q14 ∷
   rw 29 q12 ∷
   re 27 3 (CS02 ∷ []) ∷
   rw 7 q15 ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q16 ∷
   re 54 3 (CX13 ∷ []) ∷
   rw 53 q17 ∷
   rw 52 q11 ∷
   rw 51 q18 ∷
   re 51 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 50 q19 ∷
   re 51 5 (CK30 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q16 ∷
   re 53 3 (CX13 ∷ []) ∷
   rw 52 q17 ∷
   rw 51 q11 ∷
   rw 50 q18 ∷
   re 50 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q19 ∷
   re 50 5 (CK30 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q16 ∷
   re 52 3 (CX13 ∷ []) ∷
   rw 51 q17 ∷
   rw 50 q14 ∷
   rw 49 q18 ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q19 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q16 ∷
   re 51 3 (CX13 ∷ []) ∷
   rw 50 q17 ∷
   rw 49 q11 ∷
   rw 48 q18 ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q19 ∷
   re 48 5 (CK30 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q16 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 49 q17 ∷
   rw 48 q14 ∷
   rw 47 q18 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q19 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q16 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 48 q17 ∷
   rw 47 q14 ∷
   rw 46 q18 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q19 ∷
   re 46 5 (CS03 ∷ []) ∷
   rw 44 q20 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q16 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 46 q17 ∷
   rw 45 q14 ∷
   rw 44 q18 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q19 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q16 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 45 q17 ∷
   rw 44 q14 ∷
   rw 43 q18 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q19 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q16 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 44 q17 ∷
   rw 43 q14 ∷
   rw 42 q18 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q19 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q16 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 43 q17 ∷
   rw 42 q14 ∷
   rw 41 q18 ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q19 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q16 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 42 q17 ∷
   rw 41 q14 ∷
   rw 40 q18 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q19 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q16 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 41 q17 ∷
   rw 40 q14 ∷
   rw 39 q18 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q19 ∷
   re 39 5 (CS03 ∷ []) ∷
   rw⁻ 37 q21 ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q16 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q17 ∷
   rw 38 q11 ∷
   rw 37 q18 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q19 ∷
   re 37 5 (CK30 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q16 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q17 ∷
   rw 37 q14 ∷
   rw 36 q18 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q19 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q16 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q17 ∷
   rw 36 q14 ∷
   rw 35 q18 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q19 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q16 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 36 q17 ∷
   rw 35 q14 ∷
   rw 34 q18 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q19 ∷
   re 34 5 (CS03 ∷ []) ∷
   rw⁻ 32 q21 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q16 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 34 q17 ∷
   rw 33 q11 ∷
   rw 32 q18 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   re 32 5 (CK30 ∷ []) ∷
   rw⁻ 30 q21 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q16 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 32 q17 ∷
   rw 31 q11 ∷
   rw 30 q18 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 30 5 (CK30 ∷ []) ∷
   rw 28 q20 ∷
   rw 22 q22 ∷
   rw 58 q23 ∷
   rw 57 q4 ∷
   rw 56 q4 ∷
   rw 55 q2 ∷
   rw 54 q4 ∷
   rw 53 q2 ∷
   rw 52 q2 ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q1 ∷
   rw 52 q4 ∷
   rw⁻ 51 q1 ∷
   re 52 3 (CK31 ∷ []) ∷
   re 50 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q1 ∷
   rw 51 q4 ∷
   rw⁻ 50 q1 ∷
   re 51 3 (CK31 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q1 ∷
   rw 50 q2 ∷
   rw⁻ 49 q1 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q1 ∷
   rw 49 q4 ∷
   rw⁻ 48 q1 ∷
   re 49 3 (CK31 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q1 ∷
   rw 48 q2 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q1 ∷
   rw 47 q2 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q24 ∷
   rw 46 q8 ∷
   rw 47 q8 ∷
   rw 48 q6 ∷
   rw 49 q8 ∷
   rw 50 q6 ∷
   rw 51 q6 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   rw 53 q8 ∷
   rw 54 q1 ∷
   re 52 3 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   rw 54 q8 ∷
   rw 55 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   rw 55 q6 ∷
   rw 56 q1 ∷
   re 54 3 (CK30 ∷ []) ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   rw 56 q8 ∷
   rw 57 q1 ∷
   re 55 3 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   rw 57 q6 ∷
   rw 58 q1 ∷
   re 56 3 (CK30 ∷ []) ∷
   re 58 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   rw 58 q6 ∷
   rw 59 q1 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 58 q9 ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q10 ∷
   rw⁻ 46 q14 ∷
   rw 47 q12 ∷
   re 45 3 (CS02 ∷ []) ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q10 ∷
   rw⁻ 47 q14 ∷
   rw 48 q12 ∷
   re 46 3 (CS02 ∷ []) ∷
   re 48 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 47 q10 ∷
   rw⁻ 48 q11 ∷
   rw 49 q12 ∷
   re 47 3 (CK20 ∷ []) ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q10 ∷
   rw⁻ 49 q14 ∷
   rw 50 q12 ∷
   re 48 3 (CS02 ∷ []) ∷
   re 50 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 49 q10 ∷
   rw⁻ 50 q11 ∷
   rw 51 q12 ∷
   re 49 3 (CK20 ∷ []) ∷
   re 51 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 50 q10 ∷
   rw⁻ 51 q11 ∷
   rw 52 q12 ∷
   re 50 3 (CK20 ∷ []) ∷
   rw 51 q23 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q2 ∷
   rw 47 q4 ∷
   rw 46 q2 ∷
   rw 45 q2 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q1 ∷
   rw 45 q2 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q1 ∷
   rw 43 q2 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q1 ∷
   rw 42 q2 ∷
   rw⁻ 41 q1 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q1 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q1 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw⁻ 38 q3 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q1 ∷
   rw 38 q4 ∷
   rw⁻ 37 q1 ∷
   re 38 3 (CK31 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q1 ∷
   rw 37 q2 ∷
   rw⁻ 36 q1 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q1 ∷
   rw 36 q2 ∷
   rw⁻ 35 q1 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q1 ∷
   rw 35 q2 ∷
   rw⁻ 34 q1 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw⁻ 33 q3 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q1 ∷
   rw 33 q4 ∷
   rw⁻ 32 q1 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw⁻ 31 q3 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q1 ∷ []) Eq.refl
