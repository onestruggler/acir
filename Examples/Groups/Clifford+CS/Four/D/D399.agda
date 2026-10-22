{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D399 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 157 W
  q3 : Eqn
  q3 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q4 : Eqn
  q4 = wE 158 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 625 W
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 624 W
  q9 : Eqn
  q9 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q11 : Eqn
  q11 = wE 1126 W
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 7 W
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = wE 1130 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 142 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = wE 36 W
  q21 : Eqn
  q21 = wE 37 W
  q22 : Eqn
  q22 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q23 : Eqn
  q23 = wE 1131 W
  q24 : Eqn
  q24 = wE 1132 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03] part2: 435 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part2 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-part2 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 35 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q2 ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   re 35 3 (CX13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q2 ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 34 3 (CX13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q2 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 33 3 (CX13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 36 q2 ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 32 3 (CX13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 35 q2 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q6 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 33 q2 ∷
   rw 32 q7 ∷
   rw 31 q4 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 29 3 (CX13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 28 3 (CX13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 27 3 (CX13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 26 3 (CX13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 25 3 (CX13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 24 3 (CX13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 22 q8 ∷
   rw 23 q1 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q9 ∷
   rw 17 q11 ∷
   rw 18 q1 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw⁻ 17 q9 ∷
   rw⁻ 18 q9 ∷
   rw⁻ 19 q9 ∷
   rw⁻ 20 q10 ∷
   rw⁻ 21 q9 ∷
   rw⁻ 22 q9 ∷
   rw 23 q5 ∷
   rw 52 q12 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q13 ∷
   rw 52 q14 ∷
   rw⁻ 51 q13 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q13 ∷
   rw 51 q15 ∷
   rw⁻ 50 q13 ∷
   re 51 3 (CK31 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q13 ∷
   rw 50 q14 ∷
   rw⁻ 49 q13 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q13 ∷
   rw 49 q14 ∷
   rw⁻ 48 q13 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 47 q14 ∷
   rw 46 q14 ∷
   rw 45 q15 ∷
   rw 44 q14 ∷
   rw 43 q14 ∷
   rw 42 q14 ∷
   rw 43 q16 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q13 ∷
   rw 43 q17 ∷
   rw 44 q13 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q13 ∷
   rw 44 q17 ∷
   rw 45 q13 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 44 q13 ∷
   rw 45 q18 ∷
   rw 46 q13 ∷
   re 44 3 (CK30 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q13 ∷
   rw 46 q17 ∷
   rw 47 q13 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q17 ∷
   rw 47 q17 ∷
   rw 48 q17 ∷
   rw 49 q18 ∷
   rw 50 q17 ∷
   rw 51 q17 ∷
   rw 52 q19 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 42 q20 ∷
   rw⁻ 43 q3 ∷
   rw 44 q21 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 43 q20 ∷
   rw⁻ 44 q3 ∷
   rw 45 q21 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 44 q20 ∷
   rw⁻ 45 q7 ∷
   rw 46 q21 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 43 5 (CK30 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 45 q20 ∷
   rw⁻ 46 q3 ∷
   rw 47 q21 ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 44 5 (CS03 ∷ []) ∷
   rw 45 q12 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q13 ∷
   rw 45 q14 ∷
   rw⁻ 44 q13 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q13 ∷
   rw 44 q15 ∷
   rw⁻ 43 q13 ∷
   re 44 3 (CK31 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q13 ∷
   rw 43 q14 ∷
   rw⁻ 42 q13 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q13 ∷
   rw 42 q14 ∷
   rw⁻ 41 q13 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 40 q14 ∷
   rw 39 q14 ∷
   rw 38 q14 ∷
   rw 37 q14 ∷
   rw 36 q14 ∷
   rw 35 q14 ∷
   rw 34 q14 ∷
   rw 33 q14 ∷
   rw 32 q14 ∷
   rw⁻ 31 q22 ∷
   rw 30 q15 ∷
   rw 29 q14 ∷
   rw 28 q14 ∷
   rw 27 q14 ∷
   rw 26 q14 ∷
   rw 25 q14 ∷
   rw 24 q14 ∷
   rw 25 q23 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q13 ∷
   rw 25 q17 ∷
   rw 26 q13 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q13 ∷
   rw 26 q17 ∷
   rw 27 q13 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q13 ∷
   rw 27 q18 ∷
   rw 28 q13 ∷
   re 26 3 (CK30 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q13 ∷
   rw 28 q17 ∷
   rw 29 q13 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q17 ∷
   rw 29 q17 ∷
   rw 30 q17 ∷
   rw 31 q17 ∷
   rw 32 q17 ∷
   rw 33 q17 ∷
   rw 34 q18 ∷
   rw 35 q22 ∷
   rw 36 q17 ∷
   rw 37 q17 ∷
   rw 38 q17 ∷
   rw 39 q17 ∷
   rw 40 q17 ∷
   rw 41 q17 ∷
   rw 42 q17 ∷
   rw 43 q17 ∷
   rw 44 q17 ∷
   rw 45 q19 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 24 3 (CX13 ∷ []) ∷
   rw 24 q20 ∷
   rw⁻ 25 q3 ∷
   rw 26 q21 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 25 q20 ∷
   rw⁻ 26 q3 ∷
   rw 27 q21 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 3 (CX13 ∷ []) ∷
   rw 26 q20 ∷
   rw⁻ 27 q7 ∷
   rw 28 q21 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 25 5 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 27 q20 ∷
   rw⁻ 28 q3 ∷
   rw 29 q21 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 26 5 (CS03 ∷ []) ∷
   rw 27 q1 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q5 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   rw 22 q9 ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 18 q24 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CK30 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw⁻ 21 q9 ∷
   rw⁻ 22 q9 ∷
   rw⁻ 23 q9 ∷
   rw⁻ 24 q10 ∷
   rw⁻ 25 q9 ∷
   rw⁻ 26 q9 ∷
   rw 27 q5 ∷ []) Eq.refl
