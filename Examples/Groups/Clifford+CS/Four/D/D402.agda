{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D402 (W : Ws) where

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
  q1 = wE 158 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 157 W
  q5 : Eqn
  q5 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q6 : Eqn
  q6 = wE 625 W
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 624 W
  q9 : Eqn
  q9 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q10 : Eqn
  q10 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = wE 1115 W
  q12 : Eqn
  q12 = wE 5 W
  q13 : Eqn
  q13 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 140 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 1134 W
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
  q23 = wE 1135 W
  q24 : Eqn
  q24 = wE 764 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] part2: 495 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part2 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part2 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 44 q1 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   re 42 3 (CX13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   rw 43 q1 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   re 41 3 (CX13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 44 q4 ∷
   rw 43 q5 ∷
   rw 42 q1 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   re 40 3 (CX13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   rw 41 q1 ∷
   re 41 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   re 39 3 (CX13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 42 q4 ∷
   rw 41 q5 ∷
   rw 40 q1 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q6 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 37 3 (CK30 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 40 q4 ∷
   rw 39 q7 ∷
   rw 38 q1 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 38 5 (CK30 ∷ []) ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 36 3 (CX13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q4 ∷
   rw 38 q5 ∷
   rw 37 q1 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 35 3 (CX13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   rw 36 q1 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 34 3 (CX13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q4 ∷
   rw 36 q5 ∷
   rw 35 q1 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 32 q6 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 32 3 (CK30 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 35 q4 ∷
   rw 34 q7 ∷
   rw 33 q1 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 33 5 (CK30 ∷ []) ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q6 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 33 q4 ∷
   rw 32 q7 ∷
   rw 31 q1 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q8 ∷
   rw 29 q3 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   rw 27 q9 ∷
   rw 26 q9 ∷
   rw 25 q10 ∷
   rw 24 q9 ∷
   rw 23 q10 ∷
   rw 22 q10 ∷
   rw 23 q11 ∷
   rw 24 q3 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw⁻ 23 q10 ∷
   rw⁻ 24 q10 ∷
   rw⁻ 25 q9 ∷
   rw⁻ 26 q10 ∷
   rw⁻ 27 q9 ∷
   rw⁻ 28 q9 ∷
   rw 29 q2 ∷
   rw 58 q12 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 59 q13 ∷
   rw 58 q14 ∷
   rw⁻ 57 q13 ∷
   re 58 3 (CK31 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q13 ∷
   rw 57 q14 ∷
   rw⁻ 56 q13 ∷
   re 57 3 (CK31 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 57 q13 ∷
   rw 56 q15 ∷
   rw⁻ 55 q13 ∷
   re 56 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 56 q13 ∷
   rw 55 q14 ∷
   rw⁻ 54 q13 ∷
   re 55 3 (CK31 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q13 ∷
   rw 54 q15 ∷
   rw⁻ 53 q13 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 54 q13 ∷
   rw 53 q15 ∷
   rw⁻ 52 q13 ∷
   re 53 3 (CS13 ∷ []) ∷
   rw 51 q14 ∷
   rw 50 q14 ∷
   rw 49 q15 ∷
   rw 48 q14 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw 47 q16 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q13 ∷
   rw 47 q17 ∷
   rw 48 q13 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q13 ∷
   rw 48 q17 ∷
   rw 49 q13 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 48 q13 ∷
   rw 49 q18 ∷
   rw 50 q13 ∷
   re 48 3 (CK30 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q13 ∷
   rw 50 q17 ∷
   rw 51 q13 ∷
   re 49 3 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 50 q13 ∷
   rw 51 q18 ∷
   rw 52 q13 ∷
   re 50 3 (CK30 ∷ []) ∷
   re 52 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 51 q13 ∷
   rw 52 q18 ∷
   rw 53 q13 ∷
   re 51 3 (CK30 ∷ []) ∷
   rw 52 q17 ∷
   rw 53 q17 ∷
   rw 54 q18 ∷
   rw 55 q17 ∷
   rw 56 q18 ∷
   rw 57 q18 ∷
   rw 58 q19 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 46 q20 ∷
   rw⁻ 47 q5 ∷
   rw 48 q21 ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 47 q20 ∷
   rw⁻ 48 q5 ∷
   rw 49 q21 ∷
   re 50 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 48 q20 ∷
   rw⁻ 49 q7 ∷
   rw 50 q21 ∷
   re 51 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   re 47 5 (CK30 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 49 q20 ∷
   rw⁻ 50 q5 ∷
   rw 51 q21 ∷
   re 52 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 50 q20 ∷
   rw⁻ 51 q7 ∷
   rw 52 q21 ∷
   re 53 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   re 49 5 (CK30 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   re 51 3 (CX13 ∷ []) ∷
   rw 51 q20 ∷
   rw⁻ 52 q7 ∷
   rw 53 q21 ∷
   re 54 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   re 50 5 (CK30 ∷ []) ∷
   rw 51 q12 ∷
   re 50 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q13 ∷
   rw 51 q14 ∷
   rw⁻ 50 q13 ∷
   re 51 3 (CK31 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q13 ∷
   rw 50 q14 ∷
   rw⁻ 49 q13 ∷
   re 50 3 (CK31 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q13 ∷
   rw 49 q15 ∷
   rw⁻ 48 q13 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q13 ∷
   rw 48 q14 ∷
   rw⁻ 47 q13 ∷
   re 48 3 (CK31 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q13 ∷
   rw 47 q15 ∷
   rw⁻ 46 q13 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q13 ∷
   rw 46 q15 ∷
   rw⁻ 45 q13 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q15 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   rw 39 q15 ∷
   rw⁻ 38 q22 ∷
   rw 37 q14 ∷
   rw 36 q15 ∷
   rw 35 q15 ∷
   rw 34 q15 ∷
   rw⁻ 33 q22 ∷
   rw 32 q14 ∷
   rw⁻ 31 q22 ∷
   rw 30 q14 ∷
   rw 31 q23 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q13 ∷
   rw 31 q17 ∷
   rw 32 q13 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q13 ∷
   rw 32 q17 ∷
   rw 33 q13 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 32 q13 ∷
   rw 33 q18 ∷
   rw 34 q13 ∷
   re 32 3 (CK30 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q13 ∷
   rw 34 q17 ∷
   rw 35 q13 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 34 q13 ∷
   rw 35 q18 ∷
   rw 36 q13 ∷
   re 34 3 (CK30 ∷ []) ∷
   re 36 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 35 q13 ∷
   rw 36 q18 ∷
   rw 37 q13 ∷
   re 35 3 (CK30 ∷ []) ∷
   rw 36 q18 ∷
   rw 37 q22 ∷
   rw 38 q18 ∷
   rw 39 q22 ∷
   rw 40 q17 ∷
   rw 41 q17 ∷
   rw 42 q17 ∷
   rw 43 q18 ∷
   rw 44 q22 ∷
   rw 45 q17 ∷
   rw 46 q17 ∷
   rw 47 q17 ∷
   rw 48 q17 ∷
   rw 49 q17 ∷
   rw 50 q17 ∷
   rw 51 q19 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 30 q20 ∷
   rw⁻ 31 q5 ∷
   rw 32 q21 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 31 q20 ∷
   rw⁻ 32 q5 ∷
   rw 33 q21 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 32 q20 ∷
   rw⁻ 33 q7 ∷
   rw 34 q21 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 33 q20 ∷
   rw⁻ 34 q5 ∷
   rw 35 q21 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 34 q20 ∷
   rw⁻ 35 q7 ∷
   rw 36 q21 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 33 5 (CK30 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 35 q20 ∷
   rw⁻ 36 q7 ∷
   rw 37 q21 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 34 5 (CK30 ∷ []) ∷
   rw 35 q3 ∷
   re 34 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 25 q9 ∷
   rw 24 q10 ∷
   rw 23 q10 ∷
   rw 24 q24 ∷
   rw 25 q3 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q3 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q3 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 28 q3 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q3 ∷
   re 27 3 (CK30 ∷ []) ∷
   rw 30 q3 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw⁻ 29 q10 ∷
   rw⁻ 30 q10 ∷
   rw⁻ 31 q9 ∷
   rw⁻ 32 q10 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 34 q9 ∷
   rw 35 q2 ∷ []) Eq.refl
