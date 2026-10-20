{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D489 (W : Ws) where

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
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q8 : Eqn
  q8 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q9 : Eqn
  q9 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ []) (wn 1297 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q17 : Eqn
  q17 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q18 : Eqn
  q18 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q19 : Eqn
  q19 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q20 : Eqn
  q20 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q21 : Eqn
  q21 = eqn (CX20 ∷ CX21 ∷ []) (CX21 ∷ CX20 ∷ []) (wn 112 W)
  q22 : Eqn
  q22 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q23 : Eqn
  q23 = eqn (CS23 ∷ CX31 ∷ []) (CX31 ∷ CS23 ∷ []) (wn 40 W)
  q24 : Eqn
  q24 = eqn (CK32 ∷ CX31 ∷ []) (CX31 ∷ CK32 ∷ []) (wn 1290 W)
  q25 : Eqn
  q25 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q26 : Eqn
  q26 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q27 : Eqn
  q27 = eqn (CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) (wn 1298 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CX31]: 521 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CX31 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CX31 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CX31 ∷ []) (CX31 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  (rw 31 q1 ∷
   rw⁻ 30 q2 ∷
   rw⁻ 29 q2 ∷
   rw⁻ 28 q3 ∷
   rw⁻ 27 q2 ∷
   rw⁻ 26 q2 ∷
   rw⁻ 25 q2 ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q4 ∷
   rw 25 q5 ∷
   rw⁻ 24 q4 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw⁻ 22 q2 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 18 q2 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 7 q2 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 7 q5 ∷
   rw⁻ 6 q4 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw 2 q7 ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   rw 1 q2 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q2 ∷
   rw 5 q2 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q10 ∷
   rw 8 q4 ∷
   re 6 3 (CX30 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q11 ∷
   rw 9 q11 ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   rw 12 q11 ∷
   rw 13 q12 ∷
   rw 14 q13 ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   rw 17 q11 ∷
   rw 18 q11 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   rw 25 q10 ∷
   rw 26 q4 ∷
   re 24 3 (CX30 ∷ []) ∷
   rw 25 q11 ∷
   rw 26 q11 ∷
   rw 27 q11 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 30 q11 ∷
   rw 31 q14 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q15 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q15 ∷
   re 35 3 (CX31 ∷ []) ∷
   rw 34 q16 ∷
   rw 33 q17 ∷
   rw 32 q18 ∷
   re 32 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q19 ∷
   re 30 3 (CX31 ∷ []) ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q15 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q15 ∷
   re 34 3 (CX31 ∷ []) ∷
   rw 33 q16 ∷
   rw 32 q17 ∷
   rw 31 q18 ∷
   re 31 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 30 q19 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q19 ∷
   re 29 3 (CX31 ∷ []) ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q15 ∷
   re 29 3 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q15 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q16 ∷
   rw 31 q20 ∷
   rw 30 q18 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 30 5 (CK03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 32 q19 ∷
   re 28 3 (CX31 ∷ []) ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q15 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q15 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   rw 29 q18 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   re 27 3 (CX31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q15 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 30 q16 ∷
   rw 29 q17 ∷
   rw 28 q18 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q19 ∷
   re 26 3 (CX31 ∷ []) ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q15 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 29 q16 ∷
   rw 28 q17 ∷
   rw 27 q18 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 26 q15 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 24 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   rw 25 q21 ∷
   rw 26 q15 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw 26 q19 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q15 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CX31 ∷ []) ∷
   rw 27 q16 ∷
   rw 26 q17 ∷
   rw 25 q18 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 23 3 (CX31 ∷ []) ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q15 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw 26 q16 ∷
   rw 25 q17 ∷
   rw 24 q18 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 22 3 (CX31 ∷ []) ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q15 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q15 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 25 q16 ∷
   rw 24 q17 ∷
   rw 23 q18 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q19 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 21 3 (CX31 ∷ []) ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q15 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 24 q16 ∷
   rw 23 q17 ∷
   rw 22 q18 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 20 3 (CX31 ∷ []) ∷
   re 20 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q15 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 23 q16 ∷
   rw 22 q17 ∷
   rw 21 q18 ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 19 3 (CX31 ∷ []) ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q15 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q15 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 22 q16 ∷
   rw 21 q17 ∷
   rw 20 q18 ∷
   re 20 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q19 ∷
   re 18 3 (CX31 ∷ []) ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q15 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q15 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 21 q16 ∷
   rw 20 q17 ∷
   rw 19 q18 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q19 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 17 3 (CX31 ∷ []) ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q15 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q15 ∷
   re 21 3 (CX31 ∷ []) ∷
   rw 20 q16 ∷
   rw 19 q17 ∷
   rw 18 q18 ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q19 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 16 3 (CX31 ∷ []) ∷
   re 16 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 15 q15 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q15 ∷
   re 20 3 (CX31 ∷ []) ∷
   rw 19 q16 ∷
   rw 18 q17 ∷
   rw 17 q18 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 15 3 (CX31 ∷ []) ∷
   rw 14 q22 ∷
   re 14 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 13 q15 ∷
   re 14 3 (CK03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q15 ∷
   re 18 3 (CX31 ∷ []) ∷
   rw 17 q16 ∷
   rw 16 q20 ∷
   rw 15 q18 ∷
   re 15 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   re 15 5 (CK03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 17 q19 ∷
   re 13 3 (CX31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 12 q15 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CX31 ∷ []) ∷
   rw 16 q16 ∷
   rw 15 q17 ∷
   rw 14 q18 ∷
   re 14 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   re 12 3 (CX31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 11 q15 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q15 ∷
   re 16 3 (CX31 ∷ []) ∷
   rw 15 q16 ∷
   rw 14 q17 ∷
   rw 13 q18 ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 12 q19 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q19 ∷
   re 11 3 (CX31 ∷ []) ∷
   re 11 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q15 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q15 ∷
   re 15 3 (CX31 ∷ []) ∷
   rw 14 q16 ∷
   rw 13 q17 ∷
   rw 12 q18 ∷
   re 12 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   re 10 3 (CX31 ∷ []) ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q15 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q15 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw 13 q16 ∷
   rw 12 q17 ∷
   rw 11 q18 ∷
   re 11 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q19 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   re 9 3 (CX31 ∷ []) ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q15 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q15 ∷
   re 13 3 (CX31 ∷ []) ∷
   rw 12 q16 ∷
   rw 11 q17 ∷
   rw 10 q18 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q19 ∷
   re 8 3 (CX31 ∷ []) ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q15 ∷
   re 12 3 (CX31 ∷ []) ∷
   rw 11 q16 ∷
   rw 10 q17 ∷
   rw 9 q18 ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw 8 q15 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   rw 7 q21 ∷
   rw 8 q15 ∷
   re 6 3 (CX31 ∷ []) ∷
   rw 9 q15 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw 8 q19 ∷
   rw 5 q23 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 2 q23 ∷
   rw 1 q23 ∷
   rw 0 q23 ∷
   rw 32 q1 ∷
   rw 31 q7 ∷
   rw 30 q7 ∷
   rw 29 q8 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   re 25 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q4 ∷
   rw 26 q25 ∷
   rw⁻ 25 q4 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 24 q7 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q26 ∷
   rw 14 q8 ∷
   rw 13 q7 ∷
   rw 12 q7 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   rw 9 q7 ∷
   rw 8 q7 ∷
   re 7 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 8 q25 ∷
   rw⁻ 7 q4 ∷
   re 8 3 (CX31 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 1 q2 ∷
   rw 2 q27 ∷
   rw 1 q11 ∷
   rw 2 q11 ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q28 ∷
   rw 9 q4 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q2 ∷
   rw 10 q2 ∷
   rw 11 q2 ∷
   rw 12 q2 ∷
   rw 13 q2 ∷
   rw 14 q3 ∷
   rw 15 q6 ∷
   rw 16 q2 ∷
   rw 17 q2 ∷
   rw 18 q2 ∷
   rw 19 q2 ∷
   rw 20 q2 ∷
   rw 21 q2 ∷
   rw 22 q2 ∷
   rw 23 q2 ∷
   rw 24 q2 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw 26 q28 ∷
   rw 27 q4 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 26 q2 ∷
   rw 27 q2 ∷
   rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q2 ∷
   rw 31 q2 ∷
   rw 32 q14 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q30 : Eqn
  q30 = eqn (CS01⁻ ∷ CK32 ∷ []) (CK32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₁₀))
  q31 : Eqn
  q31 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q32 : Eqn
  q32 = eqn (CX02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CX02 ∷ []) (wn 1291 W)
  q33 : Eqn
  q33 = eqn (CS01⁻ ∷ S3 ∷ []) (S3 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((S ↑)))
  q34 : Eqn
  q34 = eqn (CS02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS02 ∷ []) (wn 246 W)
  q35 : Eqn
  q35 = eqn (CK02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK02 ∷ []) (wn 1292 W)

-- pass [CS02 CS02 CS02 CK02 CS02 CS02 CX03 CS23 CS23 CS23 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CS23 CK32 CS23 CS23] [CSd01]: 47 steps
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CSd01 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-CSd01 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CS02 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CS23 ∷ [])
  (rw⁻ 30 q29 ∷
   rw⁻ 29 q29 ∷
   rw⁻ 28 q30 ∷
   rw⁻ 27 q29 ∷
   rw⁻ 26 q29 ∷
   rw⁻ 25 q29 ∷
   rw 26 q15 ∷
   rw 25 q31 ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   rw 25 q32 ∷
   rw⁻ 24 q31 ∷
   rw 27 q15 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 26 q19 ∷
   rw⁻ 23 q29 ∷
   rw⁻ 22 q29 ∷
   rw⁻ 21 q29 ∷
   rw⁻ 20 q29 ∷
   rw⁻ 19 q29 ∷
   rw⁻ 18 q29 ∷
   rw⁻ 17 q29 ∷
   rw⁻ 16 q29 ∷
   rw⁻ 15 q29 ∷
   rw⁻ 14 q33 ∷
   rw⁻ 13 q30 ∷
   rw⁻ 12 q29 ∷
   rw⁻ 11 q29 ∷
   rw⁻ 10 q29 ∷
   rw⁻ 9 q29 ∷
   rw⁻ 8 q29 ∷
   rw⁻ 7 q29 ∷
   rw 8 q15 ∷
   rw 7 q31 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 q19 ∷
   rw 7 q32 ∷
   rw⁻ 6 q31 ∷
   rw 9 q15 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q19 ∷
   rw 5 q34 ∷
   rw 4 q34 ∷
   rw 3 q35 ∷
   rw 2 q34 ∷
   rw 1 q34 ∷
   rw 0 q34 ∷ []) Eq.refl
