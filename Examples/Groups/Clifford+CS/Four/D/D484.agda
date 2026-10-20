{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D484 (W : Ws) where

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
  q2 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q7 : Eqn
  q7 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q9 : Eqn
  q9 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q10 : Eqn
  q10 = eqn (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X1 ∷ CK13 ∷ X1 ∷ []) (X1 ∷ CK13 ∷ X1 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (wn 1283 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [X0 CK03 X0]: 91 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CK03-X0 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CK03 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CK03-X0 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ X0 ∷ CK03 ∷ X0 ∷ []) (X0 ∷ CK03 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CK13 ∷ []) ∷
   rw 29 q2 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 23 q6 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q3 ∷
   rw 23 q7 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw⁻ 21 q6 ∷
   rw⁻ 20 q6 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q8 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 10 q8 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 7 q5 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 7 q7 ∷
   rw⁻ 6 q3 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q9 ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   re 2 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q12 ∷
   rw 3 q3 ∷
   re 1 3 (CK03 ∷ []) ∷
   rw 2 q11 ∷
   rw 3 q13 ∷
   rw 4 q13 ∷
   rw 5 q12 ∷
   rw 6 q13 ∷
   rw 7 q12 ∷
   rw 8 q12 ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 10 q14 ∷
   rw 11 q3 ∷
   re 9 3 (CX03 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q8 ∷
   rw 12 q5 ∷
   rw 13 q8 ∷
   rw 14 q6 ∷
   rw 15 q6 ∷
   rw 16 q6 ∷
   rw 17 q5 ∷
   rw 18 q8 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   rw 23 q6 ∷
   rw 24 q6 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   rw 26 q14 ∷
   rw 27 q3 ∷
   re 25 3 (CX03 ∷ []) ∷
   rw 26 q6 ∷
   rw 27 q6 ∷
   rw 28 q5 ∷
   rw 29 q6 ∷
   rw 30 q5 ∷
   rw 31 q5 ∷
   rw 32 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = eqn (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (wn 1284 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q19 : Eqn
  q19 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q20 : Eqn
  q20 = eqn (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) (wn 107 W)
  q21 : Eqn
  q21 = eqn (CK01 ∷ CZ23 ∷ []) (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ))
  q22 : Eqn
  q22 = eqn (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) (wn 108 W)
  q23 : Eqn
  q23 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q24 : Eqn
  q24 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q25 : Eqn
  q25 = eqn (CX20 ∷ CZ12 ∷ []) (CZ12 ∷ CX20 ∷ []) (wn 714 W)
  q26 : Eqn
  q26 = eqn (S0 ∷ CZ13 ∷ []) (CZ13 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CZ • Swap ↑)))
  q27 : Eqn
  q27 = eqn (CK32 ∷ CZ13 ∷ []) (CZ13 ∷ CK32 ∷ []) (wn 1285 W)
  q28 : Eqn
  q28 = eqn (CS23 ∷ CZ13 ∷ []) (CZ13 ∷ CS23 ∷ []) (wn 713 W)
  q29 : Eqn
  q29 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q30 : Eqn
  q30 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q31 : Eqn
  q31 = eqn (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ []) (CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ CX13 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX13 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) (wn 1286 W)

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CZ13]: 455 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CZ13 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CZ13 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CZ13 ∷ []) (CZ13 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw 29 q1 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 23 q6 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q3 ∷
   rw 23 q7 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw⁻ 21 q6 ∷
   rw⁻ 20 q6 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 15 q8 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 10 q8 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 7 q5 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 7 q7 ∷
   rw⁻ 6 q3 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw 3 q9 ∷
   rw 2 q4 ∷
   rw 1 q9 ∷
   rw 0 q9 ∷
   rw 1 q16 ∷
   rw 0 q6 ∷
   rw 1 q6 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q5 ∷
   rw 5 q5 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q17 ∷
   rw 8 q3 ∷
   re 6 3 (CX30 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q18 ∷
   rw 9 q12 ∷
   rw 10 q18 ∷
   rw 11 q13 ∷
   rw 12 q13 ∷
   rw 13 q13 ∷
   rw 14 q12 ∷
   rw 15 q18 ∷
   rw 16 q13 ∷
   rw 17 q13 ∷
   rw 18 q13 ∷
   rw 19 q13 ∷
   rw 20 q13 ∷
   rw 21 q13 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   rw 23 q17 ∷
   rw 24 q3 ∷
   re 22 3 (CX30 ∷ []) ∷
   rw 23 q13 ∷
   rw 24 q13 ∷
   rw 25 q12 ∷
   rw 26 q13 ∷
   rw 27 q12 ∷
   rw 28 q12 ∷
   rw 29 q15 ∷
   re 29 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 29 3 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q19 ∷
   re 33 3 (CZ13 ∷ []) ∷
   rw 32 q20 ∷
   rw 31 q21 ∷
   rw 30 q22 ∷
   re 30 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 29 q23 ∷
   re 30 5 (CK03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 32 q23 ∷
   re 28 3 (CZ13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 28 3 (CK03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q19 ∷
   re 32 3 (CZ13 ∷ []) ∷
   rw 31 q20 ∷
   rw 30 q21 ∷
   rw 29 q22 ∷
   re 29 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 28 q23 ∷
   re 29 5 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 31 q23 ∷
   re 27 3 (CZ13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q19 ∷
   re 31 3 (CZ13 ∷ []) ∷
   rw 30 q20 ∷
   rw 29 q24 ∷
   rw 28 q22 ∷
   re 28 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 27 q23 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q23 ∷
   re 26 3 (CZ13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 26 3 (CK03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q19 ∷
   re 30 3 (CZ13 ∷ []) ∷
   rw 29 q20 ∷
   rw 28 q21 ∷
   rw 27 q22 ∷
   re 27 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 26 q23 ∷
   re 27 5 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 29 q23 ∷
   re 25 3 (CZ13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   re 29 3 (CZ13 ∷ []) ∷
   rw 28 q20 ∷
   rw 27 q24 ∷
   rw 26 q22 ∷
   re 26 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 25 q23 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q23 ∷
   re 24 3 (CZ13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q19 ∷
   re 28 3 (CZ13 ∷ []) ∷
   rw 27 q20 ∷
   rw 26 q24 ∷
   rw 25 q22 ∷
   re 25 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 24 q23 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q23 ∷
   re 23 3 (CZ13 ∷ []) ∷
   rw 24 q19 ∷
   re 23 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 25 q23 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 24 q23 ∷
   rw 23 q25 ∷
   rw 24 q19 ∷
   re 22 3 (CZ13 ∷ []) ∷
   rw 25 q19 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw 24 q23 ∷
   re 22 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 26 3 (CZ13 ∷ []) ∷
   rw 25 q20 ∷
   rw 24 q24 ∷
   rw 23 q22 ∷
   re 23 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 22 q23 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q23 ∷
   re 21 3 (CZ13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 25 3 (CZ13 ∷ []) ∷
   rw 24 q20 ∷
   rw 23 q24 ∷
   rw 22 q22 ∷
   re 22 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 21 q23 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q23 ∷
   re 20 3 (CZ13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 24 3 (CZ13 ∷ []) ∷
   rw 23 q20 ∷
   rw 22 q24 ∷
   rw 21 q22 ∷
   re 21 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 20 q23 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q23 ∷
   re 19 3 (CZ13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 18 q19 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 23 3 (CZ13 ∷ []) ∷
   rw 22 q20 ∷
   rw 21 q24 ∷
   rw 20 q22 ∷
   re 20 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 19 q23 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q23 ∷
   re 18 3 (CZ13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 17 q19 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 22 3 (CZ13 ∷ []) ∷
   rw 21 q20 ∷
   rw 20 q24 ∷
   rw 19 q22 ∷
   re 19 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 18 q23 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q23 ∷
   re 17 3 (CZ13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 21 3 (CZ13 ∷ []) ∷
   rw 20 q20 ∷
   rw 19 q24 ∷
   rw 18 q22 ∷
   re 18 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 17 q23 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q23 ∷
   re 16 3 (CZ13 ∷ []) ∷
   rw 15 q26 ∷
   re 15 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   re 15 3 (CK03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 19 3 (CZ13 ∷ []) ∷
   rw 18 q20 ∷
   rw 17 q21 ∷
   rw 16 q22 ∷
   re 16 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 15 q23 ∷
   re 16 5 (CK03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 18 q23 ∷
   re 14 3 (CZ13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 18 3 (CZ13 ∷ []) ∷
   rw 17 q20 ∷
   rw 16 q24 ∷
   rw 15 q22 ∷
   re 15 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 14 q23 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q23 ∷
   re 13 3 (CZ13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 12 q19 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 17 3 (CZ13 ∷ []) ∷
   rw 16 q20 ∷
   rw 15 q24 ∷
   rw 14 q22 ∷
   re 14 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 13 q23 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q23 ∷
   re 12 3 (CZ13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q19 ∷
   re 16 3 (CZ13 ∷ []) ∷
   rw 15 q20 ∷
   rw 14 q24 ∷
   rw 13 q22 ∷
   re 13 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 12 q23 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q23 ∷
   re 11 3 (CZ13 ∷ []) ∷
   rw 10 q26 ∷
   re 10 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   re 10 3 (CK03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   re 14 3 (CZ13 ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   rw 11 q22 ∷
   re 11 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 10 q23 ∷
   re 11 5 (CK03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 13 q23 ∷
   re 9 3 (CZ13 ∷ []) ∷
   rw 8 q26 ∷
   re 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   re 8 3 (CK03 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   re 12 3 (CZ13 ∷ []) ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   rw 9 q22 ∷
   re 9 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 8 q23 ∷
   re 9 5 (CK03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 11 q23 ∷
   re 7 3 (CZ13 ∷ []) ∷
   rw 8 q19 ∷
   re 7 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 9 q23 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 8 q23 ∷
   rw 7 q25 ∷
   rw 8 q19 ∷
   re 6 3 (CZ13 ∷ []) ∷
   rw 9 q19 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw 8 q23 ∷
   rw 5 q27 ∷
   rw 4 q27 ∷
   rw 3 q28 ∷
   rw 2 q27 ∷
   rw 1 q28 ∷
   rw 0 q28 ∷
   rw 30 q1 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q9 ∷
   rw 26 q4 ∷
   rw 25 q9 ∷
   rw 24 q9 ∷
   re 23 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q3 ∷
   rw 24 q29 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 22 q9 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q30 ∷
   rw 15 q4 ∷
   rw 14 q9 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q30 ∷
   rw 10 q4 ∷
   rw 9 q30 ∷
   rw 8 q4 ∷
   re 7 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 8 q29 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (CX31 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 1 q6 ∷
   rw 2 q31 ∷
   rw 1 q13 ∷
   rw 2 q13 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q12 ∷
   rw 6 q12 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 8 q14 ∷
   rw 9 q3 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q5 ∷
   rw 9 q8 ∷
   rw 10 q5 ∷
   rw 11 q8 ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 14 q6 ∷
   rw 15 q5 ∷
   rw 16 q8 ∷
   rw 17 q6 ∷
   rw 18 q6 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   rw 24 q14 ∷
   rw 25 q3 ∷
   re 23 3 (CX03 ∷ []) ∷
   rw 24 q6 ∷
   rw 25 q6 ∷
   rw 26 q5 ∷
   rw 27 q6 ∷
   rw 28 q5 ∷
   rw 29 q5 ∷
   rw 30 q15 ∷ []) Eq.refl
