{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D503 (W : Ws) where

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
  q2 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q8 : Eqn
  q8 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q9 : Eqn
  q9 = eqn (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CX21 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX21 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (wn 1322 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CZ13 ∷ []) (CZ23 ∷ Sw12 ∷ []) (wn 107 W)
  q17 : Eqn
  q17 = eqn (CK01 ∷ CZ23 ∷ []) (CZ23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CZ))
  q18 : Eqn
  q18 = eqn (Sw12 ∷ CZ23 ∷ []) (CZ13 ∷ Sw12 ∷ []) (wn 108 W)
  q19 : Eqn
  q19 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q20 : Eqn
  q20 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q21 : Eqn
  q21 = eqn (CX20 ∷ CZ12 ∷ []) (CZ12 ∷ CX20 ∷ []) (wn 714 W)
  q22 : Eqn
  q22 = eqn (S0 ∷ CZ12 ∷ []) (CZ12 ∷ S0 ∷ []) (low₁-comm (S) (CZ))
  q23 : Eqn
  q23 = eqn (CK23 ∷ CZ12 ∷ []) (CZ12 ∷ CK23 ∷ []) (wn 1323 W)
  q24 : Eqn
  q24 = eqn (CS23 ∷ CZ12 ∷ []) (CZ12 ∷ CS23 ∷ []) (wn 550 W)
  q25 : Eqn
  q25 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q26 : Eqn
  q26 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q27 : Eqn
  q27 = eqn (CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CX21 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX21 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (wn 1324 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [CZ12]: 487 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CZ12 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CZ12 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CZ12 ∷ []) (CZ12 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw 29 q1 ∷
   rw⁻ 28 q2 ∷
   rw⁻ 27 q2 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 25 q2 ∷
   rw⁻ 24 q3 ∷
   rw⁻ 23 q3 ∷
   rw 22 q4 ∷
   rw⁻ 21 q3 ∷
   rw⁻ 20 q3 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 16 q3 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 14 q2 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 7 q2 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 6 q7 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (CK13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q7 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CK13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 4 q8 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 3 q7 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (CK13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q8 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 1 q8 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q9 ∷
   rw 0 q3 ∷
   rw 1 q3 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q2 ∷
   rw 5 q2 ∷
   rw 6 q10 ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q11 ∷
   rw 9 q6 ∷
   re 7 3 (CK03 ∷ []) ∷
   rw 8 q12 ∷
   re 10 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q11 ∷
   rw 11 q6 ∷
   re 9 3 (CK03 ∷ []) ∷
   rw 10 q12 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 12 q13 ∷
   rw 13 q6 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 13 q13 ∷
   rw 14 q6 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 14 q13 ∷
   rw 15 q6 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw 15 q11 ∷
   rw 16 q6 ∷
   re 14 3 (CK03 ∷ []) ∷
   rw 15 q12 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   rw 17 q13 ∷
   rw 18 q6 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   rw 18 q13 ∷
   rw 19 q6 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   rw 19 q13 ∷
   rw 20 q6 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   rw 20 q13 ∷
   rw 21 q6 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   rw 21 q13 ∷
   rw 22 q6 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   rw 22 q13 ∷
   rw 23 q6 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q10 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   rw 24 q13 ∷
   rw 25 q6 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   rw 25 q13 ∷
   rw 26 q6 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   rw 26 q11 ∷
   rw 27 q6 ∷
   re 25 3 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw 27 q13 ∷
   rw 28 q6 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   rw 28 q11 ∷
   rw 29 q6 ∷
   re 27 3 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   rw 29 q11 ∷
   rw 30 q6 ∷
   re 28 3 (CK03 ∷ []) ∷
   rw 29 q14 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q15 ∷
   re 32 3 (CZ13 ∷ []) ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   rw 29 q18 ∷
   re 29 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 29 5 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CZ13 ∷ []) ∷
   rw 30 q16 ∷
   rw 29 q17 ∷
   rw 28 q18 ∷
   re 28 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 28 5 (CK03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CZ13 ∷ []) ∷
   rw 29 q16 ∷
   rw 28 q20 ∷
   rw 27 q18 ∷
   re 27 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q15 ∷
   re 29 3 (CZ13 ∷ []) ∷
   rw 28 q16 ∷
   rw 27 q17 ∷
   rw 26 q18 ∷
   re 26 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 26 5 (CK03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CZ13 ∷ []) ∷
   rw 27 q16 ∷
   rw 26 q20 ∷
   rw 25 q18 ∷
   re 25 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CZ13 ∷ []) ∷
   rw 26 q16 ∷
   rw 25 q20 ∷
   rw 24 q18 ∷
   re 24 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 22 q21 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CZ13 ∷ []) ∷
   rw 24 q16 ∷
   rw 23 q20 ∷
   rw 22 q18 ∷
   re 22 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CZ13 ∷ []) ∷
   rw 23 q16 ∷
   rw 22 q20 ∷
   rw 21 q18 ∷
   re 21 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q15 ∷
   re 23 3 (CZ13 ∷ []) ∷
   rw 22 q16 ∷
   rw 21 q20 ∷
   rw 20 q18 ∷
   re 20 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 19 q19 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q15 ∷
   re 22 3 (CZ13 ∷ []) ∷
   rw 21 q16 ∷
   rw 20 q20 ∷
   rw 19 q18 ∷
   re 19 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 18 q19 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q15 ∷
   re 21 3 (CZ13 ∷ []) ∷
   rw 20 q16 ∷
   rw 19 q20 ∷
   rw 18 q18 ∷
   re 18 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 17 q19 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q15 ∷
   re 20 3 (CZ13 ∷ []) ∷
   rw 19 q16 ∷
   rw 18 q20 ∷
   rw 17 q18 ∷
   re 17 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 16 q19 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 15 q22 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q15 ∷
   re 18 3 (CZ13 ∷ []) ∷
   rw 17 q16 ∷
   rw 16 q17 ∷
   rw 15 q18 ∷
   re 15 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 14 q19 ∷
   re 15 5 (CK03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CZ13 ∷ []) ∷
   rw 16 q16 ∷
   rw 15 q20 ∷
   rw 14 q18 ∷
   re 14 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 13 q19 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q15 ∷
   re 16 3 (CZ13 ∷ []) ∷
   rw 15 q16 ∷
   rw 14 q20 ∷
   rw 13 q18 ∷
   re 13 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 12 q19 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q15 ∷
   re 15 3 (CZ13 ∷ []) ∷
   rw 14 q16 ∷
   rw 13 q20 ∷
   rw 12 q18 ∷
   re 12 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 11 q19 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 10 q22 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q15 ∷
   re 13 3 (CZ13 ∷ []) ∷
   rw 12 q16 ∷
   rw 11 q17 ∷
   rw 10 q18 ∷
   re 10 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 9 q19 ∷
   re 10 5 (CK03 ∷ []) ∷
   rw 8 q22 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q15 ∷
   re 11 3 (CZ13 ∷ []) ∷
   rw 10 q16 ∷
   rw 9 q17 ∷
   rw 8 q18 ∷
   re 8 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 7 q19 ∷
   re 8 5 (CK03 ∷ []) ∷
   rw 6 q21 ∷
   rw 5 q23 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 0 q24 ∷
   rw 30 q1 ∷
   re 29 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q6 ∷
   rw 30 q7 ∷
   rw⁻ 29 q6 ∷
   re 30 3 (CK13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q6 ∷
   rw 29 q7 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (CK13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q6 ∷
   rw 28 q8 ∷
   rw⁻ 27 q6 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q6 ∷
   rw 27 q7 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (CK13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q6 ∷
   rw 26 q8 ∷
   rw⁻ 25 q6 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q6 ∷
   rw 25 q8 ∷
   rw⁻ 24 q6 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 23 q25 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q6 ∷
   rw 23 q8 ∷
   rw⁻ 22 q6 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q6 ∷
   rw 22 q8 ∷
   rw⁻ 21 q6 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q6 ∷
   rw 21 q8 ∷
   rw⁻ 20 q6 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q6 ∷
   rw 20 q8 ∷
   rw⁻ 19 q6 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q6 ∷
   rw 19 q8 ∷
   rw⁻ 18 q6 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q6 ∷
   rw 18 q8 ∷
   rw⁻ 17 q6 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 16 q26 ∷
   re 15 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q6 ∷
   rw 16 q7 ∷
   rw⁻ 15 q6 ∷
   re 16 3 (CK13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q6 ∷
   rw 15 q8 ∷
   rw⁻ 14 q6 ∷
   re 15 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q6 ∷
   rw 14 q8 ∷
   rw⁻ 13 q6 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q6 ∷
   rw 13 q8 ∷
   rw⁻ 12 q6 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q26 ∷
   re 10 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q6 ∷
   rw 11 q7 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (CK13 ∷ []) ∷
   rw 9 q26 ∷
   re 8 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q6 ∷
   rw 9 q7 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (CK13 ∷ []) ∷
   rw 7 q25 ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 1 q3 ∷
   rw 2 q27 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q6 ∷
   rw 2 q13 ∷
   rw 3 q6 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q13 ∷
   rw 4 q6 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q11 ∷
   rw 5 q6 ∷
   re 3 3 (CK03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 5 q13 ∷
   rw 6 q6 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   rw 7 q6 ∷
   re 5 3 (CK03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q11 ∷
   rw 8 q6 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw 7 q28 ∷
   rw 8 q2 ∷
   rw 9 q5 ∷
   rw 10 q2 ∷
   rw 11 q5 ∷
   rw 12 q3 ∷
   rw 13 q3 ∷
   rw 14 q3 ∷
   rw 15 q2 ∷
   rw 16 q5 ∷
   rw 17 q3 ∷
   rw 18 q3 ∷
   rw 19 q3 ∷
   rw 20 q3 ∷
   rw 21 q3 ∷
   rw 22 q3 ∷
   rw 23 q28 ∷
   rw 24 q3 ∷
   rw 25 q3 ∷
   rw 26 q2 ∷
   rw 27 q3 ∷
   rw 28 q2 ∷
   rw 29 q2 ∷
   rw 30 q14 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS12 ∷ []) (CS12 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (wn 1325 W)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [CS02]: 111 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CS02 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CS02 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS02 ∷ []) (CS02 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw 30 q1 ∷
   rw 29 q8 ∷
   rw⁻ 28 q2 ∷
   rw⁻ 27 q2 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 25 q2 ∷
   rw⁻ 24 q3 ∷
   rw⁻ 23 q3 ∷
   rw 22 q4 ∷
   rw⁻ 21 q3 ∷
   rw⁻ 20 q3 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 16 q3 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 14 q2 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 7 q2 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 6 q7 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (CK13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q7 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CK13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 4 q8 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 3 q7 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (CK13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q8 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 1 q8 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q29 ∷
   rw 0 q13 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q6 ∷
   rw 2 q13 ∷
   rw 3 q6 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q13 ∷
   rw 4 q6 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 4 q11 ∷
   rw 5 q6 ∷
   re 3 3 (CK03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 5 q13 ∷
   rw 6 q6 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   rw 7 q6 ∷
   re 5 3 (CK03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q11 ∷
   rw 8 q6 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw 7 q28 ∷
   rw 8 q2 ∷
   rw 9 q5 ∷
   rw 10 q2 ∷
   rw 11 q5 ∷
   rw 12 q3 ∷
   rw 13 q3 ∷
   rw 14 q3 ∷
   rw 15 q2 ∷
   rw 16 q5 ∷
   rw 17 q3 ∷
   rw 18 q3 ∷
   rw 19 q3 ∷
   rw 20 q3 ∷
   rw 21 q3 ∷
   rw 22 q3 ∷
   rw 23 q28 ∷
   rw 24 q3 ∷
   rw 25 q3 ∷
   rw 26 q2 ∷
   rw 27 q3 ∷
   rw 28 q2 ∷
   rw 29 q2 ∷
   rw 30 q14 ∷ []) Eq.refl
