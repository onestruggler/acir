{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D504 (W : Ws) where

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
  q1 = eqn (CS01 ∷ CK23 ∷ []) (CK23 ∷ CS01 ∷ []) (low-comm (CS) (CK₀₁))
  q2 : Eqn
  q2 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q3 : Eqn
  q3 = eqn (CX02 ∷ CS01 ∷ []) (CS01 ∷ CX02 ∷ []) (wn 1288 W)
  q4 : Eqn
  q4 = eqn (CS01 ∷ S2 ∷ []) (S2 ∷ CS01 ∷ []) (low-comm (CS) (S))
  q5 : Eqn
  q5 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q6 : Eqn
  q6 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q7 : Eqn
  q7 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q8 : Eqn
  q8 = eqn (CK02 ∷ CS01 ∷ []) (CS01 ∷ CK02 ∷ []) (wn 1289 W)
  q9 : Eqn
  q9 = eqn (CS02 ∷ CS01 ∷ []) (CS01 ∷ CS02 ∷ []) (wn 245 W)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [CS01]: 77 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CS01 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CS01 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS01 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw⁻ 28 q1 ∷
   rw⁻ 27 q1 ∷
   rw⁻ 26 q2 ∷
   rw⁻ 25 q1 ∷
   rw⁻ 24 q2 ∷
   rw⁻ 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 20 q2 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 18 q2 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 14 q1 ∷
   rw⁻ 13 q2 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 9 q1 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 7 q1 ∷
   rw 6 q3 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q8 ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 5 q8 ∷
   rw⁻ 4 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw 6 q7 ∷
   rw 5 q5 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q9 ∷
   rw⁻ 3 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw⁻ 2 q6 ∷
   rw 5 q5 ∷
   re 3 3 (CK03 ∷ []) ∷
   rw 4 q7 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q9 ∷
   rw⁻ 1 q6 ∷
   rw 4 q5 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q9 ∷
   rw⁻ 0 q6 ∷
   rw 3 q5 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q13 : Eqn
  q13 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q16 : Eqn
  q16 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q17 : Eqn
  q17 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q18 : Eqn
  q18 = eqn (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CX21 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX21 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (wn 1322 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q24 : Eqn
  q24 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q25 : Eqn
  q25 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q26 : Eqn
  q26 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q27 : Eqn
  q27 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q28 : Eqn
  q28 = eqn (CX20 ∷ CX21 ∷ []) (CX21 ∷ CX20 ∷ []) (wn 112 W)
  q29 : Eqn
  q29 = eqn (S0 ∷ CX21 ∷ []) (CX21 ∷ S0 ∷ []) (low₁-comm (S) (CX₁₀))
  q30 : Eqn
  q30 = eqn (CK23 ∷ CX21 ∷ []) (CX21 ∷ CK23 ∷ []) (wn 1326 W)
  q31 : Eqn
  q31 = eqn (CS23 ∷ CX21 ∷ []) (CX21 ∷ CS23 ∷ []) (wn 1327 W)
  q32 : Eqn
  q32 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q33 : Eqn
  q33 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q34 : Eqn
  q34 = eqn (CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CX21 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX21 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (wn 1324 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [CX21]: 487 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CX21 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CX21 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CX21 ∷ []) (CX21 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw 29 q10 ∷
   rw⁻ 28 q11 ∷
   rw⁻ 27 q11 ∷
   rw⁻ 26 q12 ∷
   rw⁻ 25 q11 ∷
   rw⁻ 24 q12 ∷
   rw⁻ 23 q12 ∷
   rw 22 q13 ∷
   rw⁻ 21 q12 ∷
   rw⁻ 20 q12 ∷
   rw⁻ 19 q12 ∷
   rw⁻ 18 q12 ∷
   rw⁻ 17 q12 ∷
   rw⁻ 16 q12 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 14 q11 ∷
   rw⁻ 13 q12 ∷
   rw⁻ 12 q12 ∷
   rw⁻ 11 q12 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 9 q11 ∷
   rw⁻ 8 q14 ∷
   rw⁻ 7 q11 ∷
   rw 6 q13 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw 6 q16 ∷
   rw⁻ 5 q15 ∷
   re 6 3 (CK13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw 5 q16 ∷
   rw⁻ 4 q15 ∷
   re 5 3 (CK13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 4 q17 ∷
   rw⁻ 3 q15 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 3 q16 ∷
   rw⁻ 2 q15 ∷
   re 3 3 (CK13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q15 ∷
   rw 2 q17 ∷
   rw⁻ 1 q15 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q15 ∷
   rw 1 q17 ∷
   rw⁻ 0 q15 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q18 ∷
   rw 0 q12 ∷
   rw 1 q12 ∷
   rw 2 q11 ∷
   rw 3 q12 ∷
   rw 4 q11 ∷
   rw 5 q11 ∷
   rw 6 q19 ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   rw 8 q20 ∷
   rw 9 q15 ∷
   re 7 3 (CK03 ∷ []) ∷
   rw 8 q21 ∷
   re 10 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 9 q15 ∷
   rw 10 q20 ∷
   rw 11 q15 ∷
   re 9 3 (CK03 ∷ []) ∷
   rw 10 q21 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q15 ∷
   rw 12 q22 ∷
   rw 13 q15 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q15 ∷
   rw 13 q22 ∷
   rw 14 q15 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q15 ∷
   rw 14 q22 ∷
   rw 15 q15 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 14 q15 ∷
   rw 15 q20 ∷
   rw 16 q15 ∷
   re 14 3 (CK03 ∷ []) ∷
   rw 15 q21 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q15 ∷
   rw 17 q22 ∷
   rw 18 q15 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q15 ∷
   rw 18 q22 ∷
   rw 19 q15 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q15 ∷
   rw 19 q22 ∷
   rw 20 q15 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q15 ∷
   rw 20 q22 ∷
   rw 21 q15 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q15 ∷
   rw 21 q22 ∷
   rw 22 q15 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q15 ∷
   rw 22 q22 ∷
   rw 23 q15 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q19 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q15 ∷
   rw 24 q22 ∷
   rw 25 q15 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q15 ∷
   rw 25 q22 ∷
   rw 26 q15 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 25 q15 ∷
   rw 26 q20 ∷
   rw 27 q15 ∷
   re 25 3 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q15 ∷
   rw 27 q22 ∷
   rw 28 q15 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 27 q15 ∷
   rw 28 q20 ∷
   rw 29 q15 ∷
   re 27 3 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 28 q15 ∷
   rw 29 q20 ∷
   rw 30 q15 ∷
   re 28 3 (CK03 ∷ []) ∷
   rw 29 q23 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 31 q24 ∷
   rw 30 q25 ∷
   rw 29 q26 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q7 ∷
   re 29 5 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 30 q24 ∷
   rw 29 q25 ∷
   rw 28 q26 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q7 ∷
   re 28 5 (CK03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 29 q24 ∷
   rw 28 q27 ∷
   rw 27 q26 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q7 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 28 q24 ∷
   rw 27 q25 ∷
   rw 26 q26 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q7 ∷
   re 26 5 (CK03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q5 ∷
   re 28 3 (CX31 ∷ []) ∷
   rw 27 q24 ∷
   rw 26 q27 ∷
   rw 25 q26 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q7 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q5 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw 26 q24 ∷
   rw 25 q27 ∷
   rw 24 q26 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q7 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 22 q28 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q5 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 24 q24 ∷
   rw 23 q27 ∷
   rw 22 q26 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q7 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q5 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 23 q24 ∷
   rw 22 q27 ∷
   rw 21 q26 ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q7 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q5 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 22 q24 ∷
   rw 21 q27 ∷
   rw 20 q26 ∷
   re 20 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q5 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 21 q24 ∷
   rw 20 q27 ∷
   rw 19 q26 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q5 ∷
   re 21 3 (CX31 ∷ []) ∷
   rw 20 q24 ∷
   rw 19 q27 ∷
   rw 18 q26 ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q5 ∷
   re 20 3 (CX31 ∷ []) ∷
   rw 19 q24 ∷
   rw 18 q27 ∷
   rw 17 q26 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   re 17 5 (CS03 ∷ []) ∷
   rw 15 q29 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   re 18 3 (CX31 ∷ []) ∷
   rw 17 q24 ∷
   rw 16 q25 ∷
   rw 15 q26 ∷
   re 15 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   re 15 5 (CK03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   re 17 3 (CX31 ∷ []) ∷
   rw 16 q24 ∷
   rw 15 q27 ∷
   rw 14 q26 ∷
   re 14 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   re 16 3 (CX31 ∷ []) ∷
   rw 15 q24 ∷
   rw 14 q27 ∷
   rw 13 q26 ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   re 15 3 (CX31 ∷ []) ∷
   rw 14 q24 ∷
   rw 13 q27 ∷
   rw 12 q26 ∷
   re 12 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 10 q29 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   re 13 3 (CX31 ∷ []) ∷
   rw 12 q24 ∷
   rw 11 q25 ∷
   rw 10 q26 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   re 10 5 (CK03 ∷ []) ∷
   rw 8 q29 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   re 11 3 (CX31 ∷ []) ∷
   rw 10 q24 ∷
   rw 9 q25 ∷
   rw 8 q26 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   re 8 5 (CK03 ∷ []) ∷
   rw 6 q28 ∷
   rw 5 q30 ∷
   rw 4 q30 ∷
   rw 3 q31 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   rw 0 q31 ∷
   rw 30 q10 ∷
   re 29 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q15 ∷
   rw 30 q16 ∷
   rw⁻ 29 q15 ∷
   re 30 3 (CK13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q15 ∷
   rw 29 q16 ∷
   rw⁻ 28 q15 ∷
   re 29 3 (CK13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q15 ∷
   rw 28 q17 ∷
   rw⁻ 27 q15 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q15 ∷
   rw 27 q16 ∷
   rw⁻ 26 q15 ∷
   re 27 3 (CK13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q15 ∷
   rw 26 q17 ∷
   rw⁻ 25 q15 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q15 ∷
   rw 25 q17 ∷
   rw⁻ 24 q15 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 23 q32 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q15 ∷
   rw 23 q17 ∷
   rw⁻ 22 q15 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q15 ∷
   rw 22 q17 ∷
   rw⁻ 21 q15 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q15 ∷
   rw 21 q17 ∷
   rw⁻ 20 q15 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q15 ∷
   rw 20 q17 ∷
   rw⁻ 19 q15 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q15 ∷
   rw 19 q17 ∷
   rw⁻ 18 q15 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q15 ∷
   rw 18 q17 ∷
   rw⁻ 17 q15 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 16 q33 ∷
   re 15 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q15 ∷
   rw 16 q16 ∷
   rw⁻ 15 q15 ∷
   re 16 3 (CK13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q15 ∷
   rw 15 q17 ∷
   rw⁻ 14 q15 ∷
   re 15 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q15 ∷
   rw 14 q17 ∷
   rw⁻ 13 q15 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q15 ∷
   rw 13 q17 ∷
   rw⁻ 12 q15 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q33 ∷
   re 10 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q15 ∷
   rw 11 q16 ∷
   rw⁻ 10 q15 ∷
   re 11 3 (CK13 ∷ []) ∷
   rw 9 q33 ∷
   re 8 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q15 ∷
   rw 9 q16 ∷
   rw⁻ 8 q15 ∷
   re 9 3 (CK13 ∷ []) ∷
   rw 7 q32 ∷
   rw⁻ 6 q11 ∷
   rw⁻ 5 q11 ∷
   rw⁻ 4 q12 ∷
   rw⁻ 3 q11 ∷
   rw⁻ 2 q12 ∷
   rw⁻ 1 q12 ∷
   rw 2 q34 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q15 ∷
   rw 2 q22 ∷
   rw 3 q15 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q15 ∷
   rw 3 q22 ∷
   rw 4 q15 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q20 ∷
   rw 5 q15 ∷
   re 3 3 (CK03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q22 ∷
   rw 6 q15 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q15 ∷
   rw 6 q20 ∷
   rw 7 q15 ∷
   re 5 3 (CK03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q20 ∷
   rw 8 q15 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw 7 q35 ∷
   rw 8 q11 ∷
   rw 9 q14 ∷
   rw 10 q11 ∷
   rw 11 q14 ∷
   rw 12 q12 ∷
   rw 13 q12 ∷
   rw 14 q12 ∷
   rw 15 q11 ∷
   rw 16 q14 ∷
   rw 17 q12 ∷
   rw 18 q12 ∷
   rw 19 q12 ∷
   rw 20 q12 ∷
   rw 21 q12 ∷
   rw 22 q12 ∷
   rw 23 q35 ∷
   rw 24 q12 ∷
   rw 25 q12 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 29 q11 ∷
   rw 30 q23 ∷ []) Eq.refl
