{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D505 (W : Ws) where

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
  q1 = eqn (CS01⁻ ∷ CK23 ∷ []) (CK23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₀₁))
  q2 : Eqn
  q2 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q3 : Eqn
  q3 = eqn (CX02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CX02 ∷ []) (wn 1291 W)
  q4 : Eqn
  q4 = eqn (CS01⁻ ∷ S2 ∷ []) (S2 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (S))
  q5 : Eqn
  q5 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q6 : Eqn
  q6 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q7 : Eqn
  q7 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q8 : Eqn
  q8 = eqn (CK02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CK02 ∷ []) (wn 1292 W)
  q9 : Eqn
  q9 = eqn (CS02 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS02 ∷ []) (wn 246 W)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [CSd01]: 77 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CSd01 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-CSd01 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
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
  q11 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q12 : Eqn
  q12 = eqn (CK02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK12⁻ ∷ []) (wn 1228 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q15 : Eqn
  q15 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q19 : Eqn
  q19 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q20 : Eqn
  q20 = eqn (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) (X1 ∷ CK12⁻ ∷ X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (wn 1328 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CK12⁻ ∷ []) (CK02⁻ ∷ Sw01 ∷ []) (wn 330 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [X0 CKd02 X0]: 115 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CKd02-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CKd02-X0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw 32 q10 ∷
   rw 31 q11 ∷
   rw 30 q12 ∷
   rw 29 q11 ∷
   rw⁻ 28 q13 ∷
   rw⁻ 27 q13 ∷
   rw⁻ 26 q14 ∷
   rw⁻ 25 q13 ∷
   rw⁻ 24 q14 ∷
   rw⁻ 23 q14 ∷
   rw 22 q15 ∷
   rw⁻ 21 q14 ∷
   rw⁻ 20 q14 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 18 q14 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 16 q14 ∷
   rw⁻ 15 q16 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 13 q14 ∷
   rw⁻ 12 q14 ∷
   rw⁻ 11 q14 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 9 q13 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 7 q13 ∷
   rw 6 q15 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q17 ∷
   rw 6 q18 ∷
   rw⁻ 5 q17 ∷
   re 6 3 (CK13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q17 ∷
   rw 5 q18 ∷
   rw⁻ 4 q17 ∷
   re 5 3 (CK13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q17 ∷
   rw 4 q19 ∷
   rw⁻ 3 q17 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q17 ∷
   rw 3 q18 ∷
   rw⁻ 2 q17 ∷
   re 3 3 (CK13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q17 ∷
   rw 2 q19 ∷
   rw⁻ 1 q17 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q17 ∷
   rw 1 q19 ∷
   rw⁻ 0 q17 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q20 ∷
   rw 0 q21 ∷
   rw 1 q22 ∷
   rw 2 q21 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   rw 4 q23 ∷
   rw 5 q17 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw 5 q23 ∷
   rw 6 q17 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 6 q24 ∷
   rw 7 q17 ∷
   re 5 3 (CK03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 7 q23 ∷
   rw 8 q17 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 8 q24 ∷
   rw 9 q17 ∷
   re 7 3 (CK03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw 9 q24 ∷
   rw 10 q17 ∷
   re 8 3 (CK03 ∷ []) ∷
   rw 9 q25 ∷
   rw 10 q13 ∷
   rw 11 q16 ∷
   rw 12 q13 ∷
   rw 13 q16 ∷
   rw 14 q14 ∷
   rw 15 q14 ∷
   rw 16 q14 ∷
   rw 17 q13 ∷
   rw 18 q16 ∷
   rw 19 q14 ∷
   rw 20 q14 ∷
   rw 21 q14 ∷
   rw 22 q14 ∷
   rw 23 q14 ∷
   rw 24 q14 ∷
   rw 25 q25 ∷
   rw 26 q14 ∷
   rw 27 q14 ∷
   rw 28 q13 ∷
   rw 29 q14 ∷
   rw 30 q13 ∷
   rw 31 q13 ∷
   rw 32 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (Toff201 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ Toff201 ∷ []) (wn 1295 W)

-- pass [TOFF201] [X0 TOFF201 X0]: 1 steps
lem-pass-TOFF201-vs-X0-TOFF201-X0 : ⟪ (Toff201 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ Toff201 ∷ X0 ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-X0-TOFF201-X0 = derive (Toff201 ∷ X0 ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ Toff201 ∷ X0 ∷ Toff201 ∷ [])
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X1 ∷ CK12 ∷ X1 ∷ []) (X1 ∷ CK12 ∷ X1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CS13 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) (wn 1329 W)

-- pass [CS03 CS03 CS03 CK03 CS03 CS03 CX02 CS23 CS23 CS23 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CS23 CK23 CS23 CS23] [X0 CK02 X0]: 119 steps
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CK02-X0 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CK02-X0 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ [])
  (rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q18 ∷
   rw 31 q11 ∷
   rw⁻ 30 q14 ∷
   rw⁻ 29 q14 ∷
   rw⁻ 28 q13 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q14 ∷
   rw⁻ 25 q14 ∷
   rw 24 q15 ∷
   rw⁻ 23 q14 ∷
   rw⁻ 22 q14 ∷
   rw⁻ 21 q14 ∷
   rw⁻ 20 q14 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 18 q14 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 16 q14 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 14 q16 ∷
   rw⁻ 13 q13 ∷
   rw⁻ 12 q14 ∷
   rw⁻ 11 q14 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q14 ∷
   rw⁻ 7 q14 ∷
   rw 6 q15 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q17 ∷
   rw 6 q19 ∷
   rw⁻ 5 q17 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q17 ∷
   rw 5 q19 ∷
   rw⁻ 4 q17 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q17 ∷
   rw 4 q18 ∷
   rw⁻ 3 q17 ∷
   re 4 3 (CK13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q17 ∷
   rw 3 q19 ∷
   rw⁻ 2 q17 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q17 ∷
   rw 2 q19 ∷
   rw⁻ 1 q17 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q17 ∷
   rw 1 q19 ∷
   rw⁻ 0 q17 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q28 ∷
   rw 0 q21 ∷
   rw 1 q24 ∷
   rw 2 q21 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   rw 4 q23 ∷
   rw 5 q17 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw 5 q23 ∷
   rw 6 q17 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 6 q23 ∷
   rw 7 q17 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 7 q24 ∷
   rw 8 q17 ∷
   re 6 3 (CK03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 8 q23 ∷
   rw 9 q17 ∷
   re 7 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw 9 q23 ∷
   rw 10 q17 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q25 ∷
   rw 10 q14 ∷
   rw 11 q14 ∷
   rw 12 q14 ∷
   rw 13 q14 ∷
   rw 14 q14 ∷
   rw 15 q14 ∷
   rw 16 q13 ∷
   rw 17 q16 ∷
   rw 18 q14 ∷
   rw 19 q14 ∷
   rw 20 q14 ∷
   rw 21 q14 ∷
   rw 22 q14 ∷
   rw 23 q14 ∷
   rw 24 q14 ∷
   rw 25 q14 ∷
   rw 26 q14 ∷
   rw 27 q25 ∷
   rw 28 q14 ∷
   rw 29 q14 ∷
   rw 30 q14 ∷
   rw 31 q13 ∷
   rw 32 q14 ∷
   rw 33 q14 ∷
   rw 34 q26 ∷ []) Eq.refl
