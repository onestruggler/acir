{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D509 (W : Ws) where

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
  q1 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q2 : Eqn
  q2 = eqn (CS01⁻ ∷ CK23 ∷ []) (CK23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₀₁))
  q3 : Eqn
  q3 = wE 1291 W
  q4 : Eqn
  q4 = eqn (CS01⁻ ∷ S2 ∷ []) (S2 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (S))
  q5 : Eqn
  q5 = wE 1 W
  q6 : Eqn
  q6 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 246 W
  q9 : Eqn
  q9 = wE 1292 W

-- pass [CS03 CS03 CS03 CK03 CS03 CS03 CX02 CS23 CS23 CS23 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CS23 CK23 CS23 CS23] [CSd01]: 79 steps
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-CSd01 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-CSd01 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ [])
  (rw⁻ 30 q1 ∷
   rw⁻ 29 q1 ∷
   rw⁻ 28 q2 ∷
   rw⁻ 27 q1 ∷
   rw⁻ 26 q1 ∷
   rw⁻ 25 q1 ∷
   rw 24 q3 ∷
   rw⁻ 23 q1 ∷
   rw⁻ 22 q1 ∷
   rw⁻ 21 q1 ∷
   rw⁻ 20 q1 ∷
   rw⁻ 19 q1 ∷
   rw⁻ 18 q1 ∷
   rw⁻ 17 q1 ∷
   rw⁻ 16 q1 ∷
   rw⁻ 15 q1 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 13 q2 ∷
   rw⁻ 12 q1 ∷
   rw⁻ 11 q1 ∷
   rw⁻ 10 q1 ∷
   rw⁻ 9 q1 ∷
   rw⁻ 8 q1 ∷
   rw⁻ 7 q1 ∷
   rw 6 q3 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q8 ∷
   rw⁻ 5 q6 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 5 q8 ∷
   rw⁻ 4 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q7 ∷
   rw 5 q5 ∷
   rw 4 q6 ∷
   re 3 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q9 ∷
   rw⁻ 3 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CK03 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw⁻ 2 q6 ∷
   rw 5 q5 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q7 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q8 ∷
   rw⁻ 1 q6 ∷
   rw 4 q5 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 1 q8 ∷
   rw⁻ 0 q6 ∷
   rw 3 q5 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 5 W
  q11 : Eqn
  q11 = wE 1106 W
  q12 : Eqn
  q12 = wE 1228 W
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))
  q15 : Eqn
  q15 = wE 74 W
  q16 : Eqn
  q16 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = wE 772 W
  q20 : Eqn
  q20 = wE 1333 W
  q21 : Eqn
  q21 = wE 317 W
  q22 : Eqn
  q22 = wE 330 W
  q23 : Eqn
  q23 = wE 27 W
  q24 : Eqn
  q24 = wE 329 W
  q25 : Eqn
  q25 = wE 30 W
  q26 : Eqn
  q26 = wE 31 W

-- pass [CS03 CS03 CS03 CK03 CS03 CS03 CX02 CS23 CS23 CS23 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CS23 CK23 CS23 CS23] [X0 CKd02 X0]: 119 steps
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CKd02-X0 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-X0-CKd02-X0 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X0 ∷ CK02⁻ ∷ X0 ∷ []) (X0 ∷ CK02⁻ ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ [])
  (rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q12 ∷
   rw 31 q11 ∷
   rw⁻ 30 q13 ∷
   rw⁻ 29 q13 ∷
   rw⁻ 28 q14 ∷
   rw⁻ 27 q13 ∷
   rw⁻ 26 q13 ∷
   rw⁻ 25 q13 ∷
   rw 24 q15 ∷
   rw⁻ 23 q13 ∷
   rw⁻ 22 q13 ∷
   rw⁻ 21 q13 ∷
   rw⁻ 20 q13 ∷
   rw⁻ 19 q13 ∷
   rw⁻ 18 q13 ∷
   rw⁻ 17 q13 ∷
   rw⁻ 16 q13 ∷
   rw⁻ 15 q13 ∷
   rw⁻ 14 q16 ∷
   rw⁻ 13 q14 ∷
   rw⁻ 12 q13 ∷
   rw⁻ 11 q13 ∷
   rw⁻ 10 q13 ∷
   rw⁻ 9 q13 ∷
   rw⁻ 8 q13 ∷
   rw⁻ 7 q13 ∷
   rw 6 q15 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q17 ∷
   rw 6 q18 ∷
   rw⁻ 5 q17 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q17 ∷
   rw 5 q18 ∷
   rw⁻ 4 q17 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q17 ∷
   rw 4 q19 ∷
   rw⁻ 3 q17 ∷
   re 4 3 (CK13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q17 ∷
   rw 3 q18 ∷
   rw⁻ 2 q17 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q17 ∷
   rw 2 q18 ∷
   rw⁻ 1 q17 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q17 ∷
   rw 1 q18 ∷
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
   rw 10 q13 ∷
   rw 11 q13 ∷
   rw 12 q13 ∷
   rw 13 q13 ∷
   rw 14 q13 ∷
   rw 15 q13 ∷
   rw 16 q14 ∷
   rw 17 q16 ∷
   rw 18 q13 ∷
   rw 19 q13 ∷
   rw 20 q13 ∷
   rw 21 q13 ∷
   rw 22 q13 ∷
   rw 23 q13 ∷
   rw 24 q13 ∷
   rw 25 q13 ∷
   rw 26 q13 ∷
   rw 27 q25 ∷
   rw 28 q13 ∷
   rw 29 q13 ∷
   rw 30 q13 ∷
   rw 31 q14 ∷
   rw 32 q13 ∷
   rw 33 q13 ∷
   rw 34 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1334 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [X0 CS03 CS03 CS03 CK03 CS03 CS03 CX02 CS23 CS23 CS23 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CS23 CK23 CS23 CS23 X0]: 223 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-X0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X0 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw 62 q10 ∷
   rw 61 q11 ∷
   rw⁻ 60 q13 ∷
   rw⁻ 59 q13 ∷
   rw⁻ 58 q14 ∷
   rw⁻ 57 q13 ∷
   rw⁻ 56 q13 ∷
   rw⁻ 55 q13 ∷
   rw 54 q15 ∷
   rw⁻ 53 q13 ∷
   rw⁻ 52 q13 ∷
   rw⁻ 51 q13 ∷
   rw⁻ 50 q13 ∷
   rw⁻ 49 q13 ∷
   rw⁻ 48 q13 ∷
   rw⁻ 47 q13 ∷
   rw⁻ 46 q13 ∷
   rw⁻ 45 q13 ∷
   rw⁻ 44 q16 ∷
   rw⁻ 43 q14 ∷
   rw⁻ 42 q13 ∷
   rw⁻ 41 q13 ∷
   rw⁻ 40 q13 ∷
   rw⁻ 39 q13 ∷
   rw⁻ 38 q13 ∷
   rw⁻ 37 q13 ∷
   rw 36 q15 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q17 ∷
   rw 36 q18 ∷
   rw⁻ 35 q17 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q17 ∷
   rw 35 q18 ∷
   rw⁻ 34 q17 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q17 ∷
   rw 34 q19 ∷
   rw⁻ 33 q17 ∷
   re 34 3 (CK13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q17 ∷
   rw 33 q18 ∷
   rw⁻ 32 q17 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q17 ∷
   rw 32 q18 ∷
   rw⁻ 31 q17 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q17 ∷
   rw 31 q18 ∷
   rw⁻ 30 q17 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 29 q11 ∷
   rw⁻ 28 q14 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q13 ∷
   rw⁻ 25 q14 ∷
   rw⁻ 24 q13 ∷
   rw⁻ 23 q13 ∷
   rw 22 q15 ∷
   rw⁻ 21 q13 ∷
   rw⁻ 20 q13 ∷
   rw⁻ 19 q13 ∷
   rw⁻ 18 q13 ∷
   rw⁻ 17 q13 ∷
   rw⁻ 16 q13 ∷
   rw⁻ 15 q16 ∷
   rw⁻ 14 q14 ∷
   rw⁻ 13 q13 ∷
   rw⁻ 12 q13 ∷
   rw⁻ 11 q13 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 7 q14 ∷
   rw 6 q15 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q17 ∷
   rw 6 q19 ∷
   rw⁻ 5 q17 ∷
   re 6 3 (CK13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q17 ∷
   rw 5 q19 ∷
   rw⁻ 4 q17 ∷
   re 5 3 (CK13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q17 ∷
   rw 4 q18 ∷
   rw⁻ 3 q17 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q17 ∷
   rw 3 q19 ∷
   rw⁻ 2 q17 ∷
   re 3 3 (CK13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q17 ∷
   rw 2 q18 ∷
   rw⁻ 1 q17 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q17 ∷
   rw 1 q18 ∷
   rw⁻ 0 q17 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q27 ∷
   rw 0 q21 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q17 ∷
   rw 2 q23 ∷
   rw 3 q17 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 3 q23 ∷
   rw 4 q17 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   rw 4 q23 ∷
   rw 5 q17 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw 5 q24 ∷
   rw 6 q17 ∷
   re 4 3 (CK03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 6 q23 ∷
   rw 7 q17 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 7 q23 ∷
   rw 8 q17 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q25 ∷
   rw 8 q13 ∷
   rw 9 q13 ∷
   rw 10 q13 ∷
   rw 11 q13 ∷
   rw 12 q13 ∷
   rw 13 q13 ∷
   rw 14 q14 ∷
   rw 15 q16 ∷
   rw 16 q13 ∷
   rw 17 q13 ∷
   rw 18 q13 ∷
   rw 19 q13 ∷
   rw 20 q13 ∷
   rw 21 q13 ∷
   rw 22 q13 ∷
   rw 23 q13 ∷
   rw 24 q13 ∷
   rw 25 q25 ∷
   rw 26 q13 ∷
   rw 27 q13 ∷
   rw 28 q13 ∷
   rw 29 q14 ∷
   rw 30 q13 ∷
   rw 31 q13 ∷
   rw 32 q21 ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q17 ∷
   rw 34 q23 ∷
   rw 35 q17 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q17 ∷
   rw 35 q23 ∷
   rw 36 q17 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 35 q17 ∷
   rw 36 q24 ∷
   rw 37 q17 ∷
   re 35 3 (CK03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q17 ∷
   rw 37 q23 ∷
   rw 38 q17 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 37 q17 ∷
   rw 38 q24 ∷
   rw 39 q17 ∷
   re 37 3 (CK03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 38 q17 ∷
   rw 39 q24 ∷
   rw 40 q17 ∷
   re 38 3 (CK03 ∷ []) ∷
   rw 39 q25 ∷
   rw 40 q14 ∷
   rw 41 q16 ∷
   rw 42 q14 ∷
   rw 43 q16 ∷
   rw 44 q13 ∷
   rw 45 q13 ∷
   rw 46 q13 ∷
   rw 47 q14 ∷
   rw 48 q16 ∷
   rw 49 q13 ∷
   rw 50 q13 ∷
   rw 51 q13 ∷
   rw 52 q13 ∷
   rw 53 q13 ∷
   rw 54 q13 ∷
   rw 55 q25 ∷
   rw 56 q13 ∷
   rw 57 q13 ∷
   rw 58 q14 ∷
   rw 59 q13 ∷
   rw 60 q14 ∷
   rw 61 q14 ∷
   rw 62 q26 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 1335 W

-- L87 iI: 1 steps
lem-L87-iI : ⟪ (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ []) ⟫ʷ
lem-L87-iI = derive (X0 ∷ S0 ∷ X0 ∷ S0 ∷ []) (ι ∷ [])
  (rw 0 q28 ∷ []) Eq.refl
