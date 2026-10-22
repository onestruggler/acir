{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D507 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 7 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))
  q5 : Eqn
  q5 = wE 74 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 772 W
  q9 : Eqn
  q9 = wE 1332 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 329 W
  q12 : Eqn
  q12 = wE 30 W
  q13 : Eqn
  q13 = wE 31 W

-- pass [CS03 CS03 CS03 CK03 CS03 CS03 CX02 CS23 CS23 CS23 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CS23 CK23 CS23 CS23] [CS02]: 115 steps
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-CS02 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-CS02 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS02 ∷ []) (CS02 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ [])
  (rw 32 q1 ∷
   rw 31 q2 ∷
   rw⁻ 30 q3 ∷
   rw⁻ 29 q3 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 27 q3 ∷
   rw⁻ 26 q3 ∷
   rw⁻ 25 q3 ∷
   rw 24 q5 ∷
   rw⁻ 23 q3 ∷
   rw⁻ 22 q3 ∷
   rw⁻ 21 q3 ∷
   rw⁻ 20 q3 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 16 q3 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 7 q3 ∷
   rw 6 q5 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q2 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q2 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q8 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CK13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q7 ∷
   rw 3 q2 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q7 ∷
   rw 2 q2 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q7 ∷
   rw 1 q2 ∷
   rw⁻ 0 q7 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q9 ∷
   rw 0 q10 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q10 ∷
   rw 3 q7 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 3 q10 ∷
   rw 4 q7 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q11 ∷
   rw 6 q7 ∷
   re 4 3 (CK03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q7 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q10 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q3 ∷
   rw 9 q3 ∷
   rw 10 q3 ∷
   rw 11 q3 ∷
   rw 12 q3 ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q6 ∷
   rw 16 q3 ∷
   rw 17 q3 ∷
   rw 18 q3 ∷
   rw 19 q3 ∷
   rw 20 q3 ∷
   rw 21 q3 ∷
   rw 22 q3 ∷
   rw 23 q3 ∷
   rw 24 q3 ∷
   rw 25 q12 ∷
   rw 26 q3 ∷
   rw 27 q3 ∷
   rw 28 q3 ∷
   rw 29 q4 ∷
   rw 30 q3 ∷
   rw 31 q3 ∷
   rw 32 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q15 : Eqn
  q15 = eqn (CS01 ∷ CK23 ∷ []) (CK23 ∷ CS01 ∷ []) (low-comm (CS) (CK₀₁))
  q16 : Eqn
  q16 = wE 1288 W
  q17 : Eqn
  q17 = eqn (CS01 ∷ S2 ∷ []) (S2 ∷ CS01 ∷ []) (low-comm (CS) (S))
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = wE 3 W
  q21 : Eqn
  q21 = wE 245 W
  q22 : Eqn
  q22 = wE 1289 W

-- pass [CS03 CS03 CS03 CK03 CS03 CS03 CX02 CS23 CS23 CS23 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CS23 CK23 CS23 CS23] [CS01]: 79 steps
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-CS01 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK03-CS03-CS03-CX02-CS23-CS23-CS23-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CS23-CK23-CS23-CS23-vs-CS01 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ CS01 ∷ []) (CS01 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ [])
  (rw⁻ 30 q14 ∷
   rw⁻ 29 q14 ∷
   rw⁻ 28 q15 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q14 ∷
   rw⁻ 25 q14 ∷
   rw 24 q16 ∷
   rw⁻ 23 q14 ∷
   rw⁻ 22 q14 ∷
   rw⁻ 21 q14 ∷
   rw⁻ 20 q14 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 18 q14 ∷
   rw⁻ 17 q14 ∷
   rw⁻ 16 q14 ∷
   rw⁻ 15 q14 ∷
   rw⁻ 14 q17 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 12 q14 ∷
   rw⁻ 11 q14 ∷
   rw⁻ 10 q14 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q14 ∷
   rw⁻ 7 q14 ∷
   rw 6 q16 ∷
   rw 7 q18 ∷
   rw 6 q19 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 6 q21 ∷
   rw⁻ 5 q19 ∷
   rw 8 q18 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q20 ∷
   rw 6 q18 ∷
   rw 5 q19 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q20 ∷
   rw 5 q21 ∷
   rw⁻ 4 q19 ∷
   rw 7 q18 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q20 ∷
   rw 5 q18 ∷
   rw 4 q19 ∷
   re 3 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 4 q22 ∷
   rw⁻ 3 q19 ∷
   rw 6 q18 ∷
   re 4 3 (CK03 ∷ []) ∷
   rw 5 q20 ∷
   rw 4 q18 ∷
   rw 3 q19 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw⁻ 2 q19 ∷
   rw 5 q18 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q20 ∷
   rw 3 q18 ∷
   rw 2 q19 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q20 ∷
   rw 2 q21 ∷
   rw⁻ 1 q19 ∷
   rw 4 q18 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q20 ∷
   rw 2 q18 ∷
   rw 1 q19 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw⁻ 0 q19 ∷
   rw 3 q18 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q20 ∷ []) Eq.refl
