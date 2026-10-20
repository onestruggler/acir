{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D694 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D656 W using (lem-pass-X0-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-vs-X3-TOFF123-X3)

private
  q1 : Eqn
  q1 = eqn (Toff123 ∷ []) (X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ []) (wn 1776 W)
  q2 : Eqn
  q2 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q5 : Eqn
  q5 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q6 : Eqn
  q6 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q7 : Eqn
  q7 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q10 : Eqn
  q10 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q13 : Eqn
  q13 = eqn (X3 ∷ X1 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X1 ∷ X2 ∷ X3 ∷ []) (X1 ∷ X2 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X1 ∷ X2 ∷ X3 ∷ []) (wn 2030 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q20 : Eqn
  q20 = eqn (X0 ∷ X2 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X0 ∷ X2 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ []) lem-pass-X0-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-vs-X3-TOFF123-X3
  q21 : Eqn
  q21 = eqn (X3 ∷ X1 ∷ X2 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X1 ∷ X2 ∷ X3 ∷ X3 ∷ []) (wn 2031 W)
  q22 : Eqn
  q22 = eqn (X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ []) (Toff123 ∷ []) (wn 1779 W)

-- pass [TOFF123] [X0 X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X0 X2 X3]: 181 steps
lem-pass-TOFF123-vs-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 : ⟪ (Toff123 ∷ X0 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 = derive (Toff123 ∷ X0 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ X2 ∷ X3 ∷ Toff123 ∷ [])
  (rw 0 q1 ∷
   rw 40 q2 ∷
   rw⁻ 39 q3 ∷
   rw⁻ 38 q4 ∷
   rw 37 q5 ∷
   rw 36 q6 ∷
   rw 35 q6 ∷
   rw 34 q7 ∷
   rw 33 q6 ∷
   rw 32 q7 ∷
   rw 31 q7 ∷
   re 30 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q8 ∷
   rw 31 q9 ∷
   rw⁻ 30 q8 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 29 q7 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q7 ∷
   rw 24 q7 ∷
   rw 23 q10 ∷
   rw 22 q6 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q10 ∷
   rw 17 q6 ∷
   rw 16 q10 ∷
   rw 15 q6 ∷
   re 14 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q8 ∷
   rw 15 q9 ∷
   rw⁻ 14 q8 ∷
   re 15 3 (CX31 ∷ []) ∷
   rw⁻ 13 q11 ∷
   rw⁻ 12 q11 ∷
   rw⁻ 11 q12 ∷
   rw⁻ 10 q11 ∷
   rw⁻ 9 q12 ∷
   rw⁻ 8 q12 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 6 q4 ∷
   rw 5 q5 ∷
   rw⁻ 4 q3 ∷
   rw 5 q13 ∷
   rw 4 q14 ∷
   rw 5 q4 ∷
   rw 6 q12 ∷
   rw 7 q12 ∷
   rw 8 q11 ∷
   rw 9 q12 ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 12 q8 ∷
   rw 13 q15 ∷
   rw 14 q8 ∷
   re 12 3 (CX30 ∷ []) ∷
   rw 13 q16 ∷
   rw 14 q17 ∷
   rw 15 q16 ∷
   rw 16 q17 ∷
   rw 17 q18 ∷
   rw 18 q18 ∷
   rw 19 q18 ∷
   rw 20 q16 ∷
   rw 21 q17 ∷
   rw 22 q18 ∷
   rw 23 q18 ∷
   rw 24 q18 ∷
   rw 25 q18 ∷
   rw 26 q18 ∷
   rw 27 q18 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q8 ∷
   rw 29 q15 ∷
   rw 30 q8 ∷
   re 28 3 (CX30 ∷ []) ∷
   rw 29 q18 ∷
   rw 30 q18 ∷
   rw 31 q16 ∷
   rw 32 q18 ∷
   rw 33 q16 ∷
   rw 34 q16 ∷
   rw 35 q14 ∷
   rw 36 q4 ∷
   rw 37 q3 ∷
   rw 38 q19 ∷
   rw⁻ 1 q20 ∷
   rw 34 q2 ∷
   rw⁻ 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   rw 30 q6 ∷
   rw 29 q7 ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   re 25 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q8 ∷
   rw 26 q9 ∷
   rw⁻ 25 q8 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 24 q7 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q10 ∷
   rw 17 q6 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   rw 14 q7 ∷
   rw 13 q10 ∷
   rw 12 q6 ∷
   rw 11 q10 ∷
   rw 10 q6 ∷
   re 9 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q8 ∷
   rw 10 q9 ∷
   rw⁻ 9 q8 ∷
   re 10 3 (CX31 ∷ []) ∷
   rw⁻ 8 q11 ∷
   rw⁻ 7 q11 ∷
   rw⁻ 6 q12 ∷
   rw⁻ 5 q11 ∷
   rw⁻ 4 q12 ∷
   rw⁻ 3 q12 ∷
   rw⁻ 2 q4 ∷
   rw 1 q5 ∷
   rw⁻ 0 q3 ∷
   rw 1 q21 ∷
   rw 0 q14 ∷
   rw 1 q4 ∷
   rw 2 q3 ∷
   rw 3 q12 ∷
   rw 4 q12 ∷
   rw 5 q11 ∷
   rw 6 q12 ∷
   rw 7 q11 ∷
   rw 8 q11 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 10 q15 ∷
   rw 11 q8 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw 10 q16 ∷
   rw 11 q17 ∷
   rw 12 q16 ∷
   rw 13 q17 ∷
   rw 14 q18 ∷
   rw 15 q18 ∷
   rw 16 q18 ∷
   rw 17 q16 ∷
   rw 18 q17 ∷
   rw 19 q18 ∷
   rw 20 q18 ∷
   rw 21 q18 ∷
   rw 22 q18 ∷
   rw 23 q18 ∷
   rw 24 q18 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q8 ∷
   rw 26 q15 ∷
   rw 27 q8 ∷
   re 25 3 (CX30 ∷ []) ∷
   rw 26 q18 ∷
   rw 27 q18 ∷
   rw 28 q16 ∷
   rw 29 q18 ∷
   rw 30 q16 ∷
   rw 31 q16 ∷
   rw 32 q14 ∷
   rw 33 q4 ∷
   rw 34 q3 ∷
   rw 35 q3 ∷
   rw 36 q19 ∷
   rw 35 q22 ∷ []) Eq.refl
