{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD690 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D690 (W : Ws) (Sᴰ : SD690) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-vs-X3-TOFF123-X3 : St 1832
  lem-pass-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-vs-X3-TOFF123-X3 = pickᴰ 0 Sᴰ

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
  q5 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q6 : Eqn
  q6 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q9 : Eqn
  q9 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q12 : Eqn
  q12 = eqn (X3 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X2 ∷ X3 ∷ []) (X2 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X2 ∷ X3 ∷ []) (wn 1782 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ S1 ∷ []) (S0 ∷ Sw01 ∷ []) (wn 315 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q18 : Eqn
  q18 = eqn (X2 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ X2 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ []) lem-pass-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-vs-X3-TOFF123-X3
  q19 : Eqn
  q19 = eqn (X3 ∷ X2 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X2 ∷ []) (X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK12 ∷ CK12 ∷ X2 ∷ X3 ∷ X3 ∷ []) (wn 1783 W)
  q20 : Eqn
  q20 = eqn (X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ []) (Toff123 ∷ []) (wn 1779 W)

-- pass [TOFF123] [X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X2 X3]: 173 steps
lem-pass-TOFF123-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 : ⟪ (Toff123 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 = derive (Toff123 ∷ X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X2 ∷ X3 ∷ Toff123 ∷ [])
  (rw 0 q1 ∷
   rw 38 q2 ∷
   rw⁻ 37 q3 ∷
   rw⁻ 36 q4 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw 33 q6 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   rw 30 q6 ∷
   re 29 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q7 ∷
   rw 30 q8 ∷
   rw⁻ 29 q7 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 28 q6 ∷
   rw 27 q6 ∷
   rw 26 q6 ∷
   rw 25 q6 ∷
   rw 24 q6 ∷
   rw 23 q6 ∷
   rw 22 q9 ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q9 ∷
   rw 16 q5 ∷
   rw 15 q9 ∷
   rw 14 q5 ∷
   re 13 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q7 ∷
   rw 14 q8 ∷
   rw⁻ 13 q7 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw⁻ 12 q10 ∷
   rw⁻ 11 q10 ∷
   rw⁻ 10 q11 ∷
   rw⁻ 9 q10 ∷
   rw⁻ 8 q11 ∷
   rw⁻ 7 q11 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 4 q3 ∷
   rw 5 q12 ∷
   rw 4 q4 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   rw 7 q10 ∷
   rw 8 q11 ∷
   rw 9 q10 ∷
   rw 10 q10 ∷
   re 12 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q13 ∷
   rw 13 q7 ∷
   re 11 3 (CX30 ∷ []) ∷
   rw 12 q14 ∷
   rw 13 q15 ∷
   rw 14 q14 ∷
   rw 15 q15 ∷
   rw 16 q16 ∷
   rw 17 q16 ∷
   rw 18 q16 ∷
   rw 19 q14 ∷
   rw 20 q15 ∷
   rw 21 q16 ∷
   rw 22 q16 ∷
   rw 23 q16 ∷
   rw 24 q16 ∷
   rw 25 q16 ∷
   rw 26 q16 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q7 ∷
   rw 28 q13 ∷
   rw 29 q7 ∷
   re 27 3 (CX30 ∷ []) ∷
   rw 28 q16 ∷
   rw 29 q16 ∷
   rw 30 q14 ∷
   rw 31 q16 ∷
   rw 32 q14 ∷
   rw 33 q14 ∷
   rw 34 q4 ∷
   rw 35 q3 ∷
   rw 36 q17 ∷
   rw⁻ 1 q18 ∷
   rw 32 q2 ∷
   rw⁻ 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q6 ∷
   re 24 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q7 ∷
   rw 25 q8 ∷
   rw⁻ 24 q7 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 23 q6 ∷
   rw 22 q6 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q9 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q6 ∷
   rw 13 q6 ∷
   rw 12 q9 ∷
   rw 11 q5 ∷
   rw 10 q9 ∷
   rw 9 q5 ∷
   re 8 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q7 ∷
   rw 9 q8 ∷
   rw⁻ 8 q7 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q10 ∷
   rw⁻ 5 q11 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 3 q11 ∷
   rw⁻ 2 q11 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 0 q3 ∷
   rw 1 q19 ∷
   rw 0 q4 ∷
   rw 1 q3 ∷
   rw 2 q11 ∷
   rw 3 q11 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q10 ∷
   rw 7 q10 ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q13 ∷
   rw 10 q7 ∷
   re 8 3 (CX30 ∷ []) ∷
   rw 9 q14 ∷
   rw 10 q15 ∷
   rw 11 q14 ∷
   rw 12 q15 ∷
   rw 13 q16 ∷
   rw 14 q16 ∷
   rw 15 q16 ∷
   rw 16 q14 ∷
   rw 17 q15 ∷
   rw 18 q16 ∷
   rw 19 q16 ∷
   rw 20 q16 ∷
   rw 21 q16 ∷
   rw 22 q16 ∷
   rw 23 q16 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q7 ∷
   rw 25 q13 ∷
   rw 26 q7 ∷
   re 24 3 (CX30 ∷ []) ∷
   rw 25 q16 ∷
   rw 26 q16 ∷
   rw 27 q14 ∷
   rw 28 q16 ∷
   rw 29 q14 ∷
   rw 30 q14 ∷
   rw 31 q4 ∷
   rw 32 q3 ∷
   rw 33 q3 ∷
   rw 34 q17 ∷
   rw 33 q20 ∷ []) Eq.refl
