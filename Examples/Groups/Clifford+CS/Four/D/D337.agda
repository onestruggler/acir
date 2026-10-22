{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D337 (W : Ws) where

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
  q1 = wE 879 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 353 W
  q4 : Eqn
  q4 = eqn (CK10 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S • CK₀₁)))
  q5 : Eqn
  q5 = wE 358 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 880 W
  q8 : Eqn
  q8 = eqn (CS01 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S • CK₀₁)))
  q9 : Eqn
  q9 = wE 918 W
  q10 : Eqn
  q10 = eqn (X1 ∷ S2 ∷ []) (S2 ∷ X1 ∷ []) (low-comm ((X ↑)) (S))
  q11 : Eqn
  q11 = wE 706 W
  q12 : Eqn
  q12 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q13 : Eqn
  q13 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q14 : Eqn
  q14 = wE 921 W
  q15 : Eqn
  q15 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q16 : Eqn
  q16 = wE 919 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [X1 CKd13 X1]: 395 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CKd13-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CKd13-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 28 q1 ∷
   re 30 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CK13⁻ ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 29 3 (CK13⁻ ∷ []) ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   re 29 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CK13⁻ ∷ []) ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 28 3 (CK13⁻ ∷ []) ∷
   rw 29 q1 ∷
   rw 26 q7 ∷
   re 28 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CK13⁻ ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q8 ∷
   rw 29 q5 ∷
   re 29 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 27 3 (CK13⁻ ∷ []) ∷
   rw 28 q7 ∷
   rw 25 q1 ∷
   re 27 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CK13⁻ ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 26 3 (CK13⁻ ∷ []) ∷
   rw 27 q1 ∷
   rw 24 q7 ∷
   re 26 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CK13⁻ ∷ []) ∷
   rw 29 q3 ∷
   rw 28 q8 ∷
   rw 27 q5 ∷
   re 27 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 25 3 (CK13⁻ ∷ []) ∷
   rw 26 q7 ∷
   rw 23 q7 ∷
   re 25 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CK13⁻ ∷ []) ∷
   rw 28 q3 ∷
   rw 27 q8 ∷
   rw 26 q5 ∷
   re 26 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 24 3 (CK13⁻ ∷ []) ∷
   rw 25 q7 ∷
   rw 22 q9 ∷
   rw 21 q7 ∷
   re 23 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CK13⁻ ∷ []) ∷
   rw 26 q3 ∷
   rw 25 q8 ∷
   rw 24 q5 ∷
   re 24 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 22 3 (CK13⁻ ∷ []) ∷
   rw 23 q7 ∷
   rw 20 q7 ∷
   re 22 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CK13⁻ ∷ []) ∷
   rw 25 q3 ∷
   rw 24 q8 ∷
   rw 23 q5 ∷
   re 23 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 21 3 (CK13⁻ ∷ []) ∷
   rw 22 q7 ∷
   rw 19 q7 ∷
   re 21 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CK13⁻ ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q8 ∷
   rw 22 q5 ∷
   re 22 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 20 3 (CK13⁻ ∷ []) ∷
   rw 21 q7 ∷
   rw 18 q7 ∷
   re 20 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CK13⁻ ∷ []) ∷
   rw 23 q3 ∷
   rw 22 q8 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 19 3 (CK13⁻ ∷ []) ∷
   rw 20 q7 ∷
   rw 17 q7 ∷
   re 19 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CK13⁻ ∷ []) ∷
   rw 22 q3 ∷
   rw 21 q8 ∷
   rw 20 q5 ∷
   re 20 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 18 3 (CK13⁻ ∷ []) ∷
   rw 19 q7 ∷
   rw 16 q7 ∷
   re 18 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CK13⁻ ∷ []) ∷
   rw 21 q3 ∷
   rw 20 q8 ∷
   rw 19 q5 ∷
   re 19 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 17 3 (CK13⁻ ∷ []) ∷
   rw 18 q7 ∷
   rw⁻ 15 q10 ∷
   rw 16 q11 ∷
   rw⁻ 17 q10 ∷
   rw 14 q1 ∷
   re 16 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 16 3 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 20 3 (CK13⁻ ∷ []) ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   rw 17 q5 ∷
   re 17 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 17 5 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 15 3 (CK13⁻ ∷ []) ∷
   rw 16 q1 ∷
   rw 13 q7 ∷
   re 15 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 19 3 (CK13⁻ ∷ []) ∷
   rw 18 q3 ∷
   rw 17 q8 ∷
   rw 16 q5 ∷
   re 16 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 14 3 (CK13⁻ ∷ []) ∷
   rw 15 q7 ∷
   rw 12 q7 ∷
   re 14 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CK13⁻ ∷ []) ∷
   rw 17 q3 ∷
   rw 16 q8 ∷
   rw 15 q5 ∷
   re 15 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   re 13 3 (CK13⁻ ∷ []) ∷
   rw 14 q7 ∷
   rw 11 q7 ∷
   re 13 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 17 3 (CK13⁻ ∷ []) ∷
   rw 16 q3 ∷
   rw 15 q8 ∷
   rw 14 q5 ∷
   re 14 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 12 3 (CK13⁻ ∷ []) ∷
   rw 13 q7 ∷
   rw⁻ 10 q10 ∷
   rw 11 q11 ∷
   rw⁻ 12 q10 ∷
   rw 9 q1 ∷
   re 11 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 11 3 (CK30 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 15 3 (CK13⁻ ∷ []) ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   re 12 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   re 12 5 (CK30 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 10 3 (CK13⁻ ∷ []) ∷
   rw 11 q1 ∷
   rw⁻ 8 q10 ∷
   rw 9 q11 ∷
   rw⁻ 10 q10 ∷
   rw 7 q1 ∷
   re 9 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 9 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 13 3 (CK13⁻ ∷ []) ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   re 10 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   re 10 5 (CK30 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   re 8 3 (CK13⁻ ∷ []) ∷
   rw 9 q1 ∷
   rw 6 q9 ∷
   rw 9 q2 ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q12 ∷
   rw 5 q13 ∷
   rw 6 q14 ∷
   rw⁻ 5 q12 ∷
   rw 8 q2 ∷
   re 6 3 (CK13⁻ ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw⁻ 8 q13 ∷
   rw 9 q6 ∷
   rw 8 q2 ∷
   rw 7 q12 ∷
   re 6 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q12 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw⁻ 4 q12 ∷
   rw 7 q2 ∷
   re 5 3 (CK13⁻ ∷ []) ∷
   rw⁻ 6 q12 ∷
   rw⁻ 7 q13 ∷
   rw 8 q6 ∷
   rw 7 q2 ∷
   rw 6 q12 ∷
   re 5 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q12 ∷
   rw 3 q15 ∷
   rw 4 q16 ∷
   rw⁻ 3 q12 ∷
   rw 6 q2 ∷
   re 4 3 (CK13⁻ ∷ []) ∷
   rw⁻ 5 q12 ∷
   rw⁻ 6 q15 ∷
   rw 7 q6 ∷
   rw 6 q2 ∷
   rw 5 q12 ∷
   re 4 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q12 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw⁻ 2 q12 ∷
   rw 5 q2 ∷
   re 3 3 (CK13⁻ ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw⁻ 5 q13 ∷
   rw 6 q6 ∷
   rw 5 q2 ∷
   rw 4 q12 ∷
   re 3 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q12 ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw⁻ 1 q12 ∷
   rw 4 q2 ∷
   re 2 3 (CK13⁻ ∷ []) ∷
   rw⁻ 3 q12 ∷
   rw⁻ 4 q15 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   rw 3 q12 ∷
   re 2 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q12 ∷
   rw 0 q15 ∷
   rw 1 q16 ∷
   rw⁻ 0 q12 ∷
   rw 3 q2 ∷
   re 1 3 (CK13⁻ ∷ []) ∷
   rw⁻ 2 q12 ∷
   rw⁻ 3 q15 ∷
   rw 4 q6 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 896 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [X1 CS01 CS01 CK10 CS01 X1]: 1 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CS01-CS01-CK10-CS01-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CS01-CS01-CK10-CS01-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q17 ∷ []) Eq.refl
