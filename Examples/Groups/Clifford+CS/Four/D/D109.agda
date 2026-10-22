{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D109 (W : Ws) where

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
  q1 = wE 655 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 157 W
  q4 : Eqn
  q4 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q5 : Eqn
  q5 = wE 158 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q8 : Eqn
  q8 = wE 624 W
  q9 : Eqn
  q9 = wE 625 W
  q10 : Eqn
  q10 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = wE 591 W
  q12 : Eqn
  q12 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q13 : Eqn
  q13 = wE 590 W
  q14 : Eqn
  q14 = wE 656 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [CX13]: 389 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-CX13 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-CX13 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ []) (CX13 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 0 q1 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 30 3 (CX13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 29 3 (CX13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 32 q3 ∷
   rw 31 q7 ∷
   rw 30 q5 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 28 3 (CX13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 27 3 (CX13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 26 3 (CX13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 24 q8 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 23 3 (CX13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 22 3 (CX13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CX13 ∷ []) ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 21 3 (CX13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 20 3 (CX13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CX13 ∷ []) ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 19 3 (CX13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 18 3 (CX13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 17 3 (CX13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 21 3 (CX13 ∷ []) ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   rw 18 q5 ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 16 3 (CX13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 20 3 (CX13 ∷ []) ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   rw 17 q5 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 15 3 (CX13 ∷ []) ∷
   rw 14 q9 ∷
   re 14 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 14 3 (CK30 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CX13 ∷ []) ∷
   rw 17 q3 ∷
   rw 16 q7 ∷
   rw 15 q5 ∷
   re 15 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   re 13 3 (CX13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 17 3 (CX13 ∷ []) ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   rw 14 q5 ∷
   re 14 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 12 3 (CX13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   re 13 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   re 11 3 (CX13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 15 3 (CX13 ∷ []) ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   rw 12 q5 ∷
   re 12 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 10 3 (CX13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   re 14 3 (CX13 ∷ []) ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   re 11 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   re 9 3 (CX13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 13 3 (CX13 ∷ []) ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   re 10 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   re 8 3 (CX13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   re 12 3 (CX13 ∷ []) ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   re 9 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q2 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q2 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw⁻ 6 q10 ∷
   rw 7 q6 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q2 ∷
   re 4 3 (CX13 ∷ []) ∷
   rw⁻ 5 q10 ∷
   rw 6 q6 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q2 ∷
   re 3 3 (CX13 ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q2 ∷
   re 2 3 (CX13 ∷ []) ∷
   rw⁻ 3 q10 ∷
   rw 4 q6 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q10 ∷
   rw 2 q11 ∷
   rw 3 q2 ∷
   re 1 3 (CX13 ∷ []) ∷
   rw⁻ 2 q10 ∷
   rw 3 q6 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q10 ∷
   rw 1 q11 ∷
   rw 2 q2 ∷
   re 0 3 (CX13 ∷ []) ∷
   rw⁻ 1 q10 ∷
   rw 2 q6 ∷
   rw 1 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q16 : Eqn
  q16 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))
  q17 : Eqn
  q17 = wE 457 W
  q18 : Eqn
  q18 = eqn (S1 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((CS • CS • CS)))
  q19 : Eqn
  q19 = wE 5 W
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q21 : Eqn
  q21 = wE 7 W
  q22 : Eqn
  q22 = wE 416 W
  q23 : Eqn
  q23 = wE 27 W
  q24 : Eqn
  q24 = wE 31 W
  q25 : Eqn
  q25 = wE 140 W
  q26 : Eqn
  q26 = wE 626 W
  q27 : Eqn
  q27 = wE 142 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [CSd23]: 67 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd23 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-CSd23 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 30 q15 ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   rw 27 q15 ∷
   rw 26 q15 ∷
   rw 25 q15 ∷
   rw 24 q17 ∷
   rw 23 q15 ∷
   rw 22 q15 ∷
   rw 21 q15 ∷
   rw 20 q15 ∷
   rw 19 q15 ∷
   rw 18 q15 ∷
   rw 17 q15 ∷
   rw 16 q15 ∷
   rw 15 q15 ∷
   rw 14 q18 ∷
   rw 13 q16 ∷
   rw 12 q15 ∷
   rw 11 q15 ∷
   rw 10 q15 ∷
   rw 9 q15 ∷
   rw 8 q15 ∷
   rw 7 q15 ∷
   rw 6 q17 ∷
   rw 7 q19 ∷
   rw⁻ 6 q20 ∷
   rw 5 q21 ∷
   rw 6 q22 ∷
   rw 5 q20 ∷
   rw 6 q23 ∷
   rw 7 q24 ∷
   rw 6 q19 ∷
   rw⁻ 5 q20 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   rw 4 q20 ∷
   rw 5 q23 ∷
   rw 6 q24 ∷
   rw 5 q19 ∷
   rw⁻ 4 q20 ∷
   rw 3 q25 ∷
   rw 4 q26 ∷
   rw 3 q20 ∷
   rw 4 q27 ∷
   rw 5 q24 ∷
   rw 4 q19 ∷
   rw⁻ 3 q20 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   rw 2 q20 ∷
   rw 3 q23 ∷
   rw 4 q24 ∷
   rw 3 q19 ∷
   rw⁻ 2 q20 ∷
   rw 1 q21 ∷
   rw 2 q22 ∷
   rw 1 q20 ∷
   rw 2 q23 ∷
   rw 3 q24 ∷
   rw 2 q19 ∷
   rw⁻ 1 q20 ∷
   rw 0 q21 ∷
   rw 1 q22 ∷
   rw 0 q20 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 658 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CKd21 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CKd21-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (X2 ∷ CK21⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 659 W

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX21 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CS01 CK10 CS01 CS01] [X2 CSd02 CKd20 CS02 CS02 X2]: 1 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-CKd20-CS02-CS02-X2 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX21-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-CSd02-CKd20-CS02-CS02-X2 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ CK20⁻ ∷ CS02 ∷ CS02 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 0 q29 ∷ []) Eq.refl
