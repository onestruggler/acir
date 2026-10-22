{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D255 (W : Ws) where

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
  q2 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 836 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [CS23]: 115 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS23 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS23 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS23 ∷ []) (CS23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q3 ∷
   rw 26 q3 ∷
   rw 25 q3 ∷
   rw⁻ 24 q5 ∷
   rw 23 q3 ∷
   rw 22 q3 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw 15 q3 ∷
   rw⁻ 14 q6 ∷
   rw 13 q4 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q3 ∷
   rw 9 q3 ∷
   rw 8 q3 ∷
   rw 7 q3 ∷
   rw⁻ 6 q5 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q3 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q3 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q4 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CK31 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q7 ∷
   rw 3 q3 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q7 ∷
   rw 2 q3 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q7 ∷
   rw 1 q3 ∷
   rw⁻ 0 q7 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q9 ∷
   rw 3 q7 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw 3 q9 ∷
   rw 4 q7 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q9 ∷
   rw 5 q7 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q10 ∷
   rw 6 q7 ∷
   re 4 3 (CK30 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q9 ∷
   rw 7 q7 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q9 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q9 ∷
   rw 9 q9 ∷
   rw 10 q9 ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q10 ∷
   rw 15 q6 ∷
   rw 16 q9 ∷
   rw 17 q9 ∷
   rw 18 q9 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q5 ∷
   rw 26 q9 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q10 ∷
   rw 30 q9 ∷
   rw 31 q9 ∷
   rw 32 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = wE 20 W
  q14 : Eqn
  q14 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q15 : Eqn
  q15 = wE 49 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q18 : Eqn
  q18 = wE 749 W
  q19 : Eqn
  q19 = wE 210 W
  q20 : Eqn
  q20 = wE 524 W
  q21 : Eqn
  q21 = wE 523 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [CS13]: 399 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS13 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS13 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS13 ∷ []) (CS13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ [])
  (re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q12 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 34 q13 ∷
   rw 33 q14 ∷
   rw 32 q15 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q16 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q16 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 33 q13 ∷
   rw 32 q14 ∷
   rw 31 q15 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q16 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q16 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q12 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q13 ∷
   rw 31 q17 ∷
   rw 30 q15 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q16 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q16 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q12 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 31 q13 ∷
   rw 30 q14 ∷
   rw 29 q15 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q16 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q16 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q12 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q13 ∷
   rw 29 q14 ∷
   rw 28 q15 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q16 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q16 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q12 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 29 q13 ∷
   rw 28 q14 ∷
   rw 27 q15 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q16 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q16 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q18 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q12 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 27 q13 ∷
   rw 26 q14 ∷
   rw 25 q15 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q16 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q16 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q12 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q12 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 26 q13 ∷
   rw 25 q14 ∷
   rw 24 q15 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q16 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q16 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q12 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q12 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q13 ∷
   rw 24 q14 ∷
   rw 23 q15 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q16 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q16 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q12 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q13 ∷
   rw 23 q14 ∷
   rw 22 q15 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q16 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q16 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q12 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q12 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 23 q13 ∷
   rw 22 q14 ∷
   rw 21 q15 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q16 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q16 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q12 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 22 q13 ∷
   rw 21 q14 ∷
   rw 20 q15 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q16 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q16 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q12 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 21 q13 ∷
   rw 20 q14 ∷
   rw 19 q15 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q16 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q16 ∷
   re 17 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q12 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q12 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 20 q13 ∷
   rw 19 q14 ∷
   rw 18 q15 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q16 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q16 ∷
   re 16 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q12 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q12 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 19 q13 ∷
   rw 18 q14 ∷
   rw 17 q15 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q16 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q16 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 14 q19 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   re 14 3 (CK30 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q12 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 17 q13 ∷
   rw 16 q17 ∷
   rw 15 q15 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q16 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q16 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q12 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 16 q13 ∷
   rw 15 q14 ∷
   rw 14 q15 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q16 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 15 q13 ∷
   rw 14 q14 ∷
   rw 13 q15 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q16 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q16 ∷
   re 11 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 14 q13 ∷
   rw 13 q14 ∷
   rw 12 q15 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q16 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q16 ∷
   re 10 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q12 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 13 q13 ∷
   rw 12 q14 ∷
   rw 11 q15 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q16 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   re 9 3 (CS13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q12 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 12 q13 ∷
   rw 11 q14 ∷
   rw 10 q15 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q16 ∷
   re 8 3 (CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 11 q13 ∷
   rw 10 q14 ∷
   rw 9 q15 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q16 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q16 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 6 q18 ∷
   rw 7 q12 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q16 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q16 ∷
   rw 6 q20 ∷
   rw 7 q12 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q16 ∷
   rw 6 q12 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q16 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q20 ∷
   rw 6 q12 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q12 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q16 ∷
   rw 4 q21 ∷
   rw 5 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 6 q12 ∷
   re 4 3 (CK30 ∷ []) ∷
   rw 5 q16 ∷
   rw 4 q12 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q16 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q20 ∷
   rw 4 q12 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 5 q12 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q12 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q16 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 2 q20 ∷
   rw 3 q12 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 4 q12 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q16 ∷
   rw 2 q12 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q20 ∷
   rw 2 q12 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw 3 q12 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q16 ∷ []) Eq.refl
