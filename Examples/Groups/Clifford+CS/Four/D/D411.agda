{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D411 (W : Ws) where

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
  q1 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q6 : Eqn
  q6 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q7 : Eqn
  q7 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q8 : Eqn
  q8 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q12 : Eqn
  q12 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q13 : Eqn
  q13 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q14 : Eqn
  q14 = eqn (CS12 ∷ S3 ∷ []) (S3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (S))
  q15 : Eqn
  q15 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q16 : Eqn
  q16 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q18 : Eqn
  q18 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q19 : Eqn
  q19 = eqn (CX23 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CX23 ∷ []) (wn 754 W)
  q20 : Eqn
  q20 = eqn (CK20 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CK20 ∷ []) (wn 511 W)
  q21 : Eqn
  q21 = eqn (CS02 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ []) (wn 512 W)
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q23 : Eqn
  q23 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q24 : Eqn
  q24 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 517 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 CS12 X2] part1: 500 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part1 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part1 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ [])
  (re 22 3 (CS13 ∷ []) ∷
   rw 22 q1 ∷
   rw 21 q2 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   rw 23 q4 ∷
   rw 24 q3 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q5 ∷
   rw 20 q6 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 19 q7 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q1 ∷
   rw 18 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q5 ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q8 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 22 q9 ∷
   rw 21 q10 ∷
   rw 20 q11 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q12 ∷
   re 20 5 (CS03 ∷ []) ∷
   rw 22 q6 ∷
   rw⁻ 21 q2 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q3 ∷
   rw 21 q7 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q1 ∷
   rw 20 q2 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   rw 22 q4 ∷
   rw 23 q3 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q5 ∷
   rw 19 q6 ∷
   rw⁻ 18 q2 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q3 ∷
   rw 18 q7 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 18 q1 ∷
   rw 17 q2 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 19 q4 ∷
   rw 20 q3 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q5 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q8 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 21 q9 ∷
   rw 20 q10 ∷
   rw 19 q11 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q12 ∷
   re 19 5 (CS03 ∷ []) ∷
   rw 21 q6 ∷
   rw⁻ 20 q2 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q3 ∷
   rw 20 q7 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q1 ∷
   rw 19 q2 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 21 q4 ∷
   rw 22 q3 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q5 ∷
   rw 18 q6 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 17 q7 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 17 q1 ∷
   rw 16 q2 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 18 q4 ∷
   rw 19 q3 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q5 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q8 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q11 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q12 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 20 q6 ∷
   rw⁻ 19 q2 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 19 q7 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 19 q1 ∷
   rw 18 q2 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 20 q4 ∷
   rw 21 q3 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q5 ∷
   rw⁻ 15 q13 ∷
   rw⁻ 16 q14 ∷
   rw⁻ 17 q13 ∷
   rw 16 q6 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 15 q15 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 15 q16 ∷
   rw 14 q2 ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 16 q17 ∷
   rw 17 q3 ∷
   re 15 3 (CK30 ∷ []) ∷
   rw 16 q5 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q8 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 18 q9 ∷
   rw 17 q18 ∷
   rw 16 q11 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q12 ∷
   re 16 5 (CK30 ∷ []) ∷
   rw 18 q6 ∷
   rw⁻ 17 q2 ∷
   re 16 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 17 q15 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 17 q16 ∷
   rw 16 q2 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 18 q17 ∷
   rw 19 q3 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q5 ∷
   rw 15 q6 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 14 q7 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q1 ∷
   rw 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 15 q4 ∷
   rw 16 q3 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q5 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q8 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 17 q9 ∷
   rw 16 q10 ∷
   rw 15 q11 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   re 15 5 (CS03 ∷ []) ∷
   rw 17 q6 ∷
   rw⁻ 16 q2 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q3 ∷
   rw 16 q7 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 16 q1 ∷
   rw 15 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q3 ∷
   rw 17 q4 ∷
   rw 18 q3 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q6 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 13 q7 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q1 ∷
   rw 12 q2 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q4 ∷
   rw 15 q3 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q5 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q8 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   rw 14 q11 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   re 14 5 (CS03 ∷ []) ∷
   rw 16 q6 ∷
   rw⁻ 15 q2 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 15 q7 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 15 q1 ∷
   rw 14 q2 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   rw 16 q4 ∷
   rw 17 q3 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 16 q5 ∷
   rw 13 q6 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 12 q7 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 12 q1 ∷
   rw 11 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q3 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q5 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q8 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 15 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   re 13 5 (CS03 ∷ []) ∷
   rw 15 q6 ∷
   rw⁻ 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q3 ∷
   rw 14 q7 ∷
   rw⁻ 13 q3 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 14 q1 ∷
   rw 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   rw 15 q4 ∷
   rw 16 q3 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q5 ∷
   rw⁻ 10 q13 ∷
   rw⁻ 11 q14 ∷
   rw⁻ 12 q13 ∷
   rw 11 q6 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 10 q15 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q16 ∷
   rw 9 q2 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 11 q17 ∷
   rw 12 q3 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q5 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q8 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 13 q9 ∷
   rw 12 q18 ∷
   rw 11 q11 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   re 11 5 (CK30 ∷ []) ∷
   rw 13 q6 ∷
   rw⁻ 12 q2 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw 12 q15 ∷
   rw⁻ 11 q3 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw 12 q16 ∷
   rw 11 q2 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q17 ∷
   rw 14 q3 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q5 ∷
   rw⁻ 8 q13 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q13 ∷
   rw 9 q6 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 8 q15 ∷
   rw⁻ 7 q3 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 8 q16 ∷
   rw 7 q2 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q17 ∷
   rw 10 q3 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q5 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q8 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 11 q9 ∷
   rw 10 q18 ∷
   rw 9 q11 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   re 9 5 (CK30 ∷ []) ∷
   rw 11 q6 ∷
   rw⁻ 10 q2 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw 10 q15 ∷
   rw⁻ 9 q3 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw 10 q16 ∷
   rw 9 q2 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 11 q17 ∷
   rw 12 q3 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q5 ∷
   rw 6 q19 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q21 ∷
   rw 32 q6 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q3 ∷
   rw 32 q15 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (CK31 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q15 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CK31 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q3 ∷
   rw 30 q7 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 29 q15 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q3 ∷
   rw 28 q7 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q3 ∷
   rw 27 q7 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw⁻ 25 q22 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q3 ∷
   rw 25 q7 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q3 ∷
   rw 24 q7 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q3 ∷
   rw 23 q7 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q3 ∷
   rw 22 q7 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q3 ∷
   rw 21 q7 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q3 ∷
   rw 20 q7 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw⁻ 18 q23 ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q3 ∷
   rw 18 q15 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (CK31 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 17 q7 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (CS13 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q3 ∷
   rw 16 q7 ∷
   rw⁻ 15 q3 ∷
   re 16 3 (CS13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 15 q7 ∷
   rw⁻ 14 q3 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 13 q23 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 13 q15 ∷
   rw⁻ 12 q3 ∷
   re 13 3 (CK31 ∷ []) ∷
   rw⁻ 11 q23 ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 11 q15 ∷
   rw⁻ 10 q3 ∷
   re 11 3 (CK31 ∷ []) ∷
   rw⁻ 9 q22 ∷
   rw 8 q15 ∷
   rw 7 q15 ∷
   rw 6 q7 ∷
   rw 5 q15 ∷
   rw 4 q7 ∷
   rw 3 q7 ∷
   rw 4 q24 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q3 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q17 ∷
   rw 7 q3 ∷
   re 5 3 (CK30 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q3 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q26 : Eqn
  q26 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 CS12 X2] part2: 33 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part2 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part2 = derive (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CK21 ∷ Sw23 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ Sw01 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 7 q3 ∷
   rw 8 q17 ∷
   rw 9 q3 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q17 ∷
   rw 10 q3 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q25 ∷
   rw 10 q17 ∷
   rw 11 q26 ∷
   rw 12 q17 ∷
   rw 13 q26 ∷
   rw 14 q4 ∷
   rw 15 q4 ∷
   rw 16 q4 ∷
   rw 17 q17 ∷
   rw 18 q26 ∷
   rw 19 q4 ∷
   rw 20 q4 ∷
   rw 21 q4 ∷
   rw 22 q4 ∷
   rw 23 q4 ∷
   rw 24 q4 ∷
   rw 25 q25 ∷
   rw 26 q4 ∷
   rw 27 q4 ∷
   rw 28 q17 ∷
   rw 29 q4 ∷
   rw 30 q17 ∷
   rw 31 q17 ∷
   rw 32 q5 ∷ []) Eq.refl
