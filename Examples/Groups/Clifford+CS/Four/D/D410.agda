{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D410 (W : Ws) where

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
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q3 : Eqn
  q3 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 513 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q14 : Eqn
  q14 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q17 : Eqn
  q17 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q18 : Eqn
  q18 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q19 : Eqn
  q19 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q20 : Eqn
  q20 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q21 : Eqn
  q21 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q22 : Eqn
  q22 = eqn (CX23 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CX23 ∷ []) (wn 754 W)

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 CS12 X2] part0: 500 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part0 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-CS12-X2-part0 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ CS12 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ X2 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 29 q1 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw⁻ 22 q4 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw⁻ 15 q5 ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw⁻ 10 q5 ∷
   rw 9 q2 ∷
   rw⁻ 8 q5 ∷
   rw 7 q2 ∷
   rw⁻ 6 q4 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw 6 q2 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q2 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 4 q3 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 3 q2 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (CK31 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q3 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 1 q3 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 1 q8 ∷
   rw 2 q9 ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q9 ∷
   rw 9 q6 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q11 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   rw 11 q6 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q11 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 12 q8 ∷
   rw 13 q6 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 13 q8 ∷
   rw 14 q6 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 14 q8 ∷
   rw 15 q6 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw 15 q9 ∷
   rw 16 q6 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q11 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   rw 17 q8 ∷
   rw 18 q6 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   rw 18 q8 ∷
   rw 19 q6 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   rw 19 q8 ∷
   rw 20 q6 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   rw 20 q8 ∷
   rw 21 q6 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   rw 21 q8 ∷
   rw 22 q6 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   rw 22 q8 ∷
   rw 23 q6 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q10 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   rw 24 q8 ∷
   rw 25 q6 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   rw 25 q8 ∷
   rw 26 q6 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   rw 26 q9 ∷
   rw 27 q6 ∷
   re 25 3 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw 27 q8 ∷
   rw 28 q6 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   rw 28 q9 ∷
   rw 29 q6 ∷
   re 27 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   rw 29 q9 ∷
   rw 30 q6 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q12 ∷
   rw 30 q1 ∷
   rw⁻ 29 q13 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q6 ∷
   rw 29 q2 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (CK31 ∷ []) ∷
   rw 29 q14 ∷
   rw 28 q13 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   rw 30 q9 ∷
   rw 31 q6 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q12 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q15 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q16 ∷
   rw 31 q17 ∷
   rw 30 q18 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 30 5 (CK30 ∷ []) ∷
   rw 32 q1 ∷
   rw⁻ 31 q13 ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q6 ∷
   rw 31 q2 ∷
   rw⁻ 30 q6 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 31 q14 ∷
   rw 30 q13 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   rw 32 q9 ∷
   rw 33 q6 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q12 ∷
   rw 29 q1 ∷
   rw⁻ 28 q13 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q6 ∷
   rw 28 q2 ∷
   rw⁻ 27 q6 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 28 q14 ∷
   rw 27 q13 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   rw 29 q9 ∷
   rw 30 q6 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q12 ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q15 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   rw 29 q18 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 29 5 (CK30 ∷ []) ∷
   rw 31 q1 ∷
   rw⁻ 30 q13 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q6 ∷
   rw 30 q2 ∷
   rw⁻ 29 q6 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 30 q14 ∷
   rw 29 q13 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   rw 31 q9 ∷
   rw 32 q6 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 31 q12 ∷
   rw 28 q1 ∷
   rw⁻ 27 q13 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q6 ∷
   rw 27 q3 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q20 ∷
   rw 26 q13 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   rw 28 q8 ∷
   rw 29 q6 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q12 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q16 ∷
   rw 29 q21 ∷
   rw 28 q18 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   rw⁻ 29 q13 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q6 ∷
   rw 29 q3 ∷
   rw⁻ 28 q6 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 29 q20 ∷
   rw 28 q13 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   rw 30 q8 ∷
   rw 31 q6 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 30 q12 ∷
   rw 27 q1 ∷
   rw⁻ 26 q13 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q6 ∷
   rw 26 q2 ∷
   rw⁻ 25 q6 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 26 q14 ∷
   rw 25 q13 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw 27 q9 ∷
   rw 28 q6 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 27 q12 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 29 q16 ∷
   rw 28 q17 ∷
   rw 27 q18 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 27 5 (CK30 ∷ []) ∷
   rw 29 q1 ∷
   rw⁻ 28 q13 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q6 ∷
   rw 28 q2 ∷
   rw⁻ 27 q6 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 28 q14 ∷
   rw 27 q13 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   rw 29 q9 ∷
   rw 30 q6 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 29 q12 ∷
   rw 26 q1 ∷
   rw⁻ 25 q13 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q6 ∷
   rw 25 q3 ∷
   rw⁻ 24 q6 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 25 q20 ∷
   rw 24 q13 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   rw 26 q8 ∷
   rw 27 q6 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 26 q12 ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q15 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 28 q16 ∷
   rw 27 q21 ∷
   rw 26 q18 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 26 5 (CS03 ∷ []) ∷
   rw 28 q1 ∷
   rw⁻ 27 q13 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q6 ∷
   rw 27 q3 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 27 q20 ∷
   rw 26 q13 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   rw 28 q8 ∷
   rw 29 q6 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 28 q12 ∷
   rw 25 q1 ∷
   rw⁻ 24 q13 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q6 ∷
   rw 24 q3 ∷
   rw⁻ 23 q6 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q20 ∷
   rw 23 q13 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   rw 25 q8 ∷
   rw 26 q6 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q12 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 27 q16 ∷
   rw 26 q21 ∷
   rw 25 q18 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 25 5 (CS03 ∷ []) ∷
   rw 27 q1 ∷
   rw⁻ 26 q13 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q6 ∷
   rw 26 q3 ∷
   rw⁻ 25 q6 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 26 q20 ∷
   rw 25 q13 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   rw 27 q8 ∷
   rw 28 q6 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 27 q12 ∷
   rw 22 q22 ∷
   rw 23 q1 ∷
   rw⁻ 22 q13 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q6 ∷
   rw 22 q3 ∷
   rw⁻ 21 q6 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 22 q20 ∷
   rw 21 q13 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   rw 23 q8 ∷
   rw 24 q6 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 23 q12 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q15 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q16 ∷
   rw 24 q21 ∷
   rw 23 q18 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q19 ∷
   re 23 5 (CS03 ∷ []) ∷
   rw 25 q1 ∷
   rw⁻ 24 q13 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q6 ∷
   rw 24 q3 ∷
   rw⁻ 23 q6 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 24 q20 ∷
   rw 23 q13 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   rw 25 q8 ∷
   rw 26 q6 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q12 ∷
   rw 22 q1 ∷
   rw⁻ 21 q13 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q6 ∷
   rw 21 q3 ∷
   rw⁻ 20 q6 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 21 q20 ∷
   rw 20 q13 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   rw 22 q8 ∷
   rw 23 q6 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 22 q12 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q16 ∷
   rw 23 q21 ∷
   rw 22 q18 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q19 ∷
   re 22 5 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   rw⁻ 23 q13 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q6 ∷
   rw 23 q3 ∷
   rw⁻ 22 q6 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 23 q20 ∷
   rw 22 q13 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   rw 24 q8 ∷
   rw 25 q6 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q12 ∷
   rw 21 q1 ∷
   rw⁻ 20 q13 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q6 ∷
   rw 20 q3 ∷
   rw⁻ 19 q6 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 20 q20 ∷
   rw 19 q13 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   rw 21 q8 ∷
   rw 22 q6 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q12 ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 23 q16 ∷
   rw 22 q21 ∷
   rw 21 q18 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q19 ∷
   re 21 5 (CS03 ∷ []) ∷
   rw 23 q1 ∷
   rw⁻ 22 q13 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q6 ∷
   rw 22 q3 ∷
   rw⁻ 21 q6 ∷ []) Eq.refl
