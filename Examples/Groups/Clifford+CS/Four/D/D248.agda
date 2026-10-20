{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D248 (W : Ws) where

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
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q4 : Eqn
  q4 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (wn 571 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q14 : Eqn
  q14 = eqn (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) (wn 359 W)
  q15 : Eqn
  q15 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CK32 ∷ []) (CK31 ∷ Sw12 ∷ []) (wn 361 W)
  q17 : Eqn
  q17 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q18 : Eqn
  q18 = eqn (CK10 ∷ CK32 ∷ []) (CK32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₁₀))
  q19 : Eqn
  q19 = eqn (CX32 ∷ CK31 ∷ []) (CK31 ∷ CX32 ∷ []) (wn 755 W)
  q20 : Eqn
  q20 = eqn (S2 ∷ CK31 ∷ []) (CK31 ∷ S2 ∷ []) (wn 495 W)
  q21 : Eqn
  q21 = eqn (CS02 ∷ CK21 ∷ []) (CK21 ∷ CS02 ∷ []) (wn 516 W)
  q22 : Eqn
  q22 = eqn (CK20 ∷ CK21 ∷ []) (CK21 ∷ CK20 ∷ []) (wn 515 W)
  q23 : Eqn
  q23 = eqn (CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ []) (CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ []) (wn 570 W)

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [CK31]: 753 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-CK31 : ⟪ (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-CK31 = derive (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CK31 ∷ []) (CK31 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 31 q1 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q2 ∷
   rw 31 q3 ∷
   rw⁻ 30 q2 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q2 ∷
   rw 29 q4 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q2 ∷
   rw 27 q3 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q2 ∷
   rw 26 q3 ∷
   rw⁻ 25 q2 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw⁻ 24 q5 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q2 ∷
   rw 24 q3 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q2 ∷
   rw 23 q3 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q2 ∷
   rw 21 q3 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q2 ∷
   rw 20 q3 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw 19 q3 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q2 ∷
   rw 18 q3 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 17 q3 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q2 ∷
   rw 16 q3 ∷
   rw⁻ 15 q2 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw⁻ 14 q6 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 14 q4 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (CK31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 13 q3 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 12 q3 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 11 q3 ∷
   rw⁻ 10 q2 ∷
   re 11 3 (CS13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw 10 q3 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 9 q3 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q7 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q8 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q8 ∷
   rw 3 q2 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q8 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q9 ∷
   rw 5 q2 ∷
   re 3 3 (CK30 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q8 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q8 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q8 ∷
   rw 8 q8 ∷
   rw 9 q8 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q9 ∷
   rw 14 q11 ∷
   rw 15 q8 ∷
   rw 16 q8 ∷
   rw 17 q8 ∷
   rw 18 q8 ∷
   rw 19 q8 ∷
   rw 20 q8 ∷
   rw 21 q8 ∷
   rw 22 q8 ∷
   rw 23 q8 ∷
   rw 24 q10 ∷
   rw 25 q8 ∷
   rw 26 q8 ∷
   rw 27 q8 ∷
   rw 28 q9 ∷
   rw 29 q8 ∷
   rw 30 q8 ∷
   rw 31 q12 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q13 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q13 ∷
   re 35 3 (CK31 ∷ []) ∷
   rw 34 q14 ∷
   rw 33 q15 ∷
   rw 32 q16 ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q17 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q17 ∷
   re 30 3 (CK31 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q13 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q13 ∷
   re 34 3 (CK31 ∷ []) ∷
   rw 33 q14 ∷
   rw 32 q15 ∷
   rw 31 q16 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q17 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q17 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q13 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q13 ∷
   re 33 3 (CK31 ∷ []) ∷
   rw 32 q14 ∷
   rw 31 q18 ∷
   rw 30 q16 ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q17 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q17 ∷
   re 28 3 (CK31 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q13 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q13 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw 31 q14 ∷
   rw 30 q15 ∷
   rw 29 q16 ∷
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q17 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q17 ∷
   re 27 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q13 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q13 ∷
   re 31 3 (CK31 ∷ []) ∷
   rw 30 q14 ∷
   rw 29 q15 ∷
   rw 28 q16 ∷
   re 28 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 27 q17 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q17 ∷
   re 26 3 (CK31 ∷ []) ∷
   re 26 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 25 q13 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q13 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 29 q14 ∷
   rw 28 q15 ∷
   rw 27 q16 ∷
   re 27 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 26 q17 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q17 ∷
   re 25 3 (CK31 ∷ []) ∷
   rw 24 q19 ∷
   re 24 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 23 q13 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q13 ∷
   re 28 3 (CK31 ∷ []) ∷
   rw 27 q14 ∷
   rw 26 q15 ∷
   rw 25 q16 ∷
   re 25 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 24 q17 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q17 ∷
   re 23 3 (CK31 ∷ []) ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 22 q13 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q13 ∷
   re 27 3 (CK31 ∷ []) ∷
   rw 26 q14 ∷
   rw 25 q15 ∷
   rw 24 q16 ∷
   re 24 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 23 q17 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q17 ∷
   re 22 3 (CK31 ∷ []) ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 q13 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q13 ∷
   re 26 3 (CK31 ∷ []) ∷
   rw 25 q14 ∷
   rw 24 q15 ∷
   rw 23 q16 ∷
   re 23 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 22 q17 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q17 ∷
   re 21 3 (CK31 ∷ []) ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q13 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q13 ∷
   re 25 3 (CK31 ∷ []) ∷
   rw 24 q14 ∷
   rw 23 q15 ∷
   rw 22 q16 ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 q17 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q17 ∷
   re 20 3 (CK31 ∷ []) ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q13 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q13 ∷
   re 24 3 (CK31 ∷ []) ∷
   rw 23 q14 ∷
   rw 22 q15 ∷
   rw 21 q16 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 20 q17 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q17 ∷
   re 19 3 (CK31 ∷ []) ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 18 q13 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q13 ∷
   re 23 3 (CK31 ∷ []) ∷
   rw 22 q14 ∷
   rw 21 q15 ∷
   rw 20 q16 ∷
   re 20 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 19 q17 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q17 ∷
   re 18 3 (CK31 ∷ []) ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q13 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q13 ∷
   re 22 3 (CK31 ∷ []) ∷
   rw 21 q14 ∷
   rw 20 q15 ∷
   rw 19 q16 ∷
   re 19 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 18 q17 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q17 ∷
   re 17 3 (CK31 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q13 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q13 ∷
   re 21 3 (CK31 ∷ []) ∷
   rw 20 q14 ∷
   rw 19 q15 ∷
   rw 18 q16 ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q17 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q17 ∷
   re 16 3 (CK31 ∷ []) ∷
   re 16 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 15 q13 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q13 ∷
   re 20 3 (CK31 ∷ []) ∷
   rw 19 q14 ∷
   rw 18 q15 ∷
   rw 17 q16 ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q17 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q17 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 14 q20 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q13 ∷
   re 14 3 (CK30 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q13 ∷
   re 18 3 (CK31 ∷ []) ∷
   rw 17 q14 ∷
   rw 16 q18 ∷
   rw 15 q16 ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q17 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q17 ∷
   re 13 3 (CK31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q13 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q13 ∷
   re 17 3 (CK31 ∷ []) ∷
   rw 16 q14 ∷
   rw 15 q15 ∷
   rw 14 q16 ∷
   re 14 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 13 q17 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q17 ∷
   re 12 3 (CK31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q13 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q13 ∷
   re 16 3 (CK31 ∷ []) ∷
   rw 15 q14 ∷
   rw 14 q15 ∷
   rw 13 q16 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q17 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q17 ∷
   re 11 3 (CK31 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q13 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q13 ∷
   re 15 3 (CK31 ∷ []) ∷
   rw 14 q14 ∷
   rw 13 q15 ∷
   rw 12 q16 ∷
   re 12 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 11 q17 ∷
   re 12 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q17 ∷
   re 10 3 (CK31 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q13 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q13 ∷
   re 14 3 (CK31 ∷ []) ∷
   rw 13 q14 ∷
   rw 12 q15 ∷
   rw 11 q16 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q17 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q17 ∷
   re 9 3 (CK31 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q13 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q13 ∷
   re 13 3 (CK31 ∷ []) ∷
   rw 12 q14 ∷
   rw 11 q15 ∷
   rw 10 q16 ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q17 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q17 ∷
   re 8 3 (CK31 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q13 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q13 ∷
   re 12 3 (CK31 ∷ []) ∷
   rw 11 q14 ∷
   rw 10 q15 ∷
   rw 9 q16 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q17 ∷
   re 7 3 (CK31 ∷ []) ∷
   rw 6 q19 ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 6 q21 ∷
   rw 7 q13 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 8 q13 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q17 ∷
   rw 6 q13 ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 5 q21 ∷
   rw 6 q13 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 7 q13 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q17 ∷
   rw 5 q13 ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 4 q22 ∷
   rw 5 q13 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 6 q13 ∷
   re 4 3 (CK30 ∷ []) ∷
   rw 5 q17 ∷
   rw 4 q13 ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q21 ∷
   rw 4 q13 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw 5 q13 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q13 ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   rw 2 q21 ∷
   rw 3 q13 ∷
   re 1 3 (CK31 ∷ []) ∷
   rw 4 q13 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q17 ∷
   rw 2 q13 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q21 ∷
   rw 2 q13 ∷
   re 0 3 (CK31 ∷ []) ∷
   rw 3 q13 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q17 ∷
   rw 32 q1 ∷
   rw 31 q3 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q3 ∷
   rw 27 q3 ∷
   rw 26 q3 ∷
   rw⁻ 25 q10 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw 22 q3 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw⁻ 15 q11 ∷
   rw 14 q4 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q3 ∷
   rw 9 q3 ∷
   rw 8 q3 ∷
   rw⁻ 7 q10 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 7 q3 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q2 ∷
   rw 6 q3 ∷
   rw⁻ 5 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw 5 q4 ∷
   rw⁻ 4 q2 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 4 q3 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q2 ∷
   rw 3 q3 ∷
   rw⁻ 2 q2 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 2 q3 ∷
   rw⁻ 1 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q23 ∷
   rw 1 q8 ∷
   rw 2 q8 ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q8 ∷
   rw 6 q8 ∷
   rw 7 q5 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q8 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 11 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q8 ∷
   rw 12 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 12 q8 ∷
   rw 13 q2 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 13 q8 ∷
   rw 14 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 14 q8 ∷
   rw 15 q2 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q9 ∷
   rw 16 q2 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q6 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw 17 q8 ∷
   rw 18 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw 18 q8 ∷
   rw 19 q2 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   rw 19 q8 ∷
   rw 20 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw 20 q8 ∷
   rw 21 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   rw 21 q8 ∷
   rw 22 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   rw 22 q8 ∷
   rw 23 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   rw 23 q8 ∷
   rw 24 q2 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw 24 q8 ∷
   rw 25 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   rw 25 q8 ∷
   rw 26 q2 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q5 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   rw 27 q8 ∷
   rw 28 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   rw 28 q8 ∷
   rw 29 q2 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   rw 29 q8 ∷
   rw 30 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   rw 30 q9 ∷
   rw 31 q2 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   rw 31 q8 ∷
   rw 32 q2 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   rw 32 q8 ∷
   rw 33 q2 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 32 q12 ∷ []) Eq.refl
