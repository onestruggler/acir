{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D372 (W : Ws) where

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
  q3 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q4 : Eqn
  q4 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (wn 517 W)
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
  q13 = eqn (CK20 ∷ X3 ∷ []) (X3 ∷ CK20 ∷ []) (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q14 : Eqn
  q14 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q16 : Eqn
  q16 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))
  q17 : Eqn
  q17 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q18 : Eqn
  q18 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q19 : Eqn
  q19 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q20 : Eqn
  q20 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q21 : Eqn
  q21 = eqn (CX32 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CX32 ∷ []) (wn 510 W)
  q22 : Eqn
  q22 = eqn (S2 ∷ X3 ∷ []) (X3 ∷ S2 ∷ []) (low₃-comm ((S ↑ ↑)) (X))
  q23 : Eqn
  q23 = eqn (S2 ∷ CS13 ∷ []) (CS13 ∷ S2 ∷ []) (wn 210 W)
  q24 : Eqn
  q24 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q25 : Eqn
  q25 = eqn (CK20 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CK20 ∷ []) (wn 511 W)
  q26 : Eqn
  q26 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q27 : Eqn
  q27 = eqn (CS02 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ CS02 ∷ []) (wn 512 W)
  q28 : Eqn
  q28 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ []) (CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ CX23 ∷ CK31 ∷ S3 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX23 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ []) (wn 513 W)

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X3 CS13 X3]: 721 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 29 q1 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (CK31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (CK31 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q2 ∷
   rw 27 q4 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q2 ∷
   rw 26 q3 ∷
   rw⁻ 25 q2 ∷
   re 26 3 (CK31 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q2 ∷
   rw 25 q4 ∷
   rw⁻ 24 q2 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q2 ∷
   rw 24 q4 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw⁻ 22 q5 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw 22 q4 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q2 ∷
   rw 21 q4 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q2 ∷
   rw 20 q4 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw 19 q4 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q2 ∷
   rw 18 q4 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 17 q4 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q6 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw 15 q3 ∷
   rw⁻ 14 q2 ∷
   re 15 3 (CK31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q2 ∷
   rw 14 q4 ∷
   rw⁻ 13 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 13 q4 ∷
   rw⁻ 12 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q2 ∷
   rw 12 q4 ∷
   rw⁻ 11 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 10 q6 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw 10 q3 ∷
   rw⁻ 9 q2 ∷
   re 10 3 (CK31 ∷ []) ∷
   rw⁻ 8 q6 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 0 q4 ∷
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
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q9 ∷
   rw 4 q2 ∷
   re 2 3 (CK30 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q8 ∷
   rw 5 q2 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q9 ∷
   rw 6 q2 ∷
   re 4 3 (CK30 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q9 ∷
   rw 7 q2 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   rw 8 q11 ∷
   rw 9 q9 ∷
   rw 10 q11 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q9 ∷
   rw 15 q11 ∷
   rw 16 q8 ∷
   rw 17 q8 ∷
   rw 18 q8 ∷
   rw 19 q8 ∷
   rw 20 q8 ∷
   rw 21 q8 ∷
   rw 22 q10 ∷
   rw 23 q8 ∷
   rw 24 q8 ∷
   rw 25 q9 ∷
   rw 26 q8 ∷
   rw 27 q9 ∷
   rw 28 q9 ∷
   rw 29 q12 ∷
   rw 28 q13 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q14 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q14 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 33 q15 ∷
   rw 32 q16 ∷
   rw 31 q17 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 31 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 33 q18 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 30 q13 ∷
   rw 27 q13 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q14 ∷
   re 29 3 (CK30 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q14 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q15 ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 32 q18 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 29 q13 ∷
   rw 26 q19 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q14 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q14 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 31 q15 ∷
   rw 30 q20 ∷
   rw 29 q17 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q18 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 28 q19 ∷
   rw 25 q13 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q14 ∷
   re 27 3 (CK30 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q14 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q15 ∷
   rw 29 q16 ∷
   rw 28 q17 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 28 5 (CK30 ∷ []) ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 27 q13 ∷
   rw 24 q19 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q14 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q14 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 29 q15 ∷
   rw 28 q20 ∷
   rw 27 q17 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 26 q19 ∷
   rw 23 q19 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q14 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q14 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 28 q15 ∷
   rw 27 q20 ∷
   rw 26 q17 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 25 q19 ∷
   rw 22 q21 ∷
   rw 21 q19 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q14 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q14 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 26 q15 ∷
   rw 25 q20 ∷
   rw 24 q17 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 23 q19 ∷
   rw 20 q19 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q14 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q14 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q15 ∷
   rw 24 q20 ∷
   rw 23 q17 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 22 q19 ∷
   rw 19 q19 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q14 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q14 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 24 q15 ∷
   rw 23 q20 ∷
   rw 22 q17 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 21 q19 ∷
   rw 18 q19 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q14 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q14 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 23 q15 ∷
   rw 22 q20 ∷
   rw 21 q17 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 20 q19 ∷
   rw 17 q19 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q14 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q14 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 22 q15 ∷
   rw 21 q20 ∷
   rw 20 q17 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 19 q19 ∷
   rw 16 q19 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q14 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q14 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 21 q15 ∷
   rw 20 q20 ∷
   rw 19 q17 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 18 q19 ∷
   rw 15 q22 ∷
   rw 16 q23 ∷
   rw 17 q22 ∷
   rw 14 q13 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q14 ∷
   re 16 3 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q14 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 19 q15 ∷
   rw 18 q16 ∷
   rw 17 q17 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 17 5 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 16 q13 ∷
   rw 13 q19 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q14 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q14 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw 18 q15 ∷
   rw 17 q20 ∷
   rw 16 q17 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 15 q19 ∷
   rw 12 q19 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q14 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q14 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 17 q15 ∷
   rw 16 q20 ∷
   rw 15 q17 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q18 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 14 q19 ∷
   rw 11 q19 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q14 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q14 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 16 q15 ∷
   rw 15 q20 ∷
   rw 14 q17 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 13 q19 ∷
   rw 10 q22 ∷
   rw 11 q23 ∷
   rw 12 q22 ∷
   rw 9 q13 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q14 ∷
   re 11 3 (CK30 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q14 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 14 q15 ∷
   rw 13 q16 ∷
   rw 12 q17 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q18 ∷
   re 12 5 (CK30 ∷ []) ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q13 ∷
   rw 8 q22 ∷
   rw 9 q23 ∷
   rw 10 q22 ∷
   rw 7 q13 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   re 9 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q14 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 12 q15 ∷
   rw 11 q16 ∷
   rw 10 q17 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   re 10 5 (CK30 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 12 q18 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q13 ∷
   rw 6 q21 ∷
   rw 9 q14 ∷
   rw 8 q24 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   rw 6 q24 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 6 q25 ∷
   rw 5 q26 ∷
   rw 8 q14 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q26 ∷
   rw 10 q14 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q18 ∷
   rw 8 q14 ∷
   rw 7 q24 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q24 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 5 q25 ∷
   rw 4 q26 ∷
   rw 7 q14 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q26 ∷
   rw 9 q14 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q18 ∷
   rw 7 q14 ∷
   rw 6 q24 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 4 q24 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw 4 q27 ∷
   rw 3 q26 ∷
   rw 6 q14 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q26 ∷
   rw 8 q14 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q18 ∷
   rw 6 q14 ∷
   rw 5 q24 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 3 q24 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q25 ∷
   rw 2 q26 ∷
   rw 5 q14 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 4 q26 ∷
   rw 7 q14 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q18 ∷
   rw 5 q14 ∷
   rw 4 q24 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw 2 q24 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   rw 2 q27 ∷
   rw 1 q26 ∷
   rw 4 q14 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q26 ∷
   rw 6 q14 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q18 ∷
   rw 4 q14 ∷
   rw 3 q24 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   rw 1 q24 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q18 ∷
   rw 1 q27 ∷
   rw 0 q26 ∷
   rw 3 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q26 ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q18 ∷
   rw 32 q1 ∷
   rw 31 q3 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw⁻ 25 q10 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw⁻ 18 q11 ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw 14 q4 ∷
   rw⁻ 13 q11 ∷
   rw 12 q3 ∷
   rw⁻ 11 q11 ∷
   rw 10 q3 ∷
   rw⁻ 9 q10 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 9 q3 ∷
   rw⁻ 8 q2 ∷
   re 9 3 (CK31 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (CK31 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 7 q4 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q2 ∷
   rw 6 q3 ∷
   rw⁻ 5 q2 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw 5 q4 ∷
   rw⁻ 4 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 4 q4 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q28 ∷
   rw 3 q8 ∷
   rw 4 q8 ∷
   rw 5 q9 ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 9 q5 ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q9 ∷
   rw 12 q2 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q6 ∷
   re 13 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 13 q9 ∷
   rw 14 q2 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q6 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q8 ∷
   rw 16 q2 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   rw 16 q8 ∷
   rw 17 q2 ∷
   re 15 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw 17 q8 ∷
   rw 18 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw 18 q9 ∷
   rw 19 q2 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q6 ∷
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
   re 29 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   rw 29 q9 ∷
   rw 30 q2 ∷
   re 28 3 (CK30 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   rw 30 q8 ∷
   rw 31 q2 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   rw 31 q9 ∷
   rw 32 q2 ∷
   re 30 3 (CK30 ∷ []) ∷
   re 32 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   rw 32 q9 ∷
   rw 33 q2 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q12 ∷ []) Eq.refl
