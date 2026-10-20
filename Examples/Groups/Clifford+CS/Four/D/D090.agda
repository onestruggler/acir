{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D090 (W : Ws) where

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
  q1 = eqn (CK10 ∷ CK32 ∷ []) (CK32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CK₁₀))
  q2 : Eqn
  q2 = eqn (Sw12 ∷ CK32 ∷ []) (CK31 ∷ Sw12 ∷ []) (wn 361 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q8 : Eqn
  q8 = eqn (CK31 ∷ X2 ∷ []) (X2 ∷ CK31 ∷ []) (wn 630 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q11 : Eqn
  q11 = eqn (X2 ∷ S3 ∷ []) (S3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (S))
  q12 : Eqn
  q12 = eqn (CK21 ∷ S3 ∷ []) (S3 ∷ CK21 ∷ []) (low₃-comm ((CK₁₀ ↑)) (S))
  q13 : Eqn
  q13 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q14 : Eqn
  q14 = eqn (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) (wn 359 W)
  q15 : Eqn
  q15 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q16 : Eqn
  q16 = eqn (CS13 ∷ X2 ∷ []) (X2 ∷ CS13 ∷ []) (wn 629 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q18 : Eqn
  q18 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [X2 CK21 X2] part1: 500 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CK21-X2-part1 : ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CK31 ∷ Sw23 ∷ X2 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-X2-CK21-X2-part1 = derive (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ CK32 ∷ Sw12 ∷ Sw23 ∷ X2 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X2 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ CK31 ∷ Sw23 ∷ X2 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 59 q1 ∷
   rw 58 q2 ∷
   re 58 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   re 58 5 (CK30 ∷ []) ∷
   rw 60 q4 ∷
   rw⁻ 59 q5 ∷
   re 58 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q6 ∷
   rw 59 q7 ∷
   rw⁻ 58 q6 ∷
   re 59 3 (CK31 ∷ []) ∷
   rw 59 q8 ∷
   rw 58 q5 ∷
   re 60 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 59 q6 ∷
   rw 60 q9 ∷
   rw 61 q6 ∷
   re 59 3 (CK30 ∷ []) ∷
   rw 60 q10 ∷
   rw⁻ 55 q11 ∷
   rw⁻ 56 q12 ∷
   rw⁻ 57 q11 ∷
   rw⁻ 54 q11 ∷
   rw⁻ 55 q12 ∷
   rw⁻ 56 q11 ∷
   rw⁻ 53 q11 ∷
   rw⁻ 54 q12 ∷
   rw⁻ 55 q11 ∷
   rw⁻ 52 q11 ∷
   rw⁻ 53 q12 ∷
   rw⁻ 54 q11 ∷
   rw 53 q4 ∷
   rw⁻ 52 q5 ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q6 ∷
   rw 52 q7 ∷
   rw⁻ 51 q6 ∷
   re 52 3 (CK31 ∷ []) ∷
   rw 52 q8 ∷
   rw 51 q5 ∷
   re 53 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 52 q6 ∷
   rw 53 q9 ∷
   rw 54 q6 ∷
   re 52 3 (CK30 ∷ []) ∷
   rw 53 q10 ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q13 ∷
   re 56 3 (CK31 ∷ []) ∷
   rw 55 q14 ∷
   rw 54 q1 ∷
   rw 53 q2 ∷
   re 53 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   re 53 5 (CK30 ∷ []) ∷
   rw 55 q4 ∷
   rw⁻ 54 q5 ∷
   re 53 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 55 q6 ∷
   rw 54 q7 ∷
   rw⁻ 53 q6 ∷
   re 54 3 (CK31 ∷ []) ∷
   rw 54 q8 ∷
   rw 53 q5 ∷
   re 55 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 54 q6 ∷
   rw 55 q9 ∷
   rw 56 q6 ∷
   re 54 3 (CK30 ∷ []) ∷
   rw 55 q10 ∷
   rw⁻ 50 q11 ∷
   rw⁻ 51 q12 ∷
   rw⁻ 52 q11 ∷
   rw⁻ 49 q11 ∷
   rw⁻ 50 q12 ∷
   rw⁻ 51 q11 ∷
   rw⁻ 48 q11 ∷
   rw⁻ 49 q12 ∷
   rw⁻ 50 q11 ∷
   rw 49 q4 ∷
   rw⁻ 48 q5 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q6 ∷
   rw 48 q15 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 48 q16 ∷
   rw 47 q5 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   rw 49 q17 ∷
   rw 50 q6 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q10 ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q13 ∷
   re 52 3 (CK31 ∷ []) ∷
   rw 51 q14 ∷
   rw 50 q18 ∷
   rw 49 q2 ∷
   re 49 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 49 5 (CS03 ∷ []) ∷
   rw 51 q4 ∷
   rw⁻ 50 q5 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q6 ∷
   rw 50 q15 ∷
   rw⁻ 49 q6 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 50 q16 ∷
   rw 49 q5 ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q6 ∷
   rw 51 q17 ∷
   rw 52 q6 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 51 q10 ∷
   rw 48 q4 ∷
   rw⁻ 47 q5 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q6 ∷
   rw 47 q15 ∷
   rw⁻ 46 q6 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q16 ∷
   rw 46 q5 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   rw 48 q17 ∷
   rw 49 q6 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q10 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q13 ∷
   re 51 3 (CK31 ∷ []) ∷
   rw 50 q14 ∷
   rw 49 q18 ∷
   rw 48 q2 ∷
   re 48 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 48 5 (CS03 ∷ []) ∷
   rw 50 q4 ∷
   rw⁻ 49 q5 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q6 ∷
   rw 49 q15 ∷
   rw⁻ 48 q6 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 49 q16 ∷
   rw 48 q5 ∷
   re 50 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 49 q6 ∷
   rw 50 q17 ∷
   rw 51 q6 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 50 q10 ∷
   rw 47 q4 ∷
   rw⁻ 46 q5 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q6 ∷
   rw 46 q15 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 46 q16 ∷
   rw 45 q5 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   rw 47 q17 ∷
   rw 48 q6 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q10 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q13 ∷
   re 50 3 (CK31 ∷ []) ∷
   rw 49 q14 ∷
   rw 48 q18 ∷
   rw 47 q2 ∷
   re 47 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 47 5 (CS03 ∷ []) ∷
   rw 49 q4 ∷
   rw⁻ 48 q5 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q6 ∷
   rw 48 q15 ∷
   rw⁻ 47 q6 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 48 q16 ∷
   rw 47 q5 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q6 ∷
   rw 49 q17 ∷
   rw 50 q6 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q10 ∷
   rw 46 q4 ∷
   rw⁻ 45 q5 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q6 ∷
   rw 45 q15 ∷
   rw⁻ 44 q6 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 45 q16 ∷
   rw 44 q5 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 46 q17 ∷
   rw 47 q6 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q10 ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q13 ∷
   re 49 3 (CK31 ∷ []) ∷
   rw 48 q14 ∷
   rw 47 q18 ∷
   rw 46 q2 ∷
   re 46 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 46 5 (CS03 ∷ []) ∷
   rw 48 q4 ∷
   rw⁻ 47 q5 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q6 ∷
   rw 47 q15 ∷
   rw⁻ 46 q6 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 47 q16 ∷
   rw 46 q5 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q6 ∷
   rw 48 q17 ∷
   rw 49 q6 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 48 q10 ∷
   rw 45 q4 ∷
   rw⁻ 44 q5 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q6 ∷
   rw 44 q15 ∷
   rw⁻ 43 q6 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q16 ∷
   rw 43 q5 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 45 q17 ∷
   rw 46 q6 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q10 ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q13 ∷
   re 48 3 (CK31 ∷ []) ∷
   rw 47 q14 ∷
   rw 46 q18 ∷
   rw 45 q2 ∷
   re 45 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   re 45 5 (CS03 ∷ []) ∷
   rw 47 q4 ∷
   rw⁻ 46 q5 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q6 ∷
   rw 46 q15 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw 46 q16 ∷
   rw 45 q5 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q6 ∷
   rw 47 q17 ∷
   rw 48 q6 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 47 q10 ∷
   rw 44 q4 ∷
   rw⁻ 43 q5 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q6 ∷
   rw 43 q15 ∷
   rw⁻ 42 q6 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q16 ∷
   rw 42 q5 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 44 q17 ∷
   rw 45 q6 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q10 ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q13 ∷
   re 47 3 (CK31 ∷ []) ∷
   rw 46 q14 ∷
   rw 45 q18 ∷
   rw 44 q2 ∷
   re 44 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 44 5 (CS03 ∷ []) ∷
   rw 46 q4 ∷
   rw⁻ 45 q5 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q6 ∷
   rw 45 q15 ∷
   rw⁻ 44 q6 ∷
   re 45 3 (CS13 ∷ []) ∷
   rw 45 q16 ∷
   rw 44 q5 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q6 ∷
   rw 46 q17 ∷
   rw 47 q6 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 46 q10 ∷
   rw 43 q4 ∷
   rw⁻ 42 q5 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q6 ∷
   rw 42 q15 ∷
   rw⁻ 41 q6 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q16 ∷
   rw 41 q5 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   rw 43 q17 ∷
   rw 44 q6 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q10 ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q13 ∷
   re 46 3 (CK31 ∷ []) ∷
   rw 45 q14 ∷
   rw 44 q18 ∷
   rw 43 q2 ∷
   re 43 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 45 q4 ∷
   rw⁻ 44 q5 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q6 ∷
   rw 44 q15 ∷
   rw⁻ 43 q6 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 44 q16 ∷
   rw 43 q5 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q6 ∷
   rw 45 q17 ∷
   rw 46 q6 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q10 ∷
   rw 42 q4 ∷
   rw⁻ 41 q5 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q6 ∷
   rw 41 q15 ∷
   rw⁻ 40 q6 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 41 q16 ∷
   rw 40 q5 ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   rw 42 q17 ∷
   rw 43 q6 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 42 q10 ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q13 ∷
   re 45 3 (CK31 ∷ []) ∷
   rw 44 q14 ∷
   rw 43 q18 ∷
   rw 42 q2 ∷
   re 42 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 42 5 (CS03 ∷ []) ∷
   rw 44 q4 ∷
   rw⁻ 43 q5 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q6 ∷
   rw 43 q15 ∷
   rw⁻ 42 q6 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q16 ∷
   rw 42 q5 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q6 ∷
   rw 44 q17 ∷
   rw 45 q6 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 44 q10 ∷
   rw 41 q4 ∷
   rw⁻ 40 q5 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q6 ∷
   rw 40 q15 ∷
   rw⁻ 39 q6 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 40 q16 ∷
   rw 39 q5 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 41 q17 ∷
   rw 42 q6 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q10 ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q13 ∷
   re 44 3 (CK31 ∷ []) ∷
   rw 43 q14 ∷
   rw 42 q18 ∷
   rw 41 q2 ∷
   re 41 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 41 5 (CS03 ∷ []) ∷
   rw 43 q4 ∷
   rw⁻ 42 q5 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q6 ∷
   rw 42 q15 ∷
   rw⁻ 41 q6 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 42 q16 ∷
   rw 41 q5 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   rw 43 q17 ∷
   rw 44 q6 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 43 q10 ∷
   rw⁻ 38 q11 ∷
   rw⁻ 39 q12 ∷
   rw⁻ 40 q11 ∷
   rw 39 q4 ∷
   rw⁻ 38 q5 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q6 ∷
   rw 38 q7 ∷
   rw⁻ 37 q6 ∷
   re 38 3 (CK31 ∷ []) ∷
   rw 38 q8 ∷
   rw 37 q5 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   rw 39 q9 ∷
   rw 40 q6 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q10 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q13 ∷
   re 42 3 (CK31 ∷ []) ∷
   rw 41 q14 ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 39 5 (CK30 ∷ []) ∷
   rw 41 q4 ∷
   rw⁻ 40 q5 ∷
   re 39 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q6 ∷
   rw 40 q7 ∷
   rw⁻ 39 q6 ∷
   re 40 3 (CK31 ∷ []) ∷
   rw 40 q8 ∷
   rw 39 q5 ∷
   re 41 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   rw 41 q9 ∷
   rw 42 q6 ∷
   re 40 3 (CK30 ∷ []) ∷
   rw 41 q10 ∷
   rw⁻ 36 q11 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 38 q11 ∷
   rw⁻ 35 q11 ∷
   rw⁻ 36 q12 ∷
   rw⁻ 37 q11 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 35 q12 ∷
   rw⁻ 36 q11 ∷
   rw 35 q4 ∷
   rw⁻ 34 q5 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q6 ∷
   rw 34 q15 ∷
   rw⁻ 33 q6 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 34 q16 ∷
   rw 33 q5 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   rw 35 q17 ∷
   rw 36 q6 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q10 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q13 ∷
   re 38 3 (CK31 ∷ []) ∷ []) Eq.refl
