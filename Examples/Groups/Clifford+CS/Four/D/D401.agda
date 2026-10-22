{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D401 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 36 W
  q4 : Eqn
  q4 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q5 : Eqn
  q5 = wE 37 W
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q10 : Eqn
  q10 = wE 140 W
  q11 : Eqn
  q11 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q12 : Eqn
  q12 = wE 966 W
  q13 : Eqn
  q13 = wE 142 W
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 31 W
  q16 : Eqn
  q16 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q17 : Eqn
  q17 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q18 : Eqn
  q18 = wE 464 W
  q19 : Eqn
  q19 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q20 : Eqn
  q20 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = wE 617 W
  q22 : Eqn
  q22 = wE 151 W
  q23 : Eqn
  q23 = wE 157 W
  q24 : Eqn
  q24 = wE 158 W
  q25 : Eqn
  q25 = wE 624 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] part1: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ Sw23 ∷ Sw12 ∷ CX23 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ Sw23 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 44 q1 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 40 q3 ∷
   rw⁻ 41 q4 ∷
   rw 42 q5 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q1 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 41 q3 ∷
   rw⁻ 42 q4 ∷
   rw 43 q5 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 42 q3 ∷
   rw⁻ 43 q4 ∷
   rw 44 q5 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 43 q3 ∷
   rw⁻ 44 q4 ∷
   rw 45 q5 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   re 44 3 (CX13 ∷ []) ∷
   rw 44 q3 ∷
   rw⁻ 45 q4 ∷
   rw 46 q5 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 43 5 (CS03 ∷ []) ∷
   rw 44 q6 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q7 ∷
   rw 44 q8 ∷
   rw⁻ 43 q7 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q7 ∷
   rw 43 q8 ∷
   rw⁻ 42 q7 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q7 ∷
   rw 42 q8 ∷
   rw⁻ 41 q7 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q7 ∷
   rw 41 q8 ∷
   rw⁻ 40 q7 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q7 ∷
   rw 40 q8 ∷
   rw⁻ 39 q7 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q7 ∷
   rw 39 q8 ∷
   rw⁻ 38 q7 ∷
   re 39 3 (CS13 ∷ []) ∷
   rw⁻ 37 q9 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q7 ∷
   rw 37 q10 ∷
   rw⁻ 36 q7 ∷
   re 37 3 (CK31 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q7 ∷
   rw 36 q8 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q7 ∷
   rw 35 q8 ∷
   rw⁻ 34 q7 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q7 ∷
   rw 34 q8 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw⁻ 32 q9 ∷
   re 31 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q7 ∷
   rw 32 q10 ∷
   rw⁻ 31 q7 ∷
   re 32 3 (CK31 ∷ []) ∷
   rw⁻ 30 q9 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q7 ∷
   rw 30 q10 ∷
   rw⁻ 29 q7 ∷
   re 30 3 (CK31 ∷ []) ∷
   rw 28 q8 ∷
   rw 27 q8 ∷
   rw 26 q8 ∷
   rw 25 q8 ∷
   rw 24 q8 ∷
   rw 23 q8 ∷
   rw⁻ 22 q11 ∷
   rw 21 q10 ∷
   rw 20 q8 ∷
   rw 19 q8 ∷
   rw 18 q8 ∷
   rw⁻ 17 q11 ∷
   rw 16 q10 ∷
   rw⁻ 15 q11 ∷
   rw 14 q10 ∷
   rw 15 q12 ∷
   re 15 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 14 q7 ∷
   rw 15 q13 ∷
   rw 16 q7 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q9 ∷
   re 17 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   rw 17 q13 ∷
   rw 18 q7 ∷
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q9 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   rw 19 q14 ∷
   rw 20 q7 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   rw 20 q14 ∷
   rw 21 q7 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q7 ∷
   rw 21 q14 ∷
   rw 22 q7 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 21 q7 ∷
   rw 22 q13 ∷
   rw 23 q7 ∷
   re 21 3 (CK30 ∷ []) ∷
   rw 22 q9 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q7 ∷
   rw 24 q14 ∷
   rw 25 q7 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q7 ∷
   rw 25 q14 ∷
   rw 26 q7 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q7 ∷
   rw 26 q14 ∷
   rw 27 q7 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q7 ∷
   rw 27 q14 ∷
   rw 28 q7 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q7 ∷
   rw 28 q14 ∷
   rw 29 q7 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q7 ∷
   rw 29 q14 ∷
   rw 30 q7 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q13 ∷
   rw 30 q11 ∷
   rw 31 q13 ∷
   rw 32 q11 ∷
   rw 33 q14 ∷
   rw 34 q14 ∷
   rw 35 q14 ∷
   rw 36 q13 ∷
   rw 37 q11 ∷
   rw 38 q14 ∷
   rw 39 q14 ∷
   rw 40 q14 ∷
   rw 41 q14 ∷
   rw 42 q14 ∷
   rw 43 q14 ∷
   rw 44 q15 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 14 3 (CX13 ∷ []) ∷
   rw 14 q3 ∷
   rw⁻ 15 q16 ∷
   rw 16 q5 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 13 5 (CK30 ∷ []) ∷
   rw 14 q17 ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 16 q3 ∷
   rw⁻ 17 q16 ∷
   rw 18 q5 ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 15 5 (CK30 ∷ []) ∷
   rw 16 q17 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CX13 ∷ []) ∷
   rw 18 q3 ∷
   rw⁻ 19 q4 ∷
   rw 20 q5 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CX13 ∷ []) ∷
   rw 19 q3 ∷
   rw⁻ 20 q4 ∷
   rw 21 q5 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CX13 ∷ []) ∷
   rw 20 q3 ∷
   rw⁻ 21 q4 ∷
   rw 22 q5 ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CX13 ∷ []) ∷
   rw 21 q3 ∷
   rw⁻ 22 q16 ∷
   rw 23 q5 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 20 5 (CK30 ∷ []) ∷
   rw 21 q17 ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 23 q3 ∷
   rw⁻ 24 q4 ∷
   rw 25 q5 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 24 3 (CX13 ∷ []) ∷
   rw 24 q3 ∷
   rw⁻ 25 q4 ∷
   rw 26 q5 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 25 q3 ∷
   rw⁻ 26 q4 ∷
   rw 27 q5 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CX13 ∷ []) ∷
   rw 26 q3 ∷
   rw⁻ 27 q4 ∷
   rw 28 q5 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 27 q3 ∷
   rw⁻ 28 q4 ∷
   rw 29 q5 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 28 q3 ∷
   rw⁻ 29 q4 ∷
   rw 30 q5 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 27 5 (CS03 ∷ []) ∷
   rw 28 q2 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 21 q18 ∷
   re 20 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 22 q1 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q1 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   rw 16 q18 ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   rw 14 q18 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 15 q1 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q19 ∷
   rw 8 q20 ∷
   rw 7 q20 ∷
   rw 8 q21 ∷
   rw 9 q2 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q22 ∷
   rw 11 q2 ∷
   re 9 3 (CK30 ∷ []) ∷
   rw 10 q22 ∷
   rw 13 q2 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q2 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q2 ∷
   re 14 3 (CK30 ∷ []) ∷
   rw 15 q22 ∷
   rw 18 q2 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q2 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q2 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw⁻ 22 q20 ∷
   rw⁻ 23 q20 ∷
   rw⁻ 24 q19 ∷
   rw⁻ 25 q20 ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw 28 q1 ∷
   re 51 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   re 51 3 (CK30 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   re 55 3 (CX13 ∷ []) ∷
   rw 54 q23 ∷
   rw 53 q16 ∷
   rw 52 q24 ∷
   re 52 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 52 5 (CK30 ∷ []) ∷
   re 52 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 50 3 (CX13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   re 50 3 (CK30 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   re 54 3 (CX13 ∷ []) ∷
   rw 53 q23 ∷
   rw 52 q16 ∷
   rw 51 q24 ∷
   re 51 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 51 5 (CK30 ∷ []) ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 49 3 (CX13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   re 49 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   re 53 3 (CX13 ∷ []) ∷
   rw 52 q23 ∷
   rw 51 q4 ∷
   rw 50 q24 ∷
   re 50 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 48 3 (CX13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   re 48 3 (CK30 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 52 3 (CX13 ∷ []) ∷
   rw 51 q23 ∷
   rw 50 q16 ∷
   rw 49 q24 ∷
   re 49 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   re 49 5 (CK30 ∷ []) ∷
   re 49 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   re 47 3 (CX13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   re 51 3 (CX13 ∷ []) ∷
   rw 50 q23 ∷
   rw 49 q4 ∷
   rw 48 q24 ∷
   re 48 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   re 46 3 (CX13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 49 q23 ∷
   rw 48 q4 ∷
   rw 47 q24 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 44 q25 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 47 q23 ∷
   rw 46 q4 ∷
   rw 45 q24 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 43 3 (CX13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 46 q23 ∷
   rw 45 q4 ∷ []) Eq.refl
