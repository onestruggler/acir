{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D437 (W : Ws) where

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
  q1 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q2 : Eqn
  q2 = wE 7 W
  q3 : Eqn
  q3 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 1176 W
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 142 W
  q8 : Eqn
  q8 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 36 W
  q11 : Eqn
  q11 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q12 : Eqn
  q12 = wE 37 W
  q13 : Eqn
  q13 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q14 : Eqn
  q14 = wE 883 W
  q15 : Eqn
  q15 = wE 1129 W
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = wE 157 W
  q18 : Eqn
  q18 = wE 158 W
  q19 : Eqn
  q19 = wE 3 W
  q20 : Eqn
  q20 = wE 589 W
  q21 : Eqn
  q21 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))
  q22 : Eqn
  q22 = wE 1126 W
  q23 : Eqn
  q23 = wE 5 W
  q24 : Eqn
  q24 = wE 1177 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02] part1: 500 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-part1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ Sw01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q1 ∷
   rw 23 q2 ∷
   rw⁻ 22 q1 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q1 ∷
   rw 22 q2 ∷
   rw⁻ 21 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q1 ∷
   rw 21 q2 ∷
   rw⁻ 20 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw⁻ 19 q3 ∷
   re 18 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q1 ∷
   rw 19 q4 ∷
   rw⁻ 18 q1 ∷
   re 19 3 (CK31 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q1 ∷
   rw 18 q2 ∷
   rw⁻ 17 q1 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q1 ∷
   rw 17 q2 ∷
   rw⁻ 16 q1 ∷
   re 17 3 (CS13 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q1 ∷
   rw 16 q2 ∷
   rw⁻ 15 q1 ∷
   re 16 3 (CS13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q1 ∷
   rw 15 q2 ∷
   rw⁻ 14 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q1 ∷
   rw 14 q2 ∷
   rw⁻ 13 q1 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q1 ∷
   rw 13 q2 ∷
   rw⁻ 12 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 13 q6 ∷
   rw 14 q6 ∷
   rw 15 q7 ∷
   rw 16 q8 ∷
   rw 17 q6 ∷
   rw 18 q6 ∷
   rw 19 q6 ∷
   rw 20 q6 ∷
   rw 21 q6 ∷
   rw 22 q6 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   rw 24 q6 ∷
   rw 25 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   rw 25 q6 ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   rw 26 q6 ∷
   rw 27 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   rw 27 q6 ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   rw 28 q6 ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   rw 29 q6 ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   rw 30 q7 ∷
   rw 31 q1 ∷
   re 29 3 (CK30 ∷ []) ∷
   rw 30 q3 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   rw 32 q6 ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   rw 33 q6 ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   rw 34 q6 ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   rw 35 q6 ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   rw 36 q6 ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   rw 37 q6 ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   rw 38 q6 ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   rw 39 q6 ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   rw 40 q6 ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 40 q9 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q10 ∷
   rw⁻ 12 q11 ∷
   rw 13 q12 ∷
   re 11 3 (CS02 ∷ []) ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q10 ∷
   rw⁻ 13 q11 ∷
   rw 14 q12 ∷
   re 12 3 (CS02 ∷ []) ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q10 ∷
   rw⁻ 14 q11 ∷
   rw 15 q12 ∷
   re 13 3 (CS02 ∷ []) ∷
   re 15 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 14 q10 ∷
   rw⁻ 15 q13 ∷
   rw 16 q12 ∷
   re 14 3 (CK20 ∷ []) ∷
   rw 15 q14 ∷
   re 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q10 ∷
   rw⁻ 17 q11 ∷
   rw 18 q12 ∷
   re 16 3 (CS02 ∷ []) ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q10 ∷
   rw⁻ 18 q11 ∷
   rw 19 q12 ∷
   re 17 3 (CS02 ∷ []) ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q10 ∷
   rw⁻ 19 q11 ∷
   rw 20 q12 ∷
   re 18 3 (CS02 ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q10 ∷
   rw⁻ 20 q11 ∷
   rw 21 q12 ∷
   re 19 3 (CS02 ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q10 ∷
   rw⁻ 21 q11 ∷
   rw 22 q12 ∷
   re 20 3 (CS02 ∷ []) ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q10 ∷
   rw⁻ 22 q11 ∷
   rw 23 q12 ∷
   re 21 3 (CS02 ∷ []) ∷
   rw 5 q15 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q16 ∷
   re 50 3 (CX13 ∷ []) ∷
   rw 49 q17 ∷
   rw 48 q11 ∷
   rw 47 q18 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 46 q19 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q16 ∷
   re 49 3 (CX13 ∷ []) ∷
   rw 48 q17 ∷
   rw 47 q11 ∷
   rw 46 q18 ∷
   re 46 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 45 q19 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q16 ∷
   re 48 3 (CX13 ∷ []) ∷
   rw 47 q17 ∷
   rw 46 q13 ∷
   rw 45 q18 ∷
   re 45 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 44 q19 ∷
   re 45 5 (CK30 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q16 ∷
   re 47 3 (CX13 ∷ []) ∷
   rw 46 q17 ∷
   rw 45 q11 ∷
   rw 44 q18 ∷
   re 44 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 43 q19 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q16 ∷
   re 46 3 (CX13 ∷ []) ∷
   rw 45 q17 ∷
   rw 44 q11 ∷
   rw 43 q18 ∷
   re 43 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q19 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q16 ∷
   re 45 3 (CX13 ∷ []) ∷
   rw 44 q17 ∷
   rw 43 q11 ∷
   rw 42 q18 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q19 ∷
   re 42 5 (CS03 ∷ []) ∷
   rw 40 q20 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q16 ∷
   re 43 3 (CX13 ∷ []) ∷
   rw 42 q17 ∷
   rw 41 q11 ∷
   rw 40 q18 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q19 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q16 ∷
   re 42 3 (CX13 ∷ []) ∷
   rw 41 q17 ∷
   rw 40 q11 ∷
   rw 39 q18 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 38 q19 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q16 ∷
   re 41 3 (CX13 ∷ []) ∷
   rw 40 q17 ∷
   rw 39 q11 ∷
   rw 38 q18 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q19 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q16 ∷
   re 40 3 (CX13 ∷ []) ∷
   rw 39 q17 ∷
   rw 38 q11 ∷
   rw 37 q18 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 36 q19 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q16 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q17 ∷
   rw 37 q11 ∷
   rw 36 q18 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q19 ∷
   re 36 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q16 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q17 ∷
   rw 36 q11 ∷
   rw 35 q18 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q19 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q16 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 36 q17 ∷
   rw 35 q11 ∷
   rw 34 q18 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q19 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q16 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 35 q17 ∷
   rw 34 q11 ∷
   rw 33 q18 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q19 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q16 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 34 q17 ∷
   rw 33 q11 ∷
   rw 32 q18 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q19 ∷
   re 32 5 (CS03 ∷ []) ∷
   rw⁻ 30 q21 ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q16 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 32 q17 ∷
   rw 31 q13 ∷
   rw 30 q18 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q19 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q16 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q17 ∷
   rw 30 q11 ∷
   rw 29 q18 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q19 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q16 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q17 ∷
   rw 29 q11 ∷
   rw 28 q18 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q19 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q16 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 29 q17 ∷
   rw 28 q11 ∷
   rw 27 q18 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q19 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q16 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q17 ∷
   rw 27 q11 ∷
   rw 26 q18 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q19 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q16 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 27 q17 ∷
   rw 26 q11 ∷
   rw 25 q18 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q19 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q16 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 26 q17 ∷
   rw 25 q11 ∷
   rw 24 q18 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q19 ∷
   re 24 5 (CS03 ∷ []) ∷
   rw 22 q20 ∷
   rw 16 q22 ∷
   rw 52 q23 ∷
   rw 51 q2 ∷
   rw 50 q4 ∷
   rw 49 q2 ∷
   rw 48 q2 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q1 ∷
   rw 48 q2 ∷
   rw⁻ 47 q1 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q1 ∷
   rw 47 q2 ∷
   rw⁻ 46 q1 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q1 ∷
   rw 46 q4 ∷
   rw⁻ 45 q1 ∷
   re 46 3 (CK31 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q1 ∷
   rw 45 q2 ∷
   rw⁻ 44 q1 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q1 ∷
   rw 44 q2 ∷
   rw⁻ 43 q1 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q1 ∷
   rw 43 q2 ∷
   rw⁻ 42 q1 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 43 q24 ∷
   rw 42 q6 ∷
   rw 43 q6 ∷
   rw 44 q7 ∷
   rw 45 q6 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q1 ∷
   rw 47 q6 ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   rw 48 q6 ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q1 ∷
   rw 49 q6 ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 49 q1 ∷
   rw 50 q7 ∷
   rw 51 q1 ∷
   re 49 3 (CK30 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 50 q1 ∷
   rw 51 q6 ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q1 ∷
   rw 52 q6 ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q9 ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q10 ∷
   rw⁻ 42 q11 ∷
   rw 43 q12 ∷
   re 41 3 (CS02 ∷ []) ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q10 ∷
   rw⁻ 43 q11 ∷
   rw 44 q12 ∷
   re 42 3 (CS02 ∷ []) ∷
   re 44 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 43 q10 ∷
   rw⁻ 44 q13 ∷
   rw 45 q12 ∷
   re 43 3 (CK20 ∷ []) ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q10 ∷
   rw⁻ 45 q11 ∷
   rw 46 q12 ∷
   re 44 3 (CS02 ∷ []) ∷
   rw 45 q23 ∷
   rw 44 q2 ∷
   rw 43 q4 ∷
   rw 42 q2 ∷
   rw 41 q2 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q1 ∷
   rw 41 q2 ∷
   rw⁻ 40 q1 ∷ []) Eq.refl
