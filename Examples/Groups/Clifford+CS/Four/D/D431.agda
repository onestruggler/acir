{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D431 (W : Ws) where

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
  q2 = wE 378 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 151 W
  q5 : Eqn
  q5 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = wE 22 W
  q8 : Eqn
  q8 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q9 : Eqn
  q9 = wE 23 W
  q10 : Eqn
  q10 = wE 114 W
  q11 : Eqn
  q11 = wE 14 W
  q12 : Eqn
  q12 = wE 343 W
  q13 : Eqn
  q13 = wE 12 W
  q14 : Eqn
  q14 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q15 : Eqn
  q15 = wE 338 W
  q16 : Eqn
  q16 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 275 W
  q19 : Eqn
  q19 = wE 39 W
  q20 : Eqn
  q20 = wE 219 W
  q21 : Eqn
  q21 = wE 327 W
  q22 : Eqn
  q22 = wE 315 W
  q23 : Eqn
  q23 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q24 : Eqn
  q24 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q25 : Eqn
  q25 = wE 31 W

-- hyb sym 23 @1320 part2: 381 steps
lem-hyb-sym-23-at1320-part2 : ⟪ (Sw01 ∷ Sw12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ []) ⟫ʷ
lem-hyb-sym-23-at1320-part2 = derive (Sw01 ∷ Sw12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S2 ∷ CK21 ∷ [])
  (re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q1 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q1 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q1 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q1 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q1 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q1 ∷
   rw 68 q2 ∷
   rw 71 q3 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 72 q3 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q3 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 72 q4 ∷
   rw 75 q3 ∷
   re 73 3 (CK30 ∷ []) ∷
   rw 76 q3 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 77 q3 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q3 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 79 q3 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 80 q3 ∷
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q3 ∷
   re 79 3 (CS03 ∷ []) ∷
   rw⁻ 80 q5 ∷
   rw⁻ 81 q6 ∷
   rw 82 q1 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q7 ∷
   rw⁻ 3 q8 ∷
   rw 4 q9 ∷
   re 1 5 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw⁻ 4 q8 ∷
   rw 5 q9 ∷
   re 2 5 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw⁻ 5 q6 ∷
   rw 6 q9 ∷
   re 3 5 (CK30 ∷ []) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 6 q8 ∷
   rw 7 q9 ∷
   re 4 5 (CS03 ∷ []) ∷
   rw 5 q10 ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q11 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q11 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q11 ∷
   re 10 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q11 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q11 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q11 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q11 ∷
   re 16 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q11 ∷
   re 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q11 ∷
   rw 17 q10 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q11 ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q11 ∷
   re 21 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 20 q11 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q11 ∷
   rw 24 q13 ∷
   re 22 3 (CK20 ∷ []) ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q11 ∷
   re 25 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 24 q11 ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q11 ∷
   rw 26 q12 ∷
   re 28 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 27 q11 ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q11 ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 29 q11 ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q11 ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q11 ∷
   re 33 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q11 ∷
   re 34 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q11 ∷
   rw 34 q10 ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q11 ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 36 q11 ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q11 ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q11 ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q11 ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q11 ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q11 ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q11 ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q11 ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q11 ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q11 ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q11 ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q11 ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q11 ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q11 ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q11 ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q11 ∷
   re 53 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q11 ∷
   rw 53 q12 ∷
   rw 54 q12 ∷
   rw 55 q12 ∷
   rw 56 q12 ∷
   re 58 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 57 q11 ∷
   re 59 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 58 q11 ∷
   re 60 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 59 q11 ∷
   re 61 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 60 q11 ∷
   re 62 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 61 q11 ∷
   re 63 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 62 q11 ∷
   re 64 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 63 q11 ∷
   re 65 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 64 q11 ∷
   re 66 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 65 q11 ∷
   re 67 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 66 q11 ∷
   rw 67 q10 ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q7 ∷
   rw⁻ 70 q8 ∷
   rw 71 q9 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q7 ∷
   rw⁻ 71 q8 ∷
   rw 72 q9 ∷
   re 69 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q7 ∷
   rw⁻ 72 q8 ∷
   rw 73 q9 ∷
   re 70 5 (CS03 ∷ []) ∷
   rw 71 q14 ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q7 ∷
   rw⁻ 74 q6 ∷
   rw 75 q9 ∷
   re 72 5 (CK30 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q7 ∷
   rw⁻ 75 q8 ∷
   rw 76 q9 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q7 ∷
   rw⁻ 76 q8 ∷
   rw 77 q9 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q7 ∷
   rw⁻ 77 q8 ∷
   rw 78 q9 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q7 ∷
   rw⁻ 78 q8 ∷
   rw 79 q9 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q7 ∷
   rw⁻ 79 q8 ∷
   rw 80 q9 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q7 ∷
   rw⁻ 80 q8 ∷
   rw 81 q9 ∷
   re 78 5 (CS03 ∷ []) ∷
   rw 79 q15 ∷
   rw 82 q13 ∷
   re 80 3 (CK20 ∷ []) ∷
   rw 81 q11 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 q16 ∷
   rw 1 q17 ∷
   rw 2 q16 ∷
   re 0 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 1 q16 ∷
   rw 2 q17 ∷
   rw 3 q16 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 3 q18 ∷
   rw 4 q16 ∷
   re 2 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 4 q17 ∷
   rw 5 q16 ∷
   re 3 3 (CS13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q16 ∷
   rw 5 q19 ∷
   rw 6 q16 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q20 ∷
   rw 7 q20 ∷
   rw 8 q21 ∷
   rw 9 q22 ∷
   rw 10 q20 ∷
   rw 11 q20 ∷
   rw 12 q20 ∷
   rw 13 q20 ∷
   rw 14 q20 ∷
   rw 15 q20 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q16 ∷
   rw 17 q19 ∷
   rw 18 q16 ∷
   re 16 3 (CX30 ∷ []) ∷
   rw 17 q20 ∷
   rw 18 q20 ∷
   rw 19 q21 ∷
   rw 20 q20 ∷
   rw 21 q18 ∷
   rw 22 q20 ∷
   rw 23 q20 ∷
   rw 24 q20 ∷
   rw 25 q22 ∷
   rw 26 q21 ∷
   rw 27 q20 ∷
   rw 28 q20 ∷
   rw 29 q20 ∷
   rw 30 q20 ∷
   rw 31 q20 ∷
   rw 32 q20 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 33 q16 ∷
   rw 34 q19 ∷
   rw 35 q16 ∷
   re 33 3 (CX30 ∷ []) ∷
   rw 34 q20 ∷
   rw 35 q20 ∷
   rw 36 q20 ∷
   rw 37 q20 ∷
   rw 38 q20 ∷
   rw 39 q20 ∷
   rw 40 q20 ∷
   rw 41 q20 ∷
   rw 42 q20 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   rw 45 q20 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q20 ∷
   rw 49 q20 ∷
   rw 50 q20 ∷
   rw 51 q20 ∷
   rw 52 q22 ∷
   rw 53 q22 ∷
   rw 54 q22 ∷
   rw 55 q22 ∷
   rw 56 q21 ∷
   rw 57 q20 ∷
   rw 58 q20 ∷
   rw 59 q20 ∷
   rw 60 q20 ∷
   rw 61 q20 ∷
   rw 62 q20 ∷
   rw 63 q20 ∷
   rw 64 q20 ∷
   rw 65 q20 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 66 q16 ∷
   rw 67 q19 ∷
   rw 68 q16 ∷
   re 66 3 (CX30 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q16 ∷
   rw 68 q17 ∷
   rw 69 q16 ∷
   re 67 3 (CS13 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q16 ∷
   rw 69 q17 ∷
   rw 70 q16 ∷
   re 68 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q16 ∷
   rw 70 q17 ∷
   rw 71 q16 ∷
   re 69 3 (CS13 ∷ []) ∷
   rw 70 q23 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q16 ∷
   rw 72 q18 ∷
   rw 73 q16 ∷
   re 71 3 (CK31 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q16 ∷
   rw 73 q17 ∷
   rw 74 q16 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q16 ∷
   rw 74 q17 ∷
   rw 75 q16 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q16 ∷
   rw 75 q17 ∷
   rw 76 q16 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q16 ∷
   rw 76 q17 ∷
   rw 77 q16 ∷
   re 75 3 (CS13 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q16 ∷
   rw 77 q17 ∷
   rw 78 q16 ∷
   re 76 3 (CS13 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q16 ∷
   rw 78 q17 ∷
   rw 79 q16 ∷
   re 77 3 (CS13 ∷ []) ∷
   rw 78 q24 ∷
   rw 79 q18 ∷
   rw 80 q25 ∷ []) Eq.refl
