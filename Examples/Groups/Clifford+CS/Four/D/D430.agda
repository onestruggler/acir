{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D430 (W : Ws) where

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
  q2 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wn 480 W)
  q3 : Eqn
  q3 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q5 : Eqn
  q5 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q6 : Eqn
  q6 = eqn (CK21 ∷ Sw01 ∷ []) (Sw01 ∷ CK20 ∷ []) (wn 273 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q10 : Eqn
  q10 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q11 : Eqn
  q11 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wn 479 W)
  q12 : Eqn
  q12 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q13 : Eqn
  q13 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q14 : Eqn
  q14 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q15 : Eqn
  q15 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q16 : Eqn
  q16 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q17 : Eqn
  q17 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q18 : Eqn
  q18 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q19 : Eqn
  q19 = eqn (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) (wn 477 W)
  q20 : Eqn
  q20 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q21 : Eqn
  q21 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wn 476 W)
  q22 : Eqn
  q22 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q23 : Eqn
  q23 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q24 : Eqn
  q24 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q25 : Eqn
  q25 = eqn (CX21 ∷ Sw12 ∷ []) (Sw12 ∷ CX12 ∷ []) (wn 478 W)

-- hyb sym 23 @1320 part0: 500 steps
lem-hyb-sym-23-at1320-part0 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ
lem-hyb-sym-23-at1320-part0 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK01 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S0 ∷ CK01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q4 ∷
   rw 78 q5 ∷
   rw⁻ 77 q4 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q4 ∷
   rw 77 q5 ∷
   rw⁻ 76 q4 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q4 ∷
   rw 76 q5 ∷
   rw⁻ 75 q4 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q4 ∷
   rw 75 q5 ∷
   rw⁻ 74 q4 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q4 ∷
   rw 74 q5 ∷
   rw⁻ 73 q4 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q4 ∷
   rw 73 q5 ∷
   rw⁻ 72 q4 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q4 ∷
   rw 72 q6 ∷
   rw⁻ 71 q4 ∷
   re 72 3 (CK30 ∷ []) ∷
   rw⁻ 70 q7 ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q4 ∷
   rw 70 q5 ∷
   rw⁻ 69 q4 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q4 ∷
   rw 69 q5 ∷
   rw⁻ 68 q4 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 69 q4 ∷
   rw 68 q5 ∷
   rw⁻ 67 q4 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw⁻ 66 q8 ∷
   rw 65 q5 ∷
   rw 64 q5 ∷
   rw 63 q5 ∷
   rw 62 q5 ∷
   rw 61 q5 ∷
   rw 60 q5 ∷
   rw 59 q5 ∷
   rw 58 q5 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   rw⁻ 55 q9 ∷
   rw⁻ 54 q9 ∷
   rw⁻ 53 q9 ∷
   rw⁻ 52 q9 ∷
   rw 51 q5 ∷
   rw 50 q5 ∷
   rw 49 q5 ∷
   rw 48 q5 ∷
   rw 47 q5 ∷
   rw 46 q5 ∷
   rw 45 q5 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw 41 q5 ∷
   rw 40 q5 ∷
   rw 39 q5 ∷
   rw 38 q5 ∷
   rw 37 q5 ∷
   rw 36 q5 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw⁻ 33 q8 ∷
   rw 32 q5 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw⁻ 25 q9 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q2 ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw⁻ 16 q8 ∷
   rw 15 q5 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw⁻ 9 q9 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q5 ∷
   rw 5 q5 ∷
   rw⁻ 4 q8 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 4 q5 ∷
   rw⁻ 3 q4 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 3 q6 ∷
   rw⁻ 2 q4 ∷
   re 3 3 (CK30 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 2 q5 ∷
   rw⁻ 1 q4 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 1 q5 ∷
   rw⁻ 0 q4 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 81 q10 ∷
   rw 80 q10 ∷
   re 81 3 (CK20 ∷ []) ∷
   rw 79 q11 ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q12 ∷
   rw 80 q13 ∷
   rw 78 q14 ∷
   re 79 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q12 ∷
   rw 79 q13 ∷
   rw 77 q14 ∷
   re 78 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q12 ∷
   rw 78 q13 ∷
   rw 76 q14 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q12 ∷
   rw 77 q13 ∷
   rw 75 q14 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q12 ∷
   rw 76 q13 ∷
   rw 74 q14 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q12 ∷
   rw 75 q13 ∷
   rw 73 q14 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q12 ∷
   rw 74 q15 ∷
   rw 72 q14 ∷
   re 73 5 (CK30 ∷ []) ∷
   rw⁻ 71 q16 ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q12 ∷
   rw 72 q13 ∷
   rw 70 q14 ∷
   re 71 5 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q12 ∷
   rw 71 q13 ∷
   rw 69 q14 ∷
   re 70 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q12 ∷
   rw 70 q13 ∷
   rw 68 q14 ∷
   re 69 5 (CS03 ∷ []) ∷
   rw 67 q17 ∷
   re 66 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 68 q18 ∷
   re 65 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 67 q18 ∷
   re 64 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 66 q18 ∷
   re 63 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 65 q18 ∷
   re 62 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 64 q18 ∷
   re 61 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 63 q18 ∷
   re 60 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 62 q18 ∷
   re 59 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 61 q18 ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 60 q18 ∷
   re 57 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 59 q18 ∷
   rw 56 q19 ∷
   rw 55 q19 ∷
   rw 54 q19 ∷
   rw 53 q19 ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q18 ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q18 ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q18 ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q18 ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q18 ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q18 ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q18 ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q18 ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q18 ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q18 ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q18 ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q18 ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q18 ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q18 ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q18 ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q18 ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q18 ∷
   re 35 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q18 ∷
   rw 34 q17 ∷
   re 33 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q18 ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 34 q18 ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q18 ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q18 ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q18 ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q18 ∷
   re 27 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 29 q18 ∷
   rw 26 q19 ∷
   re 25 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q18 ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q18 ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q18 ∷
   rw 22 q10 ∷
   re 23 3 (CK20 ∷ []) ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q18 ∷
   re 20 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 22 q18 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q18 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q18 ∷
   rw 17 q17 ∷
   re 16 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q18 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q18 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q18 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q18 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q18 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q18 ∷
   rw 10 q19 ∷
   re 9 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 11 q18 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q18 ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q18 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q17 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 6 q13 ∷
   rw 4 q14 ∷
   re 5 5 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 5 q15 ∷
   rw 3 q14 ∷
   re 4 5 (CK30 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q12 ∷
   rw 4 q13 ∷
   rw 2 q14 ∷
   re 3 5 (CS03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 1 q14 ∷
   re 2 5 (CS03 ∷ []) ∷
   rw 82 q20 ∷
   rw 81 q20 ∷
   re 82 3 (CK30 ∷ []) ∷
   rw 80 q21 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q22 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q22 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q22 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q22 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q22 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q22 ∷
   re 73 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 75 q22 ∷
   rw 72 q23 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q22 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q22 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q22 ∷
   re 68 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 70 q22 ∷
   rw 67 q13 ∷
   rw 66 q13 ∷
   rw 65 q13 ∷
   rw 64 q13 ∷
   rw 63 q13 ∷
   rw 62 q13 ∷
   rw 61 q13 ∷
   rw 60 q13 ∷
   rw 59 q13 ∷
   rw 58 q15 ∷
   rw 57 q24 ∷
   rw 56 q24 ∷
   rw 55 q24 ∷
   rw 54 q24 ∷
   rw 53 q13 ∷
   rw 52 q13 ∷
   rw 51 q13 ∷
   rw 50 q13 ∷
   rw 49 q13 ∷
   rw 48 q13 ∷
   rw 47 q13 ∷
   rw 46 q13 ∷
   rw 45 q13 ∷
   rw 44 q13 ∷
   rw 43 q13 ∷
   rw 42 q13 ∷
   rw 41 q13 ∷
   rw 40 q13 ∷
   rw 39 q13 ∷
   rw 38 q13 ∷
   rw 37 q13 ∷
   rw 36 q13 ∷
   re 35 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 37 q22 ∷
   rw 34 q13 ∷
   rw 33 q13 ∷
   rw 32 q13 ∷
   rw 31 q13 ∷
   rw 30 q13 ∷
   rw 29 q13 ∷
   rw 28 q15 ∷
   rw 27 q24 ∷
   rw 26 q13 ∷
   rw 25 q13 ∷
   rw 24 q13 ∷
   rw 23 q20 ∷
   re 24 3 (CK30 ∷ []) ∷
   rw 22 q13 ∷
   rw 21 q15 ∷
   rw 20 q13 ∷
   rw 19 q13 ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q22 ∷
   rw 17 q13 ∷
   rw 16 q13 ∷
   rw 15 q13 ∷
   rw 14 q13 ∷
   rw 13 q13 ∷
   rw 12 q13 ∷
   rw 11 q24 ∷
   rw 10 q15 ∷
   rw 9 q13 ∷
   rw 8 q13 ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q22 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q22 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q22 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q22 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q22 ∷
   rw 83 q10 ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q12 ∷
   rw 84 q15 ∷
   rw 82 q14 ∷
   re 83 5 (CK30 ∷ []) ∷
   rw⁻ 81 q16 ∷
   re 80 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 82 q18 ∷
   re 79 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 81 q18 ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q18 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q18 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q18 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q18 ∷
   re 74 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 76 q18 ∷
   rw 73 q19 ∷
   re 72 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 74 q18 ∷
   re 71 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 73 q18 ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q18 ∷
   rw 69 q25 ∷
   rw 68 q10 ∷
   re 69 3 (CS02 ∷ []) ∷
   rw 67 q10 ∷
   re 68 3 (CS02 ∷ []) ∷
   rw 66 q10 ∷
   re 67 3 (CS02 ∷ []) ∷
   rw 65 q10 ∷
   re 66 3 (CS02 ∷ []) ∷
   rw 64 q10 ∷
   re 65 3 (CS02 ∷ []) ∷
   rw 63 q10 ∷
   re 64 3 (CS02 ∷ []) ∷
   rw 62 q10 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 61 q10 ∷
   re 62 3 (CS02 ∷ []) ∷
   rw 60 q10 ∷
   re 61 3 (CS02 ∷ []) ∷
   rw 59 q10 ∷
   re 60 3 (CK20 ∷ []) ∷
   rw 58 q11 ∷
   rw 57 q11 ∷
   rw 56 q11 ∷
   rw 55 q11 ∷
   rw 54 q10 ∷
   re 55 3 (CS02 ∷ []) ∷
   rw 53 q10 ∷
   re 54 3 (CS02 ∷ []) ∷
   rw 52 q10 ∷
   re 53 3 (CS02 ∷ []) ∷
   rw 51 q10 ∷
   re 52 3 (CS02 ∷ []) ∷
   rw 50 q10 ∷
   re 51 3 (CS02 ∷ []) ∷
   rw 49 q10 ∷
   re 50 3 (CS02 ∷ []) ∷
   rw 48 q10 ∷
   re 49 3 (CS02 ∷ []) ∷
   rw 47 q10 ∷
   re 48 3 (CS02 ∷ []) ∷
   rw 46 q10 ∷
   re 47 3 (CS02 ∷ []) ∷ []) Eq.refl
