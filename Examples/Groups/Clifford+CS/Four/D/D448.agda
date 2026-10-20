{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D448 (W : Ws) where

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
  q2 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q3 : Eqn
  q3 = eqn (S0 ∷ Sw01 ∷ []) (Sw01 ∷ S1 ∷ []) (wn 481 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (CX21 ∷ Sw01 ∷ []) (Sw01 ∷ CX20 ∷ []) (wn 1205 W)
  q9 : Eqn
  q9 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q10 : Eqn
  q10 = eqn (CK12 ∷ Sw01 ∷ []) (Sw01 ∷ CK02 ∷ []) (wn 1206 W)
  q11 : Eqn
  q11 = eqn (S1 ∷ Sw01 ∷ []) (Sw01 ∷ S0 ∷ []) (wn 1207 W)
  q12 : Eqn
  q12 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q13 : Eqn
  q13 = eqn (CK12 ∷ Sw12 ∷ []) (Sw12 ∷ CK21 ∷ []) (wn 757 W)
  q14 : Eqn
  q14 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wn 479 W)
  q15 : Eqn
  q15 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q16 : Eqn
  q16 = eqn (CK32 ∷ Sw12 ∷ []) (Sw12 ∷ CK31 ∷ []) (wn 280 W)
  q17 : Eqn
  q17 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q18 : Eqn
  q18 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q19 : Eqn
  q19 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q20 : Eqn
  q20 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q21 : Eqn
  q21 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q22 : Eqn
  q22 = eqn (S0 ∷ Sw12 ∷ []) (Sw12 ∷ S0 ∷ []) (low₁-comm (S) (Swap))
  q23 : Eqn
  q23 = eqn (CK21 ∷ Sw01 ∷ []) (Sw01 ∷ CK20 ∷ []) (wn 273 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q25 : Eqn
  q25 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q26 : Eqn
  q26 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wn 216 W)
  q27 : Eqn
  q27 = eqn (CK01 ∷ Sw01 ∷ []) (Sw01 ∷ CK10 ∷ []) (wn 480 W)
  q28 : Eqn
  q28 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q29 : Eqn
  q29 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wn 476 W)
  q30 : Eqn
  q30 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q31 : Eqn
  q31 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q32 : Eqn
  q32 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q33 : Eqn
  q33 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q34 : Eqn
  q34 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))

-- hyb sym 23 @2310 part0: 500 steps
lem-hyb-sym-23-at2310-part0 : ⟪ (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ
lem-hyb-sym-23-at2310-part0 = derive (CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CK12 ∷ CS12 ∷ CK02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX31 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S3 ∷ CK32 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ S0 ∷ CK02 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  (rw 80 q1 ∷
   rw 79 q2 ∷
   rw 78 q3 ∷
   rw⁻ 77 q4 ∷
   rw⁻ 76 q4 ∷
   rw⁻ 75 q4 ∷
   rw⁻ 74 q4 ∷
   rw⁻ 73 q4 ∷
   rw⁻ 72 q4 ∷
   rw⁻ 71 q5 ∷
   rw⁻ 70 q6 ∷
   rw⁻ 69 q4 ∷
   rw⁻ 68 q4 ∷
   rw⁻ 67 q4 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q7 ∷
   rw 67 q8 ∷
   rw⁻ 66 q7 ∷
   re 67 3 (CX30 ∷ []) ∷
   rw 65 q9 ∷
   rw 64 q9 ∷
   rw 63 q9 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 59 q9 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q10 ∷
   rw 55 q11 ∷
   rw 54 q11 ∷
   rw 53 q11 ∷
   rw 52 q11 ∷
   rw 51 q9 ∷
   rw 50 q9 ∷
   rw 49 q9 ∷
   rw 48 q9 ∷
   rw 47 q9 ∷
   rw 46 q9 ∷
   rw 45 q9 ∷
   rw 44 q9 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q9 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   rw 35 q9 ∷
   rw 34 q9 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q7 ∷
   rw 34 q8 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (CX30 ∷ []) ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q10 ∷
   rw 25 q11 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   rw 22 q9 ∷
   rw 21 q2 ∷
   rw 20 q9 ∷
   rw 19 q10 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   re 16 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q7 ∷
   rw 17 q8 ∷
   rw⁻ 16 q7 ∷
   re 17 3 (CX30 ∷ []) ∷
   rw 15 q9 ∷
   rw 14 q9 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q9 ∷
   rw 10 q9 ∷
   rw 9 q11 ∷
   rw 8 q10 ∷
   rw 7 q9 ∷
   rw 6 q9 ∷
   rw 5 q9 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q8 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CX30 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 1 q4 ∷
   rw⁻ 0 q4 ∷
   rw 81 q12 ∷
   rw 80 q13 ∷
   rw 79 q14 ∷
   rw 78 q15 ∷
   rw 77 q15 ∷
   rw 76 q15 ∷
   rw 75 q15 ∷
   rw 74 q15 ∷
   rw 73 q15 ∷
   rw 72 q16 ∷
   rw⁻ 71 q17 ∷
   rw 70 q15 ∷
   rw 69 q15 ∷
   rw 68 q15 ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q18 ∷
   rw 69 q19 ∷
   rw 67 q20 ∷
   re 68 5 (CX30 ∷ []) ∷
   re 66 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 68 q21 ∷
   re 65 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 67 q21 ∷
   re 64 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 66 q21 ∷
   re 63 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 65 q21 ∷
   re 62 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 64 q21 ∷
   re 61 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 63 q21 ∷
   re 60 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 62 q21 ∷
   re 59 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 61 q21 ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 60 q21 ∷
   re 57 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 59 q21 ∷
   rw 56 q22 ∷
   rw 55 q22 ∷
   rw 54 q22 ∷
   rw 53 q22 ∷
   re 52 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 54 q21 ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q21 ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q21 ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q21 ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q21 ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q21 ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q21 ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q21 ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q21 ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q21 ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q21 ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q21 ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q21 ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q21 ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q21 ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q21 ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q21 ∷
   re 35 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q21 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q18 ∷
   rw 36 q19 ∷
   rw 34 q20 ∷
   re 35 5 (CX30 ∷ []) ∷
   re 33 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 35 q21 ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 34 q21 ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q21 ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q21 ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q21 ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q21 ∷
   re 27 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 29 q21 ∷
   rw 26 q22 ∷
   re 25 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q21 ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q21 ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q21 ∷
   rw 22 q13 ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q21 ∷
   re 20 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 22 q21 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q21 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q21 ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   rw 19 q19 ∷
   rw 17 q20 ∷
   re 18 5 (CX30 ∷ []) ∷
   re 16 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q21 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q21 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q21 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q21 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q21 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q21 ∷
   rw 10 q22 ∷
   re 9 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 11 q21 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q21 ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q21 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q21 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 7 q19 ∷
   rw 5 q20 ∷
   re 6 5 (CX30 ∷ []) ∷
   rw 4 q15 ∷
   rw 3 q16 ∷
   rw 2 q15 ∷
   rw 1 q15 ∷
   rw 82 q1 ∷
   rw 81 q23 ∷
   rw⁻ 80 q24 ∷
   re 79 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q7 ∷
   rw 80 q9 ∷
   rw⁻ 79 q7 ∷
   re 80 3 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 80 q7 ∷
   rw 79 q9 ∷
   rw⁻ 78 q7 ∷
   re 79 3 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 79 q7 ∷
   rw 78 q9 ∷
   rw⁻ 77 q7 ∷
   re 78 3 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 78 q7 ∷
   rw 77 q9 ∷
   rw⁻ 76 q7 ∷
   re 77 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 77 q7 ∷
   rw 76 q9 ∷
   rw⁻ 75 q7 ∷
   re 76 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 76 q7 ∷
   rw 75 q9 ∷
   rw⁻ 74 q7 ∷
   re 75 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q7 ∷
   rw 74 q23 ∷
   rw⁻ 73 q7 ∷
   re 74 3 (CK30 ∷ []) ∷
   rw⁻ 72 q6 ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q7 ∷
   rw 72 q9 ∷
   rw⁻ 71 q7 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q7 ∷
   rw 71 q9 ∷
   rw⁻ 70 q7 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q7 ∷
   rw 70 q9 ∷
   rw⁻ 69 q7 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q7 ∷
   rw 69 q25 ∷
   rw⁻ 68 q7 ∷
   re 69 3 (CX31 ∷ []) ∷
   rw 67 q26 ∷
   rw 66 q26 ∷
   rw 65 q26 ∷
   rw 64 q26 ∷
   rw 63 q26 ∷
   rw 62 q26 ∷
   rw 61 q26 ∷
   rw 60 q26 ∷
   rw 59 q26 ∷
   rw 58 q27 ∷
   rw 57 q3 ∷
   rw 56 q3 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q26 ∷
   rw 52 q26 ∷
   rw 51 q26 ∷
   rw 50 q26 ∷
   rw 49 q26 ∷
   rw 48 q26 ∷
   rw 47 q26 ∷
   rw 46 q26 ∷
   rw 45 q26 ∷
   rw 44 q26 ∷
   rw 43 q26 ∷
   rw 42 q26 ∷
   rw 41 q26 ∷
   rw 40 q26 ∷
   rw 39 q26 ∷
   rw 38 q26 ∷
   rw 37 q26 ∷
   rw 36 q26 ∷
   re 35 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q7 ∷
   rw 36 q25 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (CX31 ∷ []) ∷
   rw 34 q26 ∷
   rw 33 q26 ∷
   rw 32 q26 ∷
   rw 31 q26 ∷
   rw 30 q26 ∷
   rw 29 q26 ∷
   rw 28 q27 ∷
   rw 27 q3 ∷
   rw 26 q26 ∷
   rw 25 q26 ∷
   rw 24 q26 ∷
   rw 23 q23 ∷
   rw 22 q26 ∷
   rw 21 q27 ∷
   rw 20 q26 ∷
   rw 19 q26 ∷
   re 18 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q7 ∷
   rw 19 q25 ∷
   rw⁻ 18 q7 ∷
   re 19 3 (CX31 ∷ []) ∷
   rw 17 q26 ∷
   rw 16 q26 ∷
   rw 15 q26 ∷
   rw 14 q26 ∷
   rw 13 q26 ∷
   rw 12 q26 ∷
   rw 11 q3 ∷
   rw 10 q27 ∷
   rw 9 q26 ∷
   rw 8 q26 ∷
   rw 7 q26 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 7 q25 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (CX31 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q9 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q23 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CK30 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q7 ∷
   rw 4 q9 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q7 ∷
   rw 3 q9 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 83 q28 ∷
   rw 82 q28 ∷
   re 83 3 (CK30 ∷ []) ∷
   rw 81 q29 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q30 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q30 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q30 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q30 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q30 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q30 ∷
   re 74 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 76 q30 ∷
   rw 73 q31 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q30 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q30 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q30 ∷
   re 69 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 71 q30 ∷
   rw 68 q32 ∷
   rw 67 q32 ∷
   rw 66 q32 ∷
   rw 65 q32 ∷
   rw 64 q32 ∷
   rw 63 q32 ∷
   rw 62 q32 ∷
   rw 61 q32 ∷
   rw 60 q32 ∷
   rw 59 q33 ∷
   rw 58 q34 ∷
   rw 57 q34 ∷
   rw 56 q34 ∷
   rw 55 q34 ∷
   rw 54 q32 ∷
   rw 53 q32 ∷
   rw 52 q32 ∷
   rw 51 q32 ∷
   rw 50 q32 ∷
   rw 49 q32 ∷
   rw 48 q32 ∷
   rw 47 q32 ∷
   rw 46 q32 ∷
   rw 45 q32 ∷
   rw 44 q32 ∷
   rw 43 q32 ∷
   rw 42 q32 ∷
   rw 41 q32 ∷
   rw 40 q32 ∷
   rw 39 q32 ∷
   rw 38 q32 ∷
   rw 37 q32 ∷
   re 36 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 38 q30 ∷
   rw 35 q32 ∷
   rw 34 q32 ∷
   rw 33 q32 ∷
   rw 32 q32 ∷
   rw 31 q32 ∷
   rw 30 q32 ∷
   rw 29 q33 ∷
   rw 28 q34 ∷
   rw 27 q32 ∷
   rw 26 q32 ∷
   rw 25 q32 ∷
   rw 24 q28 ∷
   re 25 3 (CK30 ∷ []) ∷
   rw 23 q32 ∷
   rw 22 q33 ∷
   rw 21 q32 ∷
   rw 20 q32 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q30 ∷
   rw 18 q32 ∷
   rw 17 q32 ∷
   rw 16 q32 ∷
   rw 15 q32 ∷
   rw 14 q32 ∷
   rw 13 q32 ∷
   rw 12 q34 ∷
   rw 11 q33 ∷
   rw 10 q32 ∷
   rw 9 q32 ∷
   rw 8 q32 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q30 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q30 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 7 q30 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q30 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q30 ∷ []) Eq.refl
