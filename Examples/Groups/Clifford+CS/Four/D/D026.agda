{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D026 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wn 476 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q9 : Eqn
  q9 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q10 : Eqn
  q10 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q11 : Eqn
  q11 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q12 : Eqn
  q12 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q13 : Eqn
  q13 = eqn (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) (wn 477 W)
  q14 : Eqn
  q14 = eqn (CX21 ∷ Sw12 ∷ []) (Sw12 ∷ CX12 ∷ []) (wn 478 W)
  q15 : Eqn
  q15 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wn 479 W)
  q16 : Eqn
  q16 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q17 : Eqn
  q17 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q18 : Eqn
  q18 = eqn (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) (wn 343 W)
  q19 : Eqn
  q19 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K))
  q20 : Eqn
  q20 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q21 : Eqn
  q21 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q22 : Eqn
  q22 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q23 : Eqn
  q23 = eqn (Sw12 ∷ ι1 ∷ []) (ι2 ∷ Sw12 ∷ []) (wn 364 W)
  q24 : Eqn
  q24 = eqn (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ ι2 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wn 369 W)
  q25 : Eqn
  q25 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q26 : Eqn
  q26 = eqn (Sw23 ∷ K3 ∷ []) (K2 ∷ Sw23 ∷ []) (wn 336 W)
  q27 : Eqn
  q27 = eqn (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) (wn 71 W)
  q28 : Eqn
  q28 = eqn (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) (wn 72 W)
  q29 : Eqn
  q29 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q30 : Eqn
  q30 = eqn (K2 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 386 W)
  q31 : Eqn
  q31 = eqn (Sw23 ∷ CX23 ∷ []) (CX32 ∷ Sw23 ∷ []) (wn 378 W)
  q32 : Eqn
  q32 = eqn (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) (wn 372 W)

-- AXIOM LF @0312: 743 steps
lem-AXIOM-LF-at0312 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-AXIOM-LF-at0312 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK20 ∷ []) (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ Toff213 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 80 q1 ∷
   rw 79 q1 ∷
   re 80 3 (CK30 ∷ []) ∷
   rw 78 q2 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   rw 70 q4 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q3 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q3 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q3 ∷
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
   rw 55 q7 ∷
   rw 54 q7 ∷
   rw 53 q7 ∷
   rw 52 q7 ∷
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
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   rw 32 q5 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q7 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q1 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 20 q5 ∷
   rw 19 q6 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   re 16 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 15 q5 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q5 ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 81 q8 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q9 ∷
   rw 82 q6 ∷
   rw 80 q10 ∷
   re 81 5 (CK30 ∷ []) ∷
   rw⁻ 79 q11 ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q12 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q12 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q12 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q12 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q12 ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q12 ∷
   re 72 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 74 q12 ∷
   rw 71 q13 ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q12 ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q12 ∷
   re 68 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q12 ∷
   rw 67 q14 ∷
   rw 66 q8 ∷
   re 67 3 (CS02 ∷ []) ∷
   rw 65 q8 ∷
   re 66 3 (CS02 ∷ []) ∷
   rw 64 q8 ∷
   re 65 3 (CS02 ∷ []) ∷
   rw 63 q8 ∷
   re 64 3 (CS02 ∷ []) ∷
   rw 62 q8 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 61 q8 ∷
   re 62 3 (CS02 ∷ []) ∷
   rw 60 q8 ∷
   re 61 3 (CS02 ∷ []) ∷
   rw 59 q8 ∷
   re 60 3 (CS02 ∷ []) ∷
   rw 58 q8 ∷
   re 59 3 (CS02 ∷ []) ∷
   rw 57 q8 ∷
   re 58 3 (CK20 ∷ []) ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q8 ∷
   re 53 3 (CS02 ∷ []) ∷
   rw 51 q8 ∷
   re 52 3 (CS02 ∷ []) ∷
   rw 50 q8 ∷
   re 51 3 (CS02 ∷ []) ∷
   rw 49 q8 ∷
   re 50 3 (CS02 ∷ []) ∷
   rw 48 q8 ∷
   re 49 3 (CS02 ∷ []) ∷
   rw 47 q8 ∷
   re 48 3 (CS02 ∷ []) ∷
   rw 46 q8 ∷
   re 47 3 (CS02 ∷ []) ∷
   rw 45 q8 ∷
   re 46 3 (CS02 ∷ []) ∷
   rw 44 q8 ∷
   re 45 3 (CS02 ∷ []) ∷
   rw 43 q8 ∷
   re 44 3 (CS02 ∷ []) ∷
   rw 42 q8 ∷
   re 43 3 (CS02 ∷ []) ∷
   rw 41 q8 ∷
   re 42 3 (CS02 ∷ []) ∷
   rw 40 q8 ∷
   re 41 3 (CS02 ∷ []) ∷
   rw 39 q8 ∷
   re 40 3 (CS02 ∷ []) ∷
   rw 38 q8 ∷
   re 39 3 (CS02 ∷ []) ∷
   rw 37 q8 ∷
   re 38 3 (CS02 ∷ []) ∷
   rw 36 q8 ∷
   re 37 3 (CS02 ∷ []) ∷
   rw 35 q8 ∷
   re 36 3 (CS02 ∷ []) ∷
   rw 34 q14 ∷
   rw 33 q8 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 32 q8 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 31 q8 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 30 q8 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 29 q8 ∷
   re 30 3 (CS02 ∷ []) ∷
   rw 28 q8 ∷
   re 29 3 (CS02 ∷ []) ∷
   rw 27 q8 ∷
   re 28 3 (CK20 ∷ []) ∷
   rw 26 q15 ∷
   rw 25 q8 ∷
   re 26 3 (CS02 ∷ []) ∷
   rw 24 q8 ∷
   re 25 3 (CS02 ∷ []) ∷
   rw 23 q8 ∷
   re 24 3 (CS02 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q9 ∷
   rw 24 q6 ∷
   rw 22 q10 ∷
   re 23 5 (CK30 ∷ []) ∷
   rw 21 q8 ∷
   re 22 3 (CS02 ∷ []) ∷
   rw 20 q8 ∷
   re 21 3 (CK20 ∷ []) ∷
   rw 19 q8 ∷
   re 20 3 (CS02 ∷ []) ∷
   rw 18 q8 ∷
   re 19 3 (CS02 ∷ []) ∷
   rw 17 q14 ∷
   rw 16 q8 ∷
   re 17 3 (CS02 ∷ []) ∷
   rw 15 q8 ∷
   re 16 3 (CS02 ∷ []) ∷
   rw 14 q8 ∷
   re 15 3 (CS02 ∷ []) ∷
   rw 13 q8 ∷
   re 14 3 (CS02 ∷ []) ∷
   rw 12 q8 ∷
   re 13 3 (CS02 ∷ []) ∷
   rw 11 q8 ∷
   re 12 3 (CS02 ∷ []) ∷
   rw 10 q15 ∷
   rw 9 q8 ∷
   re 10 3 (CK20 ∷ []) ∷
   rw 8 q8 ∷
   re 9 3 (CS02 ∷ []) ∷
   rw 7 q8 ∷
   re 8 3 (CS02 ∷ []) ∷
   rw 6 q8 ∷
   re 7 3 (CS02 ∷ []) ∷
   rw 5 q14 ∷
   re 4 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q12 ∷
   re 3 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 5 q12 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 4 q12 ∷
   re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 3 q12 ∷
   rw 2 q16 ∷
   rw 3 q8 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 4 q8 ∷
   re 2 3 (CS02 ∷ []) ∷
   rw 5 q8 ∷
   re 3 3 (CK20 ∷ []) ∷
   rw 6 q8 ∷
   re 4 3 (CS02 ∷ []) ∷
   rw 7 q8 ∷
   re 5 3 (CK20 ∷ []) ∷
   rw 8 q8 ∷
   re 6 3 (CK20 ∷ []) ∷
   rw 7 q17 ∷
   re 9 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q18 ∷
   re 11 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q18 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q12 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q12 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q12 ∷
   re 16 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 15 q12 ∷
   rw 16 q18 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q12 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q12 ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q12 ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q12 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q12 ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q12 ∷
   rw 23 q17 ∷
   re 25 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 24 q12 ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q12 ∷
   re 27 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 26 q12 ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 27 q12 ∷
   re 29 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 28 q12 ∷
   re 30 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 29 q12 ∷
   re 31 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 30 q19 ∷
   rw 31 q20 ∷
   rw 32 q17 ∷
   rw 33 q21 ∷
   rw 34 q17 ∷
   rw 35 q22 ∷
   rw 36 q19 ∷
   rw 37 q23 ∷
   rw 30 q24 ∷
   re 30 8 (Toff312 ∷ []) ∷
   rw 33 q8 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 34 q8 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 35 q8 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 36 q8 ∷
   re 34 3 (CK20 ∷ []) ∷
   rw 37 q8 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 38 q8 ∷
   re 36 3 (CS02 ∷ []) ∷
   rw 37 q25 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q9 ∷
   rw⁻ 40 q5 ∷
   rw 41 q10 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q9 ∷
   rw⁻ 41 q5 ∷
   rw 42 q10 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q9 ∷
   rw⁻ 42 q5 ∷
   rw 43 q10 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q9 ∷
   rw⁻ 43 q5 ∷
   rw 44 q10 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q9 ∷
   rw⁻ 44 q5 ∷
   rw 45 q10 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q9 ∷
   rw⁻ 45 q5 ∷
   rw 46 q10 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q9 ∷
   rw⁻ 46 q6 ∷
   rw 47 q10 ∷
   re 44 5 (CK30 ∷ []) ∷
   rw 45 q11 ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q9 ∷
   rw⁻ 48 q5 ∷
   rw 49 q10 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q9 ∷
   rw⁻ 49 q5 ∷
   rw 50 q10 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q9 ∷
   rw⁻ 50 q5 ∷
   rw 51 q10 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q9 ∷
   rw⁻ 51 q5 ∷
   rw 52 q10 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q9 ∷
   rw⁻ 52 q5 ∷
   rw 53 q10 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q9 ∷
   rw⁻ 53 q5 ∷
   rw 54 q10 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q9 ∷
   rw⁻ 54 q5 ∷
   rw 55 q10 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q9 ∷
   rw⁻ 55 q5 ∷
   rw 56 q10 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q9 ∷
   rw⁻ 56 q5 ∷
   rw 57 q10 ∷
   re 54 5 (CS03 ∷ []) ∷
   rw 55 q25 ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q9 ∷
   rw⁻ 58 q5 ∷
   rw 59 q10 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q9 ∷
   rw⁻ 59 q5 ∷
   rw 60 q10 ∷
   re 57 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q9 ∷
   rw⁻ 60 q5 ∷
   rw 61 q10 ∷
   re 58 5 (CS03 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q9 ∷
   rw⁻ 61 q6 ∷
   rw 62 q10 ∷
   re 59 5 (CK30 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q9 ∷
   rw⁻ 62 q5 ∷
   rw 63 q10 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q9 ∷
   rw⁻ 63 q5 ∷
   rw 64 q10 ∷
   re 61 5 (CS03 ∷ []) ∷
   re 63 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 62 q19 ∷
   rw 63 q20 ∷
   rw 64 q17 ∷
   rw 65 q21 ∷
   rw 66 q17 ∷
   rw 67 q22 ∷
   rw 68 q19 ∷
   rw 69 q23 ∷
   rw 62 q24 ∷
   re 62 8 (Toff312 ∷ []) ∷
   rw 65 q8 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 66 q8 ∷
   re 64 3 (CS02 ∷ []) ∷
   rw 67 q8 ∷
   re 65 3 (CK20 ∷ []) ∷
   rw 68 q8 ∷
   re 66 3 (CS02 ∷ []) ∷
   rw 69 q8 ∷
   re 67 3 (CK20 ∷ []) ∷
   rw 70 q8 ∷
   re 68 3 (CK20 ∷ []) ∷
   rw 69 q25 ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q9 ∷
   rw⁻ 72 q6 ∷
   rw 73 q10 ∷
   re 70 5 (CK30 ∷ []) ∷
   rw 71 q11 ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q9 ∷
   rw⁻ 74 q6 ∷
   rw 75 q10 ∷
   re 72 5 (CK30 ∷ []) ∷
   rw 73 q11 ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q9 ∷
   rw⁻ 76 q5 ∷
   rw 77 q10 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q9 ∷
   rw⁻ 77 q5 ∷
   rw 78 q10 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q9 ∷
   rw⁻ 78 q5 ∷
   rw 79 q10 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 78 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q9 ∷
   rw⁻ 79 q6 ∷
   rw 80 q10 ∷
   re 77 5 (CK30 ∷ []) ∷
   rw 78 q11 ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q9 ∷
   rw⁻ 81 q5 ∷
   rw 82 q10 ∷
   re 79 5 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q9 ∷
   rw⁻ 82 q5 ∷
   rw 83 q10 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q9 ∷
   rw⁻ 83 q5 ∷
   rw 84 q10 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q9 ∷
   rw⁻ 84 q5 ∷
   rw 85 q10 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q9 ∷
   rw⁻ 85 q5 ∷
   rw 86 q10 ∷
   re 83 5 (CS03 ∷ []) ∷
   re 85 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q9 ∷
   rw⁻ 86 q5 ∷
   rw 87 q10 ∷
   re 84 5 (CS03 ∷ []) ∷
   rw 85 q25 ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q9 ∷
   rw⁻ 88 q5 ∷
   rw 89 q10 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q9 ∷
   rw⁻ 89 q5 ∷
   rw 90 q10 ∷
   re 87 5 (CS03 ∷ []) ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q9 ∷
   rw⁻ 90 q6 ∷
   rw 91 q10 ∷
   re 88 5 (CK30 ∷ []) ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q9 ∷
   rw⁻ 91 q5 ∷
   rw 92 q10 ∷
   re 89 5 (CS03 ∷ []) ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q9 ∷
   rw⁻ 92 q6 ∷
   rw 93 q10 ∷
   re 90 5 (CK30 ∷ []) ∷
   re 92 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 91 q9 ∷
   rw⁻ 93 q6 ∷
   rw 94 q10 ∷
   re 91 5 (CK30 ∷ []) ∷
   rw 92 q12 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CK30 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CX31 ∷ []) ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw 24 q1 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q6 ∷
   rw⁻ 28 q6 ∷
   re 30 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 29 q26 ∷
   rw 30 q27 ∷
   rw 33 q1 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 32 q28 ∷
   rw 35 q1 ∷
   re 33 3 (CX13 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   rw 35 q26 ∷
   rw⁻ 36 q29 ∷
   rw 29 q30 ∷
   re 29 8 (Toff213 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CK30 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 36 q31 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 44 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   rw 44 q32 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   rw 54 q31 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q3 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q3 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q3 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q3 ∷
   re 62 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 61 q26 ∷
   rw 62 q27 ∷
   rw 65 q1 ∷
   re 63 3 (CX13 ∷ []) ∷
   rw 64 q28 ∷
   rw 67 q1 ∷
   re 65 3 (CX13 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q3 ∷
   rw 67 q26 ∷
   rw⁻ 68 q29 ∷
   rw 61 q30 ∷
   re 61 8 (Toff213 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CK30 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CK30 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q31 ∷
   re 70 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 69 q3 ∷
   rw 70 q32 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   rw 72 q32 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   re 77 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   rw 77 q32 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   rw 84 q31 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   re 88 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q3 ∷
   re 90 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 90 q3 ∷
   rw 91 q3 ∷ []) Eq.refl
