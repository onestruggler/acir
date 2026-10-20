{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D178 (W : Ws) where

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
  q1 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q2 : Eqn
  q2 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wn 479 W)
  q3 : Eqn
  q3 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q4 : Eqn
  q4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q6 : Eqn
  q6 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q8 : Eqn
  q8 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q9 : Eqn
  q9 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q10 : Eqn
  q10 = eqn (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) (wn 477 W)
  q11 : Eqn
  q11 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q12 : Eqn
  q12 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wn 476 W)
  q13 : Eqn
  q13 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q14 : Eqn
  q14 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q15 : Eqn
  q15 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q16 : Eqn
  q16 = eqn (CX21 ∷ Sw12 ∷ []) (Sw12 ∷ CX12 ∷ []) (wn 478 W)
  q17 : Eqn
  q17 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q18 : Eqn
  q18 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q19 : Eqn
  q19 = eqn (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) (wn 343 W)

-- AXIOM LF @0321 part0: 500 steps
lem-AXIOM-LF-at0321-part0 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ []) ⟫ʷ ≈ ⟪ (Sw12 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ
lem-AXIOM-LF-at0321-part0 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S1 ∷ CK10 ∷ []) (Sw12 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ Sw12 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ [])
  (rw 80 q1 ∷
   rw 79 q1 ∷
   re 80 3 (CK20 ∷ []) ∷
   rw 78 q2 ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   rw 79 q4 ∷
   rw 77 q5 ∷
   re 78 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   rw 78 q4 ∷
   rw 76 q5 ∷
   re 77 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   rw 77 q4 ∷
   rw 75 q5 ∷
   re 76 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   rw 74 q5 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   rw 73 q5 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   rw 72 q5 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   rw 73 q6 ∷
   rw 71 q5 ∷
   re 72 5 (CK30 ∷ []) ∷
   rw⁻ 70 q7 ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   rw 69 q5 ∷
   re 70 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   rw 68 q5 ∷
   re 69 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   rw 67 q5 ∷
   re 68 5 (CS03 ∷ []) ∷
   rw 66 q8 ∷
   re 65 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 67 q9 ∷
   re 64 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 66 q9 ∷
   re 63 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 65 q9 ∷
   re 62 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 64 q9 ∷
   re 61 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 63 q9 ∷
   re 60 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 62 q9 ∷
   re 59 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 61 q9 ∷
   re 58 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 60 q9 ∷
   re 57 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 59 q9 ∷
   re 56 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 58 q9 ∷
   rw 55 q10 ∷
   rw 54 q10 ∷
   rw 53 q10 ∷
   rw 52 q10 ∷
   re 51 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 53 q9 ∷
   re 50 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 52 q9 ∷
   re 49 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 51 q9 ∷
   re 48 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 50 q9 ∷
   re 47 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 49 q9 ∷
   re 46 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 48 q9 ∷
   re 45 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 47 q9 ∷
   re 44 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 46 q9 ∷
   re 43 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 45 q9 ∷
   re 42 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 44 q9 ∷
   re 41 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 43 q9 ∷
   re 40 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 42 q9 ∷
   re 39 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 41 q9 ∷
   re 38 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 40 q9 ∷
   re 37 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 39 q9 ∷
   re 36 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 38 q9 ∷
   re 35 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 37 q9 ∷
   re 34 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 36 q9 ∷
   rw 33 q8 ∷
   re 32 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 34 q9 ∷
   re 31 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 33 q9 ∷
   re 30 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 32 q9 ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 31 q9 ∷
   re 28 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 30 q9 ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 29 q9 ∷
   re 26 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 28 q9 ∷
   rw 25 q10 ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q9 ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q9 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 24 q9 ∷
   rw 21 q1 ∷
   re 22 3 (CK20 ∷ []) ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q9 ∷
   re 19 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 21 q9 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q9 ∷
   re 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q9 ∷
   rw 16 q8 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q9 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q9 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q9 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q9 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q9 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q9 ∷
   rw 9 q10 ∷
   re 8 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 10 q9 ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q9 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q9 ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q9 ∷
   rw 4 q8 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 5 q4 ∷
   rw 3 q5 ∷
   re 4 5 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 4 q6 ∷
   rw 2 q5 ∷
   re 3 5 (CK30 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 1 q5 ∷
   re 2 5 (CS03 ∷ []) ∷
   re 0 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   rw 0 q5 ∷
   re 1 5 (CS03 ∷ []) ∷
   rw 81 q11 ∷
   rw 80 q11 ∷
   re 81 3 (CK30 ∷ []) ∷
   rw 79 q12 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q13 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q13 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q13 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q13 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q13 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q13 ∷
   re 72 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 74 q13 ∷
   rw 71 q14 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q13 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q13 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q13 ∷
   re 67 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 69 q13 ∷
   rw 66 q4 ∷
   rw 65 q4 ∷
   rw 64 q4 ∷
   rw 63 q4 ∷
   rw 62 q4 ∷
   rw 61 q4 ∷
   rw 60 q4 ∷
   rw 59 q4 ∷
   rw 58 q4 ∷
   rw 57 q6 ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q4 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q4 ∷
   rw 39 q4 ∷
   rw 38 q4 ∷
   rw 37 q4 ∷
   rw 36 q4 ∷
   rw 35 q4 ∷
   re 34 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 36 q13 ∷
   rw 33 q4 ∷
   rw 32 q4 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q6 ∷
   rw 26 q15 ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q11 ∷
   re 23 3 (CK30 ∷ []) ∷
   rw 21 q4 ∷
   rw 20 q6 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q13 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw 14 q4 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q15 ∷
   rw 9 q6 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q13 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q13 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q13 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q13 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q13 ∷
   rw 82 q1 ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   rw 83 q6 ∷
   rw 81 q5 ∷
   re 82 5 (CK30 ∷ []) ∷
   rw⁻ 80 q7 ∷
   re 79 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 81 q9 ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q9 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q9 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q9 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q9 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q9 ∷
   re 73 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 75 q9 ∷
   rw 72 q10 ∷
   re 71 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 73 q9 ∷
   re 70 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 72 q9 ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q9 ∷
   rw 68 q16 ∷
   rw 67 q1 ∷
   re 68 3 (CS02 ∷ []) ∷
   rw 66 q1 ∷
   re 67 3 (CS02 ∷ []) ∷
   rw 65 q1 ∷
   re 66 3 (CS02 ∷ []) ∷
   rw 64 q1 ∷
   re 65 3 (CS02 ∷ []) ∷
   rw 63 q1 ∷
   re 64 3 (CS02 ∷ []) ∷
   rw 62 q1 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 61 q1 ∷
   re 62 3 (CS02 ∷ []) ∷
   rw 60 q1 ∷
   re 61 3 (CS02 ∷ []) ∷
   rw 59 q1 ∷
   re 60 3 (CS02 ∷ []) ∷
   rw 58 q1 ∷
   re 59 3 (CK20 ∷ []) ∷
   rw 57 q2 ∷
   rw 56 q2 ∷
   rw 55 q2 ∷
   rw 54 q2 ∷
   rw 53 q1 ∷
   re 54 3 (CS02 ∷ []) ∷
   rw 52 q1 ∷
   re 53 3 (CS02 ∷ []) ∷
   rw 51 q1 ∷
   re 52 3 (CS02 ∷ []) ∷
   rw 50 q1 ∷
   re 51 3 (CS02 ∷ []) ∷
   rw 49 q1 ∷
   re 50 3 (CS02 ∷ []) ∷
   rw 48 q1 ∷
   re 49 3 (CS02 ∷ []) ∷
   rw 47 q1 ∷
   re 48 3 (CS02 ∷ []) ∷
   rw 46 q1 ∷
   re 47 3 (CS02 ∷ []) ∷
   rw 45 q1 ∷
   re 46 3 (CS02 ∷ []) ∷
   rw 44 q1 ∷
   re 45 3 (CS02 ∷ []) ∷
   rw 43 q1 ∷
   re 44 3 (CS02 ∷ []) ∷
   rw 42 q1 ∷
   re 43 3 (CS02 ∷ []) ∷
   rw 41 q1 ∷
   re 42 3 (CS02 ∷ []) ∷
   rw 40 q1 ∷
   re 41 3 (CS02 ∷ []) ∷
   rw 39 q1 ∷
   re 40 3 (CS02 ∷ []) ∷
   rw 38 q1 ∷
   re 39 3 (CS02 ∷ []) ∷
   rw 37 q1 ∷
   re 38 3 (CS02 ∷ []) ∷
   rw 36 q1 ∷
   re 37 3 (CS02 ∷ []) ∷
   rw 35 q16 ∷
   rw 34 q1 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 33 q1 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 32 q1 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 31 q1 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 30 q1 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 29 q1 ∷
   re 30 3 (CS02 ∷ []) ∷
   rw 28 q1 ∷
   re 29 3 (CK20 ∷ []) ∷
   rw 27 q2 ∷
   rw 26 q1 ∷
   re 27 3 (CS02 ∷ []) ∷
   rw 25 q1 ∷
   re 26 3 (CS02 ∷ []) ∷
   rw 24 q1 ∷
   re 25 3 (CS02 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   rw 25 q6 ∷
   rw 23 q5 ∷
   re 24 5 (CK30 ∷ []) ∷
   rw 22 q1 ∷
   re 23 3 (CS02 ∷ []) ∷
   rw 21 q1 ∷
   re 22 3 (CK20 ∷ []) ∷
   rw 20 q1 ∷
   re 21 3 (CS02 ∷ []) ∷
   rw 19 q1 ∷
   re 20 3 (CS02 ∷ []) ∷
   rw 18 q16 ∷
   rw 17 q1 ∷
   re 18 3 (CS02 ∷ []) ∷
   rw 16 q1 ∷
   re 17 3 (CS02 ∷ []) ∷
   rw 15 q1 ∷
   re 16 3 (CS02 ∷ []) ∷
   rw 14 q1 ∷
   re 15 3 (CS02 ∷ []) ∷
   rw 13 q1 ∷
   re 14 3 (CS02 ∷ []) ∷
   rw 12 q1 ∷
   re 13 3 (CS02 ∷ []) ∷
   rw 11 q2 ∷
   rw 10 q1 ∷
   re 11 3 (CK20 ∷ []) ∷
   rw 9 q1 ∷
   re 10 3 (CS02 ∷ []) ∷
   rw 8 q1 ∷
   re 9 3 (CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 8 3 (CS02 ∷ []) ∷
   rw 6 q16 ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q9 ∷
   re 4 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 6 q9 ∷
   re 3 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q9 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 4 q9 ∷
   rw 3 q17 ∷
   rw 4 q1 ∷
   re 2 3 (CS02 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CK20 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS02 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CK20 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CK20 ∷ []) ∷
   rw 8 q18 ∷
   re 10 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q19 ∷
   re 12 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 11 q9 ∷
   rw 12 q19 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q9 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 14 q9 ∷
   re 16 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q9 ∷
   re 17 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 16 q9 ∷
   rw 17 q19 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q9 ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q9 ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q9 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q9 ∷
   re 23 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 22 q9 ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q9 ∷
   rw 24 q18 ∷
   re 26 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 25 q9 ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q9 ∷
   re 28 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 27 q9 ∷
   re 29 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 28 q9 ∷
   re 30 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 29 q9 ∷
   re 31 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷ []) Eq.refl
