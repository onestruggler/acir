{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D211 (W : Ws) where

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
  q2 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q3 : Eqn
  q3 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q5 : Eqn
  q5 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q6 : Eqn
  q6 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q7 : Eqn
  q7 = eqn (S2 ∷ Sw12 ∷ []) (Sw12 ∷ S1 ∷ []) (wn 477 W)
  q8 : Eqn
  q8 = eqn (CX21 ∷ Sw12 ∷ []) (Sw12 ∷ CX12 ∷ []) (wn 478 W)
  q9 : Eqn
  q9 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wn 479 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q12 : Eqn
  q12 = eqn (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) (wn 343 W)
  q13 : Eqn
  q13 = eqn (Sw12 ∷ K3 ∷ []) (K3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (K))
  q14 : Eqn
  q14 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q17 : Eqn
  q17 = eqn (Sw12 ∷ ι1 ∷ []) (ι2 ∷ Sw12 ∷ []) (wn 364 W)
  q18 : Eqn
  q18 = eqn (K3 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K3 ∷ ι2 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wn 369 W)
  q19 : Eqn
  q19 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q20 : Eqn
  q20 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))

-- AXIOM LF @0213: 464 steps
lem-AXIOM-LF-at0213 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff312 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-AXIOM-LF-at0213 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ []) (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ Toff312 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ Toff312 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 80 q1 ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   rw 81 q3 ∷
   rw 79 q4 ∷
   re 80 5 (CK30 ∷ []) ∷
   rw⁻ 78 q5 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q6 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q6 ∷
   re 75 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 77 q6 ∷
   re 74 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 76 q6 ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q6 ∷
   re 72 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 74 q6 ∷
   re 71 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 73 q6 ∷
   rw 70 q7 ∷
   re 69 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 71 q6 ∷
   re 68 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 70 q6 ∷
   re 67 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 69 q6 ∷
   rw 66 q8 ∷
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
   re 59 3 (CS02 ∷ []) ∷
   rw 57 q1 ∷
   re 58 3 (CS02 ∷ []) ∷
   rw 56 q1 ∷
   re 57 3 (CK20 ∷ []) ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
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
   rw 35 q1 ∷
   re 36 3 (CS02 ∷ []) ∷
   rw 34 q1 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 33 q8 ∷
   rw 32 q1 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 31 q1 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 30 q1 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 29 q1 ∷
   re 30 3 (CS02 ∷ []) ∷
   rw 28 q1 ∷
   re 29 3 (CS02 ∷ []) ∷
   rw 27 q1 ∷
   re 28 3 (CS02 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CK20 ∷ []) ∷
   rw 25 q9 ∷
   rw 24 q1 ∷
   re 25 3 (CS02 ∷ []) ∷
   rw 23 q1 ∷
   re 24 3 (CS02 ∷ []) ∷
   rw 22 q1 ∷
   re 23 3 (CS02 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   rw 21 q4 ∷
   re 22 5 (CK30 ∷ []) ∷
   rw 20 q1 ∷
   re 21 3 (CS02 ∷ []) ∷
   rw 19 q1 ∷
   re 20 3 (CK20 ∷ []) ∷
   rw 18 q1 ∷
   re 19 3 (CS02 ∷ []) ∷
   rw 17 q1 ∷
   re 18 3 (CS02 ∷ []) ∷
   rw 16 q8 ∷
   rw 15 q1 ∷
   re 16 3 (CS02 ∷ []) ∷
   rw 14 q1 ∷
   re 15 3 (CS02 ∷ []) ∷
   rw 13 q1 ∷
   re 14 3 (CS02 ∷ []) ∷
   rw 12 q1 ∷
   re 13 3 (CS02 ∷ []) ∷
   rw 11 q1 ∷
   re 12 3 (CS02 ∷ []) ∷
   rw 10 q1 ∷
   re 11 3 (CS02 ∷ []) ∷
   rw 9 q9 ∷
   rw 8 q1 ∷
   re 9 3 (CK20 ∷ []) ∷
   rw 7 q1 ∷
   re 8 3 (CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 7 3 (CS02 ∷ []) ∷
   rw 5 q1 ∷
   re 6 3 (CS02 ∷ []) ∷
   rw 4 q8 ∷
   re 3 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q6 ∷
   re 2 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 4 q6 ∷
   re 1 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 3 q6 ∷
   re 0 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q10 ∷
   rw 2 q1 ∷
   re 0 3 (CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CK20 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CK20 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK20 ∷ []) ∷
   rw 6 q11 ∷
   re 8 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q12 ∷
   re 10 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q12 ∷
   re 12 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q6 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q6 ∷
   re 14 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q6 ∷
   re 15 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 14 q6 ∷
   rw 15 q12 ∷
   re 17 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 16 q6 ∷
   re 18 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q6 ∷
   re 19 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 18 q6 ∷
   re 20 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 19 q6 ∷
   re 21 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 20 q6 ∷
   re 22 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 21 q6 ∷
   rw 22 q11 ∷
   re 24 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 23 q6 ∷
   re 25 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 24 q6 ∷
   re 26 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 25 q6 ∷
   re 27 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 26 q6 ∷
   re 28 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 27 q6 ∷
   re 29 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 28 q6 ∷
   re 30 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 29 q13 ∷
   rw 30 q14 ∷
   rw 31 q11 ∷
   rw 32 q15 ∷
   rw 33 q11 ∷
   rw 34 q16 ∷
   rw 35 q13 ∷
   rw 36 q17 ∷
   rw 29 q18 ∷
   re 29 8 (Toff312 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS02 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS02 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CK20 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 36 q19 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw⁻ 39 q20 ∷
   rw 40 q4 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   rw⁻ 40 q20 ∷
   rw 41 q4 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw⁻ 41 q20 ∷
   rw 42 q4 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   rw⁻ 42 q20 ∷
   rw 43 q4 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw⁻ 43 q20 ∷
   rw 44 q4 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw⁻ 44 q20 ∷
   rw 45 q4 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw⁻ 45 q3 ∷
   rw 46 q4 ∷
   re 43 5 (CK30 ∷ []) ∷
   rw 44 q5 ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   rw⁻ 47 q20 ∷
   rw 48 q4 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw⁻ 48 q20 ∷
   rw 49 q4 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw⁻ 49 q20 ∷
   rw 50 q4 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   rw⁻ 50 q20 ∷
   rw 51 q4 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   rw⁻ 51 q20 ∷
   rw 52 q4 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   rw⁻ 52 q20 ∷
   rw 53 q4 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   rw⁻ 53 q20 ∷
   rw 54 q4 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   rw⁻ 54 q20 ∷
   rw 55 q4 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   rw⁻ 55 q20 ∷
   rw 56 q4 ∷
   re 53 5 (CS03 ∷ []) ∷
   rw 54 q19 ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   rw⁻ 57 q20 ∷
   rw 58 q4 ∷
   re 55 5 (CS03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   rw⁻ 58 q20 ∷
   rw 59 q4 ∷
   re 56 5 (CS03 ∷ []) ∷
   re 58 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   rw⁻ 59 q20 ∷
   rw 60 q4 ∷
   re 57 5 (CS03 ∷ []) ∷
   re 59 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   rw⁻ 60 q3 ∷
   rw 61 q4 ∷
   re 58 5 (CK30 ∷ []) ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   rw⁻ 61 q20 ∷
   rw 62 q4 ∷
   re 59 5 (CS03 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   rw⁻ 62 q20 ∷
   rw 63 q4 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 62 1 (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) ∷
   rw 61 q13 ∷
   rw 62 q14 ∷
   rw 63 q11 ∷
   rw 64 q15 ∷
   rw 65 q11 ∷
   rw 66 q16 ∷
   rw 67 q13 ∷
   rw 68 q17 ∷
   rw 61 q18 ∷
   re 61 8 (Toff312 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS02 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS02 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CK20 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CS02 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CK20 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CK20 ∷ []) ∷
   rw 68 q19 ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   rw⁻ 71 q3 ∷
   rw 72 q4 ∷
   re 69 5 (CK30 ∷ []) ∷
   rw 70 q5 ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q2 ∷
   rw⁻ 73 q3 ∷
   rw 74 q4 ∷
   re 71 5 (CK30 ∷ []) ∷
   rw 72 q5 ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q2 ∷
   rw⁻ 75 q20 ∷
   rw 76 q4 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 74 q2 ∷
   rw⁻ 76 q20 ∷
   rw 77 q4 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 76 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q2 ∷
   rw⁻ 77 q20 ∷
   rw 78 q4 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 77 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q2 ∷
   rw⁻ 78 q3 ∷
   rw 79 q4 ∷
   re 76 5 (CK30 ∷ []) ∷
   rw 77 q5 ∷
   re 79 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q2 ∷
   rw⁻ 80 q20 ∷
   rw 81 q4 ∷
   re 78 5 (CS03 ∷ []) ∷
   re 80 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q2 ∷
   rw⁻ 81 q20 ∷
   rw 82 q4 ∷
   re 79 5 (CS03 ∷ []) ∷
   re 81 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q2 ∷
   rw⁻ 82 q20 ∷
   rw 83 q4 ∷
   re 80 5 (CS03 ∷ []) ∷
   re 82 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 81 q2 ∷
   rw⁻ 83 q20 ∷
   rw 84 q4 ∷
   re 81 5 (CS03 ∷ []) ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 82 q2 ∷
   rw⁻ 84 q20 ∷
   rw 85 q4 ∷
   re 82 5 (CS03 ∷ []) ∷
   re 84 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 83 q2 ∷
   rw⁻ 85 q20 ∷
   rw 86 q4 ∷
   re 83 5 (CS03 ∷ []) ∷
   rw 84 q19 ∷
   re 86 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 85 q2 ∷
   rw⁻ 87 q20 ∷
   rw 88 q4 ∷
   re 85 5 (CS03 ∷ []) ∷
   re 87 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   rw⁻ 88 q20 ∷
   rw 89 q4 ∷
   re 86 5 (CS03 ∷ []) ∷
   re 88 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 87 q2 ∷
   rw⁻ 89 q3 ∷
   rw 90 q4 ∷
   re 87 5 (CK30 ∷ []) ∷
   re 89 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 88 q2 ∷
   rw⁻ 90 q20 ∷
   rw 91 q4 ∷
   re 88 5 (CS03 ∷ []) ∷
   re 90 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 89 q2 ∷
   rw⁻ 91 q3 ∷
   rw 92 q4 ∷
   re 89 5 (CK30 ∷ []) ∷
   re 91 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 90 q2 ∷
   rw⁻ 92 q3 ∷
   rw 93 q4 ∷
   re 90 5 (CK30 ∷ []) ∷
   rw 91 q6 ∷ []) Eq.refl
