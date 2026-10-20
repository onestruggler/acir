{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D672 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D643 W using (lem-hyb-sym-23)

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
  q10 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) (lem-hyb-sym-23)
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q12 : Eqn
  q12 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q13 : Eqn
  q13 = eqn (Sw12 ∷ S1 ∷ []) (S2 ∷ Sw12 ∷ []) (wn 338 W)
  q14 : Eqn
  q14 = eqn (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) (wn 343 W)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (Sw23 ∷ CX23 ∷ []) (CX32 ∷ Sw23 ∷ []) (wn 378 W)
  q17 : Eqn
  q17 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q18 : Eqn
  q18 = eqn (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) (wn 372 W)

-- hyb sym 23 @2310 part1: 500 steps
lem-hyb-sym-23-at2310-part1 : ⟪ (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw12 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ Sw23 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ
lem-hyb-sym-23-at2310-part1 = derive (Sw01 ∷ Sw12 ∷ Sw01 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S3 ∷ CK30 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ Sw01 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ Sw23 ∷ CK10 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ Sw23 ∷ Sw01 ∷ Sw12 ∷ Sw01 ∷ [])
  (rw 84 q1 ∷
   re 83 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 86 q2 ∷
   rw 85 q3 ∷
   rw 83 q4 ∷
   re 84 5 (CK30 ∷ []) ∷
   rw⁻ 82 q5 ∷
   re 81 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 83 q6 ∷
   re 80 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 82 q6 ∷
   re 79 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 81 q6 ∷
   re 78 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 80 q6 ∷
   re 77 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 79 q6 ∷
   re 76 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 78 q6 ∷
   re 75 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 77 q6 ∷
   rw 74 q7 ∷
   re 73 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 75 q6 ∷
   re 72 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 74 q6 ∷
   re 71 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 73 q6 ∷
   rw 70 q8 ∷
   rw 69 q1 ∷
   re 70 3 (CS02 ∷ []) ∷
   rw 68 q1 ∷
   re 69 3 (CS02 ∷ []) ∷
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
   re 61 3 (CK20 ∷ []) ∷
   rw 59 q9 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q9 ∷
   rw 55 q1 ∷
   re 56 3 (CS02 ∷ []) ∷
   rw 54 q1 ∷
   re 55 3 (CS02 ∷ []) ∷
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
   rw 37 q8 ∷
   rw 36 q1 ∷
   re 37 3 (CS02 ∷ []) ∷
   rw 35 q1 ∷
   re 36 3 (CS02 ∷ []) ∷
   rw 34 q1 ∷
   re 35 3 (CS02 ∷ []) ∷
   rw 33 q1 ∷
   re 34 3 (CS02 ∷ []) ∷
   rw 32 q1 ∷
   re 33 3 (CS02 ∷ []) ∷
   rw 31 q1 ∷
   re 32 3 (CS02 ∷ []) ∷
   rw 30 q1 ∷
   re 31 3 (CK20 ∷ []) ∷
   rw 29 q9 ∷
   rw 28 q1 ∷
   re 29 3 (CS02 ∷ []) ∷
   rw 27 q1 ∷
   re 28 3 (CS02 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CS02 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw 25 q4 ∷
   re 26 5 (CK30 ∷ []) ∷
   rw 24 q1 ∷
   re 25 3 (CS02 ∷ []) ∷
   rw 23 q1 ∷
   re 24 3 (CK20 ∷ []) ∷
   rw 22 q1 ∷
   re 23 3 (CS02 ∷ []) ∷
   rw 21 q1 ∷
   re 22 3 (CS02 ∷ []) ∷
   rw 20 q8 ∷
   rw 19 q1 ∷
   re 20 3 (CS02 ∷ []) ∷
   rw 18 q1 ∷
   re 19 3 (CS02 ∷ []) ∷
   rw 17 q1 ∷
   re 18 3 (CS02 ∷ []) ∷
   rw 16 q1 ∷
   re 17 3 (CS02 ∷ []) ∷
   rw 15 q1 ∷
   re 16 3 (CS02 ∷ []) ∷
   rw 14 q1 ∷
   re 15 3 (CS02 ∷ []) ∷
   rw 13 q9 ∷
   rw 12 q1 ∷
   re 13 3 (CK20 ∷ []) ∷
   rw 11 q1 ∷
   re 12 3 (CS02 ∷ []) ∷
   rw 10 q1 ∷
   re 11 3 (CS02 ∷ []) ∷
   rw 9 q1 ∷
   re 10 3 (CS02 ∷ []) ∷
   rw 8 q8 ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q6 ∷
   re 6 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 8 q6 ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q6 ∷
   re 4 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q10 ∷
   rw 6 q1 ∷
   re 4 3 (CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS02 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CK20 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS02 ∷ []) ∷
   rw 8 q11 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw⁻ 11 q12 ∷
   rw 12 q4 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw⁻ 12 q12 ∷
   rw 13 q4 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw⁻ 13 q12 ∷
   rw 14 q4 ∷
   re 11 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw⁻ 14 q3 ∷
   rw 15 q4 ∷
   re 12 5 (CK30 ∷ []) ∷
   rw 13 q5 ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw⁻ 16 q12 ∷
   rw 17 q4 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   rw⁻ 17 q12 ∷
   rw 18 q4 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw⁻ 18 q12 ∷
   rw 19 q4 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw⁻ 19 q12 ∷
   rw 20 q4 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   rw⁻ 20 q12 ∷
   rw 21 q4 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw⁻ 21 q12 ∷
   rw 22 q4 ∷
   re 19 5 (CS03 ∷ []) ∷
   rw 20 q11 ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q2 ∷
   rw⁻ 23 q12 ∷
   rw 24 q4 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   rw⁻ 24 q12 ∷
   rw 25 q4 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw⁻ 25 q3 ∷
   rw 26 q4 ∷
   re 23 5 (CK30 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   rw⁻ 26 q12 ∷
   rw 27 q4 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 26 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 25 q6 ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   rw⁻ 28 q12 ∷
   rw 29 q4 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   rw⁻ 29 q12 ∷
   rw 30 q4 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   rw⁻ 30 q12 ∷
   rw 31 q4 ∷
   re 28 5 (CS03 ∷ []) ∷
   rw 29 q5 ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   rw⁻ 32 q3 ∷
   rw 33 q4 ∷
   re 30 5 (CK30 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   rw⁻ 33 q12 ∷
   rw 34 q4 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   rw⁻ 34 q12 ∷
   rw 35 q4 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   rw⁻ 35 q12 ∷
   rw 36 q4 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   rw⁻ 36 q12 ∷
   rw 37 q4 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw⁻ 37 q12 ∷
   rw 38 q4 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw⁻ 38 q12 ∷
   rw 39 q4 ∷
   re 36 5 (CS03 ∷ []) ∷
   rw 37 q11 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   rw⁻ 40 q12 ∷
   rw 41 q4 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw⁻ 41 q12 ∷
   rw 42 q4 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   rw⁻ 42 q12 ∷
   rw 43 q4 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw⁻ 43 q12 ∷
   rw 44 q4 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw⁻ 44 q12 ∷
   rw 45 q4 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw⁻ 45 q12 ∷
   rw 46 q4 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   rw⁻ 46 q12 ∷
   rw 47 q4 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   rw⁻ 47 q12 ∷
   rw 48 q4 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw⁻ 48 q12 ∷
   rw 49 q4 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw⁻ 49 q12 ∷
   rw 50 q4 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   rw⁻ 50 q12 ∷
   rw 51 q4 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   rw⁻ 51 q12 ∷
   rw 52 q4 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   rw⁻ 52 q12 ∷
   rw 53 q4 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   rw⁻ 53 q12 ∷
   rw 54 q4 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   rw⁻ 54 q12 ∷
   rw 55 q4 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   rw⁻ 55 q12 ∷
   rw 56 q4 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   rw⁻ 56 q12 ∷
   rw 57 q4 ∷
   re 54 5 (CS03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   rw⁻ 57 q12 ∷
   rw 58 q4 ∷
   re 55 5 (CS03 ∷ []) ∷
   rw 56 q5 ∷
   rw 57 q5 ∷
   rw 58 q5 ∷
   rw 59 q5 ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   rw⁻ 62 q3 ∷
   rw 63 q4 ∷
   re 60 5 (CK30 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   rw⁻ 63 q12 ∷
   rw 64 q4 ∷
   re 61 5 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q2 ∷
   rw⁻ 64 q12 ∷
   rw 65 q4 ∷
   re 62 5 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q2 ∷
   rw⁻ 65 q12 ∷
   rw 66 q4 ∷
   re 63 5 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   rw⁻ 66 q12 ∷
   rw 67 q4 ∷
   re 64 5 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   rw⁻ 67 q12 ∷
   rw 68 q4 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   rw⁻ 68 q12 ∷
   rw 69 q4 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q2 ∷
   rw⁻ 69 q12 ∷
   rw 70 q4 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q2 ∷
   rw⁻ 70 q12 ∷
   rw 71 q4 ∷
   re 68 5 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 69 q2 ∷
   rw⁻ 71 q12 ∷
   rw 72 q4 ∷
   re 69 5 (CS03 ∷ []) ∷
   rw 70 q11 ∷
   rw 73 q1 ∷
   re 71 3 (CS02 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS02 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CS02 ∷ []) ∷
   rw 74 q13 ∷
   rw 77 q1 ∷
   re 75 3 (CK20 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CS02 ∷ []) ∷
   rw 79 q1 ∷
   re 77 3 (CS02 ∷ []) ∷
   rw 80 q1 ∷
   re 78 3 (CS02 ∷ []) ∷
   rw 81 q1 ∷
   re 79 3 (CS02 ∷ []) ∷
   rw 82 q1 ∷
   re 80 3 (CS02 ∷ []) ∷
   rw 83 q1 ∷
   re 81 3 (CS02 ∷ []) ∷
   rw 82 q14 ∷
   re 84 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 83 q6 ∷
   rw 84 q6 ∷
   rw 5 q15 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q15 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q15 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 8 q15 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q16 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q17 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q17 ∷
   re 12 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q17 ∷
   rw 12 q18 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q17 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q17 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q17 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q17 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q17 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q17 ∷
   rw 19 q16 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q17 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q17 ∷
   re 23 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 22 q17 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q17 ∷ []) Eq.refl
