{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D666 (W : Ws) where

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
  q2 = eqn (CX21 ∷ Sw12 ∷ []) (Sw12 ∷ CX12 ∷ []) (wn 478 W)
  q3 : Eqn
  q3 = eqn (S1 ∷ Sw12 ∷ []) (Sw12 ∷ S2 ∷ []) (wn 479 W)
  q4 : Eqn
  q4 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q5 : Eqn
  q5 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q7 : Eqn
  q7 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q8 : Eqn
  q8 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) (lem-hyb-sym-23)
  q9 : Eqn
  q9 = eqn (Sw12 ∷ CX13 ∷ []) (CX23 ∷ Sw12 ∷ []) (wn 157 W)
  q10 : Eqn
  q10 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q11 : Eqn
  q11 = eqn (Sw12 ∷ S3 ∷ []) (S3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (S))
  q12 : Eqn
  q12 = eqn (Sw12 ∷ S1 ∷ []) (S2 ∷ Sw12 ∷ []) (wn 338 W)
  q13 : Eqn
  q13 = eqn (Sw12 ∷ S2 ∷ []) (S1 ∷ Sw12 ∷ []) (wn 343 W)
  q14 : Eqn
  q14 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q15 : Eqn
  q15 = eqn (Sw23 ∷ CX23 ∷ []) (CX32 ∷ Sw23 ∷ []) (wn 378 W)
  q16 : Eqn
  q16 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q17 : Eqn
  q17 = eqn (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) (wn 372 W)

-- hyb sym 23 @1320 part1: 500 steps
lem-hyb-sym-23-at1320-part1 : ⟪ (Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Sw01 ∷ Sw12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) ⟫ʷ
lem-hyb-sym-23-at1320-part1 = derive (Sw01 ∷ Sw12 ∷ Sw23 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK30 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ Sw12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ []) (Sw01 ∷ Sw12 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK10 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX23 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S1 ∷ CK10 ∷ Sw23 ∷ Sw12 ∷ Sw01 ∷ [])
  (rw 45 q1 ∷
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
   rw 36 q2 ∷
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
   re 31 3 (CS02 ∷ []) ∷
   rw 29 q1 ∷
   re 30 3 (CK20 ∷ []) ∷
   rw 28 q3 ∷
   rw 27 q1 ∷
   re 28 3 (CS02 ∷ []) ∷
   rw 26 q1 ∷
   re 27 3 (CS02 ∷ []) ∷
   rw 25 q1 ∷
   re 26 3 (CS02 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 24 q6 ∷
   re 25 5 (CK30 ∷ []) ∷
   rw 23 q1 ∷
   re 24 3 (CS02 ∷ []) ∷
   rw 22 q1 ∷
   re 23 3 (CK20 ∷ []) ∷
   rw 21 q1 ∷
   re 22 3 (CS02 ∷ []) ∷
   rw 20 q1 ∷
   re 21 3 (CS02 ∷ []) ∷
   rw 19 q2 ∷
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
   rw 13 q1 ∷
   re 14 3 (CS02 ∷ []) ∷
   rw 12 q3 ∷
   rw 11 q1 ∷
   re 12 3 (CK20 ∷ []) ∷
   rw 10 q1 ∷
   re 11 3 (CS02 ∷ []) ∷
   rw 9 q1 ∷
   re 10 3 (CS02 ∷ []) ∷
   rw 8 q1 ∷
   re 9 3 (CS02 ∷ []) ∷
   rw 7 q2 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q7 ∷
   re 5 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 7 q7 ∷
   re 4 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q7 ∷
   re 3 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q7 ∷
   rw 4 q8 ∷
   rw 5 q1 ∷
   re 3 3 (CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CK20 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS02 ∷ []) ∷
   rw 7 q9 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw⁻ 10 q10 ∷
   rw 11 q6 ∷
   re 8 5 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw⁻ 11 q10 ∷
   rw 12 q6 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw⁻ 12 q10 ∷
   rw 13 q6 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   re 11 5 (CK30 ∷ []) ∷
   rw 12 q11 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   rw⁻ 15 q10 ∷
   rw 16 q6 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   rw⁻ 16 q10 ∷
   rw 17 q6 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   rw⁻ 17 q10 ∷
   rw 18 q6 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw⁻ 18 q10 ∷
   rw 19 q6 ∷
   re 16 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   rw⁻ 19 q10 ∷
   rw 20 q6 ∷
   re 17 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw⁻ 20 q10 ∷
   rw 21 q6 ∷
   re 18 5 (CS03 ∷ []) ∷
   rw 19 q9 ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   rw⁻ 22 q10 ∷
   rw 23 q6 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   rw⁻ 23 q10 ∷
   rw 24 q6 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   rw⁻ 24 q5 ∷
   rw 25 q6 ∷
   re 22 5 (CK30 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   rw⁻ 25 q10 ∷
   rw 26 q6 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 25 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 24 q7 ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   rw⁻ 27 q10 ∷
   rw 28 q6 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   rw⁻ 28 q10 ∷
   rw 29 q6 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   rw⁻ 29 q10 ∷
   rw 30 q6 ∷
   re 27 5 (CS03 ∷ []) ∷
   rw 28 q11 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   rw⁻ 31 q5 ∷
   rw 32 q6 ∷
   re 29 5 (CK30 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   rw⁻ 32 q10 ∷
   rw 33 q6 ∷
   re 30 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q4 ∷
   rw⁻ 33 q10 ∷
   rw 34 q6 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q4 ∷
   rw⁻ 34 q10 ∷
   rw 35 q6 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q4 ∷
   rw⁻ 35 q10 ∷
   rw 36 q6 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q4 ∷
   rw⁻ 36 q10 ∷
   rw 37 q6 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q4 ∷
   rw⁻ 37 q10 ∷
   rw 38 q6 ∷
   re 35 5 (CS03 ∷ []) ∷
   rw 36 q9 ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q4 ∷
   rw⁻ 39 q10 ∷
   rw 40 q6 ∷
   re 37 5 (CS03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q4 ∷
   rw⁻ 40 q10 ∷
   rw 41 q6 ∷
   re 38 5 (CS03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q4 ∷
   rw⁻ 41 q10 ∷
   rw 42 q6 ∷
   re 39 5 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q4 ∷
   rw⁻ 42 q10 ∷
   rw 43 q6 ∷
   re 40 5 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q4 ∷
   rw⁻ 43 q10 ∷
   rw 44 q6 ∷
   re 41 5 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q4 ∷
   rw⁻ 44 q10 ∷
   rw 45 q6 ∷
   re 42 5 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q4 ∷
   rw⁻ 45 q10 ∷
   rw 46 q6 ∷
   re 43 5 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q4 ∷
   rw⁻ 46 q10 ∷
   rw 47 q6 ∷
   re 44 5 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q4 ∷
   rw⁻ 47 q10 ∷
   rw 48 q6 ∷
   re 45 5 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q4 ∷
   rw⁻ 48 q10 ∷
   rw 49 q6 ∷
   re 46 5 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q4 ∷
   rw⁻ 49 q10 ∷
   rw 50 q6 ∷
   re 47 5 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 48 q4 ∷
   rw⁻ 50 q10 ∷
   rw 51 q6 ∷
   re 48 5 (CS03 ∷ []) ∷
   re 50 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q4 ∷
   rw⁻ 51 q10 ∷
   rw 52 q6 ∷
   re 49 5 (CS03 ∷ []) ∷
   re 51 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q4 ∷
   rw⁻ 52 q10 ∷
   rw 53 q6 ∷
   re 50 5 (CS03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q4 ∷
   rw⁻ 53 q10 ∷
   rw 54 q6 ∷
   re 51 5 (CS03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q4 ∷
   rw⁻ 54 q10 ∷
   rw 55 q6 ∷
   re 52 5 (CS03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q4 ∷
   rw⁻ 55 q10 ∷
   rw 56 q6 ∷
   re 53 5 (CS03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q4 ∷
   rw⁻ 56 q10 ∷
   rw 57 q6 ∷
   re 54 5 (CS03 ∷ []) ∷
   rw 55 q11 ∷
   rw 56 q11 ∷
   rw 57 q11 ∷
   rw 58 q11 ∷
   re 60 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q4 ∷
   rw⁻ 61 q5 ∷
   rw 62 q6 ∷
   re 59 5 (CK30 ∷ []) ∷
   re 61 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q4 ∷
   rw⁻ 62 q10 ∷
   rw 63 q6 ∷
   re 60 5 (CS03 ∷ []) ∷
   re 62 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q4 ∷
   rw⁻ 63 q10 ∷
   rw 64 q6 ∷
   re 61 5 (CS03 ∷ []) ∷
   re 63 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q4 ∷
   rw⁻ 64 q10 ∷
   rw 65 q6 ∷
   re 62 5 (CS03 ∷ []) ∷
   re 64 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q4 ∷
   rw⁻ 65 q10 ∷
   rw 66 q6 ∷
   re 63 5 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 64 q4 ∷
   rw⁻ 66 q10 ∷
   rw 67 q6 ∷
   re 64 5 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 65 q4 ∷
   rw⁻ 67 q10 ∷
   rw 68 q6 ∷
   re 65 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 66 q4 ∷
   rw⁻ 68 q10 ∷
   rw 69 q6 ∷
   re 66 5 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 67 q4 ∷
   rw⁻ 69 q10 ∷
   rw 70 q6 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   rw⁻ 70 q10 ∷
   rw 71 q6 ∷
   re 68 5 (CS03 ∷ []) ∷
   rw 69 q9 ∷
   rw 72 q1 ∷
   re 70 3 (CS02 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CS02 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS02 ∷ []) ∷
   rw 73 q12 ∷
   rw 76 q1 ∷
   re 74 3 (CK20 ∷ []) ∷
   rw 77 q1 ∷
   re 75 3 (CS02 ∷ []) ∷
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
   rw 81 q13 ∷
   re 83 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 82 q7 ∷
   rw 83 q7 ∷
   rw 4 q14 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q14 ∷
   re 4 3 (CK30 ∷ []) ∷
   rw 7 q14 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q15 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q16 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   re 11 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q16 ∷
   rw 11 q17 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q16 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q16 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q16 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q16 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q16 ∷
   rw 18 q15 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q16 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q16 ∷
   re 22 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 21 q16 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q16 ∷
   rw⁻ 23 q5 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q16 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q16 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q16 ∷
   rw 27 q17 ∷
   re 29 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q16 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q16 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q16 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q16 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q16 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q16 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q16 ∷
   rw 35 q15 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q16 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q16 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q16 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q16 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q16 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q16 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q16 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q16 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q16 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q16 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q16 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q16 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q16 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q16 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q16 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q16 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q16 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q16 ∷
   rw 54 q17 ∷
   rw 55 q17 ∷
   rw 56 q17 ∷
   rw 57 q17 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q16 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q16 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q16 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q16 ∷ []) Eq.refl
