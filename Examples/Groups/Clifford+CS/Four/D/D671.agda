{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD671 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D671 (W : Ws) (Sᴰ : SD671) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-hyb-sym-23 : St 1758
  lem-hyb-sym-23 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 273 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q5 : Eqn
  q5 = wE 216 W
  q6 : Eqn
  q6 = wE 480 W
  q7 : Eqn
  q7 = wE 481 W
  q8 : Eqn
  q8 = wE 74 W
  q9 : Eqn
  q9 = wE 10 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q11 : Eqn
  q11 = sE 1758 lem-hyb-sym-23
  q12 : Eqn
  q12 = wE 219 W
  q13 : Eqn
  q13 = wE 327 W
  q14 : Eqn
  q14 = wE 30 W
  q15 : Eqn
  q15 = wE 25 W
  q16 : Eqn
  q16 = wE 275 W
  q17 : Eqn
  q17 = wE 315 W
  q18 : Eqn
  q18 = wE 31 W

-- hyb sym 23 @1023: 395 steps
lem-hyb-sym-23-at1023 : ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ []) ⟫ʷ
lem-hyb-sym-23-at1023 = derive (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK31 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK21 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX02 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK31 ∷ []) (CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ S3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK21 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX03 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S0 ∷ CK01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK21 ∷ [])
  (rw 80 q1 ∷
   re 79 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 81 q2 ∷
   rw 80 q3 ∷
   rw⁻ 79 q2 ∷
   re 80 3 (CK30 ∷ []) ∷
   rw⁻ 78 q4 ∷
   rw 77 q5 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q5 ∷
   rw 72 q5 ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   rw 69 q5 ∷
   rw 68 q5 ∷
   rw 67 q5 ∷
   rw 66 q8 ∷
   rw 65 q9 ∷
   rw 64 q9 ∷
   rw 63 q9 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q9 ∷
   rw 59 q9 ∷
   rw 58 q9 ∷
   rw 57 q9 ∷
   rw 56 q3 ∷
   rw⁻ 55 q10 ∷
   rw⁻ 54 q10 ∷
   rw⁻ 53 q10 ∷
   rw⁻ 52 q10 ∷
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
   rw 33 q8 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q3 ∷
   rw⁻ 25 q10 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   rw 22 q9 ∷
   re 21 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (CK30 ∷ []) ∷
   rw 20 q9 ∷
   rw 19 q3 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q8 ∷
   rw 15 q9 ∷
   rw 14 q9 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q9 ∷
   rw 10 q9 ∷
   rw⁻ 9 q10 ∷
   rw 8 q3 ∷
   rw 7 q9 ∷
   rw 6 q9 ∷
   rw 5 q9 ∷
   rw 4 q8 ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q11 ∷
   rw 0 q12 ∷
   rw 1 q12 ∷
   rw 2 q13 ∷
   rw 3 q12 ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q14 ∷
   rw 6 q2 ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q15 ∷
   rw 7 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q15 ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q15 ∷
   rw 9 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q16 ∷
   rw 10 q2 ∷
   re 8 3 (CK31 ∷ []) ∷
   rw 9 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q15 ∷
   rw 12 q2 ∷
   re 10 3 (CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 12 q15 ∷
   rw 13 q2 ∷
   re 11 3 (CS13 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 13 q15 ∷
   rw 14 q2 ∷
   re 12 3 (CS13 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 14 q15 ∷
   rw 15 q2 ∷
   re 13 3 (CS13 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q15 ∷
   rw 16 q2 ∷
   re 14 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   rw 16 q15 ∷
   rw 17 q2 ∷
   re 15 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q2 ∷
   rw 17 q14 ∷
   rw 18 q2 ∷
   re 16 3 (CX03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   rw 18 q15 ∷
   rw 19 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   rw 19 q15 ∷
   rw 20 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   rw 20 q16 ∷
   rw 21 q2 ∷
   re 19 3 (CK31 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   rw 21 q15 ∷
   rw 22 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 21 q16 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   rw 23 q15 ∷
   rw 24 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw 24 q15 ∷
   rw 25 q2 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   rw 25 q15 ∷
   rw 26 q2 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 25 q4 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   rw 27 q16 ∷
   rw 28 q2 ∷
   re 26 3 (CK31 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   rw 28 q15 ∷
   rw 29 q2 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   rw 29 q15 ∷
   rw 30 q2 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   rw 30 q15 ∷
   rw 31 q2 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   rw 31 q15 ∷
   rw 32 q2 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   rw 32 q15 ∷
   rw 33 q2 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   rw 33 q15 ∷
   rw 34 q2 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   rw 34 q14 ∷
   rw 35 q2 ∷
   re 33 3 (CX03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   rw 35 q15 ∷
   rw 36 q2 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   rw 36 q15 ∷
   rw 37 q2 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   rw 37 q15 ∷
   rw 38 q2 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   rw 38 q15 ∷
   rw 39 q2 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   rw 39 q15 ∷
   rw 40 q2 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   rw 40 q15 ∷
   rw 41 q2 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   rw 41 q15 ∷
   rw 42 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   rw 42 q15 ∷
   rw 43 q2 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   rw 43 q15 ∷
   rw 44 q2 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   rw 44 q15 ∷
   rw 45 q2 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   rw 45 q15 ∷
   rw 46 q2 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   rw 46 q15 ∷
   rw 47 q2 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   rw 47 q15 ∷
   rw 48 q2 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   rw 48 q15 ∷
   rw 49 q2 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q2 ∷
   rw 49 q15 ∷
   rw 50 q2 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q2 ∷
   rw 50 q15 ∷
   rw 51 q2 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q2 ∷
   rw 51 q15 ∷
   rw 52 q2 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   rw 52 q15 ∷
   rw 53 q2 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 52 q4 ∷
   rw 53 q4 ∷
   rw 54 q4 ∷
   rw 55 q4 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   rw 57 q16 ∷
   rw 58 q2 ∷
   re 56 3 (CK31 ∷ []) ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q2 ∷
   rw 58 q15 ∷
   rw 59 q2 ∷
   re 57 3 (CS13 ∷ []) ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   rw 59 q15 ∷
   rw 60 q2 ∷
   re 58 3 (CS13 ∷ []) ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   rw 60 q15 ∷
   rw 61 q2 ∷
   re 59 3 (CS13 ∷ []) ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   rw 61 q15 ∷
   rw 62 q2 ∷
   re 60 3 (CS13 ∷ []) ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   rw 62 q15 ∷
   rw 63 q2 ∷
   re 61 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q2 ∷
   rw 63 q15 ∷
   rw 64 q2 ∷
   re 62 3 (CS13 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q2 ∷
   rw 64 q15 ∷
   rw 65 q2 ∷
   re 63 3 (CS13 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q2 ∷
   rw 65 q15 ∷
   rw 66 q2 ∷
   re 64 3 (CS13 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q2 ∷
   rw 66 q15 ∷
   rw 67 q2 ∷
   re 65 3 (CS13 ∷ []) ∷
   re 67 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 66 q2 ∷
   rw 67 q14 ∷
   rw 68 q2 ∷
   re 66 3 (CX03 ∷ []) ∷
   rw 67 q12 ∷
   rw 68 q12 ∷
   rw 69 q12 ∷
   rw 70 q17 ∷
   rw 71 q13 ∷
   rw 72 q12 ∷
   rw 73 q12 ∷
   rw 74 q12 ∷
   rw 75 q12 ∷
   rw 76 q12 ∷
   rw 77 q12 ∷
   rw 78 q10 ∷
   rw 79 q16 ∷
   rw 80 q18 ∷ []) Eq.refl
