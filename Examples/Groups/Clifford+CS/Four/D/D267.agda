{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D267 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 481 W
  q6 : Eqn
  q6 = wE 772 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 6 W
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q11 : Eqn
  q11 = wE 854 W
  q12 : Eqn
  q12 = wE 39 W
  q13 : Eqn
  q13 = wE 27 W
  q14 : Eqn
  q14 = wE 315 W
  q15 : Eqn
  q15 = wE 329 W
  q16 : Eqn
  q16 = wE 31 W

-- pass [CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX30 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 S0 S0 S0 CK02 S0 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02] [X3 CK32 X3]: 173 steps
lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CK32-X3 : ⟪ (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-CK32-X3 = derive (CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ S0 ∷ S0 ∷ S0 ∷ CK02 ∷ S0 ∷ CX30 ∷ CK02 ∷ S0 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK02 ∷ S0 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw 77 q1 ∷
   rw⁻ 76 q2 ∷
   rw⁻ 75 q3 ∷
   rw⁻ 74 q2 ∷
   rw 73 q4 ∷
   rw 72 q4 ∷
   rw 71 q4 ∷
   rw 70 q4 ∷
   rw 69 q4 ∷
   rw 68 q4 ∷
   rw 67 q5 ∷
   rw 66 q6 ∷
   rw 65 q4 ∷
   rw 64 q4 ∷
   rw 63 q4 ∷
   rw 62 q5 ∷
   rw 61 q6 ∷
   rw 60 q5 ∷
   rw 59 q6 ∷
   re 58 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 60 q7 ∷
   rw 59 q8 ∷
   rw⁻ 58 q7 ∷
   re 59 3 (CX31 ∷ []) ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   rw 55 q5 ∷
   rw 54 q5 ∷
   rw 53 q5 ∷
   rw 52 q5 ∷
   rw 51 q6 ∷
   rw 50 q5 ∷
   rw 49 q5 ∷
   rw 48 q5 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q4 ∷
   rw 44 q4 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q4 ∷
   rw 39 q4 ∷
   rw 38 q5 ∷
   rw 37 q6 ∷
   rw 36 q5 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw 33 q4 ∷
   rw 32 q4 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   re 15 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 17 q7 ∷
   rw 16 q8 ∷
   rw⁻ 15 q7 ∷
   re 16 3 (CX31 ∷ []) ∷
   rw⁻ 14 q9 ∷
   rw⁻ 13 q9 ∷
   rw⁻ 12 q9 ∷
   rw⁻ 11 q9 ∷
   rw⁻ 10 q9 ∷
   rw⁻ 9 q9 ∷
   rw⁻ 8 q10 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 6 q9 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 4 q9 ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 1 q10 ∷
   rw⁻ 0 q3 ∷
   rw 1 q11 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q10 ∷
   rw 5 q3 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 9 q9 ∷
   rw 10 q3 ∷
   rw 11 q10 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q9 ∷
   rw 17 q9 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   rw 19 q12 ∷
   rw 20 q7 ∷
   re 18 3 (CX30 ∷ []) ∷
   rw 19 q13 ∷
   rw 20 q13 ∷
   rw 21 q13 ∷
   rw 22 q13 ∷
   rw 23 q13 ∷
   rw 24 q13 ∷
   rw 25 q13 ∷
   rw 26 q13 ∷
   rw 27 q13 ∷
   rw 28 q13 ∷
   rw 29 q13 ∷
   rw 30 q13 ∷
   rw 31 q13 ∷
   rw 32 q13 ∷
   rw 33 q13 ∷
   rw 34 q13 ∷
   rw 35 q13 ∷
   rw 36 q13 ∷
   rw 37 q14 ∷
   rw 38 q14 ∷
   rw 39 q14 ∷
   rw 40 q15 ∷
   rw 41 q14 ∷
   rw 42 q13 ∷
   rw 43 q13 ∷
   rw 44 q13 ∷
   rw 45 q13 ∷
   rw 46 q13 ∷
   rw 47 q13 ∷
   rw 48 q13 ∷
   rw 49 q13 ∷
   rw 50 q13 ∷
   rw 51 q14 ∷
   rw 52 q14 ∷
   rw 53 q14 ∷
   rw 54 q15 ∷
   rw 55 q14 ∷
   rw 56 q14 ∷
   rw 57 q14 ∷
   rw 58 q14 ∷
   rw 59 q15 ∷
   rw 60 q14 ∷
   re 62 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 61 q7 ∷
   rw 62 q12 ∷
   rw 63 q7 ∷
   re 61 3 (CX30 ∷ []) ∷
   rw 62 q15 ∷
   rw 63 q14 ∷
   rw 64 q15 ∷
   rw 65 q14 ∷
   rw 66 q13 ∷
   rw 67 q13 ∷
   rw 68 q13 ∷
   rw 69 q15 ∷
   rw 70 q14 ∷
   rw 71 q13 ∷
   rw 72 q13 ∷
   rw 73 q13 ∷
   rw 74 q13 ∷
   rw 75 q13 ∷
   rw 76 q13 ∷
   rw 77 q16 ∷ []) Eq.refl
