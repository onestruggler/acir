{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD774 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D774 (W : Ws) (Sᴰ : SD774) where

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
  lem-merge-R0-at3012 : St 3345
  lem-merge-R0-at3012 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q2 : Eqn
  q2 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q3 : Eqn
  q3 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q4 : Eqn
  q4 = wE 390 W
  q5 : Eqn
  q5 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q6 : Eqn
  q6 = eqn (X0 ∷ X1 ∷ []) (X1 ∷ X0 ∷ []) (low₁-comm (X) (X))
  q7 : Eqn
  q7 = wE 388 W
  q8 : Eqn
  q8 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q9 : Eqn
  q9 = wE 387 W
  q10 : Eqn
  q10 = sE 3345 lem-merge-R0-at3012
  q11 : Eqn
  q11 = wE 1 W
  q12 : Eqn
  q12 = wE 173 W
  q13 : Eqn
  q13 = wE 689 W
  q14 : Eqn
  q14 = wE 335 W
  q15 : Eqn
  q15 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q16 : Eqn
  q16 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = wE 1294 W
  q19 : Eqn
  q19 = wE 368 W
  q20 : Eqn
  q20 = wE 464 W
  q21 : Eqn
  q21 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q22 : Eqn
  q22 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q23 : Eqn
  q23 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q24 : Eqn
  q24 = wE 2577 W
  q25 : Eqn
  q25 = wE 175 W

-- L87 X3: 230 steps
lem-L87-X3 : ⟪ (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-L87-X3 = derive (S3 ∷ S3 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X0 ∷ X0 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ X1 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X1 ∷ X0 ∷ X0 ∷ X1 ∷ X2 ∷ X0 ∷ X1 ∷ X3 ∷ S3 ∷ K3 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ Toff301 ∷ K3⁻ ∷ S3⁻ ∷ X0 ∷ X1 ∷ X3 ∷ X2 ∷ X1 ∷ X0 ∷ []) (X3 ∷ [])
  (rw⁻ 15 q1 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q3 ∷
   rw 18 q4 ∷
   rw 14 q5 ∷
   rw⁻ 15 q6 ∷
   rw 16 q7 ∷
   rw 13 q8 ∷
   rw 14 q9 ∷
   rw⁻ 24 q1 ∷
   rw⁻ 25 q2 ∷
   rw⁻ 26 q2 ∷
   rw⁻ 27 q3 ∷
   rw 28 q4 ∷
   rw 23 q5 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 25 q6 ∷
   rw 26 q7 ∷
   rw 22 q8 ∷
   rw 23 q9 ∷
   rw⁻ 34 q2 ∷
   rw⁻ 35 q2 ∷
   rw⁻ 36 q1 ∷
   rw⁻ 37 q2 ∷
   rw⁻ 38 q3 ∷
   rw 39 q4 ∷
   rw⁻ 33 q6 ∷
   rw⁻ 34 q6 ∷
   rw 35 q5 ∷
   rw⁻ 36 q6 ∷
   rw 37 q7 ∷
   rw 32 q9 ∷
   rw 32 q8 ∷
   rw 33 q9 ∷
   rw⁻ 43 q1 ∷
   rw⁻ 44 q2 ∷
   rw⁻ 45 q3 ∷
   rw⁻ 46 q2 ∷
   rw⁻ 47 q3 ∷
   rw 48 q4 ∷
   rw 42 q5 ∷
   rw⁻ 43 q6 ∷
   rw 44 q7 ∷
   rw 41 q8 ∷
   rw 42 q9 ∷
   rw⁻ 54 q3 ∷
   rw⁻ 55 q3 ∷
   rw⁻ 56 q1 ∷
   rw⁻ 57 q2 ∷
   rw⁻ 58 q3 ∷
   rw 59 q4 ∷
   rw 53 q7 ∷
   rw 53 q5 ∷
   rw⁻ 54 q6 ∷
   rw 55 q7 ∷
   rw 52 q8 ∷
   rw 53 q9 ∷
   rw⁻ 63 q1 ∷
   rw⁻ 64 q3 ∷
   rw⁻ 65 q2 ∷
   rw⁻ 66 q3 ∷
   rw⁻ 67 q2 ∷
   rw⁻ 68 q3 ∷
   rw 69 q4 ∷
   rw 62 q5 ∷
   rw 63 q7 ∷
   rw 61 q8 ∷
   rw 62 q9 ∷
   rw⁻ 62 q6 ∷
   rw 63 q7 ∷
   rw⁻ 73 q3 ∷
   rw⁻ 74 q2 ∷
   rw⁻ 75 q2 ∷
   rw⁻ 76 q3 ∷
   rw⁻ 77 q1 ∷
   rw⁻ 78 q2 ∷
   rw⁻ 79 q3 ∷
   rw 80 q4 ∷
   rw 72 q7 ∷
   rw 71 q9 ∷
   rw 72 q5 ∷
   rw⁻ 73 q6 ∷
   rw 74 q7 ∷
   rw 71 q8 ∷
   rw 72 q9 ∷
   rw⁻ 82 q1 ∷
   rw⁻ 83 q3 ∷
   rw⁻ 84 q2 ∷
   rw 81 q5 ∷
   rw 82 q7 ∷
   rw 80 q8 ∷
   rw 81 q9 ∷
   rw 5 q10 ∷
   rw 10 q10 ∷
   rw 16 q10 ∷
   rw 21 q10 ∷
   rw 26 q11 ∷
   rw 25 q12 ∷
   rw 24 q13 ∷
   re 23 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 24 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 23 q14 ∷
   rw 26 q11 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw⁻ 25 q15 ∷
   rw 28 q11 ∷
   re 26 3 (CS13⁻ ∷ []) ∷
   rw⁻ 27 q15 ∷
   rw 30 q11 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 29 q14 ∷
   rw⁻ 30 q16 ∷
   rw 31 q17 ∷
   rw 30 q16 ∷
   rw 29 q18 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q17 ∷
   rw 27 q15 ∷
   re 26 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 28 q17 ∷
   rw 25 q15 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q17 ∷
   rw 23 q18 ∷
   rw 24 q19 ∷
   re 24 8 (Toff201 ∷ []) ∷
   rw 22 q20 ∷
   rw 21 q21 ∷
   rw 20 q22 ∷
   rw 19 q13 ∷
   re 18 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 19 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 18 q14 ∷
   rw 21 q11 ∷
   re 19 3 (CS13 ∷ []) ∷
   rw⁻ 20 q15 ∷
   rw 23 q11 ∷
   re 21 3 (CS13⁻ ∷ []) ∷
   rw⁻ 22 q15 ∷
   rw 25 q11 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 24 q14 ∷
   rw⁻ 25 q16 ∷
   rw 26 q17 ∷
   rw 25 q16 ∷
   rw 24 q18 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q17 ∷
   rw 22 q15 ∷
   re 21 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 23 q17 ∷
   rw 20 q15 ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q17 ∷
   rw 18 q18 ∷
   rw 19 q19 ∷
   re 19 8 (Toff201 ∷ []) ∷
   rw 17 q20 ∷
   rw 16 q21 ∷
   rw 15 q23 ∷
   rw 14 q22 ∷
   rw 13 q13 ∷
   re 12 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 13 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 12 q14 ∷
   rw 15 q11 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q15 ∷
   rw 17 q11 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q15 ∷
   rw 19 q11 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q14 ∷
   rw⁻ 19 q16 ∷
   rw 20 q17 ∷
   rw 19 q16 ∷
   rw 18 q18 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q17 ∷
   rw 16 q15 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q17 ∷
   rw 14 q15 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q17 ∷
   rw 12 q18 ∷
   rw 13 q19 ∷
   re 13 8 (Toff201 ∷ []) ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   rw 9 q22 ∷
   rw 8 q13 ∷
   re 7 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 8 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 7 q14 ∷
   rw 10 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q15 ∷
   rw 12 q11 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q15 ∷
   rw 14 q11 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q14 ∷
   rw⁻ 14 q16 ∷
   rw 15 q17 ∷
   rw 14 q16 ∷
   rw 13 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q17 ∷
   rw 11 q15 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q17 ∷
   rw 9 q15 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q17 ∷
   rw 7 q18 ∷
   rw 8 q19 ∷
   re 8 8 (Toff201 ∷ []) ∷
   rw 6 q20 ∷
   rw 5 q21 ∷
   rw 4 q12 ∷
   rw 3 q23 ∷
   rw 2 q22 ∷
   rw 1 q20 ∷
   rw 0 q20 ∷
   rw 1 q24 ∷
   rw 0 q25 ∷
   rw 1 q17 ∷ []) Eq.refl
