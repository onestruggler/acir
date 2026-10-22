{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D485 (W : Ws) where

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
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = wE 74 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q8 : Eqn
  q8 = wE 772 W
  q9 : Eqn
  q9 = wE 1287 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 329 W
  q12 : Eqn
  q12 = wE 30 W
  q13 : Eqn
  q13 = wE 31 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CS03]: 87 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CS03 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CS03 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CS03 ∷ []) (CS03 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw 30 q1 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw⁻ 28 q4 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 23 q5 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q2 ∷
   rw 23 q6 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw⁻ 21 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 7 q6 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 5 q8 ∷
   rw 4 q8 ∷
   rw 3 q3 ∷
   rw 2 q8 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q9 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q10 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q12 ∷
   rw 9 q2 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q7 ∷
   rw 10 q4 ∷
   rw 11 q7 ∷
   rw 12 q5 ∷
   rw 13 q5 ∷
   rw 14 q5 ∷
   rw 15 q4 ∷
   rw 16 q7 ∷
   rw 17 q5 ∷
   rw 18 q5 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   rw 21 q5 ∷
   rw 22 q5 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw 24 q12 ∷
   rw 25 q2 ∷
   re 23 3 (CX03 ∷ []) ∷
   rw 24 q5 ∷
   rw 25 q5 ∷
   rw 26 q4 ∷
   rw 27 q5 ∷
   rw 28 q4 ∷
   rw 29 q4 ∷
   rw 30 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q15 : Eqn
  q15 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 1288 W
  q20 : Eqn
  q20 = eqn (CS01 ∷ S3 ∷ []) (S3 ∷ CS01 ∷ []) (low-comm (CS) ((S ↑)))
  q21 : Eqn
  q21 = wE 1289 W
  q22 : Eqn
  q22 = wE 245 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CS01]: 45 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CS01 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CS01 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CS01 ∷ []) (CS01 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw⁻ 28 q14 ∷
   rw⁻ 27 q14 ∷
   rw⁻ 26 q15 ∷
   rw⁻ 25 q14 ∷
   rw⁻ 24 q15 ∷
   rw⁻ 23 q15 ∷
   rw 24 q16 ∷
   rw 23 q17 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   rw 23 q19 ∷
   rw⁻ 22 q17 ∷
   rw 25 q16 ∷
   re 23 3 (CX03 ∷ []) ∷
   rw 24 q18 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 20 q15 ∷
   rw⁻ 19 q15 ∷
   rw⁻ 18 q15 ∷
   rw⁻ 17 q15 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 15 q20 ∷
   rw⁻ 14 q14 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 12 q15 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q20 ∷
   rw⁻ 9 q14 ∷
   rw⁻ 8 q20 ∷
   rw⁻ 7 q14 ∷
   rw 8 q16 ∷
   rw 7 q17 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 7 q19 ∷
   rw⁻ 6 q17 ∷
   rw 9 q16 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q21 ∷
   rw 4 q21 ∷
   rw 3 q22 ∷
   rw 2 q21 ∷
   rw 1 q22 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1284 W
  q24 : Eqn
  q24 = wE 39 W
  q25 : Eqn
  q25 = wE 315 W
  q26 : Eqn
  q26 = wE 113 W
  q27 : Eqn
  q27 = eqn (CK01 ∷ CX32 ∷ []) (CX32 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CX₁₀))
  q28 : Eqn
  q28 = wE 114 W
  q29 : Eqn
  q29 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q30 : Eqn
  q30 = wE 112 W
  q31 : Eqn
  q31 = eqn (S0 ∷ CX31 ∷ []) (CX31 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q32 : Eqn
  q32 = wE 1290 W
  q33 : Eqn
  q33 = wE 40 W
  q34 : Eqn
  q34 = wE 6 W
  q35 : Eqn
  q35 = wE 481 W
  q36 : Eqn
  q36 = wE 1286 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX03 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX03 CS23 CS23 CK32 CS23 CK32 CK32] [CX31]: 455 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CX31 : ⟪ (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-CX31 = derive (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ CX31 ∷ []) (CX31 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CX03 ∷ CK32 ∷ S3 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK32 ∷ S3 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX03 ∷ CS23 ∷ CS23 ∷ CK32 ∷ CS23 ∷ CK32 ∷ CK32 ∷ [])
  (rw 29 q1 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 27 q4 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 23 q5 ∷
   re 22 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q2 ∷
   rw 23 q6 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw⁻ 21 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 10 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 7 q6 ∷
   rw⁻ 6 q2 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 5 q8 ∷
   rw 4 q8 ∷
   rw 3 q3 ∷
   rw 2 q8 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q23 ∷
   rw 0 q5 ∷
   rw 1 q5 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   rw 5 q4 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q24 ∷
   rw 8 q2 ∷
   re 6 3 (CX30 ∷ []) ∷
   rw 7 q11 ∷
   rw 8 q25 ∷
   rw 9 q11 ∷
   rw 10 q25 ∷
   rw 11 q10 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q11 ∷
   rw 15 q25 ∷
   rw 16 q10 ∷
   rw 17 q10 ∷
   rw 18 q10 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   rw 23 q24 ∷
   rw 24 q2 ∷
   re 22 3 (CX30 ∷ []) ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q11 ∷
   rw 26 q10 ∷
   rw 27 q11 ∷
   rw 28 q11 ∷
   rw 29 q13 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q16 ∷
   re 29 3 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q16 ∷
   re 33 3 (CX31 ∷ []) ∷
   rw 32 q26 ∷
   rw 31 q27 ∷
   rw 30 q28 ∷
   re 30 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 30 5 (CK03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 32 q18 ∷
   re 28 3 (CX31 ∷ []) ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q16 ∷
   re 28 3 (CK03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q16 ∷
   re 32 3 (CX31 ∷ []) ∷
   rw 31 q26 ∷
   rw 30 q27 ∷
   rw 29 q28 ∷
   re 29 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 29 5 (CK03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 31 q18 ∷
   re 27 3 (CX31 ∷ []) ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q16 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q16 ∷
   re 31 3 (CX31 ∷ []) ∷
   rw 30 q26 ∷
   rw 29 q29 ∷
   rw 28 q28 ∷
   re 28 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 26 3 (CX31 ∷ []) ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q16 ∷
   re 26 3 (CK03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q16 ∷
   re 30 3 (CX31 ∷ []) ∷
   rw 29 q26 ∷
   rw 28 q27 ∷
   rw 27 q28 ∷
   re 27 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 27 5 (CK03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 25 3 (CX31 ∷ []) ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q16 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q16 ∷
   re 29 3 (CX31 ∷ []) ∷
   rw 28 q26 ∷
   rw 27 q29 ∷
   rw 26 q28 ∷
   re 26 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 24 3 (CX31 ∷ []) ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 23 q16 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q16 ∷
   re 28 3 (CX31 ∷ []) ∷
   rw 27 q26 ∷
   rw 26 q29 ∷
   rw 25 q28 ∷
   re 25 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 24 q16 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 22 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   rw 23 q30 ∷
   rw 24 q16 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 25 q16 ∷
   re 23 3 (CX30 ∷ []) ∷
   rw 24 q18 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q16 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q16 ∷
   re 26 3 (CX31 ∷ []) ∷
   rw 25 q26 ∷
   rw 24 q29 ∷
   rw 23 q28 ∷
   re 23 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 23 5 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 21 3 (CX31 ∷ []) ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q16 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q16 ∷
   re 25 3 (CX31 ∷ []) ∷
   rw 24 q26 ∷
   rw 23 q29 ∷
   rw 22 q28 ∷
   re 22 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 22 5 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 20 3 (CX31 ∷ []) ∷
   re 20 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q16 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q16 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 23 q26 ∷
   rw 22 q29 ∷
   rw 21 q28 ∷
   re 21 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 19 3 (CX31 ∷ []) ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q16 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q16 ∷
   re 23 3 (CX31 ∷ []) ∷
   rw 22 q26 ∷
   rw 21 q29 ∷
   rw 20 q28 ∷
   re 20 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 18 3 (CX31 ∷ []) ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q16 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q16 ∷
   re 22 3 (CX31 ∷ []) ∷
   rw 21 q26 ∷
   rw 20 q29 ∷
   rw 19 q28 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 17 3 (CX31 ∷ []) ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q16 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 17 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 23 q16 ∷
   re 21 3 (CX31 ∷ []) ∷
   rw 20 q26 ∷
   rw 19 q29 ∷
   rw 18 q28 ∷
   re 18 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 17 q18 ∷
   re 18 5 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 16 3 (CX31 ∷ []) ∷
   rw 15 q31 ∷
   re 15 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 14 q16 ∷
   re 15 3 (CK03 ∷ []) ∷
   re 15 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q16 ∷
   re 19 3 (CX31 ∷ []) ∷
   rw 18 q26 ∷
   rw 17 q27 ∷
   rw 16 q28 ∷
   re 16 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 16 5 (CK03 ∷ []) ∷
   re 16 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   re 14 3 (CX31 ∷ []) ∷
   re 14 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 13 q16 ∷
   re 14 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q16 ∷
   re 18 3 (CX31 ∷ []) ∷
   rw 17 q26 ∷
   rw 16 q29 ∷
   rw 15 q28 ∷
   re 15 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   re 15 5 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q18 ∷
   re 13 3 (CX31 ∷ []) ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 12 q16 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 19 q16 ∷
   re 17 3 (CX31 ∷ []) ∷
   rw 16 q26 ∷
   rw 15 q29 ∷
   rw 14 q28 ∷
   re 14 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 12 3 (CX31 ∷ []) ∷
   re 12 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 11 q16 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 18 q16 ∷
   re 16 3 (CX31 ∷ []) ∷
   rw 15 q26 ∷
   rw 14 q29 ∷
   rw 13 q28 ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 12 q18 ∷
   re 13 5 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 11 3 (CX31 ∷ []) ∷
   rw 10 q31 ∷
   re 10 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q16 ∷
   re 10 3 (CK03 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q16 ∷
   re 14 3 (CX31 ∷ []) ∷
   rw 13 q26 ∷
   rw 12 q27 ∷
   rw 11 q28 ∷
   re 11 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q18 ∷
   re 11 5 (CK03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw 8 q31 ∷
   re 8 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q16 ∷
   re 8 3 (CK03 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CK01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q16 ∷
   re 12 3 (CX31 ∷ []) ∷
   rw 11 q26 ∷
   rw 10 q27 ∷
   rw 9 q28 ∷
   re 9 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   re 9 5 (CK03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 11 q18 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw 8 q16 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 7 q30 ∷
   rw 8 q16 ∷
   re 6 3 (CX31 ∷ []) ∷
   rw 9 q16 ∷
   re 7 3 (CX30 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q32 ∷
   rw 4 q32 ∷
   rw 3 q33 ∷
   rw 2 q32 ∷
   rw 1 q33 ∷
   rw 0 q33 ∷
   rw 30 q1 ∷
   rw 29 q8 ∷
   rw 28 q8 ∷
   rw 27 q3 ∷
   rw 26 q8 ∷
   rw 25 q3 ∷
   rw 24 q3 ∷
   re 23 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q2 ∷
   rw 24 q34 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw 22 q3 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q35 ∷
   rw 15 q8 ∷
   rw 14 q3 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q35 ∷
   rw 10 q8 ∷
   rw 9 q35 ∷
   rw 8 q8 ∷
   re 7 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw 8 q34 ∷
   rw⁻ 7 q2 ∷
   re 8 3 (CX31 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw⁻ 5 q4 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 3 q4 ∷
   rw⁻ 2 q5 ∷
   rw⁻ 1 q5 ∷
   rw 2 q36 ∷
   rw 1 q10 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   re 8 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q12 ∷
   rw 9 q2 ∷
   re 7 3 (CX03 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q7 ∷
   rw 10 q4 ∷
   rw 11 q7 ∷
   rw 12 q5 ∷
   rw 13 q5 ∷
   rw 14 q5 ∷
   rw 15 q4 ∷
   rw 16 q7 ∷
   rw 17 q5 ∷
   rw 18 q5 ∷
   rw 19 q5 ∷
   rw 20 q5 ∷
   rw 21 q5 ∷
   rw 22 q5 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   rw 24 q12 ∷
   rw 25 q2 ∷
   re 23 3 (CX03 ∷ []) ∷
   rw 24 q5 ∷
   rw 25 q5 ∷
   rw 26 q4 ∷
   rw 27 q5 ∷
   rw 28 q4 ∷
   rw 29 q4 ∷
   rw 30 q13 ∷ []) Eq.refl
