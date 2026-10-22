{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D400 (W : Ws) where

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
  q1 = wE 1133 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 157 W
  q4 : Eqn
  q4 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q5 : Eqn
  q5 = wE 158 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q8 : Eqn
  q8 = wE 624 W
  q9 : Eqn
  q9 = wE 625 W
  q10 : Eqn
  q10 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q11 : Eqn
  q11 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q12 : Eqn
  q12 = wE 1115 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q17 : Eqn
  q17 = wE 140 W
  q18 : Eqn
  q18 = wE 619 W
  q19 : Eqn
  q19 = wE 142 W
  q20 : Eqn
  q20 = wE 27 W
  q21 : Eqn
  q21 = wE 31 W
  q22 : Eqn
  q22 = wE 36 W
  q23 : Eqn
  q23 = wE 37 W
  q24 : Eqn
  q24 = eqn (CX12 ∷ S3 ∷ []) (S3 ∷ CX12 ∷ []) (low₃-comm ((CX₀₁ ↑)) (S))

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] part0: 500 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part0 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-part0 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ CX12 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 0 q1 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 35 3 (CK30 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   rw 36 q5 ∷
   re 36 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 36 5 (CK30 ∷ []) ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 38 q6 ∷
   re 34 3 (CX13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 34 3 (CK30 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 38 3 (CX13 ∷ []) ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 35 5 (CK30 ∷ []) ∷
   re 35 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   re 33 3 (CX13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 36 q3 ∷
   rw 35 q7 ∷
   rw 34 q5 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q6 ∷
   re 32 3 (CX13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 32 3 (CK30 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q6 ∷
   re 33 5 (CK30 ∷ []) ∷
   re 33 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 31 3 (CX13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 34 q3 ∷
   rw 33 q7 ∷
   rw 32 q5 ∷
   re 32 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 32 5 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q6 ∷
   re 30 3 (CX13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q7 ∷
   rw 31 q5 ∷
   re 31 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 31 5 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q6 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q8 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q7 ∷
   rw 29 q5 ∷
   re 29 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 29 5 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q6 ∷
   re 27 3 (CX13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CX13 ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q7 ∷
   rw 28 q5 ∷
   re 28 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 28 5 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q6 ∷
   re 26 3 (CX13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 29 q3 ∷
   rw 28 q7 ∷
   rw 27 q5 ∷
   re 27 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 27 5 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q6 ∷
   re 25 3 (CX13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CX13 ∷ []) ∷
   rw 28 q3 ∷
   rw 27 q7 ∷
   rw 26 q5 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 25 q6 ∷
   re 26 5 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q6 ∷
   re 24 3 (CX13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CX13 ∷ []) ∷
   rw 27 q3 ∷
   rw 26 q7 ∷
   rw 25 q5 ∷
   re 25 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 25 5 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q6 ∷
   re 23 3 (CX13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CX13 ∷ []) ∷
   rw 26 q3 ∷
   rw 25 q7 ∷
   rw 24 q5 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 24 5 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q6 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 21 q9 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 21 3 (CK30 ∷ []) ∷
   re 21 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 22 5 (CK30 ∷ []) ∷
   re 22 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 24 q6 ∷
   re 20 3 (CX13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q2 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CX13 ∷ []) ∷
   rw 23 q3 ∷
   rw 22 q7 ∷
   rw 21 q5 ∷
   re 21 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 20 q6 ∷
   re 21 5 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q6 ∷
   re 19 3 (CX13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q2 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CX13 ∷ []) ∷
   rw 22 q3 ∷
   rw 21 q7 ∷
   rw 20 q5 ∷
   re 20 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 20 5 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q6 ∷
   re 18 3 (CX13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 17 q2 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CX13 ∷ []) ∷
   rw 21 q3 ∷
   rw 20 q7 ∷
   rw 19 q5 ∷
   re 19 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q6 ∷
   re 19 5 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q6 ∷
   re 17 3 (CX13 ∷ []) ∷
   rw 16 q9 ∷
   re 16 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 15 q2 ∷
   re 16 3 (CK30 ∷ []) ∷
   re 16 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 20 3 (CX13 ∷ []) ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   rw 17 q5 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   re 17 5 (CK30 ∷ []) ∷
   re 17 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q6 ∷
   re 15 3 (CX13 ∷ []) ∷
   rw 14 q9 ∷
   re 14 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   re 14 3 (CK30 ∷ []) ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CX13 ∷ []) ∷
   rw 17 q3 ∷
   rw 16 q4 ∷
   rw 15 q5 ∷
   re 15 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   re 15 5 (CK30 ∷ []) ∷
   re 15 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   re 13 3 (CX13 ∷ []) ∷
   rw 12 q8 ∷
   rw 13 q2 ∷
   re 12 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw 11 q10 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   rw 8 q10 ∷
   rw 7 q11 ∷
   rw 6 q11 ∷
   rw 7 q12 ∷
   rw 8 q2 ∷
   re 6 3 (CX13 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw⁻ 8 q11 ∷
   rw⁻ 9 q10 ∷
   rw⁻ 10 q11 ∷
   rw⁻ 11 q10 ∷
   rw⁻ 12 q10 ∷
   rw 13 q6 ∷
   rw 51 q13 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 52 q14 ∷
   rw 51 q15 ∷
   rw⁻ 50 q14 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 51 q14 ∷
   rw 50 q15 ∷
   rw⁻ 49 q14 ∷
   re 50 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 50 q14 ∷
   rw 49 q15 ∷
   rw⁻ 48 q14 ∷
   re 49 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q14 ∷
   rw 48 q15 ∷
   rw⁻ 47 q14 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q14 ∷
   rw 47 q15 ∷
   rw⁻ 46 q14 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q14 ∷
   rw 46 q15 ∷
   rw⁻ 45 q14 ∷
   re 46 3 (CS13 ∷ []) ∷
   rw⁻ 44 q16 ∷
   re 43 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q14 ∷
   rw 44 q17 ∷
   rw⁻ 43 q14 ∷
   re 44 3 (CK31 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q14 ∷
   rw 43 q15 ∷
   rw⁻ 42 q14 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q14 ∷
   rw 42 q15 ∷
   rw⁻ 41 q14 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q14 ∷
   rw 41 q15 ∷
   rw⁻ 40 q14 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw⁻ 39 q16 ∷
   re 38 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 40 q14 ∷
   rw 39 q17 ∷
   rw⁻ 38 q14 ∷
   re 39 3 (CK31 ∷ []) ∷
   rw⁻ 37 q16 ∷
   re 36 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q14 ∷
   rw 37 q17 ∷
   rw⁻ 36 q14 ∷
   re 37 3 (CK31 ∷ []) ∷
   rw 35 q17 ∷
   rw 34 q17 ∷
   rw 33 q15 ∷
   rw 32 q17 ∷
   rw 31 q15 ∷
   rw 30 q15 ∷
   rw 31 q18 ∷
   re 31 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 30 q14 ∷
   rw 31 q19 ∷
   rw 32 q14 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 31 q16 ∷
   re 33 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 32 q14 ∷
   rw 33 q19 ∷
   rw 34 q14 ∷
   re 32 3 (CK30 ∷ []) ∷
   rw 33 q16 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q14 ∷
   rw 35 q20 ∷
   rw 36 q14 ∷
   re 34 3 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q14 ∷
   rw 36 q20 ∷
   rw 37 q14 ∷
   re 35 3 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q14 ∷
   rw 37 q20 ∷
   rw 38 q14 ∷
   re 36 3 (CS03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 37 q14 ∷
   rw 38 q19 ∷
   rw 39 q14 ∷
   re 37 3 (CK30 ∷ []) ∷
   rw 38 q16 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q14 ∷
   rw 40 q20 ∷
   rw 41 q14 ∷
   re 39 3 (CS03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q14 ∷
   rw 41 q20 ∷
   rw 42 q14 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q14 ∷
   rw 42 q20 ∷
   rw 43 q14 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q14 ∷
   rw 43 q20 ∷
   rw 44 q14 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q14 ∷
   rw 44 q20 ∷
   rw 45 q14 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q14 ∷
   rw 45 q20 ∷
   rw 46 q14 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 45 q20 ∷
   rw 46 q20 ∷
   rw 47 q19 ∷
   rw 48 q20 ∷
   rw 49 q19 ∷
   rw 50 q19 ∷
   rw 51 q21 ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CX13 ∷ []) ∷
   rw 30 q22 ∷
   rw⁻ 31 q4 ∷
   rw 32 q23 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q6 ∷
   re 29 5 (CK30 ∷ []) ∷
   rw 30 q24 ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 32 3 (CX13 ∷ []) ∷
   rw 32 q22 ∷
   rw⁻ 33 q4 ∷
   rw 34 q23 ∷
   re 35 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 37 q6 ∷
   re 31 5 (CK30 ∷ []) ∷
   rw 32 q24 ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 34 3 (CX13 ∷ []) ∷
   rw 34 q22 ∷
   rw⁻ 35 q7 ∷
   rw 36 q23 ∷
   re 37 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 39 q6 ∷
   re 33 5 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 35 3 (CX13 ∷ []) ∷
   rw 35 q22 ∷
   rw⁻ 36 q7 ∷
   rw 37 q23 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q6 ∷
   re 34 5 (CS03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 36 3 (CX13 ∷ []) ∷
   rw 36 q22 ∷
   rw⁻ 37 q7 ∷
   rw 38 q23 ∷
   re 39 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 41 q6 ∷
   re 35 5 (CS03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 37 3 (CX13 ∷ []) ∷
   rw 37 q22 ∷
   rw⁻ 38 q4 ∷
   rw 39 q23 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q6 ∷
   re 36 5 (CK30 ∷ []) ∷
   rw 37 q24 ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 39 3 (CX13 ∷ []) ∷
   rw 39 q22 ∷
   rw⁻ 40 q7 ∷
   rw 41 q23 ∷
   re 42 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷ []) Eq.refl
