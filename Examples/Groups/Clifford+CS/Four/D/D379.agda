{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D379 (W : Ws) where

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
  q3 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q4 : Eqn
  q4 = wE 140 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 1043 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = wE 142 W
  q12 : Eqn
  q12 = wE 31 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CSd23 X3]: 115 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CSd23-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) (X3 ∷ CS23⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   rw⁻ 30 q3 ∷
   rw⁻ 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw⁻ 22 q6 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw⁻ 15 q7 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw⁻ 10 q7 ∷
   rw 9 q4 ∷
   rw⁻ 8 q7 ∷
   rw 7 q4 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q8 ∷
   rw 6 q4 ∷
   rw⁻ 5 q8 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q8 ∷
   rw 5 q4 ∷
   rw⁻ 4 q8 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q8 ∷
   rw 4 q5 ∷
   rw⁻ 3 q8 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q8 ∷
   rw 3 q4 ∷
   rw⁻ 2 q8 ∷
   re 3 3 (CK31 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q8 ∷
   rw 2 q5 ∷
   rw⁻ 1 q8 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q8 ∷
   rw 1 q5 ∷
   rw⁻ 0 q8 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw 5 q10 ∷
   rw 6 q8 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 6 q11 ∷
   rw 7 q8 ∷
   re 5 3 (CK30 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q10 ∷
   rw 8 q8 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 8 q11 ∷
   rw 9 q8 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 9 q11 ∷
   rw 10 q8 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q11 ∷
   rw 11 q7 ∷
   rw 12 q11 ∷
   rw 13 q7 ∷
   rw 14 q10 ∷
   rw 15 q10 ∷
   rw 16 q10 ∷
   rw 17 q11 ∷
   rw 18 q7 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q6 ∷
   rw 26 q10 ∷
   rw 27 q10 ∷
   rw 28 q11 ∷
   rw 29 q10 ∷
   rw 30 q11 ∷
   rw 31 q11 ∷
   rw 32 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = wE 1044 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS23 X3]: 115 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS23 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   rw⁻ 30 q13 ∷
   rw⁻ 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw⁻ 22 q6 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw⁻ 15 q7 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw⁻ 10 q7 ∷
   rw 9 q4 ∷
   rw⁻ 8 q7 ∷
   rw 7 q4 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q8 ∷
   rw 6 q4 ∷
   rw⁻ 5 q8 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q8 ∷
   rw 5 q4 ∷
   rw⁻ 4 q8 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q8 ∷
   rw 4 q5 ∷
   rw⁻ 3 q8 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q8 ∷
   rw 3 q4 ∷
   rw⁻ 2 q8 ∷
   re 3 3 (CK31 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q8 ∷
   rw 2 q5 ∷
   rw⁻ 1 q8 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q8 ∷
   rw 1 q5 ∷
   rw⁻ 0 q8 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q14 ∷
   rw 0 q2 ∷
   rw 1 q13 ∷
   rw 2 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q8 ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q8 ∷
   rw 5 q10 ∷
   rw 6 q8 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 6 q11 ∷
   rw 7 q8 ∷
   re 5 3 (CK30 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q10 ∷
   rw 8 q8 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 8 q11 ∷
   rw 9 q8 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 9 q11 ∷
   rw 10 q8 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q11 ∷
   rw 11 q7 ∷
   rw 12 q11 ∷
   rw 13 q7 ∷
   rw 14 q10 ∷
   rw 15 q10 ∷
   rw 16 q10 ∷
   rw 17 q11 ∷
   rw 18 q7 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q6 ∷
   rw 26 q10 ∷
   rw 27 q10 ∷
   rw 28 q11 ∷
   rw 29 q10 ∷
   rw 30 q11 ∷
   rw 31 q11 ∷
   rw 32 q12 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q17 : Eqn
  q17 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q18 : Eqn
  q18 = wE 3 W
  q19 : Eqn
  q19 = wE 464 W
  q20 : Eqn
  q20 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q21 : Eqn
  q21 = wE 1045 W
  q22 : Eqn
  q22 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CS01 X1]: 107 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CS01-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 32 q15 ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   rw 29 q16 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   rw 15 q19 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   rw 10 q19 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q18 ∷
   rw 8 q19 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q17 ∷
   rw 2 q20 ∷
   rw 1 q17 ∷
   rw 0 q17 ∷
   rw 1 q21 ∷
   rw⁻ 0 q16 ∷
   rw⁻ 1 q17 ∷
   rw⁻ 2 q16 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 8 q20 ∷
   rw 11 q15 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 12 q15 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q22 ∷
   rw 14 q15 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q22 ∷
   rw 16 q15 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q15 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q15 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q22 ∷
   rw 21 q15 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q15 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q15 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q15 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q15 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 28 q15 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 31 q15 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q18 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1046 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CK10 X1]: 107 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CK10-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 32 q15 ∷
   rw 31 q16 ∷
   rw 30 q20 ∷
   rw 29 q16 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   rw 15 q19 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   rw 10 q19 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q18 ∷
   rw 8 q19 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q17 ∷
   rw 2 q20 ∷
   rw 1 q17 ∷
   rw 0 q17 ∷
   rw 1 q23 ∷
   rw⁻ 0 q16 ∷
   rw⁻ 1 q20 ∷
   rw⁻ 2 q16 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 8 q20 ∷
   rw 11 q15 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 12 q15 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q22 ∷
   rw 14 q15 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q22 ∷
   rw 16 q15 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q15 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q15 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q22 ∷
   rw 21 q15 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q15 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q15 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q15 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q15 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 28 q15 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 31 q15 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q18 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q25 : Eqn
  q25 = wE 1047 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CKd10 X1]: 107 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CKd10-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CKd10-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 32 q15 ∷
   rw 31 q16 ∷
   rw 30 q24 ∷
   rw 29 q16 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q18 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q18 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q18 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q18 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q18 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q18 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q18 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q18 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q18 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q18 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q18 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q18 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q18 ∷
   rw 15 q19 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q18 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q18 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q18 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q18 ∷
   rw 10 q19 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q18 ∷
   rw 8 q19 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q20 ∷
   rw 4 q20 ∷
   rw 3 q17 ∷
   rw 2 q20 ∷
   rw 1 q17 ∷
   rw 0 q17 ∷
   rw 1 q25 ∷
   rw⁻ 0 q16 ∷
   rw⁻ 1 q24 ∷
   rw⁻ 2 q16 ∷
   rw⁻ 3 q17 ∷
   rw⁻ 4 q17 ∷
   rw⁻ 5 q20 ∷
   rw⁻ 6 q17 ∷
   rw⁻ 7 q20 ∷
   rw⁻ 8 q20 ∷
   rw 11 q15 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 12 q15 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q22 ∷
   rw 14 q15 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q22 ∷
   rw 16 q15 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q15 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q15 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q15 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q22 ∷
   rw 21 q15 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q15 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q15 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q15 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q15 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q15 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q15 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 28 q15 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q15 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q15 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 31 q15 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q15 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 33 q15 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q18 ∷ []) Eq.refl
