{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D380 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q4 : Eqn
  q4 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q5 : Eqn
  q5 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q6 : Eqn
  q6 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (wn 1048 W)
  q9 : Eqn
  q9 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CSd01 X1]: 107 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CSd01-X1 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ [])
  (rw 32 q1 ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q2 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q4 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 29 q4 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q4 ∷
   re 25 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 27 q4 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q4 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q4 ∷
   re 22 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 24 q4 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q4 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q4 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q4 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q4 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q4 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw 15 q5 ∷
   re 14 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   rw 10 q5 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   rw 8 q5 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw 5 q6 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   rw 2 q6 ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 5 q6 ∷
   rw⁻ 6 q7 ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q6 ∷
   rw 11 q1 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 12 q1 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q9 ∷
   rw 14 q1 ∷
   re 12 3 (CK30 ∷ []) ∷
   rw 13 q9 ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CK30 ∷ []) ∷
   rw 18 q9 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CX13 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CK30 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CK30 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 32 q4 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ []) (wn 1049 W)
  q11 : Eqn
  q11 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q12 : Eqn
  q12 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q13 : Eqn
  q13 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)

-- pass [X1 CS13 X1] [CS02]: 7 steps
lem-pass-X1-CS13-X1-vs-CS02 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-CS02 = derive (X1 ∷ CS13 ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  (rw 2 q10 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q11 ∷
   rw⁻ 2 q12 ∷
   rw 3 q13 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q15 : Eqn
  q15 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q16 : Eqn
  q16 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q17 : Eqn
  q17 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q18 : Eqn
  q18 = eqn (X1 ∷ CS12 ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS12 ∷ X1 ∷ []) (wn 1050 W)

-- pass [X1 CS13 X1] [TOFF013]: 65 steps
lem-pass-X1-CS13-X1-vs-TOFF013 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-TOFF013 = derive (X1 ∷ CS13 ∷ X1 ∷ Toff013 ∷ []) (Toff013 ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q16 ∷
   rw 11 q4 ∷
   rw 10 q16 ∷
   rw 9 q14 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q2 ∷
   rw 1 q18 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q15 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q16 ∷
   rw 0 q1 ∷
   rw⁻ 1 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw⁻ 3 q15 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q17 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 4 q4 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ []) (wn 1051 W)
  q20 : Eqn
  q20 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))

-- pass [X1 CS13 X1] [CSd02]: 7 steps
lem-pass-X1-CS13-X1-vs-CSd02 : ⟪ (X1 ∷ CS13 ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS13-X1-vs-CSd02 = derive (X1 ∷ CS13 ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CS13 ∷ X1 ∷ [])
  (rw 2 q19 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q11 ∷
   rw⁻ 2 q20 ∷
   rw 3 q13 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw 0 q19 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = eqn (CK13 ∷ Sw12 ∷ []) (Sw12 ∷ CK23 ∷ []) (wn 1052 W)
  q22 : Eqn
  q22 = eqn (CS01 ∷ CK23 ∷ []) (CK23 ∷ CS01 ∷ []) (low-comm (CS) (CK₀₁))
  q23 : Eqn
  q23 = eqn (CK23 ∷ Sw12 ∷ []) (Sw12 ∷ CK13 ∷ []) (wn 1053 W)

-- pass [X1 CK13 X1] [CS02]: 7 steps
lem-pass-X1-CK13-X1-vs-CS02 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-CS02 = derive (X1 ∷ CK13 ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  (rw 2 q10 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q21 ∷
   rw⁻ 2 q22 ∷
   rw 3 q23 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (X1 ∷ CK12 ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CK12 ∷ X1 ∷ []) (wn 1054 W)

-- pass [X1 CK13 X1] [TOFF013]: 65 steps
lem-pass-X1-CK13-X1-vs-TOFF013 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-TOFF013 = derive (X1 ∷ CK13 ∷ X1 ∷ Toff013 ∷ []) (Toff013 ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q16 ∷
   rw 11 q4 ∷
   rw 10 q16 ∷
   rw 9 q14 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q2 ∷
   rw 1 q24 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q15 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q16 ∷
   rw 0 q1 ∷
   rw⁻ 1 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw⁻ 3 q15 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q17 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CK13 ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 4 q4 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (CS01⁻ ∷ CK23 ∷ []) (CK23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₀₁))

-- pass [X1 CK13 X1] [CSd02]: 7 steps
lem-pass-X1-CK13-X1-vs-CSd02 : ⟪ (X1 ∷ CK13 ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK13-X1-vs-CSd02 = derive (X1 ∷ CK13 ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CK13 ∷ X1 ∷ [])
  (rw 2 q19 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q21 ∷
   rw⁻ 2 q25 ∷
   rw 3 q23 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw 0 q19 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wn 84 W)
  q27 : Eqn
  q27 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q28 : Eqn
  q28 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)

-- pass [X1 CSd13 X1] [CS02]: 7 steps
lem-pass-X1-CSd13-X1-vs-CS02 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CS02 = derive (X1 ∷ CS13⁻ ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  (rw 2 q10 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q26 ∷
   rw⁻ 2 q27 ∷
   rw 3 q28 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (X1 ∷ CS12⁻ ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS12⁻ ∷ X1 ∷ []) (wn 1055 W)

-- pass [X1 CSd13 X1] [TOFF013]: 65 steps
lem-pass-X1-CSd13-X1-vs-TOFF013 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-TOFF013 = derive (X1 ∷ CS13⁻ ∷ X1 ∷ Toff013 ∷ []) (Toff013 ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q16 ∷
   rw 11 q4 ∷
   rw 10 q16 ∷
   rw 9 q14 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q2 ∷
   rw 1 q29 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q15 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q16 ∷
   rw 0 q1 ∷
   rw⁻ 1 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw⁻ 3 q15 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q17 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 4 q4 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))

-- pass [X1 CSd13 X1] [CSd02]: 7 steps
lem-pass-X1-CSd13-X1-vs-CSd02 : ⟪ (X1 ∷ CS13⁻ ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd13-X1-vs-CSd02 = derive (X1 ∷ CS13⁻ ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CS13⁻ ∷ X1 ∷ [])
  (rw 2 q19 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q26 ∷
   rw⁻ 2 q30 ∷
   rw 3 q28 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw 0 q19 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (CCZ123 ∷ []) (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (wn 1056 W)
  q32 : Eqn
  q32 = eqn (X1 ∷ CX23 ∷ []) (CX23 ∷ X1 ∷ []) (low-comm ((X ↑)) (CX₀₁))
  q33 : Eqn
  q33 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q34 : Eqn
  q34 = eqn (CS12⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS12⁻ ∷ []) (wn 1057 W)
  q35 : Eqn
  q35 = eqn (CS12 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CS12 ∷ []) (wn 1058 W)
  q36 : Eqn
  q36 = eqn (CS12 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ []) (CCZ123 ∷ []) (wn 1059 W)

-- pass [CCZ123] [X1 CS01 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CS01-X1 : ⟪ (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CS01-X1 = derive (CCZ123 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ CCZ123 ∷ [])
  (rw 0 q31 ∷
   rw⁻ 4 q32 ∷
   rw⁻ 5 q33 ∷
   rw⁻ 6 q32 ∷
   rw 7 q1 ∷
   rw 6 q2 ∷
   rw 5 q7 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q34 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 7 q4 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 3 q33 ∷
   rw⁻ 4 q32 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q7 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q35 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q7 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q4 ∷
   rw 0 q35 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (CK10 ∷ CX23 ∷ []) (CX23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₀₁))
  q38 : Eqn
  q38 = eqn (CS12⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS12⁻ ∷ []) (wn 1060 W)
  q39 : Eqn
  q39 = eqn (CS12 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CS12 ∷ []) (wn 1061 W)

-- pass [CCZ123] [X1 CK10 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CK10-X1 : ⟪ (CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CK10-X1 = derive (CCZ123 ∷ X1 ∷ CK10 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ X1 ∷ CCZ123 ∷ [])
  (rw 0 q31 ∷
   rw⁻ 4 q32 ∷
   rw⁻ 5 q37 ∷
   rw⁻ 6 q32 ∷
   rw 7 q1 ∷
   rw 6 q2 ∷
   rw 5 q6 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q38 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 7 q4 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 3 q37 ∷
   rw⁻ 4 q32 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q6 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q39 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q4 ∷
   rw 0 q39 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (CS02 ∷ ι ∷ []) (ι ∷ CS02 ∷ []) (wn 1062 W)

-- pass [CS03] [iI]: 9 steps
lem-pass-CS03-vs-iI : ⟪ (CS03 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-iI = derive (CS03 ∷ ι ∷ []) (ι ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw 1 q16 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q40 ∷
   rw⁻ 0 q16 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = eqn (Z1 ∷ Sw23 ∷ []) (Sw23 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (Swap))
  q42 : Eqn
  q42 = eqn (CS02 ∷ Z1 ∷ []) (Z1 ∷ CS02 ∷ []) (wn 1063 W)

-- pass [CS03] [Z1]: 9 steps
lem-pass-CS03-vs-Z1 : ⟪ (CS03 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z1 = derive (CS03 ∷ Z1 ∷ []) (Z1 ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw 1 q41 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q42 ∷
   rw⁻ 0 q41 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q44 : Eqn
  q44 = eqn (Sw01 ∷ Z2 ∷ []) (Z2 ∷ Sw01 ∷ []) (low-comm (Swap) (Z))
  q45 : Eqn
  q45 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q46 : Eqn
  q46 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q47 : Eqn
  q47 = eqn (CS13 ∷ Z2 ∷ []) (Z2 ∷ CS13 ∷ []) (wn 1064 W)
  q48 : Eqn
  q48 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q49 : Eqn
  q49 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)

-- pass [CS03] [Z2]: 15 steps
lem-pass-CS03-vs-Z2 : ⟪ (CS03 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z2 = derive (CS03 ∷ Z2 ∷ []) (Z2 ∷ CS03 ∷ [])
  (rw 2 q43 ∷
   rw⁻ 1 q44 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw 1 q46 ∷
   rw⁻ 0 q45 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q47 ∷
   rw 0 q44 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q45 ∷
   rw 2 q48 ∷
   rw 3 q45 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (Z3 ∷ Sw23 ∷ []) (Sw23 ∷ Z2 ∷ []) (wn 1065 W)
  q51 : Eqn
  q51 = eqn (CS02 ∷ Z2 ∷ []) (Z2 ∷ CS02 ∷ []) (wn 1066 W)
  q52 : Eqn
  q52 = eqn (Sw23 ∷ Z2 ∷ []) (Z3 ∷ Sw23 ∷ []) (wn 371 W)

-- pass [CS03] [Z3]: 9 steps
lem-pass-CS03-vs-Z3 : ⟪ (CS03 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Z3 = derive (CS03 ∷ Z3 ∷ []) (Z3 ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw 1 q50 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q51 ∷
   rw 0 q52 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (CS02 ∷ CZ12 ∷ []) (CZ12 ∷ CS02 ∷ []) (wn 552 W)

-- pass [CS03] [CZ13]: 11 steps
lem-pass-CS03-vs-CZ13 : ⟪ (CS03 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CZ13 = derive (CS03 ∷ CZ13 ∷ []) (CZ13 ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q53 ∷
   rw 2 q1 ∷
   re 0 3 (CZ13 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ))
  q55 : Eqn
  q55 = eqn (CS13 ∷ CZ23 ∷ []) (CZ23 ∷ CS13 ∷ []) (wn 890 W)

-- pass [CS03] [CZ23]: 15 steps
lem-pass-CS03-vs-CZ23 : ⟪ (CS03 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CZ23 = derive (CS03 ∷ CZ23 ∷ []) (CZ23 ∷ CS03 ∷ [])
  (rw 2 q43 ∷
   rw⁻ 1 q54 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw 1 q46 ∷
   rw⁻ 0 q45 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q55 ∷
   rw 0 q54 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q45 ∷
   rw 2 q48 ∷
   rw 3 q45 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q49 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (Toff012 ∷ ι ∷ []) (ι ∷ Toff012 ∷ []) (wn 1067 W)

-- pass [TOFF012] [iI]: 1 steps
lem-pass-TOFF012-vs-iI : ⟪ (Toff012 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-iI = derive (Toff012 ∷ ι ∷ []) (ι ∷ Toff012 ∷ [])
  (rw 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (Toff012 ∷ Z1 ∷ []) (Z1 ∷ Toff012 ∷ []) (wn 1068 W)

-- pass [TOFF012] [Z1]: 1 steps
lem-pass-TOFF012-vs-Z1 : ⟪ (Toff012 ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z1 = derive (Toff012 ∷ Z1 ∷ []) (Z1 ∷ Toff012 ∷ [])
  (rw 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (Toff012 ∷ Z2 ∷ []) (Z2 ∷ Toff012 ∷ []) (wn 1069 W)

-- pass [TOFF012] [Z2]: 1 steps
lem-pass-TOFF012-vs-Z2 : ⟪ (Toff012 ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z2 = derive (Toff012 ∷ Z2 ∷ []) (Z2 ∷ Toff012 ∷ [])
  (rw 0 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (Toff012 ∷ CZ12 ∷ []) (CZ12 ∷ Toff012 ∷ []) (wn 1070 W)

-- pass [TOFF012] [CZ12]: 1 steps
lem-pass-TOFF012-vs-CZ12 : ⟪ (Toff012 ∷ CZ12 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CZ12 = derive (Toff012 ∷ CZ12 ∷ []) (CZ12 ∷ Toff012 ∷ [])
  (rw 0 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (Toff012 ∷ Z3 ∷ []) (Z3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (Z))

-- pass [TOFF012] [Z3]: 1 steps
lem-pass-TOFF012-vs-Z3 : ⟪ (Toff012 ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Z3 = derive (Toff012 ∷ Z3 ∷ []) (Z3 ∷ Toff012 ∷ [])
  (rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (CCZ012 ∷ []) (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (wn 100 W)
  q62 : Eqn
  q62 = eqn (CS12 ∷ CZ23 ∷ []) (CZ23 ∷ CS12 ∷ []) (wn 909 W)
  q63 : Eqn
  q63 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q64 : Eqn
  q64 = eqn (CX21 ∷ CZ23 ∷ []) (CZ23 ∷ CX21 ∷ []) (wn 908 W)
  q65 : Eqn
  q65 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q66 : Eqn
  q66 = eqn (CS01⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CZ))
  q67 : Eqn
  q67 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q68 : Eqn
  q68 = eqn (CS01 ∷ CX20 ∷ CS01⁻ ∷ CX20 ∷ CS12 ∷ []) (CCZ012 ∷ []) (wn 104 W)

-- comm CCZ012 CZ23: 19 steps
lem-comm-CCZ012-CZ23 : ⟪ (CCZ012 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CZ23 = derive (CCZ012 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ012 ∷ [])
  (rw 0 q61 ∷
   rw 4 q62 ∷
   rw 5 q43 ∷
   rw⁻ 4 q54 ∷
   rw 3 q63 ∷
   rw 4 q64 ∷
   rw 3 q54 ∷
   rw 4 q65 ∷
   rw 5 q49 ∷
   rw 2 q66 ∷
   rw 3 q43 ∷
   rw⁻ 2 q54 ∷
   rw 1 q63 ∷
   rw 2 q64 ∷
   rw 1 q54 ∷
   rw 2 q65 ∷
   rw 3 q49 ∷
   rw 0 q67 ∷
   rw 1 q68 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = eqn (CS02⁻ ∷ ι ∷ []) (ι ∷ CS02⁻ ∷ []) (wn 1071 W)

-- pass [CSd03] [iI]: 9 steps
lem-pass-CSd03-vs-iI : ⟪ (CS03⁻ ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-iI = derive (CS03⁻ ∷ ι ∷ []) (ι ∷ CS03⁻ ∷ [])
  (rw 2 q1 ∷
   rw 1 q16 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q69 ∷
   rw⁻ 0 q16 ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (CS02⁻ ∷ Z1 ∷ []) (Z1 ∷ CS02⁻ ∷ []) (wn 1072 W)

-- pass [CSd03] [Z1]: 9 steps
lem-pass-CSd03-vs-Z1 : ⟪ (CS03⁻ ∷ Z1 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z1 = derive (CS03⁻ ∷ Z1 ∷ []) (Z1 ∷ CS03⁻ ∷ [])
  (rw 2 q1 ∷
   rw 1 q41 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q70 ∷
   rw⁻ 0 q41 ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q72 : Eqn
  q72 = eqn (CS13⁻ ∷ Z2 ∷ []) (Z2 ∷ CS13⁻ ∷ []) (wn 1073 W)
  q73 : Eqn
  q73 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)

-- pass [CSd03] [Z2]: 15 steps
lem-pass-CSd03-vs-Z2 : ⟪ (CS03⁻ ∷ Z2 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z2 = derive (CS03⁻ ∷ Z2 ∷ []) (Z2 ∷ CS03⁻ ∷ [])
  (rw 2 q43 ∷
   rw⁻ 1 q44 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw 1 q71 ∷
   rw⁻ 0 q45 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 q72 ∷
   rw 0 q44 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q45 ∷
   rw 2 q73 ∷
   rw 3 q45 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q49 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = eqn (CS02⁻ ∷ Z2 ∷ []) (Z2 ∷ CS02⁻ ∷ []) (wn 1074 W)

-- pass [CSd03] [Z3]: 9 steps
lem-pass-CSd03-vs-Z3 : ⟪ (CS03⁻ ∷ Z3 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Z3 = derive (CS03⁻ ∷ Z3 ∷ []) (Z3 ∷ CS03⁻ ∷ [])
  (rw 2 q1 ∷
   rw 1 q50 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q74 ∷
   rw 0 q52 ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = eqn (CS02⁻ ∷ CZ12 ∷ []) (CZ12 ∷ CS02⁻ ∷ []) (wn 551 W)

-- pass [CSd03] [CZ13]: 11 steps
lem-pass-CSd03-vs-CZ13 : ⟪ (CS03⁻ ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CZ13 = derive (CS03⁻ ∷ CZ13 ∷ []) (CZ13 ∷ CS03⁻ ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q75 ∷
   rw 2 q1 ∷
   re 0 3 (CZ13 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q4 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (CS13⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CS13⁻ ∷ []) (wn 1075 W)

-- pass [CSd03] [CZ23]: 15 steps
lem-pass-CSd03-vs-CZ23 : ⟪ (CS03⁻ ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CZ23 = derive (CS03⁻ ∷ CZ23 ∷ []) (CZ23 ∷ CS03⁻ ∷ [])
  (rw 2 q43 ∷
   rw⁻ 1 q54 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw 1 q71 ∷
   rw⁻ 0 q45 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 q76 ∷
   rw 0 q54 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q45 ∷
   rw 2 q73 ∷
   rw 3 q45 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q49 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = eqn (CK10⁻ ∷ CX23 ∷ []) (CX23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q78 : Eqn
  q78 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q79 : Eqn
  q79 = eqn (CS12⁻ ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS12⁻ ∷ []) (wn 1076 W)
  q80 : Eqn
  q80 = eqn (CS12 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CS12 ∷ []) (wn 1077 W)

-- pass [CCZ123] [X1 CKd10 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CKd10-X1 : ⟪ (CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CKd10-X1 = derive (CCZ123 ∷ X1 ∷ CK10⁻ ∷ X1 ∷ []) (X1 ∷ CK10⁻ ∷ X1 ∷ CCZ123 ∷ [])
  (rw 0 q31 ∷
   rw⁻ 4 q32 ∷
   rw⁻ 5 q77 ∷
   rw⁻ 6 q32 ∷
   rw 7 q1 ∷
   rw 6 q2 ∷
   rw 5 q78 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q79 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q78 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 7 q4 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 3 q77 ∷
   rw⁻ 4 q32 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q78 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q80 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q78 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q4 ∷
   rw 0 q80 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q82 : Eqn
  q82 = eqn (CS12⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS12⁻ ∷ []) (wn 1078 W)
  q83 : Eqn
  q83 = eqn (CS12 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CS12 ∷ []) (wn 1079 W)

-- pass [CCZ123] [X1 CSd01 X1]: 35 steps
lem-pass-CCZ123-vs-X1-CSd01-X1 : ⟪ (CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-X1-CSd01-X1 = derive (CCZ123 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ CCZ123 ∷ [])
  (rw 0 q31 ∷
   rw⁻ 4 q32 ∷
   rw⁻ 5 q81 ∷
   rw⁻ 6 q32 ∷
   rw 7 q1 ∷
   rw 6 q2 ∷
   rw 5 q3 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q82 ∷
   rw⁻ 3 q2 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 7 q4 ∷
   rw⁻ 2 q32 ∷
   rw⁻ 3 q81 ∷
   rw⁻ 4 q32 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q83 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q4 ∷
   rw 0 q83 ∷
   rw 3 q36 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = eqn (CK13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CK23⁻ ∷ []) (wn 1080 W)
  q85 : Eqn
  q85 = eqn (CS01 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S • CK₀₁)))
  q86 : Eqn
  q86 = eqn (CK23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CK13⁻ ∷ []) (wn 1081 W)

-- pass [X1 CKd13 X1] [CS02]: 7 steps
lem-pass-X1-CKd13-X1-vs-CS02 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CS02 = derive (X1 ∷ CK13⁻ ∷ X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  (rw 2 q10 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q84 ∷
   rw⁻ 2 q85 ∷
   rw 3 q86 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 0 q10 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = eqn (X1 ∷ CK12⁻ ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CK12⁻ ∷ X1 ∷ []) (wn 1082 W)

-- pass [X1 CKd13 X1] [TOFF013]: 65 steps
lem-pass-X1-CKd13-X1-vs-TOFF013 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-TOFF013 = derive (X1 ∷ CK13⁻ ∷ X1 ∷ Toff013 ∷ []) (Toff013 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q14 ∷
   rw⁻ 10 q16 ∷
   rw 11 q4 ∷
   rw 10 q16 ∷
   rw 9 q14 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw 3 q14 ∷
   rw 4 q17 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 0 q2 ∷
   rw 1 q87 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q14 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q15 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q14 ∷
   rw⁻ 7 q16 ∷
   rw 0 q1 ∷
   rw⁻ 1 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw⁻ 3 q15 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q17 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CK13⁻ ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 4 q4 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = eqn (CS01⁻ ∷ CK23⁻ ∷ []) (CK23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((S • CK₀₁)))

-- pass [X1 CKd13 X1] [CSd02]: 7 steps
lem-pass-X1-CKd13-X1-vs-CSd02 : ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CKd13-X1-vs-CSd02 = derive (X1 ∷ CK13⁻ ∷ X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ CK13⁻ ∷ X1 ∷ [])
  (rw 2 q19 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q84 ∷
   rw⁻ 2 q88 ∷
   rw 3 q86 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw 0 q19 ∷ []) Eq.refl
