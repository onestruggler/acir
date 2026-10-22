{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D387 (W : Ws) where

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
  q1 = wE 1103 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX21 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX21 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X2 TOFF102 X0 X2]: 1 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-TOFF102-X0-X2 : ⟪ (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX21-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX21-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X2-TOFF102-X0-X2 = derive (CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ []) (X0 ∷ X2 ∷ Toff102 ∷ X0 ∷ X2 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CX21 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 0 q1 ∷ []) Eq.refl

private
  q2 : Eqn
  q2 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q3 : Eqn
  q3 = eqn (CK10 ∷ CX32 ∷ []) (CX32 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CX₁₀))
  q4 : Eqn
  q4 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q5 : Eqn
  q5 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q6 : Eqn
  q6 = wE 537 W
  q7 : Eqn
  q7 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q8 : Eqn
  q8 = eqn (S1 ∷ CX32 ∷ []) (CX32 ∷ S1 ∷ []) (low-comm ((S ↑)) (CX₁₀))
  q9 : Eqn
  q9 = wE 5 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 140 W
  q14 : Eqn
  q14 = wE 1104 W
  q15 : Eqn
  q15 = wE 142 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = wE 1105 W
  q19 : Eqn
  q19 = wE 27 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CX32 X3]: 179 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CX32-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CX32-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX31 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ [])
  (rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q2 ∷
   rw 27 q2 ∷
   rw 28 q3 ∷
   rw 29 q2 ∷
   rw 26 q4 ∷
   rw 27 q5 ∷
   rw 28 q4 ∷
   rw 25 q2 ∷
   rw 26 q3 ∷
   rw 27 q2 ∷
   rw 24 q4 ∷
   rw 25 q5 ∷
   rw 26 q4 ∷
   rw 23 q4 ∷
   rw 24 q5 ∷
   rw 25 q4 ∷
   rw 22 q6 ∷
   rw 21 q4 ∷
   rw 22 q5 ∷
   rw 23 q4 ∷
   rw 20 q4 ∷
   rw 21 q5 ∷
   rw 22 q4 ∷
   rw 19 q4 ∷
   rw 20 q5 ∷
   rw 21 q4 ∷
   rw 18 q4 ∷
   rw 19 q5 ∷
   rw 20 q4 ∷
   rw 17 q4 ∷
   rw 18 q5 ∷
   rw 19 q4 ∷
   rw 16 q4 ∷
   rw 17 q5 ∷
   rw 18 q4 ∷
   rw 15 q7 ∷
   rw 16 q8 ∷
   rw 17 q7 ∷
   rw 14 q2 ∷
   rw 15 q3 ∷
   rw 16 q2 ∷
   rw 13 q4 ∷
   rw 14 q5 ∷
   rw 15 q4 ∷
   rw 12 q4 ∷
   rw 13 q5 ∷
   rw 14 q4 ∷
   rw 11 q4 ∷
   rw 12 q5 ∷
   rw 13 q4 ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   rw 9 q2 ∷
   rw 10 q3 ∷
   rw 11 q2 ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 10 q7 ∷
   rw 7 q2 ∷
   rw 8 q3 ∷
   rw 9 q2 ∷
   rw 6 q6 ∷
   rw 9 q9 ∷
   rw⁻ 8 q10 ∷
   rw⁻ 7 q11 ∷
   rw⁻ 6 q10 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw 6 q13 ∷
   rw⁻ 5 q12 ∷
   re 6 3 (CK31 ∷ []) ∷
   rw 6 q14 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q10 ∷
   re 9 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q15 ∷
   rw 10 q12 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q16 ∷
   rw 8 q9 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q11 ∷
   rw⁻ 5 q10 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q12 ∷
   rw 5 q13 ∷
   rw⁻ 4 q12 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 5 q14 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q10 ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q15 ∷
   rw 9 q12 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q16 ∷
   rw 7 q9 ∷
   rw⁻ 6 q10 ∷
   rw⁻ 5 q11 ∷
   rw⁻ 4 q10 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q12 ∷
   rw 4 q17 ∷
   rw⁻ 3 q12 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 5 q10 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q19 ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q16 ∷
   rw 6 q9 ∷
   rw⁻ 5 q10 ∷
   rw⁻ 4 q11 ∷
   rw⁻ 3 q10 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw 3 q13 ∷
   rw⁻ 2 q12 ∷
   re 3 3 (CK31 ∷ []) ∷
   rw 3 q14 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 5 q12 ∷
   rw 6 q15 ∷
   rw 7 q12 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q9 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 3 q11 ∷
   rw⁻ 2 q10 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q12 ∷
   rw 2 q17 ∷
   rw⁻ 1 q12 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q18 ∷
   rw 1 q10 ∷
   rw 2 q11 ∷
   rw 3 q10 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q12 ∷
   rw 5 q19 ∷
   rw 6 q12 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q16 ∷
   rw 4 q9 ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q11 ∷
   rw⁻ 1 q10 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q12 ∷
   rw 1 q17 ∷
   rw⁻ 0 q12 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q18 ∷
   rw 0 q10 ∷
   rw 1 q11 ∷
   rw 2 q10 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q12 ∷
   rw 4 q19 ∷
   rw 5 q12 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q16 ∷ []) Eq.refl

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CX32 X3]: 185 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CX32-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CX32-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CX32 ∷ X3 ∷ []) (X3 ∷ CX32 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 30 q4 ∷
   rw 31 q5 ∷
   rw 32 q4 ∷
   rw 29 q4 ∷
   rw 30 q5 ∷
   rw 31 q4 ∷
   rw 28 q2 ∷
   rw 29 q3 ∷
   rw 30 q2 ∷
   rw 27 q4 ∷
   rw 28 q5 ∷
   rw 29 q4 ∷
   rw 26 q4 ∷
   rw 27 q5 ∷
   rw 28 q4 ∷
   rw 25 q4 ∷
   rw 26 q5 ∷
   rw 27 q4 ∷
   rw 24 q6 ∷
   rw 23 q4 ∷
   rw 24 q5 ∷
   rw 25 q4 ∷
   rw 22 q4 ∷
   rw 23 q5 ∷
   rw 24 q4 ∷
   rw 21 q4 ∷
   rw 22 q5 ∷
   rw 23 q4 ∷
   rw 20 q4 ∷
   rw 21 q5 ∷
   rw 22 q4 ∷
   rw 19 q4 ∷
   rw 20 q5 ∷
   rw 21 q4 ∷
   rw 18 q4 ∷
   rw 19 q5 ∷
   rw 20 q4 ∷
   rw 17 q4 ∷
   rw 18 q5 ∷
   rw 19 q4 ∷
   rw 16 q4 ∷
   rw 17 q5 ∷
   rw 18 q4 ∷
   rw 15 q4 ∷
   rw 16 q5 ∷
   rw 17 q4 ∷
   rw 14 q7 ∷
   rw 15 q8 ∷
   rw 16 q7 ∷
   rw 13 q2 ∷
   rw 14 q3 ∷
   rw 15 q2 ∷
   rw 12 q4 ∷
   rw 13 q5 ∷
   rw 14 q4 ∷
   rw 11 q4 ∷
   rw 12 q5 ∷
   rw 13 q4 ∷
   rw 10 q4 ∷
   rw 11 q5 ∷
   rw 12 q4 ∷
   rw 9 q4 ∷
   rw 10 q5 ∷
   rw 11 q4 ∷
   rw 8 q4 ∷
   rw 9 q5 ∷
   rw 10 q4 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q4 ∷
   rw 6 q6 ∷
   rw 9 q9 ∷
   rw⁻ 8 q10 ∷
   rw⁻ 7 q11 ∷
   rw⁻ 6 q10 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw 6 q17 ∷
   rw⁻ 5 q12 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 6 q18 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q10 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q19 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q16 ∷
   rw 8 q9 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q11 ∷
   rw⁻ 5 q10 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q12 ∷
   rw 5 q17 ∷
   rw⁻ 4 q12 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   rw 4 q10 ∷
   rw 5 q11 ∷
   rw 6 q10 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q19 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q16 ∷
   rw 7 q9 ∷
   rw⁻ 6 q10 ∷
   rw⁻ 5 q11 ∷
   rw⁻ 4 q10 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q12 ∷
   rw 4 q13 ∷
   rw⁻ 3 q12 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 4 q14 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 5 q10 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q15 ∷
   rw 8 q12 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q16 ∷
   rw 6 q9 ∷
   rw⁻ 5 q10 ∷
   rw⁻ 4 q11 ∷
   rw⁻ 3 q10 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw 3 q17 ∷
   rw⁻ 2 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 3 q18 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q12 ∷
   rw 6 q19 ∷
   rw 7 q12 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q9 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 3 q11 ∷
   rw⁻ 2 q10 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q12 ∷
   rw 2 q17 ∷
   rw⁻ 1 q12 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q18 ∷
   rw 1 q10 ∷
   rw 2 q11 ∷
   rw 3 q10 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q12 ∷
   rw 5 q19 ∷
   rw 6 q12 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q16 ∷
   rw 4 q9 ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q11 ∷
   rw⁻ 1 q10 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q12 ∷
   rw 1 q17 ∷
   rw⁻ 0 q12 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q18 ∷
   rw 0 q10 ∷
   rw 1 q11 ∷
   rw 2 q10 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q12 ∷
   rw 4 q19 ∷
   rw 5 q12 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q16 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1106 W
  q21 : Eqn
  q21 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q23 : Eqn
  q23 = wE 30 W
  q24 : Eqn
  q24 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q25 : Eqn
  q25 = wE 122 W
  q26 : Eqn
  q26 = wE 127 W
  q27 : Eqn
  q27 = wE 74 W
  q28 : Eqn
  q28 = wE 334 W
  q29 : Eqn
  q29 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q30 : Eqn
  q30 = wE 1107 W
  q31 : Eqn
  q31 = wE 317 W
  q32 : Eqn
  q32 = wE 24 W
  q33 : Eqn
  q33 = wE 25 W
  q34 : Eqn
  q34 = wE 124 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X3 TOFF203 X0 X3]: 175 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF203-X0-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X3-TOFF203-X0-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ Toff203 ∷ X0 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 34 q9 ∷
   rw⁻ 33 q10 ∷
   rw 32 q20 ∷
   re 31 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 32 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 31 q21 ∷
   rw 32 q22 ∷
   rw 33 q23 ∷
   rw 34 q24 ∷
   rw 35 q23 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q12 ∷
   rw 37 q19 ∷
   rw 38 q12 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 37 q21 ∷
   rw 38 q25 ∷
   rw 39 q16 ∷
   rw 38 q26 ∷
   rw⁻ 37 q21 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 38 q12 ∷
   rw 37 q17 ∷
   rw⁻ 36 q12 ∷
   re 37 3 (CS13 ∷ []) ∷
   rw 35 q27 ∷
   rw⁻ 34 q24 ∷
   rw 33 q27 ∷
   rw⁻ 32 q22 ∷
   rw⁻ 31 q21 ∷
   rw 32 q28 ∷
   re 32 8 (Toff213 ∷ []) ∷
   rw⁻ 30 q10 ∷
   rw 29 q20 ∷
   rw 28 q13 ∷
   rw 27 q13 ∷
   rw 26 q17 ∷
   rw 25 q13 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   rw⁻ 22 q11 ∷
   rw 21 q17 ∷
   rw 20 q17 ∷
   rw 19 q17 ∷
   rw 18 q17 ∷
   rw 17 q17 ∷
   rw 16 q17 ∷
   rw⁻ 15 q29 ∷
   rw 14 q13 ∷
   rw 13 q17 ∷
   rw 12 q17 ∷
   rw 11 q17 ∷
   rw⁻ 10 q29 ∷
   rw 9 q13 ∷
   rw⁻ 8 q29 ∷
   rw 7 q13 ∷
   rw⁻ 6 q11 ∷
   re 5 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q12 ∷
   rw 6 q13 ∷
   rw⁻ 5 q12 ∷
   re 6 3 (CK31 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q12 ∷
   rw 5 q13 ∷
   rw⁻ 4 q12 ∷
   re 5 3 (CK31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q12 ∷
   rw 4 q17 ∷
   rw⁻ 3 q12 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q12 ∷
   rw 3 q13 ∷
   rw⁻ 2 q12 ∷
   re 3 3 (CK31 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q12 ∷
   rw 2 q17 ∷
   rw⁻ 1 q12 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q12 ∷
   rw 1 q17 ∷
   rw⁻ 0 q12 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q30 ∷
   rw 0 q31 ∷
   rw 1 q10 ∷
   re 3 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   rw 5 q24 ∷
   rw 6 q23 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q19 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q21 ∷
   rw 9 q25 ∷
   rw 2 q9 ∷
   rw 3 q21 ∷
   rw 4 q22 ∷
   rw 5 q32 ∷
   rw 6 q24 ∷
   rw 7 q32 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q33 ∷
   rw 10 q12 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q34 ∷
   rw 3 q28 ∷
   re 3 8 (Toff213 ∷ []) ∷
   re 2 3 (Toff203 ∷ []) ∷
   rw 3 q31 ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q12 ∷
   rw 6 q19 ∷
   rw 7 q12 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q19 ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q15 ∷
   rw 9 q12 ∷
   re 7 3 (CK30 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q19 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q15 ∷
   rw 11 q12 ∷
   re 9 3 (CK30 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q15 ∷
   rw 12 q12 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q11 ∷
   rw 12 q15 ∷
   rw 13 q29 ∷
   rw 14 q15 ∷
   rw 15 q29 ∷
   rw 16 q19 ∷
   rw 17 q19 ∷
   rw 18 q19 ∷
   rw 19 q15 ∷
   rw 20 q29 ∷
   rw 21 q19 ∷
   rw 22 q19 ∷
   rw 23 q19 ∷
   rw 24 q19 ∷
   rw 25 q19 ∷
   rw 26 q19 ∷
   rw 27 q11 ∷
   rw 28 q19 ∷
   rw 29 q19 ∷
   rw 30 q15 ∷
   rw 31 q19 ∷
   rw 32 q15 ∷
   rw 33 q15 ∷
   rw 34 q16 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 1 W
  q36 : Eqn
  q36 = wE 20 W
  q37 : Eqn
  q37 = eqn (CZ01 ∷ CS23 ∷ []) (CS23 ∷ CZ01 ∷ []) (low-comm (CZ) (CS))
  q38 : Eqn
  q38 = wE 49 W
  q39 : Eqn
  q39 = wE 3 W

-- pass [CZ02] [CS13]: 15 steps
lem-pass-CZ02-vs-CS13 : ⟪ (CZ02 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CZ02 ∷ []) ⟫ʷ
lem-pass-CZ02-vs-CS13 = derive (CZ02 ∷ CS13 ∷ []) (CS13 ∷ CZ02 ∷ [])
  (re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   re 1 3 (CZ03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CZ01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q35 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 4 q36 ∷
   rw 3 q37 ∷
   rw 2 q38 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q39 ∷
   re 2 5 (CZ03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 4 q39 ∷
   re 0 3 (CS13 ∷ []) ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 1018 W
  q41 : Eqn
  q41 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q42 : Eqn
  q42 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q43 : Eqn
  q43 = wE 390 W
  q44 : Eqn
  q44 = wE 257 W
  q45 : Eqn
  q45 = wE 389 W
  q46 : Eqn
  q46 = wE 258 W

-- distribute Gad(t=1, W=(2, 3), d=1, e=1) TOFF102 CS13 TOFF102 CSd13: 15 steps
lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13 ∷ X3 ∷ X2 ∷ Toff102 ∷ X2 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 3 q40 ∷
   rw 8 q40 ∷
   rw 13 q40 ∷
   rw⁻ 1 q41 ∷
   rw⁻ 2 q42 ∷
   rw 3 q43 ∷
   rw 3 q42 ∷
   rw 4 q44 ∷
   rw 5 q45 ∷
   rw⁻ 7 q41 ∷
   rw⁻ 8 q42 ∷
   rw 9 q43 ∷
   rw 9 q42 ∷
   rw 10 q46 ∷
   rw 11 q45 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 1108 W
  q48 : Eqn
  q48 = wE 1109 W

-- b2g 0011PP2: 3 steps
lem-b2g-0011PP2 : ⟪ (X2 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X3 ∷ []) ⟫ʷ
lem-b2g-0011PP2 = derive (X2 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ K2 ∷ S2 ∷ S2 ∷ K2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ K2 ∷ S2⁻ ∷ S2⁻ ∷ K2⁻ ∷ X3 ∷ [])
  (rw 0 q42 ∷
   rw 1 q47 ∷
   rw 9 q48 ∷ []) Eq.refl

-- pass [CZ01] [CS23]: 1 steps
lem-pass-CZ01-vs-CS23 : ⟪ (CZ01 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CZ01 ∷ []) ⟫ʷ
lem-pass-CZ01-vs-CS23 = derive (CZ01 ∷ CS23 ∷ []) (CS23 ∷ CZ01 ∷ [])
  (rw 0 q37 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ []) (low-comm ((X ↑)) (X))
  q50 : Eqn
  q50 = eqn (X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((X ↑)))
  q51 : Eqn
  q51 = wE 1110 W
  q52 : Eqn
  q52 = wE 1111 W

-- b2g 0111PP1: 4 steps
lem-b2g-0111PP1 : ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-0111PP1 = derive (X1 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K1 ∷ S1 ∷ S1 ∷ K1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ K1 ∷ S1⁻ ∷ S1⁻ ∷ K1⁻ ∷ X2 ∷ X3 ∷ [])
  (rw 0 q49 ∷
   rw 1 q50 ∷
   rw 2 q51 ∷
   rw 10 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q54 : Eqn
  q54 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q55 : Eqn
  q55 = wE 1112 W
  q56 : Eqn
  q56 = wE 1113 W

-- b2g 1011PP0: 4 steps
lem-b2g-1011PP0 : ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-b2g-1011PP0 = derive (X0 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ K0 ∷ S0 ∷ S0 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ S0⁻ ∷ S0⁻ ∷ K0⁻ ∷ X2 ∷ X3 ∷ [])
  (rw 0 q53 ∷
   rw 1 q54 ∷
   rw 2 q55 ∷
   rw 10 q56 ∷ []) Eq.refl
