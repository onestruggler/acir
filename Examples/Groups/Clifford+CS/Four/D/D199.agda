{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D199 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 725 W)
  q8 : Eqn
  q8 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CK30 X3]: 89 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK30-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK30-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   rw 31 q2 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw 14 q6 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 23 q4 ∷
   rw⁻ 24 q4 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q4 ∷
   rw 29 q1 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 30 q4 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q4 ∷
   rw⁻ 33 q4 ∷
   rw 34 q3 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = eqn (CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ X2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX21 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) (wn 736 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CKd30 X3]: 89 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd30-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd30-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 34 q1 ∷
   rw 33 q2 ∷
   re 32 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   rw 31 q2 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   re 24 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw 14 q6 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 1 q9 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (CK30⁻ ∷ []) ∷
   rw 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CX31 ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q4 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q4 ∷
   rw⁻ 14 q4 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 18 q4 ∷
   rw⁻ 19 q4 ∷
   rw⁻ 20 q4 ∷
   rw⁻ 21 q4 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 23 q4 ∷
   rw⁻ 24 q4 ∷
   rw⁻ 25 q4 ∷
   rw⁻ 26 q4 ∷
   rw 29 q1 ∷
   re 27 3 (CX31 ∷ []) ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   rw⁻ 30 q4 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q4 ∷
   rw⁻ 33 q4 ∷
   rw 34 q3 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (CS01 ∷ X3 ∷ []) (X3 ∷ CS01 ∷ []) (low-comm (CS) ((X ↑)))
  q11 : Eqn
  q11 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q12 : Eqn
  q12 = eqn (CK10 ∷ X3 ∷ []) (X3 ∷ CK10 ∷ []) (low-comm (CK₁₀) ((X ↑)))
  q13 : Eqn
  q13 = eqn (CK10 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((S ↑ • CK₁₀)))
  q14 : Eqn
  q14 = eqn (CX31 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CX31 ∷ []) (wn 547 W)
  q15 : Eqn
  q15 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q16 : Eqn
  q16 = eqn (S1 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ S1 ∷ []) (low-comm ((S ↑)) ((S ↑ • CK₁₀)))
  q17 : Eqn
  q17 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))
  q20 : Eqn
  q20 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q22 : Eqn
  q22 = eqn (CS13 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ []) (wn 549 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q24 : Eqn
  q24 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q25 : Eqn
  q25 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q26 : Eqn
  q26 = eqn (CK31 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CK31 ∷ []) (wn 548 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CKd32 X3]: 185 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3 : ⟪ (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd32-X3 = derive (CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ [])
  (rw 30 q10 ∷
   rw 31 q11 ∷
   rw 32 q10 ∷
   rw 29 q10 ∷
   rw 30 q11 ∷
   rw 31 q10 ∷
   rw 28 q12 ∷
   rw 29 q13 ∷
   rw 30 q12 ∷
   rw 27 q10 ∷
   rw 28 q11 ∷
   rw 29 q10 ∷
   rw 26 q10 ∷
   rw 27 q11 ∷
   rw 28 q10 ∷
   rw 25 q10 ∷
   rw 26 q11 ∷
   rw 27 q10 ∷
   rw 24 q14 ∷
   rw 23 q10 ∷
   rw 24 q11 ∷
   rw 25 q10 ∷
   rw 22 q10 ∷
   rw 23 q11 ∷
   rw 24 q10 ∷
   rw 21 q10 ∷
   rw 22 q11 ∷
   rw 23 q10 ∷
   rw 20 q10 ∷
   rw 21 q11 ∷
   rw 22 q10 ∷
   rw 19 q10 ∷
   rw 20 q11 ∷
   rw 21 q10 ∷
   rw 18 q10 ∷
   rw 19 q11 ∷
   rw 20 q10 ∷
   rw 17 q10 ∷
   rw 18 q11 ∷
   rw 19 q10 ∷
   rw 16 q10 ∷
   rw 17 q11 ∷
   rw 18 q10 ∷
   rw 15 q10 ∷
   rw 16 q11 ∷
   rw 17 q10 ∷
   rw 14 q15 ∷
   rw 15 q16 ∷
   rw 16 q15 ∷
   rw 13 q12 ∷
   rw 14 q13 ∷
   rw 15 q12 ∷
   rw 12 q10 ∷
   rw 13 q11 ∷
   rw 14 q10 ∷
   rw 11 q10 ∷
   rw 12 q11 ∷
   rw 13 q10 ∷
   rw 10 q10 ∷
   rw 11 q11 ∷
   rw 12 q10 ∷
   rw 9 q10 ∷
   rw 10 q11 ∷
   rw 11 q10 ∷
   rw 8 q10 ∷
   rw 9 q11 ∷
   rw 10 q10 ∷
   rw 7 q10 ∷
   rw 8 q11 ∷
   rw 9 q10 ∷
   rw 6 q14 ∷
   rw 9 q17 ∷
   rw⁻ 8 q18 ∷
   rw⁻ 7 q19 ∷
   rw⁻ 6 q18 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q20 ∷
   rw 6 q21 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 6 q22 ∷
   rw 5 q18 ∷
   rw 6 q19 ∷
   rw 7 q18 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q20 ∷
   rw 9 q23 ∷
   rw 10 q20 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q24 ∷
   rw 8 q17 ∷
   rw⁻ 7 q18 ∷
   rw⁻ 6 q19 ∷
   rw⁻ 5 q18 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q20 ∷
   rw 5 q21 ∷
   rw⁻ 4 q20 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q22 ∷
   rw 4 q18 ∷
   rw 5 q19 ∷
   rw 6 q18 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q23 ∷
   rw 9 q20 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q24 ∷
   rw 7 q17 ∷
   rw⁻ 6 q18 ∷
   rw⁻ 5 q19 ∷
   rw⁻ 4 q18 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q20 ∷
   rw 4 q25 ∷
   rw⁻ 3 q20 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 4 q26 ∷
   rw 3 q18 ∷
   rw 4 q19 ∷
   rw 5 q18 ∷
   re 7 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 6 q20 ∷
   rw 7 q27 ∷
   rw 8 q20 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q17 ∷
   rw⁻ 5 q18 ∷
   rw⁻ 4 q19 ∷
   rw⁻ 3 q18 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q20 ∷
   rw 3 q21 ∷
   rw⁻ 2 q20 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 3 q22 ∷
   rw 2 q18 ∷
   rw 3 q19 ∷
   rw 4 q18 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q23 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q24 ∷
   rw 5 q17 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 3 q19 ∷
   rw⁻ 2 q18 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 2 q21 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q22 ∷
   rw 1 q18 ∷
   rw 2 q19 ∷
   rw 3 q18 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q20 ∷
   rw 5 q23 ∷
   rw 6 q20 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q24 ∷
   rw 4 q17 ∷
   rw⁻ 3 q18 ∷
   rw⁻ 2 q19 ∷
   rw⁻ 1 q18 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q20 ∷
   rw 1 q21 ∷
   rw⁻ 0 q20 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q22 ∷
   rw 0 q18 ∷
   rw 1 q19 ∷
   rw 2 q18 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q23 ∷
   rw 5 q20 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q24 ∷ []) Eq.refl
