{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D299 (W : Ws) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = wE 899 W
  q8 : Eqn
  q8 = eqn (ℓ "丵之") (ℓ "之丵") (low-comm ((S ↑ • CK₁₀)) (CZ))
  q9 : Eqn
  q9 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q10 : Eqn
  q10 = eqn (ℓ "临之") (ℓ "之临") (low-comm (CK₁₀) (CZ))
  q11 : Eqn
  q11 = wE 900 W
  q12 : Eqn
  q12 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q13 : Eqn
  q13 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q14 : Eqn
  q14 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q15 : Eqn
  q15 = wE 901 W
  q16 : Eqn
  q16 = wE 902 W

-- groups [CK10 CS01 CS01 CKd10] [X1 CK13 X1 CZ23 CS12 CS13 CX23 CSd13 CX23 X1 CKd13 X1]: 81 steps
lem-groups-CK10-CS01-CS01-CKd10-vs-X1-CK13-X1-CZ23-CS12-CS13-CX23-CSd13-CX23-X1-CKd13-X1 : ⟪ (ℓ "临丠丠丵丒乁丒之丶丽乌举乌丒乂丒") ⟫ʷ ≈ ⟪ (ℓ "丒乁丒之丶丽乌举乌丒乂丒临丠丠丵") ⟫ʷ
lem-groups-CK10-CS01-CS01-CKd10-vs-X1-CK13-X1-CZ23-CS12-CS13-CX23-CSd13-CX23-X1-CKd13-X1 = derive (ℓ "临丠丠丵丒乁丒之丶丽乌举乌丒乂丒") (ℓ "丒乁丒之丶丽乌举乌丒乂丒临丠丠丵")
  (rw 7 q1 ∷
   rw 6 q2 ∷
   re 5 1 (ℓ "乏为乏") ∷
   rw 7 q3 ∷
   rw 4 q2 ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw 0 q6 ∷
   rw 1 q7 ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乁") ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q6 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q4 ∷
   rw 7 q3 ∷
   rw 6 q8 ∷
   rw 5 q9 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q3 ∷
   rw 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q6 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q4 ∷
   rw 10 q3 ∷
   rw 9 q12 ∷
   rw 8 q13 ∷
   rw 7 q13 ∷
   rw 6 q14 ∷
   rw 12 q1 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 8 q15 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q6 ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q4 ∷
   rw 12 q3 ∷
   rw 11 q12 ∷
   rw 10 q13 ∷
   rw 9 q13 ∷
   rw 8 q14 ∷
   rw 16 q1 ∷
   rw 15 q2 ∷
   re 14 1 (ℓ "乏主乏") ∷
   rw 16 q3 ∷
   rw 13 q2 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   rw 10 q16 ∷
   rw⁻ 9 q2 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乂") ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q6 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q4 ∷
   rw 16 q3 ∷ []) Eq.refl
