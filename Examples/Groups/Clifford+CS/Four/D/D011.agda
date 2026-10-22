{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D011 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 196 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 238 W
  q9 : Eqn
  q9 = wE 175 W

-- pass [X3 CSd30 X3] [TOFF103]: 65 steps
lem-pass-X3-CSd30-X3-vs-TOFF103 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF103 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q2 ∷
   rw 4 q6 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q8 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (CS12 ∷ X3 ∷ []) (X3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (X))
  q11 : Eqn
  q11 = wE 20 W
  q12 : Eqn
  q12 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q13 : Eqn
  q13 = wE 49 W

-- pass [X3 CSd30 X3] [CS12]: 11 steps
lem-pass-X3-CSd30-X3-vs-CS12 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS12 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q10 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 4 q11 ∷
   rw 3 q12 ∷
   rw 2 q13 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CS03⁻ ∷ []) ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (CS12⁻ ∷ X3 ∷ []) (X3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (X))
  q15 : Eqn
  q15 = wE 21 W
  q16 : Eqn
  q16 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q17 : Eqn
  q17 = wE 51 W

-- pass [X3 CSd30 X3] [CSd12]: 11 steps
lem-pass-X3-CSd30-X3-vs-CSd12 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CSd12 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q14 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 4 q15 ∷
   rw 3 q16 ∷
   rw 2 q17 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CS03⁻ ∷ []) ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 239 W

-- pass [X3 CKd30 X3] [TOFF103]: 65 steps
lem-pass-X3-CKd30-X3-vs-TOFF103 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF103 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q2 ∷
   rw 4 q6 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q18 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (CK10⁻ ∷ CS23 ∷ []) (CS23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (CS))

-- pass [X3 CKd30 X3] [CS12]: 11 steps
lem-pass-X3-CKd30-X3-vs-CS12 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS12 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q10 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 4 q11 ∷
   rw 3 q19 ∷
   rw 2 q13 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CK30⁻ ∷ []) ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = eqn (CK10⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) ((CS • CS • CS)))

-- pass [X3 CKd30 X3] [CSd12]: 11 steps
lem-pass-X3-CKd30-X3-vs-CSd12 : ⟪ (X3 ∷ CK30⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CSd12 = derive (X3 ∷ CK30⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CK30⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q14 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 4 q15 ∷
   rw 3 q20 ∷
   rw 2 q17 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CK30⁻ ∷ []) ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 240 W

-- pass [X3 CK30 X3] [TOFF103]: 65 steps
lem-pass-X3-CK30-X3-vs-TOFF103 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF103 = derive (X3 ∷ CK30 ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q2 ∷
   rw 4 q6 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q21 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (CK10 ∷ CS23 ∷ []) (CS23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CS))

-- pass [X3 CK30 X3] [CS12]: 11 steps
lem-pass-X3-CK30-X3-vs-CS12 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-CS12 = derive (X3 ∷ CK30 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw⁻ 2 q10 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 4 q11 ∷
   rw 3 q22 ∷
   rw 2 q13 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CK30 ∷ []) ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = eqn (CK10 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CK10 ∷ []) (low-comm (CK₁₀) ((CS • CS • CS)))

-- pass [X3 CK30 X3] [CSd12]: 11 steps
lem-pass-X3-CK30-X3-vs-CSd12 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-CSd12 = derive (X3 ∷ CK30 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw⁻ 2 q14 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 4 q15 ∷
   rw 3 q23 ∷
   rw 2 q17 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CK30 ∷ []) ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 241 W

-- pass [X3 CS30 X3] [TOFF103]: 65 steps
lem-pass-X3-CS30-X3-vs-TOFF103 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF103 = derive (X3 ∷ CS03 ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q2 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q2 ∷
   rw 4 q6 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q24 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))

-- pass [X3 CS30 X3] [CS12]: 11 steps
lem-pass-X3-CS30-X3-vs-CS12 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS12 = derive (X3 ∷ CS03 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw⁻ 2 q10 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 4 q11 ∷
   rw 3 q25 ∷
   rw 2 q13 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CS03 ∷ []) ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))

-- pass [X3 CS30 X3] [CSd12]: 11 steps
lem-pass-X3-CS30-X3-vs-CSd12 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CSd12 = derive (X3 ∷ CS03 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw⁻ 2 q14 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 4 q15 ∷
   rw 3 q26 ∷
   rw 2 q17 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CS03 ∷ []) ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q28 : Eqn
  q28 = wE 242 W

-- pass [CS03] [S1]: 9 steps
lem-pass-CS03-vs-S1 : ⟪ (CS03 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-S1 = derive (CS03 ∷ S1 ∷ []) (S1 ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw 1 q27 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q28 ∷
   rw⁻ 0 q27 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q30 : Eqn
  q30 = wE 243 W

-- pass [CS03] [Sd1]: 9 steps
lem-pass-CS03-vs-Sd1 : ⟪ (CS03 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-Sd1 = derive (CS03 ∷ S1⁻ ∷ []) (S1⁻ ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw 1 q29 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q30 ∷
   rw⁻ 0 q29 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 244 W

-- pass [CS03] [X3 TOFF103 X3]: 65 steps
lem-pass-CS03-vs-X3-TOFF103-X3 : ⟪ (CS03 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-TOFF103-X3 = derive (CS03 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS03 ∷ [])
  (rw 4 q1 ∷
   rw 3 q7 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 10 q5 ∷
   rw 9 q4 ∷
   rw 8 q2 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q2 ∷
   rw 3 q6 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q7 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q31 ∷
   rw 0 q9 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q1 ∷
   rw⁻ 2 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q6 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q9 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q33 : Eqn
  q33 = wE 245 W

-- pass [CS03] [CS01]: 9 steps
lem-pass-CS03-vs-CS01 : ⟪ (CS03 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CS01 = derive (CS03 ∷ CS01 ∷ []) (CS01 ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw 1 q32 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q33 ∷
   rw⁻ 0 q32 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q35 : Eqn
  q35 = wE 246 W

-- pass [CS03] [CSd01]: 9 steps
lem-pass-CS03-vs-CSd01 : ⟪ (CS03 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CSd01 = derive (CS03 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   rw 1 q34 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q35 ∷
   rw⁻ 0 q34 ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q37 : Eqn
  q37 = wE 56 W
  q38 : Eqn
  q38 = wE 247 W

-- pass [TOFF013] [X3 TOFF103 X3]: 115 steps
lem-pass-TOFF013-vs-X3-TOFF103-X3 : ⟪ (Toff013 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ Toff013 ∷ []) ⟫ʷ
lem-pass-TOFF013-vs-X3-TOFF103-X3 = derive (Toff013 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ Toff013 ∷ [])
  (rw 4 q1 ∷
   rw 3 q7 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 10 q5 ∷
   rw 9 q4 ∷
   rw 8 q2 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q2 ∷
   rw 3 q6 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q7 ∷
   re 0 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q36 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q4 ∷
   rw 8 q5 ∷
   rw 7 q4 ∷
   rw 6 q36 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q36 ∷
   rw 1 q37 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q38 ∷
   rw 0 q9 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q1 ∷
   rw⁻ 2 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q6 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q9 ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q36 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q4 ∷
   rw 3 q1 ∷
   rw⁻ 4 q36 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q36 ∷
   rw⁻ 11 q4 ∷
   rw 4 q37 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 43 W
  q40 : Eqn
  q40 = wE 85 W
  q41 : Eqn
  q41 = wE 5 W
  q42 : Eqn
  q42 = wE 76 W
  q43 : Eqn
  q43 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q44 : Eqn
  q44 = wE 7 W
  q45 : Eqn
  q45 = wE 198 W
  q46 : Eqn
  q46 = wE 29 W
  q47 : Eqn
  q47 = wE 27 W
  q48 : Eqn
  q48 = wE 31 W
  q49 : Eqn
  q49 = wE 13 W
  q50 : Eqn
  q50 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q51 : Eqn
  q51 = wE 78 W
  q52 : Eqn
  q52 = wE 87 W
  q53 : Eqn
  q53 = wE 88 W
  q54 : Eqn
  q54 = wE 89 W

-- comm CCZ013 CSd02: 91 steps
lem-comm-CCZ013-CSd02 : ⟪ (CCZ013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CSd02 = derive (CCZ013 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ013 ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q1 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q39 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q40 ∷
   rw⁻ 0 q32 ∷
   rw 3 q1 ∷
   re 1 3 (CX31 ∷ []) ∷
   rw⁻ 2 q34 ∷
   rw 5 q1 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q41 ∷
   rw 5 q42 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q43 ∷
   rw 5 q44 ∷
   rw⁻ 4 q43 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q45 ∷
   rw 4 q46 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q43 ∷
   rw 6 q47 ∷
   rw 7 q43 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q48 ∷
   re 4 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 3 q49 ∷
   rw⁻ 4 q50 ∷
   rw 5 q51 ∷
   re 3 3 (CS02⁻ ∷ []) ∷
   rw 2 q52 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q49 ∷
   rw⁻ 2 q50 ∷
   rw 3 q51 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw 0 q53 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q34 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q32 ∷
   rw 2 q54 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q39 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = wE 248 W

-- pass [X3 CSd30 X3] [TOFF013]: 65 steps
lem-pass-X3-CSd30-X3-vs-TOFF013 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF013 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q36 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q36 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q36 ∷
   rw 4 q37 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q55 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q36 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q36 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q36 ∷
   rw⁻ 8 q4 ∷
   rw 1 q37 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q57 : Eqn
  q57 = wE 249 W

-- pass [X3 CSd30 X3] [CS02]: 19 steps
lem-pass-X3-CSd30-X3-vs-CS02 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS02 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q41 ∷
   rw 3 q44 ∷
   rw⁻ 2 q56 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q43 ∷
   rw 2 q42 ∷
   rw⁻ 1 q43 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q56 ∷
   rw 1 q57 ∷
   rw 0 q47 ∷
   rw 1 q56 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q43 ∷
   rw 3 q46 ∷
   rw 4 q43 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q56 ∷
   rw 4 q48 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 250 W

-- pass [X3 CSd30 X3] [CSd02]: 19 steps
lem-pass-X3-CSd30-X3-vs-CSd02 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CSd02 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 4 q41 ∷
   rw 3 q42 ∷
   rw⁻ 2 q56 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q43 ∷
   rw 2 q42 ∷
   rw⁻ 1 q43 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q56 ∷
   rw 1 q58 ∷
   rw 0 q46 ∷
   rw 1 q56 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q43 ∷
   rw 3 q46 ∷
   rw 4 q43 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q56 ∷
   rw 4 q48 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 251 W

-- pass [CCZ013] [CS03]: 49 steps
lem-pass-CCZ013-vs-CS03 : ⟪ (CCZ013 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CS03 = derive (CCZ013 ∷ CS03 ∷ []) (CS03 ∷ CCZ013 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q1 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q3 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q39 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q59 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q39 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl
