{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D016 (W : Ws) where

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
  q2 = wE 3 W
  q3 : Eqn
  q3 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = wE 297 W

-- pass [X1 CS10 X1] [CS03]: 13 steps
lem-pass-X1-CS10-X1-vs-CS03 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-CS03 = derive (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ []) (CS03 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 0 q3 ∷
   rw 1 q5 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q3 ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = wE 298 W

-- pass [X1 CS10 X1] [CSd03]: 13 steps
lem-pass-X1-CS10-X1-vs-CSd03 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-CSd03 = derive (X1 ∷ CS01 ∷ X1 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 0 q3 ∷
   rw 1 q6 ∷
   rw 2 q1 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q3 ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q9 : Eqn
  q9 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q10 : Eqn
  q10 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q11 : Eqn
  q11 = wE 196 W
  q12 : Eqn
  q12 = wE 299 W
  q13 : Eqn
  q13 = wE 175 W

-- pass [CS13] [X3 TOFF103 X3]: 65 steps
lem-pass-CS13-vs-X3-TOFF103-X3 : ⟪ (CS13 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-X3-TOFF103-X3 = derive (CS13 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13 ∷ [])
  (rw 4 q1 ∷
   rw 3 q7 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q9 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 10 q2 ∷
   rw 9 q10 ∷
   rw 8 q8 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 6 q9 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 4 q9 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 2 q8 ∷
   rw 3 q11 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q7 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q12 ∷
   rw 0 q13 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q8 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q9 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q10 ∷
   rw 1 q1 ∷
   rw⁻ 2 q8 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw⁻ 4 q9 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw⁻ 6 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 2 q11 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q13 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 300 W

-- pass [CSd13] [X3 TOFF103 X3]: 65 steps
lem-pass-CSd13-vs-X3-TOFF103-X3 : ⟪ (CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-X3-TOFF103-X3 = derive (CS13⁻ ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ CS13⁻ ∷ [])
  (rw 4 q1 ∷
   rw 3 q7 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q9 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 10 q2 ∷
   rw 9 q10 ∷
   rw 8 q8 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 6 q9 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 4 q9 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 2 q8 ∷
   rw 3 q11 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q7 ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q14 ∷
   rw 0 q13 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q8 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q9 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q10 ∷
   rw 1 q1 ∷
   rw⁻ 2 q8 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw⁻ 4 q9 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw⁻ 6 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw⁻ 8 q8 ∷
   rw⁻ 9 q10 ∷
   rw 2 q11 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q13 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 93 W

-- pass [CS12] [CS13]: 1 steps
lem-pass-CS12-vs-CS13 : ⟪ (CS12 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CS13 = derive (CS12 ∷ CS13 ∷ []) (CS13 ∷ CS12 ∷ [])
  (rw 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 301 W

-- pass [CCZ012] [CZ02]: 1 steps
lem-pass-CCZ012-vs-CZ02 : ⟪ (CCZ012 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CZ02 = derive (CCZ012 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ012 ∷ [])
  (rw 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 302 W

-- pass [CS12] [CZ02]: 1 steps
lem-pass-CS12-vs-CZ02 : ⟪ (CS12 ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CZ02 = derive (CS12 ∷ CZ02 ∷ []) (CZ02 ∷ CS12 ∷ [])
  (rw 0 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 86 W

-- pass [CS12] [CSd13]: 1 steps
lem-pass-CS12-vs-CSd13 : ⟪ (CS12 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CSd13 = derive (CS12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12 ∷ [])
  (rw 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 179 W

-- pass [CSd12] [CS13]: 1 steps
lem-pass-CSd12-vs-CS13 : ⟪ (CS12⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CS13 = derive (CS12⁻ ∷ CS13 ∷ []) (CS13 ∷ CS12⁻ ∷ [])
  (rw 0 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 303 W

-- pass [CSd12] [CZ02]: 1 steps
lem-pass-CSd12-vs-CZ02 : ⟪ (CS12⁻ ∷ CZ02 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CZ02 = derive (CS12⁻ ∷ CZ02 ∷ []) (CZ02 ∷ CS12⁻ ∷ [])
  (rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 181 W

-- pass [CSd12] [CSd13]: 1 steps
lem-pass-CSd12-vs-CSd13 : ⟪ (CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CSd13 = derive (CS12⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12⁻ ∷ [])
  (rw 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 304 W

-- pass [X3 CSd31 X3] [TOFF103]: 65 steps
lem-pass-X3-CSd31-X3-vs-TOFF103 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF103 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q8 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q9 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q8 ∷
   rw⁻ 10 q10 ∷
   rw 11 q2 ∷
   rw 10 q10 ∷
   rw 9 q8 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 5 q9 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 3 q8 ∷
   rw 4 q11 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw 0 q7 ∷
   rw 1 q22 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q9 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q10 ∷
   rw 0 q1 ∷
   rw⁻ 1 q8 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw⁻ 3 q9 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw⁻ 5 q9 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q10 ∷
   rw 1 q11 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q13 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 3 q13 ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 249 W

-- pass [X3 CSd31 X3] [CS12]: 1 steps
lem-pass-X3-CSd31-X3-vs-CS12 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS12 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 0 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 250 W

-- pass [X3 CSd31 X3] [CSd12]: 1 steps
lem-pass-X3-CSd31-X3-vs-CSd12 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CSd12 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 305 W

-- pass [TOFF102] [X2 TOFF102 X2]: 1 steps
lem-pass-TOFF102-vs-X2-TOFF102-X2 : ⟪ (Toff102 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-X2-TOFF102-X2 = derive (Toff102 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ [])
  (rw 0 q25 ∷ []) Eq.refl

-- pass [CS12] [X2 TOFF102 X2]: 1 steps
lem-pass-CS12-vs-X2-TOFF102-X2 : ⟪ (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-X2-TOFF102-X2 = derive (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ [])
  (rw 0 q12 ∷ []) Eq.refl

-- pass [CSd12] [X2 TOFF102 X2]: 1 steps
lem-pass-CSd12-vs-X2-TOFF102-X2 : ⟪ (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-X2-TOFF102-X2 = derive (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ [])
  (rw 0 q14 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 43 W

-- pass [CCZ013] [CZ03]: 49 steps
lem-pass-CCZ013-vs-CZ03 : ⟪ (CCZ013 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CCZ013 ∷ []) ⟫ʷ
lem-pass-CCZ013-vs-CZ03 = derive (CCZ013 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ013 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q1 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q9 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 3 q9 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 1 q9 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q26 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q16 ∷
   rw 2 q1 ∷
   re 0 3 (CZ03 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q9 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw⁻ 3 q9 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw⁻ 5 q9 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 2 q26 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q2 ∷ []) Eq.refl

-- pass [CS13] [CZ03]: 11 steps
lem-pass-CS13-vs-CZ03 : ⟪ (CS13 ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-CZ03 = derive (CS13 ∷ CZ03 ∷ []) (CZ03 ∷ CS13 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q17 ∷
   rw 2 q1 ∷
   re 0 3 (CZ03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 2 q2 ∷ []) Eq.refl

-- pass [CSd13] [CZ03]: 11 steps
lem-pass-CSd13-vs-CZ03 : ⟪ (CS13⁻ ∷ CZ03 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-CSd13-vs-CZ03 = derive (CS13⁻ ∷ CZ03 ∷ []) (CZ03 ∷ CS13⁻ ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   re 0 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 1 q20 ∷
   rw 2 q1 ∷
   re 0 3 (CZ03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 2 q2 ∷ []) Eq.refl

-- pass [X2 CSd21 X2] [TOFF102]: 1 steps
lem-pass-X2-CSd21-X2-vs-TOFF102 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-TOFF102 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q22 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 287 W

-- pass [X2 CSd21 X2] [CS13]: 1 steps
lem-pass-X2-CSd21-X2-vs-CS13 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS13 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 288 W

-- pass [X2 CSd21 X2] [CSd13]: 1 steps
lem-pass-X2-CSd21-X2-vs-CSd13 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CSd13 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 306 W

-- pass [S1] [CS13]: 1 steps
lem-pass-S1-vs-CS13 : ⟪ (S1 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1 ∷ []) ⟫ʷ
lem-pass-S1-vs-CS13 = derive (S1 ∷ CS13 ∷ []) (CS13 ∷ S1 ∷ [])
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 251 W

-- pass [CCZ012] [CS02]: 1 steps
lem-pass-CCZ012-vs-CS02 : ⟪ (CCZ012 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CS02 = derive (CCZ012 ∷ CS02 ∷ []) (CS02 ∷ CCZ012 ∷ [])
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 307 W

-- pass [S1] [CSd13]: 1 steps
lem-pass-S1-vs-CSd13 : ⟪ (S1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1 ∷ []) ⟫ʷ
lem-pass-S1-vs-CSd13 = derive (S1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1 ∷ [])
  (rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 308 W

-- pass [Sd1] [CS13]: 1 steps
lem-pass-Sd1-vs-CS13 : ⟪ (S1⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-Sd1-vs-CS13 = derive (S1⁻ ∷ CS13 ∷ []) (CS13 ∷ S1⁻ ∷ [])
  (rw 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 254 W

-- pass [CCZ012] [CSd02]: 1 steps
lem-pass-CCZ012-vs-CSd02 : ⟪ (CCZ012 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CSd02 = derive (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ [])
  (rw 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 309 W

-- pass [Sd1] [CSd13]: 1 steps
lem-pass-Sd1-vs-CSd13 : ⟪ (S1⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-Sd1-vs-CSd13 = derive (S1⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1⁻ ∷ [])
  (rw 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q36 : Eqn
  q36 = wE 27 W
  q37 : Eqn
  q37 = wE 31 W
  q38 : Eqn
  q38 = wE 310 W

-- bridge G-pp: 43 steps
lem-bridge-G-pp : ⟪ (Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-bridge-G-pp = derive (Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ Toff012 ∷ Sw01 ∷ Sw23 ∷ CS12 ∷ CS12 ∷ CS12 ∷ Sw23 ∷ Sw01 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q36 ∷
   rw 3 q35 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q37 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q36 ∷
   rw 5 q35 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 6 q35 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   rw 7 q35 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q37 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 4 q38 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 311 W

-- sw0 S0: 2 steps
lem-sw0-S0 : ⟪ (Sw01 ∷ S0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ []) ⟫ʷ
lem-sw0-S0 = derive (Sw01 ∷ S0 ∷ Sw01 ∷ []) (S1 ∷ [])
  (rw 0 q39 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 312 W

-- sw0 Sd0: 2 steps
lem-sw0-Sd0 : ⟪ (Sw01 ∷ S0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ []) ⟫ʷ
lem-sw0-Sd0 = derive (Sw01 ∷ S0⁻ ∷ Sw01 ∷ []) (S1⁻ ∷ [])
  (rw 0 q40 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 123 W

-- sw0 K0: 2 steps
lem-sw0-K0 : ⟪ (Sw01 ∷ K0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K1 ∷ []) ⟫ʷ
lem-sw0-K0 = derive (Sw01 ∷ K0 ∷ Sw01 ∷ []) (K1 ∷ [])
  (rw 0 q41 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 313 W

-- sw0 Kd0: 2 steps
lem-sw0-Kd0 : ⟪ (Sw01 ∷ K0⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K1⁻ ∷ []) ⟫ʷ
lem-sw0-Kd0 = derive (Sw01 ∷ K0⁻ ∷ Sw01 ∷ []) (K1⁻ ∷ [])
  (rw 0 q42 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 220 W

-- sw0 X0: 2 steps
lem-sw0-X0 : ⟪ (Sw01 ∷ X0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ []) ⟫ʷ
lem-sw0-X0 = derive (Sw01 ∷ X0 ∷ Sw01 ∷ []) (X1 ∷ [])
  (rw 0 q43 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 314 W

-- sw0 Z0: 2 steps
lem-sw0-Z0 : ⟪ (Sw01 ∷ Z0 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ []) ⟫ʷ
lem-sw0-Z0 = derive (Sw01 ∷ Z0 ∷ Sw01 ∷ []) (Z1 ∷ [])
  (rw 0 q44 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 315 W

-- sw0 S1: 2 steps
lem-sw0-S1 : ⟪ (Sw01 ∷ S1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ []) ⟫ʷ
lem-sw0-S1 = derive (Sw01 ∷ S1 ∷ Sw01 ∷ []) (S0 ∷ [])
  (rw 0 q45 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 316 W

-- sw0 Sd1: 2 steps
lem-sw0-Sd1 : ⟪ (Sw01 ∷ S1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ []) ⟫ʷ
lem-sw0-Sd1 = derive (Sw01 ∷ S1⁻ ∷ Sw01 ∷ []) (S0⁻ ∷ [])
  (rw 0 q46 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 121 W

-- sw0 K1: 2 steps
lem-sw0-K1 : ⟪ (Sw01 ∷ K1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ []) ⟫ʷ
lem-sw0-K1 = derive (Sw01 ∷ K1 ∷ Sw01 ∷ []) (K0 ∷ [])
  (rw 0 q47 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 129 W

-- sw0 Kd1: 2 steps
lem-sw0-Kd1 : ⟪ (Sw01 ∷ K1⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ []) ⟫ʷ
lem-sw0-Kd1 = derive (Sw01 ∷ K1⁻ ∷ Sw01 ∷ []) (K0⁻ ∷ [])
  (rw 0 q48 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 317 W

-- sw0 X1: 2 steps
lem-sw0-X1 : ⟪ (Sw01 ∷ X1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ []) ⟫ʷ
lem-sw0-X1 = derive (Sw01 ∷ X1 ∷ Sw01 ∷ []) (X0 ∷ [])
  (rw 0 q49 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 318 W

-- sw0 Z1: 2 steps
lem-sw0-Z1 : ⟪ (Sw01 ∷ Z1 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z0 ∷ []) ⟫ʷ
lem-sw0-Z1 = derive (Sw01 ∷ Z1 ∷ Sw01 ∷ []) (Z0 ∷ [])
  (rw 0 q50 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))

-- sw0 S2: 2 steps
lem-sw0-S2 : ⟪ (Sw01 ∷ S2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ []) ⟫ʷ
lem-sw0-S2 = derive (Sw01 ∷ S2 ∷ Sw01 ∷ []) (S2 ∷ [])
  (rw 0 q51 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (Sw01 ∷ S2⁻ ∷ []) (S2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • S • S)))

-- sw0 Sd2: 2 steps
lem-sw0-Sd2 : ⟪ (Sw01 ∷ S2⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ []) ⟫ʷ
lem-sw0-Sd2 = derive (Sw01 ∷ S2⁻ ∷ Sw01 ∷ []) (S2⁻ ∷ [])
  (rw 0 q52 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))

-- sw0 K2: 2 steps
lem-sw0-K2 : ⟪ (Sw01 ∷ K2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K2 ∷ []) ⟫ʷ
lem-sw0-K2 = derive (Sw01 ∷ K2 ∷ Sw01 ∷ []) (K2 ∷ [])
  (rw 0 q53 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (Sw01 ∷ K2⁻ ∷ []) (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI)))

-- sw0 Kd2: 2 steps
lem-sw0-Kd2 : ⟪ (Sw01 ∷ K2⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K2⁻ ∷ []) ⟫ʷ
lem-sw0-Kd2 = derive (Sw01 ∷ K2⁻ ∷ Sw01 ∷ []) (K2⁻ ∷ [])
  (rw 0 q54 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))

-- sw0 X2: 2 steps
lem-sw0-X2 : ⟪ (Sw01 ∷ X2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ []) ⟫ʷ
lem-sw0-X2 = derive (Sw01 ∷ X2 ∷ Sw01 ∷ []) (X2 ∷ [])
  (rw 0 q55 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (Sw01 ∷ Z2 ∷ []) (Z2 ∷ Sw01 ∷ []) (low-comm (Swap) (Z))

-- sw0 Z2: 2 steps
lem-sw0-Z2 : ⟪ (Sw01 ∷ Z2 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z2 ∷ []) ⟫ʷ
lem-sw0-Z2 = derive (Sw01 ∷ Z2 ∷ Sw01 ∷ []) (Z2 ∷ [])
  (rw 0 q56 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))

-- sw0 S3: 2 steps
lem-sw0-S3 : ⟪ (Sw01 ∷ S3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S3 ∷ []) ⟫ʷ
lem-sw0-S3 = derive (Sw01 ∷ S3 ∷ Sw01 ∷ []) (S3 ∷ [])
  (rw 0 q57 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (Sw01 ∷ S3⁻ ∷ []) (S3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((S • S • S) ↑)))

-- sw0 Sd3: 2 steps
lem-sw0-Sd3 : ⟪ (Sw01 ∷ S3⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ []) ⟫ʷ
lem-sw0-Sd3 = derive (Sw01 ∷ S3⁻ ∷ Sw01 ∷ []) (S3⁻ ∷ [])
  (rw 0 q58 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))

-- sw0 K3: 2 steps
lem-sw0-K3 : ⟪ (Sw01 ∷ K3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K3 ∷ []) ⟫ʷ
lem-sw0-K3 = derive (Sw01 ∷ K3 ∷ Sw01 ∷ []) (K3 ∷ [])
  (rw 0 q59 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (Sw01 ∷ K3⁻ ∷ []) (K3⁻ ∷ Sw01 ∷ []) (low-comm (Swap) (((K • iI) ↑)))

-- sw0 Kd3: 2 steps
lem-sw0-Kd3 : ⟪ (Sw01 ∷ K3⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (K3⁻ ∷ []) ⟫ʷ
lem-sw0-Kd3 = derive (Sw01 ∷ K3⁻ ∷ Sw01 ∷ []) (K3⁻ ∷ [])
  (rw 0 q60 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))

-- sw0 X3: 2 steps
lem-sw0-X3 : ⟪ (Sw01 ∷ X3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ []) ⟫ʷ
lem-sw0-X3 = derive (Sw01 ∷ X3 ∷ Sw01 ∷ []) (X3 ∷ [])
  (rw 0 q61 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (Sw01 ∷ Z3 ∷ []) (Z3 ∷ Sw01 ∷ []) (low-comm (Swap) ((Z ↑)))

-- sw0 Z3: 2 steps
lem-sw0-Z3 : ⟪ (Sw01 ∷ Z3 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Z3 ∷ []) ⟫ʷ
lem-sw0-Z3 = derive (Sw01 ∷ Z3 ∷ Sw01 ∷ []) (Z3 ∷ [])
  (rw 0 q62 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 219 W

-- sw0 CS01: 2 steps
lem-sw0-CS01 : ⟪ (Sw01 ∷ CS01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ []) ⟫ʷ
lem-sw0-CS01 = derive (Sw01 ∷ CS01 ∷ Sw01 ∷ []) (CS01 ∷ [])
  (rw 0 q63 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 319 W

-- sw0 CSd01: 2 steps
lem-sw0-CSd01 : ⟪ (Sw01 ∷ CS01⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ []) ⟫ʷ
lem-sw0-CSd01 = derive (Sw01 ∷ CS01⁻ ∷ Sw01 ∷ []) (CS01⁻ ∷ [])
  (rw 0 q64 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 320 W

-- sw0 CZ01: 2 steps
lem-sw0-CZ01 : ⟪ (Sw01 ∷ CZ01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ []) ⟫ʷ
lem-sw0-CZ01 = derive (Sw01 ∷ CZ01 ∷ Sw01 ∷ []) (CZ01 ∷ [])
  (rw 0 q65 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 28 W

-- sw0 CX01: 2 steps
lem-sw0-CX01 : ⟪ (Sw01 ∷ CX01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX10 ∷ []) ⟫ʷ
lem-sw0-CX01 = derive (Sw01 ∷ CX01 ∷ Sw01 ∷ []) (CX10 ∷ [])
  (rw 0 q66 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 221 W

-- sw0 CK01: 2 steps
lem-sw0-CK01 : ⟪ (Sw01 ∷ CK01 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ []) ⟫ʷ
lem-sw0-CK01 = derive (Sw01 ∷ CK01 ∷ Sw01 ∷ []) (CK10 ∷ [])
  (rw 0 q67 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 321 W

-- sw0 CKd01: 2 steps
lem-sw0-CKd01 : ⟪ (Sw01 ∷ CK01⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK10⁻ ∷ []) ⟫ʷ
lem-sw0-CKd01 = derive (Sw01 ∷ CK01⁻ ∷ Sw01 ∷ []) (CK10⁻ ∷ [])
  (rw 0 q68 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = wE 25 W

-- sw0 CS02: 2 steps
lem-sw0-CS02 : ⟪ (Sw01 ∷ CS02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ []) ⟫ʷ
lem-sw0-CS02 = derive (Sw01 ∷ CS02 ∷ Sw01 ∷ []) (CS12 ∷ [])
  (rw 0 q69 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 322 W

-- sw0 CSd02: 2 steps
lem-sw0-CSd02 : ⟪ (Sw01 ∷ CS02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ []) ⟫ʷ
lem-sw0-CSd02 = derive (Sw01 ∷ CS02⁻ ∷ Sw01 ∷ []) (CS12⁻ ∷ [])
  (rw 0 q70 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 323 W

-- sw0 CZ02: 2 steps
lem-sw0-CZ02 : ⟪ (Sw01 ∷ CZ02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ12 ∷ []) ⟫ʷ
lem-sw0-CZ02 = derive (Sw01 ∷ CZ02 ∷ Sw01 ∷ []) (CZ12 ∷ [])
  (rw 0 q71 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 24 W

-- sw0 CX02: 2 steps
lem-sw0-CX02 : ⟪ (Sw01 ∷ CX02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX12 ∷ []) ⟫ʷ
lem-sw0-CX02 = derive (Sw01 ∷ CX02 ∷ Sw01 ∷ []) (CX12 ∷ [])
  (rw 0 q72 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = wE 324 W

-- sw0 CK02: 2 steps
lem-sw0-CK02 : ⟪ (Sw01 ∷ CK02 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK12 ∷ []) ⟫ʷ
lem-sw0-CK02 = derive (Sw01 ∷ CK02 ∷ Sw01 ∷ []) (CK12 ∷ [])
  (rw 0 q73 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 325 W

-- sw0 CKd02: 2 steps
lem-sw0-CKd02 : ⟪ (Sw01 ∷ CK02⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK12⁻ ∷ []) ⟫ʷ
lem-sw0-CKd02 = derive (Sw01 ∷ CK02⁻ ∷ Sw01 ∷ []) (CK12⁻ ∷ [])
  (rw 0 q74 ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CS03: 6 steps
lem-sw0-CS03 : ⟪ (Sw01 ∷ CS03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ []) ⟫ʷ
lem-sw0-CS03 = derive (Sw01 ∷ CS03 ∷ Sw01 ∷ []) (CS13 ∷ [])
  (re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q69 ∷
   rw 2 q35 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CSd03: 6 steps
lem-sw0-CSd03 : ⟪ (Sw01 ∷ CS03⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ []) ⟫ʷ
lem-sw0-CSd03 = derive (Sw01 ∷ CS03⁻ ∷ Sw01 ∷ []) (CS13⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q70 ∷
   rw 2 q35 ∷
   re 0 3 (CS13⁻ ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CZ03: 6 steps
lem-sw0-CZ03 : ⟪ (Sw01 ∷ CZ03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ []) ⟫ʷ
lem-sw0-CZ03 = derive (Sw01 ∷ CZ03 ∷ Sw01 ∷ []) (CZ13 ∷ [])
  (re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q71 ∷
   rw 2 q35 ∷
   re 0 3 (CZ13 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CX03: 6 steps
lem-sw0-CX03 : ⟪ (Sw01 ∷ CX03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX13 ∷ []) ⟫ʷ
lem-sw0-CX03 = derive (Sw01 ∷ CX03 ∷ Sw01 ∷ []) (CX13 ∷ [])
  (re 1 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q72 ∷
   rw 2 q35 ∷
   re 0 3 (CX13 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CK03: 6 steps
lem-sw0-CK03 : ⟪ (Sw01 ∷ CK03 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK13 ∷ []) ⟫ʷ
lem-sw0-CK03 = derive (Sw01 ∷ CK03 ∷ Sw01 ∷ []) (CK13 ∷ [])
  (re 1 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q73 ∷
   rw 2 q35 ∷
   re 0 3 (CK13 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CKd03: 6 steps
lem-sw0-CKd03 : ⟪ (Sw01 ∷ CK03⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK13⁻ ∷ []) ⟫ʷ
lem-sw0-CKd03 = derive (Sw01 ∷ CK03⁻ ∷ Sw01 ∷ []) (CK13⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CK02⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q74 ∷
   rw 2 q35 ∷
   re 0 3 (CK13⁻ ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 326 W

-- sw0 CX10: 2 steps
lem-sw0-CX10 : ⟪ (Sw01 ∷ CX10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX01 ∷ []) ⟫ʷ
lem-sw0-CX10 = derive (Sw01 ∷ CX10 ∷ Sw01 ∷ []) (CX01 ∷ [])
  (rw 0 q75 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 327 W

-- sw0 CK10: 2 steps
lem-sw0-CK10 : ⟪ (Sw01 ∷ CK10 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ []) ⟫ʷ
lem-sw0-CK10 = derive (Sw01 ∷ CK10 ∷ Sw01 ∷ []) (CK01 ∷ [])
  (rw 0 q76 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 328 W

-- sw0 CKd10: 2 steps
lem-sw0-CKd10 : ⟪ (Sw01 ∷ CK10⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK01⁻ ∷ []) ⟫ʷ
lem-sw0-CKd10 = derive (Sw01 ∷ CK10⁻ ∷ Sw01 ∷ []) (CK01⁻ ∷ [])
  (rw 0 q77 ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CS12: 2 steps
lem-sw0-CS12 : ⟪ (Sw01 ∷ CS12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ []) ⟫ʷ
lem-sw0-CS12 = derive (Sw01 ∷ CS12 ∷ Sw01 ∷ []) (CS02 ∷ [])
  (rw 0 q36 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 29 W

-- sw0 CSd12: 2 steps
lem-sw0-CSd12 : ⟪ (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ []) ⟫ʷ
lem-sw0-CSd12 = derive (Sw01 ∷ CS12⁻ ∷ Sw01 ∷ []) (CS02⁻ ∷ [])
  (rw 0 q78 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 191 W

-- sw0 CZ12: 2 steps
lem-sw0-CZ12 : ⟪ (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ02 ∷ []) ⟫ʷ
lem-sw0-CZ12 = derive (Sw01 ∷ CZ12 ∷ Sw01 ∷ []) (CZ02 ∷ [])
  (rw 0 q79 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 30 W

-- sw0 CX12: 2 steps
lem-sw0-CX12 : ⟪ (Sw01 ∷ CX12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX02 ∷ []) ⟫ʷ
lem-sw0-CX12 = derive (Sw01 ∷ CX12 ∷ Sw01 ∷ []) (CX02 ∷ [])
  (rw 0 q80 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 329 W

-- sw0 CK12: 2 steps
lem-sw0-CK12 : ⟪ (Sw01 ∷ CK12 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ []) ⟫ʷ
lem-sw0-CK12 = derive (Sw01 ∷ CK12 ∷ Sw01 ∷ []) (CK02 ∷ [])
  (rw 0 q81 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 330 W

-- sw0 CKd12: 2 steps
lem-sw0-CKd12 : ⟪ (Sw01 ∷ CK12⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK02⁻ ∷ []) ⟫ʷ
lem-sw0-CKd12 = derive (Sw01 ∷ CK12⁻ ∷ Sw01 ∷ []) (CK02⁻ ∷ [])
  (rw 0 q82 ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CS13: 6 steps
lem-sw0-CS13 : ⟪ (Sw01 ∷ CS13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ []) ⟫ʷ
lem-sw0-CS13 = derive (Sw01 ∷ CS13 ∷ Sw01 ∷ []) (CS03 ∷ [])
  (re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   rw 2 q35 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CSd13: 6 steps
lem-sw0-CSd13 : ⟪ (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ []) ⟫ʷ
lem-sw0-CSd13 = derive (Sw01 ∷ CS13⁻ ∷ Sw01 ∷ []) (CS03⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q78 ∷
   rw 2 q35 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CZ13: 6 steps
lem-sw0-CZ13 : ⟪ (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ03 ∷ []) ⟫ʷ
lem-sw0-CZ13 = derive (Sw01 ∷ CZ13 ∷ Sw01 ∷ []) (CZ03 ∷ [])
  (re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q79 ∷
   rw 2 q35 ∷
   re 0 3 (CZ03 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CX13: 6 steps
lem-sw0-CX13 : ⟪ (Sw01 ∷ CX13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX03 ∷ []) ⟫ʷ
lem-sw0-CX13 = derive (Sw01 ∷ CX13 ∷ Sw01 ∷ []) (CX03 ∷ [])
  (re 1 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q80 ∷
   rw 2 q35 ∷
   re 0 3 (CX03 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CK13: 6 steps
lem-sw0-CK13 : ⟪ (Sw01 ∷ CK13 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK03 ∷ []) ⟫ʷ
lem-sw0-CK13 = derive (Sw01 ∷ CK13 ∷ Sw01 ∷ []) (CK03 ∷ [])
  (re 1 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q81 ∷
   rw 2 q35 ∷
   re 0 3 (CK03 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CKd13: 6 steps
lem-sw0-CKd13 : ⟪ (Sw01 ∷ CK13⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK03⁻ ∷ []) ⟫ʷ
lem-sw0-CKd13 = derive (Sw01 ∷ CK13⁻ ∷ Sw01 ∷ []) (CK03⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q82 ∷
   rw 2 q35 ∷
   re 0 3 (CK03⁻ ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 331 W

-- sw0 CX20: 2 steps
lem-sw0-CX20 : ⟪ (Sw01 ∷ CX20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX21 ∷ []) ⟫ʷ
lem-sw0-CX20 = derive (Sw01 ∷ CX20 ∷ Sw01 ∷ []) (CX21 ∷ [])
  (rw 0 q83 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 275 W

-- sw0 CK20: 2 steps
lem-sw0-CK20 : ⟪ (Sw01 ∷ CK20 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK21 ∷ []) ⟫ʷ
lem-sw0-CK20 = derive (Sw01 ∷ CK20 ∷ Sw01 ∷ []) (CK21 ∷ [])
  (rw 0 q84 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 332 W

-- sw0 CKd20: 2 steps
lem-sw0-CKd20 : ⟪ (Sw01 ∷ CK20⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK21⁻ ∷ []) ⟫ʷ
lem-sw0-CKd20 = derive (Sw01 ∷ CK20⁻ ∷ Sw01 ∷ []) (CK21⁻ ∷ [])
  (rw 0 q85 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 39 W

-- sw0 CX21: 2 steps
lem-sw0-CX21 : ⟪ (Sw01 ∷ CX21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX20 ∷ []) ⟫ʷ
lem-sw0-CX21 = derive (Sw01 ∷ CX21 ∷ Sw01 ∷ []) (CX20 ∷ [])
  (rw 0 q86 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = wE 142 W

-- sw0 CK21: 2 steps
lem-sw0-CK21 : ⟪ (Sw01 ∷ CK21 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK20 ∷ []) ⟫ʷ
lem-sw0-CK21 = derive (Sw01 ∷ CK21 ∷ Sw01 ∷ []) (CK20 ∷ [])
  (rw 0 q87 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = wE 139 W

-- sw0 CKd21: 2 steps
lem-sw0-CKd21 : ⟪ (Sw01 ∷ CK21⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK20⁻ ∷ []) ⟫ʷ
lem-sw0-CKd21 = derive (Sw01 ∷ CK21⁻ ∷ Sw01 ∷ []) (CK20⁻ ∷ [])
  (rw 0 q88 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))

-- sw0 CS23: 2 steps
lem-sw0-CS23 : ⟪ (Sw01 ∷ CS23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ []) ⟫ʷ
lem-sw0-CS23 = derive (Sw01 ∷ CS23 ∷ Sw01 ∷ []) (CS23 ∷ [])
  (rw 0 q89 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))

-- sw0 CSd23: 2 steps
lem-sw0-CSd23 : ⟪ (Sw01 ∷ CS23⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ []) ⟫ʷ
lem-sw0-CSd23 = derive (Sw01 ∷ CS23⁻ ∷ Sw01 ∷ []) (CS23⁻ ∷ [])
  (rw 0 q90 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ))

-- sw0 CZ23: 2 steps
lem-sw0-CZ23 : ⟪ (Sw01 ∷ CZ23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ []) ⟫ʷ
lem-sw0-CZ23 = derive (Sw01 ∷ CZ23 ∷ Sw01 ∷ []) (CZ23 ∷ [])
  (rw 0 q91 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))

-- sw0 CX23: 2 steps
lem-sw0-CX23 : ⟪ (Sw01 ∷ CX23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX23 ∷ []) ⟫ʷ
lem-sw0-CX23 = derive (Sw01 ∷ CX23 ∷ Sw01 ∷ []) (CX23 ∷ [])
  (rw 0 q92 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))

-- sw0 CK23: 2 steps
lem-sw0-CK23 : ⟪ (Sw01 ∷ CK23 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK23 ∷ []) ⟫ʷ
lem-sw0-CK23 = derive (Sw01 ∷ CK23 ∷ Sw01 ∷ []) (CK23 ∷ [])
  (rw 0 q93 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = eqn (Sw01 ∷ CK23⁻ ∷ []) (CK23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S • CK₀₁)))

-- sw0 CKd23: 2 steps
lem-sw0-CKd23 : ⟪ (Sw01 ∷ CK23⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK23⁻ ∷ []) ⟫ʷ
lem-sw0-CKd23 = derive (Sw01 ∷ CK23⁻ ∷ Sw01 ∷ []) (CK23⁻ ∷ [])
  (rw 0 q94 ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CX30: 6 steps
lem-sw0-CX30 : ⟪ (Sw01 ∷ CX30 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ []) ⟫ʷ
lem-sw0-CX30 = derive (Sw01 ∷ CX30 ∷ Sw01 ∷ []) (CX31 ∷ [])
  (re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q83 ∷
   rw 2 q35 ∷
   re 0 3 (CX31 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CK30: 6 steps
lem-sw0-CK30 : ⟪ (Sw01 ∷ CK30 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK31 ∷ []) ⟫ʷ
lem-sw0-CK30 = derive (Sw01 ∷ CK30 ∷ Sw01 ∷ []) (CK31 ∷ [])
  (re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q84 ∷
   rw 2 q35 ∷
   re 0 3 (CK31 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CKd30: 6 steps
lem-sw0-CKd30 : ⟪ (Sw01 ∷ CK30⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK31⁻ ∷ []) ⟫ʷ
lem-sw0-CKd30 = derive (Sw01 ∷ CK30⁻ ∷ Sw01 ∷ []) (CK31⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q85 ∷
   rw 2 q35 ∷
   re 0 3 (CK31⁻ ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CX31: 6 steps
lem-sw0-CX31 : ⟪ (Sw01 ∷ CX31 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ []) ⟫ʷ
lem-sw0-CX31 = derive (Sw01 ∷ CX31 ∷ Sw01 ∷ []) (CX30 ∷ [])
  (re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q86 ∷
   rw 2 q35 ∷
   re 0 3 (CX30 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CK31: 6 steps
lem-sw0-CK31 : ⟪ (Sw01 ∷ CK31 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ []) ⟫ʷ
lem-sw0-CK31 = derive (Sw01 ∷ CK31 ∷ Sw01 ∷ []) (CK30 ∷ [])
  (re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q87 ∷
   rw 2 q35 ∷
   re 0 3 (CK30 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

-- sw0 CKd31: 6 steps
lem-sw0-CKd31 : ⟪ (Sw01 ∷ CK31⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK30⁻ ∷ []) ⟫ʷ
lem-sw0-CKd31 = derive (Sw01 ∷ CK31⁻ ∷ Sw01 ∷ []) (CK30⁻ ∷ [])
  (re 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q88 ∷
   rw 2 q35 ∷
   re 0 3 (CK30⁻ ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))

-- sw0 CX32: 2 steps
lem-sw0-CX32 : ⟪ (Sw01 ∷ CX32 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CX32 ∷ []) ⟫ʷ
lem-sw0-CX32 = derive (Sw01 ∷ CX32 ∷ Sw01 ∷ []) (CX32 ∷ [])
  (rw 0 q95 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = eqn (Sw01 ∷ CK32 ∷ []) (CK32 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₁₀))

-- sw0 CK32: 2 steps
lem-sw0-CK32 : ⟪ (Sw01 ∷ CK32 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK32 ∷ []) ⟫ʷ
lem-sw0-CK32 = derive (Sw01 ∷ CK32 ∷ Sw01 ∷ []) (CK32 ∷ [])
  (rw 0 q96 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn (Sw01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑ • CK₁₀)))

-- sw0 CKd32: 2 steps
lem-sw0-CKd32 : ⟪ (Sw01 ∷ CK32⁻ ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CK32⁻ ∷ []) ⟫ʷ
lem-sw0-CKd32 = derive (Sw01 ∷ CK32⁻ ∷ Sw01 ∷ []) (CK32⁻ ∷ [])
  (rw 0 q97 ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 11 W

-- sw0 CCZ012: 9 steps
lem-sw0-CCZ012 : ⟪ (Sw01 ∷ CCZ012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-sw0-CCZ012 = derive (Sw01 ∷ CCZ012 ∷ Sw01 ∷ []) (CCZ012 ∷ [])
  (re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 0 q36 ∷
   rw 1 q66 ∷
   rw 2 q78 ∷
   rw 3 q66 ∷
   rw 4 q69 ∷
   rw 0 q98 ∷
   re 0 5 (CCZ012 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q99 : Eqn
  q99 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))

-- sw0 CCZ013: 41 steps
lem-sw0-CCZ013 : ⟪ (Sw01 ∷ CCZ013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ []) ⟫ʷ
lem-sw0-CCZ013 = derive (Sw01 ∷ CCZ013 ∷ Sw01 ∷ []) (CCZ013 ∷ [])
  (re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q9 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q9 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q2 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   rw 2 q35 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q66 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q35 ∷
   rw 3 q78 ∷
   rw 4 q35 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q66 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q35 ∷
   rw 5 q69 ∷
   rw 6 q35 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 0 q1 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 1 q2 ∷
   rw⁻ 2 q99 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   rw⁻ 4 q99 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 1 q98 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 0 3 (CCZ013 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = wE 26 W

-- sw0 CCZ023: 24 steps
lem-sw0-CCZ023 : ⟪ (Sw01 ∷ CCZ023 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-sw0-CCZ023 = derive (Sw01 ∷ CCZ023 ∷ Sw01 ∷ []) (CCZ123 ∷ [])
  (re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q89 ∷
   rw 2 q80 ∷
   rw 3 q90 ∷
   rw 4 q80 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q35 ∷
   rw 6 q36 ∷
   rw 7 q35 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q37 ∷
   rw 0 q89 ∷
   rw 1 q72 ∷
   rw 2 q90 ∷
   rw 3 q72 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q35 ∷
   rw 5 q69 ∷
   rw 6 q35 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 0 q100 ∷
   re 0 5 (CCZ123 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = wE 5 W

-- sw0 CCZ123: 24 steps
lem-sw0-CCZ123 : ⟪ (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-sw0-CCZ123 = derive (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) (CCZ023 ∷ [])
  (re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q89 ∷
   rw 1 q80 ∷
   rw 2 q90 ∷
   rw 3 q80 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 6 q35 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 0 q101 ∷
   rw 1 q89 ∷
   rw 2 q72 ∷
   rw 3 q90 ∷
   rw 4 q72 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q35 ∷
   rw 6 q69 ∷
   rw 7 q35 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q100 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ023 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q102 : Eqn
  q102 = wE 124 W
  q103 : Eqn
  q103 = wE 274 W

-- sw0 TOFF012: 12 steps
lem-sw0-TOFF012 : ⟪ (Sw01 ∷ Toff012 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ []) ⟫ʷ
lem-sw0-TOFF012 = derive (Sw01 ∷ Toff012 ∷ Sw01 ∷ []) (Toff102 ∷ [])
  (re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 0 q41 ∷
   rw 1 q36 ∷
   rw 2 q66 ∷
   rw 3 q78 ∷
   rw 4 q66 ∷
   rw 5 q69 ∷
   rw 6 q41 ∷
   rw 7 q102 ∷
   rw 0 q103 ∷
   re 0 8 (Toff102 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q105 : Eqn
  q105 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))

-- sw0 TOFF013: 50 steps
lem-sw0-TOFF013 : ⟪ (Sw01 ∷ Toff013 ∷ Sw01 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ []) ⟫ʷ
lem-sw0-TOFF013 = derive (Sw01 ∷ Toff013 ∷ Sw01 ∷ []) (Toff103 ∷ [])
  (re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q104 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q9 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q9 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q104 ∷
   rw⁻ 8 q10 ∷
   rw 9 q2 ∷
   rw 0 q41 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q36 ∷
   rw 3 q35 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q66 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q78 ∷
   rw 5 q35 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q66 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q35 ∷
   rw 6 q69 ∷
   rw 7 q35 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q41 ∷
   rw 7 q102 ∷
   rw 0 q1 ∷
   rw⁻ 1 q8 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw⁻ 3 q99 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw⁻ 5 q99 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw⁻ 7 q8 ∷
   rw⁻ 8 q105 ∷
   rw 1 q103 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q37 ∷ []) Eq.refl
