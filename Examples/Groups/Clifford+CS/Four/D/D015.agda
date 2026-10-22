{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D015 (W : Ws) where

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
  q2 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 56 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 278 W
  q9 : Eqn
  q9 = wE 175 W

-- pass [X3 CS31 X3] [TOFF013]: 65 steps
lem-pass-X3-CS31-X3-vs-TOFF013 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF013 = derive (X3 ∷ CS13 ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q8 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (CS02⁻ ∷ X3 ∷ []) (X3 ∷ CS02⁻ ∷ []) (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))
  q11 : Eqn
  q11 = wE 65 W
  q12 : Eqn
  q12 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q13 : Eqn
  q13 = wE 48 W

-- pass [X3 CS31 X3] [CSd02]: 7 steps
lem-pass-X3-CS31-X3-vs-CSd02 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-CSd02 = derive (X3 ∷ CS13 ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw⁻ 2 q10 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q11 ∷
   rw⁻ 2 q12 ∷
   rw 3 q13 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q15 : Eqn
  q15 = wE 279 W
  q16 : Eqn
  q16 = eqn (CS01 ∷ CK32 ∷ []) (CK32 ∷ CS01 ∷ []) (low-comm (CS) (CK₁₀))
  q17 : Eqn
  q17 = wE 280 W

-- pass [X3 CK31 X3] [CS02]: 7 steps
lem-pass-X3-CK31-X3-vs-CS02 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS02 = derive (X3 ∷ CK31 ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw⁻ 2 q14 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q15 ∷
   rw⁻ 2 q16 ∷
   rw 3 q17 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 281 W

-- pass [X3 CK31 X3] [TOFF013]: 65 steps
lem-pass-X3-CK31-X3-vs-TOFF013 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF013 = derive (X3 ∷ CK31 ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q18 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (CS01⁻ ∷ CK32 ∷ []) (CK32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CK₁₀))

-- pass [X3 CK31 X3] [CSd02]: 7 steps
lem-pass-X3-CK31-X3-vs-CSd02 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-CSd02 = derive (X3 ∷ CK31 ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw⁻ 2 q10 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q15 ∷
   rw⁻ 2 q19 ∷
   rw 3 q17 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 282 W
  q21 : Eqn
  q21 = eqn (CS01 ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01 ∷ []) (low-comm (CS) ((S ↑ • CK₁₀)))
  q22 : Eqn
  q22 = wE 283 W

-- pass [X3 CKd31 X3] [CS02]: 7 steps
lem-pass-X3-CKd31-X3-vs-CS02 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS02 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q14 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q20 ∷
   rw⁻ 2 q21 ∷
   rw 3 q22 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 284 W

-- pass [X3 CKd31 X3] [TOFF013]: 65 steps
lem-pass-X3-CKd31-X3-vs-TOFF013 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF013 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q23 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (CS01⁻ ∷ CK32⁻ ∷ []) (CK32⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((S ↑ • CK₁₀)))

-- pass [X3 CKd31 X3] [CSd02]: 7 steps
lem-pass-X3-CKd31-X3-vs-CSd02 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CSd02 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q10 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q20 ∷
   rw⁻ 2 q24 ∷
   rw 3 q22 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 84 W
  q26 : Eqn
  q26 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q27 : Eqn
  q27 = wE 47 W

-- pass [X3 CSd31 X3] [CS02]: 7 steps
lem-pass-X3-CSd31-X3-vs-CS02 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS02 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q14 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q25 ∷
   rw⁻ 2 q26 ∷
   rw 3 q27 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw⁻ 0 q14 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 285 W

-- pass [X3 CSd31 X3] [TOFF013]: 65 steps
lem-pass-X3-CSd31-X3-vs-TOFF013 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF013 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q28 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q9 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))

-- pass [X3 CSd31 X3] [CSd02]: 7 steps
lem-pass-X3-CSd31-X3-vs-CSd02 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CSd02 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw⁻ 2 q10 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q25 ∷
   rw⁻ 2 q29 ∷
   rw 3 q27 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 286 W

-- pass [CS03] [CS03]: 11 steps
lem-pass-CS03-vs-CS03 : ⟪ (CS03 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CS03 = derive (CS03 ∷ CS03 ∷ []) (CS03 ∷ CS03 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q30 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 248 W

-- pass [X2 CSd20 X2] [TOFF012]: 1 steps
lem-pass-X2-CSd20-X2-vs-TOFF012 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-TOFF012 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 5 W
  q33 : Eqn
  q33 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q34 : Eqn
  q34 = wE 7 W
  q35 : Eqn
  q35 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q36 : Eqn
  q36 = wE 76 W
  q37 : Eqn
  q37 = wE 287 W
  q38 : Eqn
  q38 = wE 27 W
  q39 : Eqn
  q39 = wE 29 W
  q40 : Eqn
  q40 = wE 31 W

-- pass [X2 CSd20 X2] [CS03]: 19 steps
lem-pass-X2-CSd20-X2-vs-CS03 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CS03 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ CS03 ∷ []) (CS03 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q34 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 1 q36 ∷
   rw⁻ 0 q35 ∷
   rw 1 q37 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q38 ∷
   rw 2 q33 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q39 ∷
   rw 3 q35 ∷
   rw 4 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 288 W

-- pass [X2 CSd20 X2] [CSd03]: 19 steps
lem-pass-X2-CSd20-X2-vs-CSd03 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CSd03 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q36 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 1 q36 ∷
   rw⁻ 0 q35 ∷
   rw 1 q41 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q39 ∷
   rw 2 q33 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q39 ∷
   rw 3 q35 ∷
   rw 4 q40 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 277 W

-- pass [X2 CS21 X2] [TOFF102]: 1 steps
lem-pass-X2-CS21-X2-vs-TOFF102 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-TOFF102 = derive (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 255 W

-- pass [X2 CS21 X2] [CS13]: 1 steps
lem-pass-X2-CS21-X2-vs-CS13 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-CS13 = derive (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 256 W

-- pass [X2 CS21 X2] [CSd13]: 1 steps
lem-pass-X2-CS21-X2-vs-CSd13 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-CSd13 = derive (X2 ∷ CS12 ∷ X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 257 W
  q46 : Eqn
  q46 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))

-- pass [X2 CS21 X2] [CS03]: 39 steps
lem-pass-X2-CS21-X2-vs-CS03 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-CS03 = derive (X2 ∷ CS12 ∷ X2 ∷ CS03 ∷ []) (CS03 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q34 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 3 q45 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q38 ∷
   rw 4 q33 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q40 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q11 ∷
   rw⁻ 3 q46 ∷
   rw 4 q13 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 1 5 (CS03 ∷ []) ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q33 ∷
   rw 2 q34 ∷
   rw⁻ 1 q33 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 1 q45 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q38 ∷
   rw 2 q33 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q40 ∷ []) Eq.refl

-- pass [X2 CS21 X2] [TOFF012]: 1 steps
lem-pass-X2-CS21-X2-vs-TOFF012 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-TOFF012 = derive (X2 ∷ CS12 ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q8 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 258 W

-- pass [X2 CS21 X2] [CSd03]: 39 steps
lem-pass-X2-CS21-X2-vs-CSd03 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-CSd03 = derive (X2 ∷ CS12 ∷ X2 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q36 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 3 q47 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q39 ∷
   rw 4 q33 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q40 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q11 ∷
   rw⁻ 3 q12 ∷
   rw 4 q13 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 1 5 (CS03⁻ ∷ []) ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q33 ∷
   rw 2 q36 ∷
   rw⁻ 1 q33 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 1 q47 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q39 ∷
   rw 2 q33 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q40 ∷ []) Eq.refl

-- pass [X2 CK21 X2] [CS03]: 39 steps
lem-pass-X2-CK21-X2-vs-CS03 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-CS03 = derive (X2 ∷ CK21 ∷ X2 ∷ CS03 ∷ []) (CS03 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q34 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 3 q45 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q38 ∷
   rw 4 q33 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q40 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw 2 q15 ∷
   rw⁻ 3 q16 ∷
   rw 4 q17 ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 1 5 (CS03 ∷ []) ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q33 ∷
   rw 2 q34 ∷
   rw⁻ 1 q33 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 1 q45 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q38 ∷
   rw 2 q33 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q40 ∷ []) Eq.refl

-- pass [X2 CK21 X2] [TOFF012]: 1 steps
lem-pass-X2-CK21-X2-vs-TOFF012 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-TOFF012 = derive (X2 ∷ CK21 ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 0 q18 ∷ []) Eq.refl

-- pass [X2 CK21 X2] [CSd03]: 39 steps
lem-pass-X2-CK21-X2-vs-CSd03 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-CSd03 = derive (X2 ∷ CK21 ∷ X2 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q36 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 3 q47 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q39 ∷
   rw 4 q33 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q40 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw 2 q15 ∷
   rw⁻ 3 q19 ∷
   rw 4 q17 ∷
   re 5 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 1 5 (CS03⁻ ∷ []) ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q33 ∷
   rw 2 q36 ∷
   rw⁻ 1 q33 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 1 q47 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q39 ∷
   rw 2 q33 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q40 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 247 W

-- pass [TOFF012] [X2 TOFF102 X2]: 1 steps
lem-pass-TOFF012-vs-X2-TOFF102-X2 : ⟪ (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-X2-TOFF102-X2 = derive (Toff012 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff012 ∷ [])
  (rw 0 q48 ∷ []) Eq.refl

-- pass [X2 CKd21 X2] [CS03]: 39 steps
lem-pass-X2-CKd21-X2-vs-CS03 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CS03 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ CS03 ∷ []) (CS03 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q34 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 3 q45 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q38 ∷
   rw 4 q33 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q40 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw 2 q20 ∷
   rw⁻ 3 q21 ∷
   rw 4 q22 ∷
   re 5 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 1 5 (CS03 ∷ []) ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q33 ∷
   rw 2 q34 ∷
   rw⁻ 1 q33 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 1 q45 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q38 ∷
   rw 2 q33 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q40 ∷ []) Eq.refl

-- pass [X2 CKd21 X2] [TOFF012]: 1 steps
lem-pass-X2-CKd21-X2-vs-TOFF012 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-TOFF012 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 0 q23 ∷ []) Eq.refl

-- pass [X2 CKd21 X2] [CSd03]: 39 steps
lem-pass-X2-CKd21-X2-vs-CSd03 : ⟪ (X2 ∷ CK21⁻ ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd21-X2-vs-CSd03 = derive (X2 ∷ CK21⁻ ∷ X2 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X2 ∷ CK21⁻ ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q36 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 3 q47 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q39 ∷
   rw 4 q33 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q40 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CK31⁻ ∷ []) ∷
   rw 2 q20 ∷
   rw⁻ 3 q24 ∷
   rw 4 q22 ∷
   re 5 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 1 5 (CS03⁻ ∷ []) ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q33 ∷
   rw 2 q36 ∷
   rw⁻ 1 q33 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 1 q47 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q39 ∷
   rw 2 q33 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q40 ∷ []) Eq.refl

-- pass [X2 CSd21 X2] [CS03]: 39 steps
lem-pass-X2-CSd21-X2-vs-CS03 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS03 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS03 ∷ []) (CS03 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q34 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 3 q45 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q38 ∷
   rw 4 q33 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q40 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 2 q25 ∷
   rw⁻ 3 q26 ∷
   rw 4 q27 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 1 5 (CS03 ∷ []) ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q33 ∷
   rw 2 q34 ∷
   rw⁻ 1 q33 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 1 q45 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q38 ∷
   rw 2 q33 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q40 ∷ []) Eq.refl

-- pass [X2 CSd21 X2] [TOFF012]: 1 steps
lem-pass-X2-CSd21-X2-vs-TOFF012 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-TOFF012 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ Toff012 ∷ []) (Toff012 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q28 ∷ []) Eq.refl

-- pass [X2 CSd21 X2] [CSd03]: 39 steps
lem-pass-X2-CSd21-X2-vs-CSd03 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CSd03 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 4 q32 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q33 ∷
   rw 4 q36 ∷
   rw⁻ 3 q33 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 3 q47 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q39 ∷
   rw 4 q33 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q35 ∷
   rw 4 q40 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 2 q25 ∷
   rw⁻ 3 q29 ∷
   rw 4 q27 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 1 5 (CS03⁻ ∷ []) ∷
   rw 2 q32 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q33 ∷
   rw 2 q36 ∷
   rw⁻ 1 q33 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 0 q35 ∷
   rw 1 q47 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q39 ∷
   rw 2 q33 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 1 q35 ∷
   rw 2 q40 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 289 W

-- pass [TOFF012] [S1]: 1 steps
lem-pass-TOFF012-vs-S1 : ⟪ (Toff012 ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-S1 = derive (Toff012 ∷ S1 ∷ []) (S1 ∷ Toff012 ∷ [])
  (rw 0 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 290 W

-- pass [TOFF012] [Sd1]: 1 steps
lem-pass-TOFF012-vs-Sd1 : ⟪ (Toff012 ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-Sd1 = derive (Toff012 ∷ S1⁻ ∷ []) (S1⁻ ∷ Toff012 ∷ [])
  (rw 0 q50 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q52 : Eqn
  q52 = wE 291 W

-- pass [CSd03] [S1]: 9 steps
lem-pass-CSd03-vs-S1 : ⟪ (CS03⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-S1 = derive (CS03⁻ ∷ S1 ∷ []) (S1 ∷ CS03⁻ ∷ [])
  (rw 2 q1 ∷
   rw 1 q51 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q52 ∷
   rw⁻ 0 q51 ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (S1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (Swap))
  q54 : Eqn
  q54 = wE 292 W

-- pass [CSd03] [Sd1]: 9 steps
lem-pass-CSd03-vs-Sd1 : ⟪ (CS03⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-Sd1 = derive (CS03⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ CS03⁻ ∷ [])
  (rw 2 q1 ∷
   rw 1 q53 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q54 ∷
   rw⁻ 0 q53 ∷
   rw 3 q1 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q56 : Eqn
  q56 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q57 : Eqn
  q57 = wE 196 W
  q58 : Eqn
  q58 = wE 201 W

-- pass [TOFF103] [S0]: 59 steps
lem-pass-TOFF103-vs-S0 : ⟪ (Toff103 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff103 ∷ []) ⟫ʷ
lem-pass-TOFF103-vs-S0 = derive (Toff103 ∷ S0 ∷ []) (S0 ∷ Toff103 ∷ [])
  (rw 2 q1 ∷
   rw 1 q55 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q56 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q56 ∷
   rw⁻ 7 q4 ∷
   rw 8 q5 ∷
   rw 7 q4 ∷
   rw 6 q56 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q56 ∷
   rw 1 q57 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 1 q58 ∷
   rw⁻ 0 q55 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q56 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q56 ∷
   rw⁻ 8 q4 ∷
   rw 1 q1 ∷
   rw⁻ 2 q56 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q56 ∷
   rw⁻ 9 q4 ∷
   rw 2 q57 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 293 W

-- pass [TOFF103] [CSd03]: 61 steps
lem-pass-TOFF103-vs-CSd03 : ⟪ (Toff103 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff103 ∷ []) ⟫ʷ
lem-pass-TOFF103-vs-CSd03 = derive (Toff103 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff103 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q56 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q56 ∷
   rw⁻ 7 q4 ∷
   rw 8 q5 ∷
   rw 7 q4 ∷
   rw 6 q56 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q3 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q56 ∷
   rw 1 q57 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 1 q59 ∷
   rw 2 q1 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q56 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q56 ∷
   rw⁻ 8 q4 ∷
   rw 1 q1 ∷
   rw⁻ 2 q56 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q56 ∷
   rw⁻ 9 q4 ∷
   rw 2 q57 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 294 W

-- pass [S0] [CS12]: 1 steps
lem-pass-S0-vs-CS12 : ⟪ (S0 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS12 = derive (S0 ∷ CS12 ∷ []) (CS12 ∷ S0 ∷ [])
  (rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 295 W

-- pass [S0] [CSd12]: 1 steps
lem-pass-S0-vs-CSd12 : ⟪ (S0 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd12 = derive (S0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ S0 ∷ [])
  (rw 0 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (S0 ∷ Toff123 ∷ []) (Toff123 ∷ S0 ∷ []) (low₁-comm (S) (Toff))

-- pass [TOFF123] [S0]: 1 steps
lem-pass-TOFF123-vs-S0 : ⟪ (Toff123 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-S0 = derive (Toff123 ∷ S0 ∷ []) (S0 ∷ Toff123 ∷ [])
  (rw⁻ 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 296 W

-- pass [X1 CS10 X1] [TOFF012]: 1 steps
lem-pass-X1-CS10-X1-vs-TOFF012 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-TOFF012 = derive (X1 ∷ CS01 ∷ X1 ∷ Toff012 ∷ []) (Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 0 q63 ∷ []) Eq.refl
