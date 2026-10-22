{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD726 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D726 (W : Ws) (Sᴰ : SD726) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ123-CS03 : St 54
  lem-comm-CCZ123-CS03 = pickᴰ 0 Sᴰ
  lem-T-CZ03-T : St 1036
  lem-T-CZ03-T = pickᴰ 1 Sᴰ
  lem-C3-Ai : St 2196
  lem-C3-Ai = pickᴰ 2 Sᴰ
  lem-C3d-A : St 2197
  lem-C3d-A = pickᴰ 3 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 : St 2198
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = sE 2197 lem-C3d-A
  q2 : Eqn
  q2 = wE 227 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 2211 W
  q6 : Eqn
  q6 = wE 2212 W
  q7 : Eqn
  q7 = sE 1036 lem-T-CZ03-T
  q8 : Eqn
  q8 = wE 1808 W

-- PP2=E: 28 steps
lem-PP2≡E : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-PP2≡E = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (CCZ123 ∷ [])
  (rw 3 q1 ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 3 q3 ∷
   re 1 3 (CZ03 ∷ []) ∷
   rw 2 q4 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q6 ∷
   rw 5 q3 ∷
   re 3 3 (CZ03 ∷ []) ∷
   rw 4 q4 ∷
   rw 0 q7 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q8 ∷
   rw 1 q4 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = sE 2196 lem-C3-Ai
  q10 : Eqn
  q10 = sE 54 lem-comm-CCZ123-CS03
  q11 : Eqn
  q11 = wE 2213 W

-- PPi2=E: 22 steps
lem-PPi2≡E : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ []) ⟫ʷ
lem-PPi2≡E = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CCZ123 ∷ [])
  (rw 4 q9 ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw 3 q6 ∷
   rw 4 q3 ∷
   re 2 3 (CZ03 ∷ []) ∷
   rw 3 q4 ∷
   rw 1 q7 ∷
   rw⁻ 0 q10 ∷
   rw 4 q3 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   re 2 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   rw 2 q11 ∷
   rw 1 q4 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 873 W
  q13 : Eqn
  q13 = wE 2214 W
  q14 : Eqn
  q14 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q15 : Eqn
  q15 = wE 2215 W
  q16 : Eqn
  q16 = wE 151 W
  q17 : Eqn
  q17 = wE 2216 W
  q18 : Eqn
  q18 = wE 153 W
  q19 : Eqn
  q19 = wE 464 W
  q20 : Eqn
  q20 = wE 2217 W
  q21 : Eqn
  q21 = eqn (Toff012 ∷ S3 ∷ []) (S3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (S))
  q22 : Eqn
  q22 = wE 2218 W
  q23 : Eqn
  q23 = wE 154 W
  q24 : Eqn
  q24 = sE 2196 lem-C3-Ai

-- PP-flip: 46 steps
lem-PP-flip : ⟪ (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-PP-flip = derive (X0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X0 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw 4 q12 ∷
   rw 3 q12 ∷
   rw 2 q12 ∷
   rw 0 q13 ∷
   rw 4 q3 ∷
   rw 3 q14 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw 1 q14 ∷
   rw 2 q15 ∷
   rw 1 q16 ∷
   rw 4 q3 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q4 ∷
   rw 3 q13 ∷
   rw 7 q3 ∷
   rw 6 q14 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   rw 4 q14 ∷
   rw 5 q17 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q18 ∷
   rw 6 q4 ∷
   rw 3 q3 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   rw 3 q3 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q16 ∷
   rw 3 q4 ∷
   rw⁻ 2 q21 ∷
   rw 5 q3 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw 3 q19 ∷
   rw 4 q22 ∷
   rw 5 q3 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q16 ∷
   rw 5 q4 ∷
   rw 4 q23 ∷
   rw⁻ 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q26 : Eqn
  q26 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q28 : Eqn
  q28 = wE 56 W
  q29 : Eqn
  q29 = wE 173 W
  q30 : Eqn
  q30 = wE 2016 W
  q31 : Eqn
  q31 = wE 175 W
  q32 : Eqn
  q32 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q33 : Eqn
  q33 = eqn (CS02⁻ ∷ X3 ∷ []) (X3 ∷ CS02⁻ ∷ []) (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))
  q34 : Eqn
  q34 = sE 2198 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02
  q35 : Eqn
  q35 = wE 2017 W

-- pass [X3 TOFF102 CS13 TOFF102 CSd13 X3] [TOFF013 CS02 TOFF013 CSd02]: 249 steps
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 7 q3 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q25 ∷
   rw 9 q3 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q3 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q26 ∷
   rw 13 q3 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q25 ∷
   rw⁻ 13 q27 ∷
   rw 14 q4 ∷
   rw 13 q27 ∷
   rw 12 q25 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   rw 10 q26 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   rw 8 q26 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw 6 q25 ∷
   rw 7 q28 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q29 ∷
   rw 6 q30 ∷
   rw 5 q31 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q25 ∷
   rw 9 q3 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q3 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q26 ∷
   rw 13 q3 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q25 ∷
   rw⁻ 13 q27 ∷
   rw 6 q3 ∷
   rw⁻ 7 q25 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw⁻ 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q4 ∷
   rw⁻ 11 q26 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw⁻ 13 q25 ∷
   rw⁻ 14 q27 ∷
   rw 7 q28 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 7 q31 ∷
   rw 8 q31 ∷
   rw 9 q4 ∷
   rw⁻ 8 q32 ∷
   rw 11 q3 ∷
   re 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q25 ∷
   rw 13 q3 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q26 ∷
   rw 15 q3 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q26 ∷
   rw 17 q3 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q25 ∷
   rw⁻ 17 q27 ∷
   rw 18 q4 ∷
   rw 17 q27 ∷
   rw 16 q25 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q4 ∷
   rw 14 q26 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q4 ∷
   rw 12 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q4 ∷
   rw 10 q25 ∷
   rw 11 q28 ∷
   re 11 8 (Toff012 ∷ []) ∷
   rw 9 q29 ∷
   rw 10 q30 ∷
   rw 9 q31 ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q25 ∷
   rw 13 q3 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q26 ∷
   rw 15 q3 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q26 ∷
   rw 17 q3 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q25 ∷
   rw⁻ 17 q27 ∷
   rw 10 q3 ∷
   rw⁻ 11 q25 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q4 ∷
   rw⁻ 13 q26 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q4 ∷
   rw⁻ 15 q26 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q4 ∷
   rw⁻ 17 q25 ∷
   rw⁻ 18 q27 ∷
   rw 11 q28 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 10 3 (Toff013 ∷ []) ∷
   rw 11 q31 ∷
   rw 12 q31 ∷
   rw 13 q4 ∷
   rw⁻ 12 q33 ∷
   rw 1 q34 ∷
   rw 4 q3 ∷
   rw 3 q29 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q25 ∷
   rw 5 q3 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q3 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q3 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q25 ∷
   rw⁻ 9 q27 ∷
   rw 10 q4 ∷
   rw 9 q27 ∷
   rw 8 q25 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw 6 q26 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   rw 4 q26 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   rw 2 q25 ∷
   rw 3 q28 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q29 ∷
   rw 0 q29 ∷
   rw 1 q35 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q25 ∷
   rw 3 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q26 ∷
   rw 5 q3 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q3 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q25 ∷
   rw⁻ 7 q27 ∷
   rw 0 q3 ∷
   rw⁻ 1 q25 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw⁻ 3 q26 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw⁻ 7 q25 ∷
   rw⁻ 8 q27 ∷
   rw 1 q28 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q31 ∷
   rw 2 q4 ∷
   rw⁻ 1 q32 ∷
   rw 6 q3 ∷
   rw 5 q29 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q25 ∷
   rw 7 q3 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q3 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q3 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q25 ∷
   rw⁻ 11 q27 ∷
   rw 12 q4 ∷
   rw 11 q27 ∷
   rw 10 q25 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q4 ∷
   rw 8 q26 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q4 ∷
   rw 6 q26 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q4 ∷
   rw 4 q25 ∷
   rw 5 q28 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 3 q29 ∷
   rw 2 q29 ∷
   rw 3 q35 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q25 ∷
   rw 5 q3 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q3 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q3 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q25 ∷
   rw⁻ 9 q27 ∷
   rw 2 q3 ∷
   rw⁻ 3 q25 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q4 ∷
   rw⁻ 9 q25 ∷
   rw⁻ 10 q27 ∷
   rw 3 q28 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 3 q31 ∷
   rw 4 q4 ∷
   rw⁻ 3 q33 ∷ []) Eq.refl
