{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D682 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D651 W using (lem-S2 ; lem-pass-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 ; lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03)

private
  q1 : Eqn
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q7 : Eqn
  q7 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q8 : Eqn
  q8 = eqn (X2 ∷ Toff012 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ X2 ∷ []) (wn 2016 W)
  q9 : Eqn
  q9 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q10 : Eqn
  q10 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q11 : Eqn
  q11 = eqn (CS02⁻ ∷ X3 ∷ []) (X3 ∷ CS02⁻ ∷ []) (low₃-comm ((Swap ↑ • (CS • CS • CS) • Swap ↑)) (X))
  q12 : Eqn
  q12 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS02 ∷ X3 ∷ Toff013 ∷ X3 ∷ CS02⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X3-TOFF013-X3-CS02-X3-TOFF013-X3-CSd02)
  q13 : Eqn
  q13 = eqn (X2 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (Toff012 ∷ X2 ∷ []) (wn 2017 W)

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [TOFF013 CS02 TOFF013 CSd02]: 249 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ [])
  (rw 7 q1 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw⁻ 13 q4 ∷
   rw 14 q5 ∷
   rw 13 q4 ∷
   rw 12 q2 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q2 ∷
   rw 7 q6 ∷
   re 7 8 (Toff012 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 5 q9 ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw⁻ 13 q4 ∷
   rw 6 q1 ∷
   rw⁻ 7 q2 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 13 q2 ∷
   rw⁻ 14 q4 ∷
   rw 7 q6 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 7 q9 ∷
   rw 8 q9 ∷
   rw 9 q5 ∷
   rw⁻ 8 q10 ∷
   rw 11 q1 ∷
   re 10 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 18 q5 ∷
   rw 17 q4 ∷
   rw 16 q2 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q2 ∷
   rw 11 q6 ∷
   re 11 8 (Toff012 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   re 11 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q4 ∷
   rw 10 q1 ∷
   rw⁻ 11 q2 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q3 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw⁻ 17 q2 ∷
   rw⁻ 18 q4 ∷
   rw 11 q6 ∷
   re 11 8 (Toff012 ∷ []) ∷
   re 10 3 (Toff013 ∷ []) ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q5 ∷
   rw⁻ 12 q11 ∷
   rw 1 q12 ∷
   rw 4 q1 ∷
   rw 3 q7 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   re 3 8 (Toff012 ∷ []) ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q13 ∷
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
   rw 2 q5 ∷
   rw⁻ 1 q10 ∷
   rw 6 q1 ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 12 q5 ∷
   rw 11 q4 ∷
   rw 10 q2 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q2 ∷
   rw 5 q6 ∷
   re 5 8 (Toff012 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q7 ∷
   rw 3 q13 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
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
   rw 2 q1 ∷
   rw⁻ 3 q2 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q6 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q5 ∷
   rw⁻ 3 q11 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2)
  q15 : Eqn
  q15 = eqn (X3 ∷ CS03⁻ ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) (lem-pass-X3-CSd30-X3-vs-TOFF013-CS02-TOFF013-CSd02)
  q16 : Eqn
  q16 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) lem-S2

-- pass [X3 CSd30 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CS03⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS03⁻ ∷ X3 ∷ [])
  (rw 3 q14 ∷
   rw 0 q15 ∷
   rw⁻ 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q18 : Eqn
  q18 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q19 : Eqn
  q19 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q20 : Eqn
  q20 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q21 : Eqn
  q21 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q23 : Eqn
  q23 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wn 84 W)
  q24 : Eqn
  q24 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q25 : Eqn
  q25 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q27 : Eqn
  q27 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q30 : Eqn
  q30 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q32 : Eqn
  q32 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q33 : Eqn
  q33 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q34 : Eqn
  q34 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q35 : Eqn
  q35 = eqn (X2 ∷ Sw12 ∷ []) (Sw12 ∷ X1 ∷ []) (wn 215 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q38 : Eqn
  q38 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q41 : Eqn
  q41 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q42 : Eqn
  q42 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q43 : Eqn
  q43 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q44 : Eqn
  q44 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q45 : Eqn
  q45 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wn 216 W)
  q46 : Eqn
  q46 = eqn (X1 ∷ Sw01 ∷ []) (Sw01 ∷ X0 ∷ []) (wn 217 W)
  q47 : Eqn
  q47 = eqn (CK10 ∷ Sw01 ∷ []) (Sw01 ∷ CK01 ∷ []) (wn 218 W)
  q48 : Eqn
  q48 = eqn (X0 ∷ CK01 ∷ X0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (ax ck-tct)
  q49 : Eqn
  q49 = eqn (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) (wn 219 W)
  q50 : Eqn
  q50 = eqn (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) (wn 220 W)
  q51 : Eqn
  q51 = eqn (Sw01 ∷ CK01 ∷ []) (CK10 ∷ Sw01 ∷ []) (wn 221 W)
  q52 : Eqn
  q52 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q53 : Eqn
  q53 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q54 : Eqn
  q54 = eqn (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) (wn 222 W)
  q55 : Eqn
  q55 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 223 W)

-- pass [X2 CK20 X2] [TOFF012 CS03 TOFF012 CSd03]: 320 steps
lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X2 ∷ CK20 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 3 q14 ∷
   rw 6 q17 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 12 q18 ∷
   rw 11 q19 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   rw 10 q22 ∷
   re 11 5 (CS03 ∷ []) ∷
   rw 9 q17 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q23 ∷
   rw 7 q17 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q24 ∷
   rw 5 q19 ∷
   rw 6 q25 ∷
   rw 7 q26 ∷
   rw 8 q27 ∷
   rw 9 q28 ∷
   rw 10 q29 ∷
   rw 11 q28 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q30 ∷
   rw 13 q31 ∷
   rw 14 q30 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 13 q26 ∷
   rw 14 q32 ∷
   rw 7 q33 ∷
   re 7 8 (Toff123 ∷ []) ∷
   re 6 3 (Toff023 ∷ []) ∷
   re 4 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q34 ∷
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
   rw 10 q18 ∷
   rw 9 q19 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   rw 8 q22 ∷
   re 9 5 (CS03 ∷ []) ∷
   rw 7 q17 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q23 ∷
   rw 5 q17 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q24 ∷
   rw 3 q19 ∷
   rw 4 q25 ∷
   rw 5 q26 ∷
   rw 6 q27 ∷
   rw 7 q28 ∷
   rw 8 q29 ∷
   rw 9 q28 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q31 ∷
   rw 12 q30 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q26 ∷
   rw 12 q32 ∷
   rw 5 q33 ∷
   re 5 8 (Toff123 ∷ []) ∷
   re 4 3 (Toff023 ∷ []) ∷
   rw 2 q35 ∷
   re 1 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 3 q34 ∷
   rw 0 q35 ∷
   rw 7 q25 ∷
   re 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q36 ∷
   rw 7 q27 ∷
   rw 8 q37 ∷
   rw 9 q29 ∷
   rw 10 q37 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q30 ∷
   rw 12 q38 ∷
   rw 13 q30 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q36 ∷
   rw 13 q39 ∷
   rw 14 q40 ∷
   rw 13 q41 ∷
   rw 12 q42 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q30 ∷
   rw 12 q43 ∷
   rw⁻ 11 q30 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q44 ∷
   rw⁻ 9 q29 ∷
   rw 8 q44 ∷
   rw⁻ 7 q27 ∷
   rw 6 q42 ∷
   rw 7 q33 ∷
   re 7 8 (Toff123 ∷ []) ∷
   rw 5 q45 ∷
   re 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q36 ∷
   rw 5 q27 ∷
   rw 6 q37 ∷
   rw 7 q29 ∷
   rw 8 q37 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q30 ∷
   rw 10 q38 ∷
   rw 11 q30 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q36 ∷
   rw 11 q39 ∷
   rw 12 q40 ∷
   rw 11 q41 ∷
   rw 10 q42 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q30 ∷
   rw 10 q43 ∷
   rw⁻ 9 q30 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q44 ∷
   rw⁻ 7 q29 ∷
   rw 6 q44 ∷
   rw⁻ 5 q27 ∷
   rw 4 q42 ∷
   rw 5 q33 ∷
   re 5 8 (Toff123 ∷ []) ∷
   rw 3 q46 ∷
   rw 2 q47 ∷
   rw 1 q46 ∷
   rw 2 q48 ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q36 ∷
   rw 2 q27 ∷
   rw 3 q37 ∷
   rw 4 q29 ∷
   rw 5 q37 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q30 ∷
   rw 7 q38 ∷
   rw 8 q30 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q36 ∷
   rw 8 q39 ∷
   rw 1 q25 ∷
   rw 2 q26 ∷
   rw 3 q27 ∷
   rw 4 q28 ∷
   rw 5 q29 ∷
   rw 6 q28 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q30 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q26 ∷
   rw 9 q32 ∷
   rw 2 q33 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw 2 q49 ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q27 ∷
   rw 5 q37 ∷
   rw 6 q29 ∷
   rw 7 q37 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q30 ∷
   rw 9 q38 ∷
   rw 10 q30 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q36 ∷
   rw 10 q39 ∷
   rw 3 q25 ∷
   rw 4 q26 ∷
   rw 5 q27 ∷
   rw 6 q28 ∷
   rw 7 q29 ∷
   rw 8 q28 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q30 ∷
   rw 10 q31 ∷
   rw 11 q30 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q26 ∷
   rw 11 q32 ∷
   rw 4 q33 ∷
   re 4 8 (Toff123 ∷ []) ∷
   re 3 3 (Toff023 ∷ []) ∷
   rw 4 q50 ∷
   rw 5 q51 ∷
   rw 6 q50 ∷
   rw 7 q40 ∷
   re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q36 ∷
   rw 2 q27 ∷
   rw 3 q37 ∷
   rw 4 q29 ∷
   rw 5 q37 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q30 ∷
   rw 7 q38 ∷
   rw 8 q30 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q36 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw⁻ 0 q19 ∷
   rw 1 q52 ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 2 q34 ∷
   rw 3 q53 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q34 ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw⁻ 7 q21 ∷
   rw 8 q22 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw⁻ 6 q19 ∷
   rw⁻ 7 q18 ∷
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
   rw 3 q17 ∷
   re 1 3 (CS02 ∷ []) ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q27 ∷
   rw 5 q37 ∷
   rw 6 q29 ∷
   rw 7 q37 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q30 ∷
   rw 9 q38 ∷
   rw 10 q30 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q36 ∷
   rw 10 q39 ∷
   rw 11 q40 ∷
   rw⁻ 2 q19 ∷
   rw 3 q52 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q34 ∷
   rw 5 q53 ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q34 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw⁻ 9 q21 ∷
   rw 10 q22 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw⁻ 8 q19 ∷
   rw⁻ 9 q18 ∷
   rw 2 q1 ∷
   rw⁻ 3 q2 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q6 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 3 q54 ∷
   rw 6 q17 ∷
   re 4 3 (CK20 ∷ []) ∷
   rw 5 q54 ∷
   rw 6 q34 ∷
   rw 3 q55 ∷
   rw⁻ 0 q16 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q57 : Eqn
  q57 = eqn (X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ []) (wn 257 W)
  q58 : Eqn
  q58 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q59 : Eqn
  q59 = eqn (X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ []) (wn 258 W)
  q60 : Eqn
  q60 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q61 : Eqn
  q61 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2)

-- pass [X2 TOFF102 CS13 TOFF102 CSd13 X2] [CS03 TOFF012 CSd03 TOFF012]: 65 steps
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ [])
  (rw 7 q25 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q30 ∷
   rw 7 q43 ∷
   rw⁻ 6 q30 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 5 q56 ∷
   rw 6 q57 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q30 ∷
   rw 6 q38 ∷
   rw 7 q30 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q56 ∷
   rw 7 q40 ∷
   rw 6 q8 ∷
   rw 11 q25 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q30 ∷
   rw 11 q58 ∷
   rw⁻ 10 q30 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q56 ∷
   rw 10 q59 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q30 ∷
   rw 10 q60 ∷
   rw 11 q30 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q56 ∷
   rw 11 q40 ∷
   rw 10 q8 ∷
   rw 1 q61 ∷
   rw 2 q25 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q30 ∷
   rw 2 q43 ∷
   rw⁻ 1 q30 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q56 ∷
   rw 1 q57 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q30 ∷
   rw 1 q38 ∷
   rw 2 q30 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q56 ∷
   rw 2 q40 ∷
   rw 1 q13 ∷
   rw 4 q25 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q30 ∷
   rw 4 q58 ∷
   rw⁻ 3 q30 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 2 q56 ∷
   rw 3 q59 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q30 ∷
   rw 3 q60 ∷
   rw 4 q30 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q56 ∷
   rw 4 q40 ∷
   rw 3 q13 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ CS03⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF012-X2-CS03-X2-TOFF012-X2-CSd03)

-- pass [X2 TOFF102 CS13 TOFF102 CSd13 X2] [TOFF012 CS03 TOFF012 CSd03]: 65 steps
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-TOFF102-CS13-TOFF102-CSd13-X2-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ [])
  (rw 5 q8 ∷
   rw 10 q25 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q30 ∷
   rw 10 q43 ∷
   rw⁻ 9 q30 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 8 q56 ∷
   rw 9 q57 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q30 ∷
   rw 9 q38 ∷
   rw 10 q30 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q56 ∷
   rw 10 q40 ∷
   rw 9 q8 ∷
   rw 14 q25 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q30 ∷
   rw 14 q58 ∷
   rw⁻ 13 q30 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q56 ∷
   rw 13 q59 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q30 ∷
   rw 13 q60 ∷
   rw 14 q30 ∷
   re 12 3 (CS03⁻ ∷ []) ∷
   rw 13 q56 ∷
   rw 14 q40 ∷
   rw 1 q62 ∷
   rw 0 q13 ∷
   rw 3 q25 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q30 ∷
   rw 3 q43 ∷
   rw⁻ 2 q30 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 1 q56 ∷
   rw 2 q57 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q30 ∷
   rw 2 q38 ∷
   rw 3 q30 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q56 ∷
   rw 3 q40 ∷
   rw 2 q13 ∷
   rw 5 q25 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q30 ∷
   rw 5 q58 ∷
   rw⁻ 4 q30 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q56 ∷
   rw 4 q59 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q30 ∷
   rw 4 q60 ∷
   rw 5 q30 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q56 ∷
   rw 5 q40 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CCZ123 ∷ []) lem-pass-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [CCZ123]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CCZ123 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-CCZ123 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CCZ123 ∷ []) (CCZ123 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw⁻ 0 q63 ∷ []) Eq.refl
