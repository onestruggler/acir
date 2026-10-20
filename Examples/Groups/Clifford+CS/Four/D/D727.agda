{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D727 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D711 W using (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02)

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
  q12 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q13 : Eqn
  q13 = eqn (X1 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ X1 ∷ []) (wn 2019 W)
  q14 : Eqn
  q14 = eqn (X1 ∷ CS02 ∷ []) (CS02 ∷ X1 ∷ []) (wn 1049 W)
  q15 : Eqn
  q15 = eqn (X1 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X1 ∷ []) (wn 1051 W)
  q16 : Eqn
  q16 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3-CS02-X1-X3-TOFF013-X1-X3-CSd02)
  q17 : Eqn
  q17 = eqn (X2 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (wn 2020 W)
  q18 : Eqn
  q18 = eqn (X1 ∷ X1 ∷ Toff012 ∷ X1 ∷ []) (Toff012 ∷ X1 ∷ []) (wn 2021 W)

-- pass [X1 X3 TOFF102 CS13 TOFF102 CSd13 X1 X3] [TOFF013 CS02 TOFF013 CSd02]: 513 steps
lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 : ⟪ (X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3-vs-TOFF013-CS02-TOFF013-CSd02 = derive (X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X1 ∷ X3 ∷ [])
  (rw 9 q1 ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   rw 15 q4 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 7 q9 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 8 q1 ∷
   rw⁻ 9 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw 9 q9 ∷
   rw 10 q9 ∷
   rw 11 q5 ∷
   rw⁻ 10 q10 ∷
   rw 13 q1 ∷
   re 12 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 13 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw⁻ 19 q4 ∷
   rw 20 q5 ∷
   rw 19 q4 ∷
   rw 18 q2 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 16 q3 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q3 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q2 ∷
   rw 13 q6 ∷
   re 13 8 (Toff012 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 11 q9 ∷
   re 13 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 12 q2 ∷
   rw 15 q1 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw⁻ 14 q3 ∷
   rw 17 q1 ∷
   re 15 3 (CS13⁻ ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw⁻ 19 q4 ∷
   rw 12 q1 ∷
   rw⁻ 13 q2 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q3 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw⁻ 17 q3 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw⁻ 19 q2 ∷
   rw⁻ 20 q4 ∷
   rw 13 q6 ∷
   re 13 8 (Toff012 ∷ []) ∷
   re 12 3 (Toff013 ∷ []) ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q5 ∷
   rw⁻ 14 q11 ∷
   rw 10 q1 ∷
   rw 9 q7 ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   rw 15 q4 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   rw⁻ 6 q12 ∷
   rw 7 q9 ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 8 q1 ∷
   rw⁻ 9 q2 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 16 q4 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw⁻ 9 q12 ∷
   rw 10 q9 ∷
   rw⁻ 11 q12 ∷
   rw 12 q5 ∷
   rw 11 q14 ∷
   rw 16 q1 ∷
   rw 15 q7 ∷
   re 14 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 15 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q4 ∷
   rw 22 q5 ∷
   rw 21 q4 ∷
   rw 20 q2 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q5 ∷
   rw 18 q3 ∷
   re 17 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 19 q5 ∷
   rw 16 q3 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q5 ∷
   rw 14 q2 ∷
   rw 15 q6 ∷
   re 15 8 (Toff012 ∷ []) ∷
   rw 13 q7 ∷
   rw 12 q12 ∷
   rw 13 q13 ∷
   rw⁻ 12 q12 ∷
   rw 13 q9 ∷
   re 15 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw 17 q1 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw⁻ 16 q3 ∷
   rw 19 q1 ∷
   re 17 3 (CS13⁻ ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw⁻ 21 q4 ∷
   rw 14 q1 ∷
   rw⁻ 15 q2 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q5 ∷
   rw⁻ 17 q3 ∷
   re 19 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q5 ∷
   rw⁻ 19 q3 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q5 ∷
   rw⁻ 21 q2 ∷
   rw⁻ 22 q4 ∷
   rw 15 q6 ∷
   re 15 8 (Toff012 ∷ []) ∷
   re 14 3 (Toff013 ∷ []) ∷
   rw⁻ 15 q12 ∷
   rw 16 q9 ∷
   rw⁻ 17 q12 ∷
   rw 18 q5 ∷
   rw 17 q15 ∷
   rw 2 q16 ∷
   rw 7 q1 ∷
   rw 6 q7 ∷
   rw 5 q12 ∷
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
   rw 2 q12 ∷
   rw 1 q7 ∷
   rw 2 q17 ∷
   rw⁻ 1 q12 ∷
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
   rw⁻ 3 q12 ∷
   rw 4 q9 ∷
   rw 5 q5 ∷
   rw⁻ 4 q10 ∷
   rw 11 q1 ∷
   rw 10 q7 ∷
   rw 9 q12 ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q2 ∷
   rw 11 q1 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw 13 q1 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q2 ∷
   rw⁻ 15 q4 ∷
   rw 16 q5 ∷
   rw 15 q4 ∷
   rw 14 q2 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q5 ∷
   rw 12 q3 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw 10 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 8 q2 ∷
   rw 9 q6 ∷
   re 9 8 (Toff012 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q12 ∷
   rw 5 q7 ∷
   rw 6 q17 ∷
   rw⁻ 5 q12 ∷
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
   rw⁻ 7 q12 ∷
   rw 8 q9 ∷
   rw 9 q5 ∷
   rw⁻ 8 q11 ∷
   rw 4 q1 ∷
   rw 3 q12 ∷
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
   rw 1 q12 ∷
   rw 0 q12 ∷
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
   rw⁻ 1 q12 ∷
   rw 2 q5 ∷
   rw 1 q14 ∷
   rw 6 q1 ∷
   rw 5 q12 ∷
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
   rw 3 q12 ∷
   rw 2 q12 ∷
   rw 3 q18 ∷
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
   rw⁻ 3 q12 ∷
   rw 4 q5 ∷
   rw 3 q15 ∷ []) Eq.refl
