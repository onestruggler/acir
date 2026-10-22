{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D502 (W : Ws) where

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
  q2 = wE 352 W
  q3 : Eqn
  q3 = eqn (CX01 ∷ CK23 ∷ []) (CK23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (CK₀₁))
  q4 : Eqn
  q4 = wE 357 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 1282 W

-- Bar(SSSKSS;0,2->3) passes groups of WBar(SSKSKK;~0,1->3) part2: 67 steps
lem-Bar⟨SSSKSS02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part2 : ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ CX02 ∷ CK13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ
lem-Bar⟨SSSKSS02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part2 = derive (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ Sw23 ∷ CK12 ∷ Sw23 ∷ CX02 ∷ CK13 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CS03 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CS23 ∷ [])
  (re 39 3 (CK13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 41 3 (CX03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CK13 ∷ []) ∷
   rw 44 q2 ∷
   rw 43 q3 ∷
   rw 42 q4 ∷
   re 42 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 42 5 (CX03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 40 3 (CK13 ∷ []) ∷
   rw 41 q1 ∷
   re 40 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 39 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   re 37 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 32 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   rw 31 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS13 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CK13 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CK13 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CK13 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CK03 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 41 q5 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = wE 1106 W
  q9 : Eqn
  q9 = wE 772 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q12 : Eqn
  q12 = wE 74 W
  q13 : Eqn
  q13 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q14 : Eqn
  q14 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 1321 W
  q17 : Eqn
  q17 = wE 317 W
  q18 : Eqn
  q18 = wE 329 W
  q19 : Eqn
  q19 = wE 27 W
  q20 : Eqn
  q20 = wE 30 W
  q21 : Eqn
  q21 = wE 31 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX02 CK23 S2 CK23 S2 CS23 CS23 CS23 CK23 S2 CS23 CS23 CS23 CS23 CS23 CS23 CX02 CS23 CS23 CK23 CS23 CK23 CK23] [X0 CK02 X0]: 115 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CK02-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX02-CK23-S2-CK23-S2-CS23-CS23-CS23-CK23-S2-CS23-CS23-CS23-CS23-CS23-CS23-CX02-CS23-CS23-CK23-CS23-CK23-CK23-vs-X0-CK02-X0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw 32 q7 ∷
   rw 31 q8 ∷
   rw 30 q9 ∷
   rw 29 q8 ∷
   rw⁻ 28 q10 ∷
   rw⁻ 27 q10 ∷
   rw⁻ 26 q11 ∷
   rw⁻ 25 q10 ∷
   rw⁻ 24 q11 ∷
   rw⁻ 23 q11 ∷
   rw 22 q12 ∷
   rw⁻ 21 q11 ∷
   rw⁻ 20 q11 ∷
   rw⁻ 19 q11 ∷
   rw⁻ 18 q11 ∷
   rw⁻ 17 q11 ∷
   rw⁻ 16 q11 ∷
   rw⁻ 15 q13 ∷
   rw⁻ 14 q10 ∷
   rw⁻ 13 q11 ∷
   rw⁻ 12 q11 ∷
   rw⁻ 11 q11 ∷
   rw⁻ 10 q13 ∷
   rw⁻ 9 q10 ∷
   rw⁻ 8 q13 ∷
   rw⁻ 7 q10 ∷
   rw 6 q12 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q14 ∷
   rw 6 q9 ∷
   rw⁻ 5 q14 ∷
   re 6 3 (CK13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q14 ∷
   rw 5 q9 ∷
   rw⁻ 4 q14 ∷
   re 5 3 (CK13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q14 ∷
   rw 4 q15 ∷
   rw⁻ 3 q14 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q14 ∷
   rw 3 q9 ∷
   rw⁻ 2 q14 ∷
   re 3 3 (CK13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q14 ∷
   rw 2 q15 ∷
   rw⁻ 1 q14 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q14 ∷
   rw 1 q15 ∷
   rw⁻ 0 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q16 ∷
   rw 0 q17 ∷
   rw 1 q18 ∷
   rw 2 q17 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q14 ∷
   rw 4 q19 ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   rw 5 q19 ∷
   rw 6 q14 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q14 ∷
   rw 6 q18 ∷
   rw 7 q14 ∷
   re 5 3 (CK03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   rw 7 q19 ∷
   rw 8 q14 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q14 ∷
   rw 8 q18 ∷
   rw 9 q14 ∷
   re 7 3 (CK03 ∷ []) ∷
   re 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   rw 9 q18 ∷
   rw 10 q14 ∷
   re 8 3 (CK03 ∷ []) ∷
   rw 9 q20 ∷
   rw 10 q10 ∷
   rw 11 q13 ∷
   rw 12 q10 ∷
   rw 13 q13 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   rw 17 q10 ∷
   rw 18 q13 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   rw 24 q11 ∷
   rw 25 q20 ∷
   rw 26 q11 ∷
   rw 27 q11 ∷
   rw 28 q10 ∷
   rw 29 q11 ∷
   rw 30 q10 ∷
   rw 31 q10 ∷
   rw 32 q21 ∷ []) Eq.refl
