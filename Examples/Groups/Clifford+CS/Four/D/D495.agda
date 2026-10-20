{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D495 (W : Ws) where

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
  q1 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q2 : Eqn
  q2 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q3 : Eqn
  q3 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q4 : Eqn
  q4 = eqn (CX01 ∷ CS23 ∷ []) (CS23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (CS))
  q5 : Eqn
  q5 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q6 : Eqn
  q6 = eqn (Sw12 ∷ CK13 ∷ []) (CK23 ∷ Sw12 ∷ []) (wn 352 W)
  q7 : Eqn
  q7 = eqn (CX01 ∷ CK23 ∷ []) (CK23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (CK₀₁))
  q8 : Eqn
  q8 = eqn (Sw12 ∷ CK23 ∷ []) (CK13 ∷ Sw12 ∷ []) (wn 357 W)
  q9 : Eqn
  q9 = eqn (CX02 ∷ S1 ∷ []) (S1 ∷ CX02 ∷ []) (wn 1247 W)
  q10 : Eqn
  q10 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = eqn (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ []) (CK12 ∷ S1 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK12 ∷ S1 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ []) (wn 1249 W)
  q12 : Eqn
  q12 = eqn (X0 ∷ CK23 ∷ []) (CK23 ∷ X0 ∷ []) (low₁-comm (X) ((CK₀₁ ↑)))
  q13 : Eqn
  q13 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (low₁-comm (X) ((CS ↑)))
  q14 : Eqn
  q14 = eqn (CX02 ∷ X0 ∷ CX01 ∷ X0 ∷ []) (X0 ∷ CX01 ∷ X0 ∷ CX02 ∷ []) (wn 1244 W)
  q15 : Eqn
  q15 = eqn (X0 ∷ S2 ∷ []) (S2 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑)))
  q16 : Eqn
  q16 = eqn (CX01 ∷ S2 ∷ []) (S2 ∷ CX01 ∷ []) (low-comm (CX₀₁) (S))
  q17 : Eqn
  q17 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q18 : Eqn
  q18 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q19 : Eqn
  q19 = eqn (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ CX01 ∷ X0 ∷ []) (X0 ∷ CX01 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ []) (wn 1245 W)
  q20 : Eqn
  q20 = eqn (CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (wn 1306 W)
  q21 : Eqn
  q21 = eqn (CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ []) (wn 1307 W)

-- Bar(SSKSKK;0,2->3) passes groups of WBar(SSKSKK;~0,1->3) part1: 500 steps
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part1 : ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ Sw23 ∷ CS12 ∷ CX03 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part1 = derive (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ Sw23 ∷ CS12 ∷ CX03 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (re 23 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q2 ∷
   re 23 3 (CX03 ∷ []) ∷
   re 23 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CS13 ∷ []) ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   re 24 5 (CX03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q2 ∷
   re 24 3 (CX03 ∷ []) ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CS13 ∷ []) ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 25 5 (CX03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 24 q2 ∷
   re 25 3 (CX03 ∷ []) ∷
   re 25 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CK13 ∷ []) ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   rw 26 q8 ∷
   re 26 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 26 5 (CX03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 24 3 (CK13 ∷ []) ∷
   rw 25 q9 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q2 ∷
   re 27 3 (CX03 ∷ []) ∷
   re 27 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q1 ∷
   re 28 5 (CX03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q2 ∷
   re 28 3 (CX03 ∷ []) ∷
   re 28 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CS13 ∷ []) ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   re 29 5 (CX03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q2 ∷
   re 29 3 (CX03 ∷ []) ∷
   re 29 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CS13 ∷ []) ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 30 5 (CX03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q2 ∷
   re 30 3 (CX03 ∷ []) ∷
   re 30 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CS13 ∷ []) ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 31 5 (CX03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q2 ∷
   re 31 3 (CX03 ∷ []) ∷
   re 31 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 35 3 (CS13 ∷ []) ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 32 5 (CX03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 34 q1 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   re 32 3 (CX03 ∷ []) ∷
   re 32 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 36 3 (CS13 ∷ []) ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 33 5 (CX03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 35 q1 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 32 q2 ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   rw 25 q10 ∷
   re 24 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 26 q1 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q1 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q1 ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q1 ∷
   rw 20 q10 ∷
   re 19 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 21 q1 ∷
   rw 18 q10 ∷
   re 17 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 19 q1 ∷
   re 16 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 18 q1 ∷
   re 15 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 17 q1 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q1 ∷
   re 13 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 15 q1 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q1 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q1 ∷
   rw 12 q11 ∷
   rw 13 q2 ∷
   re 11 3 (CK13 ∷ []) ∷
   rw⁻ 12 q10 ∷
   rw 15 q2 ∷
   re 13 3 (CK13 ∷ []) ∷
   rw⁻ 14 q10 ∷
   rw 17 q2 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 18 q2 ∷
   re 16 3 (CS13 ∷ []) ∷
   rw 19 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw 20 q2 ∷
   re 18 3 (CK13 ∷ []) ∷
   rw⁻ 19 q10 ∷
   rw 22 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 23 q2 ∷
   re 21 3 (CS13 ∷ []) ∷
   rw 24 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   rw 25 q2 ∷
   re 23 3 (CS13 ∷ []) ∷
   rw 26 q2 ∷
   re 24 3 (CS13 ∷ []) ∷
   rw 27 q2 ∷
   re 25 3 (CS13 ∷ []) ∷
   rw 28 q2 ∷
   re 26 3 (CS03 ∷ []) ∷
   rw 29 q2 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q2 ∷
   re 28 3 (CK03 ∷ []) ∷
   rw 31 q2 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CK03 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CK03 ∷ []) ∷
   rw 32 q1 ∷
   rw⁻ 54 q12 ∷
   rw⁻ 55 q7 ∷
   rw⁻ 56 q12 ∷
   rw⁻ 53 q12 ∷
   rw⁻ 54 q7 ∷
   rw⁻ 55 q12 ∷
   rw⁻ 52 q13 ∷
   rw⁻ 53 q4 ∷
   rw⁻ 54 q13 ∷
   rw⁻ 51 q12 ∷
   rw⁻ 52 q7 ∷
   rw⁻ 53 q12 ∷
   rw⁻ 50 q13 ∷
   rw⁻ 51 q4 ∷
   rw⁻ 52 q13 ∷
   rw⁻ 49 q13 ∷
   rw⁻ 50 q4 ∷
   rw⁻ 51 q13 ∷
   rw 48 q14 ∷
   rw⁻ 47 q13 ∷
   rw⁻ 48 q4 ∷
   rw⁻ 49 q13 ∷
   rw⁻ 46 q13 ∷
   rw⁻ 47 q4 ∷
   rw⁻ 48 q13 ∷
   rw⁻ 45 q13 ∷
   rw⁻ 46 q4 ∷
   rw⁻ 47 q13 ∷
   rw⁻ 44 q13 ∷
   rw⁻ 45 q4 ∷
   rw⁻ 46 q13 ∷
   rw⁻ 43 q13 ∷
   rw⁻ 44 q4 ∷
   rw⁻ 45 q13 ∷
   rw⁻ 42 q13 ∷
   rw⁻ 43 q4 ∷
   rw⁻ 44 q13 ∷
   rw⁻ 41 q15 ∷
   rw⁻ 42 q16 ∷
   rw⁻ 43 q15 ∷
   rw⁻ 40 q12 ∷
   rw⁻ 41 q7 ∷
   rw⁻ 42 q12 ∷
   rw⁻ 39 q13 ∷
   rw⁻ 40 q4 ∷
   rw⁻ 41 q13 ∷
   rw⁻ 38 q13 ∷
   rw⁻ 39 q4 ∷
   rw⁻ 40 q13 ∷
   rw⁻ 37 q13 ∷
   rw⁻ 38 q4 ∷
   rw⁻ 39 q13 ∷
   rw⁻ 36 q15 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 38 q15 ∷
   rw⁻ 35 q12 ∷
   rw⁻ 36 q7 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 34 q15 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 36 q15 ∷
   rw⁻ 33 q12 ∷
   rw⁻ 34 q7 ∷
   rw⁻ 35 q12 ∷
   rw 32 q14 ∷
   rw 35 q2 ∷
   rw 34 q17 ∷
   rw 33 q18 ∷
   rw 32 q17 ∷
   re 31 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 33 q1 ∷
   re 30 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 32 q1 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q1 ∷
   re 28 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 30 q1 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q1 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q1 ∷
   rw 27 q19 ∷
   rw⁻ 26 q17 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 28 q17 ∷
   rw 31 q2 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q2 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q2 ∷
   re 31 3 (CK03 ∷ []) ∷
   rw 34 q2 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q2 ∷
   re 33 3 (CK03 ∷ []) ∷
   rw 36 q2 ∷
   re 34 3 (CK03 ∷ []) ∷
   rw 35 q1 ∷
   rw 52 q20 ∷
   re 52 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 51 q2 ∷
   re 52 3 (CX03 ∷ []) ∷
   re 52 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 58 q2 ∷
   re 56 3 (CS13 ∷ []) ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q1 ∷
   re 53 5 (CX03 ∷ []) ∷
   re 53 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 51 3 (CS13 ∷ []) ∷
   re 53 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 52 q2 ∷
   re 53 3 (CX03 ∷ []) ∷
   re 53 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 59 q2 ∷
   re 57 3 (CS13 ∷ []) ∷
   rw 56 q3 ∷
   rw 55 q4 ∷
   rw 54 q5 ∷
   re 54 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 53 q1 ∷
   re 54 5 (CX03 ∷ []) ∷
   re 54 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 52 3 (CS13 ∷ []) ∷
   re 54 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 53 q2 ∷
   re 54 3 (CX03 ∷ []) ∷
   re 54 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 60 q2 ∷
   re 58 3 (CK13 ∷ []) ∷
   rw 57 q6 ∷
   rw 56 q7 ∷
   rw 55 q8 ∷
   re 55 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 54 q1 ∷
   re 55 5 (CX03 ∷ []) ∷
   re 55 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 53 3 (CK13 ∷ []) ∷
   re 55 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 54 q2 ∷
   re 55 3 (CX03 ∷ []) ∷
   re 55 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 61 q2 ∷
   re 59 3 (CS13 ∷ []) ∷
   rw 58 q3 ∷
   rw 57 q4 ∷
   rw 56 q5 ∷
   re 56 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 55 q1 ∷
   re 56 5 (CX03 ∷ []) ∷
   re 56 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 58 q1 ∷
   re 54 3 (CS13 ∷ []) ∷
   re 56 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 55 q2 ∷
   re 56 3 (CX03 ∷ []) ∷
   re 56 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 62 q2 ∷
   re 60 3 (CK13 ∷ []) ∷
   rw 59 q6 ∷
   rw 58 q7 ∷
   rw 57 q8 ∷
   re 57 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 56 q1 ∷
   re 57 5 (CX03 ∷ []) ∷
   re 57 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 59 q1 ∷
   re 55 3 (CK13 ∷ []) ∷
   re 57 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 56 q2 ∷
   re 57 3 (CX03 ∷ []) ∷
   re 57 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 63 q2 ∷
   re 61 3 (CK13 ∷ []) ∷
   rw 60 q6 ∷
   rw 59 q7 ∷
   rw 58 q8 ∷
   re 58 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 57 q1 ∷
   re 58 5 (CX03 ∷ []) ∷
   re 58 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 60 q1 ∷
   re 56 3 (CK13 ∷ []) ∷
   rw 36 q21 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 36 3 (CX03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q1 ∷
   re 37 5 (CX03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 35 3 (CS13 ∷ []) ∷
   re 37 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 37 3 (CX03 ∷ []) ∷
   re 37 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 43 q2 ∷
   re 41 3 (CS13 ∷ []) ∷
   rw 40 q3 ∷
   rw 39 q4 ∷
   rw 38 q5 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q1 ∷
   re 38 5 (CX03 ∷ []) ∷
   re 38 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 36 3 (CS13 ∷ []) ∷
   re 38 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 38 3 (CX03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q2 ∷
   re 42 3 (CK13 ∷ []) ∷
   rw 41 q6 ∷
   rw 40 q7 ∷
   rw 39 q8 ∷
   re 39 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 38 q1 ∷
   re 39 5 (CX03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 37 3 (CK13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 39 3 (CX03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q2 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 42 q3 ∷
   rw 41 q4 ∷
   rw 40 q5 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q1 ∷
   re 40 5 (CX03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 42 q1 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 40 3 (CX03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q2 ∷
   re 44 3 (CK13 ∷ []) ∷
   rw 43 q6 ∷
   rw 42 q7 ∷
   rw 41 q8 ∷
   re 41 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 40 q1 ∷
   re 41 5 (CX03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 43 q1 ∷
   re 39 3 (CK13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 41 3 (CX03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q2 ∷
   re 45 3 (CK13 ∷ []) ∷
   rw 44 q6 ∷
   rw 43 q7 ∷
   rw 42 q8 ∷
   re 42 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 41 q1 ∷
   re 42 5 (CX03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 44 q1 ∷
   re 40 3 (CK13 ∷ []) ∷ []) Eq.refl
