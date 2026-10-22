{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D496 (W : Ws) where

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
  q3 = wE 1252 W

-- Bar(SSKSKK;0,2->3) passes groups of WBar(SSKSKK;~0,1->3) part2: 51 steps
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part2 : ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part2 = derive (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ [])
  (rw 41 q1 ∷
   re 40 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 42 q2 ∷
   re 39 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 41 q2 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q2 ∷
   re 37 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 39 q2 ∷
   re 36 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q2 ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q2 ∷
   re 34 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 36 q2 ∷
   re 33 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 35 q2 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q2 ∷
   re 31 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 33 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q2 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
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
   re 37 3 (CK03 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CK03 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CK03 ∷ []) ∷
   rw 41 q2 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = eqn (X0 ∷ CK13 ∷ []) (CK13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CK₀₁ • Swap ↑)))
  q5 : Eqn
  q5 = wE 1052 W
  q6 : Eqn
  q6 = eqn (CK01 ∷ CK23 ∷ []) (CK23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CK₀₁))
  q7 : Eqn
  q7 = wE 1053 W
  q8 : Eqn
  q8 = eqn (X0 ∷ CS13 ∷ []) (CS13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q9 : Eqn
  q9 = wE 65 W
  q10 : Eqn
  q10 = eqn (CK01 ∷ CS23 ∷ []) (CS23 ∷ CK01 ∷ []) (low-comm (CK₀₁) (CS))
  q11 : Eqn
  q11 = wE 48 W
  q12 : Eqn
  q12 = wE 1253 W
  q13 : Eqn
  q13 = eqn (X0 ∷ S1 ∷ []) (S1 ∷ X0 ∷ []) (low₁-comm (X) (S))
  q14 : Eqn
  q14 = wE 1254 W
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = wE 1106 W
  q17 : Eqn
  q17 = wE 772 W
  q18 : Eqn
  q18 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 1308 W
  q20 : Eqn
  q20 = wE 317 W
  q21 : Eqn
  q21 = wE 329 W
  q22 : Eqn
  q22 = wE 31 W
  q23 : Eqn
  q23 = wE 7 W
  q24 : Eqn
  q24 = wE 1309 W
  q25 : Eqn
  q25 = wE 27 W

-- pass [CS03 CS03 CK03 CS03 CK03 CK03 CX01 CK13 S1 CK13 S1 CS13 CS13 CS13 CK13 S1 CS13 CS13 CS13 CS13 CS13 CS13 CX01 CS13 CS13 CK13 CS13 CK13 CK13] [X0 CK02 X0]: 251 steps
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-CK02-X0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-pass-CS03-CS03-CK03-CS03-CK03-CK03-CX01-CK13-S1-CK13-S1-CS13-CS13-CS13-CK13-S1-CS13-CS13-CS13-CS13-CS13-CS13-CX01-CS13-CS13-CK13-CS13-CK13-CK13-vs-X0-CK02-X0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X0 ∷ CK02 ∷ X0 ∷ []) (X0 ∷ CK02 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX01 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CX01 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  (rw⁻ 28 q4 ∷
   re 30 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 29 q5 ∷
   rw⁻ 30 q6 ∷
   rw 31 q7 ∷
   re 29 3 (CK02 ∷ []) ∷
   rw⁻ 30 q4 ∷
   rw⁻ 27 q4 ∷
   re 29 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 28 q5 ∷
   rw⁻ 29 q6 ∷
   rw 30 q7 ∷
   re 28 3 (CK02 ∷ []) ∷
   rw⁻ 29 q4 ∷
   rw⁻ 26 q8 ∷
   re 28 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 27 q9 ∷
   rw⁻ 28 q10 ∷
   rw 29 q11 ∷
   re 27 3 (CK02 ∷ []) ∷
   rw⁻ 28 q8 ∷
   rw⁻ 25 q4 ∷
   re 27 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 26 q5 ∷
   rw⁻ 27 q6 ∷
   rw 28 q7 ∷
   re 26 3 (CK02 ∷ []) ∷
   rw⁻ 27 q4 ∷
   rw⁻ 24 q8 ∷
   re 26 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 25 q9 ∷
   rw⁻ 26 q10 ∷
   rw 27 q11 ∷
   re 25 3 (CK02 ∷ []) ∷
   rw⁻ 26 q8 ∷
   rw⁻ 23 q8 ∷
   re 25 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 24 q9 ∷
   rw⁻ 25 q10 ∷
   rw 26 q11 ∷
   re 24 3 (CK02 ∷ []) ∷
   rw⁻ 25 q8 ∷
   rw 22 q12 ∷
   rw⁻ 21 q8 ∷
   re 23 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 22 q9 ∷
   rw⁻ 23 q10 ∷
   rw 24 q11 ∷
   re 22 3 (CK02 ∷ []) ∷
   rw⁻ 23 q8 ∷
   rw⁻ 20 q8 ∷
   re 22 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 21 q9 ∷
   rw⁻ 22 q10 ∷
   rw 23 q11 ∷
   re 21 3 (CK02 ∷ []) ∷
   rw⁻ 22 q8 ∷
   rw⁻ 19 q8 ∷
   re 21 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 20 q9 ∷
   rw⁻ 21 q10 ∷
   rw 22 q11 ∷
   re 20 3 (CK02 ∷ []) ∷
   rw⁻ 21 q8 ∷
   rw⁻ 18 q8 ∷
   re 20 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 19 q9 ∷
   rw⁻ 20 q10 ∷
   rw 21 q11 ∷
   re 19 3 (CK02 ∷ []) ∷
   rw⁻ 20 q8 ∷
   rw⁻ 17 q8 ∷
   re 19 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 18 q9 ∷
   rw⁻ 19 q10 ∷
   rw 20 q11 ∷
   re 18 3 (CK02 ∷ []) ∷
   rw⁻ 19 q8 ∷
   rw⁻ 16 q8 ∷
   re 18 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 17 q9 ∷
   rw⁻ 18 q10 ∷
   rw 19 q11 ∷
   re 17 3 (CK02 ∷ []) ∷
   rw⁻ 18 q8 ∷
   rw⁻ 15 q13 ∷
   rw 16 q14 ∷
   rw⁻ 17 q13 ∷
   rw⁻ 14 q4 ∷
   re 16 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 15 q5 ∷
   rw⁻ 16 q6 ∷
   rw 17 q7 ∷
   re 15 3 (CK02 ∷ []) ∷
   rw⁻ 16 q4 ∷
   rw⁻ 13 q8 ∷
   re 15 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 14 q9 ∷
   rw⁻ 15 q10 ∷
   rw 16 q11 ∷
   re 14 3 (CK02 ∷ []) ∷
   rw⁻ 15 q8 ∷
   rw⁻ 12 q8 ∷
   re 14 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 13 q9 ∷
   rw⁻ 14 q10 ∷
   rw 15 q11 ∷
   re 13 3 (CK02 ∷ []) ∷
   rw⁻ 14 q8 ∷
   rw⁻ 11 q8 ∷
   re 13 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 12 q9 ∷
   rw⁻ 13 q10 ∷
   rw 14 q11 ∷
   re 12 3 (CK02 ∷ []) ∷
   rw⁻ 13 q8 ∷
   rw⁻ 10 q13 ∷
   rw 11 q14 ∷
   rw⁻ 12 q13 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q6 ∷
   rw 12 q7 ∷
   re 10 3 (CK02 ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw⁻ 8 q13 ∷
   rw 9 q14 ∷
   rw⁻ 10 q13 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw12 ∷ CK01 ∷ Sw12 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q6 ∷
   rw 10 q7 ∷
   re 8 3 (CK02 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 6 q12 ∷
   rw 9 q15 ∷
   rw 8 q16 ∷
   rw 7 q17 ∷
   rw 6 q16 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q18 ∷
   rw 6 q17 ∷
   rw⁻ 5 q18 ∷
   re 6 3 (CK13 ∷ []) ∷
   rw 6 q19 ∷
   rw 5 q20 ∷
   rw 6 q21 ∷
   rw 7 q20 ∷
   re 9 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 9 q21 ∷
   rw 10 q18 ∷
   re 8 3 (CK03 ∷ []) ∷
   rw 9 q22 ∷
   rw 8 q15 ∷
   rw 7 q16 ∷
   rw 6 q17 ∷
   rw 5 q16 ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q18 ∷
   rw 5 q17 ∷
   rw⁻ 4 q18 ∷
   re 5 3 (CK13 ∷ []) ∷
   rw 5 q19 ∷
   rw 4 q20 ∷
   rw 5 q21 ∷
   rw 6 q20 ∷
   re 8 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 8 q21 ∷
   rw 9 q18 ∷
   re 7 3 (CK03 ∷ []) ∷
   rw 8 q22 ∷
   rw 7 q15 ∷
   rw 6 q16 ∷
   rw 5 q17 ∷
   rw 4 q16 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q18 ∷
   rw 4 q23 ∷
   rw⁻ 3 q18 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 4 q24 ∷
   rw 3 q20 ∷
   rw 4 q21 ∷
   rw 5 q20 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 7 q25 ∷
   rw 8 q18 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q22 ∷
   rw 6 q15 ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   rw 3 q16 ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q18 ∷
   rw 3 q17 ∷
   rw⁻ 2 q18 ∷
   re 3 3 (CK13 ∷ []) ∷
   rw 3 q19 ∷
   rw 2 q20 ∷
   rw 3 q21 ∷
   rw 4 q20 ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw 6 q21 ∷
   rw 7 q18 ∷
   re 5 3 (CK03 ∷ []) ∷
   rw 6 q22 ∷
   rw 5 q15 ∷
   rw 4 q16 ∷
   rw 3 q17 ∷
   rw 2 q16 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q18 ∷
   rw 2 q23 ∷
   rw⁻ 1 q18 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 2 q24 ∷
   rw 1 q20 ∷
   rw 2 q21 ∷
   rw 3 q20 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   rw 5 q25 ∷
   rw 6 q18 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q22 ∷
   rw 4 q15 ∷
   rw 3 q16 ∷
   rw 2 q17 ∷
   rw 1 q16 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q18 ∷
   rw 1 q23 ∷
   rw⁻ 0 q18 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q24 ∷
   rw 0 q20 ∷
   rw 1 q21 ∷
   rw 2 q20 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   rw 4 q25 ∷
   rw 5 q18 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q22 ∷ []) Eq.refl
