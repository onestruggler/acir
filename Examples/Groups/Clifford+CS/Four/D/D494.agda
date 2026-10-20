{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D494 (W : Ws) where

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
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (X0 ∷ Sw01 ∷ []) (Sw01 ∷ X1 ∷ []) (wn 1106 W)
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = eqn (CK02 ∷ Sw01 ∷ []) (Sw01 ∷ CK12 ∷ []) (wn 772 W)
  q5 : Eqn
  q5 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CK23 ∷ []) (CK23 ∷ Sw01 ∷ []) (low-comm (Swap) (CK₀₁))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q8 : Eqn
  q8 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q10 : Eqn
  q10 = eqn (CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X1 ∷ []) (X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ X1 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ CX12 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX12 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (wn 1303 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ X1 ∷ []) (X0 ∷ Sw01 ∷ []) (wn 317 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CK12 ∷ []) (CK02 ∷ Sw01 ∷ []) (wn 329 W)
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q16 : Eqn
  q16 = eqn (X0 ∷ CK23 ∷ []) (CK23 ∷ X0 ∷ []) (low₁-comm (X) ((CK₀₁ ↑)))
  q17 : Eqn
  q17 = eqn (CX01 ∷ CK23 ∷ []) (CK23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (CK₀₁))
  q18 : Eqn
  q18 = eqn (X0 ∷ CS23 ∷ []) (CS23 ∷ X0 ∷ []) (low₁-comm (X) ((CS ↑)))
  q19 : Eqn
  q19 = eqn (CX01 ∷ CS23 ∷ []) (CS23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (CS))
  q20 : Eqn
  q20 = eqn (CX02 ∷ X0 ∷ CX01 ∷ X0 ∷ []) (X0 ∷ CX01 ∷ X0 ∷ CX02 ∷ []) (wn 1244 W)
  q21 : Eqn
  q21 = eqn (X0 ∷ S2 ∷ []) (S2 ∷ X0 ∷ []) (low₁-comm (X) ((S ↑)))
  q22 : Eqn
  q22 = eqn (CX01 ∷ S2 ∷ []) (S2 ∷ CX01 ∷ []) (low-comm (CX₀₁) (S))
  q23 : Eqn
  q23 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q24 : Eqn
  q24 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q26 : Eqn
  q26 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q27 : Eqn
  q27 = eqn (CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ X0 ∷ CX01 ∷ X0 ∷ []) (X0 ∷ CX01 ∷ X0 ∷ CS02 ∷ CS02 ∷ CK02 ∷ CS02 ∷ CK02 ∷ CK02 ∷ []) (wn 1245 W)
  q28 : Eqn
  q28 = eqn (CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ []) (wn 1304 W)
  q29 : Eqn
  q29 = eqn (Sw12 ∷ CK13 ∷ []) (CK23 ∷ Sw12 ∷ []) (wn 352 W)
  q30 : Eqn
  q30 = eqn (Sw12 ∷ CK23 ∷ []) (CK13 ∷ Sw12 ∷ []) (wn 357 W)
  q31 : Eqn
  q31 = eqn (CX02 ∷ S1 ∷ []) (S1 ∷ CX02 ∷ []) (wn 1247 W)
  q32 : Eqn
  q32 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q33 : Eqn
  q33 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q34 : Eqn
  q34 = eqn (CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ []) (CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ []) (wn 1305 W)

-- Bar(SSKSKK;0,2->3) passes groups of WBar(SSKSKK;~0,1->3) part0: 500 steps
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part0 : ⟪ (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ Sw23 ∷ CS12 ∷ CX03 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part0 = derive (CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CX02 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ []) (X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ X0 ∷ X0 ∷ CX01 ∷ X0 ∷ CS03 ∷ CS03 ∷ CK03 ∷ CS03 ∷ CK03 ∷ CK03 ∷ CK13 ∷ S1 ∷ CK13 ∷ S1 ∷ Sw23 ∷ CS12 ∷ CX03 ∷ Sw23 ∷ CS13 ∷ CS13 ∷ CK13 ∷ S1 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK23 ∷ S2 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CK23 ∷ S2 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CX02 ∷ CS23 ∷ CS23 ∷ CK23 ∷ CS23 ∷ CK23 ∷ CK23 ∷ X0 ∷ CX01 ∷ X0 ∷ CS13 ∷ CS13 ∷ CK13 ∷ CS13 ∷ CK13 ∷ CK13 ∷ [])
  (rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 37 q3 ∷
   rw 36 q4 ∷
   rw⁻ 35 q3 ∷
   re 36 3 (CK13 ∷ []) ∷
   re 34 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 36 q3 ∷
   rw 35 q4 ∷
   rw⁻ 34 q3 ∷
   re 35 3 (CK13 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q3 ∷
   rw 34 q5 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (CK13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q3 ∷
   rw 32 q5 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q5 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CS13 ∷ []) ∷
   rw 29 q2 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 27 q6 ∷
   rw⁻ 26 q7 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 23 q7 ∷
   rw 22 q8 ∷
   rw⁻ 21 q7 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 18 q7 ∷
   rw⁻ 17 q7 ∷
   rw⁻ 16 q7 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 13 q7 ∷
   rw⁻ 12 q7 ∷
   rw⁻ 11 q7 ∷
   rw⁻ 10 q9 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 8 q9 ∷
   rw⁻ 7 q6 ∷
   rw 6 q8 ∷
   re 5 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (CK13 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 5 q4 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (CK13 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 4 q5 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (CS13 ∷ []) ∷
   re 2 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (CK13 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 2 q5 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q3 ∷
   rw 1 q5 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q10 ∷
   rw 0 q11 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q12 ∷
   rw 3 q3 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw 3 q12 ∷
   rw 4 q3 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 4 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw 4 q13 ∷
   rw 5 q3 ∷
   re 3 3 (CK03 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q12 ∷
   rw 6 q3 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q13 ∷
   rw 7 q3 ∷
   re 5 3 (CK03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q13 ∷
   rw 8 q3 ∷
   re 6 3 (CK03 ∷ []) ∷
   rw 7 q11 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 9 q12 ∷
   rw 10 q3 ∷
   re 8 3 (CS03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 10 q12 ∷
   rw 11 q3 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   rw 11 q13 ∷
   rw 12 q3 ∷
   re 10 3 (CK03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   rw 12 q12 ∷
   rw 13 q3 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q13 ∷
   rw 14 q3 ∷
   re 12 3 (CK03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   rw 14 q13 ∷
   rw 15 q3 ∷
   re 13 3 (CK03 ∷ []) ∷
   rw 14 q14 ∷
   rw 15 q6 ∷
   rw 16 q9 ∷
   rw 17 q6 ∷
   rw 18 q9 ∷
   rw 19 q7 ∷
   rw 20 q7 ∷
   rw 21 q7 ∷
   rw 22 q6 ∷
   rw 23 q9 ∷
   rw 24 q7 ∷
   rw 25 q7 ∷
   rw 26 q7 ∷
   rw 27 q7 ∷
   rw 28 q7 ∷
   rw 29 q7 ∷
   rw 30 q14 ∷
   rw 31 q7 ∷
   rw 32 q7 ∷
   rw 33 q6 ∷
   rw 34 q7 ∷
   rw 35 q6 ∷
   rw 36 q6 ∷
   rw 37 q15 ∷
   rw⁻ 36 q16 ∷
   rw⁻ 37 q17 ∷
   rw⁻ 38 q16 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 36 q17 ∷
   rw⁻ 37 q16 ∷
   rw⁻ 34 q18 ∷
   rw⁻ 35 q19 ∷
   rw⁻ 36 q18 ∷
   rw⁻ 33 q16 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 35 q16 ∷
   rw⁻ 32 q18 ∷
   rw⁻ 33 q19 ∷
   rw⁻ 34 q18 ∷
   rw⁻ 31 q18 ∷
   rw⁻ 32 q19 ∷
   rw⁻ 33 q18 ∷
   rw 30 q20 ∷
   rw⁻ 29 q18 ∷
   rw⁻ 30 q19 ∷
   rw⁻ 31 q18 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 28 q19 ∷
   rw⁻ 29 q18 ∷
   rw⁻ 26 q18 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 25 q18 ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 24 q18 ∷
   rw⁻ 25 q19 ∷
   rw⁻ 26 q18 ∷
   rw⁻ 23 q21 ∷
   rw⁻ 24 q22 ∷
   rw⁻ 25 q21 ∷
   rw⁻ 22 q16 ∷
   rw⁻ 23 q17 ∷
   rw⁻ 24 q16 ∷
   rw⁻ 21 q18 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q18 ∷
   rw⁻ 20 q18 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q18 ∷
   rw⁻ 19 q18 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q18 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 19 q22 ∷
   rw⁻ 20 q21 ∷
   rw⁻ 17 q16 ∷
   rw⁻ 18 q17 ∷
   rw⁻ 19 q16 ∷
   rw⁻ 16 q21 ∷
   rw⁻ 17 q22 ∷
   rw⁻ 18 q21 ∷
   rw⁻ 15 q16 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q16 ∷
   rw 14 q20 ∷
   rw 17 q23 ∷
   rw 16 q24 ∷
   rw 15 q25 ∷
   rw 14 q24 ∷
   re 13 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 15 q26 ∷
   re 12 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 14 q26 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q26 ∷
   re 10 1 (Sw23 ∷ CK02 ∷ Sw23 ∷ []) ∷
   rw 12 q26 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q26 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q26 ∷
   rw 9 q27 ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q25 ∷
   rw⁻ 10 q24 ∷
   rw 13 q23 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q23 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q23 ∷
   re 13 3 (CK03 ∷ []) ∷
   rw 16 q23 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q23 ∷
   re 15 3 (CK03 ∷ []) ∷
   rw 18 q23 ∷
   re 16 3 (CK03 ∷ []) ∷
   rw 17 q26 ∷
   rw 34 q28 ∷
   re 34 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 33 q23 ∷
   re 34 3 (CX03 ∷ []) ∷
   re 34 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 40 q23 ∷
   re 38 3 (CK13 ∷ []) ∷
   rw 37 q29 ∷
   rw 36 q17 ∷
   rw 35 q30 ∷
   re 35 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 34 q26 ∷
   re 35 5 (CX03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 37 q26 ∷
   re 33 3 (CK13 ∷ []) ∷
   rw 34 q31 ∷
   re 36 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 35 q23 ∷
   re 36 3 (CX03 ∷ []) ∷
   re 36 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 42 q23 ∷
   re 40 3 (CK13 ∷ []) ∷
   rw 39 q29 ∷
   rw 38 q17 ∷
   rw 37 q30 ∷
   re 37 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 36 q26 ∷
   re 37 5 (CX03 ∷ []) ∷
   re 37 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 39 q26 ∷
   re 35 3 (CK13 ∷ []) ∷
   rw 36 q31 ∷
   re 38 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 37 q23 ∷
   re 38 3 (CX03 ∷ []) ∷
   re 38 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 44 q23 ∷
   re 42 3 (CS13 ∷ []) ∷
   rw 41 q32 ∷
   rw 40 q19 ∷
   rw 39 q33 ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q26 ∷
   re 39 5 (CX03 ∷ []) ∷
   re 39 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 41 q26 ∷
   re 37 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 38 q23 ∷
   re 39 3 (CX03 ∷ []) ∷
   re 39 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 45 q23 ∷
   re 43 3 (CS13 ∷ []) ∷
   rw 42 q32 ∷
   rw 41 q19 ∷
   rw 40 q33 ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q26 ∷
   re 40 5 (CX03 ∷ []) ∷
   re 40 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 42 q26 ∷
   re 38 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 39 q23 ∷
   re 40 3 (CX03 ∷ []) ∷
   re 40 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 46 q23 ∷
   re 44 3 (CS13 ∷ []) ∷
   rw 43 q32 ∷
   rw 42 q19 ∷
   rw 41 q33 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q26 ∷
   re 41 5 (CX03 ∷ []) ∷
   re 41 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 43 q26 ∷
   re 39 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 40 q23 ∷
   re 41 3 (CX03 ∷ []) ∷
   re 41 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 47 q23 ∷
   re 45 3 (CK13 ∷ []) ∷
   rw 44 q29 ∷
   rw 43 q17 ∷
   rw 42 q30 ∷
   re 42 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 41 q26 ∷
   re 42 5 (CX03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 44 q26 ∷
   re 40 3 (CK13 ∷ []) ∷
   rw 41 q31 ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q23 ∷
   re 43 3 (CX03 ∷ []) ∷
   re 43 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 49 q23 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 46 q32 ∷
   rw 45 q19 ∷
   rw 44 q33 ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q26 ∷
   re 44 5 (CX03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 46 q26 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q23 ∷
   re 44 3 (CX03 ∷ []) ∷
   re 44 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 50 q23 ∷
   re 48 3 (CS13 ∷ []) ∷
   rw 47 q32 ∷
   rw 46 q19 ∷
   rw 45 q33 ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q26 ∷
   re 45 5 (CX03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 47 q26 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q23 ∷
   re 45 3 (CX03 ∷ []) ∷
   re 45 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 51 q23 ∷
   re 49 3 (CS13 ∷ []) ∷
   rw 48 q32 ∷
   rw 47 q19 ∷
   rw 46 q33 ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q26 ∷
   re 46 5 (CX03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 48 q26 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q23 ∷
   re 46 3 (CX03 ∷ []) ∷
   re 46 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 52 q23 ∷
   re 50 3 (CS13 ∷ []) ∷
   rw 49 q32 ∷
   rw 48 q19 ∷
   rw 47 q33 ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q26 ∷
   re 47 5 (CX03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 49 q26 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q23 ∷
   re 47 3 (CX03 ∷ []) ∷
   re 47 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 53 q23 ∷
   re 51 3 (CS13 ∷ []) ∷
   rw 50 q32 ∷
   rw 49 q19 ∷
   rw 48 q33 ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q26 ∷
   re 48 5 (CX03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 50 q26 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q23 ∷
   re 48 3 (CX03 ∷ []) ∷
   re 48 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 54 q23 ∷
   re 52 3 (CS13 ∷ []) ∷
   rw 51 q32 ∷
   rw 50 q19 ∷
   rw 49 q33 ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q26 ∷
   re 49 5 (CX03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 51 q26 ∷
   re 47 3 (CS13 ∷ []) ∷
   rw 18 q34 ∷
   re 18 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 17 q23 ∷
   re 18 3 (CX03 ∷ []) ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 24 q23 ∷
   re 22 3 (CK13 ∷ []) ∷
   rw 21 q29 ∷
   rw 20 q17 ∷
   rw 19 q30 ∷
   re 19 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 18 q26 ∷
   re 19 5 (CX03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 21 q26 ∷
   re 17 3 (CK13 ∷ []) ∷
   rw 18 q31 ∷
   re 20 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 19 q23 ∷
   re 20 3 (CX03 ∷ []) ∷
   re 20 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 26 q23 ∷
   re 24 3 (CK13 ∷ []) ∷
   rw 23 q29 ∷
   rw 22 q17 ∷
   rw 21 q30 ∷
   re 21 1 (Sw23 ∷ CK12 ∷ Sw23 ∷ []) ∷
   rw 20 q26 ∷
   re 21 5 (CX03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 23 q26 ∷
   re 19 3 (CK13 ∷ []) ∷
   rw 20 q31 ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q23 ∷
   re 22 3 (CX03 ∷ []) ∷
   re 22 1 (Sw23 ∷ Sw12 ∷ CX01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 28 q23 ∷
   re 26 3 (CS13 ∷ []) ∷
   rw 25 q32 ∷
   rw 24 q19 ∷
   rw 23 q33 ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q26 ∷
   re 23 5 (CX03 ∷ []) ∷ []) Eq.refl
