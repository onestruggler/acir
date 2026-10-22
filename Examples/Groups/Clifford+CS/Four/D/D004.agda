{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D004 (W : Ws) where

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
  q1 = wE 2 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 4 W
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 43 W
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = wE 6 W
  q10 : Eqn
  q10 = wE 7 W
  q11 : Eqn
  q11 = wE 8 W
  q12 : Eqn
  q12 = wE 9 W
  q13 : Eqn
  q13 = wE 10 W
  q14 : Eqn
  q14 = wE 11 W
  q15 : Eqn
  q15 = wE 12 W
  q16 : Eqn
  q16 = wE 13 W
  q17 : Eqn
  q17 = wE 14 W
  q18 : Eqn
  q18 = wE 15 W
  q19 : Eqn
  q19 = wE 16 W
  q20 : Eqn
  q20 = wE 17 W
  q21 : Eqn
  q21 = eqn (CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz)
  q22 : Eqn
  q22 = wE 18 W
  q23 : Eqn
  q23 = wE 19 W
  q24 : Eqn
  q24 = wE 20 W
  q25 : Eqn
  q25 = wE 21 W
  q26 : Eqn
  q26 = wE 22 W
  q27 : Eqn
  q27 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q28 : Eqn
  q28 = wE 23 W
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q30 : Eqn
  q30 = wE 24 W
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q32 : Eqn
  q32 = wE 25 W
  q33 : Eqn
  q33 = wE 26 W
  q34 : Eqn
  q34 = wE 27 W
  q35 : Eqn
  q35 = wE 28 W
  q36 : Eqn
  q36 = wE 29 W
  q37 : Eqn
  q37 = wE 30 W
  q38 : Eqn
  q38 = wE 31 W
  q39 : Eqn
  q39 = wE 71 W
  q40 : Eqn
  q40 = wE 72 W
  q41 : Eqn
  q41 = wE 73 W
  q42 : Eqn
  q42 = wE 32 W
  q43 : Eqn
  q43 = wE 33 W

-- comm CCZ123 CCZ013: 437 steps
lem-comm-CCZ123-CCZ013 : ⟪ (CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CCZ013 = derive (CCZ123 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ123 ∷ [])
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q2 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q2 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q2 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 4 q6 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 5 q6 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 5 q5 ∷
   rw 4 q1 ∷
   rw 5 q2 ∷
   rw 4 q2 ∷
   re 5 3 (CX30 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q2 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q2 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q5 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 4 q6 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 2 q2 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 6 q7 ∷
   re 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q8 ∷
   rw 6 q9 ∷
   rw⁻ 5 q8 ∷
   re 6 3 (CX31 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q10 ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   rw 5 q11 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q8 ∷
   rw 4 q9 ∷
   rw⁻ 3 q8 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw 7 q15 ∷
   rw 6 q16 ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q17 ∷
   rw 8 q15 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q18 ∷
   rw 6 q15 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   rw 4 q16 ∷
   rw 5 q21 ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q22 ∷
   rw 7 q15 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q23 ∷
   rw 9 q15 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q17 ∷
   rw 4 q20 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q5 ∷
   rw 5 q24 ∷
   rw 8 q15 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 7 q25 ∷
   rw 10 q15 ∷
   re 8 3 (CX02 ∷ []) ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q26 ∷
   rw⁻ 11 q27 ∷
   rw 12 q28 ∷
   re 9 5 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q29 ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q30 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q8 ∷
   rw 11 q32 ∷
   rw 12 q8 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q33 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   rw 6 q17 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q34 ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 6 q35 ∷
   rw 7 q32 ∷
   rw 3 q14 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q29 ∷
   rw 6 q37 ∷
   rw 7 q31 ∷
   rw 8 q37 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 10 q34 ∷
   rw 11 q8 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q38 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 7 q30 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 9 q32 ∷
   rw 10 q8 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q33 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   rw 5 q38 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q2 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 3 q6 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q39 ∷
   rw 6 q2 ∷
   re 4 3 (CX13 ∷ []) ∷
   rw 5 q40 ∷
   rw 8 q2 ∷
   re 6 3 (CX13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 3 q41 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 4 q5 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q5 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q5 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 2 q42 ∷
   rw 1 q5 ∷
   rw 0 q43 ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   re 3 3 (CX30 ∷ []) ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q5 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 0 q2 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw 4 q7 ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q8 ∷
   rw 4 q9 ∷
   rw⁻ 3 q8 ∷
   re 4 3 (CX31 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q10 ∷
   rw 5 q11 ∷
   rw 4 q12 ∷
   rw 3 q11 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q8 ∷
   rw 2 q9 ∷
   rw⁻ 1 q8 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 5 q15 ∷
   rw 4 q16 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q17 ∷
   rw 6 q15 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q18 ∷
   rw 4 q15 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 2 q16 ∷
   rw 3 q21 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q22 ∷
   rw 5 q15 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q23 ∷
   rw 7 q15 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q17 ∷
   rw 2 q20 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q5 ∷
   rw 3 q24 ∷
   rw 6 q15 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q25 ∷
   rw 8 q15 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q26 ∷
   rw⁻ 9 q27 ∷
   rw 10 q28 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 7 q30 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 9 q32 ∷
   rw 10 q8 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q33 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q17 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 1 q34 ∷
   rw 2 q35 ∷
   rw 3 q36 ∷
   rw 4 q35 ∷
   rw 5 q32 ∷
   rw 1 q14 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q29 ∷
   rw 4 q37 ∷
   rw 5 q31 ∷
   rw 6 q37 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 8 q34 ∷
   rw 9 q8 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q38 ∷
   rw 2 q29 ∷
   rw 3 q30 ∷
   rw 4 q31 ∷
   rw 5 q30 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q32 ∷
   rw 8 q8 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q33 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   rw 3 q38 ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q2 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 4 q2 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 0 q2 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 1 q6 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 0 3 (CCZ013 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q39 ∷
   rw 4 q2 ∷
   re 2 3 (CX13 ∷ []) ∷
   rw 3 q40 ∷
   rw 6 q2 ∷
   re 4 3 (CX13 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 1 q41 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 100 W
  q45 : Eqn
  q45 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q46 : Eqn
  q46 = wE 101 W
  q47 : Eqn
  q47 = eqn (CX10 ∷ CS23 ∷ []) (CS23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CS))
  q48 : Eqn
  q48 = wE 49 W
  q49 : Eqn
  q49 = wE 102 W
  q50 : Eqn
  q50 = wE 103 W
  q51 : Eqn
  q51 = wE 104 W

-- comm CCZ013 CS12: 85 steps
lem-comm-CCZ013-CS12 : ⟪ (CCZ013 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS12 = derive (CCZ013 ∷ CS12 ∷ []) (CS12 ∷ CCZ013 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q2 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 4 q2 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q4 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q44 ∷
   rw⁻ 0 q27 ∷
   rw 3 q2 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw 5 q2 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 5 q5 ∷
   rw 4 q46 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 6 q24 ∷
   rw 5 q47 ∷
   rw 4 q48 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   re 4 5 (CX30 ∷ []) ∷
   rw 2 q49 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 4 q24 ∷
   rw 3 q47 ∷
   rw 2 q48 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   re 2 5 (CX30 ∷ []) ∷
   rw 0 q50 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q45 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q27 ∷
   rw 2 q51 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q6 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = wE 105 W

-- comm CCZ013 CCZ012: 51 steps
lem-comm-CCZ013-CCZ012 : ⟪ (CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CCZ012 = derive (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ [])
  (rw 2 q52 ∷
   rw 3 q3 ∷
   rw 4 q52 ∷
   rw 2 q21 ∷
   rw 1 q42 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q5 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 2 q6 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q2 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 4 q2 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q4 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q42 ∷
   rw 0 q5 ∷
   rw 0 q21 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 106 W
  q54 : Eqn
  q54 = wE 107 W
  q55 : Eqn
  q55 = eqn (CX10 ∷ CZ23 ∷ []) (CZ23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CZ))
  q56 : Eqn
  q56 = wE 108 W
  q57 : Eqn
  q57 = wE 109 W
  q58 : Eqn
  q58 = wE 110 W

-- comm CCZ012 CZ13: 51 steps
lem-comm-CCZ012-CZ13 : ⟪ (CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CZ13 = derive (CCZ012 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ012 ∷ [])
  (rw 0 q44 ∷
   rw 4 q53 ∷
   re 4 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q2 ∷
   re 4 3 (CX30 ∷ []) ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   re 8 3 (CZ13 ∷ []) ∷
   rw 7 q54 ∷
   rw 6 q55 ∷
   rw 5 q56 ∷
   re 5 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   re 5 5 (CX30 ∷ []) ∷
   re 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 3 3 (CZ13 ∷ []) ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 2 q45 ∷
   rw 3 q57 ∷
   rw 4 q2 ∷
   re 2 3 (CZ13 ∷ []) ∷
   rw⁻ 3 q45 ∷
   rw 4 q5 ∷
   re 2 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 1 q2 ∷
   re 2 3 (CX30 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   re 6 3 (CZ13 ∷ []) ∷
   rw 5 q54 ∷
   rw 4 q55 ∷
   rw 3 q56 ∷
   re 3 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   re 3 5 (CX30 ∷ []) ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   re 1 3 (CZ13 ∷ []) ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q27 ∷
   rw 1 q58 ∷
   rw 2 q2 ∷
   re 0 3 (CZ13 ∷ []) ∷
   rw⁻ 1 q27 ∷
   rw 2 q5 ∷
   rw 1 q51 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 85 W
  q60 : Eqn
  q60 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q61 : Eqn
  q61 = wE 78 W
  q62 : Eqn
  q62 = wE 94 W
  q63 : Eqn
  q63 = wE 95 W
  q64 : Eqn
  q64 = wE 89 W

-- comm CCZ013 CS02: 91 steps
lem-comm-CCZ013-CS02 : ⟪ (CCZ013 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CS02 = derive (CCZ013 ∷ CS02 ∷ []) (CS02 ∷ CCZ013 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q2 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 4 q2 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q4 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 1 q6 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q59 ∷
   rw⁻ 0 q27 ∷
   rw 3 q2 ∷
   re 1 3 (CX31 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw 5 q2 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q7 ∷
   rw 5 q10 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q8 ∷
   rw 5 q10 ∷
   rw⁻ 4 q8 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 5 q46 ∷
   rw 4 q34 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q8 ∷
   rw 6 q34 ∷
   rw 7 q8 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q38 ∷
   re 4 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 3 q16 ∷
   rw⁻ 4 q60 ∷
   rw 5 q61 ∷
   re 3 3 (CS02 ∷ []) ∷
   rw 2 q62 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q16 ∷
   rw⁻ 2 q60 ∷
   rw 3 q61 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 0 q63 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q45 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q27 ∷
   rw 2 q64 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q6 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl
