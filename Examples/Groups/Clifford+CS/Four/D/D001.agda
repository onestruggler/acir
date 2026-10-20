{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D001 (W : Ws) where

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
  q1 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q2 : Eqn
  q2 = eqn [] (CX20 ∷ CX20 ∷ []) (wn 2 W)
  q3 : Eqn
  q3 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q4 : Eqn
  q4 = eqn [] (CCZ012 ∷ CCZ012 ∷ []) (wn 4 W)
  q5 : Eqn
  q5 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q8 : Eqn
  q8 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q9 : Eqn
  q9 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q10 : Eqn
  q10 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q11 : Eqn
  q11 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q12 : Eqn
  q12 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q13 : Eqn
  q13 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q14 : Eqn
  q14 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q16 : Eqn
  q16 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q17 : Eqn
  q17 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q18 : Eqn
  q18 = eqn (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 17 W)
  q19 : Eqn
  q19 = eqn (CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz)
  q20 : Eqn
  q20 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q21 : Eqn
  q21 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q22 : Eqn
  q22 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q23 : Eqn
  q23 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q24 : Eqn
  q24 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q25 : Eqn
  q25 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q26 : Eqn
  q26 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q27 : Eqn
  q27 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q32 : Eqn
  q32 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q38 : Eqn
  q38 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q39 : Eqn
  q39 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)

-- CCZ312-CCZ012: 243 steps
lem-CCZ312-CCZ012 : ⟪ (CCZ123 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ312-CCZ012 = derive (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ [])
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q1 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 4 q1 ∷
   rw 5 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CX30 ∷ []) ∷
   rw 6 q3 ∷
   rw 5 q5 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q6 ∷
   rw 5 q7 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (CX31 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw 5 q10 ∷
   rw 4 q9 ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 3 q7 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q15 ∷
   rw 7 q13 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q17 ∷
   rw 5 q18 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q14 ∷
   rw 4 q19 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q20 ∷
   rw 6 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q21 ∷
   rw 8 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q15 ∷
   rw 3 q18 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q3 ∷
   rw 4 q23 ∷
   rw 7 q13 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q24 ∷
   rw 9 q13 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q25 ∷
   rw⁻ 10 q26 ∷
   rw 11 q27 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q28 ∷
   rw 6 q29 ∷
   rw 7 q30 ∷
   rw 8 q29 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 10 q31 ∷
   rw 11 q6 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q32 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q15 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q33 ∷
   rw 3 q34 ∷
   rw 4 q35 ∷
   rw 5 q34 ∷
   rw 6 q31 ∷
   rw 2 q12 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q28 ∷
   rw 5 q36 ∷
   rw 6 q30 ∷
   rw 7 q36 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 9 q33 ∷
   rw 10 q6 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q37 ∷
   rw 3 q28 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q29 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q31 ∷
   rw 9 q6 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q32 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 4 q37 ∷
   rw 1 q38 ∷
   rw 0 q39 ∷
   rw 3 q5 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q6 ∷
   rw 3 q7 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (CX31 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q8 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   rw 2 q9 ∷
   rw 1 q11 ∷
   rw 2 q12 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 0 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 2 q6 ∷
   rw 1 q7 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (CX31 ∷ []) ∷
   rw 4 q13 ∷
   rw 3 q14 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q15 ∷
   rw 5 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 2 q17 ∷
   rw 3 q18 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q14 ∷
   rw 2 q19 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 1 q20 ∷
   rw 4 q13 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q21 ∷
   rw 6 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q15 ∷
   rw 1 q18 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q3 ∷
   rw 2 q23 ∷
   rw 5 q13 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q24 ∷
   rw 7 q13 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q25 ∷
   rw⁻ 8 q26 ∷
   rw 9 q27 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q28 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q29 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 8 q31 ∷
   rw 9 q6 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q32 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ023 ∷ []) ∷
   rw 3 q15 ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   rw 2 q35 ∷
   rw 3 q34 ∷
   rw 4 q31 ∷
   rw 0 q12 ∷
   re 0 5 (CCZ012 ∷ []) ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q28 ∷
   rw 3 q36 ∷
   rw 4 q30 ∷
   rw 5 q36 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q33 ∷
   rw 8 q6 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q37 ∷
   rw 1 q28 ∷
   rw 2 q29 ∷
   rw 3 q30 ∷
   rw 4 q29 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q31 ∷
   rw 7 q6 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q32 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 2 q37 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (CCZ123 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 34 W)
  q41 : Eqn
  q41 = eqn (CS12 ∷ CX20 ∷ []) (CX20 ∷ CS12 ∷ []) (wn 35 W)
  q42 : Eqn
  q42 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wn 36 W)
  q43 : Eqn
  q43 = eqn (CX10 ∷ CX23 ∷ []) (CX23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (CX₀₁))
  q44 : Eqn
  q44 = eqn (CX23 ∷ Sw12 ∷ []) (Sw12 ∷ CX13 ∷ []) (wn 37 W)
  q45 : Eqn
  q45 = eqn (CS23⁻ ∷ CX31 ∷ []) (CX31 ∷ CS23⁻ ∷ []) (wn 38 W)
  q46 : Eqn
  q46 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q47 : Eqn
  q47 = eqn (CS23 ∷ CX31 ∷ []) (CX31 ∷ CS23 ∷ []) (wn 40 W)
  q48 : Eqn
  q48 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CCZ123 ∷ []) (wn 41 W)

-- CCZ123-CX30: 61 steps
lem-CCZ123-CX30 : ⟪ (CCZ123 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (CX30 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ123-CX30 = derive (CCZ123 ∷ CX30 ∷ []) (CX30 ∷ CCZ123 ∷ [])
  (rw 0 q40 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 5 q41 ∷
   rw 6 q1 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q3 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q1 ∷
   re 4 3 (CX13 ∷ []) ∷
   rw 4 q42 ∷
   rw⁻ 5 q43 ∷
   rw 6 q44 ∷
   re 7 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   re 3 5 (CX30 ∷ []) ∷
   rw 4 q5 ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q6 ∷
   rw 4 q7 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw⁻ 2 q30 ∷
   rw 3 q45 ∷
   re 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 3 q46 ∷
   rw 4 q6 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q30 ∷
   rw 4 q37 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q1 ∷
   re 2 3 (CX13 ∷ []) ∷
   rw 2 q42 ∷
   rw⁻ 3 q43 ∷
   rw 4 q44 ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 1 5 (CX30 ∷ []) ∷
   rw 2 q5 ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q6 ∷
   rw 2 q7 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw⁻ 0 q28 ∷
   rw 1 q47 ∷
   re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 0 q6 ∷
   rw 1 q46 ∷
   rw 2 q6 ∷
   re 0 3 (CX30 ∷ []) ∷
   rw 1 q28 ∷
   rw 2 q37 ∷
   rw 1 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn [] (CX23 ∷ CX23 ∷ []) (wn 42 W)
  q50 : Eqn
  q50 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q51 : Eqn
  q51 = eqn (CX23 ∷ Sw23 ∷ []) (Sw23 ∷ CX32 ∷ []) (wn 44 W)

-- comm CCZ012 CCZ013: 229 steps
lem-comm-CCZ012-CCZ013 : ⟪ (CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CCZ013 = derive (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ [])
  (rw 2 q49 ∷
   rw 3 q1 ∷
   rw 4 q4 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q1 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw⁻ 7 q22 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 4 q50 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q1 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 5 q50 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 5 q3 ∷
   rw 4 q49 ∷
   rw 5 q1 ∷
   rw 4 q51 ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   rw 6 q22 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 4 q22 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 4 q50 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 2 q51 ∷
   rw 3 q19 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q1 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 3 q50 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 3 q50 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 4 q3 ∷
   rw 3 q1 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 5 q22 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 3 q22 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 3 q50 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q22 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 4 q22 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 2 q22 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw 2 q50 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 2 q38 ∷
   rw 1 q3 ∷
   rw 0 q38 ∷
   rw 3 q1 ∷
   rw 2 q51 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q22 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 4 q22 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 2 q22 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw 2 q50 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 0 q51 ∷
   rw 1 q19 ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q1 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q22 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 0 q1 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q3 ∷
   rw⁻ 2 q22 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 1 q50 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 0 3 (CCZ013 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q3 ∷
   rw⁻ 2 q22 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw 1 q50 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 2 q3 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q53 : Eqn
  q53 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)

-- CCZ013-T: 2 steps
lem-CCZ013-T : ⟪ (CCZ013 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ013-T = derive (CCZ013 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ [])
  (rw 0 q52 ∷
   rw 1 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q55 : Eqn
  q55 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q56 : Eqn
  q56 = eqn (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 46 W)
  q57 : Eqn
  q57 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q58 : Eqn
  q58 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q59 : Eqn
  q59 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q60 : Eqn
  q60 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q61 : Eqn
  q61 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q62 : Eqn
  q62 = eqn (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 52 W)

-- CCZ023-T: 110 steps
lem-CCZ023-T : ⟪ (CCZ023 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ023-T = derive (CCZ023 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ023 ∷ CCZ123 ∷ [])
  (rw 0 q52 ∷
   rw 4 q13 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 10 q54 ∷
   rw 9 q55 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q15 ∷
   rw 7 q13 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q55 ∷
   rw 4 q56 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q28 ∷
   rw 3 q36 ∷
   rw 4 q30 ∷
   rw 5 q36 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q33 ∷
   rw 8 q6 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q37 ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q25 ∷
   rw 8 q26 ∷
   rw 6 q27 ∷
   re 7 5 (CS03 ∷ []) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q15 ∷
   rw 4 q57 ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q15 ∷
   rw 2 q58 ∷
   rw 3 q1 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw⁻ 7 q22 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 4 q50 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 8 q54 ∷
   rw 7 q55 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q15 ∷
   rw 5 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q55 ∷
   rw 2 q56 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 2 q53 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   rw 1 q23 ∷
   rw 4 q13 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q24 ∷
   rw 6 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q25 ∷
   rw⁻ 7 q26 ∷
   rw 8 q27 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 1 q5 ∷
   rw 2 q28 ∷
   rw 3 q29 ∷
   rw 4 q30 ∷
   rw 5 q29 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q31 ∷
   rw 8 q6 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q32 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q59 ∷
   rw 3 q60 ∷
   rw 4 q61 ∷
   rw 5 q60 ∷
   rw 6 q23 ∷
   rw 2 q62 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   rw 3 q15 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (wn 53 W)
  q64 : Eqn
  q64 = eqn (K0 ∷ CX32 ∷ []) (CX32 ∷ K0 ∷ []) (low₁-comm (K) ((CX₁₀ ↑)))
  q65 : Eqn
  q65 = eqn (K0⁻ ∷ CX32 ∷ []) (CX32 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((CX₁₀ ↑)))
  q66 : Eqn
  q66 = eqn [] (K0⁻ ∷ K0 ∷ []) (wn 54 W)
  q67 : Eqn
  q67 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wn 55 W)
  q68 : Eqn
  q68 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q69 : Eqn
  q69 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q70 : Eqn
  q70 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q71 : Eqn
  q71 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)

-- N32-T: 59 steps
lem-N32-T : ⟪ (CX32 ∷ Toff012 ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff013 ∷ []) ⟫ʷ
lem-N32-T = derive (CX32 ∷ Toff012 ∷ CX32 ∷ []) (Toff012 ∷ Toff013 ∷ [])
  (rw 1 q63 ∷
   rw⁻ 0 q64 ∷
   rw 3 q65 ∷
   rw 1 q19 ∷
   rw 2 q66 ∷
   rw 0 q67 ∷
   rw 4 q1 ∷
   rw 3 q68 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 5 q22 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 3 q22 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 3 q50 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q69 ∷
   rw 2 q67 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q69 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q69 ∷
   rw⁻ 8 q70 ∷
   rw 1 q1 ∷
   rw⁻ 2 q69 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q3 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw⁻ 8 q69 ∷
   rw⁻ 9 q70 ∷
   rw 2 q71 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q3 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (Toff012 ∷ []) (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) (wn 57 W)
  q73 : Eqn
  q73 = eqn (K0 ∷ CX23 ∷ []) (CX23 ∷ K0 ∷ []) (low₁-comm (K) ((CX₀₁ ↑)))
  q74 : Eqn
  q74 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q75 : Eqn
  q75 = eqn (CX23 ∷ CX21 ∷ []) (CX21 ∷ CX23 ∷ []) (wn 58 W)
  q76 : Eqn
  q76 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q77 : Eqn
  q77 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q78 : Eqn
  q78 = eqn (CX23 ∷ CS12 ∷ []) (CS12 ∷ CX23 ∷ []) (wn 59 W)
  q79 : Eqn
  q79 = eqn (K0⁻ ∷ CX23 ∷ []) (CX23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((CX₀₁ ↑)))
  q80 : Eqn
  q80 = eqn (CX23 ∷ CX23 ∷ []) [] (wn 60 W)
  q81 : Eqn
  q81 = eqn (K0 ∷ CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wn 61 W)

-- N23-T: 16 steps
lem-N23-T : ⟪ (CX23 ∷ Toff012 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ []) ⟫ʷ
lem-N23-T = derive (CX23 ∷ Toff012 ∷ CX23 ∷ []) (Toff012 ∷ [])
  (rw 1 q72 ∷
   rw⁻ 0 q73 ∷
   rw⁻ 1 q74 ∷
   rw 2 q75 ∷
   rw⁻ 3 q76 ∷
   rw 4 q75 ∷
   rw 7 q5 ∷
   rw 6 q8 ∷
   rw⁻ 5 q77 ∷
   rw 6 q78 ∷
   rw 5 q33 ∷
   rw 6 q77 ∷
   rw 7 q37 ∷
   rw⁻ 6 q79 ∷
   rw 7 q80 ∷
   rw 0 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = eqn (Sw23 ∷ CX21 ∷ []) (CX31 ∷ Sw23 ∷ []) (wn 62 W)
  q83 : Eqn
  q83 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q84 : Eqn
  q84 = eqn (Sw23 ∷ CS12 ∷ []) (CS13 ∷ Sw23 ∷ []) (wn 63 W)

-- SW-T-SW: 59 steps
lem-SW-T-SW : ⟪ (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ []) ⟫ʷ
lem-SW-T-SW = derive (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) (Toff013 ∷ [])
  (rw 1 q72 ∷
   rw⁻ 0 q69 ∷
   rw⁻ 1 q26 ∷
   rw 2 q82 ∷
   rw⁻ 3 q83 ∷
   rw 4 q82 ∷
   rw 7 q5 ∷
   rw 6 q8 ∷
   rw⁻ 5 q6 ∷
   rw 6 q84 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 6 q33 ∷
   rw 7 q6 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q6 ∷
   rw 7 q37 ∷
   rw⁻ 6 q68 ∷
   rw 7 q3 ∷
   rw 7 q1 ∷
   rw 6 q68 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw 3 q83 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw 1 q26 ∷
   rw 0 q69 ∷
   rw 1 q81 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q69 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q22 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q69 ∷
   rw⁻ 7 q70 ∷
   rw 0 q1 ∷
   rw⁻ 1 q69 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q3 ∷
   rw⁻ 3 q22 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q3 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q3 ∷
   rw⁻ 7 q69 ∷
   rw⁻ 8 q70 ∷
   rw 1 q71 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q3 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = eqn (Toff012 ∷ []) (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) (wn 64 W)
  q86 : Eqn
  q86 = eqn (K0 ∷ CS13 ∷ []) (CS13 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑ • CS • Swap ↑)))
  q87 : Eqn
  q87 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q88 : Eqn
  q88 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q89 : Eqn
  q89 = eqn (CS13 ∷ CX12 ∷ []) (CX12 ∷ CS13 ∷ []) (wn 66 W)
  q90 : Eqn
  q90 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q91 : Eqn
  q91 = eqn (CS12 ∷ CS01 ∷ []) (CS01 ∷ CS12 ∷ []) (wn 67 W)
  q92 : Eqn
  q92 = eqn (K0⁻ ∷ CS13 ∷ []) (CS13 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑ • CS • Swap ↑)))
  q93 : Eqn
  q93 = eqn (K0 ∷ CS02 ∷ CX12 ∷ CS02⁻ ∷ CX12 ∷ CS01 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wn 68 W)

-- CS13 passes T: 25 steps
lem-CS13-passes-T : ⟪ (CS13 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS13 ∷ []) ⟫ʷ
lem-CS13-passes-T = derive (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ [])
  (rw 1 q85 ∷
   rw⁻ 0 q86 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q87 ∷
   rw⁻ 2 q88 ∷
   rw 3 q58 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw 2 q89 ∷
   re 4 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 3 q87 ∷
   rw⁻ 4 q90 ∷
   rw 5 q58 ∷
   re 3 3 (CS02⁻ ∷ []) ∷
   rw 4 q89 ∷
   rw 7 q1 ∷
   rw 6 q26 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q3 ∷
   rw 6 q91 ∷
   rw⁻ 5 q26 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q3 ∷
   rw⁻ 6 q92 ∷
   rw 0 q93 ∷ []) Eq.refl
