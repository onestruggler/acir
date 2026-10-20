{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D002 (W : Ws) where

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
  q1 = eqn [] (CX10 ∷ CX10 ∷ []) (wn 69 W)
  q2 : Eqn
  q2 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q3 : Eqn
  q3 = eqn [] (CCZ123 ∷ CCZ123 ∷ []) (wn 70 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q11 : Eqn
  q11 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q13 : Eqn
  q13 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q14 : Eqn
  q14 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q15 : Eqn
  q15 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q16 : Eqn
  q16 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q17 : Eqn
  q17 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q18 : Eqn
  q18 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q19 : Eqn
  q19 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q20 : Eqn
  q20 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q21 : Eqn
  q21 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q22 : Eqn
  q22 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q23 : Eqn
  q23 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q24 : Eqn
  q24 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q25 : Eqn
  q25 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q26 : Eqn
  q26 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q27 : Eqn
  q27 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q28 : Eqn
  q28 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q29 : Eqn
  q29 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q30 : Eqn
  q30 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q31 : Eqn
  q31 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q32 : Eqn
  q32 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q33 : Eqn
  q33 = eqn (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 17 W)
  q34 : Eqn
  q34 = eqn (CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz)
  q35 : Eqn
  q35 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q36 : Eqn
  q36 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q37 : Eqn
  q37 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q38 : Eqn
  q38 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q41 : Eqn
  q41 = eqn (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) (wn 71 W)
  q42 : Eqn
  q42 = eqn (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) (wn 72 W)
  q43 : Eqn
  q43 = eqn (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 73 W)
  q44 : Eqn
  q44 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q45 : Eqn
  q45 = eqn (Sw12 ∷ CX12 ∷ []) (CX21 ∷ Sw12 ∷ []) (wn 50 W)
  q46 : Eqn
  q46 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q47 : Eqn
  q47 = eqn (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 52 W)
  q48 : Eqn
  q48 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q49 : Eqn
  q49 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)

-- comm CCZ123 CCZ023: 613 steps
lem-comm-CCZ123-CCZ023 : ⟪ (CCZ123 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CCZ023 = derive (CCZ123 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ123 ∷ [])
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q2 ∷
   rw 4 q4 ∷
   rw 5 q9 ∷
   rw 6 q6 ∷
   rw 7 q9 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q10 ∷
   rw 10 q7 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q11 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 10 q7 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q4 ∷
   rw 6 q9 ∷
   rw 7 q6 ∷
   rw 8 q9 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q10 ∷
   rw 11 q7 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q11 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q12 ∷
   rw 4 q1 ∷
   rw 5 q13 ∷
   rw 4 q13 ∷
   re 5 3 (CX20 ∷ []) ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 9 q7 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q12 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q14 ∷
   rw 9 q15 ∷
   rw 7 q16 ∷
   re 8 5 (CS03 ∷ []) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q17 ∷
   rw 5 q18 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q17 ∷
   rw 3 q19 ∷
   rw 4 q20 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 5 q23 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 2 q13 ∷
   re 3 3 (CX20 ∷ []) ∷
   rw 6 q20 ∷
   rw 5 q20 ∷
   re 6 3 (CX30 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q20 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q20 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q21 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 5 q22 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 5 q23 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q20 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 7 q2 ∷
   re 6 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 7 q24 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (CX31 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q25 ∷
   rw 8 q26 ∷
   rw 7 q27 ∷
   rw 6 q26 ∷
   rw 5 q28 ∷
   rw 6 q29 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q24 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw 8 q13 ∷
   rw 7 q30 ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q17 ∷
   rw 9 q13 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q31 ∷
   rw 7 q13 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q32 ∷
   rw 7 q33 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   rw 5 q30 ∷
   rw 6 q34 ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q35 ∷
   rw 8 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 7 q36 ∷
   rw 10 q13 ∷
   re 8 3 (CX02 ∷ []) ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q17 ∷
   rw 5 q33 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q20 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q22 ∷
   rw 13 q20 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q21 ∷
   rw 6 q37 ∷
   rw 9 q13 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 8 q38 ∷
   rw 11 q13 ∷
   re 9 3 (CX02 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q14 ∷
   rw⁻ 12 q15 ∷
   rw 13 q16 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q4 ∷
   rw 8 q9 ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q10 ∷
   rw 13 q7 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q11 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q17 ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q8 ∷
   rw 5 q39 ∷
   rw 6 q40 ∷
   rw 7 q39 ∷
   rw 8 q10 ∷
   rw 4 q29 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q6 ∷
   rw 9 q5 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q8 ∷
   rw 12 q7 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q12 ∷
   rw 5 q4 ∷
   rw 6 q9 ∷
   rw 7 q6 ∷
   rw 8 q9 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q10 ∷
   rw 11 q7 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q11 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 6 q12 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q20 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q20 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw⁻ 7 q22 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 4 q23 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q41 ∷
   rw 7 q20 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q42 ∷
   rw 9 q20 ∷
   re 7 3 (CX13 ∷ []) ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 4 q43 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   rw 5 q21 ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q20 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q21 ∷
   rw 2 q37 ∷
   rw 5 q13 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q38 ∷
   rw 7 q13 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   rw⁻ 8 q15 ∷
   rw 9 q16 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q4 ∷
   rw 4 q9 ∷
   rw 5 q6 ∷
   rw 6 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q10 ∷
   rw 9 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q11 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ023 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q44 ∷
   rw 4 q45 ∷
   rw 5 q46 ∷
   rw 6 q45 ∷
   rw 7 q37 ∷
   rw 3 q47 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q2 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q12 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q7 ∷
   rw 7 q25 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q48 ∷
   rw⁻ 4 q6 ∷
   rw 3 q48 ∷
   rw⁻ 2 q4 ∷
   rw 3 q11 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q5 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 7 q7 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q12 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q25 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q48 ∷
   rw⁻ 3 q6 ∷
   rw 2 q48 ∷
   rw⁻ 1 q4 ∷
   rw 2 q11 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   rw 2 q49 ∷
   rw 1 q12 ∷
   rw 0 q49 ∷
   rw 3 q13 ∷
   rw 2 q13 ∷
   re 3 3 (CX20 ∷ []) ∷
   re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q5 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 7 q7 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q12 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   rw 7 q15 ∷
   rw 5 q16 ∷
   re 6 5 (CS03 ∷ []) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q17 ∷
   rw 3 q18 ∷
   re 2 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q17 ∷
   rw 1 q19 ∷
   rw 2 q20 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 3 q23 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 0 q13 ∷
   re 1 3 (CX20 ∷ []) ∷
   rw 4 q20 ∷
   rw 3 q20 ∷
   re 4 3 (CX30 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q20 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q22 ∷
   rw 6 q20 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q22 ∷
   rw 8 q20 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q21 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 5 q22 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 3 q22 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw 3 q23 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q20 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q7 ∷
   rw 5 q24 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (CX31 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q25 ∷
   rw 6 q26 ∷
   rw 5 q27 ∷
   rw 4 q26 ∷
   rw 3 q28 ∷
   rw 4 q29 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q7 ∷
   rw 3 q24 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q13 ∷
   rw 5 q30 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q17 ∷
   rw 7 q13 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q31 ∷
   rw 5 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q32 ∷
   rw 5 q33 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q30 ∷
   rw 4 q34 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q35 ∷
   rw 6 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q36 ∷
   rw 8 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q17 ∷
   rw 3 q33 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q20 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q21 ∷
   rw 4 q37 ∷
   rw 7 q13 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q38 ∷
   rw 9 q13 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   rw⁻ 10 q15 ∷
   rw 11 q16 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q4 ∷
   rw 6 q9 ∷
   rw 7 q6 ∷
   rw 8 q9 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw 10 q10 ∷
   rw 11 q7 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q11 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q17 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q8 ∷
   rw 3 q39 ∷
   rw 4 q40 ∷
   rw 5 q39 ∷
   rw 6 q10 ∷
   rw 2 q29 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw 9 q8 ∷
   rw 10 q7 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q12 ∷
   rw 3 q4 ∷
   rw 4 q9 ∷
   rw 5 q6 ∷
   rw 6 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q10 ∷
   rw 9 q7 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q11 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 4 q12 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q20 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q22 ∷
   rw 5 q20 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q20 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q21 ∷
   rw⁻ 3 q22 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 2 q23 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q41 ∷
   rw 5 q20 ∷
   re 3 3 (CX13 ∷ []) ∷
   rw 4 q42 ∷
   rw 7 q20 ∷
   re 5 3 (CX13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   rw 2 q43 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   rw 3 q21 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q20 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q22 ∷
   rw 5 q20 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q21 ∷
   rw 0 q37 ∷
   rw 3 q13 ∷
   re 1 3 (CX02 ∷ []) ∷
   rw 2 q38 ∷
   rw 5 q13 ∷
   re 3 3 (CX02 ∷ []) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   rw⁻ 6 q15 ∷
   rw 7 q16 ∷
   re 4 5 (CS03 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q4 ∷
   rw 2 q9 ∷
   rw 3 q6 ∷
   rw 4 q9 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q7 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q11 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ023 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q44 ∷
   rw 2 q45 ∷
   rw 3 q46 ∷
   rw 4 q45 ∷
   rw 5 q37 ∷
   rw 1 q47 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 2 q17 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wn 75 W)
  q51 : Eqn
  q51 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q52 : Eqn
  q52 = eqn (CS23 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CS23 ∷ []) (wn 77 W)
  q53 : Eqn
  q53 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q54 : Eqn
  q54 = eqn (CX32 ∷ Sw12 ∷ []) (Sw12 ∷ CX31 ∷ []) (wn 78 W)
  q55 : Eqn
  q55 = eqn (CS12⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS12⁻ ∷ []) (wn 79 W)
  q56 : Eqn
  q56 = eqn (CS12 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS12 ∷ []) (wn 80 W)
  q57 : Eqn
  q57 = eqn (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) (wn 81 W)

-- comm CCZ123 CSd02: 21 steps
lem-comm-CCZ123-CSd02 : ⟪ (CCZ123 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CSd02 = derive (CCZ123 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ123 ∷ [])
  (rw 0 q50 ∷
   rw 6 q2 ∷
   rw 5 q51 ∷
   rw⁻ 4 q4 ∷
   rw 5 q52 ∷
   rw 4 q40 ∷
   rw 5 q4 ∷
   rw 6 q12 ∷
   re 4 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 3 q30 ∷
   rw⁻ 4 q53 ∷
   rw 5 q54 ∷
   re 3 3 (CS02⁻ ∷ []) ∷
   rw 2 q55 ∷
   re 2 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 1 q30 ∷
   rw⁻ 2 q53 ∷
   rw 3 q54 ∷
   re 1 3 (CS02⁻ ∷ []) ∷
   rw 0 q56 ∷
   rw 1 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (CS23 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS23 ∷ []) (wn 82 W)
  q59 : Eqn
  q59 = eqn (CX21 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CX21 ∷ []) (wn 83 W)
  q60 : Eqn
  q60 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wn 84 W)
  q61 : Eqn
  q61 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q62 : Eqn
  q62 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q63 : Eqn
  q63 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))

-- comm CCZ123 CSd03: 57 steps
lem-comm-CCZ123-CSd03 : ⟪ (CCZ123 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ123 ∷ []) ⟫ʷ
lem-comm-CCZ123-CSd03 = derive (CCZ123 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ123 ∷ [])
  (rw 0 q50 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q51 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 5 q58 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q40 ∷
   rw 6 q7 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw 5 q4 ∷
   rw 6 q12 ∷
   rw 5 q20 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   re 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 4 q59 ∷
   rw 5 q20 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q20 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw 5 q21 ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 2 q20 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw 3 q60 ∷
   rw⁻ 4 q61 ∷
   rw 5 q18 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   re 2 5 (CS03⁻ ∷ []) ∷
   rw 3 q20 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q21 ∷
   re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw 2 q59 ∷
   rw 3 q20 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 4 q20 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 3 q21 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q20 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q62 ∷
   rw⁻ 2 q63 ∷
   rw 3 q19 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q21 ∷
   re 0 5 (CS03⁻ ∷ []) ∷
   rw 1 q57 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (CCZ012 ∷ []) (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (wn 85 W)
  q65 : Eqn
  q65 = eqn (CS12 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS12 ∷ []) (wn 86 W)
  q66 : Eqn
  q66 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q67 : Eqn
  q67 = eqn (CS01⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS01⁻ ∷ []) (wn 87 W)
  q68 : Eqn
  q68 = eqn (CS01 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS01 ∷ []) (wn 88 W)
  q69 : Eqn
  q69 = eqn (CS01 ∷ CX21 ∷ CS01⁻ ∷ CX21 ∷ CS02 ∷ []) (CCZ012 ∷ []) (wn 89 W)

-- comm CCZ012 CSd03: 53 steps
lem-comm-CCZ012-CSd03 : ⟪ (CCZ012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CSd03 = derive (CCZ012 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CCZ012 ∷ [])
  (rw 0 q64 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q7 ∷
   rw 6 q51 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw 4 q25 ∷
   rw 5 q65 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw 5 q40 ∷
   rw 6 q7 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw 5 q8 ∷
   rw 6 q12 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 3 q20 ∷
   re 4 3 (CX31 ∷ []) ∷
   rw 4 q30 ∷
   rw⁻ 5 q53 ∷
   rw 6 q54 ∷
   re 7 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   re 3 5 (CS03⁻ ∷ []) ∷
   rw 4 q20 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 2 q66 ∷
   rw 3 q67 ∷
   rw 4 q20 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw⁻ 3 q66 ∷
   rw 4 q21 ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 1 q20 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 2 q30 ∷
   rw⁻ 3 q53 ∷
   rw 4 q54 ∷
   re 5 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   re 1 5 (CS03⁻ ∷ []) ∷
   rw 2 q20 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw 0 q15 ∷
   rw 1 q68 ∷
   rw 2 q20 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 q15 ∷
   rw 2 q21 ∷
   rw 1 q69 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (CS01 ∷ CX23 ∷ []) (CX23 ∷ CS01 ∷ []) (low-comm (CS) (CX₀₁))
  q71 : Eqn
  q71 = eqn (CX23 ∷ CX21 ∷ []) (CX21 ∷ CX23 ∷ []) (wn 58 W)
  q72 : Eqn
  q72 = eqn (CS01⁻ ∷ CX23 ∷ []) (CX23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₀₁))
  q73 : Eqn
  q73 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q74 : Eqn
  q74 = eqn (CX23 ∷ CS12 ∷ []) (CS12 ∷ CX23 ∷ []) (wn 59 W)
  q75 : Eqn
  q75 = eqn (CX23 ∷ CX23 ∷ []) [] (wn 60 W)

-- N23-D: 14 steps
lem-N23-D : ⟪ (CX23 ∷ CCZ012 ∷ CX23 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ []) ⟫ʷ
lem-N23-D = derive (CX23 ∷ CCZ012 ∷ CX23 ∷ []) (CCZ012 ∷ [])
  (rw 1 q64 ∷
   rw⁻ 0 q70 ∷
   rw 1 q71 ∷
   rw⁻ 2 q72 ∷
   rw 3 q71 ∷
   rw 6 q2 ∷
   rw 5 q25 ∷
   rw⁻ 4 q73 ∷
   rw 5 q74 ∷
   rw 4 q8 ∷
   rw 5 q73 ∷
   rw 6 q12 ∷
   rw 5 q75 ∷
   rw 0 q69 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (wn 90 W)

-- CS12 passes T: 1 steps
lem-CS12-passes-T : ⟪ (CS12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12 ∷ []) ⟫ʷ
lem-CS12-passes-T = derive (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ [])
  (rw 0 q76 ∷ []) Eq.refl
