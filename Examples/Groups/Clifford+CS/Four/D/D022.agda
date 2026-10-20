{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D022 (W : Ws) where

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
  q1 = eqn [] (CX02 ∷ CX02 ∷ []) (wn 252 W)
  q2 : Eqn
  q2 = eqn [] (CCZ123 ∷ CCZ123 ∷ []) (wn 70 W)
  q3 : Eqn
  q3 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q4 : Eqn
  q4 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q7 : Eqn
  q7 = eqn (CX12 ∷ Sw01 ∷ []) (Sw01 ∷ CX02 ∷ []) (wn 253 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q12 : Eqn
  q12 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q13 : Eqn
  q13 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q14 : Eqn
  q14 = eqn (CX12 ∷ Sw12 ∷ []) (Sw12 ∷ CX21 ∷ []) (wn 414 W)
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q18 : Eqn
  q18 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q19 : Eqn
  q19 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q21 : Eqn
  q21 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q22 : Eqn
  q22 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q23 : Eqn
  q23 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q24 : Eqn
  q24 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q25 : Eqn
  q25 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q26 : Eqn
  q26 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q28 : Eqn
  q28 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q29 : Eqn
  q29 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q30 : Eqn
  q30 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q31 : Eqn
  q31 = eqn (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 17 W)
  q32 : Eqn
  q32 = eqn (CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz)
  q33 : Eqn
  q33 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q34 : Eqn
  q34 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q35 : Eqn
  q35 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q36 : Eqn
  q36 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q37 : Eqn
  q37 = eqn (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) (wn 71 W)
  q38 : Eqn
  q38 = eqn (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) (wn 72 W)
  q39 : Eqn
  q39 = eqn (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 73 W)
  q40 : Eqn
  q40 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q41 : Eqn
  q41 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q44 : Eqn
  q44 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q45 : Eqn
  q45 = eqn (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 11 W)
  q46 : Eqn
  q46 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)
  q47 : Eqn
  q47 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)

-- comm CCZ013 CCZ123: 741 steps
lem-comm-CCZ013-CCZ123 : ⟪ (CCZ013 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ013 ∷ []) ⟫ʷ
lem-comm-CCZ013-CCZ123 = derive (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ [])
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q1 ∷
   rw 5 q3 ∷
   rw 4 q4 ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 8 q6 ∷
   rw⁻ 7 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 5 q8 ∷
   rw 4 q7 ∷
   rw⁻ 3 q9 ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q8 ∷
   rw 8 q10 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q11 ∷
   rw 11 q5 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q12 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 2 q4 ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q9 ∷
   rw 5 q15 ∷
   rw 6 q8 ∷
   rw 7 q15 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 9 q16 ∷
   rw 10 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q17 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 11 q18 ∷
   rw 10 q19 ∷
   rw 8 q20 ∷
   re 9 5 (CS03 ∷ []) ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q21 ∷
   rw 4 q23 ∷
   rw 5 q24 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q25 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q25 ∷
   rw⁻ 9 q26 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q25 ∷
   rw 6 q27 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   rw 3 q14 ∷
   rw 7 q24 ∷
   rw 6 q24 ∷
   re 7 3 (CX31 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q24 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q24 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q24 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q25 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q25 ∷
   rw 8 q26 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q25 ∷
   rw 6 q26 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw 6 q27 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   rw 4 q24 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw 8 q13 ∷
   rw 7 q28 ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q21 ∷
   rw 9 q13 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q29 ∷
   rw 7 q13 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q30 ∷
   rw 7 q31 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   rw 5 q28 ∷
   rw 6 q32 ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q33 ∷
   rw 8 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 7 q34 ∷
   rw 10 q13 ∷
   re 8 3 (CX02 ∷ []) ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q21 ∷
   rw 5 q31 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 7 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 8 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 9 q24 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q24 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q26 ∷
   rw 13 q24 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q25 ∷
   rw 6 q35 ∷
   rw 9 q13 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 8 q36 ∷
   rw 11 q13 ∷
   re 9 3 (CX02 ∷ []) ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q18 ∷
   rw⁻ 12 q19 ∷
   rw 13 q20 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 9 q8 ∷
   rw 10 q10 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw 12 q11 ∷
   rw 13 q5 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q21 ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q24 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q26 ∷
   rw 10 q24 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q24 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q25 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw⁻ 8 q26 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q25 ∷
   rw 5 q27 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q9 ∷
   rw 7 q15 ∷
   rw 8 q8 ∷
   rw 9 q15 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 11 q16 ∷
   rw 12 q5 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q17 ∷
   rw 5 q37 ∷
   rw 8 q24 ∷
   re 6 3 (CX03 ∷ []) ∷
   rw 7 q38 ∷
   rw 10 q24 ∷
   re 8 3 (CX03 ∷ []) ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q25 ∷
   rw 5 q3 ∷
   rw 6 q9 ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q10 ∷
   rw 9 q5 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 8 q8 ∷
   re 10 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q10 ∷
   rw 11 q5 ∷
   re 9 3 (CX13 ∷ []) ∷
   rw 10 q11 ∷
   rw 6 q39 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   rw 6 q25 ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q24 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q26 ∷
   rw 10 q24 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q25 ∷
   rw 3 q35 ∷
   rw 6 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q36 ∷
   rw 8 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw⁻ 9 q19 ∷
   rw 10 q20 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q8 ∷
   rw 7 q10 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 9 q11 ∷
   rw 10 q5 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q12 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q9 ∷
   rw 6 q15 ∷
   rw 7 q8 ∷
   rw 8 q15 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q16 ∷
   rw 11 q5 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q17 ∷
   rw 4 q40 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q21 ∷
   rw 6 q41 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q21 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw⁻ 10 q19 ∷
   rw 11 q20 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q24 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q25 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw⁻ 8 q26 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q25 ∷
   rw 5 q27 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 5 q21 ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q15 ∷
   rw 5 q8 ∷
   rw 6 q15 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q16 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q17 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q10 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q12 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q24 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q26 ∷
   rw 10 q24 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q25 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q16 ∷
   rw 5 q5 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q42 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q43 ∷
   rw 7 q5 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q42 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q11 ∷
   rw 9 q5 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q24 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q25 ∷
   rw⁻ 5 q44 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q25 ∷
   rw⁻ 7 q44 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q25 ∷
   rw 4 q45 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   rw 4 q17 ∷
   rw 1 q46 ∷
   rw 2 q24 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q24 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q25 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw 4 q26 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q25 ∷
   rw 2 q26 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q25 ∷
   rw 2 q27 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 0 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q24 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q26 ∷
   rw 4 q24 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q25 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q25 ∷
   rw 3 q26 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q25 ∷
   rw 1 q26 ∷
   re 0 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q25 ∷
   rw 1 q27 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 1 q47 ∷
   rw 0 q25 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 6 q6 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 3 q8 ∷
   rw 2 q7 ∷
   rw⁻ 1 q9 ∷
   rw 2 q3 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   rw 6 q10 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q11 ∷
   rw 9 q5 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q12 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ023 ∷ []) ∷
   rw 0 q4 ∷
   rw 4 q13 ∷
   rw 3 q14 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q9 ∷
   rw 3 q15 ∷
   rw 4 q8 ∷
   rw 5 q15 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q16 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q17 ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   rw 8 q19 ∷
   rw 6 q20 ∷
   re 7 5 (CS03 ∷ []) ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q21 ∷
   rw 4 q22 ∷
   re 3 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q21 ∷
   rw 2 q23 ∷
   rw 3 q24 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q25 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q25 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q25 ∷
   rw 4 q27 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   rw 1 q14 ∷
   rw 5 q24 ∷
   rw 4 q24 ∷
   re 5 3 (CX31 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q24 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q24 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q25 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q25 ∷
   rw 6 q26 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw 4 q26 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q25 ∷
   rw 4 q27 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 2 q24 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q13 ∷
   rw 5 q28 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q21 ∷
   rw 7 q13 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q29 ∷
   rw 5 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q28 ∷
   rw 4 q32 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q33 ∷
   rw 6 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q34 ∷
   rw 8 q13 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q21 ∷
   rw 3 q31 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q24 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q24 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q24 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q25 ∷
   rw 4 q35 ∷
   rw 7 q13 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q36 ∷
   rw 9 q13 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw⁻ 10 q19 ∷
   rw 11 q20 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q8 ∷
   rw 8 q10 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw 10 q11 ∷
   rw 11 q5 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q12 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q21 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q24 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q24 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q25 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q25 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw 3 q27 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q9 ∷
   rw 5 q15 ∷
   rw 6 q8 ∷
   rw 7 q15 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 9 q16 ∷
   rw 10 q5 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q17 ∷
   rw 3 q37 ∷
   rw 6 q24 ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 q38 ∷
   rw 8 q24 ∷
   re 6 3 (CX03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q10 ∷
   rw 7 q5 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q8 ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q10 ∷
   rw 9 q5 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 8 q11 ∷
   rw 4 q39 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q25 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q24 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q25 ∷
   rw 1 q35 ∷
   rw 4 q13 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q36 ∷
   rw 6 q13 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw⁻ 7 q19 ∷
   rw 8 q20 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q10 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q12 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q15 ∷
   rw 5 q8 ∷
   rw 6 q15 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q16 ∷
   rw 9 q5 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q17 ∷
   rw 2 q40 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q41 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q21 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw⁻ 8 q19 ∷
   rw 9 q20 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 2 q24 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q25 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q25 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw 3 q27 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 3 q21 ∷
   re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q9 ∷
   rw 2 q15 ∷
   rw 3 q8 ∷
   rw 4 q15 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q16 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q17 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q8 ∷
   rw 3 q10 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q11 ∷
   rw 6 q5 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw 0 q12 ∷
   re 0 5 (CCZ123 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q24 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q25 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw 2 q16 ∷
   rw 3 q5 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q42 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q43 ∷
   rw 5 q5 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q42 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q24 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q25 ∷
   rw⁻ 3 q44 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q25 ∷
   rw⁻ 5 q44 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q25 ∷
   rw 2 q45 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw 2 q17 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (CS02 ∷ CZ01 ∷ []) (CZ01 ∷ CS02 ∷ []) (wn 415 W)

-- pass [CS02] [CZ01]: 1 steps
lem-pass-CS02-vs-CZ01 : ⟪ (CS02 ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CZ01 = derive (CS02 ∷ CZ01 ∷ []) (CZ01 ∷ CS02 ∷ [])
  (rw 0 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q50 : Eqn
  q50 = eqn (CS12 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS12 ∷ []) (wn 416 W)

-- pass [CS02] [CSd23]: 7 steps
lem-pass-CS02-vs-CSd23 : ⟪ (CS02 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CSd23 = derive (CS02 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS02 ∷ [])
  (rw 2 q3 ∷
   rw⁻ 1 q8 ∷
   rw 0 q49 ∷
   rw 1 q50 ∷
   rw 0 q8 ∷
   rw 1 q16 ∷
   rw 2 q17 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (CS02⁻ ∷ CZ01 ∷ []) (CZ01 ∷ CS02⁻ ∷ []) (wn 417 W)

-- pass [CSd02] [CZ01]: 1 steps
lem-pass-CSd02-vs-CZ01 : ⟪ (CS02⁻ ∷ CZ01 ∷ []) ⟫ʷ ≈ ⟪ (CZ01 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CZ01 = derive (CS02⁻ ∷ CZ01 ∷ []) (CZ01 ∷ CS02⁻ ∷ [])
  (rw 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q53 : Eqn
  q53 = eqn (CS12⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS12⁻ ∷ []) (wn 418 W)

-- pass [CSd02] [CSd23]: 7 steps
lem-pass-CSd02-vs-CSd23 : ⟪ (CS02⁻ ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CSd23 = derive (CS02⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS02⁻ ∷ [])
  (rw 2 q3 ∷
   rw⁻ 1 q8 ∷
   rw 0 q52 ∷
   rw 1 q53 ∷
   rw 0 q8 ∷
   rw 1 q43 ∷
   rw 2 q17 ∷ []) Eq.refl
