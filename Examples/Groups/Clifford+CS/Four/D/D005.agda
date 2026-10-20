{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D005 (W : Ws) where

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
  q1 = eqn [] (CX31 ∷ CX31 ∷ []) (wn 111 W)
  q2 : Eqn
  q2 = eqn [] (CCZ012 ∷ CCZ012 ∷ []) (wn 4 W)
  q3 : Eqn
  q3 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q4 : Eqn
  q4 = eqn (CX31 ∷ Sw12 ∷ []) (Sw12 ∷ CX32 ∷ []) (wn 13 W)
  q5 : Eqn
  q5 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q6 : Eqn
  q6 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q7 : Eqn
  q7 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q8 : Eqn
  q8 = eqn (CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 17 W)
  q9 : Eqn
  q9 = eqn (CX32 ∷ CCZ012 ∷ CX32 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (ax cx-ccz)
  q10 : Eqn
  q10 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q11 : Eqn
  q11 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q12 : Eqn
  q12 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q13 : Eqn
  q13 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q14 : Eqn
  q14 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q16 : Eqn
  q16 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q17 : Eqn
  q17 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q18 : Eqn
  q18 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q19 : Eqn
  q19 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q20 : Eqn
  q20 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q22 : Eqn
  q22 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q23 : Eqn
  q23 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q24 : Eqn
  q24 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q26 : Eqn
  q26 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q27 : Eqn
  q27 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q28 : Eqn
  q28 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q31 : Eqn
  q31 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q32 : Eqn
  q32 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q33 : Eqn
  q33 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)

-- comm CCZ023 CCZ012: 177 steps
lem-comm-CCZ023-CCZ012 : ⟪ (CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CCZ012 = derive (CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ023 ∷ [])
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q1 ∷
   rw 5 q3 ∷
   rw 4 q4 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q6 ∷
   rw 4 q3 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 3 q7 ∷
   rw 4 q8 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 2 q4 ∷
   rw 3 q9 ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q10 ∷
   rw 5 q3 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q11 ∷
   rw 7 q3 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 6 q5 ∷
   rw 2 q8 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q12 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q13 ∷
   rw 8 q12 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q13 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q14 ∷
   rw 3 q15 ∷
   rw 6 q3 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q16 ∷
   rw 8 q3 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw⁻ 9 q18 ∷
   rw 10 q19 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   rw 6 q23 ∷
   rw 7 q22 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q24 ∷
   rw 9 q25 ∷
   rw 10 q24 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q26 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q27 ∷
   rw 2 q20 ∷
   re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q21 ∷
   rw 2 q28 ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q24 ∷
   rw 6 q29 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q30 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 6 q31 ∷
   rw⁻ 5 q24 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q32 ∷
   rw⁻ 3 q23 ∷
   rw 2 q32 ∷
   rw⁻ 1 q21 ∷
   rw 2 q26 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q21 ∷
   rw 1 q28 ∷
   rw 2 q23 ∷
   rw 3 q28 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q24 ∷
   rw 5 q29 ∷
   rw 6 q24 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q30 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 5 q31 ∷
   rw⁻ 4 q24 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q32 ∷
   rw⁻ 2 q23 ∷
   rw 1 q32 ∷
   rw⁻ 0 q21 ∷
   rw 1 q26 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q33 ∷
   rw 0 q30 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q3 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q8 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 0 q4 ∷
   rw 1 q9 ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 0 q10 ∷
   rw 3 q3 ∷
   re 1 3 (CX02 ∷ []) ∷
   rw 2 q11 ∷
   rw 5 q3 ∷
   re 3 3 (CX02 ∷ []) ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 4 q5 ∷
   rw 0 q8 ∷
   re 0 5 (CCZ012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q12 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q13 ∷
   rw 6 q12 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q13 ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q14 ∷
   rw 1 q15 ∷
   rw 4 q3 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q16 ∷
   rw 6 q3 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw⁻ 7 q18 ∷
   rw 8 q19 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 1 q20 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   rw 5 q22 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q24 ∷
   rw 7 q25 ∷
   rw 8 q24 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q26 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wn 75 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q37 : Eqn
  q37 = eqn (CS23 ∷ CX31 ∷ []) (CX31 ∷ CS23 ∷ []) (wn 40 W)
  q38 : Eqn
  q38 = eqn (CX20 ∷ CX21 ∷ []) (CX21 ∷ CX20 ∷ []) (wn 112 W)
  q39 : Eqn
  q39 = eqn (Sw12 ∷ CX31 ∷ []) (CX32 ∷ Sw12 ∷ []) (wn 113 W)
  q40 : Eqn
  q40 = eqn (CS01⁻ ∷ CX32 ∷ []) (CX32 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CX₁₀))
  q41 : Eqn
  q41 = eqn (Sw12 ∷ CX32 ∷ []) (CX31 ∷ Sw12 ∷ []) (wn 114 W)
  q42 : Eqn
  q42 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q43 : Eqn
  q43 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q44 : Eqn
  q44 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q45 : Eqn
  q45 = eqn (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) (wn 81 W)

-- CCZ023 passes CX31: 131 steps
lem-CCZ023-passes-CX31 : ⟪ (CCZ023 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (CX31 ∷ CCZ023 ∷ []) ⟫ʷ
lem-CCZ023-passes-CX31 = derive (CCZ023 ∷ CX31 ∷ []) (CX31 ∷ CCZ023 ∷ [])
  (rw 1 q20 ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q21 ∷
   rw 1 q28 ∷
   rw 2 q23 ∷
   rw 3 q28 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q24 ∷
   rw 5 q29 ∷
   rw 6 q24 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q30 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 5 q31 ∷
   rw⁻ 4 q24 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q32 ∷
   rw⁻ 2 q23 ∷
   rw 1 q32 ∷
   rw⁻ 0 q21 ∷
   rw 1 q26 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q34 ∷
   rw 0 q29 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 1 q24 ∷
   rw 2 q35 ∷
   rw 3 q24 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw 2 q36 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q24 ∷
   rw 4 q35 ∷
   rw 5 q24 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 4 q21 ∷
   rw 5 q30 ∷
   rw 4 q37 ∷
   rw 5 q12 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 5 q14 ∷
   rw 4 q38 ∷
   rw 5 q12 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 6 q12 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 5 q14 ∷
   re 3 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 2 q12 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   re 7 3 (CX31 ∷ []) ∷
   rw 6 q39 ∷
   rw 5 q40 ∷
   rw 4 q41 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q14 ∷
   re 4 5 (CS03⁻ ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   re 2 3 (CX31 ∷ []) ∷
   rw 3 q12 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 3 q14 ∷
   rw 2 q38 ∷
   rw 3 q12 ∷
   re 1 3 (CX31 ∷ []) ∷
   rw 4 q12 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q14 ∷
   re 1 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 0 q12 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw 4 q39 ∷
   rw 3 q42 ∷
   rw 2 q41 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 1 q14 ∷
   re 2 5 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   re 0 3 (CX31 ∷ []) ∷
   rw 6 q20 ∷
   rw⁻ 5 q21 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 5 q43 ∷
   rw⁻ 4 q24 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw 3 q44 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q24 ∷
   rw 3 q43 ∷
   rw⁻ 2 q24 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 1 q31 ∷
   rw 2 q45 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q21 ∷
   rw 2 q28 ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q24 ∷
   rw 6 q29 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q20 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   rw 5 q22 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q24 ∷
   rw 7 q25 ∷
   rw 8 q24 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q26 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q30 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn [] (CX13 ∷ CX13 ∷ []) (wn 115 W)
  q47 : Eqn
  q47 = eqn [] (CCZ123 ∷ CCZ123 ∷ []) (wn 70 W)
  q48 : Eqn
  q48 = eqn (CX13 ∷ Sw12 ∷ []) (Sw12 ∷ CX23 ∷ []) (wn 36 W)
  q49 : Eqn
  q49 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q50 : Eqn
  q50 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q51 : Eqn
  q51 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q52 : Eqn
  q52 = eqn (CX23 ∷ Sw23 ∷ []) (Sw23 ∷ CX32 ∷ []) (wn 44 W)

-- comm CCZ012 CCZ023: 407 steps
lem-comm-CCZ012-CCZ023 : ⟪ (CCZ012 ∷ CCZ023 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ CCZ012 ∷ []) ⟫ʷ
lem-comm-CCZ012-CCZ023 = derive (CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ012 ∷ [])
  (rw 2 q46 ∷
   rw 3 q20 ∷
   rw 4 q47 ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q28 ∷
   rw 5 q23 ∷
   rw 6 q28 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q24 ∷
   rw 8 q29 ∷
   rw 9 q24 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   rw 6 q23 ∷
   rw 7 q22 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q24 ∷
   rw 9 q25 ∷
   rw 10 q24 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q26 ∷
   re 4 5 (CCZ123 ∷ []) ∷
   re 3 3 (CCZ023 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q21 ∷
   rw 5 q28 ∷
   rw 6 q23 ∷
   rw 7 q28 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q24 ∷
   rw 9 q29 ∷
   rw 10 q24 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q20 ∷
   rw 5 q21 ∷
   rw 6 q22 ∷
   rw 7 q23 ∷
   rw 8 q22 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q24 ∷
   rw 10 q25 ∷
   rw 11 q24 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q26 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   rw 5 q30 ∷
   rw 4 q46 ∷
   rw 5 q3 ∷
   rw 4 q48 ∷
   re 3 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q28 ∷
   rw 5 q23 ∷
   rw 6 q28 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q24 ∷
   rw 8 q29 ∷
   rw 9 q24 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q30 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q17 ∷
   rw 9 q18 ∷
   rw 7 q19 ∷
   re 8 5 (CS03 ∷ []) ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q49 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q50 ∷
   rw 4 q12 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q14 ∷
   rw⁻ 6 q13 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q14 ∷
   rw⁻ 8 q13 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q14 ∷
   rw 5 q51 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 2 q48 ∷
   rw 6 q12 ∷
   rw 5 q52 ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q12 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q13 ∷
   rw 8 q12 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q13 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q14 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q14 ∷
   rw 7 q13 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   rw 5 q13 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   rw 5 q51 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q52 ∷
   rw 4 q9 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q13 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q12 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   rw⁻ 7 q13 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   rw 4 q51 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q12 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q13 ∷
   rw 9 q12 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q13 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q14 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   rw⁻ 7 q13 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   rw 4 q51 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 5 q14 ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q13 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q14 ∷
   rw 2 q15 ∷
   rw 5 q3 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q16 ∷
   rw 7 q3 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw⁻ 8 q18 ∷
   rw 9 q19 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 2 q20 ∷
   rw 3 q21 ∷
   rw 4 q22 ∷
   rw 5 q23 ∷
   rw 6 q22 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q24 ∷
   rw 8 q25 ∷
   rw 9 q24 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q26 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 2 3 (CCZ023 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q10 ∷
   rw 6 q3 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q11 ∷
   rw 8 q3 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q5 ∷
   rw 3 q8 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 4 q5 ∷
   rw 3 q20 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q28 ∷
   rw 4 q23 ∷
   rw 5 q28 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q24 ∷
   rw 7 q29 ∷
   rw 8 q24 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q30 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 7 q31 ∷
   rw⁻ 6 q24 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q32 ∷
   rw⁻ 4 q23 ∷
   rw 3 q32 ∷
   rw⁻ 2 q21 ∷
   rw 3 q26 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q21 ∷
   rw 2 q28 ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q24 ∷
   rw 6 q29 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q30 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 6 q31 ∷
   rw⁻ 5 q24 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q32 ∷
   rw⁻ 3 q23 ∷
   rw 2 q32 ∷
   rw⁻ 1 q21 ∷
   rw 2 q26 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   rw 2 q33 ∷
   rw 1 q30 ∷
   rw 0 q27 ∷
   rw 3 q3 ∷
   rw 2 q48 ∷
   re 1 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q21 ∷
   rw 2 q28 ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q24 ∷
   rw 6 q29 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q30 ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw 7 q18 ∷
   rw 5 q19 ∷
   re 6 5 (CS03 ∷ []) ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q49 ∷
   re 2 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q5 ∷
   rw 1 q50 ∷
   rw 2 q12 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q14 ∷
   rw⁻ 4 q13 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q14 ∷
   rw⁻ 6 q13 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q14 ∷
   rw 3 q51 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 0 q48 ∷
   rw 4 q12 ∷
   rw 3 q52 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q12 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q13 ∷
   rw 6 q12 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q13 ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q14 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q14 ∷
   rw 5 q13 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   rw 3 q13 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   rw 3 q51 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q52 ∷
   rw 2 q9 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q12 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q13 ∷
   rw 5 q12 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q12 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q14 ∷
   rw⁻ 3 q13 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   rw 2 q51 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q13 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q14 ∷
   rw⁻ 3 q13 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q14 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q14 ∷
   rw 2 q51 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 3 q14 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q12 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q13 ∷
   rw 5 q12 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q14 ∷
   rw 0 q15 ∷
   rw 3 q3 ∷
   re 1 3 (CX02 ∷ []) ∷
   rw 2 q16 ∷
   rw 5 q3 ∷
   re 3 3 (CX02 ∷ []) ∷
   re 5 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw⁻ 6 q18 ∷
   rw 7 q19 ∷
   re 4 5 (CS03 ∷ []) ∷
   rw 0 q20 ∷
   rw 1 q21 ∷
   rw 2 q22 ∷
   rw 3 q23 ∷
   rw 4 q22 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q24 ∷
   rw 6 q25 ∷
   rw 7 q24 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 1 q26 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   re 0 3 (CCZ023 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 1 q10 ∷
   rw 4 q3 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q11 ∷
   rw 6 q3 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q5 ∷
   rw 1 q8 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   rw 2 q5 ∷ []) Eq.refl
