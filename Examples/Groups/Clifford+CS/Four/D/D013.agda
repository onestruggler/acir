{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D013 (W : Ws) where

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
  q2 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q8 : Eqn
  q8 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q9 : Eqn
  q9 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q10 : Eqn
  q10 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q11 : Eqn
  q11 = eqn (CCZ123 ∷ []) (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wn 75 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CX21 ∷ []) (CX20 ∷ Sw01 ∷ []) (wn 39 W)
  q13 : Eqn
  q13 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q14 : Eqn
  q14 = eqn (CS23 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS23 ∷ []) (wn 82 W)
  q15 : Eqn
  q15 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q16 : Eqn
  q16 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q17 : Eqn
  q17 = eqn (CX20 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CX20 ∷ []) (wn 261 W)
  q18 : Eqn
  q18 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q19 : Eqn
  q19 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q20 : Eqn
  q20 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q21 : Eqn
  q21 = eqn (CS01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01 ∷ []) (low-comm (CS) ((CS • CS • CS)))
  q22 : Eqn
  q22 = eqn (CX20 ∷ Sw01 ∷ []) (Sw01 ∷ CX21 ∷ []) (wn 6 W)
  q23 : Eqn
  q23 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q24 : Eqn
  q24 = eqn (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (CCZ123 ∷ []) (wn 81 W)
  q25 : Eqn
  q25 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q26 : Eqn
  q26 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)

-- comm CCZ023 CSd13: 131 steps
lem-comm-CCZ023-CSd13 : ⟪ (CCZ023 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CSd13 = derive (CCZ023 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CCZ023 ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q11 ∷
   rw 0 q6 ∷
   re 2 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw 2 q12 ∷
   rw 3 q5 ∷
   re 1 3 (CX30 ∷ []) ∷
   rw 2 q13 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 4 q12 ∷
   rw 5 q5 ∷
   re 3 3 (CX30 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q7 ∷
   rw 4 q14 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   re 3 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   rw 5 q15 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw 6 q15 ∷
   re 4 3 (CX30 ∷ []) ∷
   rw 5 q16 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q15 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   re 3 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q15 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw 6 q18 ∷
   rw 5 q19 ∷
   rw 4 q20 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   re 4 5 (CS03⁻ ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw 3 q15 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q16 ∷
   re 1 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   rw 2 q17 ∷
   rw 3 q15 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 4 q15 ∷
   re 2 3 (CX30 ∷ []) ∷
   rw 3 q16 ∷
   re 1 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 0 q15 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   re 2 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 1 q16 ∷
   re 2 5 (CS03 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q16 ∷
   re 0 3 (CS13⁻ ∷ []) ∷
   rw 6 q1 ∷
   rw⁻ 5 q2 ∷
   re 4 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q22 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (CX31 ∷ []) ∷
   rw 3 q23 ∷
   re 2 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q5 ∷
   rw 3 q22 ∷
   rw⁻ 2 q5 ∷
   re 3 3 (CX31 ∷ []) ∷
   rw 1 q8 ∷
   rw 2 q24 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q10 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (CS02 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS02 ∷ []) (wn 262 W)

-- pass [CS03] [CSd03]: 11 steps
lem-pass-CS03-vs-CSd03 : ⟪ (CS03 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CSd03 = derive (CS03 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS03 ∷ [])
  (rw 2 q15 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q16 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q27 ∷
   rw 2 q15 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw 3 q15 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q29 : Eqn
  q29 = eqn (CS02 ∷ S0 ∷ CS02⁻ ∷ []) (S0 ∷ CS02⁻ ∷ CS02 ∷ []) (wn 263 W)

-- pass [CS03] [S0 CSd03]: 13 steps
lem-pass-CS03-vs-S0-CSd03 : ⟪ (CS03 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-S0-CSd03 = derive (CS03 ∷ S0 ∷ CS03⁻ ∷ []) (S0 ∷ CS03⁻ ∷ CS03 ∷ [])
  (rw 3 q15 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q16 ∷
   rw 1 q28 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q29 ∷
   rw⁻ 0 q28 ∷
   rw 3 q15 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 4 q15 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q16 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (S0 ∷ CS02 ∷ []) (CS02 ∷ S0 ∷ []) (wn 183 W)

-- pass [S0] [CS02]: 1 steps
lem-pass-S0-vs-CS02 : ⟪ (S0 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS02 = derive (S0 ∷ CS02 ∷ []) (CS02 ∷ S0 ∷ [])
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (S0 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ S0 ∷ []) (wn 184 W)

-- pass [S0] [CSd02]: 1 steps
lem-pass-S0-vs-CSd02 : ⟪ (S0 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd02 = derive (S0 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ S0 ∷ [])
  (rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (CCZ123 ∷ []) (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (wn 163 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q34 : Eqn
  q34 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q35 : Eqn
  q35 = eqn (CS02 ∷ CS01 ∷ []) (CS01 ∷ CS02 ∷ []) (wn 245 W)
  q36 : Eqn
  q36 = eqn (CS01 ∷ CX32 ∷ []) (CX32 ∷ CS01 ∷ []) (low-comm (CS) (CX₁₀))
  q37 : Eqn
  q37 = eqn (CS02⁻ ∷ CS01 ∷ []) (CS01 ∷ CS02⁻ ∷ []) (wn 264 W)
  q38 : Eqn
  q38 = eqn (CS12 ∷ CX32 ∷ CS12⁻ ∷ CX32 ∷ CS13 ∷ []) (CCZ123 ∷ []) (wn 166 W)

-- comm CCZ023 CS01: 83 steps
lem-comm-CCZ023-CS01 : ⟪ (CCZ023 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CCZ023 ∷ []) ⟫ʷ
lem-comm-CCZ023-CS01 = derive (CCZ023 ∷ CS01 ∷ []) (CS01 ∷ CCZ023 ∷ [])
  (rw 1 q1 ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q32 ∷
   rw 0 q6 ∷
   rw 1 q33 ∷
   rw 2 q13 ∷
   rw 3 q33 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   rw 6 q15 ∷
   rw 5 q34 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q35 ∷
   rw⁻ 4 q34 ∷
   rw 7 q15 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q16 ∷
   rw⁻ 3 q36 ∷
   rw 2 q37 ∷
   rw⁻ 1 q36 ∷
   rw 0 q35 ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 6 q8 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 4 q33 ∷
   rw 3 q23 ∷
   rw⁻ 2 q33 ∷
   rw 1 q8 ∷
   rw 2 q38 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q10 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))

-- pass [CS23] [CS01]: 1 steps
lem-pass-CS23-vs-CS01 : ⟪ (CS23 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-CS01 = derive (CS23 ∷ CS01 ∷ []) (CS01 ∷ CS23 ∷ [])
  (rw⁻ 0 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (S0 ∷ CS01 ∷ []) (CS01 ∷ S0 ∷ []) (wn 265 W)

-- pass [S0] [CS01]: 1 steps
lem-pass-S0-vs-CS01 : ⟪ (S0 ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS01 = derive (S0 ∷ CS01 ∷ []) (CS01 ∷ S0 ∷ [])
  (rw 0 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = eqn (CCZ123 ∷ CS23 ∷ []) (CS23 ∷ CCZ123 ∷ []) (wn 266 W)

-- pass [CCZ023] [CS23]: 51 steps
lem-pass-CCZ023-vs-CS23 : ⟪ (CCZ023 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CS23 = derive (CCZ023 ∷ CS23 ∷ []) (CS23 ∷ CCZ023 ∷ [])
  (rw 2 q1 ∷
   rw⁻ 1 q2 ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q41 ∷
   rw 0 q2 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q10 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CZ23 ∷ []) (CZ23 ∷ Sw01 ∷ []) (low-comm (Swap) (CZ))
  q43 : Eqn
  q43 = eqn (CCZ123 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ123 ∷ []) (wn 267 W)

-- pass [CCZ023] [CZ23]: 51 steps
lem-pass-CCZ023-vs-CZ23 : ⟪ (CCZ023 ∷ CZ23 ∷ []) ⟫ʷ ≈ ⟪ (CZ23 ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CZ23 = derive (CCZ023 ∷ CZ23 ∷ []) (CZ23 ∷ CCZ023 ∷ [])
  (rw 2 q1 ∷
   rw⁻ 1 q42 ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q43 ∷
   rw 0 q42 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q10 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (S0 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ S0 ∷ []) (wn 268 W)

-- pass [S0] [CSd01]: 1 steps
lem-pass-S0-vs-CSd01 : ⟪ (S0 ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CSd01 = derive (S0 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ S0 ∷ [])
  (rw 0 q44 ∷ []) Eq.refl

-- pass [CSd23] [CS01]: 1 steps
lem-pass-CSd23-vs-CS01 : ⟪ (CS23⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-CS01 = derive (CS23⁻ ∷ CS01 ∷ []) (CS01 ∷ CS23⁻ ∷ [])
  (rw⁻ 0 q21 ∷ []) Eq.refl

-- pass [CSd03] [CS01]: 9 steps
lem-pass-CSd03-vs-CS01 : ⟪ (CS03⁻ ∷ CS01 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CS01 = derive (CS03⁻ ∷ CS01 ∷ []) (CS01 ∷ CS03⁻ ∷ [])
  (rw 2 q15 ∷
   rw 1 q34 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q37 ∷
   rw⁻ 0 q34 ∷
   rw 3 q15 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = eqn (CCZ123 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ123 ∷ []) (wn 269 W)

-- pass [CCZ023] [CSd23]: 51 steps
lem-pass-CCZ023-vs-CSd23 : ⟪ (CCZ023 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ CCZ023 ∷ []) ⟫ʷ
lem-pass-CCZ023-vs-CSd23 = derive (CCZ023 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ023 ∷ [])
  (rw 2 q1 ∷
   rw⁻ 1 q4 ∷
   re 0 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 1 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (CCZ123 ∷ []) ∷
   rw 1 q45 ∷
   rw 0 q4 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q10 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q47 : Eqn
  q47 = eqn (CS02⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS02⁻ ∷ []) (wn 270 W)

-- pass [CSd03] [CSd01]: 9 steps
lem-pass-CSd03-vs-CSd01 : ⟪ (CS03⁻ ∷ CS01⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS01⁻ ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CSd01 = derive (CS03⁻ ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS03⁻ ∷ [])
  (rw 2 q15 ∷
   rw 1 q46 ∷
   re 0 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 2 q16 ∷
   rw 1 q47 ∷
   rw⁻ 0 q46 ∷
   rw 3 q15 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q16 ∷ []) Eq.refl
