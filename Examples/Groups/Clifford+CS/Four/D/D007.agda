{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D007 (W : Ws) where

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
  q1 = wE 12 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = wE 121 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = wE 30 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 122 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 127 W
  q12 : Eqn
  q12 = wE 118 W
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 74 W
  q15 : Eqn
  q15 = wE 125 W
  q16 : Eqn
  q16 = wE 128 W
  q17 : Eqn
  q17 = wE 24 W
  q18 : Eqn
  q18 = wE 25 W
  q19 : Eqn
  q19 = wE 26 W
  q20 : Eqn
  q20 = wE 129 W
  q21 : Eqn
  q21 = eqn (K0⁻ ∷ Sw12 ∷ []) (Sw12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (Swap))
  q22 : Eqn
  q22 = wE 14 W
  q23 : Eqn
  q23 = wE 75 W
  q24 : Eqn
  q24 = wE 39 W
  q25 : Eqn
  q25 = wE 29 W
  q26 : Eqn
  q26 = wE 130 W
  q27 : Eqn
  q27 = wE 22 W
  q28 : Eqn
  q28 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q29 : Eqn
  q29 = wE 23 W
  q30 : Eqn
  q30 = wE 131 W
  q31 : Eqn
  q31 = wE 132 W
  q32 : Eqn
  q32 = wE 1 W
  q33 : Eqn
  q33 = wE 3 W
  q34 : Eqn
  q34 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q35 : Eqn
  q35 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q36 : Eqn
  q36 = wE 104 W
  q37 : Eqn
  q37 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q38 : Eqn
  q38 = wE 43 W
  q39 : Eqn
  q39 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q40 : Eqn
  q40 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q41 : Eqn
  q41 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q42 : Eqn
  q42 = wE 55 W
  q43 : Eqn
  q43 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q44 : Eqn
  q44 = wE 56 W
  q45 : Eqn
  q45 = wE 133 W
  q46 : Eqn
  q46 = wE 134 W
  q47 : Eqn
  q47 = wE 53 W
  q48 : Eqn
  q48 = wE 100 W
  q49 : Eqn
  q49 = wE 135 W
  q50 : Eqn
  q50 = wE 6 W
  q51 : Eqn
  q51 = wE 136 W
  q52 : Eqn
  q52 = wE 137 W
  q53 : Eqn
  q53 = wE 138 W
  q54 : Eqn
  q54 = wE 139 W
  q55 : Eqn
  q55 = wE 140 W
  q56 : Eqn
  q56 = wE 141 W
  q57 : Eqn
  q57 = wE 142 W
  q58 : Eqn
  q58 = wE 143 W
  q59 : Eqn
  q59 = wE 144 W
  q60 : Eqn
  q60 = wE 145 W
  q61 : Eqn
  q61 = wE 146 W
  q62 : Eqn
  q62 = wE 147 W
  q63 : Eqn
  q63 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q64 : Eqn
  q64 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))

-- SW13-Rk: 743 steps
lem-SW13-Rk : ⟪ (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-SW13-Rk = derive (Sw12 ∷ Sw23 ∷ Sw12 ∷ CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (CK30 ∷ Toff012 ∷ CK30⁻ ∷ Toff012 ∷ [])
  (rw 6 q1 ∷
   rw 5 q1 ∷
   rw 4 q1 ∷
   rw 13 q2 ∷
   re 12 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 13 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q4 ∷
   rw 14 q5 ∷
   rw 15 q6 ∷
   rw 16 q5 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   rw 18 q8 ∷
   rw 19 q7 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 18 q3 ∷
   rw 19 q9 ∷
   rw 20 q10 ∷
   rw 19 q11 ∷
   rw 18 q12 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q7 ∷
   rw 18 q13 ∷
   rw⁻ 17 q7 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 16 q14 ∷
   rw⁻ 15 q6 ∷
   rw 14 q14 ∷
   rw⁻ 13 q4 ∷
   rw 12 q12 ∷
   rw 13 q15 ∷
   re 13 8 (Toff123 ∷ []) ∷
   rw 13 q16 ∷
   rw 12 q3 ∷
   re 14 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 13 q4 ∷
   rw 14 q5 ∷
   rw 15 q6 ∷
   rw 16 q5 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q7 ∷
   rw 18 q8 ∷
   rw 19 q7 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 13 q2 ∷
   rw 14 q4 ∷
   rw 15 q17 ∷
   rw 16 q6 ∷
   rw 17 q17 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   rw 19 q18 ∷
   rw 20 q7 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 14 q19 ∷
   re 14 5 (CCZ123 ∷ []) ∷
   re 13 3 (CCZ023 ∷ []) ∷
   rw 14 q20 ∷
   rw 15 q10 ∷
   rw 14 q1 ∷
   rw 16 q21 ∷
   rw 15 q22 ∷
   rw 13 q1 ∷
   rw 16 q2 ∷
   re 15 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 16 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 15 q4 ∷
   rw 16 q5 ∷
   rw 17 q6 ∷
   rw 18 q5 ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q7 ∷
   rw 20 q8 ∷
   rw 21 q7 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 20 q10 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q7 ∷
   rw 20 q13 ∷
   rw⁻ 19 q7 ∷
   re 20 3 (CS13 ∷ []) ∷
   rw 18 q14 ∷
   rw⁻ 17 q6 ∷
   rw 16 q14 ∷
   rw⁻ 15 q4 ∷
   rw 16 q19 ∷
   re 16 5 (CCZ123 ∷ []) ∷
   rw 16 q23 ∷
   rw 15 q8 ∷
   re 17 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 16 q7 ∷
   rw 17 q24 ∷
   rw 18 q7 ∷
   re 16 3 (CX30 ∷ []) ∷
   rw 17 q25 ∷
   re 19 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q7 ∷
   rw 19 q24 ∷
   rw 20 q7 ∷
   re 18 3 (CX30 ∷ []) ∷
   rw 19 q4 ∷
   rw 20 q10 ∷
   rw 16 q1 ∷
   rw 19 q1 ∷
   rw 22 q1 ∷
   rw 25 q1 ∷
   rw 26 q26 ∷
   re 24 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 27 q27 ∷
   rw 26 q28 ∷
   rw 24 q29 ∷
   re 25 5 (CX30 ∷ []) ∷
   rw 23 q22 ∷
   rw 20 q30 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q27 ∷
   rw 20 q28 ∷
   rw 18 q29 ∷
   re 19 5 (CX30 ∷ []) ∷
   rw 17 q22 ∷
   rw 14 q31 ∷
   rw 19 q32 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q33 ∷
   re 17 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 19 q33 ∷
   rw 16 q34 ∷
   re 15 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 17 q33 ∷
   rw 14 q35 ∷
   rw 15 q36 ∷
   re 15 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 16 q32 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 15 q37 ∷
   rw 18 q32 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw⁻ 17 q37 ∷
   rw 20 q32 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 14 q32 ∷
   re 16 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 15 q33 ∷
   rw⁻ 16 q37 ∷
   re 18 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 17 q33 ∷
   rw⁻ 18 q37 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q33 ∷
   rw 15 q38 ∷
   re 15 5 (CCZ012 ∷ []) ∷
   re 14 3 (CCZ013 ∷ []) ∷
   rw 15 q33 ∷
   rw 12 q39 ∷
   rw 11 q22 ∷
   rw 14 q32 ∷
   rw 13 q40 ∷
   re 12 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 13 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 14 q32 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q37 ∷
   rw 16 q32 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q37 ∷
   rw 18 q32 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 17 q33 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q33 ∷
   rw 15 q37 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q33 ∷
   rw 13 q37 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q33 ∷
   rw 13 q38 ∷
   re 13 5 (CCZ012 ∷ []) ∷
   rw 11 q41 ∷
   rw 12 q42 ∷
   re 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 11 q41 ∷
   rw 14 q32 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q37 ∷
   rw 16 q32 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q37 ∷
   rw 18 q32 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw⁻ 17 q41 ∷
   rw⁻ 18 q43 ∷
   rw 11 q32 ∷
   rw⁻ 12 q41 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q33 ∷
   rw⁻ 14 q37 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q33 ∷
   rw⁻ 16 q37 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q33 ∷
   rw⁻ 18 q41 ∷
   rw⁻ 19 q43 ∷
   rw 12 q44 ∷
   re 12 8 (Toff012 ∷ []) ∷
   re 11 3 (Toff013 ∷ []) ∷
   rw 12 q33 ∷
   rw 8 q45 ∷
   rw 7 q2 ∷
   re 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 13 q7 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q3 ∷
   rw 13 q9 ∷
   rw 14 q10 ∷
   rw 13 q11 ∷
   rw 12 q12 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q7 ∷
   rw 12 q13 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q14 ∷
   rw⁻ 9 q6 ∷
   rw 8 q14 ∷
   rw⁻ 7 q4 ∷
   rw 6 q12 ∷
   rw 7 q15 ∷
   re 7 8 (Toff123 ∷ []) ∷
   rw 7 q16 ∷
   rw 6 q3 ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q6 ∷
   rw 10 q5 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q7 ∷
   rw 12 q8 ∷
   rw 13 q7 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q4 ∷
   rw 9 q17 ∷
   rw 10 q6 ∷
   rw 11 q17 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q18 ∷
   rw 14 q7 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q19 ∷
   re 8 5 (CCZ123 ∷ []) ∷
   re 7 3 (CCZ023 ∷ []) ∷
   rw 8 q20 ∷
   rw 9 q10 ∷
   rw 8 q1 ∷
   rw 10 q21 ∷
   rw 9 q22 ∷
   rw 7 q1 ∷
   rw 10 q2 ∷
   re 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q4 ∷
   rw 10 q5 ∷
   rw 11 q6 ∷
   rw 12 q5 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q7 ∷
   rw 14 q8 ∷
   rw 15 q7 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q10 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q7 ∷
   rw 14 q13 ∷
   rw⁻ 13 q7 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 12 q14 ∷
   rw⁻ 11 q6 ∷
   rw 10 q14 ∷
   rw⁻ 9 q4 ∷
   rw 10 q19 ∷
   re 10 5 (CCZ123 ∷ []) ∷
   rw 10 q23 ∷
   rw 9 q8 ∷
   re 11 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw 11 q24 ∷
   rw 12 q7 ∷
   re 10 3 (CX30 ∷ []) ∷
   rw 11 q25 ∷
   re 13 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw 13 q24 ∷
   rw 14 q7 ∷
   re 12 3 (CX30 ∷ []) ∷
   rw 13 q4 ∷
   rw 14 q10 ∷
   rw 10 q1 ∷
   rw 13 q1 ∷
   rw 16 q1 ∷
   rw 19 q1 ∷
   rw 20 q26 ∷
   re 18 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 21 q27 ∷
   rw 20 q28 ∷
   rw 18 q29 ∷
   re 19 5 (CX30 ∷ []) ∷
   rw 17 q22 ∷
   rw 14 q30 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CX10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q27 ∷
   rw 14 q28 ∷
   rw 12 q29 ∷
   re 13 5 (CX30 ∷ []) ∷
   rw 11 q22 ∷
   rw 8 q31 ∷
   rw 13 q32 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q33 ∷
   re 11 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 13 q33 ∷
   rw 10 q34 ∷
   re 9 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw 8 q35 ∷
   rw 9 q36 ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 10 q32 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q37 ∷
   rw 12 q32 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q37 ∷
   rw 14 q32 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 8 q32 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw⁻ 10 q37 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw⁻ 12 q37 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q33 ∷
   rw 9 q38 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   rw 9 q33 ∷
   rw 6 q39 ∷
   rw 5 q22 ∷
   rw 8 q32 ∷
   rw 7 q40 ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q32 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q37 ∷
   rw 10 q32 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q37 ∷
   rw 12 q32 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q33 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q33 ∷
   rw 9 q37 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw 7 q37 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q33 ∷
   rw 7 q38 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   rw 5 q41 ∷
   rw 6 q42 ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q41 ∷
   rw 8 q32 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q37 ∷
   rw 10 q32 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q37 ∷
   rw 12 q32 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q41 ∷
   rw⁻ 12 q43 ∷
   rw 5 q32 ∷
   rw⁻ 6 q41 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q33 ∷
   rw⁻ 8 q37 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw⁻ 10 q37 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw⁻ 12 q41 ∷
   rw⁻ 13 q43 ∷
   rw 6 q44 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 5 3 (Toff013 ∷ []) ∷
   rw 6 q33 ∷
   rw 2 q46 ∷
   rw 5 q32 ∷
   rw 4 q32 ∷
   rw 3 q32 ∷
   rw 12 q32 ∷
   re 11 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 12 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 11 q41 ∷
   rw 14 q32 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q37 ∷
   rw 16 q32 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q37 ∷
   rw 18 q32 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw⁻ 17 q41 ∷
   rw⁻ 18 q43 ∷
   rw 19 q33 ∷
   rw 18 q43 ∷
   rw 17 q41 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q33 ∷
   rw 15 q37 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 16 q33 ∷
   rw 13 q37 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q33 ∷
   rw 11 q41 ∷
   rw 12 q44 ∷
   re 12 8 (Toff012 ∷ []) ∷
   rw 12 q47 ∷
   rw⁻ 11 q41 ∷
   re 13 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 14 q32 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw⁻ 13 q37 ∷
   rw 16 q32 ∷
   re 14 3 (CS13⁻ ∷ []) ∷
   rw⁻ 15 q37 ∷
   rw 18 q32 ∷
   re 16 3 (CS03 ∷ []) ∷
   rw 12 q32 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q33 ∷
   rw⁻ 14 q37 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q33 ∷
   rw⁻ 16 q37 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q33 ∷
   rw 13 q38 ∷
   re 13 5 (CCZ012 ∷ []) ∷
   re 12 3 (CCZ013 ∷ []) ∷
   rw⁻ 13 q40 ∷
   rw 14 q33 ∷
   rw 13 q32 ∷
   rw 15 q40 ∷
   rw 14 q33 ∷
   rw 12 q32 ∷
   rw 15 q32 ∷
   re 14 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 15 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 16 q32 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 15 q37 ∷
   rw 18 q32 ∷
   re 16 3 (CS13⁻ ∷ []) ∷
   rw⁻ 17 q37 ∷
   rw 20 q32 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 19 q33 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q33 ∷
   rw 17 q37 ∷
   re 16 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 18 q33 ∷
   rw 15 q37 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q33 ∷
   rw 15 q38 ∷
   re 15 5 (CCZ012 ∷ []) ∷
   rw 15 q48 ∷
   rw⁻ 14 q35 ∷
   rw 17 q32 ∷
   re 15 3 (CX30 ∷ []) ∷
   rw⁻ 16 q34 ∷
   rw 19 q32 ∷
   re 17 3 (CX30 ∷ []) ∷
   rw 20 q32 ∷
   re 18 3 (CS13 ∷ []) ∷
   rw 19 q33 ∷
   rw 15 q32 ∷
   rw 18 q32 ∷
   rw 21 q32 ∷
   rw 24 q32 ∷
   rw 25 q49 ∷
   rw 25 q2 ∷
   rw⁻ 24 q7 ∷
   re 23 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q7 ∷
   rw 24 q50 ∷
   rw⁻ 23 q7 ∷
   re 24 3 (CX31 ∷ []) ∷
   rw⁻ 22 q7 ∷
   rw 23 q51 ∷
   rw 22 q24 ∷
   rw 23 q10 ∷
   rw 20 q34 ∷
   rw 19 q33 ∷
   rw 19 q2 ∷
   rw⁻ 18 q7 ∷
   re 17 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q7 ∷
   rw 18 q50 ∷
   rw⁻ 17 q7 ∷
   re 18 3 (CX31 ∷ []) ∷
   rw⁻ 16 q7 ∷
   rw 17 q51 ∷
   rw 16 q24 ∷
   rw 17 q10 ∷
   rw 14 q35 ∷
   rw 13 q33 ∷
   rw 13 q36 ∷
   rw 11 q41 ∷
   rw 10 q33 ∷
   rw 10 q42 ∷
   rw 10 q2 ∷
   rw⁻ 9 q7 ∷
   rw 8 q52 ∷
   rw⁻ 7 q7 ∷
   rw 8 q53 ∷
   re 8 1 (Sw23 ∷ CK21⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 8 q54 ∷
   rw 9 q7 ∷
   re 7 3 (CK30⁻ ∷ []) ∷
   rw 8 q10 ∷
   rw 6 q32 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q41 ∷
   rw 8 q32 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q37 ∷
   rw 10 q32 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q37 ∷
   rw 12 q32 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q41 ∷
   rw⁻ 12 q43 ∷
   rw 13 q33 ∷
   rw 12 q43 ∷
   rw 11 q41 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q33 ∷
   rw 9 q37 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw 7 q37 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q33 ∷
   rw 5 q41 ∷
   rw 6 q44 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 6 q47 ∷
   rw⁻ 5 q41 ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q32 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q37 ∷
   rw 10 q32 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q37 ∷
   rw 12 q32 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q32 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q33 ∷
   rw⁻ 8 q37 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q33 ∷
   rw⁻ 10 q37 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q33 ∷
   rw 7 q38 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   rw⁻ 7 q40 ∷
   rw 8 q33 ∷
   rw 7 q32 ∷
   rw 9 q40 ∷
   rw 8 q33 ∷
   rw 6 q32 ∷
   rw 9 q32 ∷
   re 8 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 9 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 10 q32 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q37 ∷
   rw 12 q32 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q37 ∷
   rw 14 q32 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q33 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q33 ∷
   rw 11 q37 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q33 ∷
   rw 9 q37 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw 9 q38 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   rw 9 q48 ∷
   rw⁻ 8 q35 ∷
   rw 11 q32 ∷
   re 9 3 (CX30 ∷ []) ∷
   rw⁻ 10 q34 ∷
   rw 13 q32 ∷
   re 11 3 (CX30 ∷ []) ∷
   rw 14 q32 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 13 q33 ∷
   rw 9 q32 ∷
   rw 12 q32 ∷
   rw 15 q32 ∷
   rw 18 q32 ∷
   rw 19 q49 ∷
   rw 19 q2 ∷
   rw⁻ 18 q7 ∷
   re 17 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q7 ∷
   rw 18 q50 ∷
   rw⁻ 17 q7 ∷
   re 18 3 (CX31 ∷ []) ∷
   rw⁻ 16 q7 ∷
   rw 17 q51 ∷
   rw 16 q24 ∷
   rw 17 q10 ∷
   rw 14 q34 ∷
   rw 13 q33 ∷
   rw 13 q2 ∷
   rw⁻ 12 q7 ∷
   re 11 1 (Sw23 ∷ CX20 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q7 ∷
   rw 12 q50 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (CX31 ∷ []) ∷
   rw⁻ 10 q7 ∷
   rw 11 q51 ∷
   rw 10 q24 ∷
   rw 11 q10 ∷
   rw 8 q35 ∷
   rw 7 q33 ∷
   rw 7 q36 ∷
   rw 5 q41 ∷
   rw 4 q33 ∷
   rw 4 q42 ∷
   rw 4 q2 ∷
   rw⁻ 3 q7 ∷
   rw 2 q55 ∷
   rw⁻ 1 q7 ∷
   rw 2 q56 ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 1 q7 ∷
   rw 2 q57 ∷
   rw 3 q7 ∷
   re 1 3 (CK30 ∷ []) ∷
   rw 2 q10 ∷
   rw 4 q1 ∷
   rw 3 q1 ∷
   rw 2 q1 ∷
   rw 10 q47 ∷
   rw 12 q1 ∷
   rw 14 q21 ∷
   rw 13 q22 ∷
   rw 11 q1 ∷
   rw 13 q48 ∷
   rw 14 q1 ∷
   rw 17 q1 ∷
   rw 20 q1 ∷
   rw 23 q1 ∷
   rw 24 q58 ∷
   rw 21 q59 ∷
   rw 18 q60 ∷
   rw 15 q59 ∷
   rw 12 q61 ∷
   rw 12 q62 ∷
   rw 10 q39 ∷
   rw 9 q22 ∷
   rw 9 q42 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CK10⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q27 ∷
   rw 9 q63 ∷
   rw 7 q29 ∷
   re 8 5 (CK30⁻ ∷ []) ∷
   rw 6 q22 ∷
   rw 4 q47 ∷
   rw 6 q1 ∷
   rw 8 q21 ∷
   rw 7 q22 ∷
   rw 5 q1 ∷
   rw 7 q48 ∷
   rw 8 q1 ∷
   rw 11 q1 ∷
   rw 14 q1 ∷
   rw 17 q1 ∷
   rw 18 q58 ∷
   rw 15 q59 ∷
   rw 12 q60 ∷
   rw 9 q59 ∷
   rw 6 q61 ∷
   rw 6 q62 ∷
   rw 4 q39 ∷
   rw 3 q22 ∷
   rw 3 q42 ∷
   re 1 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 4 q27 ∷
   rw 3 q64 ∷
   rw 1 q29 ∷
   re 2 5 (CK30 ∷ []) ∷
   rw 0 q22 ∷ []) Eq.refl
