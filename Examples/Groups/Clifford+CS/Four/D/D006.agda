{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D006 (W : Ws) where

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
  q1 = eqn [] (K0 ∷ K0⁻ ∷ []) (wn 116 W)
  q2 : Eqn
  q2 = eqn (K0⁻ ∷ CK10 ∷ K0 ∷ []) (CK10 ∷ []) (wn 117 W)
  q3 : Eqn
  q3 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q4 : Eqn
  q4 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q5 : Eqn
  q5 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q9 : Eqn
  q9 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q11 : Eqn
  q11 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q12 : Eqn
  q12 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q13 : Eqn
  q13 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q14 : Eqn
  q14 = eqn (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) (wn 119 W)
  q15 : Eqn
  q15 = eqn (K1⁻ ∷ CCZ123 ∷ K1 ∷ []) (Toff123 ∷ []) (wn 120 W)
  q16 : Eqn
  q16 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q17 : Eqn
  q17 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q18 : Eqn
  q18 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q19 : Eqn
  q19 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q22 : Eqn
  q22 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q23 : Eqn
  q23 = eqn (K0⁻ ∷ CK10⁻ ∷ K0 ∷ []) (CK10⁻ ∷ []) (wn 126 W)

-- Rk: 119 steps
lem-Rk : ⟪ (K0⁻ ∷ CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ []) ⟫ʷ
lem-Rk = derive (K0⁻ ∷ CK10 ∷ CCZ023 ∷ CK10⁻ ∷ CCZ023 ∷ K0 ∷ []) (CK10 ∷ Toff023 ∷ CK10⁻ ∷ Toff023 ∷ [])
  (rw 4 q1 ∷
   rw 3 q1 ∷
   rw 2 q1 ∷
   rw 0 q2 ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q10 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q8 ∷
   rw 7 q11 ∷
   rw⁻ 6 q8 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q12 ∷
   rw⁻ 4 q7 ∷
   rw 3 q12 ∷
   rw⁻ 2 q5 ∷
   rw 3 q13 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 1 q14 ∷
   rw 2 q15 ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q16 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q8 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q16 ∷
   rw 8 q17 ∷
   rw 1 q3 ∷
   rw 2 q18 ∷
   rw 3 q5 ∷
   rw 4 q19 ∷
   rw 5 q7 ∷
   rw 6 q19 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q8 ∷
   rw 8 q20 ∷
   rw 9 q8 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q18 ∷
   rw 9 q21 ∷
   rw 2 q22 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw 2 q10 ∷
   rw 2 q23 ∷
   rw 6 q3 ∷
   rw 5 q4 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q10 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q8 ∷
   rw 9 q11 ∷
   rw⁻ 8 q8 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   rw⁻ 6 q7 ∷
   rw 5 q12 ∷
   rw⁻ 4 q5 ∷
   rw 5 q13 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q16 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q16 ∷
   rw 10 q17 ∷
   rw 3 q3 ∷
   rw 4 q18 ∷
   rw 5 q5 ∷
   rw 6 q19 ∷
   rw 7 q7 ∷
   rw 8 q19 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q8 ∷
   rw 10 q20 ∷
   rw 11 q8 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q18 ∷
   rw 11 q21 ∷
   rw 4 q22 ∷
   re 4 8 (Toff123 ∷ []) ∷
   re 3 3 (Toff023 ∷ []) ∷
   rw 4 q10 ∷ []) Eq.refl
