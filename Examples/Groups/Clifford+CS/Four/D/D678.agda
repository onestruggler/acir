{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D678 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D651 W using (lem-S2)

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q4 : Eqn
  q4 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q5 : Eqn
  q5 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q6 : Eqn
  q6 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q7 : Eqn
  q7 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q8 : Eqn
  q8 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q9 : Eqn
  q9 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q10 : Eqn
  q10 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q11 : Eqn
  q11 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q12 : Eqn
  q12 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q13 : Eqn
  q13 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q14 : Eqn
  q14 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q15 : Eqn
  q15 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q16 : Eqn
  q16 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q17 : Eqn
  q17 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q18 : Eqn
  q18 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q19 : Eqn
  q19 = eqn (K0 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 46 W)
  q20 : Eqn
  q20 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q21 : Eqn
  q21 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2)
  q22 : Eqn
  q22 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q23 : Eqn
  q23 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q24 : Eqn
  q24 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q25 : Eqn
  q25 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q26 : Eqn
  q26 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q27 : Eqn
  q27 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q28 : Eqn
  q28 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q35 : Eqn
  q35 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q36 : Eqn
  q36 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q37 : Eqn
  q37 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q38 : Eqn
  q38 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) (wn 219 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ Sw01 ∷ []) (wn 319 W)

-- S2 @1203: 227 steps
lem-S2-at1203 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-S2-at1203 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ CS01⁻ ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q2 ∷
   rw 4 q3 ∷
   rw⁻ 3 q2 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q4 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q7 ∷
   rw 5 q3 ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw 2 q5 ∷
   rw 3 q9 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q2 ∷
   rw 2 q8 ∷
   rw⁻ 1 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   re 0 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   rw 4 q7 ∷
   rw 3 q3 ∷
   rw 2 q7 ∷
   rw 1 q8 ∷
   rw 0 q5 ∷
   rw 1 q9 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 5 q10 ∷
   re 4 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw 6 q12 ∷
   rw 4 q13 ∷
   re 5 5 (CS03⁻ ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 10 q14 ∷
   rw 9 q15 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q16 ∷
   rw 7 q10 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q17 ∷
   rw 5 q10 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q15 ∷
   rw 4 q19 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 2 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw 4 q20 ∷
   rw 2 q13 ∷
   re 3 5 (CS03 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 8 q14 ∷
   rw 7 q15 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q16 ∷
   rw 5 q10 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q10 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 2 q18 ∷
   rw 1 q15 ∷
   rw 2 q19 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 2 q21 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q22 ∷
   rw 5 q23 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q24 ∷
   rw 7 q23 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q23 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw⁻ 9 q25 ∷
   rw 10 q26 ∷
   rw⁻ 1 q15 ∷
   rw 2 q27 ∷
   rw 5 q10 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q28 ∷
   rw 7 q10 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw⁻ 8 q20 ∷
   rw 9 q13 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q14 ∷
   rw 1 q1 ∷
   rw 2 q29 ∷
   rw 3 q30 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   rw 6 q31 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q33 ∷
   rw 9 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q35 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   re 3 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 2 q16 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q23 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q23 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q23 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q22 ∷
   rw⁻ 11 q25 ∷
   rw 12 q26 ∷
   rw⁻ 3 q15 ∷
   rw 4 q27 ∷
   rw 7 q10 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q28 ∷
   rw 9 q10 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw⁻ 10 q20 ∷
   rw 11 q13 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q14 ∷
   rw 3 q1 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 7 q32 ∷
   rw 8 q31 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q33 ∷
   rw 11 q2 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q29 ∷
   rw 11 q34 ∷
   rw 4 q35 ∷
   re 4 8 (Toff123 ∷ []) ∷
   re 3 3 (Toff023 ∷ []) ∷
   re 5 1 (Sw12 ∷ CS01⁻ ∷ Sw12 ∷ []) ∷
   rw 4 q16 ∷
   rw 5 q16 ∷
   re 1 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q36 ∷
   rw 2 q30 ∷
   rw 3 q37 ∷
   rw 4 q32 ∷
   rw 5 q37 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q38 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q36 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw 0 q29 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 3 q32 ∷
   rw 4 q31 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q33 ∷
   rw 7 q2 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q29 ∷
   rw 7 q34 ∷
   rw 0 q35 ∷
   re 0 8 (Toff123 ∷ []) ∷
   rw 1 q41 ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q30 ∷
   rw 5 q37 ∷
   rw 6 q32 ∷
   rw 7 q37 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q38 ∷
   rw 10 q2 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q36 ∷
   rw 10 q39 ∷
   rw 11 q40 ∷
   rw 2 q29 ∷
   rw 3 q30 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   rw 6 q31 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q33 ∷
   rw 9 q2 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q35 ∷
   re 2 8 (Toff123 ∷ []) ∷
   rw 3 q42 ∷
   rw 4 q40 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q44 : Eqn
  q44 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wn 398 W)
  q45 : Eqn
  q45 = eqn (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 366 W)
  q46 : Eqn
  q46 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q47 : Eqn
  q47 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q48 : Eqn
  q48 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q49 : Eqn
  q49 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q50 : Eqn
  q50 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q51 : Eqn
  q51 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q52 : Eqn
  q52 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 274 W)
  q53 : Eqn
  q53 = eqn (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) (wn 322 W)
  q54 : Eqn
  q54 = eqn (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) (wn 340 W)
  q55 : Eqn
  q55 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q56 : Eqn
  q56 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 334 W)
  q57 : Eqn
  q57 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q58 : Eqn
  q58 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)

-- S2 @2013: 257 steps
lem-S2-at2013 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-S2-at2013 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ [])
  (rw 4 q10 ∷
   rw 3 q43 ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 9 q14 ∷
   rw 8 q44 ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q16 ∷
   rw 6 q10 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q17 ∷
   rw 4 q10 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 3 q18 ∷
   rw 2 q44 ∷
   rw 3 q45 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q46 ∷
   re 0 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 7 q14 ∷
   rw 6 q44 ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q16 ∷
   rw 4 q10 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 3 q17 ∷
   rw 2 q10 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 1 q18 ∷
   rw 0 q44 ∷
   rw 1 q45 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 5 q1 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q2 ∷
   rw 5 q3 ∷
   rw⁻ 4 q2 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q3 ∷
   rw 5 q7 ∷
   rw 4 q8 ∷
   rw 3 q5 ∷
   rw 4 q9 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 4 q2 ∷
   rw 3 q8 ∷
   rw⁻ 2 q2 ∷
   re 3 3 (CS03 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q3 ∷
   rw 3 q7 ∷
   rw 2 q8 ∷
   rw 1 q5 ∷
   rw 2 q9 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 2 q21 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q22 ∷
   rw 5 q23 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q24 ∷
   rw 7 q23 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q23 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q22 ∷
   rw⁻ 9 q25 ∷
   rw 10 q26 ∷
   rw 1 q29 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q38 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q47 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q48 ∷
   rw 6 q2 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw 5 q47 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q33 ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q29 ∷
   rw 8 q34 ∷
   rw 1 q23 ∷
   rw⁻ 2 q49 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q26 ∷
   rw⁻ 4 q50 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q26 ∷
   rw⁻ 6 q50 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q26 ∷
   rw⁻ 8 q49 ∷
   rw⁻ 9 q51 ∷
   rw 2 q52 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q33 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 7 q23 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q24 ∷
   rw 9 q23 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw 11 q23 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q22 ∷
   rw⁻ 11 q25 ∷
   rw 12 q26 ∷
   rw 3 q29 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q38 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q47 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q48 ∷
   rw 8 q2 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q47 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q33 ∷
   rw 10 q2 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q29 ∷
   rw 10 q34 ∷
   rw 3 q23 ∷
   rw⁻ 4 q49 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q26 ∷
   rw⁻ 6 q50 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q26 ∷
   rw⁻ 8 q50 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q26 ∷
   rw⁻ 10 q49 ∷
   rw⁻ 11 q51 ∷
   rw 4 q52 ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   rw 4 q53 ∷
   rw 5 q40 ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q49 ∷
   rw 4 q23 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q24 ∷
   rw 6 q23 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q23 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q49 ∷
   rw⁻ 8 q25 ∷
   rw 9 q26 ∷
   rw 0 q54 ∷
   rw 1 q27 ∷
   rw 4 q10 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q28 ∷
   rw 6 q10 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 5 q11 ∷
   rw⁻ 7 q20 ∷
   rw 8 q13 ∷
   re 5 5 (CS03 ∷ []) ∷
   rw 6 q54 ∷
   rw⁻ 7 q14 ∷
   rw 0 q1 ∷
   rw 1 q55 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 4 q32 ∷
   rw 5 q31 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q33 ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q55 ∷
   rw 8 q34 ∷
   rw 1 q56 ∷
   re 1 8 (Toff213 ∷ []) ∷
   re 0 3 (Toff203 ∷ []) ∷
   rw 1 q57 ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q49 ∷
   rw 6 q23 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q23 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q24 ∷
   rw 10 q23 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q49 ∷
   rw⁻ 10 q25 ∷
   rw 11 q26 ∷
   rw 2 q54 ∷
   rw 3 q27 ∷
   rw 6 q10 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q28 ∷
   rw 8 q10 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q11 ∷
   rw⁻ 9 q20 ∷
   rw 10 q13 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw 8 q54 ∷
   rw⁻ 9 q14 ∷
   rw 2 q1 ∷
   rw 3 q55 ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   rw 6 q32 ∷
   rw 7 q31 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q2 ∷
   rw 9 q33 ∷
   rw 10 q2 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q55 ∷
   rw 10 q34 ∷
   rw 3 q56 ∷
   re 3 8 (Toff213 ∷ []) ∷
   re 2 3 (Toff203 ∷ []) ∷
   rw 3 q58 ∷
   rw 4 q16 ∷ []) Eq.refl
