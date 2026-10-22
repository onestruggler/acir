{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D010 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 56 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 12 W
  q9 : Eqn
  q9 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q10 : Eqn
  q10 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q11 : Eqn
  q11 = wE 22 W
  q12 : Eqn
  q12 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q13 : Eqn
  q13 = wE 23 W
  q14 : Eqn
  q14 = wE 84 W
  q15 : Eqn
  q15 = wE 65 W
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = wE 123 W
  q18 : Eqn
  q18 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q19 : Eqn
  q19 = wE 24 W
  q20 : Eqn
  q20 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q21 : Eqn
  q21 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 25 W
  q23 : Eqn
  q23 = wE 124 W
  q24 : Eqn
  q24 = wE 125 W
  q25 : Eqn
  q25 = wE 14 W
  q26 : Eqn
  q26 = wE 215 W
  q27 : Eqn
  q27 = wE 121 W
  q28 : Eqn
  q28 = wE 30 W
  q29 : Eqn
  q29 = wE 27 W
  q30 : Eqn
  q30 = wE 122 W
  q31 : Eqn
  q31 = wE 31 W
  q32 : Eqn
  q32 = wE 127 W
  q33 : Eqn
  q33 = wE 118 W
  q34 : Eqn
  q34 = wE 7 W
  q35 : Eqn
  q35 = wE 74 W
  q36 : Eqn
  q36 = wE 216 W
  q37 : Eqn
  q37 = wE 217 W
  q38 : Eqn
  q38 = wE 218 W
  q39 : Eqn
  q39 = eqn (X0 ∷ CK01 ∷ X0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (ax ck-tct)
  q40 : Eqn
  q40 = wE 219 W
  q41 : Eqn
  q41 = wE 220 W
  q42 : Eqn
  q42 = wE 221 W
  q43 : Eqn
  q43 = wE 49 W
  q44 : Eqn
  q44 = wE 51 W
  q45 : Eqn
  q45 = wE 222 W
  q46 : Eqn
  q46 = wE 175 W
  q47 : Eqn
  q47 = wE 223 W

-- pass [X3 CK30 X3] [TOFF012 CS03 TOFF012 CSd03]: 454 steps
lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CK30 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK30 ∷ X3 ∷ [])
  (rw 6 q1 ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 12 q2 ∷
   rw 11 q3 ∷
   rw 10 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 9 q4 ∷
   rw 8 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw 7 q4 ∷
   rw 6 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q2 ∷
   rw 7 q6 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   rw 8 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 7 q4 ∷
   rw 6 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw 5 q4 ∷
   rw 4 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 3 q3 ∷
   rw 4 q1 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q2 ∷
   rw 5 q6 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 7 q8 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q2 ∷
   rw 14 q5 ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   rw 13 q12 ∷
   rw 11 q13 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 10 q8 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q14 ∷
   rw 8 q8 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q15 ∷
   rw 6 q10 ∷
   rw 7 q16 ∷
   rw 8 q17 ∷
   rw 9 q18 ∷
   rw 10 q19 ∷
   rw 11 q20 ∷
   rw 12 q19 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q21 ∷
   rw 14 q22 ∷
   rw 15 q21 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 14 q17 ∷
   rw 15 q23 ∷
   rw 8 q24 ∷
   re 8 8 (Toff123 ∷ []) ∷
   re 7 3 (Toff023 ∷ []) ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q25 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q2 ∷
   rw 12 q5 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   rw 11 q12 ∷
   rw 9 q13 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 8 q8 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q14 ∷
   rw 6 q8 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q15 ∷
   rw 4 q10 ∷
   rw 5 q16 ∷
   rw 6 q17 ∷
   rw 7 q18 ∷
   rw 8 q19 ∷
   rw 9 q20 ∷
   rw 10 q19 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 12 q22 ∷
   rw 13 q21 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q17 ∷
   rw 13 q23 ∷
   rw 6 q24 ∷
   re 6 8 (Toff123 ∷ []) ∷
   re 5 3 (Toff023 ∷ []) ∷
   rw 3 q26 ∷
   re 2 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 4 q25 ∷
   rw 1 q26 ∷
   rw 8 q16 ∷
   re 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q27 ∷
   rw 8 q18 ∷
   rw 9 q28 ∷
   rw 10 q20 ∷
   rw 11 q28 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   rw 13 q29 ∷
   rw 14 q21 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q27 ∷
   rw 14 q30 ∷
   rw 15 q31 ∷
   rw 14 q32 ∷
   rw 13 q33 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q21 ∷
   rw 13 q34 ∷
   rw⁻ 12 q21 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q35 ∷
   rw⁻ 10 q20 ∷
   rw 9 q35 ∷
   rw⁻ 8 q18 ∷
   rw 7 q33 ∷
   rw 8 q24 ∷
   re 8 8 (Toff123 ∷ []) ∷
   rw 6 q36 ∷
   re 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q27 ∷
   rw 6 q18 ∷
   rw 7 q28 ∷
   rw 8 q20 ∷
   rw 9 q28 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 11 q29 ∷
   rw 12 q21 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q27 ∷
   rw 12 q30 ∷
   rw 13 q31 ∷
   rw 12 q32 ∷
   rw 11 q33 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q21 ∷
   rw 11 q34 ∷
   rw⁻ 10 q21 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q35 ∷
   rw⁻ 8 q20 ∷
   rw 7 q35 ∷
   rw⁻ 6 q18 ∷
   rw 5 q33 ∷
   rw 6 q24 ∷
   re 6 8 (Toff123 ∷ []) ∷
   rw 4 q37 ∷
   rw 3 q38 ∷
   rw 2 q37 ∷
   rw 3 q39 ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q27 ∷
   rw 3 q18 ∷
   rw 4 q28 ∷
   rw 5 q20 ∷
   rw 6 q28 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q29 ∷
   rw 9 q21 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q27 ∷
   rw 9 q30 ∷
   rw 2 q16 ∷
   rw 3 q17 ∷
   rw 4 q18 ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 7 q19 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q21 ∷
   rw 9 q22 ∷
   rw 10 q21 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q17 ∷
   rw 10 q23 ∷
   rw 3 q24 ∷
   re 3 8 (Toff123 ∷ []) ∷
   re 2 3 (Toff023 ∷ []) ∷
   rw 3 q40 ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q27 ∷
   rw 5 q18 ∷
   rw 6 q28 ∷
   rw 7 q20 ∷
   rw 8 q28 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q29 ∷
   rw 11 q21 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q27 ∷
   rw 11 q30 ∷
   rw 4 q16 ∷
   rw 5 q17 ∷
   rw 6 q18 ∷
   rw 7 q19 ∷
   rw 8 q20 ∷
   rw 9 q19 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 11 q22 ∷
   rw 12 q21 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q17 ∷
   rw 12 q23 ∷
   rw 5 q24 ∷
   re 5 8 (Toff123 ∷ []) ∷
   re 4 3 (Toff023 ∷ []) ∷
   rw 5 q41 ∷
   rw 6 q42 ∷
   rw 7 q41 ∷
   rw 8 q31 ∷
   re 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q27 ∷
   rw 3 q18 ∷
   rw 4 q28 ∷
   rw 5 q20 ∷
   rw 6 q28 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q29 ∷
   rw 9 q21 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q27 ∷
   rw 9 q30 ∷
   rw 10 q31 ∷
   rw⁻ 1 q10 ∷
   rw 2 q43 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 q25 ∷
   rw 4 q44 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q25 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw⁻ 8 q12 ∷
   rw 9 q13 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw⁻ 7 q10 ∷
   rw⁻ 8 q9 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q2 ∷
   rw 2 q6 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 4 q8 ∷
   re 2 3 (CS02 ∷ []) ∷
   re 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q27 ∷
   rw 5 q18 ∷
   rw 6 q28 ∷
   rw 7 q20 ∷
   rw 8 q28 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q29 ∷
   rw 11 q21 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q27 ∷
   rw 11 q30 ∷
   rw 12 q31 ∷
   rw⁻ 3 q10 ∷
   rw 4 q43 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q25 ∷
   rw 6 q44 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q25 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw⁻ 10 q12 ∷
   rw 11 q13 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw⁻ 9 q10 ∷
   rw⁻ 10 q9 ∷
   rw 3 q1 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q2 ∷
   rw 4 q6 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 4 q45 ∷
   rw 7 q8 ∷
   re 5 3 (CK20 ∷ []) ∷
   rw 6 q45 ∷
   rw 7 q25 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q2 ∷
   rw 9 q5 ∷
   rw⁻ 0 q3 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q2 ∷
   rw 0 q6 ∷
   re 0 8 (Toff012 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q2 ∷
   rw 11 q5 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q2 ∷
   rw 2 q6 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 3 q46 ∷
   rw 6 q1 ∷
   re 4 3 (CK30 ∷ []) ∷
   rw 5 q46 ∷
   rw 6 q5 ∷
   rw 7 q1 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q7 ∷
   re 4 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q7 ∷
   rw 4 q47 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q46 ∷
   rw 7 q1 ∷
   re 5 3 (CK30 ∷ []) ∷
   rw 6 q46 ∷
   rw 7 q5 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (K0 ∷ X3 ∷ []) (X3 ∷ K0 ∷ []) (low₁-comm (K) ((X ↑ ↑)))
  q49 : Eqn
  q49 = wE 54 W
  q50 : Eqn
  q50 = eqn (K0⁻ ∷ X3 ∷ []) (X3 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((X ↑ ↑)))
  q51 : Eqn
  q51 = wE 224 W
  q52 : Eqn
  q52 = eqn (CCZ012 ∷ X3 ∷ []) (X3 ∷ CCZ012 ∷ []) (low₃-comm (CCZ) (X))
  q53 : Eqn
  q53 = wE 225 W

-- K0-PPw3-Kd0: 10 steps
lem-K0-PPw3-Kd0 : ⟪ (K0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ []) ⟫ʷ
lem-K0-PPw3-Kd0 = derive (K0 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ K0⁻ ∷ []) (CCZ012 ∷ X3 ∷ K0 ∷ CS03 ∷ K0⁻ ∷ X3 ∷ CCZ012 ∷ X3 ∷ K0 ∷ CS03⁻ ∷ K0⁻ ∷ X3 ∷ [])
  (rw 0 q48 ∷
   rw 5 q49 ∷
   rw 4 q49 ∷
   rw 3 q49 ∷
   rw⁻ 12 q50 ∷
   rw 1 q51 ∷
   rw 5 q51 ∷
   rw⁻ 0 q52 ∷
   rw 5 q53 ∷
   rw⁻ 6 q52 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 226 W
  q55 : Eqn
  q55 = wE 227 W
  q56 : Eqn
  q56 = wE 45 W
  q57 : Eqn
  q57 = wE 228 W

-- D-b: 4 steps
lem-D-b : ⟪ (CCZ012 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ CCZ012 ∷ []) ⟫ʷ
lem-D-b = derive (CCZ012 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ CCZ012 ∷ [])
  (rw 0 q54 ∷
   rw 1 q55 ∷
   rw 4 q56 ∷
   rw 5 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = wE 229 W

-- pass [CS12] [Kd0]: 1 steps
lem-pass-CS12-vs-Kd0 : ⟪ (CS12 ∷ K0⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-Kd0 = derive (CS12 ∷ K0⁻ ∷ []) (K0⁻ ∷ CS12 ∷ [])
  (rw 0 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 90 W

-- pass [CS12] [TOFF012]: 1 steps
lem-pass-CS12-vs-TOFF012 : ⟪ (CS12 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-TOFF012 = derive (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ [])
  (rw 0 q59 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (CS01⁻ ∷ CS23 ∷ []) (CS23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (CS))
  q61 : Eqn
  q61 = wE 48 W

-- pass [CS12] [CSd03]: 9 steps
lem-pass-CS12-vs-CSd03 : ⟪ (CS12 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CSd03 = derive (CS12 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS12 ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw 1 q15 ∷
   rw⁻ 2 q60 ∷
   rw 3 q61 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   re 0 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 230 W

-- pass [CS12] [K0]: 1 steps
lem-pass-CS12-vs-K0 : ⟪ (CS12 ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-K0 = derive (CS12 ∷ K0 ∷ []) (K0 ∷ CS12 ∷ [])
  (rw 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 231 W

-- cocycle S|KdSKS: 8 steps
lem-cocycle-S∣KdSKS : ⟪ (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-cocycle-S∣KdSKS = derive (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ [])
  (rw 2 q56 ∷
   rw 3 q1 ∷
   rw 4 q63 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 232 W

-- cocycle KdSK|S: 16 steps
lem-cocycle-KdSK∣S : ⟪ (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) ⟫ʷ
lem-cocycle-KdSK∣S = derive (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ [])
  (rw 4 q56 ∷
   rw 5 q1 ∷
   rw 6 q64 ∷
   rw 7 q1 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 12 q1 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q5 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 233 W

-- pass [X3 CS30 X3] [TOFF013]: 65 steps
lem-pass-X3-CS30-X3-vs-TOFF013 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF013 = derive (X3 ∷ CS03 ∷ X3 ∷ Toff013 ∷ []) (Toff013 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q2 ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 3 q3 ∷
   rw 4 q6 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q65 ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q2 ∷
   rw 0 q1 ∷
   rw⁻ 1 q3 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q2 ∷
   rw 1 q6 ∷
   re 1 8 (Toff012 ∷ []) ∷
   re 0 3 (Toff013 ∷ []) ∷
   rw 1 q46 ∷
   rw 4 q1 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q46 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q67 : Eqn
  q67 = wE 234 W

-- pass [X3 CS30 X3] [CS02]: 19 steps
lem-pass-X3-CS30-X3-vs-CS02 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS02 = derive (X3 ∷ CS03 ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q16 ∷
   rw 3 q34 ∷
   rw⁻ 2 q66 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q21 ∷
   rw 2 q34 ∷
   rw⁻ 1 q21 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q66 ∷
   rw 1 q67 ∷
   rw 0 q29 ∷
   rw 1 q66 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q29 ∷
   rw 4 q21 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q66 ∷
   rw 4 q31 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 76 W
  q69 : Eqn
  q69 = wE 235 W
  q70 : Eqn
  q70 = wE 29 W

-- pass [X3 CS30 X3] [CSd02]: 19 steps
lem-pass-X3-CS30-X3-vs-CSd02 : ⟪ (X3 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS30-X3-vs-CSd02 = derive (X3 ∷ CS03 ∷ X3 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ X3 ∷ CS03 ∷ X3 ∷ [])
  (rw 4 q16 ∷
   rw 3 q68 ∷
   rw⁻ 2 q66 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q21 ∷
   rw 2 q34 ∷
   rw⁻ 1 q21 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q66 ∷
   rw 1 q69 ∷
   rw 0 q70 ∷
   rw 1 q66 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q21 ∷
   rw 3 q29 ∷
   rw 4 q21 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q66 ∷
   rw 4 q31 ∷ []) Eq.refl

-- cocycle KdSK|SKdSK: 16 steps
lem-cocycle-KdSK∣SKdSK : ⟪ (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) ⟫ʷ
lem-cocycle-KdSK∣SKdSK = derive (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ [])
  (rw 4 q56 ∷
   rw 5 q1 ∷
   rw 6 q64 ∷
   rw 7 q1 ∷
   re 5 3 (CK30⁻ ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CK30⁻ ∷ []) ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 12 q1 ∷
   re 10 3 (CK30 ∷ []) ∷
   rw 11 q5 ∷ []) Eq.refl

-- cocycle S|KdSK: 8 steps
lem-cocycle-S∣KdSK : ⟪ (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-cocycle-S∣KdSK = derive (Toff012 ∷ CS03 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS03 ∷ Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ CS03⁻ ∷ [])
  (rw 2 q56 ∷
   rw 3 q1 ∷
   rw 4 q63 ∷
   rw 5 q1 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q5 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 43 W
  q72 : Eqn
  q72 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q73 : Eqn
  q73 = wE 236 W

-- pass [Sd0] [CCZ013]: 47 steps
lem-pass-Sd0-vs-CCZ013 : ⟪ (S0⁻ ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CCZ013 = derive (S0⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ S0⁻ ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
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
   rw 2 q71 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 0 q72 ∷
   rw 1 q73 ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q1 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 0 q1 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 1 q71 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 0 3 (CCZ013 ∷ []) ∷
   rw⁻ 1 q72 ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = eqn (CS01⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q75 : Eqn
  q75 = wE 47 W

-- pass [CSd12] [CSd03]: 9 steps
lem-pass-CSd12-vs-CSd03 : ⟪ (CS12⁻ ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-CSd12-vs-CSd03 = derive (CS12⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS12⁻ ∷ [])
  (re 1 1 (Sw23 ∷ Sw12 ∷ CS01⁻ ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 0 q1 ∷
   re 1 3 (CS13⁻ ∷ []) ∷
   rw 1 q14 ∷
   rw⁻ 2 q74 ∷
   rw 3 q75 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   re 0 5 (CS03⁻ ∷ []) ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q77 : Eqn
  q77 = wE 237 W

-- pass [S0] [CCZ013]: 47 steps
lem-pass-S0-vs-CCZ013 : ⟪ (S0 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CCZ013 = derive (S0 ∷ CCZ013 ∷ []) (CCZ013 ∷ S0 ∷ [])
  (rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
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
   rw 2 q71 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 0 q76 ∷
   rw 1 q77 ∷
   re 1 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 2 q1 ∷
   re 0 3 (CS13 ∷ []) ∷
   rw⁻ 1 q4 ∷
   rw 4 q1 ∷
   re 2 3 (CS13⁻ ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 0 q1 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q5 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 1 q71 ∷
   re 1 5 (CCZ012 ∷ []) ∷
   re 0 3 (CCZ013 ∷ []) ∷
   rw⁻ 1 q76 ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = eqn (S0 ∷ CCZ123 ∷ []) (CCZ123 ∷ S0 ∷ []) (low₁-comm (S) (CCZ))

-- pass [S0] [CCZ123]: 1 steps
lem-pass-S0-vs-CCZ123 : ⟪ (S0 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CCZ123 = derive (S0 ∷ CCZ123 ∷ []) (CCZ123 ∷ S0 ∷ [])
  (rw 0 q78 ∷ []) Eq.refl
