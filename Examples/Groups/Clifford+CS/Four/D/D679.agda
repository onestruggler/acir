{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD679 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D679 (W : Ws) (Sᴰ : SD679) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-S2 : St 1778
  lem-S2 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q2 : Eqn
  q2 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q3 : Eqn
  q3 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q5 : Eqn
  q5 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q6 : Eqn
  q6 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q7 : Eqn
  q7 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q8 : Eqn
  q8 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q9 : Eqn
  q9 = eqn (K2 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 333 W)
  q10 : Eqn
  q10 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q11 : Eqn
  q11 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q12 : Eqn
  q12 = eqn (CS23⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS13⁻ ∷ []) (wn 47 W)
  q13 : Eqn
  q13 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q14 : Eqn
  q14 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wn 398 W)
  q15 : Eqn
  q15 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q16 : Eqn
  q16 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q17 : Eqn
  q17 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q18 : Eqn
  q18 = eqn (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 366 W)
  q19 : Eqn
  q19 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q22 : Eqn
  q22 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q23 : Eqn
  q23 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff013 ∷ CS02 ∷ Toff013 ∷ CS02⁻ ∷ []) (lem-S2)
  q24 : Eqn
  q24 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q25 : Eqn
  q25 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q26 : Eqn
  q26 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q28 : Eqn
  q28 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q29 : Eqn
  q29 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q34 : Eqn
  q34 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q35 : Eqn
  q35 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q36 : Eqn
  q36 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q37 : Eqn
  q37 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q38 : Eqn
  q38 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 274 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ CS02⁻ ∷ []) (CS12⁻ ∷ Sw01 ∷ []) (wn 322 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q41 : Eqn
  q41 = eqn (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) (wn 340 W)
  q42 : Eqn
  q42 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q43 : Eqn
  q43 = eqn (Sw12 ∷ CS13⁻ ∷ []) (CS23⁻ ∷ Sw12 ∷ []) (wn 21 W)
  q44 : Eqn
  q44 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q45 : Eqn
  q45 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q46 : Eqn
  q46 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q47 : Eqn
  q47 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q48 : Eqn
  q48 = eqn (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) (wn 334 W)
  q49 : Eqn
  q49 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q50 : Eqn
  q50 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q51 : Eqn
  q51 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q52 : Eqn
  q52 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)

-- S2 @2103: 343 steps
lem-S2-at2103 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-S2-at2103 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff213 ∷ CS02 ∷ Toff213 ∷ CS02⁻ ∷ [])
  (rw 4 q1 ∷
   rw⁻ 3 q2 ∷
   re 2 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 9 q3 ∷
   rw⁻ 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw⁻ 2 q4 ∷
   rw 3 q9 ∷
   re 3 8 (Toff201 ∷ []) ∷
   rw⁻ 1 q10 ∷
   re 0 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 7 q3 ∷
   rw⁻ 6 q4 ∷
   rw 5 q5 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   rw 2 q6 ∷
   rw 1 q8 ∷
   rw⁻ 0 q4 ∷
   rw 1 q9 ∷
   re 1 8 (Toff201 ∷ []) ∷
   rw 5 q11 ∷
   rw 4 q12 ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 10 q13 ∷
   rw 9 q14 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q15 ∷
   rw 7 q11 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q11 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q14 ∷
   rw 4 q18 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q19 ∷
   re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 8 q13 ∷
   rw 7 q14 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q15 ∷
   rw 5 q11 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q11 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q14 ∷
   rw 2 q18 ∷
   re 2 8 (Toff102 ∷ []) ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q20 ∷
   rw 6 q7 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q3 ∷
   rw 10 q21 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q20 ∷
   rw 4 q8 ∷
   rw⁻ 3 q20 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q3 ∷
   rw 8 q21 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 3 q23 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q24 ∷
   rw 6 q25 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q25 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q26 ∷
   rw 10 q25 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q27 ∷
   rw 11 q28 ∷
   rw 2 q29 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q30 ∷
   rw 5 q20 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q31 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q32 ∷
   rw 7 q20 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q31 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q25 ∷
   rw⁻ 3 q35 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q28 ∷
   rw⁻ 5 q36 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q28 ∷
   rw⁻ 9 q35 ∷
   rw⁻ 10 q37 ∷
   rw 3 q38 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw 3 q33 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q25 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q26 ∷
   rw 10 q25 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q26 ∷
   rw 12 q25 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q27 ∷
   rw 13 q28 ∷
   rw 4 q29 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q30 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q31 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q32 ∷
   rw 9 q20 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q31 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q20 ∷
   rw 10 q33 ∷
   rw 11 q20 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q29 ∷
   rw 11 q34 ∷
   rw 4 q25 ∷
   rw⁻ 5 q35 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q28 ∷
   rw⁻ 9 q36 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q28 ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q37 ∷
   rw 5 q38 ∷
   re 5 8 (Toff102 ∷ []) ∷
   re 4 3 (Toff103 ∷ []) ∷
   rw 5 q39 ∷
   rw 6 q40 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 5 q25 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q25 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q35 ∷
   rw⁻ 9 q27 ∷
   rw 10 q28 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 5 q11 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q43 ∷
   rw 7 q11 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q44 ∷
   rw⁻ 8 q45 ∷
   rw 9 q46 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 7 q41 ∷
   rw⁻ 8 q13 ∷
   rw 1 q1 ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 4 q47 ∷
   rw 5 q2 ∷
   rw 6 q47 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q34 ∷
   rw 2 q48 ∷
   re 2 8 (Toff213 ∷ []) ∷
   re 1 3 (Toff203 ∷ []) ∷
   rw 2 q49 ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q35 ∷
   rw 7 q25 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q25 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q35 ∷
   rw⁻ 11 q27 ∷
   rw 12 q28 ∷
   rw 3 q41 ∷
   rw 4 q42 ∷
   rw 7 q11 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q43 ∷
   rw 9 q11 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q44 ∷
   rw⁻ 10 q45 ∷
   rw 11 q46 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 9 q41 ∷
   rw⁻ 10 q13 ∷
   rw 3 q1 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   rw 6 q47 ∷
   rw 7 q2 ∷
   rw 8 q47 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q20 ∷
   rw 10 q33 ∷
   rw 11 q20 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q4 ∷
   rw 11 q34 ∷
   rw 4 q48 ∷
   re 4 8 (Toff213 ∷ []) ∷
   re 3 3 (Toff203 ∷ []) ∷
   rw 4 q50 ∷
   rw 5 q15 ∷
   re 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 1 q4 ∷
   rw 2 q10 ∷
   rw 3 q51 ∷
   rw 4 q2 ∷
   rw 5 q51 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q20 ∷
   rw 7 q30 ∷
   rw 8 q20 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q52 ∷
   rw 9 q40 ∷
   rw 0 q4 ∷
   rw 1 q10 ∷
   rw 2 q47 ∷
   rw 3 q2 ∷
   rw 4 q47 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q33 ∷
   rw 7 q20 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q34 ∷
   rw 0 q48 ∷
   re 0 8 (Toff213 ∷ []) ∷
   rw 1 q30 ∷
   re 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   rw 5 q51 ∷
   rw 6 q2 ∷
   rw 7 q51 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q20 ∷
   rw 9 q30 ∷
   rw 10 q20 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q4 ∷
   rw 10 q52 ∷
   rw 11 q40 ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 4 q47 ∷
   rw 5 q2 ∷
   rw 6 q47 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q34 ∷
   rw 2 q48 ∷
   re 2 8 (Toff213 ∷ []) ∷
   rw 3 q32 ∷
   rw 4 q40 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (CS23⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS23⁻ ∷ []) (wn 1882 W)
  q54 : Eqn
  q54 = eqn (Sw23 ∷ K2 ∷ []) (K3 ∷ Sw23 ∷ []) (wn 335 W)
  q55 : Eqn
  q55 = eqn (K3 ∷ Sw23 ∷ []) (Sw23 ∷ K2 ∷ []) (wn 1294 W)
  q56 : Eqn
  q56 = eqn (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 368 W)
  q57 : Eqn
  q57 = eqn (CS23 ∷ Sw23 ∷ []) (Sw23 ∷ CS23 ∷ []) (wn 1883 W)
  q58 : Eqn
  q58 = eqn (Sw23 ∷ CS23 ∷ []) (CS23 ∷ Sw23 ∷ []) (wn 71 W)
  q59 : Eqn
  q59 = eqn (Sw23 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw23 ∷ []) (wn 72 W)
  q60 : Eqn
  q60 = eqn (Sw01 ∷ K3 ∷ []) (K3 ∷ Sw01 ∷ []) (low-comm (Swap) ((K ↑)))
  q61 : Eqn
  q61 = eqn (K3 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ K3 ∷ ι1 ∷ []) (K3 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K3 ∷ ι1 ∷ []) (wn 385 W)

-- S2 @3012: 411 steps
lem-S2-at3012 : ⟪ (Toff301 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-S2-at3012 = derive (Toff301 ∷ CS23 ∷ Toff301 ∷ CS23⁻ ∷ []) (Toff302 ∷ CS13 ∷ Toff302 ∷ CS13⁻ ∷ [])
  (rw 4 q25 ∷
   rw 3 q53 ∷
   re 2 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 2 q54 ∷
   rw 5 q25 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q25 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q54 ∷
   rw⁻ 9 q27 ∷
   rw 10 q28 ∷
   rw 9 q27 ∷
   rw 8 q55 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q28 ∷
   rw 6 q26 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw 4 q26 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   rw 2 q55 ∷
   rw 3 q56 ∷
   re 3 8 (Toff201 ∷ []) ∷
   rw 1 q57 ∷
   re 0 1 (Sw23 ∷ Toff201 ∷ Sw23 ∷ []) ∷
   re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 0 q54 ∷
   rw 3 q25 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q26 ∷
   rw 5 q25 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q25 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q54 ∷
   rw⁻ 7 q27 ∷
   rw 8 q28 ∷
   rw 7 q27 ∷
   rw 6 q55 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw 4 q26 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   rw 2 q26 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q55 ∷
   rw 1 q56 ∷
   re 1 8 (Toff201 ∷ []) ∷
   rw 5 q11 ∷
   rw 4 q12 ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 10 q13 ∷
   rw 9 q14 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q15 ∷
   rw 7 q11 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q16 ∷
   rw 5 q11 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q14 ∷
   rw 4 q18 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q19 ∷
   re 1 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 8 q13 ∷
   rw 7 q14 ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q15 ∷
   rw 5 q11 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q16 ∷
   rw 3 q11 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 2 q17 ∷
   rw 1 q14 ∷
   rw 2 q18 ∷
   re 2 8 (Toff102 ∷ []) ∷
   rw 6 q1 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q20 ∷
   rw 6 q7 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q3 ∷
   rw 10 q21 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q20 ∷
   rw 4 q8 ∷
   rw⁻ 3 q20 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 9 q3 ∷
   rw 8 q21 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   re 3 8 (Toff012 ∷ []) ∷
   rw 3 q23 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q24 ∷
   rw 6 q25 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q25 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q26 ∷
   rw 10 q25 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q24 ∷
   rw⁻ 10 q27 ∷
   rw 11 q28 ∷
   rw 2 q29 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q30 ∷
   rw 5 q20 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q31 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q32 ∷
   rw 7 q20 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q31 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q25 ∷
   rw⁻ 3 q35 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q28 ∷
   rw⁻ 5 q36 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q28 ∷
   rw⁻ 9 q35 ∷
   rw⁻ 10 q37 ∷
   rw 3 q38 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw 3 q33 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q24 ∷
   rw 8 q25 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q26 ∷
   rw 10 q25 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q26 ∷
   rw 12 q25 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q24 ∷
   rw⁻ 12 q27 ∷
   rw 13 q28 ∷
   rw 4 q29 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q30 ∷
   rw 7 q20 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q31 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q32 ∷
   rw 9 q20 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q31 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q20 ∷
   rw 10 q33 ∷
   rw 11 q20 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q29 ∷
   rw 11 q34 ∷
   rw 4 q25 ∷
   rw⁻ 5 q35 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q28 ∷
   rw⁻ 9 q36 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q28 ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q37 ∷
   rw 5 q38 ∷
   re 5 8 (Toff102 ∷ []) ∷
   re 4 3 (Toff103 ∷ []) ∷
   rw 5 q39 ∷
   rw 6 q40 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q35 ∷
   rw 5 q25 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q25 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q35 ∷
   rw⁻ 9 q27 ∷
   rw 10 q28 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 5 q11 ∷
   re 3 3 (CX02 ∷ []) ∷
   rw 4 q43 ∷
   rw 7 q11 ∷
   re 5 3 (CX02 ∷ []) ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q44 ∷
   rw⁻ 8 q45 ∷
   rw 9 q46 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw 7 q41 ∷
   rw⁻ 8 q13 ∷
   rw 1 q1 ∷
   rw 2 q4 ∷
   rw 3 q10 ∷
   rw 4 q47 ∷
   rw 5 q2 ∷
   rw 6 q47 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q33 ∷
   rw 9 q20 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q34 ∷
   rw 2 q48 ∷
   re 2 8 (Toff213 ∷ []) ∷
   re 1 3 (Toff203 ∷ []) ∷
   rw 2 q49 ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q35 ∷
   rw 7 q25 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q25 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q25 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q35 ∷
   rw⁻ 11 q27 ∷
   rw 12 q28 ∷
   rw 3 q41 ∷
   rw 4 q42 ∷
   rw 7 q11 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q43 ∷
   rw 9 q11 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q44 ∷
   rw⁻ 10 q45 ∷
   rw 11 q46 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 9 q41 ∷
   rw⁻ 10 q13 ∷
   rw 3 q1 ∷
   rw 4 q4 ∷
   rw 5 q10 ∷
   rw 6 q47 ∷
   rw 7 q2 ∷
   rw 8 q47 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q20 ∷
   rw 10 q33 ∷
   rw 11 q20 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q4 ∷
   rw 11 q34 ∷
   rw 4 q48 ∷
   re 4 8 (Toff213 ∷ []) ∷
   re 3 3 (Toff203 ∷ []) ∷
   rw 4 q50 ∷
   rw 5 q15 ∷
   re 1 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 2 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 1 q4 ∷
   rw 2 q10 ∷
   rw 3 q51 ∷
   rw 4 q2 ∷
   rw 5 q51 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q20 ∷
   rw 7 q30 ∷
   rw 8 q20 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q52 ∷
   rw 9 q40 ∷
   rw 0 q54 ∷
   rw 1 q58 ∷
   rw 4 q25 ∷
   re 2 3 (CX03 ∷ []) ∷
   rw 3 q59 ∷
   rw 6 q25 ∷
   re 4 3 (CX03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   rw 6 q54 ∷
   rw⁻ 7 q27 ∷
   rw 0 q1 ∷
   rw 1 q60 ∷
   rw 2 q10 ∷
   re 4 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 3 q20 ∷
   rw 4 q47 ∷
   rw 5 q20 ∷
   re 3 3 (CX13 ∷ []) ∷
   rw 4 q2 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q47 ∷
   rw 7 q20 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q33 ∷
   rw 7 q60 ∷
   rw 8 q34 ∷
   rw 1 q61 ∷
   re 1 8 (Toff312 ∷ []) ∷
   re 0 3 (Toff302 ∷ []) ∷
   rw 3 q25 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (Sw01 ∷ Toff213 ∷ Sw01 ∷ []) ∷
   re 4 1 (K2 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K2 ∷ ι1 ∷ []) ∷
   rw 3 q4 ∷
   rw 4 q10 ∷
   rw 5 q51 ∷
   rw 6 q2 ∷
   rw 7 q51 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q20 ∷
   rw 9 q30 ∷
   rw 10 q20 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q4 ∷
   rw 10 q52 ∷
   rw 11 q40 ∷
   rw 2 q54 ∷
   rw 3 q58 ∷
   rw 6 q25 ∷
   re 4 3 (CX03 ∷ []) ∷
   rw 5 q59 ∷
   rw 8 q25 ∷
   re 6 3 (CX03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw 8 q54 ∷
   rw⁻ 9 q27 ∷
   rw 2 q1 ∷
   rw 3 q60 ∷
   rw 4 q10 ∷
   re 6 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q47 ∷
   rw 7 q20 ∷
   re 5 3 (CX13 ∷ []) ∷
   rw 6 q2 ∷
   re 8 1 (Sw23 ∷ CX02 ∷ Sw23 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q47 ∷
   rw 9 q20 ∷
   re 7 3 (CX13 ∷ []) ∷
   rw 8 q33 ∷
   rw 9 q60 ∷
   rw 10 q34 ∷
   rw 3 q61 ∷
   re 3 8 (Toff312 ∷ []) ∷
   re 2 3 (Toff302 ∷ []) ∷
   rw 5 q25 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw 4 q28 ∷ []) Eq.refl
