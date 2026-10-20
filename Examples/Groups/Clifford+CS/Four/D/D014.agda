{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D014 (W : Ws) where

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
  q2 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q3 : Eqn
  q3 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q6 : Eqn
  q6 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q7 : Eqn
  q7 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q8 : Eqn
  q8 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q9 : Eqn
  q9 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q10 : Eqn
  q10 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q11 : Eqn
  q11 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q12 : Eqn
  q12 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q13 : Eqn
  q13 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q14 : Eqn
  q14 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q15 : Eqn
  q15 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q16 : Eqn
  q16 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q17 : Eqn
  q17 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q18 : Eqn
  q18 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q19 : Eqn
  q19 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q20 : Eqn
  q20 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q21 : Eqn
  q21 = eqn (CK21 ∷ Sw01 ∷ []) (Sw01 ∷ CK20 ∷ []) (wn 273 W)
  q22 : Eqn
  q22 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q23 : Eqn
  q23 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q24 : Eqn
  q24 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q25 : Eqn
  q25 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q26 : Eqn
  q26 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q27 : Eqn
  q27 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q28 : Eqn
  q28 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wn 84 W)
  q29 : Eqn
  q29 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q31 : Eqn
  q31 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q33 : Eqn
  q33 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q34 : Eqn
  q34 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q35 : Eqn
  q35 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q36 : Eqn
  q36 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q37 : Eqn
  q37 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q38 : Eqn
  q38 = eqn (X2 ∷ Sw12 ∷ []) (Sw12 ∷ X1 ∷ []) (wn 215 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q42 : Eqn
  q42 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q44 : Eqn
  q44 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q45 : Eqn
  q45 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q46 : Eqn
  q46 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wn 216 W)
  q47 : Eqn
  q47 = eqn (X1 ∷ Sw01 ∷ []) (Sw01 ∷ X0 ∷ []) (wn 217 W)
  q48 : Eqn
  q48 = eqn (CK10 ∷ Sw01 ∷ []) (Sw01 ∷ CK01 ∷ []) (wn 218 W)
  q49 : Eqn
  q49 = eqn (X0 ∷ CK01 ∷ X0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (ax ck-tct)
  q50 : Eqn
  q50 = eqn (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) (wn 219 W)
  q51 : Eqn
  q51 = eqn (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) (wn 220 W)
  q52 : Eqn
  q52 = eqn (Sw01 ∷ CK01 ∷ []) (CK10 ∷ Sw01 ∷ []) (wn 221 W)
  q53 : Eqn
  q53 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q54 : Eqn
  q54 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q55 : Eqn
  q55 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q56 : Eqn
  q56 = eqn (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) (wn 222 W)
  q57 : Eqn
  q57 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q58 : Eqn
  q58 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q59 : Eqn
  q59 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 274 W)
  q60 : Eqn
  q60 = eqn (Sw01 ∷ CK20 ∷ []) (CK21 ∷ Sw01 ∷ []) (wn 275 W)
  q61 : Eqn
  q61 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q62 : Eqn
  q62 = eqn (X3 ∷ CK31 ∷ X3 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) (wn 276 W)

-- pass [X3 CK31 X3] [TOFF102 CS13 TOFF102 CSd13]: 646 steps
lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CK31 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 6 q1 ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
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
   re 7 8 (Toff102 ∷ []) ∷
   re 6 3 (Toff103 ∷ []) ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
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
   re 5 8 (Toff102 ∷ []) ∷
   re 4 3 (Toff103 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 7 q8 ∷
   re 6 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
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
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q11 ∷
   rw 12 q12 ∷
   rw⁻ 11 q11 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q13 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q11 ∷
   rw 10 q14 ∷
   rw⁻ 9 q11 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw 8 q13 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 8 q15 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q1 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q17 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw⁻ 12 q17 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q5 ∷
   rw⁻ 14 q16 ∷
   rw⁻ 15 q18 ∷
   rw 8 q19 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 7 3 (Toff013 ∷ []) ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
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
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 11 q11 ∷
   rw 10 q12 ∷
   rw⁻ 9 q11 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 8 q13 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q11 ∷
   rw 8 q14 ∷
   rw⁻ 7 q11 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 6 q13 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q11 ∷
   rw 6 q15 ∷
   rw⁻ 5 q11 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 4 q10 ∷
   rw 5 q1 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q17 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q17 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q5 ∷
   rw⁻ 12 q16 ∷
   rw⁻ 13 q18 ∷
   rw 6 q19 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 5 3 (Toff013 ∷ []) ∷
   rw⁻ 3 q20 ∷
   rw 2 q21 ∷
   rw⁻ 1 q20 ∷
   rw 8 q22 ∷
   re 7 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q16 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q16 ∷
   rw⁻ 14 q2 ∷
   rw 15 q5 ∷
   rw 14 q23 ∷
   rw 13 q24 ∷
   re 12 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 15 q25 ∷
   rw 14 q26 ∷
   rw 12 q27 ∷
   re 13 5 (CS03 ∷ []) ∷
   rw 11 q22 ∷
   re 12 3 (CX02 ∷ []) ∷
   rw 10 q28 ∷
   rw 9 q22 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q29 ∷
   rw 7 q24 ∷
   rw 8 q8 ∷
   rw 9 q30 ∷
   rw 10 q31 ∷
   rw 11 q32 ∷
   rw 12 q33 ∷
   rw 13 q32 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q11 ∷
   rw 15 q34 ∷
   rw 16 q11 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 15 q30 ∷
   rw 16 q35 ∷
   rw 9 q36 ∷
   re 9 8 (Toff123 ∷ []) ∷
   re 8 3 (Toff023 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 8 q37 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q16 ∷
   rw⁻ 12 q2 ∷
   rw 13 q5 ∷
   rw 12 q23 ∷
   rw 11 q24 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q25 ∷
   rw 12 q26 ∷
   rw 10 q27 ∷
   re 11 5 (CS03 ∷ []) ∷
   rw 9 q22 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q28 ∷
   rw 7 q22 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q29 ∷
   rw 5 q24 ∷
   rw 6 q8 ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q32 ∷
   rw 10 q33 ∷
   rw 11 q32 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q11 ∷
   rw 13 q34 ∷
   rw 14 q11 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 13 q30 ∷
   rw 14 q35 ∷
   rw 7 q36 ∷
   re 7 8 (Toff123 ∷ []) ∷
   re 6 3 (Toff023 ∷ []) ∷
   rw 4 q38 ∷
   re 3 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 5 q37 ∷
   rw 2 q38 ∷
   rw 9 q8 ∷
   re 8 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 9 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 8 q39 ∷
   rw 9 q31 ∷
   rw 10 q40 ∷
   rw 11 q33 ∷
   rw 12 q40 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q11 ∷
   rw 14 q41 ∷
   rw 15 q11 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q39 ∷
   rw 15 q42 ∷
   rw 16 q43 ∷
   rw 15 q9 ∷
   rw 14 q44 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q11 ∷
   rw 14 q12 ∷
   rw⁻ 13 q11 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 12 q45 ∷
   rw⁻ 11 q33 ∷
   rw 10 q45 ∷
   rw⁻ 9 q31 ∷
   rw 8 q44 ∷
   rw 9 q36 ∷
   re 9 8 (Toff123 ∷ []) ∷
   rw 7 q46 ∷
   re 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q39 ∷
   rw 7 q31 ∷
   rw 8 q40 ∷
   rw 9 q33 ∷
   rw 10 q40 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   rw 12 q41 ∷
   rw 13 q11 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q39 ∷
   rw 13 q42 ∷
   rw 14 q43 ∷
   rw 13 q9 ∷
   rw 12 q44 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 13 q11 ∷
   rw 12 q12 ∷
   rw⁻ 11 q11 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 10 q45 ∷
   rw⁻ 9 q33 ∷
   rw 8 q45 ∷
   rw⁻ 7 q31 ∷
   rw 6 q44 ∷
   rw 7 q36 ∷
   re 7 8 (Toff123 ∷ []) ∷
   rw 5 q47 ∷
   rw 4 q48 ∷
   rw 3 q47 ∷
   rw 4 q49 ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q39 ∷
   rw 4 q31 ∷
   rw 5 q40 ∷
   rw 6 q33 ∷
   rw 7 q40 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q41 ∷
   rw 10 q11 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q39 ∷
   rw 10 q42 ∷
   rw 3 q8 ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   rw 6 q32 ∷
   rw 7 q33 ∷
   rw 8 q32 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q11 ∷
   rw 10 q34 ∷
   rw 11 q11 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q30 ∷
   rw 11 q35 ∷
   rw 4 q36 ∷
   re 4 8 (Toff123 ∷ []) ∷
   re 3 3 (Toff023 ∷ []) ∷
   rw 4 q50 ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q39 ∷
   rw 6 q31 ∷
   rw 7 q40 ∷
   rw 8 q33 ∷
   rw 9 q40 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q41 ∷
   rw 12 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q39 ∷
   rw 12 q42 ∷
   rw 5 q8 ∷
   rw 6 q30 ∷
   rw 7 q31 ∷
   rw 8 q32 ∷
   rw 9 q33 ∷
   rw 10 q32 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q11 ∷
   rw 12 q34 ∷
   rw 13 q11 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q30 ∷
   rw 13 q35 ∷
   rw 6 q36 ∷
   re 6 8 (Toff123 ∷ []) ∷
   re 5 3 (Toff023 ∷ []) ∷
   rw 6 q51 ∷
   rw 7 q52 ∷
   rw 8 q51 ∷
   rw 9 q43 ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q39 ∷
   rw 4 q31 ∷
   rw 5 q40 ∷
   rw 6 q33 ∷
   rw 7 q40 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q41 ∷
   rw 10 q11 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q39 ∷
   rw 10 q42 ∷
   rw 11 q43 ∷
   rw⁻ 2 q24 ∷
   rw 3 q53 ∷
   re 5 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 4 q37 ∷
   rw 5 q54 ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q37 ∷
   re 8 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 7 q25 ∷
   rw⁻ 9 q26 ∷
   rw 10 q27 ∷
   re 7 5 (CS03 ∷ []) ∷
   rw⁻ 8 q24 ∷
   rw⁻ 9 q23 ∷
   rw 2 q1 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q5 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q16 ∷
   rw⁻ 10 q2 ∷
   rw 3 q55 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw 5 q22 ∷
   re 3 3 (CS02 ∷ []) ∷
   re 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q39 ∷
   rw 6 q31 ∷
   rw 7 q40 ∷
   rw 8 q33 ∷
   rw 9 q40 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q11 ∷
   rw 11 q41 ∷
   rw 12 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q39 ∷
   rw 12 q42 ∷
   rw 13 q43 ∷
   rw⁻ 4 q24 ∷
   rw 5 q53 ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q37 ∷
   rw 7 q54 ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q37 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q25 ∷
   rw⁻ 11 q26 ∷
   rw 12 q27 ∷
   re 9 5 (CS03 ∷ []) ∷
   rw⁻ 10 q24 ∷
   rw⁻ 11 q23 ∷
   rw 4 q1 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q5 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 11 q16 ∷
   rw⁻ 12 q2 ∷
   rw 5 q55 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw 5 q56 ∷
   rw 8 q22 ∷
   re 6 3 (CK20 ∷ []) ∷
   rw 7 q56 ∷
   rw 8 q37 ∷
   re 2 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q16 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q16 ∷
   rw⁻ 9 q2 ∷
   rw 10 q5 ∷
   rw 1 q30 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q11 ∷
   rw 3 q41 ∷
   rw 4 q11 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q57 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q11 ∷
   rw 5 q58 ∷
   rw 6 q11 ∷
   re 4 3 (CS03⁻ ∷ []) ∷
   rw 5 q57 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q34 ∷
   rw 8 q11 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q30 ∷
   rw 8 q35 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw⁻ 4 q17 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q17 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q18 ∷
   rw 2 q59 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q34 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q16 ∷
   rw⁻ 11 q2 ∷
   rw 12 q5 ∷
   rw 3 q30 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q11 ∷
   rw 5 q41 ∷
   rw 6 q11 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q57 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q11 ∷
   rw 7 q58 ∷
   rw 8 q11 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q57 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q11 ∷
   rw 9 q34 ∷
   rw 10 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q30 ∷
   rw 10 q35 ∷
   rw 3 q1 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw⁻ 6 q17 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw⁻ 8 q17 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q5 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q18 ∷
   rw 4 q59 ∷
   re 4 8 (Toff102 ∷ []) ∷
   re 3 3 (Toff103 ∷ []) ∷
   rw 4 q20 ∷
   rw 5 q60 ∷
   rw 6 q20 ∷
   rw 7 q43 ∷
   re 1 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
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
   re 0 8 (Toff102 ∷ []) ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
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
   re 2 8 (Toff102 ∷ []) ∷
   rw 3 q61 ∷
   rw 6 q1 ∷
   re 4 3 (CK31 ∷ []) ∷
   rw 5 q61 ∷
   rw 6 q5 ∷
   rw 3 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = eqn (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ []) (Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 277 W)

-- pass [X3 CS31 X3] [TOFF103]: 65 steps
lem-pass-X3-CS31-X3-vs-TOFF103 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff103 ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF103 = derive (X3 ∷ CS13 ∷ X3 ∷ Toff103 ∷ []) (Toff103 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 4 q1 ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
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
   re 4 8 (Toff102 ∷ []) ∷
   rw 2 q7 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q5 ∷
   rw 0 q7 ∷
   rw 1 q63 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
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
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q61 ∷
   rw 4 q1 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw 3 q61 ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (X3 ∷ CS13 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) (wn 234 W)

-- pass [X3 CS31 X3] [CS12]: 1 steps
lem-pass-X3-CS31-X3-vs-CS12 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS12 = derive (X3 ∷ CS13 ∷ X3 ∷ CS12 ∷ []) (CS12 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 0 q64 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = eqn (X3 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) (wn 235 W)

-- pass [X3 CS31 X3] [CSd12]: 1 steps
lem-pass-X3-CS31-X3-vs-CSd12 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-CSd12 = derive (X3 ∷ CS13 ∷ X3 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 0 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = eqn (CS02 ∷ X3 ∷ []) (X3 ∷ CS02 ∷ []) (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q67 : Eqn
  q67 = eqn (CS01 ∷ CS23 ∷ []) (CS23 ∷ CS01 ∷ []) (low-comm (CS) (CS))
  q68 : Eqn
  q68 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)

-- pass [X3 CS31 X3] [CS02]: 7 steps
lem-pass-X3-CS31-X3-vs-CS02 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS02 = derive (X3 ∷ CS13 ∷ X3 ∷ CS02 ∷ []) (CS02 ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw⁻ 2 q66 ∷
   re 2 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 1 q29 ∷
   rw⁻ 2 q67 ∷
   rw 3 q68 ∷
   re 1 3 (CS02 ∷ []) ∷
   rw⁻ 0 q66 ∷ []) Eq.refl
