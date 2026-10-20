{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D020 (W : Ws) where

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
  q1 = eqn [] (Sw12 ∷ Sw12 ∷ []) (wn 12 W)
  q2 : Eqn
  q2 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q3 : Eqn
  q3 = eqn (K2 ∷ Sw12 ∷ []) (Sw12 ∷ K1 ∷ []) (wn 398 W)
  q4 : Eqn
  q4 = eqn (Sw12 ∷ Sw12 ∷ []) [] (wn 14 W)
  q5 : Eqn
  q5 = eqn (CS12⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS12⁻ ∷ []) (wn 15 W)
  q6 : Eqn
  q6 = eqn (CS12 ∷ Sw12 ∷ []) (Sw12 ∷ CS12 ∷ []) (wn 16 W)
  q7 : Eqn
  q7 = eqn (K1 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 366 W)
  q8 : Eqn
  q8 = eqn (CS23 ∷ Sw12 ∷ []) (Sw12 ∷ CS13 ∷ []) (wn 48 W)
  q9 : Eqn
  q9 = eqn (Sw12 ∷ X3 ∷ []) (X3 ∷ Sw12 ∷ []) (low₃-comm ((Swap ↑)) (X))
  q10 : Eqn
  q10 = eqn (CK32 ∷ Sw12 ∷ []) (Sw12 ∷ CK31 ∷ []) (wn 280 W)
  q11 : Eqn
  q11 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q12 : Eqn
  q12 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q13 : Eqn
  q13 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q14 : Eqn
  q14 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q15 : Eqn
  q15 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q16 : Eqn
  q16 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q17 : Eqn
  q17 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q18 : Eqn
  q18 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q19 : Eqn
  q19 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q20 : Eqn
  q20 = eqn (K1 ∷ Sw01 ∷ []) (Sw01 ∷ K0 ∷ []) (wn 271 W)
  q21 : Eqn
  q21 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q23 : Eqn
  q23 = eqn (CX01 ∷ Sw01 ∷ []) (Sw01 ∷ CX10 ∷ []) (wn 8 W)
  q24 : Eqn
  q24 = eqn (CS12⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS02⁻ ∷ []) (wn 9 W)
  q25 : Eqn
  q25 = eqn (CS12 ∷ Sw01 ∷ []) (Sw01 ∷ CS02 ∷ []) (wn 10 W)
  q26 : Eqn
  q26 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q27 : Eqn
  q27 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q28 : Eqn
  q28 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q29 : Eqn
  q29 = eqn (K0 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K0 ∷ ι1 ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 272 W)
  q30 : Eqn
  q30 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q31 : Eqn
  q31 = eqn (CK21 ∷ Sw01 ∷ []) (Sw01 ∷ CK20 ∷ []) (wn 273 W)
  q32 : Eqn
  q32 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q33 : Eqn
  q33 = eqn (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (wn 22 W)
  q34 : Eqn
  q34 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q35 : Eqn
  q35 = eqn (Sw23 ∷ Sw12 ∷ Sw23 ∷ []) (Sw12 ∷ Sw23 ∷ Sw12 ∷ []) (wn 23 W)
  q36 : Eqn
  q36 = eqn (CS13⁻ ∷ Sw12 ∷ []) (Sw12 ∷ CS23⁻ ∷ []) (wn 84 W)
  q37 : Eqn
  q37 = eqn (CS13 ∷ Sw12 ∷ []) (Sw12 ∷ CS23 ∷ []) (wn 65 W)
  q38 : Eqn
  q38 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q39 : Eqn
  q39 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q40 : Eqn
  q40 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q41 : Eqn
  q41 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q42 : Eqn
  q42 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)
  q44 : Eqn
  q44 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q45 : Eqn
  q45 = eqn (X2 ∷ Sw12 ∷ []) (Sw12 ∷ X1 ∷ []) (wn 215 W)
  q46 : Eqn
  q46 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q47 : Eqn
  q47 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q48 : Eqn
  q48 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q49 : Eqn
  q49 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q50 : Eqn
  q50 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q51 : Eqn
  q51 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q52 : Eqn
  q52 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q53 : Eqn
  q53 = eqn (CS01 ∷ Sw01 ∷ []) (Sw01 ∷ CS01 ∷ []) (wn 216 W)
  q54 : Eqn
  q54 = eqn (X1 ∷ Sw01 ∷ []) (Sw01 ∷ X0 ∷ []) (wn 217 W)
  q55 : Eqn
  q55 = eqn (CK10 ∷ Sw01 ∷ []) (Sw01 ∷ CK01 ∷ []) (wn 218 W)
  q56 : Eqn
  q56 = eqn (X0 ∷ CK01 ∷ X0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (ax ck-tct)
  q57 : Eqn
  q57 = eqn (Sw01 ∷ CS01 ∷ []) (CS01 ∷ Sw01 ∷ []) (wn 219 W)
  q58 : Eqn
  q58 = eqn (Sw01 ∷ X0 ∷ []) (X1 ∷ Sw01 ∷ []) (wn 220 W)
  q59 : Eqn
  q59 = eqn (Sw01 ∷ CK01 ∷ []) (CK10 ∷ Sw01 ∷ []) (wn 221 W)
  q60 : Eqn
  q60 = eqn (Sw12 ∷ CS23 ∷ []) (CS13 ∷ Sw12 ∷ []) (wn 49 W)
  q61 : Eqn
  q61 = eqn (Sw12 ∷ CS23⁻ ∷ []) (CS13⁻ ∷ Sw12 ∷ []) (wn 51 W)
  q62 : Eqn
  q62 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q63 : Eqn
  q63 = eqn (Sw12 ∷ X1 ∷ []) (X2 ∷ Sw12 ∷ []) (wn 222 W)
  q64 : Eqn
  q64 = eqn (Sw01 ∷ CX01 ∷ []) (CX10 ∷ Sw01 ∷ []) (wn 28 W)
  q65 : Eqn
  q65 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q66 : Eqn
  q66 = eqn (K1 ∷ CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 274 W)
  q67 : Eqn
  q67 = eqn (Sw01 ∷ CK20 ∷ []) (CK21 ∷ Sw01 ∷ []) (wn 275 W)
  q68 : Eqn
  q68 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q69 : Eqn
  q69 = eqn (Sw12 ∷ K1 ∷ []) (K2 ∷ Sw12 ∷ []) (wn 340 W)
  q70 : Eqn
  q70 = eqn (Sw12 ∷ CS12 ∷ []) (CS12 ∷ Sw12 ∷ []) (wn 18 W)
  q71 : Eqn
  q71 = eqn (Sw12 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Sw12 ∷ []) (wn 19 W)
  q72 : Eqn
  q72 = eqn (K2 ∷ CS12 ∷ CX02 ∷ CS12⁻ ∷ CX02 ∷ CS01 ∷ K2 ∷ ι ∷ []) (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) (wn 363 W)
  q73 : Eqn
  q73 = eqn (Sw12 ∷ CS13 ∷ []) (CS23 ∷ Sw12 ∷ []) (wn 20 W)
  q74 : Eqn
  q74 = eqn (Sw12 ∷ CK31 ∷ []) (CK32 ∷ Sw12 ∷ []) (wn 359 W)
  q75 : Eqn
  q75 = eqn (X3 ∷ CK32 ∷ X3 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) (wn 399 W)

-- pass [X3 CK32 X3] [TOFF201 CS23 TOFF201 CSd23]: 712 steps
lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (X3 ∷ CK32 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 6 q1 ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 12 q2 ∷
   rw 11 q3 ∷
   re 10 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 12 q4 ∷
   rw 9 q1 ∷
   re 10 3 (CX02 ∷ []) ∷
   rw 8 q5 ∷
   rw 7 q1 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q6 ∷
   rw 5 q3 ∷
   rw 6 q7 ∷
   re 6 8 (Toff102 ∷ []) ∷
   rw 4 q8 ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 10 q4 ∷
   rw 7 q1 ∷
   re 8 3 (CX02 ∷ []) ∷
   rw 6 q5 ∷
   rw 5 q1 ∷
   re 6 3 (CX02 ∷ []) ∷
   rw 4 q6 ∷
   rw 3 q3 ∷
   rw 4 q7 ∷
   re 4 8 (Toff102 ∷ []) ∷
   rw⁻ 2 q9 ∷
   rw 1 q10 ∷
   rw⁻ 0 q9 ∷
   rw 7 q11 ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 13 q12 ∷
   rw 12 q13 ∷
   rw 11 q11 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 10 q14 ∷
   rw 9 q11 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw 8 q14 ∷
   rw 7 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 6 q13 ∷
   rw 7 q11 ∷
   rw⁻ 8 q13 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q15 ∷
   rw⁻ 10 q14 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q15 ∷
   rw⁻ 12 q14 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q15 ∷
   rw⁻ 14 q13 ∷
   rw⁻ 15 q12 ∷
   rw 8 q16 ∷
   re 8 8 (Toff102 ∷ []) ∷
   re 7 3 (Toff103 ∷ []) ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 11 q12 ∷
   rw 10 q13 ∷
   rw 9 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 8 q14 ∷
   rw 7 q11 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw 6 q14 ∷
   rw 5 q11 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q13 ∷
   rw 5 q11 ∷
   rw⁻ 6 q13 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   rw⁻ 8 q14 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q15 ∷
   rw⁻ 10 q14 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q15 ∷
   rw⁻ 12 q13 ∷
   rw⁻ 13 q12 ∷
   rw 6 q16 ∷
   re 6 8 (Toff102 ∷ []) ∷
   re 5 3 (Toff103 ∷ []) ∷
   rw 3 q17 ∷
   re 2 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 4 q15 ∷
   rw 1 q17 ∷
   rw 8 q18 ∷
   re 7 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 8 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 7 q13 ∷
   rw 10 q11 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q14 ∷
   rw 12 q11 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q14 ∷
   rw 14 q11 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q13 ∷
   rw⁻ 14 q12 ∷
   rw 15 q15 ∷
   rw 14 q19 ∷
   rw 13 q20 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q21 ∷
   rw 13 q22 ∷
   rw⁻ 12 q21 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q23 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q21 ∷
   rw 11 q24 ∷
   rw⁻ 10 q21 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw 9 q23 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q21 ∷
   rw 9 q25 ∷
   rw⁻ 8 q21 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 7 q20 ∷
   rw 8 q11 ∷
   rw⁻ 9 q26 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q15 ∷
   rw⁻ 11 q27 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q15 ∷
   rw⁻ 13 q27 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q15 ∷
   rw⁻ 15 q26 ∷
   rw⁻ 16 q28 ∷
   rw 9 q29 ∷
   re 9 8 (Toff012 ∷ []) ∷
   re 8 3 (Toff013 ∷ []) ∷
   rw 6 q25 ∷
   re 5 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 5 q13 ∷
   rw 8 q11 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q14 ∷
   rw 10 q11 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q14 ∷
   rw 12 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q13 ∷
   rw⁻ 12 q12 ∷
   rw 13 q15 ∷
   rw 12 q19 ∷
   rw 11 q20 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q21 ∷
   rw 11 q22 ∷
   rw⁻ 10 q21 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q23 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q21 ∷
   rw 9 q24 ∷
   rw⁻ 8 q21 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 7 q23 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q21 ∷
   rw 7 q25 ∷
   rw⁻ 6 q21 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 5 q20 ∷
   rw 6 q11 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q15 ∷
   rw⁻ 9 q27 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q15 ∷
   rw⁻ 11 q27 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q15 ∷
   rw⁻ 13 q26 ∷
   rw⁻ 14 q28 ∷
   rw 7 q29 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw⁻ 4 q30 ∷
   rw 3 q31 ∷
   rw⁻ 2 q30 ∷
   rw 9 q1 ∷
   re 8 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 9 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 8 q26 ∷
   rw 11 q11 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q14 ∷
   rw 13 q11 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q14 ∷
   rw 15 q11 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw⁻ 14 q26 ∷
   rw⁻ 15 q12 ∷
   rw 16 q15 ∷
   rw 15 q2 ∷
   rw 14 q32 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q33 ∷
   rw 15 q34 ∷
   rw 13 q35 ∷
   re 14 5 (CS03 ∷ []) ∷
   rw 12 q1 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q36 ∷
   rw 10 q1 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q37 ∷
   rw 8 q32 ∷
   rw 9 q18 ∷
   rw 10 q38 ∷
   rw 11 q39 ∷
   rw 12 q40 ∷
   rw 13 q41 ∷
   rw 14 q40 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q21 ∷
   rw 16 q42 ∷
   rw 17 q21 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 16 q38 ∷
   rw 17 q43 ∷
   rw 10 q44 ∷
   re 10 8 (Toff123 ∷ []) ∷
   re 9 3 (Toff023 ∷ []) ∷
   re 7 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 9 q4 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q26 ∷
   rw 9 q11 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q14 ∷
   rw 11 q11 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q14 ∷
   rw 13 q11 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q26 ∷
   rw⁻ 13 q12 ∷
   rw 14 q15 ∷
   rw 13 q2 ∷
   rw 12 q32 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q33 ∷
   rw 13 q34 ∷
   rw 11 q35 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 10 q1 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q36 ∷
   rw 8 q1 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q37 ∷
   rw 6 q32 ∷
   rw 7 q18 ∷
   rw 8 q38 ∷
   rw 9 q39 ∷
   rw 10 q40 ∷
   rw 11 q41 ∷
   rw 12 q40 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q21 ∷
   rw 14 q42 ∷
   rw 15 q21 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 14 q38 ∷
   rw 15 q43 ∷
   rw 8 q44 ∷
   re 8 8 (Toff123 ∷ []) ∷
   re 7 3 (Toff023 ∷ []) ∷
   rw 5 q45 ∷
   re 4 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 6 q4 ∷
   rw 3 q45 ∷
   rw 10 q18 ∷
   re 9 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 10 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 9 q46 ∷
   rw 10 q39 ∷
   rw 11 q47 ∷
   rw 12 q41 ∷
   rw 13 q47 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q21 ∷
   rw 15 q48 ∷
   rw 16 q21 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q46 ∷
   rw 16 q49 ∷
   rw 17 q50 ∷
   rw 16 q19 ∷
   rw 15 q51 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q21 ∷
   rw 15 q22 ∷
   rw⁻ 14 q21 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 13 q52 ∷
   rw⁻ 12 q41 ∷
   rw 11 q52 ∷
   rw⁻ 10 q39 ∷
   rw 9 q51 ∷
   rw 10 q44 ∷
   re 10 8 (Toff123 ∷ []) ∷
   rw 8 q53 ∷
   re 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q46 ∷
   rw 8 q39 ∷
   rw 9 q47 ∷
   rw 10 q41 ∷
   rw 11 q47 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   rw 13 q48 ∷
   rw 14 q21 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q46 ∷
   rw 14 q49 ∷
   rw 15 q50 ∷
   rw 14 q19 ∷
   rw 13 q51 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q21 ∷
   rw 13 q22 ∷
   rw⁻ 12 q21 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q52 ∷
   rw⁻ 10 q41 ∷
   rw 9 q52 ∷
   rw⁻ 8 q39 ∷
   rw 7 q51 ∷
   rw 8 q44 ∷
   re 8 8 (Toff123 ∷ []) ∷
   rw 6 q54 ∷
   rw 5 q55 ∷
   rw 4 q54 ∷
   rw 5 q56 ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q46 ∷
   rw 5 q39 ∷
   rw 6 q47 ∷
   rw 7 q41 ∷
   rw 8 q47 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q48 ∷
   rw 11 q21 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q46 ∷
   rw 11 q49 ∷
   rw 4 q18 ∷
   rw 5 q38 ∷
   rw 6 q39 ∷
   rw 7 q40 ∷
   rw 8 q41 ∷
   rw 9 q40 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q21 ∷
   rw 11 q42 ∷
   rw 12 q21 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q38 ∷
   rw 12 q43 ∷
   rw 5 q44 ∷
   re 5 8 (Toff123 ∷ []) ∷
   re 4 3 (Toff023 ∷ []) ∷
   rw 5 q57 ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q46 ∷
   rw 7 q39 ∷
   rw 8 q47 ∷
   rw 9 q41 ∷
   rw 10 q47 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 12 q48 ∷
   rw 13 q21 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q46 ∷
   rw 13 q49 ∷
   rw 6 q18 ∷
   rw 7 q38 ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw 10 q41 ∷
   rw 11 q40 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q21 ∷
   rw 13 q42 ∷
   rw 14 q21 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 13 q38 ∷
   rw 14 q43 ∷
   rw 7 q44 ∷
   re 7 8 (Toff123 ∷ []) ∷
   re 6 3 (Toff023 ∷ []) ∷
   rw 7 q58 ∷
   rw 8 q59 ∷
   rw 9 q58 ∷
   rw 10 q50 ∷
   re 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q46 ∷
   rw 5 q39 ∷
   rw 6 q47 ∷
   rw 7 q41 ∷
   rw 8 q47 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q48 ∷
   rw 11 q21 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q46 ∷
   rw 11 q49 ∷
   rw 12 q50 ∷
   rw⁻ 3 q32 ∷
   rw 4 q60 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q4 ∷
   rw 6 q61 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q4 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q33 ∷
   rw⁻ 10 q34 ∷
   rw 11 q35 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw⁻ 9 q32 ∷
   rw⁻ 10 q2 ∷
   rw 3 q11 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q15 ∷
   rw⁻ 6 q14 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   rw⁻ 8 q14 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q15 ∷
   rw⁻ 10 q26 ∷
   rw⁻ 11 q12 ∷
   rw 4 q62 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 6 q1 ∷
   re 4 3 (CS02 ∷ []) ∷
   re 6 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 7 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 6 q46 ∷
   rw 7 q39 ∷
   rw 8 q47 ∷
   rw 9 q41 ∷
   rw 10 q47 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q21 ∷
   rw 12 q48 ∷
   rw 13 q21 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q46 ∷
   rw 13 q49 ∷
   rw 14 q50 ∷
   rw⁻ 5 q32 ∷
   rw 6 q60 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q61 ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 9 q4 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 10 q33 ∷
   rw⁻ 12 q34 ∷
   rw 13 q35 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw⁻ 11 q32 ∷
   rw⁻ 12 q2 ∷
   rw 5 q11 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q15 ∷
   rw⁻ 8 q14 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q15 ∷
   rw⁻ 10 q14 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q15 ∷
   rw⁻ 12 q26 ∷
   rw⁻ 13 q12 ∷
   rw 6 q62 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 5 3 (Toff013 ∷ []) ∷
   rw 6 q63 ∷
   rw 9 q1 ∷
   re 7 3 (CK20 ∷ []) ∷
   rw 8 q63 ∷
   rw 9 q4 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q11 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q14 ∷
   rw 8 q11 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q14 ∷
   rw 10 q11 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q26 ∷
   rw⁻ 10 q12 ∷
   rw 11 q15 ∷
   rw 2 q38 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q48 ∷
   rw 5 q21 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q64 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 6 q65 ∷
   rw 7 q21 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q64 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q42 ∷
   rw 9 q21 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q38 ∷
   rw 9 q43 ∷
   rw 2 q11 ∷
   rw⁻ 3 q13 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q15 ∷
   rw⁻ 5 q27 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q15 ∷
   rw⁻ 7 q27 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q15 ∷
   rw⁻ 9 q13 ∷
   rw⁻ 10 q28 ∷
   rw 3 q66 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw 3 q42 ∷
   re 5 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q11 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q14 ∷
   rw 10 q11 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q14 ∷
   rw 12 q11 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q26 ∷
   rw⁻ 12 q12 ∷
   rw 13 q15 ∷
   rw 4 q38 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q21 ∷
   rw 6 q48 ∷
   rw 7 q21 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q64 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q65 ∷
   rw 9 q21 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q64 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q42 ∷
   rw 11 q21 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 10 q38 ∷
   rw 11 q43 ∷
   rw 4 q11 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q15 ∷
   rw⁻ 7 q27 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q15 ∷
   rw⁻ 9 q27 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q15 ∷
   rw⁻ 11 q13 ∷
   rw⁻ 12 q28 ∷
   rw 5 q66 ∷
   re 5 8 (Toff102 ∷ []) ∷
   re 4 3 (Toff103 ∷ []) ∷
   rw 5 q30 ∷
   rw 6 q67 ∷
   rw 7 q30 ∷
   rw 8 q50 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q13 ∷
   rw 5 q11 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q14 ∷
   rw 7 q11 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q14 ∷
   rw 9 q11 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q13 ∷
   rw⁻ 9 q12 ∷
   rw 10 q15 ∷
   rw⁻ 1 q13 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q15 ∷
   rw⁻ 3 q14 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q15 ∷
   rw⁻ 5 q14 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q15 ∷
   rw⁻ 7 q13 ∷
   rw⁻ 8 q12 ∷
   rw 1 q16 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 4 q11 ∷
   re 2 3 (CS13 ∷ []) ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q13 ∷
   rw 7 q11 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q14 ∷
   rw 9 q11 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q14 ∷
   rw 11 q11 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q13 ∷
   rw⁻ 11 q12 ∷
   rw 12 q15 ∷
   rw⁻ 3 q13 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q15 ∷
   rw⁻ 5 q14 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q15 ∷
   rw⁻ 7 q14 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q15 ∷
   rw⁻ 9 q13 ∷
   rw⁻ 10 q12 ∷
   rw 3 q16 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 4 q68 ∷
   rw 7 q11 ∷
   re 5 3 (CK31 ∷ []) ∷
   rw 6 q68 ∷
   rw 7 q15 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 0 q69 ∷
   rw 1 q70 ∷
   rw 4 q1 ∷
   re 2 3 (CX02 ∷ []) ∷
   rw 3 q71 ∷
   rw 6 q1 ∷
   re 4 3 (CX02 ∷ []) ∷
   re 6 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 5 q4 ∷
   rw 6 q69 ∷
   rw⁻ 7 q2 ∷
   rw 0 q72 ∷
   re 0 8 (Toff201 ∷ []) ∷
   rw 1 q73 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 2 q69 ∷
   rw 3 q70 ∷
   rw 6 q1 ∷
   re 4 3 (CX02 ∷ []) ∷
   rw 5 q71 ∷
   rw 8 q1 ∷
   re 6 3 (CX02 ∷ []) ∷
   re 8 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q4 ∷
   rw 8 q69 ∷
   rw⁻ 9 q2 ∷
   rw 2 q72 ∷
   re 2 8 (Toff201 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q74 ∷
   rw 5 q9 ∷
   rw 6 q4 ∷
   rw 3 q75 ∷ []) Eq.refl
