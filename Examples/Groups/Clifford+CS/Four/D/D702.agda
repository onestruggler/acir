{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD702 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D702 (W : Ws) (Sᴰ : SD702) where

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
  lem-pass-X3-CKd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : St 1932
  lem-pass-X3-CKd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = pickᴰ 0 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : St 1933
  lem-pass-X3-CS32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = pickᴰ 1 Sᴰ
  lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12 : St 1934
  lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12 = pickᴰ 2 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF103-CS12-TOFF103-CSd12 : St 1935
  lem-pass-X3-CSd31-X3-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 3 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : St 1936
  lem-pass-X3-CSd32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = pickᴰ 4 Sᴰ
  lem-pass-X3-CSd32-X3-vs-TOFF203-CS12-TOFF203-CSd12 : St 1937
  lem-pass-X3-CSd32-X3-vs-TOFF203-CS12-TOFF203-CSd12 = pickᴰ 5 Sᴰ
  lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01 : St 1938
  lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01 = pickᴰ 6 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0 : St 1912
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0 = pickᴰ 7 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0 : St 1913
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0 = pickᴰ 8 Sᴰ
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CS13 : St 1939
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CS13 = pickᴰ 9 Sᴰ
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd13 : St 1940
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X2-TOFF102-X2 : St 1941
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X2-TOFF102-X2 = pickᴰ 11 Sᴰ
  lem-S2-at0213 : St 1917
  lem-S2-at0213 = pickᴰ 12 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 13 Sᴰ
  lem-S2-at2013 : St 1942
  lem-S2-at2013 = pickᴰ 14 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03 : St 1919
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03 = pickᴰ 15 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03 : St 1920
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03 = pickᴰ 16 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2 : St 1922
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2 = pickᴰ 17 Sᴰ
  lem-pass-TOFF203-CS12-TOFF203-CSd12-vs-X3-TOFF013-X3 : St 1943
  lem-pass-TOFF203-CS12-TOFF203-CSd12-vs-X3-TOFF013-X3 = pickᴰ 18 Sᴰ
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF103-CS12-TOFF103-CSd12 : St 1944
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 19 Sᴰ

private
  q1 : Eqn
  q1 = sE 1918 lem-S2-at1023
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q6 : Eqn
  q6 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 127 W
  q9 : Eqn
  q9 = wE 271 W
  q10 : Eqn
  q10 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = wE 8 W
  q13 : Eqn
  q13 = wE 9 W
  q14 : Eqn
  q14 = wE 10 W
  q15 : Eqn
  q15 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q16 : Eqn
  q16 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q17 : Eqn
  q17 = eqn (ι1 ∷ Sw23 ∷ []) (Sw23 ∷ ι1 ∷ []) (low-comm ((iI ↑)) (Swap))
  q18 : Eqn
  q18 = wE 272 W
  q19 : Eqn
  q19 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q20 : Eqn
  q20 = wE 273 W
  q21 : Eqn
  q21 = wE 12 W
  q22 : Eqn
  q22 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q23 : Eqn
  q23 = eqn (K0 ∷ Sw12 ∷ []) (Sw12 ∷ K0 ∷ []) (low₁-comm (K) (Swap))
  q24 : Eqn
  q24 = wE 22 W
  q25 : Eqn
  q25 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q26 : Eqn
  q26 = wE 23 W
  q27 : Eqn
  q27 = wE 84 W
  q28 : Eqn
  q28 = wE 65 W
  q29 : Eqn
  q29 = wE 123 W
  q30 : Eqn
  q30 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q31 : Eqn
  q31 = wE 24 W
  q32 : Eqn
  q32 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q33 : Eqn
  q33 = wE 25 W
  q34 : Eqn
  q34 = wE 124 W
  q35 : Eqn
  q35 = wE 125 W
  q36 : Eqn
  q36 = wE 14 W
  q37 : Eqn
  q37 = wE 215 W
  q38 : Eqn
  q38 = wE 121 W
  q39 : Eqn
  q39 = wE 30 W
  q40 : Eqn
  q40 = wE 27 W
  q41 : Eqn
  q41 = wE 122 W
  q42 : Eqn
  q42 = wE 31 W
  q43 : Eqn
  q43 = wE 118 W
  q44 : Eqn
  q44 = wE 74 W
  q45 : Eqn
  q45 = wE 216 W
  q46 : Eqn
  q46 = wE 217 W
  q47 : Eqn
  q47 = wE 218 W
  q48 : Eqn
  q48 = eqn (X0 ∷ CK01 ∷ X0 ∷ Toff123 ∷ CS01 ∷ Toff123 ∷ []) (Toff123 ∷ CS01 ∷ Toff123 ∷ X0 ∷ CK01 ∷ X0 ∷ []) (ax ck-tct)
  q49 : Eqn
  q49 = wE 219 W
  q50 : Eqn
  q50 = wE 220 W
  q51 : Eqn
  q51 = wE 221 W
  q52 : Eqn
  q52 = wE 49 W
  q53 : Eqn
  q53 = wE 51 W
  q54 : Eqn
  q54 = wE 56 W
  q55 : Eqn
  q55 = wE 222 W
  q56 : Eqn
  q56 = wE 28 W
  q57 : Eqn
  q57 = wE 29 W
  q58 : Eqn
  q58 = wE 274 W
  q59 : Eqn
  q59 = wE 275 W
  q60 : Eqn
  q60 = wE 2049 W
  q61 : Eqn
  q61 = sE 1918 lem-S2-at1023

-- pass [X2 CK21 X2] [TOFF102 CS13 TOFF102 CSd13]: 526 steps
lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X2 ∷ CK21 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CK21 ∷ X2 ∷ [])
  (rw 3 q1 ∷
   rw 6 q2 ∷
   re 5 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 6 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q4 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 10 q4 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q5 ∷
   rw 12 q4 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q6 ∷
   rw 13 q7 ∷
   rw 12 q8 ∷
   rw 11 q9 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q10 ∷
   rw 11 q11 ∷
   rw⁻ 10 q10 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q12 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q10 ∷
   rw 9 q13 ∷
   rw⁻ 8 q10 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 7 q12 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q10 ∷
   rw 7 q14 ∷
   rw⁻ 6 q10 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 5 q9 ∷
   rw 6 q4 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q16 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw⁻ 11 q16 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q7 ∷
   rw⁻ 13 q15 ∷
   rw⁻ 14 q17 ∷
   rw 7 q18 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   rw 4 q14 ∷
   re 3 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 4 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 6 q4 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q5 ∷
   rw 8 q4 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 10 q4 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q6 ∷
   rw 11 q7 ∷
   rw 10 q8 ∷
   rw 9 q9 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q10 ∷
   rw 9 q11 ∷
   rw⁻ 8 q10 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q12 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q10 ∷
   rw 7 q13 ∷
   rw⁻ 6 q10 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 5 q12 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 6 q10 ∷
   rw 5 q14 ∷
   rw⁻ 4 q10 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 3 q9 ∷
   rw 4 q4 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 7 q16 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q16 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q7 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 12 q17 ∷
   rw 5 q18 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   rw⁻ 2 q19 ∷
   rw 1 q20 ∷
   rw⁻ 0 q19 ∷
   rw 7 q21 ∷
   re 6 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 7 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw 9 q4 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q4 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q5 ∷
   rw 13 q4 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q15 ∷
   rw⁻ 13 q6 ∷
   rw 14 q7 ∷
   rw 13 q22 ∷
   rw 12 q23 ∷
   re 11 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 14 q24 ∷
   rw 13 q25 ∷
   rw 11 q26 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 10 q21 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q27 ∷
   rw 8 q21 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q28 ∷
   rw 6 q23 ∷
   rw 7 q2 ∷
   rw 8 q29 ∷
   rw 9 q30 ∷
   rw 10 q31 ∷
   rw 11 q32 ∷
   rw 12 q31 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q10 ∷
   rw 14 q33 ∷
   rw 15 q10 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 14 q29 ∷
   rw 15 q34 ∷
   rw 8 q35 ∷
   re 8 8 (Toff123 ∷ []) ∷
   re 7 3 (Toff023 ∷ []) ∷
   re 5 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 7 q36 ∷
   re 4 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 5 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 7 q4 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q5 ∷
   rw 9 q4 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 11 q4 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q15 ∷
   rw⁻ 11 q6 ∷
   rw 12 q7 ∷
   rw 11 q22 ∷
   rw 10 q23 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q24 ∷
   rw 11 q25 ∷
   rw 9 q26 ∷
   re 10 5 (CS03 ∷ []) ∷
   rw 8 q21 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q27 ∷
   rw 6 q21 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q28 ∷
   rw 4 q23 ∷
   rw 5 q2 ∷
   rw 6 q29 ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q32 ∷
   rw 10 q31 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q10 ∷
   rw 12 q33 ∷
   rw 13 q10 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 12 q29 ∷
   rw 13 q34 ∷
   rw 6 q35 ∷
   re 6 8 (Toff123 ∷ []) ∷
   re 5 3 (Toff023 ∷ []) ∷
   rw 3 q37 ∷
   re 2 1 (Sw12 ∷ CK10 ∷ Sw12 ∷ []) ∷
   rw 4 q36 ∷
   rw 1 q37 ∷
   rw 8 q2 ∷
   re 7 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 8 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 7 q38 ∷
   rw 8 q30 ∷
   rw 9 q39 ∷
   rw 10 q32 ∷
   rw 11 q39 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q10 ∷
   rw 13 q40 ∷
   rw 14 q10 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q38 ∷
   rw 14 q41 ∷
   rw 15 q42 ∷
   rw 14 q8 ∷
   rw 13 q43 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q10 ∷
   rw 13 q11 ∷
   rw⁻ 12 q10 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 11 q44 ∷
   rw⁻ 10 q32 ∷
   rw 9 q44 ∷
   rw⁻ 8 q30 ∷
   rw 7 q43 ∷
   rw 8 q35 ∷
   re 8 8 (Toff123 ∷ []) ∷
   rw 6 q45 ∷
   re 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q38 ∷
   rw 6 q30 ∷
   rw 7 q39 ∷
   rw 8 q32 ∷
   rw 9 q39 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q40 ∷
   rw 12 q10 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q38 ∷
   rw 12 q41 ∷
   rw 13 q42 ∷
   rw 12 q8 ∷
   rw 11 q43 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q10 ∷
   rw 11 q11 ∷
   rw⁻ 10 q10 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q44 ∷
   rw⁻ 8 q32 ∷
   rw 7 q44 ∷
   rw⁻ 6 q30 ∷
   rw 5 q43 ∷
   rw 6 q35 ∷
   re 6 8 (Toff123 ∷ []) ∷
   rw 4 q46 ∷
   rw 3 q47 ∷
   rw 2 q46 ∷
   rw 3 q48 ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q38 ∷
   rw 3 q30 ∷
   rw 4 q39 ∷
   rw 5 q32 ∷
   rw 6 q39 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q40 ∷
   rw 9 q10 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q38 ∷
   rw 9 q41 ∷
   rw 2 q2 ∷
   rw 3 q29 ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   rw 6 q32 ∷
   rw 7 q31 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q33 ∷
   rw 10 q10 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q29 ∷
   rw 10 q34 ∷
   rw 3 q35 ∷
   re 3 8 (Toff123 ∷ []) ∷
   re 2 3 (Toff023 ∷ []) ∷
   rw 3 q49 ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q38 ∷
   rw 5 q30 ∷
   rw 6 q39 ∷
   rw 7 q32 ∷
   rw 8 q39 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q40 ∷
   rw 11 q10 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q38 ∷
   rw 11 q41 ∷
   rw 4 q2 ∷
   rw 5 q29 ∷
   rw 6 q30 ∷
   rw 7 q31 ∷
   rw 8 q32 ∷
   rw 9 q31 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q33 ∷
   rw 12 q10 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 11 q29 ∷
   rw 12 q34 ∷
   rw 5 q35 ∷
   re 5 8 (Toff123 ∷ []) ∷
   re 4 3 (Toff023 ∷ []) ∷
   rw 5 q50 ∷
   rw 6 q51 ∷
   rw 7 q50 ∷
   rw 8 q42 ∷
   re 2 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q38 ∷
   rw 3 q30 ∷
   rw 4 q39 ∷
   rw 5 q32 ∷
   rw 6 q39 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q40 ∷
   rw 9 q10 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q38 ∷
   rw 9 q41 ∷
   rw 10 q42 ∷
   rw⁻ 1 q23 ∷
   rw 2 q52 ∷
   re 4 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 3 q36 ∷
   rw 4 q53 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q36 ∷
   re 7 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 6 q24 ∷
   rw⁻ 8 q25 ∷
   rw 9 q26 ∷
   re 6 5 (CS03 ∷ []) ∷
   rw⁻ 7 q23 ∷
   rw⁻ 8 q22 ∷
   rw 1 q4 ∷
   rw⁻ 2 q15 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw⁻ 4 q5 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw⁻ 6 q5 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 9 q6 ∷
   rw 2 q54 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 4 q21 ∷
   re 2 3 (CS02 ∷ []) ∷
   re 4 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 5 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 4 q38 ∷
   rw 5 q30 ∷
   rw 6 q39 ∷
   rw 7 q32 ∷
   rw 8 q39 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q10 ∷
   rw 10 q40 ∷
   rw 11 q10 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q38 ∷
   rw 11 q41 ∷
   rw 12 q42 ∷
   rw⁻ 3 q23 ∷
   rw 4 q52 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 5 q36 ∷
   rw 6 q53 ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 7 q36 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q24 ∷
   rw⁻ 10 q25 ∷
   rw 11 q26 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw⁻ 9 q23 ∷
   rw⁻ 10 q22 ∷
   rw 3 q4 ∷
   rw⁻ 4 q15 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q7 ∷
   rw⁻ 6 q5 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw⁻ 8 q5 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q7 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 11 q6 ∷
   rw 4 q54 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 4 q55 ∷
   rw 7 q21 ∷
   re 5 3 (CK20 ∷ []) ∷
   rw 6 q55 ∷
   rw 7 q36 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q15 ∷
   rw 4 q4 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q5 ∷
   rw 6 q4 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q5 ∷
   rw 8 q4 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q6 ∷
   rw 9 q7 ∷
   rw 0 q29 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 1 q10 ∷
   rw 2 q40 ∷
   rw 3 q10 ∷
   re 1 3 (CS03 ∷ []) ∷
   rw 2 q56 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q57 ∷
   rw 5 q10 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   rw 4 q56 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw 6 q33 ∷
   rw 7 q10 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw 6 q29 ∷
   rw 7 q34 ∷
   rw 0 q4 ∷
   rw⁻ 1 q3 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q7 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q17 ∷
   rw 1 q58 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q33 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q15 ∷
   rw 6 q4 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q5 ∷
   rw 8 q4 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 10 q4 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q6 ∷
   rw 11 q7 ∷
   rw 2 q29 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q10 ∷
   rw 4 q40 ∷
   rw 5 q10 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q56 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw 6 q57 ∷
   rw 7 q10 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q56 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q33 ∷
   rw 9 q10 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q29 ∷
   rw 9 q34 ∷
   rw 2 q4 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q7 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q7 ∷
   rw⁻ 7 q16 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q7 ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q17 ∷
   rw 3 q58 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw 3 q19 ∷
   rw 4 q59 ∷
   rw 5 q19 ∷
   rw 6 q42 ∷
   rw 3 q60 ∷
   rw⁻ 0 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 1912 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0
  q63 : Eqn
  q63 = sE 1920 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03
  q64 : Eqn
  q64 = sE 1922 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2
  q65 : Eqn
  q65 = sE 1913 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0
  q66 : Eqn
  q66 = sE 1919 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03

-- pass [TOFF012 CS03 TOFF012 CSd03] [S0 CSd03 X2 TOFF012 X2 Sd0 CS03 X2 TOFF012 X2]: 6 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (S0 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ S0⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 0 q62 ∷
   rw 1 q63 ∷
   rw 2 q64 ∷
   rw 5 q65 ∷
   rw 6 q66 ∷
   rw 7 q64 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = sE 1917 lem-S2-at0213
  q68 : Eqn
  q68 = wE 2050 W
  q69 : Eqn
  q69 = sE 1917 lem-S2-at0213

-- pass [X1 CK10 X1] [TOFF012 CS03 TOFF012 CSd03]: 130 steps
lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X1 ∷ CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CK10-X1-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X1 ∷ CK10 ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CK10 ∷ X1 ∷ [])
  (rw 3 q67 ∷
   rw 6 q2 ∷
   re 5 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 6 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 5 q38 ∷
   rw 6 q30 ∷
   rw 7 q39 ∷
   rw 8 q32 ∷
   rw 9 q39 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q10 ∷
   rw 11 q40 ∷
   rw 12 q10 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q38 ∷
   rw 12 q41 ∷
   rw 13 q42 ∷
   rw 12 q8 ∷
   rw 11 q43 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q10 ∷
   rw 11 q11 ∷
   rw⁻ 10 q10 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q44 ∷
   rw⁻ 8 q32 ∷
   rw 7 q44 ∷
   rw⁻ 6 q30 ∷
   rw 5 q43 ∷
   rw 6 q35 ∷
   re 6 8 (Toff123 ∷ []) ∷
   rw 4 q45 ∷
   re 3 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 4 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 3 q38 ∷
   rw 4 q30 ∷
   rw 5 q39 ∷
   rw 6 q32 ∷
   rw 7 q39 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q40 ∷
   rw 10 q10 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q38 ∷
   rw 10 q41 ∷
   rw 11 q42 ∷
   rw 10 q8 ∷
   rw 9 q43 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q10 ∷
   rw 9 q11 ∷
   rw⁻ 8 q10 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 7 q44 ∷
   rw⁻ 6 q32 ∷
   rw 5 q44 ∷
   rw⁻ 4 q30 ∷
   rw 3 q43 ∷
   rw 4 q35 ∷
   re 4 8 (Toff123 ∷ []) ∷
   rw 2 q46 ∷
   rw 1 q47 ∷
   rw 0 q46 ∷
   rw 1 q48 ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q38 ∷
   rw 1 q30 ∷
   rw 2 q39 ∷
   rw 3 q32 ∷
   rw 4 q39 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q10 ∷
   rw 6 q40 ∷
   rw 7 q10 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q38 ∷
   rw 7 q41 ∷
   rw 0 q2 ∷
   rw 1 q29 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 4 q32 ∷
   rw 5 q31 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q10 ∷
   rw 7 q33 ∷
   rw 8 q10 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 7 q29 ∷
   rw 8 q34 ∷
   rw 1 q35 ∷
   re 1 8 (Toff123 ∷ []) ∷
   re 0 3 (Toff023 ∷ []) ∷
   rw 1 q49 ∷
   re 3 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 2 q38 ∷
   rw 3 q30 ∷
   rw 4 q39 ∷
   rw 5 q32 ∷
   rw 6 q39 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q10 ∷
   rw 8 q40 ∷
   rw 9 q10 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q38 ∷
   rw 9 q41 ∷
   rw 2 q2 ∷
   rw 3 q29 ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   rw 6 q32 ∷
   rw 7 q31 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q10 ∷
   rw 9 q33 ∷
   rw 10 q10 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 9 q29 ∷
   rw 10 q34 ∷
   rw 3 q35 ∷
   re 3 8 (Toff123 ∷ []) ∷
   re 2 3 (Toff023 ∷ []) ∷
   rw 3 q50 ∷
   rw 4 q51 ∷
   rw 5 q50 ∷
   rw 6 q42 ∷
   rw 3 q68 ∷
   rw⁻ 0 q69 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = sE 1944 lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [TOFF103 CS12 TOFF103 CSd12] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  (rw⁻ 0 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = sE 1935 lem-pass-X3-CSd31-X3-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [X3 CSd31 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 3 q1 ∷
   rw 0 q71 ∷
   rw⁻ 0 q61 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = sE 1941 lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X2-TOFF102-X2

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 TOFF102 X2]: 3 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-TOFF102-X2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q1 ∷
   rw 0 q72 ∷
   rw⁻ 3 q61 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = sE 1939 lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CS13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CS13]: 3 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS13 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS13 ∷ []) (CS13 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q1 ∷
   rw 0 q73 ∷
   rw⁻ 1 q61 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = sE 1940 lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CSd13]: 3 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd13 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw 0 q1 ∷
   rw 0 q74 ∷
   rw⁻ 1 q61 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 1942 lem-S2-at2013
  q76 : Eqn
  q76 = sE 1934 lem-pass-X3-CS32-X3-vs-TOFF203-CS12-TOFF203-CSd12
  q77 : Eqn
  q77 = sE 1942 lem-S2-at2013

-- pass [X3 CS32 X3] [TOFF201 CS23 TOFF201 CSd23]: 3 steps
lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (X3 ∷ CS23 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 3 q75 ∷
   rw 0 q76 ∷
   rw⁻ 0 q77 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = sE 1937 lem-pass-X3-CSd32-X3-vs-TOFF203-CS12-TOFF203-CSd12

-- pass [X3 CSd32 X3] [TOFF201 CS23 TOFF201 CSd23]: 3 steps
lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-TOFF201-CS23-TOFF201-CSd23 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 3 q75 ∷
   rw 0 q78 ∷
   rw⁻ 0 q77 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = sE 1936 lem-pass-X3-CSd32-X3-vs-TOFF023-CS01-TOFF023-CSd01

-- pass [X3 CSd32 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CSd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CS23⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CS23⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23⁻ ∷ X3 ∷ [])
  (rw 3 q67 ∷
   rw 0 q79 ∷
   rw⁻ 0 q69 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = sE 1932 lem-pass-X3-CKd32-X3-vs-TOFF023-CS01-TOFF023-CSd01

-- pass [X3 CKd32 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CKd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 3 q67 ∷
   rw 0 q80 ∷
   rw⁻ 0 q69 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 1933 lem-pass-X3-CS32-X3-vs-TOFF023-CS01-TOFF023-CSd01

-- pass [X3 CS32 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CS32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CS23 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CS23 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS23 ∷ X3 ∷ [])
  (rw 3 q67 ∷
   rw 0 q81 ∷
   rw⁻ 0 q69 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = sE 1943 lem-pass-TOFF203-CS12-TOFF203-CSd12-vs-X3-TOFF013-X3

-- pass [TOFF201 CS23 TOFF201 CSd23] [X3 TOFF013 X3]: 3 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-X3-TOFF013-X3 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw 0 q75 ∷
   rw 0 q82 ∷
   rw⁻ 3 q77 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = sE 1938 lem-pass-X3-CK32-X3-vs-TOFF023-CS01-TOFF023-CSd01

-- pass [X3 CK32 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CK32-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK32 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CK32 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK32 ∷ X3 ∷ [])
  (rw 3 q67 ∷
   rw 0 q83 ∷
   rw⁻ 0 q69 ∷ []) Eq.refl
