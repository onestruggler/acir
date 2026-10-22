{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD659 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D659 (W : Ws) (Sᴰ : SD659) where

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
  lem-pass-CCZ123-vs-CS23 : St 1735
  lem-pass-CCZ123-vs-CS23 = pickᴰ 0 Sᴰ
  lem-pass-CCZ123-vs-CSd23 : St 1736
  lem-pass-CCZ123-vs-CSd23 = pickᴰ 1 Sᴰ
  lem-pass-CZ01-vs-CSd23 : St 1737
  lem-pass-CZ01-vs-CSd23 = pickᴰ 2 Sᴰ
  lem-pass-CZ12-vs-CS23 : St 1738
  lem-pass-CZ12-vs-CS23 = pickᴰ 3 Sᴰ
  lem-pass-CZ12-vs-CSd23 : St 1739
  lem-pass-CZ12-vs-CSd23 = pickᴰ 4 Sᴰ
  lem-pass-CCZ013-vs-CCZ123 : St 906
  lem-pass-CCZ013-vs-CCZ123 = pickᴰ 5 Sᴰ
  lem-pass-CCZ013-vs-CSd23 : St 1740
  lem-pass-CCZ013-vs-CSd23 = pickᴰ 6 Sᴰ
  lem-pass-CCZ013-vs-TOFF201 : St 1741
  lem-pass-CCZ013-vs-TOFF201 = pickᴰ 7 Sᴰ

private
  q1 : Eqn
  q1 = sE 1735 lem-pass-CCZ123-vs-CS23
  q2 : Eqn
  q2 = sE 1738 lem-pass-CZ12-vs-CS23
  q3 : Eqn
  q3 = wE 1521 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = wE 127 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 8 W
  q9 : Eqn
  q9 = wE 9 W
  q10 : Eqn
  q10 = wE 10 W
  q11 : Eqn
  q11 = wE 333 W
  q12 : Eqn
  q12 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 253 W
  q14 : Eqn
  q14 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q16 : Eqn
  q16 = wE 24 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 26 W
  q19 : Eqn
  q19 = wE 12 W
  q20 : Eqn
  q20 = eqn (ι ∷ Sw12 ∷ []) (Sw12 ∷ ι ∷ []) (low₁-comm (iI) (Swap))
  q21 : Eqn
  q21 = wE 398 W
  q22 : Eqn
  q22 = wE 14 W
  q23 : Eqn
  q23 = wE 15 W
  q24 : Eqn
  q24 = wE 16 W
  q25 : Eqn
  q25 = wE 366 W
  q26 : Eqn
  q26 = wE 30 W
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = wE 31 W
  q29 : Eqn
  q29 = wE 22 W
  q30 : Eqn
  q30 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q31 : Eqn
  q31 = wE 23 W
  q32 : Eqn
  q32 = wE 47 W
  q33 : Eqn
  q33 = wE 48 W
  q34 : Eqn
  q34 = wE 1 W
  q35 : Eqn
  q35 = wE 3 W
  q36 : Eqn
  q36 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q37 : Eqn
  q37 = wE 43 W
  q38 : Eqn
  q38 = wE 271 W
  q39 : Eqn
  q39 = wE 272 W
  q40 : Eqn
  q40 = eqn (CX10 ∷ Sw23 ∷ []) (Sw23 ∷ CX10 ∷ []) (low-comm (CX₁₀) (Swap))
  q41 : Eqn
  q41 = wE 11 W
  q42 : Eqn
  q42 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)
  q43 : Eqn
  q43 = wE 28 W
  q44 : Eqn
  q44 = wE 29 W
  q45 : Eqn
  q45 = wE 20 W
  q46 : Eqn
  q46 = wE 21 W
  q47 : Eqn
  q47 = wE 49 W
  q48 : Eqn
  q48 = wE 51 W
  q49 : Eqn
  q49 = wE 1991 W
  q50 : Eqn
  q50 = sE 906 lem-pass-CCZ013-vs-CCZ123
  q51 : Eqn
  q51 = sE 1736 lem-pass-CCZ123-vs-CSd23
  q52 : Eqn
  q52 = sE 1740 lem-pass-CCZ013-vs-CSd23
  q53 : Eqn
  q53 = sE 1739 lem-pass-CZ12-vs-CSd23
  q54 : Eqn
  q54 = sE 1737 lem-pass-CZ01-vs-CSd23
  q55 : Eqn
  q55 = sE 1741 lem-pass-CCZ013-vs-TOFF201
  q56 : Eqn
  q56 = wE 1992 W
  q57 : Eqn
  q57 = wE 1877 W
  q58 : Eqn
  q58 = wE 32 W

-- pass [CZ12 CCZ123] [CS23 TOFF201 CSd23 TOFF201]: 806 steps
lem-pass-CZ12-CCZ123-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (CZ12 ∷ CCZ123 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CZ12-CCZ123-vs-CS23-TOFF201-CSd23-TOFF201 = derive (CZ12 ∷ CCZ123 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ CZ12 ∷ CCZ123 ∷ [])
  (rw 1 q1 ∷
   rw 0 q2 ∷
   rw 2 q3 ∷
   rw 6 q4 ∷
   re 5 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 12 q5 ∷
   rw⁻ 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw⁻ 5 q6 ∷
   rw 6 q11 ∷
   re 6 8 (Toff201 ∷ []) ∷
   re 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q10 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 7 q13 ∷
   rw⁻ 6 q14 ∷
   rw 5 q13 ∷
   rw⁻ 4 q15 ∷
   rw 5 q4 ∷
   rw 6 q15 ∷
   rw 7 q16 ∷
   rw 8 q14 ∷
   rw 9 q16 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q17 ∷
   rw 12 q12 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw 6 q18 ∷
   re 6 5 (CCZ123 ∷ []) ∷
   re 5 3 (CCZ023 ∷ []) ∷
   re 3 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 10 q5 ∷
   rw⁻ 9 q6 ∷
   rw 8 q7 ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw 5 q8 ∷
   rw 4 q10 ∷
   rw⁻ 3 q6 ∷
   rw 4 q11 ∷
   re 4 8 (Toff201 ∷ []) ∷
   rw 7 q19 ∷
   re 6 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   re 11 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 13 q22 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q24 ∷
   rw 6 q21 ∷
   rw 7 q25 ∷
   re 7 8 (Toff102 ∷ []) ∷
   re 5 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q28 ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q29 ∷
   rw 11 q30 ∷
   rw 9 q31 ∷
   re 10 5 (CS03 ∷ []) ∷
   re 8 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q22 ∷
   rw 7 q32 ∷
   re 6 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q22 ∷
   rw 5 q33 ∷
   rw 6 q34 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q35 ∷
   rw⁻ 8 q36 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw⁻ 10 q36 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw 7 q37 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 6 3 (CCZ013 ∷ []) ∷
   re 4 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   re 9 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 11 q22 ∷
   rw 8 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 7 q23 ∷
   rw 6 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   rw 5 q24 ∷
   rw 4 q21 ∷
   rw 5 q25 ∷
   re 5 8 (Toff102 ∷ []) ∷
   rw 8 q4 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 14 q5 ∷
   rw 13 q38 ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw 7 q38 ∷
   rw 8 q39 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q34 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q36 ∷
   rw 10 q34 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q36 ∷
   rw 12 q34 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q35 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q7 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 9 q8 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q12 ∷
   rw 9 q9 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 7 q8 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q12 ∷
   rw 7 q10 ∷
   rw⁻ 6 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 7 q34 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q35 ∷
   rw⁻ 9 q40 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q35 ∷
   rw⁻ 11 q40 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q35 ∷
   rw 8 q41 ∷
   re 8 5 (CCZ012 ∷ []) ∷
   re 7 3 (CCZ013 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 12 q5 ∷
   rw 11 q38 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw 5 q38 ∷
   rw 6 q39 ∷
   re 6 8 (Toff012 ∷ []) ∷
   rw 6 q42 ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q34 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q36 ∷
   rw 10 q34 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q36 ∷
   rw 12 q34 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q35 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q12 ∷
   rw 6 q27 ∷
   rw 7 q12 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q43 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q44 ∷
   rw 9 q12 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q43 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q34 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q35 ∷
   rw⁻ 7 q40 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q35 ∷
   rw⁻ 9 q40 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q35 ∷
   rw 6 q41 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 6 q4 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q14 ∷
   rw 10 q16 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q17 ∷
   rw 13 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 6 3 (CCZ023 ∷ []) ∷
   rw 7 q28 ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q34 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw 9 q34 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q35 ∷
   rw 4 q45 ∷
   rw 7 q19 ∷
   re 5 3 (CX02 ∷ []) ∷
   rw 6 q46 ∷
   rw 9 q19 ∷
   re 7 3 (CX02 ∷ []) ∷
   re 9 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 8 q29 ∷
   rw⁻ 10 q30 ∷
   rw 11 q31 ∷
   re 8 5 (CS03 ∷ []) ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw 5 q18 ∷
   re 5 5 (CCZ123 ∷ []) ∷
   re 4 3 (CCZ023 ∷ []) ∷
   re 6 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q28 ∷
   rw 5 q47 ∷
   re 7 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 6 q22 ∷
   rw 7 q48 ∷
   re 9 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 8 q22 ∷
   re 10 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 9 q29 ∷
   rw⁻ 11 q30 ∷
   rw 12 q31 ∷
   re 9 5 (CS03 ∷ []) ∷
   rw 5 q34 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q35 ∷
   rw⁻ 7 q36 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q35 ∷
   rw⁻ 9 q36 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q35 ∷
   rw 6 q37 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   rw 6 q22 ∷
   re 4 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q28 ∷
   rw 3 q15 ∷
   rw 4 q16 ∷
   rw 5 q14 ∷
   rw 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q12 ∷
   rw 8 q17 ∷
   rw 9 q12 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 3 q18 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q34 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw 9 q34 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q35 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q12 ∷
   rw 5 q27 ∷
   rw 6 q12 ∷
   re 4 3 (CS03 ∷ []) ∷
   rw 5 q43 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q12 ∷
   rw 7 q44 ∷
   rw 8 q12 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q43 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q17 ∷
   rw 10 q12 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw 4 q34 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q35 ∷
   rw⁻ 6 q40 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q35 ∷
   rw⁻ 8 q40 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw 5 q41 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 5 q28 ∷
   rw 1 q49 ∷
   rw⁻ 4 q50 ∷
   rw 5 q51 ∷
   rw 4 q52 ∷
   rw 3 q53 ∷
   rw 2 q54 ∷
   rw 6 q3 ∷
   rw 10 q4 ∷
   re 9 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 16 q5 ∷
   rw⁻ 15 q6 ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q8 ∷
   rw 10 q10 ∷
   rw⁻ 9 q6 ∷
   rw 10 q11 ∷
   re 10 8 (Toff201 ∷ []) ∷
   re 8 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q12 ∷
   rw 13 q10 ∷
   rw⁻ 12 q12 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 11 q13 ∷
   rw⁻ 10 q14 ∷
   rw 9 q13 ∷
   rw⁻ 8 q15 ∷
   rw 9 q4 ∷
   rw 10 q15 ∷
   rw 11 q16 ∷
   rw 12 q14 ∷
   rw 13 q16 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   rw 15 q17 ∷
   rw 16 q12 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw 10 q18 ∷
   re 10 5 (CCZ123 ∷ []) ∷
   re 9 3 (CCZ023 ∷ []) ∷
   re 7 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 14 q5 ∷
   rw⁻ 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw⁻ 7 q6 ∷
   rw 8 q11 ∷
   re 8 8 (Toff201 ∷ []) ∷
   rw 11 q19 ∷
   re 10 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 17 q20 ∷
   rw 16 q21 ∷
   re 15 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 17 q22 ∷
   rw 14 q19 ∷
   re 15 3 (CX02 ∷ []) ∷
   rw 13 q23 ∷
   rw 12 q19 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q24 ∷
   rw 10 q21 ∷
   rw 11 q25 ∷
   re 11 8 (Toff102 ∷ []) ∷
   re 9 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 10 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 9 q15 ∷
   rw 10 q26 ∷
   rw 11 q14 ∷
   rw 12 q26 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   rw 14 q27 ∷
   rw 15 q12 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q28 ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 16 q29 ∷
   rw 15 q30 ∷
   rw 13 q31 ∷
   re 14 5 (CS03 ∷ []) ∷
   re 12 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 14 q22 ∷
   rw 11 q32 ∷
   re 10 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 12 q22 ∷
   rw 9 q33 ∷
   rw 10 q34 ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw⁻ 12 q36 ∷
   re 14 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q35 ∷
   rw⁻ 14 q36 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q35 ∷
   rw 11 q37 ∷
   re 11 5 (CCZ012 ∷ []) ∷
   re 10 3 (CCZ013 ∷ []) ∷
   re 8 1 (K2 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K2 ∷ ι ∷ []) ∷
   rw 15 q20 ∷
   rw 14 q21 ∷
   re 13 1 (Sw12 ∷ CS01 ∷ Sw12 ∷ []) ∷
   rw 15 q22 ∷
   rw 12 q19 ∷
   re 13 3 (CX02 ∷ []) ∷
   rw 11 q23 ∷
   rw 10 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   rw 9 q24 ∷
   rw 8 q21 ∷
   rw 9 q25 ∷
   re 9 8 (Toff102 ∷ []) ∷
   rw 12 q4 ∷
   re 11 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 18 q5 ∷
   rw 17 q38 ∷
   rw 16 q7 ∷
   rw 15 q8 ∷
   rw 14 q9 ∷
   rw 13 q8 ∷
   rw 12 q10 ∷
   rw 11 q38 ∷
   rw 12 q39 ∷
   re 12 8 (Toff012 ∷ []) ∷
   re 10 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 12 q34 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 11 q36 ∷
   rw 14 q34 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q36 ∷
   rw 16 q34 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q35 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 16 q12 ∷
   rw 15 q7 ∷
   rw⁻ 14 q12 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 13 q8 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 14 q12 ∷
   rw 13 q9 ∷
   rw⁻ 12 q12 ∷
   re 13 3 (CS03⁻ ∷ []) ∷
   rw 11 q8 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw⁻ 12 q12 ∷
   rw 11 q10 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 11 q34 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q35 ∷
   rw⁻ 13 q40 ∷
   re 15 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q35 ∷
   rw⁻ 15 q40 ∷
   re 17 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 16 q35 ∷
   rw 12 q41 ∷
   re 12 5 (CCZ012 ∷ []) ∷
   re 11 3 (CCZ013 ∷ []) ∷
   re 9 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw 16 q5 ∷
   rw 15 q38 ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q8 ∷
   rw 10 q10 ∷
   rw 9 q38 ∷
   rw 10 q39 ∷
   re 10 8 (Toff012 ∷ []) ∷
   rw 10 q42 ∷
   re 10 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 11 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 12 q34 ∷
   re 10 3 (CS13 ∷ []) ∷
   rw⁻ 11 q36 ∷
   rw 14 q34 ∷
   re 12 3 (CS13⁻ ∷ []) ∷
   rw⁻ 13 q36 ∷
   rw 16 q34 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q35 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q43 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q44 ∷
   rw 13 q12 ∷
   re 11 3 (CS03⁻ ∷ []) ∷
   rw 12 q43 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   rw 14 q17 ∷
   rw 15 q12 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q34 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q35 ∷
   rw⁻ 11 q40 ∷
   re 13 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q35 ∷
   rw⁻ 13 q40 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q35 ∷
   rw 10 q41 ∷
   re 10 5 (CCZ012 ∷ []) ∷
   re 9 3 (CCZ013 ∷ []) ∷
   re 11 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 10 q15 ∷
   rw 11 q26 ∷
   rw 12 q14 ∷
   rw 13 q26 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   rw 15 q27 ∷
   rw 16 q12 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 10 q4 ∷
   rw 11 q15 ∷
   rw 12 q16 ∷
   rw 13 q14 ∷
   rw 14 q16 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q12 ∷
   rw 16 q17 ∷
   rw 17 q12 ∷
   re 15 3 (CS13 ∷ []) ∷
   rw 11 q18 ∷
   re 11 5 (CCZ123 ∷ []) ∷
   re 10 3 (CCZ023 ∷ []) ∷
   rw 11 q28 ∷
   re 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 11 q34 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q36 ∷
   rw 13 q34 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q36 ∷
   rw 15 q34 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q35 ∷
   rw 8 q45 ∷
   rw 11 q19 ∷
   re 9 3 (CX02 ∷ []) ∷
   rw 10 q46 ∷
   rw 13 q19 ∷
   re 11 3 (CX02 ∷ []) ∷
   re 13 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 12 q29 ∷
   rw⁻ 14 q30 ∷
   rw 15 q31 ∷
   re 12 5 (CS03 ∷ []) ∷
   rw 8 q4 ∷
   rw 9 q15 ∷
   rw 10 q16 ∷
   rw 11 q14 ∷
   rw 12 q16 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q12 ∷
   rw 14 q17 ∷
   rw 15 q12 ∷
   re 13 3 (CS13 ∷ []) ∷
   rw 9 q18 ∷
   re 9 5 (CCZ123 ∷ []) ∷
   re 8 3 (CCZ023 ∷ []) ∷
   re 10 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 11 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 10 q15 ∷
   rw 11 q26 ∷
   rw 12 q14 ∷
   rw 13 q26 ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q12 ∷
   rw 15 q27 ∷
   rw 16 q12 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q28 ∷
   rw 9 q47 ∷
   re 11 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 10 q22 ∷
   rw 11 q48 ∷
   re 13 1 (Sw12 ∷ CX01 ∷ Sw12 ∷ []) ∷
   rw 12 q22 ∷
   re 14 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 13 q29 ∷
   rw⁻ 15 q30 ∷
   rw 16 q31 ∷
   re 13 5 (CS03 ∷ []) ∷
   rw 9 q34 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q35 ∷
   rw⁻ 11 q36 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q35 ∷
   rw⁻ 13 q36 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q35 ∷
   rw 10 q37 ∷
   re 10 5 (CCZ012 ∷ []) ∷
   re 9 3 (CCZ013 ∷ []) ∷
   rw 10 q22 ∷
   re 8 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 9 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 8 q15 ∷
   rw 9 q26 ∷
   rw 10 q14 ∷
   rw 11 q26 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q27 ∷
   rw 14 q12 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q28 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q14 ∷
   rw 10 q16 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q12 ∷
   rw 12 q17 ∷
   rw 13 q12 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw 7 q18 ∷
   re 7 5 (CCZ123 ∷ []) ∷
   re 9 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 10 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 11 q34 ∷
   re 9 3 (CS13 ∷ []) ∷
   rw⁻ 10 q36 ∷
   rw 13 q34 ∷
   re 11 3 (CS13⁻ ∷ []) ∷
   rw⁻ 12 q36 ∷
   rw 15 q34 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 14 q35 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q43 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q12 ∷
   rw 11 q44 ∷
   rw 12 q12 ∷
   re 10 3 (CS03⁻ ∷ []) ∷
   rw 11 q43 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q12 ∷
   rw 13 q17 ∷
   rw 14 q12 ∷
   re 12 3 (CS13 ∷ []) ∷
   rw 8 q34 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw⁻ 10 q40 ∷
   re 12 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw⁻ 12 q40 ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q35 ∷
   rw 9 q41 ∷
   re 9 5 (CCZ012 ∷ []) ∷
   re 8 3 (CCZ013 ∷ []) ∷
   rw 9 q28 ∷
   rw 5 q55 ∷
   rw 4 q49 ∷
   rw 3 q56 ∷
   rw⁻ 8 q50 ∷
   rw 4 q57 ∷
   rw 7 q34 ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q34 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q36 ∷
   rw 10 q34 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q36 ∷
   rw 12 q34 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q35 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q35 ∷
   rw 9 q36 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q35 ∷
   rw 7 q36 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q35 ∷
   rw 7 q37 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   re 5 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q34 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q36 ∷
   rw 9 q34 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 10 q35 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q35 ∷
   rw 8 q36 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q35 ∷
   rw 6 q36 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q35 ∷
   rw 6 q37 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   rw 6 q58 ∷
   rw 5 q35 ∷ []) Eq.refl
