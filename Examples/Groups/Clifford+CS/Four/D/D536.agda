{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD536 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D536 (W : Ws) (Sᴰ : SD536) where

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
  lem-CCZ013-T : St 809
  lem-CCZ013-T = pickᴰ 0 Sᴰ
  lem-CS13-passes-T : St 3
  lem-CS13-passes-T = pickᴰ 1 Sᴰ
  lem-N32-T : St 810
  lem-N32-T = pickᴰ 2 Sᴰ
  lem-comm-CCZ123-CS03 : St 54
  lem-comm-CCZ123-CS03 = pickᴰ 3 Sᴰ
  lem-comm-CCZ012-CZ13 : St 573
  lem-comm-CCZ012-CZ13 = pickᴰ 4 Sᴰ
  lem-comm-CCZ012-CCZ023 : St 811
  lem-comm-CCZ012-CCZ023 = pickᴰ 5 Sᴰ
  lem-pass-CCZ012-vs-CS12 : St 812
  lem-pass-CCZ012-vs-CS12 = pickᴰ 6 Sᴰ
  lem-pass-CCZ012-vs-CSd12 : St 813
  lem-pass-CCZ012-vs-CSd12 = pickᴰ 7 Sᴰ
  lem-pass-CCZ012-vs-CZ12 : St 814
  lem-pass-CCZ012-vs-CZ12 = pickᴰ 8 Sᴰ
  lem-pass-CCZ013-vs-CZ01 : St 815
  lem-pass-CCZ013-vs-CZ01 = pickᴰ 9 Sᴰ
  lem-pass-CS02-vs-CS03 : St 59
  lem-pass-CS02-vs-CS03 = pickᴰ 10 Sᴰ
  lem-pass-CS02-vs-CSd03 : St 816
  lem-pass-CS02-vs-CSd03 = pickᴰ 11 Sᴰ
  lem-pass-CS12-vs-CS03 : St 21
  lem-pass-CS12-vs-CS03 = pickᴰ 12 Sᴰ
  lem-pass-CSd02-vs-CS03 : St 60
  lem-pass-CSd02-vs-CS03 = pickᴰ 13 Sᴰ
  lem-pass-CSd02-vs-CSd03 : St 817
  lem-pass-CSd02-vs-CSd03 = pickᴰ 14 Sᴰ
  lem-pass-CSd12-vs-CS03 : St 55
  lem-pass-CSd12-vs-CS03 = pickᴰ 15 Sᴰ
  lem-pass-S0-vs-CS03 : St 62
  lem-pass-S0-vs-CS03 = pickᴰ 16 Sᴰ
  lem-pass-S0-vs-CSd03 : St 818
  lem-pass-S0-vs-CSd03 = pickᴰ 17 Sᴰ
  lem-E-T : St 819
  lem-E-T = pickᴰ 18 Sᴰ
  lem-T-T13 : St 820
  lem-T-T13 = pickᴰ 19 Sᴰ
  lem-T1-CZ13-T1 : St 821
  lem-T1-CZ13-T1 = pickᴰ 20 Sᴰ
  lem-pass-CCZ012-vs-CS03 : St 822
  lem-pass-CCZ012-vs-CS03 = pickᴰ 21 Sᴰ
  lem-pass-CCZ013-vs-CCZ012 : St 823
  lem-pass-CCZ013-vs-CCZ012 = pickᴰ 22 Sᴰ
  lem-pass-CCZ023-vs-CCZ012 : St 824
  lem-pass-CCZ023-vs-CCZ012 = pickᴰ 23 Sᴰ

private
  q1 : Eqn
  q1 = eqn [] (CX32 ∷ CX32 ∷ []) (wn 105 W)
  q2 : Eqn
  q2 = eqn (CX32 ∷ Toff012 ∷ CX32 ∷ []) (Toff012 ∷ Toff013 ∷ []) (lem-N32-T)
  q3 : Eqn
  q3 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q4 : Eqn
  q4 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q5 : Eqn
  q5 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q7 : Eqn
  q7 = eqn (CX32 ∷ CS13 ∷ CX32 ∷ []) (CS13 ∷ []) (wn 1433 W)
  q8 : Eqn
  q8 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q9 : Eqn
  q9 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q10 : Eqn
  q10 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q11 : Eqn
  q11 = eqn (CX32 ∷ CS13⁻ ∷ CX32 ∷ []) (CS13⁻ ∷ []) (wn 1434 W)
  q12 : Eqn
  q12 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q13 : Eqn
  q13 = eqn (Toff012 ∷ Toff013 ∷ []) (Toff013 ∷ Toff012 ∷ []) (lem-T-T13)
  q14 : Eqn
  q14 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q15 : Eqn
  q15 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q16 : Eqn
  q16 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q17 : Eqn
  q17 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q18 : Eqn
  q18 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q19 : Eqn
  q19 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q20 : Eqn
  q20 = eqn (Toff012 ∷ CS02 ∷ Toff012 ∷ []) (CS12 ∷ CCZ012 ∷ CS02 ∷ []) (wn 1435 W)
  q21 : Eqn
  q21 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q22 : Eqn
  q22 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q23 : Eqn
  q23 = eqn (CS13 ∷ Toff012 ∷ []) (Toff012 ∷ CS13 ∷ []) lem-CS13-passes-T
  q24 : Eqn
  q24 = eqn (Toff012 ∷ CCZ013 ∷ Toff012 ∷ []) (CCZ013 ∷ CCZ123 ∷ []) (ax toff-ccz)

-- N32-PP3: 123 steps
lem-N32-PP3 : ⟪ (CX32 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX32 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ CCZ013 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-N32-PP3 = derive (CX32 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CX32 ∷ []) (CS13 ∷ CCZ013 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw 4 q1 ∷
   rw 3 q1 ∷
   rw 2 q1 ∷
   rw 0 q2 ∷
   rw 5 q3 ∷
   rw⁻ 4 q4 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q5 ∷
   rw 4 q6 ∷
   rw⁻ 3 q5 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 3 q7 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q5 ∷
   rw 3 q8 ∷
   rw 4 q5 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q9 ∷
   rw 3 q2 ∷
   rw 8 q3 ∷
   rw⁻ 7 q4 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 7 q10 ∷
   rw⁻ 6 q5 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 6 q11 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q12 ∷
   rw 7 q5 ∷
   re 5 3 (CS03⁻ ∷ []) ∷
   rw 6 q9 ∷
   rw 3 q13 ∷
   rw 4 q14 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q15 ∷
   rw 6 q14 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q16 ∷
   rw 10 q14 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q17 ∷
   rw 11 q18 ∷
   rw 10 q17 ∷
   rw 9 q15 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q18 ∷
   rw 7 q16 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q16 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 3 q15 ∷
   rw 4 q19 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   re 1 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q15 ∷
   rw 4 q14 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q17 ∷
   rw 9 q18 ∷
   rw 8 q17 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q16 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 3 q16 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   rw 1 q15 ∷
   rw 2 q19 ∷
   re 2 8 (Toff012 ∷ []) ∷
   rw 2 q20 ∷
   rw 3 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q14 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q14 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 3 q21 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 5 q14 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q22 ∷
   rw⁻ 0 q23 ∷
   rw 1 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = eqn (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ []) (lem-E-T)

-- CCZ123 passes T: 1 steps
lem-CCZ123-passes-T : ⟪ (CCZ123 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CCZ123 ∷ []) ⟫ʷ
lem-CCZ123-passes-T = derive (CCZ123 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ123 ∷ [])
  (rw 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (CCZ013 ∷ Toff012 ∷ []) (Toff012 ∷ CCZ013 ∷ CCZ123 ∷ []) (lem-CCZ013-T)
  q27 : Eqn
  q27 = eqn (CCZ123 ∷ CS03 ∷ []) (CS03 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CS03)
  q28 : Eqn
  q28 = eqn (CCZ012 ∷ CS02 ∷ []) (CS02 ∷ CCZ012 ∷ []) (wn 251 W)
  q29 : Eqn
  q29 = eqn (CCZ123 ∷ CCZ123 ∷ []) [] (wn 33 W)
  q30 : Eqn
  q30 = eqn (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ []) (wn 254 W)

-- CCZ013 passes PP3: 103 steps
lem-CCZ013-passes-PP3 : ⟪ (CCZ013 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ []) ⟫ʷ
lem-CCZ013-passes-PP3 = derive (CCZ013 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ013 ∷ [])
  (rw 0 q26 ∷
   rw 2 q27 ∷
   rw 3 q14 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   re 1 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q18 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 4 q16 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw 2 q16 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   rw 2 q21 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   rw 2 q28 ∷
   rw 3 q14 ∷
   re 1 3 (CS03 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q14 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 2 q14 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 3 q21 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   re 2 3 (CCZ013 ∷ []) ∷
   rw 3 q18 ∷
   rw 3 q25 ∷
   rw 2 q26 ∷
   rw 4 q29 ∷
   rw 5 q14 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   re 3 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q14 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q16 ∷
   rw 9 q14 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 8 q18 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   rw 6 q16 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 4 q16 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw 4 q21 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   rw 4 q30 ∷
   rw 5 q14 ∷
   re 3 3 (CS03⁻ ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q14 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q16 ∷
   rw 10 q14 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 4 q14 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   rw 5 q21 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 4 3 (CCZ013 ∷ []) ∷
   rw 5 q18 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = eqn (Toff102 ∷ CZ13 ∷ Toff102 ∷ []) (CCZ023 ∷ CZ13 ∷ []) (lem-T1-CZ13-T1)
  q32 : Eqn
  q32 = eqn (CCZ012 ∷ CCZ023 ∷ []) (CCZ023 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CCZ023)
  q33 : Eqn
  q33 = eqn (CCZ012 ∷ CZ13 ∷ []) (CZ13 ∷ CCZ012 ∷ []) (lem-comm-CCZ012-CZ13)
  q34 : Eqn
  q34 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q35 : Eqn
  q35 = eqn (CZ13 ∷ CZ13 ∷ []) [] (wn 1436 W)

-- B=F: 5 steps
lem-B≡F : ⟪ (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ []) ⟫ʷ
lem-B≡F = derive (CCZ012 ∷ Toff102 ∷ CZ13 ∷ Toff102 ∷ CCZ012 ∷ CZ13 ∷ []) (CCZ023 ∷ [])
  (rw 1 q31 ∷
   rw 0 q32 ∷
   rw 1 q33 ∷
   rw 2 q34 ∷
   rw 1 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (wn 53 W)
  q37 : Eqn
  q37 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q38 : Eqn
  q38 = eqn (K0⁻ ∷ K0 ∷ []) [] (wn 1339 W)
  q39 : Eqn
  q39 = eqn (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CCZ012)
  q40 : Eqn
  q40 = eqn [] (K0⁻ ∷ K0 ∷ []) (wn 54 W)
  q41 : Eqn
  q41 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wn 55 W)

-- pass [TOFF013] [TOFF012]: 111 steps
lem-pass-TOFF013-vs-TOFF012 : ⟪ (Toff013 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff013 ∷ []) ⟫ʷ
lem-pass-TOFF013-vs-TOFF012 = derive (Toff013 ∷ Toff012 ∷ []) (Toff012 ∷ Toff013 ∷ [])
  (rw 1 q36 ∷
   rw 1 q14 ∷
   re 0 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q15 ∷
   rw 3 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw⁻ 7 q17 ∷
   rw 8 q18 ∷
   rw 7 q17 ∷
   rw 6 q15 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 4 q16 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw 2 q16 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   rw 0 q15 ∷
   rw 1 q19 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q36 ∷
   rw⁻ 0 q15 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q18 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 2 q21 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q37 ∷
   rw 3 q18 ∷
   rw 2 q38 ∷
   rw 1 q39 ∷
   rw 2 q40 ∷
   rw 0 q41 ∷
   rw 4 q14 ∷
   rw 3 q37 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q14 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q18 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q16 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 3 q16 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   rw 3 q21 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q15 ∷
   rw 2 q41 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q15 ∷
   rw 4 q14 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q16 ∷
   rw 6 q14 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw⁻ 8 q17 ∷
   rw 1 q14 ∷
   rw⁻ 2 q15 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   rw⁻ 4 q16 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw⁻ 8 q15 ∷
   rw⁻ 9 q17 ∷
   rw 2 q19 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q18 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q43 : Eqn
  q43 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q44 : Eqn
  q44 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q45 : Eqn
  q45 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q46 : Eqn
  q46 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q47 : Eqn
  q47 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q48 : Eqn
  q48 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q49 : Eqn
  q49 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q50 : Eqn
  q50 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q51 : Eqn
  q51 = eqn (Toff123 ∷ []) (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (wn 128 W)
  q52 : Eqn
  q52 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q53 : Eqn
  q53 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q54 : Eqn
  q54 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q55 : Eqn
  q55 = eqn (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) (wn 129 W)
  q56 : Eqn
  q56 = eqn (CCZ023 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CCZ012)
  q57 : Eqn
  q57 = eqn (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) (wn 119 W)
  q58 : Eqn
  q58 = eqn (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (Toff123 ∷ []) (wn 1437 W)
  q59 : Eqn
  q59 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q60 : Eqn
  q60 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)

-- pass [TOFF023] [TOFF012]: 119 steps
lem-pass-TOFF023-vs-TOFF012 : ⟪ (Toff023 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ Toff023 ∷ []) ⟫ʷ
lem-pass-TOFF023-vs-TOFF012 = derive (Toff023 ∷ Toff012 ∷ []) (Toff012 ∷ Toff023 ∷ [])
  (rw 1 q36 ∷
   rw 1 q3 ∷
   re 0 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q42 ∷
   rw 1 q43 ∷
   rw 2 q44 ∷
   rw 3 q45 ∷
   rw 4 q44 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q8 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q42 ∷
   rw 7 q46 ∷
   rw 8 q9 ∷
   rw 7 q47 ∷
   rw 6 q48 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q5 ∷
   rw 6 q6 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q49 ∷
   rw⁻ 3 q45 ∷
   rw 2 q49 ∷
   rw⁻ 1 q43 ∷
   rw 0 q48 ∷
   rw 1 q50 ∷
   re 1 8 (Toff123 ∷ []) ∷
   rw 1 q51 ∷
   rw 0 q42 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q43 ∷
   rw 2 q44 ∷
   rw 3 q45 ∷
   rw 4 q44 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q5 ∷
   rw 6 q8 ∷
   rw 7 q5 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q43 ∷
   rw 3 q52 ∷
   rw 4 q45 ∷
   rw 5 q52 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q53 ∷
   rw 8 q5 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q54 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q55 ∷
   rw 3 q9 ∷
   rw 2 q38 ∷
   rw 1 q56 ∷
   rw 2 q40 ∷
   rw 0 q41 ∷
   rw 4 q3 ∷
   rw 3 q57 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q43 ∷
   rw 3 q44 ∷
   rw 4 q45 ∷
   rw 5 q44 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q8 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q9 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q5 ∷
   rw 7 q6 ∷
   rw⁻ 6 q5 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q49 ∷
   rw⁻ 4 q45 ∷
   rw 3 q49 ∷
   rw⁻ 2 q43 ∷
   rw 3 q54 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 1 q48 ∷
   rw 2 q58 ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q42 ∷
   rw 2 q43 ∷
   rw 3 q44 ∷
   rw 4 q45 ∷
   rw 5 q44 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q5 ∷
   rw 7 q8 ∷
   rw 8 q5 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q42 ∷
   rw 8 q46 ∷
   rw 1 q3 ∷
   rw 2 q59 ∷
   rw 3 q43 ∷
   rw 4 q52 ∷
   rw 5 q45 ∷
   rw 6 q52 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q5 ∷
   rw 8 q53 ∷
   rw 9 q5 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q59 ∷
   rw 9 q60 ∷
   rw 2 q50 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (CCZ013 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ013 ∷ []) lem-pass-CCZ013-vs-CCZ012

-- pass [CCZ012] [CCZ013]: 1 steps
lem-pass-CCZ012-vs-CCZ013 : ⟪ (CCZ012 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-CCZ013 = derive (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ [])
  (rw⁻ 0 q61 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (CS02 ∷ Toff012 ∷ []) (Toff012 ∷ CS02 ∷ CS12 ∷ CCZ012 ∷ []) (wn 469 W)
  q63 : Eqn
  q63 = eqn (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS03)
  q64 : Eqn
  q64 = eqn (CS12 ∷ CS03 ∷ []) (CS03 ∷ CS12 ∷ []) (lem-pass-CS12-vs-CS03)
  q65 : Eqn
  q65 = eqn (CS02 ∷ CS03 ∷ []) (CS03 ∷ CS02 ∷ []) (lem-pass-CS02-vs-CS03)
  q66 : Eqn
  q66 = eqn (CCZ012 ∷ Toff012 ∷ []) (Toff012 ∷ CZ12 ∷ CCZ012 ∷ []) (wn 466 W)
  q67 : Eqn
  q67 = eqn (CS12 ∷ Toff012 ∷ []) (Toff012 ∷ CS12 ∷ []) (wn 90 W)
  q68 : Eqn
  q68 = eqn (CCZ012 ∷ CS12 ∷ []) (CS12 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS12)
  q69 : Eqn
  q69 = eqn (CCZ012 ∷ CZ12 ∷ []) (CZ12 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ12)
  q70 : Eqn
  q70 = eqn (CS12 ∷ CS12 ∷ CZ12 ∷ []) [] (wn 1438 W)
  q71 : Eqn
  q71 = eqn (CS02 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS02 ∷ []) (lem-pass-CS02-vs-CSd03)

-- pass [CS02] [TOFF012 CS03 TOFF012 CSd03]: 12 steps
lem-pass-CS02-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CS02 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CS02 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS02 ∷ [])
  (rw 0 q62 ∷
   rw 3 q63 ∷
   rw 2 q64 ∷
   rw 1 q65 ∷
   rw 4 q66 ∷
   rw 3 q67 ∷
   rw 2 q62 ∷
   rw 5 q68 ∷
   rw 6 q69 ∷
   rw 4 q70 ∷
   rw 4 q34 ∷
   rw 3 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = eqn (CS02⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS02⁻ ∷ CS12⁻ ∷ CCZ012 ∷ []) (wn 1439 W)
  q73 : Eqn
  q73 = eqn (CS12⁻ ∷ CS03 ∷ []) (CS03 ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-CS03)
  q74 : Eqn
  q74 = eqn (CS02⁻ ∷ CS03 ∷ []) (CS03 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CS03)
  q75 : Eqn
  q75 = eqn (CS12⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS12⁻ ∷ []) (wn 468 W)
  q76 : Eqn
  q76 = eqn (CCZ012 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd12)
  q77 : Eqn
  q77 = eqn (CS12⁻ ∷ CS12⁻ ∷ CZ12 ∷ []) [] (wn 1440 W)
  q78 : Eqn
  q78 = eqn (CS02⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CSd03)

-- pass [CSd02] [TOFF012 CS03 TOFF012 CSd03]: 12 steps
lem-pass-CSd02-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CS02⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CS02⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS02⁻ ∷ [])
  (rw 0 q72 ∷
   rw 3 q63 ∷
   rw 2 q73 ∷
   rw 1 q74 ∷
   rw 4 q66 ∷
   rw 3 q75 ∷
   rw 2 q72 ∷
   rw 5 q76 ∷
   rw 6 q69 ∷
   rw 4 q77 ∷
   rw 4 q34 ∷
   rw 3 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = eqn (X2 ∷ Toff012 ∷ X2 ∷ []) (K0 ∷ CZ01 ∷ CCZ012 ∷ K0⁻ ∷ []) (wn 1441 W)
  q80 : Eqn
  q80 = eqn (CCZ013 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CZ01)
  q81 : Eqn
  q81 = eqn (K0 ∷ CZ01 ∷ CCZ012 ∷ K0⁻ ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ []) (wn 1442 W)

-- pass [TOFF013] [X2 TOFF012 X2]: 112 steps
lem-pass-TOFF013-vs-X2-TOFF012-X2 : ⟪ (Toff013 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff012 ∷ X2 ∷ Toff013 ∷ []) ⟫ʷ
lem-pass-TOFF013-vs-X2-TOFF012-X2 = derive (Toff013 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff013 ∷ [])
  (rw 1 q79 ∷
   rw 1 q14 ∷
   re 0 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q15 ∷
   rw 3 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw⁻ 7 q17 ∷
   rw 8 q18 ∷
   rw 7 q17 ∷
   rw 6 q15 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw 4 q16 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw 2 q16 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q18 ∷
   rw 0 q15 ∷
   rw 1 q19 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q36 ∷
   rw⁻ 0 q15 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q14 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q16 ∷
   rw 5 q14 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q16 ∷
   rw 7 q14 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q14 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q18 ∷
   rw⁻ 3 q16 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q18 ∷
   rw⁻ 5 q16 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 2 q21 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q37 ∷
   rw 3 q18 ∷
   rw 2 q38 ∷
   rw 1 q80 ∷
   rw 2 q39 ∷
   rw 3 q40 ∷
   rw 0 q81 ∷
   rw 6 q14 ∷
   rw 5 q37 ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q14 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q16 ∷
   rw 10 q14 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q18 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q18 ∷
   rw 7 q16 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q18 ∷
   rw 5 q16 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q18 ∷
   rw 5 q21 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   rw 3 q15 ∷
   rw 4 q41 ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q15 ∷
   rw 6 q14 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q16 ∷
   rw 8 q14 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q16 ∷
   rw 10 q14 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q15 ∷
   rw⁻ 10 q17 ∷
   rw 3 q14 ∷
   rw⁻ 4 q15 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q18 ∷
   rw⁻ 6 q16 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q18 ∷
   rw⁻ 8 q16 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q18 ∷
   rw⁻ 10 q15 ∷
   rw⁻ 11 q17 ∷
   rw 4 q19 ∷
   re 4 8 (Toff012 ∷ []) ∷
   re 3 3 (Toff013 ∷ []) ∷
   rw 4 q18 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = eqn (S0 ∷ Toff012 ∷ []) (Toff012 ∷ S0 ∷ CS12 ∷ CCZ012 ∷ []) (wn 1443 W)
  q83 : Eqn
  q83 = eqn (S0 ∷ CS03 ∷ []) (CS03 ∷ S0 ∷ []) (lem-pass-S0-vs-CS03)
  q84 : Eqn
  q84 = eqn (S0 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ S0 ∷ []) (lem-pass-S0-vs-CSd03)

-- pass [S0] [TOFF012 CS03 TOFF012 CSd03]: 12 steps
lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF012-CS03-TOFF012-CSd03 = derive (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ S0 ∷ [])
  (rw 0 q82 ∷
   rw 3 q63 ∷
   rw 2 q64 ∷
   rw 1 q83 ∷
   rw 4 q66 ∷
   rw 3 q67 ∷
   rw 2 q82 ∷
   rw 5 q68 ∷
   rw 6 q69 ∷
   rw 4 q70 ∷
   rw 4 q34 ∷
   rw 3 q84 ∷ []) Eq.refl
