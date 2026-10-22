{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD538 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D538 (W : Ws) (Sᴰ : SD538) where

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
  lem-pass-CCZ012-vs-CS12 : St 812
  lem-pass-CCZ012-vs-CS12 = pickᴰ 0 Sᴰ
  lem-pass-CCZ012-vs-CSd12 : St 813
  lem-pass-CCZ012-vs-CSd12 = pickᴰ 1 Sᴰ
  lem-pass-CCZ012-vs-CZ12 : St 814
  lem-pass-CCZ012-vs-CZ12 = pickᴰ 2 Sᴰ
  lem-pass-CCZ013-vs-CZ01 : St 815
  lem-pass-CCZ013-vs-CZ01 = pickᴰ 3 Sᴰ
  lem-pass-CS02-vs-CS03 : St 59
  lem-pass-CS02-vs-CS03 = pickᴰ 4 Sᴰ
  lem-pass-CS02-vs-CSd03 : St 816
  lem-pass-CS02-vs-CSd03 = pickᴰ 5 Sᴰ
  lem-pass-CS12-vs-CS03 : St 21
  lem-pass-CS12-vs-CS03 = pickᴰ 6 Sᴰ
  lem-pass-CSd02-vs-CS03 : St 60
  lem-pass-CSd02-vs-CS03 = pickᴰ 7 Sᴰ
  lem-pass-CSd02-vs-CSd03 : St 817
  lem-pass-CSd02-vs-CSd03 = pickᴰ 8 Sᴰ
  lem-pass-CSd12-vs-CS03 : St 55
  lem-pass-CSd12-vs-CS03 = pickᴰ 9 Sᴰ
  lem-pass-S0-vs-CS03 : St 62
  lem-pass-S0-vs-CS03 = pickᴰ 10 Sᴰ
  lem-pass-S0-vs-CSd03 : St 818
  lem-pass-S0-vs-CSd03 = pickᴰ 11 Sᴰ
  lem-pass-Sd0-vs-CS03 : St 176
  lem-pass-Sd0-vs-CS03 = pickᴰ 12 Sᴰ
  lem-pass-Sd0-vs-CSd03 : St 825
  lem-pass-Sd0-vs-CSd03 = pickᴰ 13 Sᴰ
  lem-pass-CCZ013-vs-Z0 : St 827
  lem-pass-CCZ013-vs-Z0 = pickᴰ 14 Sᴰ
  lem-pass-CZ12-vs-CS03 : St 574
  lem-pass-CZ12-vs-CS03 = pickᴰ 15 Sᴰ
  lem-D-b : St 828
  lem-D-b = pickᴰ 16 Sᴰ
  lem-pass-CS12-vs-CSd03 : St 34
  lem-pass-CS12-vs-CSd03 = pickᴰ 17 Sᴰ
  lem-pass-CSd12-vs-CSd03 : St 56
  lem-pass-CSd12-vs-CSd03 = pickᴰ 18 Sᴰ
  lem-pass-CCZ012-vs-CS03 : St 822
  lem-pass-CCZ012-vs-CS03 = pickᴰ 19 Sᴰ
  lem-pass-CCZ012-vs-CS13 : St 829
  lem-pass-CCZ012-vs-CS13 = pickᴰ 20 Sᴰ
  lem-pass-CCZ012-vs-CSd03 : St 830
  lem-pass-CCZ012-vs-CSd03 = pickᴰ 21 Sᴰ
  lem-pass-CCZ012-vs-CSd13 : St 831
  lem-pass-CCZ012-vs-CSd13 = pickᴰ 22 Sᴰ
  lem-pass-CCZ013-vs-CCZ012 : St 823
  lem-pass-CCZ013-vs-CCZ012 = pickᴰ 23 Sᴰ
  lem-pass-CCZ013-vs-CS02 : St 826
  lem-pass-CCZ013-vs-CS02 = pickᴰ 24 Sᴰ
  lem-pass-CCZ013-vs-CS12 : St 832
  lem-pass-CCZ013-vs-CS12 = pickᴰ 25 Sᴰ
  lem-pass-CCZ013-vs-CSd12 : St 833
  lem-pass-CCZ013-vs-CSd12 = pickᴰ 26 Sᴰ
  lem-pass-CCZ013-vs-CZ02 : St 834
  lem-pass-CCZ013-vs-CZ02 = pickᴰ 27 Sᴰ
  lem-pass-CS02-vs-TOFF102-CS13-TOFF102-CSd13 : St 835
  lem-pass-CS02-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 28 Sᴰ
  lem-pass-CS12-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 : St 836
  lem-pass-CS12-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0 = pickᴰ 29 Sᴰ
  lem-pass-CSd02-vs-TOFF102-CS13-TOFF102-CSd13 : St 837
  lem-pass-CSd02-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 30 Sᴰ
  lem-pass-S2-vs-TOFF102-CS13-TOFF102-CSd13 : St 838
  lem-pass-S2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 31 Sᴰ
  lem-pass-Sd2-vs-TOFF102-CS13-TOFF102-CSd13 : St 839
  lem-pass-Sd2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 32 Sᴰ
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 840
  lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 33 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 841
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 34 Sᴰ
  lem-pass-CCZ013-vs-CSd02 : St 842
  lem-pass-CCZ013-vs-CSd02 = pickᴰ 35 Sᴰ
  lem-pass-CCZ123-vs-CS03 : St 843
  lem-pass-CCZ123-vs-CS03 = pickᴰ 36 Sᴰ
  lem-pass-CS12-vs-TOFF012-CS03-TOFF012-CSd03 : St 844
  lem-pass-CS12-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 37 Sᴰ
  lem-pass-CSd12-vs-TOFF012-CS03-TOFF012-CSd03 : St 845
  lem-pass-CSd12-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 38 Sᴰ
  lem-pass-CCZ012-vs-CCZ123 : St 846
  lem-pass-CCZ012-vs-CCZ123 = pickᴰ 39 Sᴰ

private
  q1 : Eqn
  q1 = wE 1446 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 56 W
  q8 : Eqn
  q8 = wE 53 W
  q9 : Eqn
  q9 = wE 43 W
  q10 : Eqn
  q10 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q11 : Eqn
  q11 = wE 1339 W
  q12 : Eqn
  q12 = sE 827 lem-pass-CCZ013-vs-Z0
  q13 : Eqn
  q13 = sE 815 lem-pass-CCZ013-vs-CZ01
  q14 : Eqn
  q14 = sE 834 lem-pass-CCZ013-vs-CZ02
  q15 : Eqn
  q15 = sE 823 lem-pass-CCZ013-vs-CCZ012
  q16 : Eqn
  q16 = wE 54 W
  q17 : Eqn
  q17 = wE 1447 W
  q18 : Eqn
  q18 = wE 55 W

-- pass [TOFF013] [X1 X2 TOFF012 X1 X2]: 114 steps
lem-pass-TOFF013-vs-X1-X2-TOFF012-X1-X2 : ⟪ (Toff013 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff013 ∷ []) ⟫ʷ
lem-pass-TOFF013-vs-X1-X2-TOFF012-X1-X2 = derive (Toff013 ∷ X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ Toff013 ∷ [])
  (rw 1 q1 ∷
   rw 1 q2 ∷
   re 0 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q5 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q3 ∷
   rw 1 q7 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q8 ∷
   rw⁻ 0 q3 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 2 q9 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q10 ∷
   rw 3 q6 ∷
   rw 2 q11 ∷
   rw 1 q12 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   rw 5 q16 ∷
   rw 0 q17 ∷
   rw 8 q2 ∷
   rw 7 q10 ∷
   re 6 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 7 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 11 q6 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw 9 q4 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q9 ∷
   re 7 5 (CCZ012 ∷ []) ∷
   rw 5 q3 ∷
   rw 6 q18 ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q2 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 5 q2 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q5 ∷
   rw 6 q7 ∷
   re 6 8 (Toff012 ∷ []) ∷
   re 5 3 (Toff013 ∷ []) ∷
   rw 6 q6 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (K0⁻ ∷ CS12 ∷ []) (CS12 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (CS))
  q20 : Eqn
  q20 = sE 832 lem-pass-CCZ013-vs-CS12
  q21 : Eqn
  q21 = eqn (K0 ∷ CS12 ∷ []) (CS12 ∷ K0 ∷ []) (low₁-comm (K) (CS))

-- pass [TOFF013] [CS12]: 109 steps
lem-pass-TOFF013-vs-CS12 : ⟪ (Toff013 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff013 ∷ []) ⟫ʷ
lem-pass-TOFF013-vs-CS12 = derive (Toff013 ∷ CS12 ∷ []) (CS12 ∷ Toff013 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q5 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q3 ∷
   rw 1 q7 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q8 ∷
   rw⁻ 0 q3 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 2 q9 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q10 ∷
   rw 3 q6 ∷
   rw 2 q19 ∷
   rw 1 q20 ∷
   rw 0 q21 ∷
   rw 4 q2 ∷
   rw 3 q10 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 3 q9 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q18 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q2 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q6 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (K0⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((CS • CS • CS)))
  q23 : Eqn
  q23 = sE 833 lem-pass-CCZ013-vs-CSd12
  q24 : Eqn
  q24 = eqn (K0 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ K0 ∷ []) (low₁-comm (K) ((CS • CS • CS)))

-- pass [TOFF013] [CSd12]: 109 steps
lem-pass-TOFF013-vs-CSd12 : ⟪ (Toff013 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff013 ∷ []) ⟫ʷ
lem-pass-TOFF013-vs-CSd12 = derive (Toff013 ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff013 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q3 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q5 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q3 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q3 ∷
   rw 1 q7 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q8 ∷
   rw⁻ 0 q3 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 2 q9 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q10 ∷
   rw 3 q6 ∷
   rw 2 q22 ∷
   rw 1 q23 ∷
   rw 0 q24 ∷
   rw 4 q2 ∷
   rw 3 q10 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 3 q9 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q3 ∷
   rw 2 q18 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q3 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q2 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q6 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 835 lem-pass-CS02-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CS02]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS02 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02 ∷ []) (CS02 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 837 lem-pass-CSd02-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CSd02]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd02 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1347 W
  q28 : Eqn
  q28 = eqn (K1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap))
  q29 : Eqn
  q29 = wE 1448 W
  q30 : Eqn
  q30 = sE 830 lem-pass-CCZ012-vs-CSd03
  q31 : Eqn
  q31 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q32 : Eqn
  q32 = wE 1449 W
  q33 : Eqn
  q33 = wE 1450 W

-- pass [TOFF102] [CSd03]: 21 steps
lem-pass-TOFF102-vs-CSd03 : ⟪ (Toff102 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS03⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-CSd03 = derive (Toff102 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff102 ∷ [])
  (rw 0 q27 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q28 ∷
   rw 3 q29 ∷
   rw 4 q2 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw⁻ 3 q28 ∷
   rw 4 q6 ∷
   rw 1 q30 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q31 ∷
   rw 1 q32 ∷
   rw 2 q2 ∷
   re 0 3 (CS03⁻ ∷ []) ∷
   rw⁻ 1 q31 ∷
   rw 2 q6 ∷
   rw 1 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 1451 W
  q35 : Eqn
  q35 = sE 822 lem-pass-CCZ012-vs-CS03
  q36 : Eqn
  q36 = wE 1452 W

-- pass [TOFF102] [CS03]: 21 steps
lem-pass-TOFF102-vs-CS03 : ⟪ (Toff102 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-CS03 = derive (Toff102 ∷ CS03 ∷ []) (CS03 ∷ Toff102 ∷ [])
  (rw 0 q27 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q28 ∷
   rw 3 q34 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw⁻ 3 q28 ∷
   rw 4 q6 ∷
   rw 1 q35 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q31 ∷
   rw 1 q36 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw⁻ 1 q31 ∷
   rw 2 q6 ∷
   rw 1 q33 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (K0⁻ ∷ CS13 ∷ []) (CS13 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑ • CS • Swap ↑)))
  q38 : Eqn
  q38 = sE 829 lem-pass-CCZ012-vs-CS13
  q39 : Eqn
  q39 = eqn (K0 ∷ CS13 ∷ []) (CS13 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑ • CS • Swap ↑)))

-- pass [TOFF012] [CS13]: 5 steps
lem-pass-TOFF012-vs-CS13 : ⟪ (Toff012 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CS13 = derive (Toff012 ∷ CS13 ∷ []) (CS13 ∷ Toff012 ∷ [])
  (rw 0 q8 ∷
   rw 2 q37 ∷
   rw 1 q38 ∷
   rw 0 q39 ∷
   rw 1 q18 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (K0⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))
  q41 : Eqn
  q41 = sE 831 lem-pass-CCZ012-vs-CSd13
  q42 : Eqn
  q42 = eqn (K0 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))

-- pass [TOFF012] [CSd13]: 5 steps
lem-pass-TOFF012-vs-CSd13 : ⟪ (Toff012 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CSd13 = derive (Toff012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff012 ∷ [])
  (rw 0 q8 ∷
   rw 2 q40 ∷
   rw 1 q41 ∷
   rw 0 q42 ∷
   rw 1 q18 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 838 lem-pass-S2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [S2]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2 ∷ []) (S2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = sE 839 lem-pass-Sd2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [Sd2]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 1443 W
  q46 : Eqn
  q46 = sE 21 lem-pass-CS12-vs-CS03
  q47 : Eqn
  q47 = sE 62 lem-pass-S0-vs-CS03
  q48 : Eqn
  q48 = wE 466 W
  q49 : Eqn
  q49 = wE 90 W
  q50 : Eqn
  q50 = sE 812 lem-pass-CCZ012-vs-CS12
  q51 : Eqn
  q51 = sE 814 lem-pass-CCZ012-vs-CZ12
  q52 : Eqn
  q52 = wE 1438 W
  q53 : Eqn
  q53 = wE 32 W

-- pass [S0] [TOFF012 CS03 TOFF012]: 11 steps
lem-pass-S0-vs-TOFF012-CS03-TOFF012 : ⟪ (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-TOFF012-CS03-TOFF012 = derive (S0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ S0 ∷ [])
  (rw 0 q45 ∷
   rw 3 q35 ∷
   rw 2 q46 ∷
   rw 1 q47 ∷
   rw 4 q48 ∷
   rw 3 q49 ∷
   rw 2 q45 ∷
   rw 5 q50 ∷
   rw 6 q51 ∷
   rw 4 q52 ∷
   rw 4 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = sE 574 lem-pass-CZ12-vs-CS03
  q55 : Eqn
  q55 = wE 467 W
  q56 : Eqn
  q56 = wE 1453 W

-- pass [CCZ012] [TOFF012 CS03 TOFF012]: 6 steps
lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012 : ⟪ (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012 = derive (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CCZ012 ∷ [])
  (rw 0 q48 ∷
   rw 2 q35 ∷
   rw 1 q54 ∷
   rw 3 q48 ∷
   rw 2 q55 ∷
   rw 3 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 469 W
  q58 : Eqn
  q58 = wE 1454 W
  q59 : Eqn
  q59 = sE 55 lem-pass-CSd12-vs-CS03
  q60 : Eqn
  q60 = sE 59 lem-pass-CS02-vs-CS03
  q61 : Eqn
  q61 = wE 468 W
  q62 : Eqn
  q62 = sE 813 lem-pass-CCZ012-vs-CSd12
  q63 : Eqn
  q63 = wE 1455 W
  q64 : Eqn
  q64 = sE 816 lem-pass-CS02-vs-CSd03

-- pass [CS02 CCZ012] [TOFF012 CS03 TOFF012 CSd03]: 13 steps
lem-pass-CS02-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CS02 ∷ CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS02 ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CS02-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CS02 ∷ CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS02 ∷ CCZ012 ∷ [])
  (rw 1 q48 ∷
   rw 0 q57 ∷
   rw 3 q51 ∷
   rw 2 q58 ∷
   rw 3 q53 ∷
   rw 2 q59 ∷
   rw 1 q60 ∷
   rw 3 q61 ∷
   rw 2 q57 ∷
   rw 5 q62 ∷
   rw 4 q63 ∷
   rw 4 q30 ∷
   rw 3 q64 ∷ []) Eq.refl

-- pass [CCZ012] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ []) ⟫ʷ
lem-pass-CCZ012-vs-TOFF012-CS03-TOFF012-CSd03 = derive (CCZ012 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CCZ012 ∷ [])
  (rw 0 q48 ∷
   rw 2 q35 ∷
   rw 1 q54 ∷
   rw 3 q48 ∷
   rw 2 q55 ∷
   rw 3 q56 ∷
   rw 3 q30 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = sE 828 lem-D-b
  q66 : Eqn
  q66 = sE 836 lem-pass-CS12-vs-Kd0-CS03-TOFF012-CSd03-TOFF012-K0

-- g-b: 2 steps
lem-g-b : ⟪ (CS12 ∷ CCZ012 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) ⟫ʷ ≈ ⟪ (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ []) ⟫ʷ
lem-g-b = derive (CS12 ∷ CCZ012 ∷ K0⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0 ∷ []) (K0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0 ∷ CS12 ∷ CCZ012 ∷ [])
  (rw 1 q65 ∷
   rw 0 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 1456 W
  q68 : Eqn
  q68 = wE 1457 W
  q69 : Eqn
  q69 = wE 1458 W
  q70 : Eqn
  q70 = wE 224 W
  q71 : Eqn
  q71 = wE 1342 W

-- C(U')=eps: 38 steps
lem-C⟨U'⟩≡eps : ⟪ (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-C⟨U'⟩≡eps = derive (Toff012 ∷ CK30⁻ ∷ CS03 ∷ CK30 ∷ Toff012 ∷ CK30⁻ ∷ CS03⁻ ∷ CK30 ∷ []) []
  (rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   re 1 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q67 ∷
   rw⁻ 1 q10 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw⁻ 3 q3 ∷
   rw 4 q6 ∷
   rw 8 q2 ∷
   re 7 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   re 6 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   re 5 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 6 q68 ∷
   rw⁻ 5 q10 ∷
   rw 8 q2 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 8 q6 ∷
   rw 0 q69 ∷
   rw 3 q70 ∷
   rw 1 q35 ∷
   rw 2 q53 ∷
   rw 3 q2 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 2 q71 ∷
   rw 1 q6 ∷
   rw 0 q11 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 1459 W
  q73 : Eqn
  q73 = wE 175 W
  q74 : Eqn
  q74 = sE 841 lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q75 : Eqn
  q75 = wE 1460 W
  q76 : Eqn
  q76 = wE 173 W
  q77 : Eqn
  q77 = wE 1461 W

-- CA CK30 Gad(t=0, W=(), d=1, e=1): 23 steps
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ : ⟪ (CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ CK30 ∷ []) ⟫ʷ
lem-CA-CK30-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡1⟩ = derive (CK30 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (K0 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ K0⁻ ∷ CK30 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q72 ∷
   rw⁻ 0 q3 ∷
   rw 1 q73 ∷
   rw 4 q2 ∷
   re 2 3 (CK30⁻ ∷ []) ∷
   rw 3 q73 ∷
   rw 4 q6 ∷
   rw 1 q74 ∷
   rw 0 q75 ∷
   rw 5 q16 ∷
   rw 10 q2 ∷
   rw 9 q76 ∷
   re 8 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q76 ∷
   rw 6 q3 ∷
   rw 7 q77 ∷
   rw 8 q2 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q6 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = sE 34 lem-pass-CS12-vs-CSd03
  q79 : Eqn
  q79 = sE 818 lem-pass-S0-vs-CSd03

-- pass [S0] [CS03 TOFF012 CSd03 TOFF012]: 12 steps
lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ []) ⟫ʷ
lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 = derive (S0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0 ∷ [])
  (rw 0 q47 ∷
   rw 1 q45 ∷
   rw 4 q30 ∷
   rw 3 q78 ∷
   rw 2 q79 ∷
   rw 5 q48 ∷
   rw 4 q49 ∷
   rw 3 q45 ∷
   rw 6 q50 ∷
   rw 7 q51 ∷
   rw 5 q52 ∷
   rw 5 q53 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = sE 832 lem-pass-CCZ013-vs-CS12

-- pass [CS12] [CCZ013]: 1 steps
lem-pass-CS12-vs-CCZ013 : ⟪ (CS12 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (CCZ013 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS12-vs-CCZ013 = derive (CS12 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS12 ∷ [])
  (rw⁻ 0 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 176 lem-pass-Sd0-vs-CS03
  q82 : Eqn
  q82 = wE 1445 W
  q83 : Eqn
  q83 = sE 56 lem-pass-CSd12-vs-CSd03
  q84 : Eqn
  q84 = sE 825 lem-pass-Sd0-vs-CSd03
  q85 : Eqn
  q85 = wE 1440 W

-- pass [Sd0] [CS03 TOFF012 CSd03 TOFF012]: 12 steps
lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ []) ⟫ʷ
lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012 = derive (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ [])
  (rw 0 q81 ∷
   rw 1 q82 ∷
   rw 4 q30 ∷
   rw 3 q83 ∷
   rw 2 q84 ∷
   rw 5 q48 ∷
   rw 4 q61 ∷
   rw 3 q82 ∷
   rw 6 q62 ∷
   rw 7 q51 ∷
   rw 5 q85 ∷
   rw 5 q53 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 1407 W
  q87 : Eqn
  q87 = sE 840 lem-pass-X3-CK30-X3-vs-CS03-TOFF012-CSd03-TOFF012
  q88 : Eqn
  q88 = wE 1408 W

-- pass [CK30] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 23 steps
lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ []) ⟫ʷ
lem-pass-CK30-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (CK30 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ []) (X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X3 ∷ CK30 ∷ [])
  (rw 2 q2 ∷
   rw 1 q76 ∷
   re 0 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q86 ∷
   rw 0 q73 ∷
   rw 1 q73 ∷
   rw 4 q2 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q73 ∷
   rw 4 q6 ∷
   rw 1 q87 ∷
   rw 9 q2 ∷
   rw 8 q76 ∷
   rw 7 q76 ∷
   re 6 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q76 ∷
   rw 6 q88 ∷
   rw 5 q73 ∷
   rw 8 q2 ∷
   re 6 3 (CK30 ∷ []) ∷
   rw 7 q6 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 128 W
  q90 : Eqn
  q90 = sE 843 lem-pass-CCZ123-vs-CS03
  q91 : Eqn
  q91 = wE 1437 W

-- pass [TOFF123] [CS03]: 21 steps
lem-pass-TOFF123-vs-CS03 : ⟪ (Toff123 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-CS03 = derive (Toff123 ∷ CS03 ∷ []) (CS03 ∷ Toff123 ∷ [])
  (rw 0 q89 ∷
   rw 4 q2 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q28 ∷
   rw 3 q34 ∷
   rw 4 q2 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw⁻ 3 q28 ∷
   rw 4 q6 ∷
   rw 1 q90 ∷
   rw 2 q2 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q31 ∷
   rw 1 q36 ∷
   rw 2 q2 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw⁻ 1 q31 ∷
   rw 2 q6 ∷
   rw 1 q91 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 196 W
  q93 : Eqn
  q93 = sE 826 lem-pass-CCZ013-vs-CS02

-- pass [TOFF103] [CS02]: 109 steps
lem-pass-TOFF103-vs-CS02 : ⟪ (Toff103 ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff103 ∷ []) ⟫ʷ
lem-pass-TOFF103-vs-CS02 = derive (Toff103 ∷ CS02 ∷ []) (CS02 ∷ Toff103 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q31 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q31 ∷
   rw⁻ 7 q5 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q31 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q31 ∷
   rw 1 q92 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 1 q27 ∷
   rw⁻ 0 q31 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 2 q9 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q28 ∷
   rw 3 q6 ∷
   rw 2 q34 ∷
   rw 1 q93 ∷
   rw 0 q36 ∷
   rw 4 q2 ∷
   rw 3 q28 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 3 q9 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q31 ∷
   rw 2 q33 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q31 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q31 ∷
   rw⁻ 8 q5 ∷
   rw 1 q2 ∷
   rw⁻ 2 q31 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q31 ∷
   rw⁻ 9 q5 ∷
   rw 2 q92 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q6 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = sE 842 lem-pass-CCZ013-vs-CSd02

-- pass [TOFF103] [CSd02]: 109 steps
lem-pass-TOFF103-vs-CSd02 : ⟪ (Toff103 ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff103 ∷ []) ⟫ʷ
lem-pass-TOFF103-vs-CSd02 = derive (Toff103 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff103 ∷ [])
  (rw 1 q2 ∷
   re 0 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q31 ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q31 ∷
   rw⁻ 7 q5 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q31 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q4 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw 0 q31 ∷
   rw 1 q92 ∷
   re 1 8 (Toff102 ∷ []) ∷
   rw 1 q27 ∷
   rw⁻ 0 q31 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q2 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q2 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 2 q9 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q28 ∷
   rw 3 q6 ∷
   rw 2 q29 ∷
   rw 1 q94 ∷
   rw 0 q32 ∷
   rw 4 q2 ∷
   rw 3 q28 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q6 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q4 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 3 q9 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q31 ∷
   rw 2 q33 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q31 ∷
   rw 4 q2 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q4 ∷
   rw 6 q2 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q31 ∷
   rw⁻ 8 q5 ∷
   rw 1 q2 ∷
   rw⁻ 2 q31 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw⁻ 8 q31 ∷
   rw⁻ 9 q5 ∷
   rw 2 q92 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q6 ∷ []) Eq.refl

private
  q95 : Eqn
  q95 = sE 844 lem-pass-CS12-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CS12]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS12 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS12 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12 ∷ []) (CS12 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q95 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = sE 845 lem-pass-CSd12-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CSd12]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd12 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd12 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q96 ∷ []) Eq.refl

-- pass [CS02] [CS03 TOFF012 CSd03 TOFF012]: 12 steps
lem-pass-CS02-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (CS02 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-CS03-TOFF012-CSd03-TOFF012 = derive (CS02 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS02 ∷ [])
  (rw 0 q60 ∷
   rw 1 q57 ∷
   rw 4 q30 ∷
   rw 3 q78 ∷
   rw 2 q64 ∷
   rw 5 q48 ∷
   rw 4 q49 ∷
   rw 3 q57 ∷
   rw 6 q50 ∷
   rw 7 q51 ∷
   rw 5 q52 ∷
   rw 5 q53 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = sE 60 lem-pass-CSd02-vs-CS03
  q98 : Eqn
  q98 = wE 1439 W
  q99 : Eqn
  q99 = sE 817 lem-pass-CSd02-vs-CSd03

-- pass [CSd02] [CS03 TOFF012 CSd03 TOFF012]: 12 steps
lem-pass-CSd02-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (CS02⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-CS03-TOFF012-CSd03-TOFF012 = derive (CS02⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS02⁻ ∷ [])
  (rw 0 q97 ∷
   rw 1 q98 ∷
   rw 4 q30 ∷
   rw 3 q83 ∷
   rw 2 q99 ∷
   rw 5 q48 ∷
   rw 4 q61 ∷
   rw 3 q98 ∷
   rw 6 q62 ∷
   rw 7 q51 ∷
   rw 5 q85 ∷
   rw 5 q53 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = eqn (K0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (CCZ))
  q101 : Eqn
  q101 = sE 846 lem-pass-CCZ012-vs-CCZ123
  q102 : Eqn
  q102 = eqn (K0 ∷ CCZ123 ∷ []) (CCZ123 ∷ K0 ∷ []) (low₁-comm (K) (CCZ))

-- pass [TOFF012] [CCZ123]: 5 steps
lem-pass-TOFF012-vs-CCZ123 : ⟪ (Toff012 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CCZ123 = derive (Toff012 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff012 ∷ [])
  (rw 0 q8 ∷
   rw 2 q100 ∷
   rw 1 q101 ∷
   rw 0 q102 ∷
   rw 1 q18 ∷ []) Eq.refl
