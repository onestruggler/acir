{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD683 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D683 (W : Ws) (Sᴰ : SD683) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1793
  lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 0 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1794
  lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 1 Sᴰ
  lem-pass-X3-CKd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1795
  lem-pass-X3-CKd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 2 Sᴰ
  lem-pass-X3-CSd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1796
  lem-pass-X3-CSd31-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 3 Sᴰ
  lem-pass-CS12-vs-X3-TOFF013-X3 : St 1625
  lem-pass-CS12-vs-X3-TOFF013-X3 = pickᴰ 4 Sᴰ
  lem-pass-CSd12-vs-X3-TOFF013-X3 : St 1629
  lem-pass-CSd12-vs-X3-TOFF013-X3 = pickᴰ 5 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 6 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 : St 1797
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 = pickᴰ 7 Sᴰ
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 1798
  lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 8 Sᴰ
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 : St 1799
  lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 9 Sᴰ
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CS03 : St 1800
  lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CS03 = pickᴰ 10 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 : St 1801
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2 = pickᴰ 11 Sᴰ
  lem-pass-TOFF203-vs-X3-TOFF013-X3 : St 1802
  lem-pass-TOFF203-vs-X3-TOFF013-X3 = pickᴰ 12 Sᴰ
  lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CS03 : St 1803
  lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CS03 = pickᴰ 13 Sᴰ
  lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CS03 : St 1804
  lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CS03 = pickᴰ 14 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 45 W
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
  q8 = wE 1357 W
  q9 : Eqn
  q9 = wE 231 W
  q10 : Eqn
  q10 = sE 1778 lem-S2
  q11 : Eqn
  q11 = wE 227 W
  q12 : Eqn
  q12 = wE 1358 W
  q13 : Eqn
  q13 = wE 1342 W

-- S2 ^-1: 133 steps
lem-S2-ᵖ-1 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ []) ⟫ʷ
lem-S2-ᵖ-1 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS02 ∷ Toff013 ∷ CS02⁻ ∷ Toff013 ∷ [])
  (rw 4 q1 ∷
   rw 5 q2 ∷
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
   rw⁻ 11 q5 ∷
   rw 4 q1 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 5 q7 ∷
   re 5 8 (Toff012 ∷ []) ∷
   re 4 3 (Toff013 ∷ []) ∷
   re 6 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw⁻ 7 q4 ∷
   rw 10 q1 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q5 ∷
   rw 5 q1 ∷
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
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 6 q1 ∷
   rw 7 q2 ∷
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
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q7 ∷
   re 7 8 (Toff012 ∷ []) ∷
   re 6 3 (Toff013 ∷ []) ∷
   re 8 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (CS13 ∷ []) ∷
   rw⁻ 9 q4 ∷
   rw 12 q1 ∷
   re 10 3 (CS13⁻ ∷ []) ∷
   rw⁻ 11 q4 ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q5 ∷
   rw 7 q1 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw⁻ 10 q4 ∷
   re 12 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw⁻ 12 q4 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q5 ∷
   rw 8 q7 ∷
   re 8 8 (Toff012 ∷ []) ∷
   re 7 3 (Toff013 ∷ []) ∷
   rw 8 q6 ∷
   rw 7 q9 ∷
   rw⁻ 4 q10 ∷
   rw 3 q11 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   re 2 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 3 q12 ∷
   rw 2 q6 ∷
   rw 1 q11 ∷
   rw 2 q1 ∷
   re 1 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 3 q6 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw 1 q13 ∷
   rw 0 q6 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 1800 lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-CS03

-- pass [CS03] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 1 steps
lem-pass-CS03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (CS03 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ CS03 ∷ [])
  (rw⁻ 0 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = sE 1798 lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q15 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = sE 1799 lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q16 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q18 : Eqn
  q18 = wE 196 W
  q19 : Eqn
  q19 = wE 173 W
  q20 : Eqn
  q20 = wE 1778 W
  q21 : Eqn
  q21 = wE 175 W
  q22 : Eqn
  q22 = eqn (CS12 ∷ X3 ∷ []) (X3 ∷ CS12 ∷ []) (low₃-comm ((CS ↑)) (X))
  q23 : Eqn
  q23 = eqn (CS12⁻ ∷ X3 ∷ []) (X3 ∷ CS12⁻ ∷ []) (low₃-comm (((CS • CS • CS) ↑)) (X))
  q24 : Eqn
  q24 = sE 1797 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12
  q25 : Eqn
  q25 = wE 1777 W

-- pass [X3 TOFF102 CS13 TOFF102 CSd13 X3] [TOFF103 CS12 TOFF103 CSd12]: 249 steps
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-TOFF102-CS13-TOFF102-CSd13-X3-vs-TOFF103-CS12-TOFF103-CSd12 = derive (X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 7 q1 ∷
   re 6 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 6 q17 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q17 ∷
   rw⁻ 13 q5 ∷
   rw 14 q6 ∷
   rw 13 q5 ∷
   rw 12 q17 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 10 q4 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q17 ∷
   rw 7 q18 ∷
   re 7 8 (Toff102 ∷ []) ∷
   rw 5 q19 ∷
   rw 6 q20 ∷
   rw 5 q21 ∷
   re 7 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 6 q17 ∷
   rw 9 q1 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 10 q4 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw⁻ 12 q17 ∷
   rw⁻ 13 q5 ∷
   rw 6 q1 ∷
   rw⁻ 7 q17 ∷
   re 9 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q4 ∷
   re 11 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw⁻ 11 q4 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 13 q17 ∷
   rw⁻ 14 q5 ∷
   rw 7 q18 ∷
   re 7 8 (Toff102 ∷ []) ∷
   re 6 3 (Toff103 ∷ []) ∷
   rw 7 q21 ∷
   rw 8 q21 ∷
   rw 9 q6 ∷
   rw⁻ 8 q22 ∷
   rw 11 q1 ∷
   re 10 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 11 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 10 q17 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q4 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q4 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q5 ∷
   rw 18 q6 ∷
   rw 17 q5 ∷
   rw 16 q17 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q6 ∷
   rw 14 q4 ∷
   re 13 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 15 q6 ∷
   rw 12 q4 ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 10 q17 ∷
   rw 11 q18 ∷
   re 11 8 (Toff102 ∷ []) ∷
   rw 9 q19 ∷
   rw 10 q20 ∷
   rw 9 q21 ∷
   re 11 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 10 q17 ∷
   rw 13 q1 ∷
   re 11 3 (CS13 ∷ []) ∷
   rw⁻ 12 q4 ∷
   rw 15 q1 ∷
   re 13 3 (CS13⁻ ∷ []) ∷
   rw⁻ 14 q4 ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw⁻ 16 q17 ∷
   rw⁻ 17 q5 ∷
   rw 10 q1 ∷
   rw⁻ 11 q17 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q6 ∷
   rw⁻ 13 q4 ∷
   re 15 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 14 q6 ∷
   rw⁻ 15 q4 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q6 ∷
   rw⁻ 17 q17 ∷
   rw⁻ 18 q5 ∷
   rw 11 q18 ∷
   re 11 8 (Toff102 ∷ []) ∷
   re 10 3 (Toff103 ∷ []) ∷
   rw 11 q21 ∷
   rw 12 q21 ∷
   rw 13 q6 ∷
   rw⁻ 12 q23 ∷
   rw 1 q24 ∷
   rw 4 q1 ∷
   rw 3 q19 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q17 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q17 ∷
   rw⁻ 9 q5 ∷
   rw 10 q6 ∷
   rw 9 q5 ∷
   rw 8 q17 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q17 ∷
   rw 3 q18 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q19 ∷
   rw 0 q19 ∷
   rw 1 q25 ∷
   re 1 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 0 q17 ∷
   rw 3 q1 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q17 ∷
   rw⁻ 7 q5 ∷
   rw 0 q1 ∷
   rw⁻ 1 q17 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q17 ∷
   rw⁻ 8 q5 ∷
   rw 1 q18 ∷
   re 1 8 (Toff102 ∷ []) ∷
   re 0 3 (Toff103 ∷ []) ∷
   rw 1 q21 ∷
   rw 2 q6 ∷
   rw⁻ 1 q22 ∷
   rw 6 q1 ∷
   rw 5 q19 ∷
   re 4 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 5 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 4 q17 ∷
   rw 7 q1 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q4 ∷
   rw 11 q1 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw⁻ 10 q17 ∷
   rw⁻ 11 q5 ∷
   rw 12 q6 ∷
   rw 11 q5 ∷
   rw 10 q17 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 9 q6 ∷
   rw 6 q4 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 7 q6 ∷
   rw 4 q17 ∷
   rw 5 q18 ∷
   re 5 8 (Toff102 ∷ []) ∷
   rw 3 q19 ∷
   rw 2 q19 ∷
   rw 3 q25 ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q17 ∷
   rw 5 q1 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q4 ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q17 ∷
   rw⁻ 9 q5 ∷
   rw 2 q1 ∷
   rw⁻ 3 q17 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw⁻ 7 q4 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q6 ∷
   rw⁻ 9 q17 ∷
   rw⁻ 10 q5 ∷
   rw 3 q18 ∷
   re 3 8 (Toff102 ∷ []) ∷
   re 2 3 (Toff103 ∷ []) ∷
   rw 3 q21 ∷
   rw 4 q6 ∷
   rw⁻ 3 q23 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = sE 1629 lem-pass-CSd12-vs-X3-TOFF013-X3
  q27 : Eqn
  q27 = sE 1802 lem-pass-TOFF203-vs-X3-TOFF013-X3
  q28 : Eqn
  q28 = sE 1625 lem-pass-CS12-vs-X3-TOFF013-X3

-- pass [TOFF203 CS12 TOFF203 CSd12] [X3 TOFF013 X3]: 4 steps
lem-pass-TOFF203-CS12-TOFF203-CSd12-vs-X3-TOFF013-X3 : ⟪ (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF203-CS12-TOFF203-CSd12-vs-X3-TOFF013-X3 = derive (Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ Toff203 ∷ CS12 ∷ Toff203 ∷ CS12⁻ ∷ [])
  (rw 3 q26 ∷
   rw 2 q27 ∷
   rw 1 q28 ∷
   rw 0 q27 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = sE 1778 lem-S2
  q30 : Eqn
  q30 = sE 1794 lem-pass-X3-CS31-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X3 CS31 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CS31-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CS13 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CS13 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS13 ∷ X3 ∷ [])
  (rw 3 q29 ∷
   rw 0 q30 ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = sE 1793 lem-pass-X3-CK31-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X3 CK31 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CK31-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CK31 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 3 q29 ∷
   rw 0 q31 ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 1795 lem-pass-X3-CKd31-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X3 CKd31 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CKd31-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CK31⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd31-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CK31⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CK31⁻ ∷ X3 ∷ [])
  (rw 3 q29 ∷
   rw 0 q32 ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = sE 1796 lem-pass-X3-CSd31-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X3 CSd31 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CSd31-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (X3 ∷ CS13⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CSd31-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (X3 ∷ CS13⁻ ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X3 ∷ CS13⁻ ∷ X3 ∷ [])
  (rw 3 q29 ∷
   rw 0 q33 ∷
   rw⁻ 0 q10 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = sE 1803 lem-pass-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3-vs-CS03

-- pass [CS03] [X0 X3 CS23 TOFF201 CSd23 TOFF201 X0 X3]: 1 steps
lem-pass-CS03-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 : ⟪ (CS03 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X0-X3-CS23-TOFF201-CSd23-TOFF201-X0-X3 = derive (CS03 ∷ X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CS03 ∷ [])
  (rw⁻ 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = sE 1804 lem-pass-X3-CS13-TOFF102-CSd13-TOFF102-X3-vs-CS03

-- pass [CS03] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 1 steps
lem-pass-CS03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (CS03 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CS03 ∷ [])
  (rw⁻ 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 1962 W
  q37 : Eqn
  q37 = eqn (S0 ∷ Sw23 ∷ []) (Sw23 ∷ S0 ∷ []) (low₁-comm (S) ((Swap ↑)))
  q38 : Eqn
  q38 = eqn (Toff012 ∷ X3 ∷ []) (X3 ∷ Toff012 ∷ []) (low₃-comm (Toff) (X))
  q39 : Eqn
  q39 = wE 1963 W
  q40 : Eqn
  q40 = eqn (S0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((Swap ↑)))
  q41 : Eqn
  q41 = eqn (S0 ∷ X2 ∷ []) (X2 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑)))
  q42 : Eqn
  q42 = wE 5 W
  q43 : Eqn
  q43 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q44 : Eqn
  q44 = wE 76 W
  q45 : Eqn
  q45 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q46 : Eqn
  q46 = wE 258 W
  q47 : Eqn
  q47 = wE 29 W
  q48 : Eqn
  q48 = wE 31 W
  q49 : Eqn
  q49 = wE 2016 W
  q50 : Eqn
  q50 = eqn (S0⁻ ∷ X2 ∷ []) (X2 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑)))
  q51 : Eqn
  q51 = wE 7 W
  q52 : Eqn
  q52 = wE 257 W
  q53 : Eqn
  q53 = wE 27 W
  q54 : Eqn
  q54 = sE 1801 lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0-CSd03-X2-TOFF012-X2-Sd0-CS03-X2-TOFF012-X2
  q55 : Eqn
  q55 = eqn (S0 ∷ X3 ∷ []) (X3 ∷ S0 ∷ []) (low₁-comm (S) ((X ↑ ↑)))
  q56 : Eqn
  q56 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q57 : Eqn
  q57 = eqn (S0⁻ ∷ X3 ∷ []) (X3 ∷ S0⁻ ∷ []) (low₁-comm ((S • S • S)) ((X ↑ ↑)))
  q58 : Eqn
  q58 = wE 2017 W
  q59 : Eqn
  q59 = wE 1964 W
  q60 : Eqn
  q60 = wE 2018 W

-- pass [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3] [CS03 TOFF012 CSd03 TOFF012]: 139 steps
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ [])
  (rw 9 q1 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q6 ∷
   rw 7 q19 ∷
   rw 8 q36 ∷
   rw⁻ 7 q37 ∷
   rw 10 q1 ∷
   re 8 3 (CS03⁻ ∷ []) ∷
   rw 9 q21 ∷
   rw 10 q6 ∷
   rw⁻ 9 q38 ∷
   rw 12 q1 ∷
   re 11 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 13 q6 ∷
   rw 10 q19 ∷
   rw 11 q39 ∷
   rw⁻ 10 q40 ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 12 q21 ∷
   rw 13 q6 ∷
   rw⁻ 12 q38 ∷
   rw⁻ 6 q41 ∷
   rw 9 q42 ∷
   re 8 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 10 q43 ∷
   rw 9 q44 ∷
   rw⁻ 8 q43 ∷
   re 9 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q45 ∷
   rw 8 q46 ∷
   re 8 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q43 ∷
   rw 8 q47 ∷
   rw 9 q43 ∷
   re 7 3 (CS03⁻ ∷ []) ∷
   rw 8 q45 ∷
   rw 9 q48 ∷
   rw 8 q49 ∷
   rw⁻ 11 q50 ∷
   rw 14 q42 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 15 q43 ∷
   rw 14 q51 ∷
   rw⁻ 13 q43 ∷
   re 14 3 (CS13 ∷ []) ∷
   rw⁻ 12 q45 ∷
   rw 13 q52 ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q43 ∷
   rw 13 q53 ∷
   rw 14 q43 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 13 q45 ∷
   rw 14 q48 ∷
   rw 13 q49 ∷
   rw 2 q54 ∷
   rw⁻ 1 q55 ∷
   rw 4 q1 ∷
   re 3 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q6 ∷
   rw 2 q19 ∷
   rw 3 q39 ∷
   rw⁻ 2 q40 ∷
   rw 5 q1 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q21 ∷
   rw 5 q6 ∷
   rw⁻ 4 q56 ∷
   rw⁻ 5 q38 ∷
   rw⁻ 6 q56 ∷
   rw⁻ 7 q57 ∷
   rw 10 q1 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q6 ∷
   rw 8 q19 ∷
   rw 9 q36 ∷
   rw⁻ 8 q37 ∷
   rw 11 q1 ∷
   re 9 3 (CS03⁻ ∷ []) ∷
   rw 10 q21 ∷
   rw 11 q6 ∷
   rw⁻ 10 q56 ∷
   rw⁻ 11 q38 ∷
   rw⁻ 12 q56 ∷
   rw⁻ 0 q41 ∷
   rw⁻ 1 q50 ∷
   rw 4 q42 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q43 ∷
   rw 4 q51 ∷
   rw⁻ 3 q43 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q45 ∷
   rw 3 q52 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q43 ∷
   rw 3 q53 ∷
   rw 4 q43 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q45 ∷
   rw 4 q48 ∷
   rw 3 q58 ∷
   rw⁻ 4 q50 ∷
   rw⁻ 5 q41 ∷
   rw 8 q42 ∷
   re 7 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw⁻ 9 q43 ∷
   rw 8 q44 ∷
   rw⁻ 7 q43 ∷
   re 8 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q45 ∷
   rw 7 q46 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q43 ∷
   rw 7 q47 ∷
   rw 8 q43 ∷
   re 6 3 (CS03⁻ ∷ []) ∷
   rw 7 q45 ∷
   rw 8 q48 ∷
   rw 7 q58 ∷
   rw 3 q1 ∷
   re 2 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 4 q6 ∷
   rw 1 q40 ∷
   rw 0 q37 ∷
   rw 1 q59 ∷
   rw 2 q1 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q6 ∷
   rw 5 q1 ∷
   re 4 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q6 ∷
   rw 3 q37 ∷
   rw 2 q40 ∷
   rw 3 q60 ∷
   rw 4 q1 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 3 q6 ∷ []) Eq.refl
