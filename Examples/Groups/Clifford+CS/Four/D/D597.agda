{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D597 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D008 W using (lem-pass-CCZ012-vs-CZ01)
open import Examples.Groups.Clifford+CS.Four.D.D009 W using (lem-pass-CS13-vs-CSd03 ; lem-pass-CS13-vs-S0 ; lem-pass-CSd13-vs-CSd03 ; lem-pass-CSd13-vs-S0 ; lem-pass-TOFF102-vs-S0 ; lem-pass-TOFF102-vs-Sd0 ; lem-pass-TOFF102-vs-X2-TOFF012-X2)
open import Examples.Groups.Clifford+CS.Four.D.D016 W using (lem-pass-CS12-vs-X2-TOFF102-X2 ; lem-pass-CSd12-vs-X2-TOFF102-X2)
open import Examples.Groups.Clifford+CS.Four.D.D023 W using (lem-pass-TOFF201-vs-Sd0 ; lem-pass-TOFF201-vs-Sd3 ; lem-pass-TOFF201-vs-iI)
open import Examples.Groups.Clifford+CS.Four.D.D024 W using (lem-pass-CCZ012-vs-Z0 ; lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0 ; lem-pass-TOFF102-vs-S3 ; lem-pass-TOFF102-vs-Sd3 ; lem-pass-TOFF102-vs-iI)
open import Examples.Groups.Clifford+CS.Four.D.D035 W using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3)
open import Examples.Groups.Clifford+CS.Four.D.D036 W using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3 ; lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3)
open import Examples.Groups.Clifford+CS.Four.D.D037 W using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3)
open import Examples.Groups.Clifford+CS.Four.D.D046 W using (lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK32-X3)
open import Examples.Groups.Clifford+CS.Four.D.D047 W using (lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK31-X3)
open import Examples.Groups.Clifford+CS.Four.D.D051 W using (lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3 ; lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3)
open import Examples.Groups.Clifford+CS.Four.D.D518 W using (lem-pass-CCZ012-vs-CZ03 ; lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2)
open import Examples.Groups.Clifford+CS.Four.D.D536 W using (lem-pass-CCZ012-vs-CCZ013)
open import Examples.Groups.Clifford+CS.Four.D.D538 W using (lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-TOFF102-vs-CS03 ; lem-pass-TOFF102-vs-CSd03)
open import Examples.Groups.Clifford+CS.Four.D.D542 W using (lem-pass-CCZ123-vs-CCZ012 ; lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-TOFF103-vs-X2-TOFF102-X2 ; lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CS21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D543 W using (lem-pass-CS13-vs-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-CSd13-vs-TOFF103-CS12-TOFF103-CSd12 ; lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D544 W using (lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 ; lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 ; lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23 ; lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23 ; lem-pass-TOFF012-vs-CS23 ; lem-pass-TOFF012-vs-CSd23 ; lem-pass-TOFF013-vs-CCZ123 ; lem-pass-TOFF013-vs-CS23 ; lem-pass-TOFF023-vs-CS13 ; lem-pass-TOFF201-vs-CS03 ; lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 ; lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 ; lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 ; lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 ; lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 ; lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 ; lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201)
open import Examples.Groups.Clifford+CS.Four.D.D545 W using (lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1 ; lem-pass-TOFF201-vs-CSd03 ; lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 ; lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3)
open import Examples.Groups.Clifford+CS.Four.D.D546 W using (lem-pass-X2-CK20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 ; lem-pass-X2-CK20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 ; lem-pass-X2-CKd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 ; lem-pass-X2-CS20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3 ; lem-pass-X2-CS20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3 ; lem-pass-X2-CSd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3)
open import Examples.Groups.Clifford+CS.Four.D.D547 W using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3)
open import Examples.Groups.Clifford+CS.Four.D.D548 W using (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 ; lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 ; lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF123-X3)

private
  q1 : Eqn
  q1 = eqn (CS12 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1474 W)
  q2 : Eqn
  q2 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q3 : Eqn
  q3 = eqn (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ []) (X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X3)
  q4 : Eqn
  q4 = eqn (X2 ∷ CS12 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ []) (wn 1475 W)

-- pass [CS21] [X2 X3 S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0 X2 X3]: 5 steps
lem-pass-CS21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 : ⟪ (CS12 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS12 ∷ []) ⟫ʷ
lem-pass-CS21-vs-X2-X3-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0-X2-X3 = derive (CS12 ∷ X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S0 ∷ K0 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ K0⁻ ∷ S0⁻ ∷ X2 ∷ X3 ∷ CS12 ∷ [])
  (rw 0 q1 ∷
   rw 13 q2 ∷
   rw 1 q3 ∷
   rw 11 q4 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q5 : Eqn
  q5 = eqn (Toff102 ∷ []) (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (wn 1347 W)
  q6 : Eqn
  q6 = eqn (Toff123 ∷ []) (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (wn 128 W)
  q7 : Eqn
  q7 = eqn (K1⁻ ∷ K1 ∷ []) [] (wn 1509 W)
  q8 : Eqn
  q8 = eqn (CCZ123 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ123 ∷ []) (lem-pass-CCZ123-vs-CCZ012)
  q9 : Eqn
  q9 = eqn [] (K1⁻ ∷ K1 ∷ []) (wn 1510 W)
  q10 : Eqn
  q10 = eqn (K1 ∷ CCZ012 ∷ K1⁻ ∷ []) (Toff102 ∷ []) (wn 1450 W)
  q11 : Eqn
  q11 = eqn (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (Toff123 ∷ []) (wn 1437 W)

-- pass [TOFF123] [TOFF102]: 7 steps
lem-pass-TOFF123-vs-TOFF102 : ⟪ (Toff123 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ Toff123 ∷ []) ⟫ʷ
lem-pass-TOFF123-vs-TOFF102 = derive (Toff123 ∷ Toff102 ∷ []) (Toff102 ∷ Toff123 ∷ [])
  (rw 1 q5 ∷
   rw 0 q6 ∷
   rw 2 q7 ∷
   rw 1 q8 ∷
   rw 2 q9 ∷
   rw 0 q10 ∷
   rw 1 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q13 : Eqn
  q13 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q14 : Eqn
  q14 = eqn (K1 ∷ Sw23 ∷ []) (Sw23 ∷ K1 ∷ []) (low-comm ((K ↑)) (Swap))
  q15 : Eqn
  q15 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q16 : Eqn
  q16 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q17 : Eqn
  q17 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q18 : Eqn
  q18 = eqn (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) (wn 196 W)
  q19 : Eqn
  q19 = eqn (X2 ∷ Toff102 ∷ X2 ∷ []) (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) (wn 1516 W)
  q20 : Eqn
  q20 = eqn (CZ01 ∷ Sw23 ∷ []) (Sw23 ∷ CZ01 ∷ []) (low-comm (CZ) (Swap))
  q21 : Eqn
  q21 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q22 : Eqn
  q22 = eqn (K1⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K1⁻ ∷ []) (low-comm (((K • iI) ↑)) (Swap))
  q23 : Eqn
  q23 = eqn (CCZ012 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ01)
  q24 : Eqn
  q24 = eqn (CCZ012 ∷ CCZ013 ∷ []) (CCZ013 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CCZ013)
  q25 : Eqn
  q25 = eqn (K1 ∷ CZ01 ∷ CCZ012 ∷ K1⁻ ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ []) (wn 1517 W)
  q26 : Eqn
  q26 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)

-- pass [TOFF102] [X3 TOFF103 X3]: 118 steps
lem-pass-TOFF102-vs-X3-TOFF103-X3 : ⟪ (Toff102 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-X3-TOFF103-X3 = derive (Toff102 ∷ X3 ∷ Toff103 ∷ X3 ∷ []) (X3 ∷ Toff103 ∷ X3 ∷ Toff102 ∷ [])
  (rw 4 q12 ∷
   rw 3 q13 ∷
   re 2 1 (Sw23 ∷ Toff102 ∷ Sw23 ∷ []) ∷
   re 3 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 2 q14 ∷
   rw 5 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 7 q12 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q14 ∷
   rw⁻ 9 q16 ∷
   rw 10 q17 ∷
   rw 9 q16 ∷
   rw 8 q14 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q17 ∷
   rw 6 q15 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw 4 q15 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 2 q14 ∷
   rw 3 q18 ∷
   re 3 8 (Toff102 ∷ []) ∷
   rw 1 q13 ∷
   rw 2 q19 ∷
   rw⁻ 1 q14 ∷
   rw⁻ 2 q20 ∷
   re 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 5 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 7 q12 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 3 q12 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw 4 q21 ∷
   re 4 5 (CCZ012 ∷ []) ∷
   re 3 3 (CCZ013 ∷ []) ∷
   rw⁻ 4 q22 ∷
   rw 5 q17 ∷
   rw 0 q5 ∷
   rw 2 q7 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷
   rw 3 q9 ∷
   rw 4 q12 ∷
   rw 3 q22 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q12 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q15 ∷
   rw 6 q12 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q17 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 3 q15 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw 3 q21 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q20 ∷
   rw 0 q14 ∷
   rw 1 q25 ∷
   rw 0 q26 ∷
   re 2 1 (K1 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K1 ∷ ι ∷ []) ∷
   rw⁻ 1 q14 ∷
   rw 4 q12 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q15 ∷
   rw 6 q12 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 8 q12 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q14 ∷
   rw⁻ 8 q16 ∷
   rw 1 q12 ∷
   rw⁻ 2 q14 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q17 ∷
   rw⁻ 4 q15 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw⁻ 6 q15 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q17 ∷
   rw⁻ 8 q14 ∷
   rw⁻ 9 q16 ∷
   rw 2 q18 ∷
   re 2 8 (Toff102 ∷ []) ∷
   re 1 3 (Toff103 ∷ []) ∷
   rw 2 q26 ∷
   rw 3 q17 ∷
   rw 3 q10 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = eqn (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ []) lem-pass-CS12-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CS12]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CS12 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12 ∷ []) (CS12 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12⁻ ∷ []) lem-pass-CSd12-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [CSd12]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd12 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-CSd12 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ CS12⁻ ∷ []) (CS12⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ []) (lem-pass-CSd12-vs-X2-TOFF102-X2)
  q30 : Eqn
  q30 = eqn (Toff103 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff103 ∷ []) (lem-pass-TOFF103-vs-X2-TOFF102-X2)
  q31 : Eqn
  q31 = eqn (CS12 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ CS12 ∷ []) (lem-pass-CS12-vs-X2-TOFF102-X2)

-- pass [TOFF103 CS12 TOFF103 CSd12] [X2 TOFF102 X2]: 4 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X2-TOFF102-X2 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ Toff102 ∷ X2 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X2-TOFF102-X2 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  (rw 3 q29 ∷
   rw 2 q30 ∷
   rw 1 q31 ∷
   rw 0 q30 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = eqn (CS13 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13 ∷ []) lem-pass-CS13-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [TOFF103 CS12 TOFF103 CSd12] [CS13]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CS13 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CS13 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13 ∷ []) (CS13 ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  (rw⁻ 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (CS13⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ []) lem-pass-CSd13-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [TOFF103 CS12 TOFF103 CSd12] [CSd13]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd13 : ⟪ (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd13 = derive (Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ Toff103 ∷ CS12 ∷ Toff103 ∷ CS12⁻ ∷ [])
  (rw⁻ 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = eqn (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ []) lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [S1]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S1 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1 ∷ []) (S1 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = eqn (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ []) lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [Sd1]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 : ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Sd1 = derive (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ []) (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ [])
  (rw⁻ 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CK32⁻ ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 1674 W)
  q37 : Eqn
  q37 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201)
  q38 : Eqn
  q38 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ []) (wn 1675 W)

-- pass [CKd32] [X3 CS23 TOFF201 CSd23 TOFF201 X3]: 3 steps
lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 : ⟪ (CK32⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK32⁻ ∷ []) ⟫ʷ
lem-pass-CKd32-vs-X3-CS23-TOFF201-CSd23-TOFF201-X3 = derive (CK32⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ []) (X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK32⁻ ∷ [])
  (rw 0 q36 ∷
   rw 1 q37 ∷
   rw 5 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ []) lem-pass-TOFF012-vs-CS23

-- pass [CS23] [TOFF012]: 1 steps
lem-pass-CS23-vs-TOFF012 : ⟪ (CS23 ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-TOFF012 = derive (CS23 ∷ Toff012 ∷ []) (Toff012 ∷ CS23 ∷ [])
  (rw⁻ 0 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ []) lem-pass-TOFF013-vs-CS23

-- pass [CS23] [TOFF013]: 1 steps
lem-pass-CS23-vs-TOFF013 : ⟪ (CS23 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CS23 ∷ []) ⟫ʷ
lem-pass-CS23-vs-TOFF013 = derive (CS23 ∷ Toff013 ∷ []) (Toff013 ∷ CS23 ∷ [])
  (rw⁻ 0 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = eqn (Toff013 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff013 ∷ []) lem-pass-TOFF013-vs-CCZ123

-- pass [CCZ123] [TOFF013]: 1 steps
lem-pass-CCZ123-vs-TOFF013 : ⟪ (CCZ123 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ123 ∷ []) ⟫ʷ
lem-pass-CCZ123-vs-TOFF013 = derive (CCZ123 ∷ Toff013 ∷ []) (Toff013 ∷ CCZ123 ∷ [])
  (rw⁻ 0 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ []) lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [CS02]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CS02 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ []) (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw⁻ 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ []) lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [CSd02]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-CSd02 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ []) (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw⁻ 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = eqn (X0 ∷ X3 ∷ []) (X3 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑ ↑)))
  q45 : Eqn
  q45 = eqn (CK31 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (wn 1366 W)
  q46 : Eqn
  q46 = eqn (X3 ∷ CK31 ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0)
  q47 : Eqn
  q47 = eqn (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ []) (wn 1367 W)

-- pass [CK31] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 5 steps
lem-pass-CK31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (CK31 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CK31-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (CK31 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31 ∷ [])
  (rw 1 q44 ∷
   rw 0 q45 ∷
   rw 1 q46 ∷
   rw 7 q47 ∷
   rw⁻ 0 q44 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = eqn (Toff023 ∷ CS13 ∷ []) (CS13 ∷ Toff023 ∷ []) lem-pass-TOFF023-vs-CS13

-- pass [CS13] [TOFF023]: 1 steps
lem-pass-CS13-vs-TOFF023 : ⟪ (CS13 ∷ Toff023 ∷ []) ⟫ʷ ≈ ⟪ (Toff023 ∷ CS13 ∷ []) ⟫ʷ
lem-pass-CS13-vs-TOFF023 = derive (CS13 ∷ Toff023 ∷ []) (Toff023 ∷ CS13 ∷ [])
  (rw⁻ 0 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ []) (X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 1687 W)
  q50 : Eqn
  q50 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ []) (wn 1688 W)

-- pass [X3 CKd32 X3] [X0 CS23 TOFF201 CSd23 TOFF201 X0]: 5 steps
lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-X0-CS23-TOFF201-CSd23-TOFF201-X0 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ []) (X0 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X0 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 0 q49 ∷
   rw 1 q50 ∷
   rw 1 q37 ∷
   rw 5 q50 ∷
   rw 5 q49 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = eqn (Toff201 ∷ CS03 ∷ []) (CS03 ∷ Toff201 ∷ []) lem-pass-TOFF201-vs-CS03

-- pass [CS03] [TOFF201]: 1 steps
lem-pass-CS03-vs-TOFF201 : ⟪ (CS03 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-TOFF201 = derive (CS03 ∷ Toff201 ∷ []) (Toff201 ∷ CS03 ∷ [])
  (rw⁻ 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (Toff201 ∷ ι ∷ []) (ι ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-iI)
  q53 : Eqn
  q53 = eqn (Toff201 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-Sd0)
  q54 : Eqn
  q54 = eqn (Toff201 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-Sd3)
  q55 : Eqn
  q55 = eqn (Toff201 ∷ CS03 ∷ []) (CS03 ∷ Toff201 ∷ []) (lem-pass-TOFF201-vs-CS03)

-- pass [TOFF201] [iI Sd0 Sd3 CS03]: 4 steps
lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 : ⟪ (Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-iI-Sd0-Sd3-CS03 = derive (Toff201 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ Toff201 ∷ [])
  (rw 0 q52 ∷
   rw 1 q53 ∷
   rw 2 q54 ∷
   rw 3 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (S2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2 ∷ []) lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [S2]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (S2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-S2 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2 ∷ []) (S2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw⁻ 0 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (S2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2⁻ ∷ []) lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23

-- pass [TOFF201 CS23 TOFF201 CSd23] [Sd2]: 1 steps
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2 : ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2⁻ ∷ []) ⟫ʷ ≈ ⟪ (S2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-TOFF201-CS23-TOFF201-CSd23-vs-Sd2 = derive (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2⁻ ∷ []) (S2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ [])
  (rw⁻ 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (CS13 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13 ∷ []) lem-pass-CS13-vs-CSd03
  q59 : Eqn
  q59 = eqn (Toff102 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff102 ∷ []) lem-pass-TOFF102-vs-CSd03
  q60 : Eqn
  q60 = eqn (CS13⁻ ∷ CS03⁻ ∷ []) (CS03⁻ ∷ CS13⁻ ∷ []) lem-pass-CSd13-vs-CSd03

-- pass [CSd03] [CS13 TOFF102 CSd13 TOFF102]: 4 steps
lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 = derive (CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q58 ∷
   rw⁻ 1 q59 ∷
   rw⁻ 2 q60 ∷
   rw⁻ 3 q59 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (CS13 ∷ S0 ∷ []) (S0 ∷ CS13 ∷ []) lem-pass-CS13-vs-S0
  q62 : Eqn
  q62 = eqn (S0 ∷ Toff102 ∷ []) (Toff102 ∷ S0 ∷ []) (wn 1368 W)
  q63 : Eqn
  q63 = eqn (CS13⁻ ∷ S0 ∷ []) (S0 ∷ CS13⁻ ∷ []) lem-pass-CSd13-vs-S0

-- pass [S0 CSd03] [CS13 TOFF102 CSd13 TOFF102]: 8 steps
lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-S0-CSd03-vs-CS13-TOFF102-CSd13-TOFF102 = derive (S0 ∷ CS03⁻ ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ CS03⁻ ∷ [])
  (rw⁻ 1 q58 ∷
   rw⁻ 0 q61 ∷
   rw⁻ 2 q59 ∷
   rw 1 q62 ∷
   rw⁻ 3 q60 ∷
   rw⁻ 2 q63 ∷
   rw⁻ 4 q59 ∷
   rw 3 q62 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1493 W)
  q65 : Eqn
  q65 = eqn (X2 ∷ CS12 ∷ X2 ∷ []) (X2 ∷ CS12 ∷ X2 ∷ []) (wn 1494 W)
  q66 : Eqn
  q66 = eqn (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X2 CS21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q64 ∷
   rw 1 q65 ∷
   rw 1 q66 ∷
   rw 5 q65 ∷
   rw 5 q64 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1499 W)
  q68 : Eqn
  q68 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ []) (X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1500 W)
  q69 : Eqn
  q69 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X2 CSd21 X2] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 5 steps
lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q67 ∷
   rw 1 q68 ∷
   rw 1 q69 ∷
   rw 5 q68 ∷
   rw 5 q67 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = eqn (CS02⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1466 W)
  q71 : Eqn
  q71 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3)
  q72 : Eqn
  q72 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02⁻ ∷ []) (wn 1467 W)

-- pass [CSd20] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CSd20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (CS02⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (CS02⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 0 q70 ∷
   rw 17 q2 ∷
   rw 1 q71 ∷
   rw 15 q72 ∷
   rw⁻ 14 q2 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = eqn (CK20⁻ ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1464 W)
  q74 : Eqn
  q74 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3)
  q75 : Eqn
  q75 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20⁻ ∷ []) (wn 1465 W)

-- pass [CKd20] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (CK20⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (CK20⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ [])
  (rw 0 q73 ∷
   rw 17 q2 ∷
   rw 1 q74 ∷
   rw 15 q75 ∷
   rw⁻ 14 q2 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (CK20 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1407 W)
  q77 : Eqn
  q77 = eqn (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3)
  q78 : Eqn
  q78 = eqn (X2 ∷ CK20 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CK20 ∷ []) (wn 1408 W)

-- pass [CK20] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (CK20 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CK20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (CK20 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CK20 ∷ [])
  (rw 0 q76 ∷
   rw 17 q2 ∷
   rw 1 q77 ∷
   rw 15 q78 ∷
   rw⁻ 14 q2 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = eqn (CS02 ∷ X2 ∷ []) (X2 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1462 W)
  q80 : Eqn
  q80 = eqn (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3)
  q81 : Eqn
  q81 = eqn (X2 ∷ CS02 ∷ X2 ∷ X2 ∷ []) (X2 ∷ CS02 ∷ []) (wn 1463 W)

-- pass [CS20] [X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 : ⟪ (CS02 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS20-vs-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X2-X3 = derive (CS02 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ X3 ∷ CS02 ∷ [])
  (rw 0 q79 ∷
   rw 17 q2 ∷
   rw 1 q80 ∷
   rw 15 q81 ∷
   rw⁻ 14 q2 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = eqn (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1680 W)
  q83 : Eqn
  q83 = eqn (X1 ∷ CS01 ∷ X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (wn 1669 W)
  q84 : Eqn
  q84 = eqn (X1 ∷ CS01 ∷ X1 ∷ []) (X1 ∷ CS01 ∷ X1 ∷ []) (wn 1670 W)
  q85 : Eqn
  q85 = eqn (X1 ∷ CS01 ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01 ∷ X1 ∷ []) (lem-pass-X1-CS10-X1-vs-CS03-TOFF012-CSd03-TOFF012)

-- pass [X1 CS10 X1] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 7 steps
lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CS10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (X1 ∷ CS01 ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CS01 ∷ X1 ∷ [])
  (rw 0 q82 ∷
   rw 1 q83 ∷
   rw 2 q84 ∷
   rw 2 q85 ∷
   rw 6 q84 ∷
   rw 6 q82 ∷
   rw 7 q83 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ []) (X2 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1678 W)
  q87 : Eqn
  q87 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ X3 ∷ []) (X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1671 W)
  q88 : Eqn
  q88 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ []) (X1 ∷ CS01⁻ ∷ X1 ∷ []) (wn 1679 W)
  q89 : Eqn
  q89 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) (lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012)

-- pass [X1 CSd10 X1] [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3]: 7 steps
lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q86 ∷
   rw 1 q87 ∷
   rw 2 q88 ∷
   rw 2 q89 ∷
   rw 6 q88 ∷
   rw 6 q86 ∷
   rw 7 q87 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = eqn (Toff012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff012 ∷ []) lem-pass-TOFF012-vs-CSd23

-- pass [CSd23] [TOFF012]: 1 steps
lem-pass-CSd23-vs-TOFF012 : ⟪ (CS23⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (Toff012 ∷ CS23⁻ ∷ []) ⟫ʷ
lem-pass-CSd23-vs-TOFF012 = derive (CS23⁻ ∷ Toff012 ∷ []) (Toff012 ∷ CS23⁻ ∷ [])
  (rw⁻ 0 q90 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = eqn (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part0)
  q92 : Eqn
  q92 = eqn (X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ Sw23 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ CS13⁻ ∷ CZ13 ∷ CZ13 ∷ CCZ013 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ []) (lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part1)
  q93 : Eqn
  q93 = eqn (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X0 ∷ CX10 ∷ CX30 ∷ S3 ∷ S3⁻ ∷ CS03 ∷ CS13⁻ ∷ CZ13 ∷ Sw23 ∷ Toff012 ∷ Sw23 ∷ Sw23 ∷ CZ12 ∷ CCZ012 ∷ Sw23 ∷ S0⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ CS03 ∷ []) (lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02-part2)

-- pass [CS03] [X1 X3 TOFF013 X1 X3 S0 CSd02 X1 X3 TOFF013 X1 X3 Sd0 CS02]: 3 steps
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 : ⟪ (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-X1-X3-TOFF013-X1-X3-S0-CSd02-X1-X3-TOFF013-X1-X3-Sd0-CS02 = derive (CS03 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0 ∷ CS02⁻ ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ S0⁻ ∷ CS02 ∷ CS03 ∷ [])
  (rw 0 q91 ∷
   rw 0 q92 ∷
   rw 0 q93 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q95 : Eqn
  q95 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q96 : Eqn
  q96 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q97 : Eqn
  q97 = eqn (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (K0 ∷ Z0 ∷ CZ01 ∷ CZ02 ∷ CCZ012 ∷ K0⁻ ∷ []) (wn 1446 W)
  q98 : Eqn
  q98 = eqn (Z0 ∷ Sw23 ∷ []) (Sw23 ∷ Z0 ∷ []) (low₁-comm (Z) ((Swap ↑)))
  q99 : Eqn
  q99 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q100 : Eqn
  q100 = eqn (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (wn 53 W)
  q101 : Eqn
  q101 = eqn (K0⁻ ∷ K0 ∷ []) [] (wn 1339 W)
  q102 : Eqn
  q102 = eqn (CCZ012 ∷ Z0 ∷ []) (Z0 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-Z0)
  q103 : Eqn
  q103 = eqn (CCZ012 ∷ CZ03 ∷ []) (CZ03 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ03)
  q104 : Eqn
  q104 = eqn [] (K0⁻ ∷ K0 ∷ []) (wn 54 W)
  q105 : Eqn
  q105 = eqn (K0 ∷ Z0 ∷ CZ01 ∷ CZ02 ∷ CCZ012 ∷ K0⁻ ∷ []) (X1 ∷ X2 ∷ Toff012 ∷ X1 ∷ X2 ∷ []) (wn 1447 W)
  q106 : Eqn
  q106 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wn 55 W)

-- pass [TOFF012] [X1 X3 TOFF013 X1 X3]: 130 steps
lem-pass-TOFF012-vs-X1-X3-TOFF013-X1-X3 : ⟪ (Toff012 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-X1-X3-TOFF013-X1-X3 = derive (Toff012 ∷ X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ []) (X1 ∷ X3 ∷ Toff013 ∷ X1 ∷ X3 ∷ Toff012 ∷ [])
  (rw 6 q12 ∷
   rw 5 q13 ∷
   rw 4 q94 ∷
   re 3 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 4 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 3 q95 ∷
   rw 6 q12 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 8 q12 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw⁻ 9 q95 ∷
   rw⁻ 10 q16 ∷
   rw 11 q17 ∷
   rw 10 q16 ∷
   rw 9 q95 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q17 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 3 q95 ∷
   rw 4 q96 ∷
   re 4 8 (Toff012 ∷ []) ∷
   rw 2 q13 ∷
   rw 1 q94 ∷
   rw 2 q97 ∷
   rw⁻ 1 q95 ∷
   rw⁻ 2 q98 ∷
   rw⁻ 3 q20 ∷
   rw 6 q12 ∷
   re 4 3 (CZ03 ∷ []) ∷
   re 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 7 q12 ∷
   re 5 3 (CS13 ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw 9 q12 ∷
   re 7 3 (CS13⁻ ∷ []) ∷
   rw⁻ 8 q15 ∷
   rw 11 q12 ∷
   re 9 3 (CS03 ∷ []) ∷
   rw 5 q12 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw⁻ 9 q15 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q17 ∷
   rw 6 q21 ∷
   re 6 5 (CCZ012 ∷ []) ∷
   re 5 3 (CCZ013 ∷ []) ∷
   rw⁻ 6 q99 ∷
   rw 7 q17 ∷
   rw 0 q100 ∷
   rw 2 q101 ∷
   rw 1 q102 ∷
   rw 2 q23 ∷
   rw 3 q103 ∷
   rw 4 q24 ∷
   rw 5 q104 ∷
   rw 6 q12 ∷
   rw 5 q99 ∷
   re 4 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 6 q12 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 5 q15 ∷
   rw 8 q12 ∷
   re 6 3 (CS13⁻ ∷ []) ∷
   rw⁻ 7 q15 ∷
   rw 10 q12 ∷
   re 8 3 (CS03 ∷ []) ∷
   rw 9 q17 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q17 ∷
   rw 7 q15 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw 5 q15 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw 5 q21 ∷
   re 5 5 (CCZ012 ∷ []) ∷
   re 3 1 (Sw23 ∷ CZ02 ∷ Sw23 ∷ []) ∷
   rw 5 q17 ∷
   rw 2 q20 ∷
   rw 1 q98 ∷
   rw 0 q95 ∷
   rw 1 q105 ∷
   rw⁻ 0 q94 ∷
   rw 1 q26 ∷
   re 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 2 q95 ∷
   rw 5 q12 ∷
   re 3 3 (CS13 ∷ []) ∷
   rw⁻ 4 q15 ∷
   rw 7 q12 ∷
   re 5 3 (CS13⁻ ∷ []) ∷
   rw⁻ 6 q15 ∷
   rw 9 q12 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw⁻ 8 q95 ∷
   rw⁻ 9 q16 ∷
   rw 2 q12 ∷
   rw⁻ 3 q95 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q17 ∷
   rw⁻ 5 q15 ∷
   re 7 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q17 ∷
   rw⁻ 7 q15 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q17 ∷
   rw⁻ 9 q95 ∷
   rw⁻ 10 q16 ∷
   rw 3 q96 ∷
   re 3 8 (Toff012 ∷ []) ∷
   re 2 3 (Toff013 ∷ []) ∷
   rw⁻ 3 q94 ∷
   rw 4 q26 ∷
   rw 5 q17 ∷
   rw 5 q106 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = eqn (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ []) lem-pass-Sd0-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [Sd0]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Sd0 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Sd0 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q107 ∷ []) Eq.refl

private
  q108 : Eqn
  q108 = eqn (Toff201 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff201 ∷ []) lem-pass-TOFF201-vs-CSd03

-- pass [CSd03] [TOFF201]: 1 steps
lem-pass-CSd03-vs-TOFF201 : ⟪ (CS03⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-CSd03-vs-TOFF201 = derive (CS03⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q108 ∷ []) Eq.refl

private
  q109 : Eqn
  q109 = eqn (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1689 W)

-- pass [X2 CS21 X2] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 7 steps
lem-pass-X2-CS21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (X2 ∷ CS12 ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q109 ∷
   rw 1 q64 ∷
   rw 2 q65 ∷
   rw 2 q66 ∷
   rw 6 q65 ∷
   rw 6 q109 ∷
   rw 7 q64 ∷ []) Eq.refl

private
  q110 : Eqn
  q110 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1749 W)

-- pass [X2 CSd21 X2] [X0 X3 CS13 TOFF102 CSd13 TOFF102 X0 X3]: 7 steps
lem-pass-X2-CSd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X0-X3-CS13-TOFF102-CSd13-TOFF102-X0-X3 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q110 ∷
   rw 1 q67 ∷
   rw 2 q68 ∷
   rw 2 q69 ∷
   rw 6 q68 ∷
   rw 6 q110 ∷
   rw 7 q67 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = eqn (Toff102 ∷ ι ∷ []) (ι ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-iI)
  q112 : Eqn
  q112 = eqn (Toff102 ∷ S0⁻ ∷ []) (S0⁻ ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-Sd0)
  q113 : Eqn
  q113 = eqn (Toff102 ∷ S3⁻ ∷ []) (S3⁻ ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-Sd3)
  q114 : Eqn
  q114 = eqn (Toff102 ∷ CS03 ∷ []) (CS03 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-CS03)
  q115 : Eqn
  q115 = eqn (Toff102 ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-X2-TOFF012-X2)
  q116 : Eqn
  q116 = eqn (Toff102 ∷ S0 ∷ []) (S0 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-S0)
  q117 : Eqn
  q117 = eqn (Toff102 ∷ S3 ∷ []) (S3 ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-S3)
  q118 : Eqn
  q118 = eqn (Toff102 ∷ CS03⁻ ∷ []) (CS03⁻ ∷ Toff102 ∷ []) (lem-pass-TOFF102-vs-CSd03)

-- pass [TOFF102] [iI Sd0 Sd3 CS03 X2 TOFF012 X2 iI iI iI S0 S3 CSd03 X2 TOFF012 X2]: 12 steps
lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 : ⟪ (Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-TOFF102-vs-iI-Sd0-Sd3-CS03-X2-TOFF012-X2-iI-iI-iI-S0-S3-CSd03-X2-TOFF012-X2 = derive (Toff102 ∷ ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ []) (ι ∷ S0⁻ ∷ S3⁻ ∷ CS03 ∷ X2 ∷ Toff012 ∷ X2 ∷ ι ∷ ι ∷ ι ∷ S0 ∷ S3 ∷ CS03⁻ ∷ X2 ∷ Toff012 ∷ X2 ∷ Toff102 ∷ [])
  (rw 0 q111 ∷
   rw 1 q112 ∷
   rw 2 q113 ∷
   rw 3 q114 ∷
   rw 4 q115 ∷
   rw 7 q111 ∷
   rw 8 q111 ∷
   rw 9 q111 ∷
   rw 10 q116 ∷
   rw 11 q117 ∷
   rw 12 q118 ∷
   rw 13 q115 ∷ []) Eq.refl

private
  q119 : Eqn
  q119 = eqn (X0 ∷ X2 ∷ []) (X2 ∷ X0 ∷ []) (low₁-comm (X) ((X ↑)))
  q120 : Eqn
  q120 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3)

-- pass [CSd20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CSd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (CS02⁻ ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (CS02⁻ ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 1 q119 ∷
   rw 0 q70 ∷
   rw 19 q2 ∷
   rw 1 q120 ∷
   rw 17 q72 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 16 q2 ∷ []) Eq.refl

private
  q121 : Eqn
  q121 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3)

-- pass [CKd20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CKd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (CK20⁻ ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (CK20⁻ ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CK20⁻ ∷ [])
  (rw 1 q119 ∷
   rw 0 q73 ∷
   rw 19 q2 ∷
   rw 1 q121 ∷
   rw 17 q75 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 16 q2 ∷ []) Eq.refl

private
  q122 : Eqn
  q122 = eqn (X2 ∷ CK20 ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3)

-- pass [CK20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CK20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (CK20 ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CK20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (CK20 ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CK20 ∷ [])
  (rw 1 q119 ∷
   rw 0 q76 ∷
   rw 19 q2 ∷
   rw 1 q122 ∷
   rw 17 q78 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 16 q2 ∷ []) Eq.refl

private
  q123 : Eqn
  q123 = eqn (X2 ∷ CS02 ∷ X2 ∷ X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ []) (X0 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-X0-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X3)

-- pass [CS20] [X0 X2 X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X0 X2 X3]: 7 steps
lem-pass-CS20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 : ⟪ (CS02 ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS20-vs-X0-X2-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X0-X2-X3 = derive (CS02 ∷ X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ []) (X0 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X0 ∷ X2 ∷ X3 ∷ CS02 ∷ [])
  (rw 1 q119 ∷
   rw 0 q79 ∷
   rw 19 q2 ∷
   rw 1 q123 ∷
   rw 17 q81 ∷
   rw⁻ 0 q119 ∷
   rw⁻ 16 q2 ∷ []) Eq.refl

private
  q124 : Eqn
  q124 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3)

-- pass [CSd20] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CSd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (CS02⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (CS02⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS02⁻ ∷ [])
  (rw 0 q70 ∷
   rw 13 q2 ∷
   rw 1 q124 ∷
   rw 11 q72 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q125 : Eqn
  q125 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3)

-- pass [CKd20] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CKd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (CK20⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ []) ⟫ʷ
lem-pass-CKd20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (CK20⁻ ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK20⁻ ∷ [])
  (rw 0 q73 ∷
   rw 13 q2 ∷
   rw 1 q125 ∷
   rw 11 q75 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = eqn (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3)

-- pass [CK20] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CK20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (CK20 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CK20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (CK20 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CK20 ∷ [])
  (rw 0 q76 ∷
   rw 13 q2 ∷
   rw 1 q126 ∷
   rw 11 q78 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q127 : Eqn
  q127 = eqn (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ []) (X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X3)

-- pass [CS20] [X2 X3 S1 K1 CS13 TOFF102 CSd13 TOFF102 Kd1 Sd1 X2 X3]: 5 steps
lem-pass-CS20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 : ⟪ (CS02 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS20-vs-X2-X3-S1-K1-CS13-TOFF102-CSd13-TOFF102-Kd1-Sd1-X2-X3 = derive (CS02 ∷ X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ []) (X2 ∷ X3 ∷ S1 ∷ K1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ K1⁻ ∷ S1⁻ ∷ X2 ∷ X3 ∷ CS02 ∷ [])
  (rw 0 q79 ∷
   rw 13 q2 ∷
   rw 1 q127 ∷
   rw 11 q81 ∷
   rw⁻ 10 q2 ∷ []) Eq.refl

private
  q128 : Eqn
  q128 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK31-X3)
  q129 : Eqn
  q129 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK30 ∷ X3 ∷ []) (X3 ∷ CK30 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK30-X3)
  q130 : Eqn
  q130 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ Toff013 ∷ X3 ∷ []) (X3 ∷ Toff013 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF013-X3)
  q131 : Eqn
  q131 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ []) (X3 ∷ CK30⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd30-X3)
  q132 : Eqn
  q132 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CKd31-X3)

-- Bar(SSKSKK;3,2->0) passes III units 1: 5 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-III-units-1 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-III-units-1 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ CK30 ∷ X3 ∷ X3 ∷ Toff013 ∷ X3 ∷ X3 ∷ CK30⁻ ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q128 ∷
   rw 3 q129 ∷
   rw 6 q130 ∷
   rw 9 q131 ∷
   rw 12 q132 ∷ []) Eq.refl

private
  q133 : Eqn
  q133 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3)

-- Bar(SSKSKK;3,2->0) passes factors of X3 CS13 CS13 CS13 CK31 CS13 CS13 CX32 CS12 CS12 CS12 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CS12 CK21 CS12 CS12 X3: 1 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CS13-CK31-CS13-CS13-CX32-CS12-CS12-CS12-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CS12-CK21-CS12-CS12-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CS13 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CS12 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q133 ∷ []) Eq.refl

private
  q134 : Eqn
  q134 = eqn (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) (lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3)

-- Bar(SSKSKK;3,2->0) passes factors of X3 CS13 CS13 CK31 CS13 CK31 CK31 CX32 CK21 S2 CK21 S2 CS12 CS12 CS12 CK21 S2 CS12 CS12 CS12 CS12 CS12 CS12 CX32 CS12 CS12 CK21 CS12 CK21 CK21 X3: 1 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X3-CS13-CS13-CK31-CS13-CK31-CK31-CX32-CK21-S2-CK21-S2-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX32-CS12-CS12-CK21-CS12-CK21-CK21-X3 = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX32 ∷ CK21 ∷ S2 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CK21 ∷ S2 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CX32 ∷ CS12 ∷ CS12 ∷ CK21 ∷ CS12 ∷ CK21 ∷ CK21 ∷ X3 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK30 ∷ CK30 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q134 ∷ []) Eq.refl

private
  q135 : Eqn
  q135 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK32 ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK32-X3)
  q136 : Eqn
  q136 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CK31-X3)
  q137 : Eqn
  q137 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ Toff123 ∷ X3 ∷ []) (X3 ∷ Toff123 ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-TOFF123-X3)
  q138 : Eqn
  q138 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ []) (X3 ∷ CK31⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd31-X3)
  q139 : Eqn
  q139 = eqn (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) (lem-pass-CS13-CS13-CK31-CS13-CK31-CK31-CX30-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX30-CS01-CS01-CK01-CS01-CK01-CK01-vs-X3-CKd32-X3)

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->1) passes III units 2: 5 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-III-units-2 : ⟪ (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ []) ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶1⟩-passes-III-units-2 = derive (CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) (X3 ∷ CK32 ∷ X3 ∷ X3 ∷ CK31 ∷ X3 ∷ X3 ∷ Toff123 ∷ X3 ∷ X3 ∷ CK31⁻ ∷ X3 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ CS13 ∷ CS13 ∷ CK31 ∷ CS13 ∷ CK31 ∷ CK31 ∷ CX30 ∷ CK01 ∷ S0 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK01 ∷ S0 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX30 ∷ CS01 ∷ CS01 ∷ CK01 ∷ CS01 ∷ CK01 ∷ CK01 ∷ [])
  (rw 0 q135 ∷
   rw 3 q136 ∷
   rw 6 q137 ∷
   rw 9 q138 ∷
   rw 12 q139 ∷ []) Eq.refl
