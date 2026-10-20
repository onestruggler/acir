{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)

module Examples.Groups.Clifford+CS.Four.D.D544 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Four.D.D009 W using (lem-pass-CSd02-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D013 W using (lem-pass-CS23-vs-CS01)
open import Examples.Groups.Clifford+CS.Four.D.D016 W using (lem-pass-CCZ012-vs-CSd02 ; lem-pass-CCZ012-vs-CZ02 ; lem-pass-Sd1-vs-CS13 ; lem-pass-Sd1-vs-CSd13)
open import Examples.Groups.Clifford+CS.Four.D.D021 W using (lem-pass-CS23-vs-CS02 ; lem-pass-CS23-vs-CSd01 ; lem-pass-CS23-vs-CSd02)
open import Examples.Groups.Clifford+CS.Four.D.D022 W using (lem-pass-CS02-vs-CSd23 ; lem-pass-CS02-vs-CZ01 ; lem-pass-CSd02-vs-CSd23 ; lem-pass-CSd02-vs-CZ01)
open import Examples.Groups.Clifford+CS.Four.D.D023 W using (lem-pass-CCZ012-vs-CS01 ; lem-pass-CCZ012-vs-CSd01 ; lem-pass-CS23-vs-S2 ; lem-pass-CS23-vs-Sd2 ; lem-pass-S2-vs-CSd23 ; lem-pass-Sd2-vs-CSd23)
open import Examples.Groups.Clifford+CS.Four.D.D510 W using (lem-pass-CCZ012-vs-CS03 ; lem-pass-CCZ012-vs-CS13)
open import Examples.Groups.Clifford+CS.Four.D.D513 W using (lem-pass-CCZ012-vs-CS23 ; lem-pass-CCZ013-vs-CS23 ; lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13 ; lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23)
open import Examples.Groups.Clifford+CS.Four.D.D514 W using (lem-pass-CCZ013-vs-CCZ123 ; lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D515 W using (lem-pass-CCZ023-vs-CS13 ; lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201 ; lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201)
open import Examples.Groups.Clifford+CS.Four.D.D516 W using (lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102)
open import Examples.Groups.Clifford+CS.Four.D.D517 W using (lem-pass-CCZ012-vs-CSd23 ; lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03 ; lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102 ; lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102)

private
  q1 : Eqn
  q1 = eqn (S1⁻ ∷ Toff102 ∷ []) (Toff102 ∷ S1⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) (wn 1519 W)
  q2 : Eqn
  q2 = eqn (CCZ012 ∷ CS13 ∷ []) (CS13 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS13)
  q3 : Eqn
  q3 = eqn (CS02⁻ ∷ CS13 ∷ []) (CS13 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CS13)
  q4 : Eqn
  q4 = eqn (S1⁻ ∷ CS13 ∷ []) (CS13 ∷ S1⁻ ∷ []) (lem-pass-Sd1-vs-CS13)
  q5 : Eqn
  q5 = eqn (CCZ012 ∷ Toff102 ∷ []) (Toff102 ∷ CZ02 ∷ CCZ012 ∷ []) (wn 1512 W)
  q6 : Eqn
  q6 = eqn (CS02⁻ ∷ Toff102 ∷ []) (Toff102 ∷ CS02⁻ ∷ []) (wn 1352 W)
  q7 : Eqn
  q7 = eqn (CCZ012 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd02)
  q8 : Eqn
  q8 = eqn (CCZ012 ∷ CZ02 ∷ []) (CZ02 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ02)
  q9 : Eqn
  q9 = eqn (CS02⁻ ∷ CS02⁻ ∷ CZ02 ∷ []) [] (wn 1515 W)
  q10 : Eqn
  q10 = eqn (CCZ012 ∷ CCZ012 ∷ []) [] (wn 32 W)
  q11 : Eqn
  q11 = eqn (S1⁻ ∷ CS13⁻ ∷ []) (CS13⁻ ∷ S1⁻ ∷ []) (lem-pass-Sd1-vs-CSd13)

-- pass [Sd1] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ []) ⟫ʷ
lem-pass-Sd1-vs-TOFF102-CS13-TOFF102-CSd13 = derive (S1⁻ ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ S1⁻ ∷ [])
  (rw 0 q1 ∷
   rw 3 q2 ∷
   rw 2 q3 ∷
   rw 1 q4 ∷
   rw 4 q5 ∷
   rw 3 q6 ∷
   rw 2 q1 ∷
   rw 5 q7 ∷
   rw 6 q8 ∷
   rw 4 q9 ∷
   rw 4 q10 ∷
   rw 3 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn [] (CS23 ∷ CS23⁻ ∷ []) (wn 1520 W)
  q13 : Eqn
  q13 = eqn [] (Toff201 ∷ Toff201 ∷ []) (wn 1521 W)
  q14 : Eqn
  q14 = eqn [] (CS23⁻ ∷ CS23 ∷ []) (wn 1522 W)
  q15 : Eqn
  q15 = eqn (X3 ∷ CK32⁻ ∷ X3 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) lem-pass-X3-CKd32-X3-vs-TOFF201-CS23-TOFF201-CSd23
  q16 : Eqn
  q16 = eqn (CS23⁻ ∷ CS23 ∷ []) [] (wn 1523 W)
  q17 : Eqn
  q17 = eqn (Toff201 ∷ Toff201 ∷ []) [] (wn 1524 W)
  q18 : Eqn
  q18 = eqn (CS23 ∷ CS23⁻ ∷ []) [] (wn 1525 W)

-- pass [X3 CKd32 X3] [CS23 TOFF201 CSd23 TOFF201]: 9 steps
lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 : ⟪ (X3 ∷ CK32⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CKd32-X3-vs-CS23-TOFF201-CSd23-TOFF201 = derive (X3 ∷ CK32⁻ ∷ X3 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ X3 ∷ CK32⁻ ∷ X3 ∷ [])
  (rw 0 q12 ∷
   rw 1 q13 ∷
   rw 2 q14 ∷
   rw 3 q13 ∷
   rw⁻ 4 q15 ∷
   rw 10 q16 ∷
   rw 9 q17 ∷
   rw 8 q18 ∷
   rw 7 q17 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = eqn (Toff012 ∷ []) (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (wn 53 W)
  q20 : Eqn
  q20 = eqn (K0⁻ ∷ CS23 ∷ []) (CS23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((CS ↑)))
  q21 : Eqn
  q21 = eqn (CCZ012 ∷ CS23 ∷ []) (CS23 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS23)
  q22 : Eqn
  q22 = eqn (K0 ∷ CS23 ∷ []) (CS23 ∷ K0 ∷ []) (low₁-comm (K) ((CS ↑)))
  q23 : Eqn
  q23 = eqn (K0 ∷ CCZ012 ∷ K0⁻ ∷ []) (Toff012 ∷ []) (wn 55 W)

-- pass [TOFF012] [CS23]: 5 steps
lem-pass-TOFF012-vs-CS23 : ⟪ (Toff012 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CS23 = derive (Toff012 ∷ CS23 ∷ []) (CS23 ∷ Toff012 ∷ [])
  (rw 0 q19 ∷
   rw 2 q20 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 1 q23 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q25 : Eqn
  q25 = eqn (K0 ∷ Sw23 ∷ []) (Sw23 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑)))
  q26 : Eqn
  q26 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = eqn (ι ∷ Sw23 ∷ []) (Sw23 ∷ ι ∷ []) (low₁-comm (iI) ((Swap ↑)))
  q28 : Eqn
  q28 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q29 : Eqn
  q29 = eqn (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) (wn 56 W)
  q30 : Eqn
  q30 = eqn (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wn 43 W)
  q31 : Eqn
  q31 = eqn (K0⁻ ∷ Sw23 ∷ []) (Sw23 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑)))
  q32 : Eqn
  q32 = eqn (CCZ013 ∷ CS23 ∷ []) (CS23 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CS23)

-- pass [TOFF013] [CS23]: 109 steps
lem-pass-TOFF013-vs-CS23 : ⟪ (Toff013 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ Toff013 ∷ []) ⟫ʷ
lem-pass-TOFF013-vs-CS23 = derive (Toff013 ∷ CS23 ∷ []) (CS23 ∷ Toff013 ∷ [])
  (rw 1 q24 ∷
   re 0 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q25 ∷
   rw 3 q24 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q25 ∷
   rw⁻ 7 q27 ∷
   rw 8 q28 ∷
   rw 7 q27 ∷
   rw 6 q25 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw 4 q26 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   rw 2 q26 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q25 ∷
   rw 1 q29 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q19 ∷
   rw⁻ 0 q25 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q24 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q24 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q28 ∷
   rw⁻ 3 q26 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q28 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw 2 q30 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q31 ∷
   rw 3 q28 ∷
   rw 2 q20 ∷
   rw 1 q32 ∷
   rw 0 q22 ∷
   rw 4 q24 ∷
   rw 3 q31 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q24 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q28 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q28 ∷
   rw 5 q26 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw 3 q26 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q28 ∷
   rw 3 q30 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q25 ∷
   rw 2 q23 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q25 ∷
   rw 4 q24 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q25 ∷
   rw⁻ 8 q27 ∷
   rw 1 q24 ∷
   rw⁻ 2 q25 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw⁻ 8 q25 ∷
   rw⁻ 9 q27 ∷
   rw 2 q29 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q28 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = eqn (K0⁻ ∷ CCZ123 ∷ []) (CCZ123 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (CCZ))
  q34 : Eqn
  q34 = eqn (CCZ013 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ013 ∷ []) (lem-pass-CCZ013-vs-CCZ123)
  q35 : Eqn
  q35 = eqn (K0 ∷ CCZ123 ∷ []) (CCZ123 ∷ K0 ∷ []) (low₁-comm (K) (CCZ))

-- pass [TOFF013] [CCZ123]: 109 steps
lem-pass-TOFF013-vs-CCZ123 : ⟪ (Toff013 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff013 ∷ []) ⟫ʷ
lem-pass-TOFF013-vs-CCZ123 = derive (Toff013 ∷ CCZ123 ∷ []) (CCZ123 ∷ Toff013 ∷ [])
  (rw 1 q24 ∷
   re 0 1 (Sw23 ∷ Toff012 ∷ Sw23 ∷ []) ∷
   re 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 0 q25 ∷
   rw 3 q24 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw⁻ 6 q25 ∷
   rw⁻ 7 q27 ∷
   rw 8 q28 ∷
   rw 7 q27 ∷
   rw 6 q25 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw 4 q26 ∷
   re 3 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   rw 2 q26 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q25 ∷
   rw 1 q29 ∷
   re 1 8 (Toff012 ∷ []) ∷
   rw 1 q19 ∷
   rw⁻ 0 q25 ∷
   re 2 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 3 q24 ∷
   re 1 3 (CS13 ∷ []) ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (CS13⁻ ∷ []) ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q24 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q28 ∷
   rw⁻ 3 q26 ∷
   re 5 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 4 q28 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw 2 q30 ∷
   re 2 5 (CCZ012 ∷ []) ∷
   re 1 3 (CCZ013 ∷ []) ∷
   rw⁻ 2 q31 ∷
   rw 3 q28 ∷
   rw 2 q33 ∷
   rw 1 q34 ∷
   rw 0 q35 ∷
   rw 4 q24 ∷
   rw 3 q31 ∷
   re 2 1 (Sw23 ∷ CCZ012 ∷ Sw23 ∷ []) ∷
   re 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) ∷
   rw 4 q24 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q28 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q28 ∷
   rw 5 q26 ∷
   re 4 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 6 q28 ∷
   rw 3 q26 ∷
   re 2 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q28 ∷
   rw 3 q30 ∷
   re 3 5 (CCZ012 ∷ []) ∷
   rw 1 q25 ∷
   rw 2 q23 ∷
   re 2 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0 ∷ ι ∷ []) ∷
   rw⁻ 1 q25 ∷
   rw 4 q24 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (CS13⁻ ∷ []) ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw⁻ 7 q25 ∷
   rw⁻ 8 q27 ∷
   rw 1 q24 ∷
   rw⁻ 2 q25 ∷
   re 4 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (Sw23 ∷ CS12⁻ ∷ Sw23 ∷ []) ∷
   rw 5 q28 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q28 ∷
   rw⁻ 8 q25 ∷
   rw⁻ 9 q27 ∷
   rw 2 q29 ∷
   re 2 8 (Toff012 ∷ []) ∷
   re 1 3 (Toff013 ∷ []) ∷
   rw 2 q28 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CS02 ∷ Toff201 ∷ []) (Toff201 ∷ CS01 ∷ CS02 ∷ CCZ012 ∷ []) (wn 1526 W)
  q37 : Eqn
  q37 = eqn (CS23 ∷ CS02 ∷ []) (CS02 ∷ CS23 ∷ []) lem-pass-CS23-vs-CS02
  q38 : Eqn
  q38 = eqn (CS23 ∷ CS01 ∷ []) (CS01 ∷ CS23 ∷ []) lem-pass-CS23-vs-CS01
  q39 : Eqn
  q39 = eqn (CCZ012 ∷ Toff201 ∷ []) (Toff201 ∷ CZ01 ∷ CCZ012 ∷ []) (wn 1527 W)
  q40 : Eqn
  q40 = eqn (CS01 ∷ Toff201 ∷ []) (Toff201 ∷ CS01 ∷ []) (wn 1528 W)
  q41 : Eqn
  q41 = eqn (CCZ012 ∷ CZ01 ∷ []) (CZ01 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CZ01)
  q42 : Eqn
  q42 = eqn (CS02 ∷ CZ01 ∷ []) (CZ01 ∷ CS02 ∷ []) (lem-pass-CS02-vs-CZ01)
  q43 : Eqn
  q43 = eqn (CS01 ∷ CS01 ∷ CZ01 ∷ []) [] (wn 1529 W)
  q44 : Eqn
  q44 = eqn (CS02 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS02 ∷ []) (lem-pass-CS02-vs-CSd23)

-- pass [CS02] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CS02-vs-TOFF201-CS23-TOFF201-CSd23 = derive (CS02 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02 ∷ [])
  (rw 0 q36 ∷
   rw 3 q21 ∷
   rw⁻ 2 q37 ∷
   rw⁻ 1 q38 ∷
   rw 4 q39 ∷
   rw 3 q36 ∷
   rw 2 q40 ∷
   rw 6 q41 ∷
   rw 5 q42 ∷
   rw 3 q43 ∷
   rw 4 q10 ∷
   rw 3 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = eqn (CS02⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS01⁻ ∷ CS02⁻ ∷ CCZ012 ∷ []) (wn 1530 W)
  q46 : Eqn
  q46 = eqn (CS23 ∷ CS02⁻ ∷ []) (CS02⁻ ∷ CS23 ∷ []) lem-pass-CS23-vs-CSd02
  q47 : Eqn
  q47 = eqn (CS23 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CS23 ∷ []) lem-pass-CS23-vs-CSd01
  q48 : Eqn
  q48 = eqn (CS01⁻ ∷ Toff201 ∷ []) (Toff201 ∷ CS01⁻ ∷ []) (wn 1531 W)
  q49 : Eqn
  q49 = eqn (CS02⁻ ∷ CZ01 ∷ []) (CZ01 ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CZ01)
  q50 : Eqn
  q50 = eqn (CS01⁻ ∷ CS01⁻ ∷ CZ01 ∷ []) [] (wn 1532 W)
  q51 : Eqn
  q51 = eqn (CS02⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CS02⁻ ∷ []) (lem-pass-CSd02-vs-CSd23)

-- pass [CSd02] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ []) ⟫ʷ
lem-pass-CSd02-vs-TOFF201-CS23-TOFF201-CSd23 = derive (CS02⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ CS02⁻ ∷ [])
  (rw 0 q45 ∷
   rw 3 q21 ∷
   rw⁻ 2 q46 ∷
   rw⁻ 1 q47 ∷
   rw 4 q39 ∷
   rw 3 q45 ∷
   rw 2 q48 ∷
   rw 6 q41 ∷
   rw 5 q49 ∷
   rw 3 q50 ∷
   rw 4 q10 ∷
   rw 3 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q53 : Eqn
  q53 = eqn (X3 ∷ Sw23 ∷ []) (Sw23 ∷ X2 ∷ []) (wn 173 W)
  q54 : Eqn
  q54 = eqn (X2 ∷ CK21 ∷ X2 ∷ X0 ∷ []) (X0 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1533 W)
  q55 : Eqn
  q55 = eqn (Sw23 ∷ X2 ∷ []) (X3 ∷ Sw23 ∷ []) (wn 175 W)
  q56 : Eqn
  q56 = eqn (X3 ∷ CK31 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ X3 ∷ []) (wn 1534 W)
  q57 : Eqn
  q57 = eqn (X3 ∷ CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (lem-pass-X3-CK31-X3-vs-CS13-TOFF102-CSd13-TOFF102)

-- pass [X3 CK31 X3] [X0 CS13 TOFF102 CSd13 TOFF102 X0]: 29 steps
lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 : ⟪ (X3 ∷ CK31 ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X3-CK31-X3-vs-X0-CS13-TOFF102-CSd13-TOFF102-X0 = derive (X3 ∷ CK31 ∷ X3 ∷ X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ []) (X0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X0 ∷ X3 ∷ CK31 ∷ X3 ∷ [])
  (rw 4 q24 ∷
   rw 3 q52 ∷
   rw 2 q53 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 3 q28 ∷
   rw 0 q53 ∷
   rw 1 q54 ∷
   rw⁻ 0 q52 ∷
   rw 1 q55 ∷
   rw 4 q24 ∷
   re 2 3 (CK31 ∷ []) ∷
   rw 3 q55 ∷
   rw 4 q28 ∷
   rw 1 q56 ∷
   rw 1 q57 ∷
   rw 5 q56 ∷
   rw 9 q24 ∷
   rw 8 q52 ∷
   rw 7 q53 ∷
   re 6 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 8 q28 ∷
   rw 5 q53 ∷
   rw 6 q54 ∷
   rw⁻ 5 q52 ∷
   rw 6 q55 ∷
   rw 9 q24 ∷
   re 7 3 (CK31 ∷ []) ∷
   rw 8 q55 ∷
   rw 9 q28 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn [] (Sw01 ∷ Sw01 ∷ []) (wn 5 W)
  q59 : Eqn
  q59 = eqn (Sw01 ∷ K1 ∷ []) (K0 ∷ Sw01 ∷ []) (wn 121 W)
  q60 : Eqn
  q60 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q61 : Eqn
  q61 = eqn (Sw01 ∷ CX12 ∷ []) (CX02 ∷ Sw01 ∷ []) (wn 30 W)
  q62 : Eqn
  q62 = eqn (Sw01 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((CS • CS • CS)))
  q63 : Eqn
  q63 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q64 : Eqn
  q64 = eqn (Sw01 ∷ CS12 ∷ []) (CS02 ∷ Sw01 ∷ []) (wn 27 W)
  q65 : Eqn
  q65 = eqn (Sw01 ∷ ι1 ∷ []) (ι ∷ Sw01 ∷ []) (wn 122 W)
  q66 : Eqn
  q66 = eqn (Sw01 ∷ Sw01 ∷ []) [] (wn 31 W)
  q67 : Eqn
  q67 = eqn (ι ∷ Sw01 ∷ []) (Sw01 ∷ ι1 ∷ []) (wn 127 W)
  q68 : Eqn
  q68 = eqn (K0 ∷ Sw01 ∷ []) (Sw01 ∷ K1 ∷ []) (wn 118 W)
  q69 : Eqn
  q69 = eqn (CS02 ∷ Sw01 ∷ []) (Sw01 ∷ CS12 ∷ []) (wn 7 W)
  q70 : Eqn
  q70 = eqn (CX02 ∷ Sw01 ∷ []) (Sw01 ∷ CX12 ∷ []) (wn 74 W)
  q71 : Eqn
  q71 = eqn (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) (wn 125 W)
  q72 : Eqn
  q72 = eqn (Toff123 ∷ []) (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (wn 128 W)
  q73 : Eqn
  q73 = eqn (Sw01 ∷ CX02 ∷ []) (CX12 ∷ Sw01 ∷ []) (wn 24 W)
  q74 : Eqn
  q74 = eqn (Sw01 ∷ CS02 ∷ []) (CS12 ∷ Sw01 ∷ []) (wn 25 W)
  q75 : Eqn
  q75 = eqn (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wn 26 W)
  q76 : Eqn
  q76 = eqn (Sw01 ∷ K1⁻ ∷ []) (K0⁻ ∷ Sw01 ∷ []) (wn 129 W)
  q77 : Eqn
  q77 = eqn (K0⁻ ∷ CS13 ∷ []) (CS13 ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) ((Swap ↑ • CS • Swap ↑)))
  q78 : Eqn
  q78 = eqn (CCZ023 ∷ CS13 ∷ []) (CS13 ∷ CCZ023 ∷ []) (lem-pass-CCZ023-vs-CS13)
  q79 : Eqn
  q79 = eqn (K0 ∷ CS13 ∷ []) (CS13 ∷ K0 ∷ []) (low₁-comm (K) ((Swap ↑ • CS • Swap ↑)))
  q80 : Eqn
  q80 = eqn (K0⁻ ∷ Sw01 ∷ []) (Sw01 ∷ K1⁻ ∷ []) (wn 119 W)
  q81 : Eqn
  q81 = eqn (K1 ∷ CCZ123 ∷ K1⁻ ∷ []) (Toff123 ∷ []) (wn 1437 W)
  q82 : Eqn
  q82 = eqn (Sw01 ∷ K0 ∷ []) (K1 ∷ Sw01 ∷ []) (wn 123 W)
  q83 : Eqn
  q83 = eqn (Sw01 ∷ ι ∷ []) (ι1 ∷ Sw01 ∷ []) (wn 124 W)

-- pass [TOFF023] [CS13]: 117 steps
lem-pass-TOFF023-vs-CS13 : ⟪ (Toff023 ∷ CS13 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff023 ∷ []) ⟫ʷ
lem-pass-TOFF023-vs-CS13 = derive (Toff023 ∷ CS13 ∷ []) (CS13 ∷ Toff023 ∷ [])
  (rw 1 q58 ∷
   re 0 1 (Sw01 ∷ Toff123 ∷ Sw01 ∷ []) ∷
   re 1 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 0 q59 ∷
   rw 1 q60 ∷
   rw 2 q61 ∷
   rw 3 q62 ∷
   rw 4 q61 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q63 ∷
   rw 6 q64 ∷
   rw 7 q63 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 6 q59 ∷
   rw 7 q65 ∷
   rw 8 q66 ∷
   rw 7 q67 ∷
   rw 6 q68 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 7 q63 ∷
   rw 6 q69 ∷
   rw⁻ 5 q63 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 4 q70 ∷
   rw⁻ 3 q62 ∷
   rw 2 q70 ∷
   rw⁻ 1 q60 ∷
   rw 0 q68 ∷
   rw 1 q71 ∷
   re 1 8 (Toff123 ∷ []) ∷
   rw 1 q72 ∷
   rw 0 q59 ∷
   re 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 1 q60 ∷
   rw 2 q61 ∷
   rw 3 q62 ∷
   rw 4 q61 ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q63 ∷
   rw 6 q64 ∷
   rw 7 q63 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 1 q58 ∷
   rw 2 q60 ∷
   rw 3 q73 ∷
   rw 4 q62 ∷
   rw 5 q73 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q63 ∷
   rw 7 q74 ∷
   rw 8 q63 ∷
   re 6 3 (CS13 ∷ []) ∷
   rw 2 q75 ∷
   re 2 5 (CCZ123 ∷ []) ∷
   re 1 3 (CCZ023 ∷ []) ∷
   rw 2 q76 ∷
   rw 3 q66 ∷
   rw 2 q77 ∷
   rw 1 q78 ∷
   rw 0 q79 ∷
   rw 4 q58 ∷
   rw 3 q80 ∷
   re 2 1 (Sw01 ∷ CCZ123 ∷ Sw01 ∷ []) ∷
   re 3 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) ∷
   rw 2 q60 ∷
   rw 3 q61 ∷
   rw 4 q62 ∷
   rw 5 q61 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q63 ∷
   rw 7 q64 ∷
   rw 8 q63 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q66 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 8 q63 ∷
   rw 7 q69 ∷
   rw⁻ 6 q63 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 5 q70 ∷
   rw⁻ 4 q62 ∷
   rw 3 q70 ∷
   rw⁻ 2 q60 ∷
   rw 3 q75 ∷
   re 3 5 (CCZ123 ∷ []) ∷
   rw 1 q68 ∷
   rw 2 q81 ∷
   re 2 1 (K1 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ K1 ∷ ι1 ∷ []) ∷
   rw 1 q59 ∷
   rw 2 q60 ∷
   rw 3 q61 ∷
   rw 4 q62 ∷
   rw 5 q61 ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q63 ∷
   rw 7 q64 ∷
   rw 8 q63 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q59 ∷
   rw 8 q65 ∷
   rw 1 q58 ∷
   rw 2 q82 ∷
   rw 3 q60 ∷
   rw 4 q73 ∷
   rw 5 q62 ∷
   rw 6 q73 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q63 ∷
   rw 8 q74 ∷
   rw 9 q63 ∷
   re 7 3 (CS13 ∷ []) ∷
   rw 8 q82 ∷
   rw 9 q83 ∷
   rw 2 q71 ∷
   re 2 8 (Toff123 ∷ []) ∷
   re 1 3 (Toff023 ∷ []) ∷
   rw 2 q66 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = eqn (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ []) lem-pass-Sd0-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [Sd0]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd0 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ []) ⟫ʷ ≈ ⟪ (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd0 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S0⁻ ∷ []) (S0⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  (rw⁻ 0 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = eqn (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ []) lem-pass-Sd3-vs-CS23-TOFF201-CSd23-TOFF201

-- pass [CS23 TOFF201 CSd23 TOFF201] [Sd3]: 1 steps
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd3 : ⟪ (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ []) ⟫ʷ ≈ ⟪ (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-CS23-TOFF201-CSd23-TOFF201-vs-Sd3 = derive (CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ S3⁻ ∷ []) (S3⁻ ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ Toff201 ∷ [])
  (rw⁻ 0 q85 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (Toff201 ∷ []) (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (wn 1535 W)
  q87 : Eqn
  q87 = eqn (Sw01 ∷ K2⁻ ∷ []) (K2⁻ ∷ Sw01 ∷ []) (low-comm (Swap) ((K • iI)))
  q88 : Eqn
  q88 = eqn (K2⁻ ∷ CS13 ∷ []) (CS13 ∷ K2⁻ ∷ []) (wn 1536 W)
  q89 : Eqn
  q89 = eqn (CCZ012 ∷ CS03 ∷ []) (CS03 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS03)
  q90 : Eqn
  q90 = eqn (Sw01 ∷ K2 ∷ []) (K2 ∷ Sw01 ∷ []) (low-comm (Swap) (K))
  q91 : Eqn
  q91 = eqn (K2 ∷ CS13 ∷ []) (CS13 ∷ K2 ∷ []) (wn 1537 W)
  q92 : Eqn
  q92 = eqn (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (Toff201 ∷ []) (wn 1538 W)

-- pass [TOFF201] [CS03]: 33 steps
lem-pass-TOFF201-vs-CS03 : ⟪ (Toff201 ∷ CS03 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff201 ∷ []) ⟫ʷ
lem-pass-TOFF201-vs-CS03 = derive (Toff201 ∷ CS03 ∷ []) (CS03 ∷ Toff201 ∷ [])
  (rw 0 q86 ∷
   rw 4 q58 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 5 q63 ∷
   rw 4 q69 ∷
   rw⁻ 3 q63 ∷
   re 4 3 (CS13 ∷ []) ∷
   rw⁻ 2 q87 ∷
   rw 3 q88 ∷
   re 3 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 2 q63 ∷
   rw 3 q64 ∷
   rw 4 q63 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q87 ∷
   rw 4 q66 ∷
   rw 1 q89 ∷
   rw 2 q58 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 3 q63 ∷
   rw 2 q69 ∷
   rw⁻ 1 q63 ∷
   re 2 3 (CS13 ∷ []) ∷
   rw⁻ 0 q90 ∷
   rw 1 q91 ∷
   re 1 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 0 q63 ∷
   rw 1 q64 ∷
   rw 2 q63 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 1 q90 ∷
   rw 2 q66 ∷
   rw 1 q92 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = eqn (S2 ∷ Toff201 ∷ []) (Toff201 ∷ S2 ∷ CS01 ∷ CCZ012 ∷ []) (wn 1539 W)
  q94 : Eqn
  q94 = eqn (CS23 ∷ S2 ∷ []) (S2 ∷ CS23 ∷ []) lem-pass-CS23-vs-S2
  q95 : Eqn
  q95 = eqn (CCZ012 ∷ CS01 ∷ []) (CS01 ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CS01)
  q96 : Eqn
  q96 = eqn (S2 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S2 ∷ []) (lem-pass-S2-vs-CSd23)

-- pass [S2] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (S2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2 ∷ []) ⟫ʷ
lem-pass-S2-vs-TOFF201-CS23-TOFF201-CSd23 = derive (S2 ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2 ∷ [])
  (rw 0 q93 ∷
   rw 3 q21 ∷
   rw⁻ 2 q38 ∷
   rw⁻ 1 q94 ∷
   rw 4 q39 ∷
   rw 3 q40 ∷
   rw 2 q93 ∷
   rw 5 q95 ∷
   rw 6 q41 ∷
   rw 4 q43 ∷
   rw 4 q10 ∷
   rw 3 q96 ∷ []) Eq.refl

private
  q97 : Eqn
  q97 = eqn (S2⁻ ∷ Toff201 ∷ []) (Toff201 ∷ S2⁻ ∷ CS01⁻ ∷ CCZ012 ∷ []) (wn 1540 W)
  q98 : Eqn
  q98 = eqn (CS23 ∷ S2⁻ ∷ []) (S2⁻ ∷ CS23 ∷ []) lem-pass-CS23-vs-Sd2
  q99 : Eqn
  q99 = eqn (CCZ012 ∷ CS01⁻ ∷ []) (CS01⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd01)
  q100 : Eqn
  q100 = eqn (S2⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ S2⁻ ∷ []) (lem-pass-Sd2-vs-CSd23)

-- pass [Sd2] [TOFF201 CS23 TOFF201 CSd23]: 12 steps
lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (S2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2⁻ ∷ []) ⟫ʷ
lem-pass-Sd2-vs-TOFF201-CS23-TOFF201-CSd23 = derive (S2⁻ ∷ Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ []) (Toff201 ∷ CS23 ∷ Toff201 ∷ CS23⁻ ∷ S2⁻ ∷ [])
  (rw 0 q97 ∷
   rw 3 q21 ∷
   rw⁻ 2 q47 ∷
   rw⁻ 1 q98 ∷
   rw 4 q39 ∷
   rw 3 q48 ∷
   rw 2 q97 ∷
   rw 5 q99 ∷
   rw 6 q41 ∷
   rw 4 q50 ∷
   rw 4 q10 ∷
   rw 3 q100 ∷ []) Eq.refl

private
  q101 : Eqn
  q101 = eqn (CK31 ∷ X3 ∷ []) (X3 ∷ X3 ∷ CK31 ∷ X3 ∷ []) (wn 1366 W)
  q102 : Eqn
  q102 = eqn (X3 ∷ CK31 ∷ X3 ∷ X3 ∷ []) (X3 ∷ CK31 ∷ []) (wn 1367 W)

-- pass [CK31] [X3 CS13 TOFF102 CSd13 TOFF102 X3]: 3 steps
lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 : ⟪ (CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ []) ⟫ʷ
lem-pass-CK31-vs-X3-CS13-TOFF102-CSd13-TOFF102-X3 = derive (CK31 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ []) (X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X3 ∷ CK31 ∷ [])
  (rw 0 q101 ∷
   rw 1 q57 ∷
   rw 5 q102 ∷ []) Eq.refl

private
  q103 : Eqn
  q103 = eqn (S0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ []) lem-pass-S0-vs-CS13-TOFF102-CSd13-TOFF102

-- pass [CS13 TOFF102 CSd13 TOFF102] [S0]: 1 steps
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0 : ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ
lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-S0 = derive (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S0 ∷ []) (S0 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ [])
  (rw⁻ 0 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = eqn [] (CS13 ∷ CS13⁻ ∷ []) (wn 1376 W)
  q105 : Eqn
  q105 = eqn [] (Toff102 ∷ Toff102 ∷ []) (wn 1377 W)
  q106 : Eqn
  q106 = eqn [] (CS13⁻ ∷ CS13 ∷ []) (wn 1378 W)
  q107 : Eqn
  q107 = eqn (X2 ∷ CS12 ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12 ∷ X2 ∷ []) lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q108 : Eqn
  q108 = eqn (CS13⁻ ∷ CS13 ∷ []) [] (wn 1379 W)
  q109 : Eqn
  q109 = eqn (Toff102 ∷ Toff102 ∷ []) [] (wn 1380 W)
  q110 : Eqn
  q110 = eqn (CS13 ∷ CS13⁻ ∷ []) [] (wn 1381 W)

-- pass [X2 CS21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CS12 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12 ∷ X2 ∷ [])
  (rw 0 q104 ∷
   rw 1 q105 ∷
   rw 2 q106 ∷
   rw 3 q105 ∷
   rw⁻ 4 q107 ∷
   rw 10 q108 ∷
   rw 9 q109 ∷
   rw 8 q110 ∷
   rw 7 q109 ∷ []) Eq.refl

private
  q111 : Eqn
  q111 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) lem-pass-X2-CSd21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [X2 CSd21 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd21-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CS12⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ [])
  (rw 0 q104 ∷
   rw 1 q105 ∷
   rw 2 q106 ∷
   rw 3 q105 ∷
   rw⁻ 4 q111 ∷
   rw 10 q108 ∷
   rw 9 q109 ∷
   rw 8 q110 ∷
   rw 7 q109 ∷ []) Eq.refl

private
  q112 : Eqn
  q112 = eqn (Sw01 ∷ X3 ∷ []) (X3 ∷ Sw01 ∷ []) (low-comm (Swap) ((X ↑)))
  q113 : Eqn
  q113 = eqn (Sw01 ∷ X2 ∷ []) (X2 ∷ Sw01 ∷ []) (low-comm (Swap) (X))
  q114 : Eqn
  q114 = eqn (CS02⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CS12⁻ ∷ []) (wn 76 W)
  q115 : Eqn
  q115 = eqn (X2 ∷ CS12⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12⁻ ∷ X2 ∷ []) (wn 1499 W)
  q116 : Eqn
  q116 = eqn (Sw01 ∷ CS12⁻ ∷ []) (CS02⁻ ∷ Sw01 ∷ []) (wn 29 W)
  q117 : Eqn
  q117 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1541 W)
  q118 : Eqn
  q118 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (lem-pass-X2-CSd20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q119 : Eqn
  q119 = eqn (X2 ∷ CS02⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) (wn 1542 W)

-- pass [X2 CSd20 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 25 steps
lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CSd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (X2 ∷ CS02⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CS02⁻ ∷ X2 ∷ [])
  (rw 4 q58 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q114 ∷
   rw⁻ 0 q113 ∷
   rw 1 q115 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q116 ∷
   rw 3 q113 ∷
   rw 4 q66 ∷
   rw 1 q117 ∷
   rw 5 q118 ∷
   rw 9 q119 ∷
   rw 17 q58 ∷
   rw⁻ 16 q112 ∷
   rw⁻ 15 q113 ∷
   rw 14 q114 ∷
   rw⁻ 13 q113 ∷
   rw 14 q115 ∷
   rw 13 q112 ∷
   rw 14 q113 ∷
   rw 15 q116 ∷
   rw 16 q113 ∷
   rw 17 q66 ∷ []) Eq.refl

private
  q120 : Eqn
  q120 = eqn (CK20⁻ ∷ Sw01 ∷ []) (Sw01 ∷ CK21⁻ ∷ []) (wn 137 W)
  q121 : Eqn
  q121 = eqn (X2 ∷ CK21⁻ ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21⁻ ∷ X2 ∷ []) (wn 1497 W)
  q122 : Eqn
  q122 = eqn (Sw01 ∷ CK21⁻ ∷ []) (CK20⁻ ∷ Sw01 ∷ []) (wn 139 W)
  q123 : Eqn
  q123 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1543 W)
  q124 : Eqn
  q124 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (lem-pass-X2-CKd20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q125 : Eqn
  q125 = eqn (X2 ∷ CK20⁻ ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) (wn 1544 W)

-- pass [X2 CKd20 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 25 steps
lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CKd20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (X2 ∷ CK20⁻ ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CK20⁻ ∷ X2 ∷ [])
  (rw 4 q58 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q120 ∷
   rw⁻ 0 q113 ∷
   rw 1 q121 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q122 ∷
   rw 3 q113 ∷
   rw 4 q66 ∷
   rw 1 q123 ∷
   rw 5 q124 ∷
   rw 9 q125 ∷
   rw 17 q58 ∷
   rw⁻ 16 q112 ∷
   rw⁻ 15 q113 ∷
   rw 14 q120 ∷
   rw⁻ 13 q113 ∷
   rw 14 q121 ∷
   rw 13 q112 ∷
   rw 14 q113 ∷
   rw 15 q122 ∷
   rw 16 q113 ∷
   rw 17 q66 ∷ []) Eq.refl

private
  q126 : Eqn
  q126 = eqn (CK20 ∷ Sw01 ∷ []) (Sw01 ∷ CK21 ∷ []) (wn 140 W)
  q127 : Eqn
  q127 = eqn (X2 ∷ CK21 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CK21 ∷ X2 ∷ []) (wn 1495 W)
  q128 : Eqn
  q128 = eqn (Sw01 ∷ CK21 ∷ []) (CK20 ∷ Sw01 ∷ []) (wn 142 W)
  q129 : Eqn
  q129 = eqn (X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1545 W)
  q130 : Eqn
  q130 = eqn (X2 ∷ CK20 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (lem-pass-X2-CK20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q131 : Eqn
  q131 = eqn (X2 ∷ CK20 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CK20 ∷ X2 ∷ []) (wn 1546 W)

-- pass [X2 CK20 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 25 steps
lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CK20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (X2 ∷ CK20 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CK20 ∷ X2 ∷ [])
  (rw 4 q58 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q126 ∷
   rw⁻ 0 q113 ∷
   rw 1 q127 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q128 ∷
   rw 3 q113 ∷
   rw 4 q66 ∷
   rw 1 q129 ∷
   rw 5 q130 ∷
   rw 9 q131 ∷
   rw 17 q58 ∷
   rw⁻ 16 q112 ∷
   rw⁻ 15 q113 ∷
   rw 14 q126 ∷
   rw⁻ 13 q113 ∷
   rw 14 q127 ∷
   rw 13 q112 ∷
   rw 14 q113 ∷
   rw 15 q128 ∷
   rw 16 q113 ∷
   rw 17 q66 ∷ []) Eq.refl

private
  q132 : Eqn
  q132 = eqn (X2 ∷ CS12 ∷ X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ CS12 ∷ X2 ∷ []) (wn 1493 W)
  q133 : Eqn
  q133 = eqn (X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ []) (S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1547 W)
  q134 : Eqn
  q134 = eqn (X2 ∷ CS02 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (lem-pass-X2-CS20-X2-vs-CS13-TOFF102-CSd13-TOFF102)
  q135 : Eqn
  q135 = eqn (X2 ∷ CS02 ∷ X2 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ []) (S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X2 ∷ CS02 ∷ X2 ∷ []) (wn 1548 W)

-- pass [X2 CS20 X2] [X3 Sd1 Kd1 S1 S1 CS13 TOFF102 CSd13 TOFF102 Sd1 Sd1 K1 S1 X3]: 25 steps
lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 : ⟪ (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS20-X2-vs-X3-Sd1-Kd1-S1-S1-CS13-TOFF102-CSd13-TOFF102-Sd1-Sd1-K1-S1-X3 = derive (X2 ∷ CS02 ∷ X2 ∷ X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ K1⁻ ∷ S1 ∷ S1 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ S1⁻ ∷ K1 ∷ S1 ∷ X3 ∷ X2 ∷ CS02 ∷ X2 ∷ [])
  (rw 4 q58 ∷
   rw⁻ 3 q112 ∷
   rw⁻ 2 q113 ∷
   rw 1 q69 ∷
   rw⁻ 0 q113 ∷
   rw 1 q132 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷
   rw 2 q64 ∷
   rw 3 q113 ∷
   rw 4 q66 ∷
   rw 1 q133 ∷
   rw 5 q134 ∷
   rw 9 q135 ∷
   rw 17 q58 ∷
   rw⁻ 16 q112 ∷
   rw⁻ 15 q113 ∷
   rw 14 q69 ∷
   rw⁻ 13 q113 ∷
   rw 14 q132 ∷
   rw 13 q112 ∷
   rw 14 q113 ∷
   rw 15 q64 ∷
   rw 16 q113 ∷
   rw 17 q66 ∷ []) Eq.refl

private
  q136 : Eqn
  q136 = eqn [] (CS02 ∷ CS02⁻ ∷ []) (wn 1357 W)
  q137 : Eqn
  q137 = eqn [] (Toff012 ∷ Toff012 ∷ []) (wn 45 W)
  q138 : Eqn
  q138 = eqn [] (CS02⁻ ∷ CS02 ∷ []) (wn 231 W)
  q139 : Eqn
  q139 = eqn (X1 ∷ CS01⁻ ∷ X1 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) lem-pass-X1-CSd10-X1-vs-TOFF012-CS03-TOFF012-CSd03
  q140 : Eqn
  q140 = eqn (CS02⁻ ∷ CS02 ∷ []) [] (wn 1358 W)
  q141 : Eqn
  q141 = eqn (Toff012 ∷ Toff012 ∷ []) [] (wn 227 W)
  q142 : Eqn
  q142 = eqn (CS02 ∷ CS02⁻ ∷ []) [] (wn 1342 W)

-- pass [X1 CSd10 X1] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ ≈ ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ []) ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CS03-TOFF012-CSd03-TOFF012 = derive (X1 ∷ CS01⁻ ∷ X1 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X1 ∷ CS01⁻ ∷ X1 ∷ [])
  (rw 0 q24 ∷
   rw 1 q136 ∷
   rw 2 q24 ∷
   re 0 3 (CS03 ∷ []) ∷
   rw 3 q24 ∷
   re 1 3 (CS03⁻ ∷ []) ∷
   rw 2 q28 ∷
   rw 1 q137 ∷
   rw 2 q24 ∷
   rw 3 q138 ∷
   rw 4 q24 ∷
   re 2 3 (CS03⁻ ∷ []) ∷
   rw 5 q24 ∷
   re 3 3 (CS03 ∷ []) ∷
   rw 4 q28 ∷
   rw 3 q137 ∷
   rw⁻ 4 q139 ∷
   rw 12 q24 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q28 ∷
   re 10 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 12 q28 ∷
   rw 11 q140 ∷
   rw 10 q28 ∷
   rw 9 q141 ∷
   rw 10 q24 ∷
   re 9 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 11 q28 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q28 ∷
   rw 9 q142 ∷
   rw 8 q28 ∷
   rw 7 q141 ∷ []) Eq.refl

private
  q143 : Eqn
  q143 = eqn (K0⁻ ∷ CS23⁻ ∷ []) (CS23⁻ ∷ K0⁻ ∷ []) (low₁-comm ((K • iI)) (((CS • CS • CS) ↑)))
  q144 : Eqn
  q144 = eqn (CCZ012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ CCZ012 ∷ []) (lem-pass-CCZ012-vs-CSd23)
  q145 : Eqn
  q145 = eqn (K0 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ K0 ∷ []) (low₁-comm (K) (((CS • CS • CS) ↑)))

-- pass [TOFF012] [CSd23]: 5 steps
lem-pass-TOFF012-vs-CSd23 : ⟪ (Toff012 ∷ CS23⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS23⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-TOFF012-vs-CSd23 = derive (Toff012 ∷ CS23⁻ ∷ []) (CS23⁻ ∷ Toff012 ∷ [])
  (rw 0 q19 ∷
   rw 2 q143 ∷
   rw 1 q144 ∷
   rw 0 q145 ∷
   rw 1 q23 ∷ []) Eq.refl
