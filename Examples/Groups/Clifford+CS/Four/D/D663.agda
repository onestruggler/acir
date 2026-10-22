{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD663 ; pickᴰ)

module Examples.Groups.Clifford+CS.Four.D.D663 (W : Ws) (Sᴰ : SD663) where

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
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : St 1756
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = pickᴰ 0 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123 : St 1754
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123 = pickᴰ 1 Sᴰ
  lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : St 1757
  lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 2 Sᴰ
  lem-hyb-sym-23 : St 1758
  lem-hyb-sym-23 = pickᴰ 3 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : St 1759
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = pickᴰ 4 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 : St 1760
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2 = pickᴰ 5 Sᴰ
  lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 : St 1761
  lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 6 Sᴰ
  lem-pass-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 : St 1762
  lem-pass-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 7 Sᴰ
  lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 : St 1763
  lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = eqn (X3 ∷ CCZ123 ∷ []) (CZ12 ∷ CCZ123 ∷ X3 ∷ []) (wn 1985 W)
  q2 : Eqn
  q2 = eqn (X2 ∷ CZ12 ∷ []) (Z1 ∷ CZ12 ∷ X2 ∷ []) (wn 1986 W)
  q3 : Eqn
  q3 = eqn (X2 ∷ CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ X2 ∷ []) (wn 1987 W)
  q4 : Eqn
  q4 = eqn (X1 ∷ Z1 ∷ []) (ι ∷ ι ∷ Z1 ∷ X1 ∷ []) (wn 1993 W)
  q5 : Eqn
  q5 = eqn (X1 ∷ CZ12 ∷ []) (Z2 ∷ CZ12 ∷ X1 ∷ []) (wn 1994 W)
  q6 : Eqn
  q6 = eqn (X1 ∷ CZ13 ∷ []) (Z3 ∷ CZ13 ∷ X1 ∷ []) (wn 1995 W)
  q7 : Eqn
  q7 = eqn (X1 ∷ CCZ123 ∷ []) (CZ23 ∷ CCZ123 ∷ X1 ∷ []) (wn 1996 W)
  q8 : Eqn
  q8 = eqn (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (ι ∷ ι ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123)
  q9 : Eqn
  q9 = eqn (ι ∷ []) (ι3 ∷ []) (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑)))))
  q10 : Eqn
  q10 = eqn (X3 ∷ ι3 ∷ []) (ι3 ∷ X3 ∷ []) (wn 1967 W)
  q11 : Eqn
  q11 = eqn (ι3 ∷ []) (ι ∷ []) (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI))))
  q12 : Eqn
  q12 = eqn (Z1 ∷ X3 ∷ []) (X3 ∷ Z1 ∷ []) (low-comm ((Z ↑)) ((X ↑)))
  q13 : Eqn
  q13 = eqn (Z2 ∷ X3 ∷ []) (X3 ∷ Z2 ∷ []) (low₃-comm ((Z ↑ ↑)) (X))
  q14 : Eqn
  q14 = eqn (CZ12 ∷ X3 ∷ []) (X3 ∷ CZ12 ∷ []) (low₃-comm ((CZ ↑)) (X))
  q15 : Eqn
  q15 = eqn (X3 ∷ Z3 ∷ []) (ι3 ∷ ι3 ∷ Z3 ∷ X3 ∷ []) (wn 1997 W)
  q16 : Eqn
  q16 = eqn (X3 ∷ CZ13 ∷ []) (Z1 ∷ CZ13 ∷ X3 ∷ []) (wn 1988 W)
  q17 : Eqn
  q17 = eqn (X3 ∷ CZ23 ∷ []) (Z2 ∷ CZ23 ∷ X3 ∷ []) (wn 1998 W)
  q18 : Eqn
  q18 = eqn (X2 ∷ ι ∷ []) (ι ∷ X2 ∷ []) (wn 1999 W)
  q19 : Eqn
  q19 = eqn (Z1 ∷ X2 ∷ []) (X2 ∷ Z1 ∷ []) (low-comm ((Z ↑)) (X))
  q20 : Eqn
  q20 = eqn (X2 ∷ Z2 ∷ []) (ι ∷ ι ∷ Z2 ∷ X2 ∷ []) (wn 2000 W)
  q21 : Eqn
  q21 = eqn (X2 ∷ Z3 ∷ []) (Z3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (Z))
  q22 : Eqn
  q22 = eqn (X2 ∷ CZ13 ∷ []) (CZ13 ∷ X2 ∷ []) (wn 1989 W)
  q23 : Eqn
  q23 = eqn (X2 ∷ CZ23 ∷ []) (Z3 ∷ CZ23 ∷ X2 ∷ []) (wn 2001 W)
  q24 : Eqn
  q24 = eqn (X1 ∷ ι ∷ []) (ι ∷ X1 ∷ []) (wn 2002 W)
  q25 : Eqn
  q25 = eqn (X1 ∷ Z2 ∷ []) (Z2 ∷ X1 ∷ []) (low-comm ((X ↑)) (Z))
  q26 : Eqn
  q26 = eqn (X1 ∷ Z3 ∷ []) (Z3 ∷ X1 ∷ []) (low-comm ((X ↑)) ((Z ↑)))
  q27 : Eqn
  q27 = eqn (X1 ∷ CZ23 ∷ []) (CZ23 ∷ X1 ∷ []) (low-comm ((X ↑)) (CZ))
  q28 : Eqn
  q28 = eqn (ι3 ∷ ι3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ ι3 ∷ ι3 ∷ Z2 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z2 ∷ CZ12 ∷ ι3 ∷ ι3 ∷ Z3 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z3 ∷ CZ13 ∷ ι3 ∷ ι3 ∷ Z2 ∷ Z3 ∷ CZ23 ∷ ι3 ∷ ι3 ∷ Z1 ∷ Z2 ∷ CZ12 ∷ Z3 ∷ CZ13 ∷ CZ23 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wn 2003 W)

-- pass [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3] [CCZ123]: 76 steps
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123 : ⟪ (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123 = derive (X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X1 ∷ X2 ∷ X3 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ X1 ∷ X2 ∷ X3 ∷ [])
  (rw 9 q1 ∷
   rw 8 q2 ∷
   rw 10 q3 ∷
   rw 7 q4 ∷
   rw 10 q5 ∷
   rw 12 q6 ∷
   rw 14 q7 ∷
   rw 3 q8 ∷
   rw 3 q9 ∷
   rw 2 q10 ∷
   rw 2 q11 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   rw 3 q11 ∷
   rw⁻ 4 q12 ∷
   rw⁻ 5 q13 ∷
   rw⁻ 6 q14 ∷
   rw 7 q15 ∷
   rw 7 q11 ∷
   rw 8 q11 ∷
   rw 10 q16 ∷
   rw 12 q17 ∷
   rw 14 q1 ∷
   rw 1 q18 ∷
   rw 2 q18 ∷
   rw⁻ 3 q19 ∷
   rw 4 q20 ∷
   rw 7 q2 ∷
   rw 9 q18 ∷
   rw 10 q18 ∷
   rw 11 q21 ∷
   rw⁻ 12 q19 ∷
   rw 13 q22 ∷
   rw 14 q20 ∷
   rw 17 q23 ∷
   rw 19 q2 ∷
   rw 21 q3 ∷
   rw 0 q24 ∷
   rw 1 q24 ∷
   rw 2 q4 ∷
   rw 5 q24 ∷
   rw 6 q24 ∷
   rw 7 q25 ∷
   rw 8 q4 ∷
   rw 11 q5 ∷
   rw 13 q24 ∷
   rw 14 q24 ∷
   rw 15 q26 ∷
   rw 16 q4 ∷
   rw 19 q6 ∷
   rw 21 q24 ∷
   rw 22 q24 ∷
   rw 23 q25 ∷
   rw 24 q26 ∷
   rw 25 q27 ∷
   rw 26 q4 ∷
   rw 29 q5 ∷
   rw 31 q6 ∷
   rw 33 q7 ∷
   rw 0 q9 ∷
   rw 1 q9 ∷
   rw 2 q9 ∷
   rw 3 q9 ∷
   rw 5 q9 ∷
   rw 6 q9 ∷
   rw 8 q9 ∷
   rw 9 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 16 q9 ∷
   rw 17 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 26 q9 ∷
   rw 27 q9 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = eqn (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [Z1 CZ12 CZ13 CCZ123]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123 : ⟪ (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123 = derive (Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff012 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ [])
  (rw⁻ 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (X0 ∷ Z1 ∷ []) (Z1 ∷ X0 ∷ []) (low₁-comm (X) (Z))
  q31 : Eqn
  q31 = eqn (X0 ∷ CZ12 ∷ []) (CZ12 ∷ X0 ∷ []) (low₁-comm (X) (CZ))
  q32 : Eqn
  q32 = eqn (X0 ∷ CZ13 ∷ []) (CZ13 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑ • CZ • Swap ↑)))
  q33 : Eqn
  q33 = eqn (X0 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ []) (low₁-comm (X) (CCZ))
  q34 : Eqn
  q34 = eqn (Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ []) (lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123)
  q35 : Eqn
  q35 = eqn (Z1 ∷ Z1 ∷ CZ12 ∷ Z1 ∷ CZ13 ∷ Z1 ∷ CZ12 ∷ CZ13 ∷ CCZ123 ∷ []) (CCZ123 ∷ []) (wn 1990 W)

-- pass [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3] [CCZ123]: 28 steps
lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123 : ⟪ (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123 = derive (X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ CCZ123 ∷ []) (CCZ123 ∷ X0 ∷ X2 ∷ X3 ∷ Toff102 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ X0 ∷ X2 ∷ X3 ∷ [])
  (rw 9 q1 ∷
   rw 8 q2 ∷
   rw 10 q3 ∷
   rw 7 q30 ∷
   rw 8 q31 ∷
   rw 9 q32 ∷
   rw 10 q33 ∷
   rw 3 q34 ∷
   rw⁻ 2 q12 ∷
   rw⁻ 3 q14 ∷
   rw 4 q16 ∷
   rw 6 q1 ∷
   rw⁻ 1 q19 ∷
   rw 2 q2 ∷
   rw⁻ 4 q19 ∷
   rw 5 q22 ∷
   rw 6 q2 ∷
   rw 8 q3 ∷
   rw 0 q30 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 3 q30 ∷
   rw 4 q32 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 7 q32 ∷
   rw 8 q33 ∷
   rw 0 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = eqn (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ []) lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [CSd13]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd13 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd13 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = eqn (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ []) lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [S1 CSd13]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ []) (S1 ∷ CS13⁻ ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = eqn (X2 ∷ CS13 ∷ []) (CS13 ∷ X2 ∷ []) (wn 257 W)
  q39 : Eqn
  q39 = eqn (X2 ∷ Toff102 ∷ []) (X2 ∷ Toff102 ∷ X2 ∷ X2 ∷ []) (wn 1778 W)
  q40 : Eqn
  q40 = eqn (X2 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ X2 ∷ []) (wn 258 W)
  q41 : Eqn
  q41 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2)
  q42 : Eqn
  q42 = eqn (X2 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (Toff102 ∷ X2 ∷ []) (wn 1777 W)

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ []) ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ [])
  (rw 5 q38 ∷
   rw 6 q39 ∷
   rw 9 q40 ∷
   rw 10 q39 ∷
   rw 1 q41 ∷
   rw 0 q38 ∷
   rw 1 q42 ∷
   rw 2 q40 ∷
   rw 3 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = eqn (X3 ∷ CS13 ∷ []) (S1 ∷ CS13⁻ ∷ X3 ∷ []) (wn 1958 W)
  q44 : Eqn
  q44 = eqn (Toff102 ∷ X3 ∷ []) (X3 ∷ Toff102 ∷ []) (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q45 : Eqn
  q45 = eqn (X3 ∷ CS13⁻ ∷ []) (S1⁻ ∷ CS13 ∷ X3 ∷ []) (wn 1959 W)
  q46 : Eqn
  q46 = eqn (S1 ∷ X2 ∷ []) (X2 ∷ S1 ∷ []) (low-comm ((S ↑)) (X))
  q47 : Eqn
  q47 = eqn (S1⁻ ∷ X2 ∷ []) (X2 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) (X))
  q48 : Eqn
  q48 = eqn (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (S1 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ S1⁻ ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2)
  q49 : Eqn
  q49 = eqn (S1 ∷ X3 ∷ []) (X3 ∷ S1 ∷ []) (low-comm ((S ↑)) ((X ↑)))
  q50 : Eqn
  q50 = eqn (X2 ∷ X3 ∷ []) (X3 ∷ X2 ∷ []) (low₃-comm ((X ↑ ↑)) (X))
  q51 : Eqn
  q51 = eqn (S1⁻ ∷ X3 ∷ []) (X3 ∷ S1⁻ ∷ []) (low-comm (((S • S • S) ↑)) ((X ↑)))
  q52 : Eqn
  q52 = eqn (S1 ∷ S1⁻ ∷ CS13 ∷ []) (CS13 ∷ []) (wn 1960 W)
  q53 : Eqn
  q53 = eqn (S1⁻ ∷ S1 ∷ CS13⁻ ∷ []) (CS13⁻ ∷ []) (wn 1961 W)

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [CS13 TOFF102 CSd13 TOFF102]: 31 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ []) ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ []) (CS13 ∷ Toff102 ∷ CS13⁻ ∷ Toff102 ∷ X2 ∷ X3 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ X2 ∷ X3 ∷ [])
  (rw 7 q43 ∷
   rw⁻ 9 q44 ∷
   rw 10 q45 ∷
   rw⁻ 12 q44 ∷
   rw⁻ 6 q46 ∷
   rw 7 q40 ∷
   rw 8 q39 ∷
   rw⁻ 11 q47 ∷
   rw 12 q38 ∷
   rw 13 q39 ∷
   rw 2 q48 ∷
   rw⁻ 1 q49 ∷
   rw 2 q45 ∷
   rw⁻ 4 q50 ∷
   rw⁻ 5 q44 ∷
   rw⁻ 6 q50 ∷
   rw⁻ 7 q51 ∷
   rw 8 q43 ∷
   rw⁻ 10 q50 ∷
   rw⁻ 11 q44 ∷
   rw⁻ 12 q50 ∷
   rw⁻ 0 q46 ∷
   rw⁻ 1 q47 ∷
   rw 2 q38 ∷
   rw 3 q42 ∷
   rw⁻ 4 q47 ∷
   rw⁻ 5 q46 ∷
   rw 6 q40 ∷
   rw 7 q42 ∷
   rw 0 q52 ∷
   rw 2 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn [] (Sw23 ∷ Sw23 ∷ []) (wn 1 W)
  q55 : Eqn
  q55 = eqn (S2 ∷ Sw23 ∷ []) (Sw23 ∷ S3 ∷ []) (wn 476 W)
  q56 : Eqn
  q56 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q57 : Eqn
  q57 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q58 : Eqn
  q58 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q59 : Eqn
  q59 = eqn (Sw23 ∷ Sw23 ∷ []) [] (wn 3 W)
  q60 : Eqn
  q60 = eqn (S3 ∷ Sw23 ∷ []) (Sw23 ∷ S2 ∷ []) (wn 464 W)
  q61 : Eqn
  q61 = eqn (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) (lem-hyb-sym-23)
  q62 : Eqn
  q62 = eqn (Sw23 ∷ S3 ∷ []) (S2 ∷ Sw23 ∷ []) (wn 372 W)
  q63 : Eqn
  q63 = eqn (Sw23 ∷ S2 ∷ []) (S3 ∷ Sw23 ∷ []) (wn 151 W)

-- hyb sym 23 @0132: 279 steps
lem-hyb-sym-23-at0132 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ []) ⟫ʷ
lem-hyb-sym-23-at0132 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK30 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S3 ∷ CK30 ∷ [])
  (rw 80 q54 ∷
   rw 79 q54 ∷
   re 80 3 (CK30 ∷ []) ∷
   rw 78 q55 ∷
   rw 77 q56 ∷
   rw 76 q56 ∷
   rw 75 q56 ∷
   rw 74 q56 ∷
   rw 73 q56 ∷
   rw 72 q56 ∷
   rw 71 q57 ∷
   rw 70 q58 ∷
   rw 69 q56 ∷
   rw 68 q56 ∷
   rw 67 q56 ∷
   re 66 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 68 q59 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q59 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q59 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q59 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q59 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q59 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q59 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q59 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q59 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q59 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 58 q59 ∷
   rw 55 q60 ∷
   rw 54 q60 ∷
   rw 53 q60 ∷
   rw 52 q60 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q59 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q59 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q59 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q59 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q59 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q59 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q59 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q59 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q59 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q59 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q59 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q59 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q59 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q59 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q59 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q59 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q59 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q59 ∷
   re 33 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 35 q59 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q59 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q59 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q59 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q59 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q59 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q59 ∷
   re 26 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 28 q59 ∷
   rw 25 q60 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 26 q59 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q59 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q59 ∷
   rw 21 q54 ∷
   re 22 3 (CK30 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q59 ∷
   re 19 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 21 q59 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q59 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q59 ∷
   re 16 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 18 q59 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q59 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 16 q59 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q59 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q59 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q59 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q59 ∷
   rw 9 q60 ∷
   re 8 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 10 q59 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q59 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 8 q59 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q59 ∷
   re 4 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 6 q59 ∷
   rw 3 q56 ∷
   rw 2 q57 ∷
   rw 1 q56 ∷
   rw 0 q56 ∷
   rw 1 q61 ∷
   rw⁻ 0 q56 ∷
   rw⁻ 1 q56 ∷
   rw⁻ 2 q57 ∷
   rw⁻ 3 q56 ∷
   re 5 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 4 q59 ∷
   re 6 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q59 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 6 q59 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q59 ∷
   re 9 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 8 q59 ∷
   rw 9 q62 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q59 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q59 ∷
   re 13 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q59 ∷
   re 14 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q59 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q59 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 15 q59 ∷
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 16 q59 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q59 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q59 ∷
   re 20 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 19 q59 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q59 ∷
   rw 23 q54 ∷
   re 21 3 (CK30 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q59 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q59 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q59 ∷
   rw 25 q62 ∷
   re 27 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 26 q59 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q59 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q59 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q59 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q59 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q59 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q59 ∷
   re 34 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 33 q59 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q59 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q59 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q59 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q59 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q59 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q59 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q59 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q59 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q59 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q59 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q59 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q59 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q59 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q59 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q59 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q59 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q59 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q59 ∷
   rw 52 q62 ∷
   rw 53 q62 ∷
   rw 54 q62 ∷
   rw 55 q62 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 56 q59 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q59 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q59 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q59 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q59 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q59 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q59 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q59 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q59 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q59 ∷
   re 67 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 66 q59 ∷
   rw⁻ 67 q56 ∷
   rw⁻ 68 q56 ∷
   rw⁻ 69 q56 ∷
   rw⁻ 70 q58 ∷
   rw⁻ 71 q57 ∷
   rw⁻ 72 q56 ∷
   rw⁻ 73 q56 ∷
   rw⁻ 74 q56 ∷
   rw⁻ 75 q56 ∷
   rw⁻ 76 q56 ∷
   rw⁻ 77 q56 ∷
   rw 78 q63 ∷
   rw 81 q54 ∷
   re 79 3 (CK30 ∷ []) ∷
   rw 80 q59 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = eqn (CZ13 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CZ13 ∷ CCZ123 ∷ []) lem-pass-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [CZ13 CCZ123]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ13-CCZ123 : ⟪ (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CZ13 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CZ13 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ []) ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ13-CCZ123 = derive (CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ CZ13 ∷ CCZ123 ∷ []) (CZ13 ∷ CCZ123 ∷ CS03 ∷ Toff012 ∷ CS03⁻ ∷ Toff012 ∷ [])
  (rw⁻ 0 q64 ∷ []) Eq.refl
