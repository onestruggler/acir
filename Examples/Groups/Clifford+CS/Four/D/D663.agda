{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD663 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D663 (W : Ws) (Sᴰ : SD663) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Four.Str using (ℓ)
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
  q1 = wE 1985 W
  q2 : Eqn
  q2 = wE 1986 W
  q3 : Eqn
  q3 = wE 1987 W
  q4 : Eqn
  q4 = wE 1993 W
  q5 : Eqn
  q5 = wE 1994 W
  q6 : Eqn
  q6 = wE 1995 W
  q7 : Eqn
  q7 = wE 1996 W
  q8 : Eqn
  q8 = sE 1756 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123
  q9 : Eqn
  q9 = eqn (ℓ "一") (ℓ "七") (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑)))))
  q10 : Eqn
  q10 = wE 1967 W
  q11 : Eqn
  q11 = eqn (ℓ "七") (ℓ "一") (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI))))
  q12 : Eqn
  q12 = eqn (ℓ "专丞") (ℓ "丞专") (low-comm ((Z ↑)) ((X ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "丙丞") (ℓ "丞丙") (low₃-comm ((Z ↑ ↑)) (X))
  q14 : Eqn
  q14 = eqn (ℓ "丸丞") (ℓ "丞丸") (low₃-comm ((CZ ↑)) (X))
  q15 : Eqn
  q15 = wE 1997 W
  q16 : Eqn
  q16 = wE 1988 W
  q17 : Eqn
  q17 = wE 1998 W
  q18 : Eqn
  q18 = wE 1999 W
  q19 : Eqn
  q19 = eqn (ℓ "专丘") (ℓ "丘专") (low-comm ((Z ↑)) (X))
  q20 : Eqn
  q20 = wE 2000 W
  q21 : Eqn
  q21 = eqn (ℓ "丘丟") (ℓ "丟丘") (low₃-comm ((X ↑ ↑)) (Z))
  q22 : Eqn
  q22 = wE 1989 W
  q23 : Eqn
  q23 = wE 2001 W
  q24 : Eqn
  q24 = wE 2002 W
  q25 : Eqn
  q25 = eqn (ℓ "丒丙") (ℓ "丙丒") (low-comm ((X ↑)) (Z))
  q26 : Eqn
  q26 = eqn (ℓ "丒丟") (ℓ "丟丒") (low-comm ((X ↑)) ((Z ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "丒之") (ℓ "之丒") (low-comm ((X ↑)) (CZ))
  q28 : Eqn
  q28 = wE 2003 W

-- pass [X1 X2 X3 TOFF012 CS03 TOFF012 CSd03 X1 X2 X3] [CCZ123]: 76 steps
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123 : ⟪ (ℓ "丒丘丞九中九丮丒丘丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丒丘丞九中九丮丒丘丞") ⟫ʷ
lem-pass-X1-X2-X3-TOFF012-CS03-TOFF012-CSd03-X1-X2-X3-vs-CCZ123 = derive (ℓ "丒丘丞九中九丮丒丘丞乜") (ℓ "乜丒丘丞九中九丮丒丘丞")
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
  q29 = sE 1757 lem-pass-Z1-CZ12-CZ13-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [Z1 CZ12 CZ13 CCZ123]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123 : ⟪ (ℓ "九中九丮专丸丿乜") ⟫ʷ ≈ ⟪ (ℓ "专丸丿乜九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Z1-CZ12-CZ13-CCZ123 = derive (ℓ "九中九丮专丸丿乜") (ℓ "专丸丿乜九中九丮")
  (rw⁻ 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = eqn (ℓ "丌专") (ℓ "专丌") (low₁-comm (X) (Z))
  q31 : Eqn
  q31 = eqn (ℓ "丌丸") (ℓ "丸丌") (low₁-comm (X) (CZ))
  q32 : Eqn
  q32 = eqn (ℓ "丌丿") (ℓ "丿丌") (low₁-comm (X) ((Swap ↑ • CZ • Swap ↑)))
  q33 : Eqn
  q33 = eqn (ℓ "丌乜") (ℓ "乜丌") (low₁-comm (X) (CCZ))
  q34 : Eqn
  q34 = sE 1754 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123
  q35 : Eqn
  q35 = wE 1990 W

-- pass [X0 X2 X3 TOFF102 CS13 TOFF102 CSd13 X0 X2 X3] [CCZ123]: 28 steps
lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123 : ⟪ (ℓ "丌丘丞习丽习举丌丘丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丌丘丞习丽习举丌丘丞") ⟫ʷ
lem-pass-X0-X2-X3-TOFF102-CS13-TOFF102-CSd13-X0-X2-X3-vs-CCZ123 = derive (ℓ "丌丘丞习丽习举丌丘丞乜") (ℓ "乜丌丘丞习丽习举丌丘丞")
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
  q36 = sE 1761 lem-pass-CSd13-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [CSd13]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd13 : ⟪ (ℓ "中九丮九举") ⟫ʷ ≈ ⟪ (ℓ "举中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CSd13 = derive (ℓ "中九丮九举") (ℓ "举中九丮九")
  (rw⁻ 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 1763 lem-pass-S1-CSd13-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [S1 CSd13]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13 : ⟪ (ℓ "中九丮九与举") ⟫ʷ ≈ ⟪ (ℓ "与举中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13 = derive (ℓ "中九丮九与举") (ℓ "与举中九丮九")
  (rw⁻ 0 q37 ∷ []) Eq.refl

private
  q38 : Eqn
  q38 = wE 257 W
  q39 : Eqn
  q39 = wE 1778 W
  q40 : Eqn
  q40 = wE 258 W
  q41 : Eqn
  q41 = sE 1759 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2
  q42 : Eqn
  q42 = wE 1777 W

-- pass [X2 CS03 TOFF012 CSd03 TOFF012 X2] [CS13 TOFF102 CSd13 TOFF102]: 9 steps
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘中九丮九丘丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘中九丮九丘") ⟫ʷ
lem-pass-X2-CS03-TOFF012-CSd03-TOFF012-X2-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘中九丮九丘丽习举习") (ℓ "丽习举习丘中九丮九丘")
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
  q43 = wE 1958 W
  q44 : Eqn
  q44 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q45 : Eqn
  q45 = wE 1959 W
  q46 : Eqn
  q46 = eqn (ℓ "与丘") (ℓ "丘与") (low-comm ((S ↑)) (X))
  q47 : Eqn
  q47 = eqn (ℓ "丏丘") (ℓ "丘丏") (low-comm (((S • S • S) ↑)) (X))
  q48 : Eqn
  q48 = sE 1760 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-S1-CSd13-X2-TOFF102-X2-Sd1-CS13-X2-TOFF102-X2
  q49 : Eqn
  q49 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q50 : Eqn
  q50 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q51 : Eqn
  q51 = eqn (ℓ "丏丞") (ℓ "丞丏") (low-comm (((S • S • S) ↑)) ((X ↑)))
  q52 : Eqn
  q52 = wE 1960 W
  q53 : Eqn
  q53 = wE 1961 W

-- pass [X2 X3 CS03 TOFF012 CSd03 TOFF012 X2 X3] [CS13 TOFF102 CSd13 TOFF102]: 31 steps
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丘丞中九丮九丘丞丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丘丞中九丮九丘丞") ⟫ʷ
lem-pass-X2-X3-CS03-TOFF012-CSd03-TOFF012-X2-X3-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丘丞中九丮九丘丞丽习举习") (ℓ "丽习举习丘丞中九丮九丘丞")
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
  q54 = wE 1 W
  q55 : Eqn
  q55 = wE 476 W
  q56 : Eqn
  q56 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q57 : Eqn
  q57 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q58 : Eqn
  q58 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q59 : Eqn
  q59 = wE 3 W
  q60 : Eqn
  q60 = wE 464 W
  q61 : Eqn
  q61 = sE 1758 lem-hyb-sym-23
  q62 : Eqn
  q62 = wE 372 W
  q63 : Eqn
  q63 = wE 151 W

-- hyb sym 23 @0132: 279 steps
lem-hyb-sym-23-at0132 : ⟪ (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄") ⟫ʷ ≈ ⟪ (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") ⟫ʷ
lem-hyb-sym-23-at0132 = derive (ℓ "丠丠临丠乀中中中乑业中中中中中中乀中中乑中乄中中中业乑中中中中中中乀中中中中中中中中中中中中中中中中中中业业业业乑中中中中中中中中中乀丠丠丠与临丠丠丠丠丠丠且乄") (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑")
  (rw 80 q54 ∷
   rw 79 q54 ∷
   re 80 3 (ℓ "乑") ∷
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
   re 66 1 (ℓ "乏丹乏") ∷
   rw 68 q59 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q59 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q59 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q59 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q59 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q59 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q59 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q59 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q59 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q59 ∷
   re 56 1 (ℓ "乏乄乏") ∷
   rw 58 q59 ∷
   rw 55 q60 ∷
   rw 54 q60 ∷
   rw 53 q60 ∷
   rw 52 q60 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q59 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q59 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q59 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q59 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q59 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q59 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q59 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q59 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q59 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q59 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q59 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q59 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q59 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q59 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q59 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q59 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q59 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q59 ∷
   re 33 1 (ℓ "乏丹乏") ∷
   rw 35 q59 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q59 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q59 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q59 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q59 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q59 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q59 ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw 28 q59 ∷
   rw 25 q60 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q59 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q59 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q59 ∷
   rw 21 q54 ∷
   re 22 3 (ℓ "乑") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q59 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q59 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q59 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q59 ∷
   re 16 1 (ℓ "乏丹乏") ∷
   rw 18 q59 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q59 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q59 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q59 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q59 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q59 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q59 ∷
   rw 9 q60 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw 10 q59 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q59 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q59 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q59 ∷
   re 4 1 (ℓ "乏丹乏") ∷
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
   re 5 1 (ℓ "乏丹乏") ∷
   rw 4 q59 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q59 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q59 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q59 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 8 q59 ∷
   rw 9 q62 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q59 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q59 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q59 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q59 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q59 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q59 ∷
   re 17 1 (ℓ "乏丹乏") ∷
   rw 16 q59 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 17 q59 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 18 q59 ∷
   re 20 1 (ℓ "乏乄乏") ∷
   rw 19 q59 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 20 q59 ∷
   rw 23 q54 ∷
   re 21 3 (ℓ "乑") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 22 q59 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 23 q59 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 24 q59 ∷
   rw 25 q62 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 26 q59 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 27 q59 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 28 q59 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 29 q59 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 30 q59 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 31 q59 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 32 q59 ∷
   re 34 1 (ℓ "乏丹乏") ∷
   rw 33 q59 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 34 q59 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 35 q59 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q59 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 37 q59 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 38 q59 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q59 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 40 q59 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 41 q59 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q59 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 43 q59 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 44 q59 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 45 q59 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 46 q59 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 47 q59 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 48 q59 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 49 q59 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 50 q59 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 51 q59 ∷
   rw 52 q62 ∷
   rw 53 q62 ∷
   rw 54 q62 ∷
   rw 55 q62 ∷
   re 57 1 (ℓ "乏乄乏") ∷
   rw 56 q59 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 57 q59 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 58 q59 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 59 q59 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 60 q59 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 61 q59 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 62 q59 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 63 q59 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 64 q59 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 65 q59 ∷
   re 67 1 (ℓ "乏丹乏") ∷
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
   re 79 3 (ℓ "乑") ∷
   rw 80 q59 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = sE 1762 lem-pass-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [CZ13 CCZ123]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ13-CCZ123 : ⟪ (ℓ "中九丮九丿乜") ⟫ʷ ≈ ⟪ (ℓ "丿乜中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-CZ13-CCZ123 = derive (ℓ "中九丮九丿乜") (ℓ "丿乜中九丮九")
  (rw⁻ 0 q64 ∷ []) Eq.refl
