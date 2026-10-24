{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD660 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D660 (W : Ws) (Sᴰ : SD660) where

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
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CX21-X2 : St 1222
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CX21-X2 = pickᴰ 0 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CX31-X3 : St 1742
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CX31-X3 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CX21-X2 : St 1743
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CX21-X2 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CX32-X3 : St 1744
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CX32-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CX32-X3 : St 1745
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CX32-X3 = pickᴰ 4 Sᴰ
  lem-pass-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1746
  lem-pass-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1747
  lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 6 Sᴰ
  lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1748
  lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 7 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 : St 1664
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3 = pickᴰ 8 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 : St 1665
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3 = pickᴰ 9 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2 : St 1678
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2 = pickᴰ 10 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3 : St 1682
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3 = pickᴰ 11 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 : St 1685
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 = pickᴰ 12 Sᴰ
  lem-pass-CKd30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : St 1749
  lem-pass-CKd30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = pickᴰ 13 Sᴰ
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 : St 1750
  lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123 = pickᴰ 14 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123 : St 1734
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123 = pickᴰ 15 Sᴰ
  lem-pass-CZ12-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 : St 1751
  lem-pass-CZ12-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 16 Sᴰ
  lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 : St 1752
  lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 17 Sᴰ

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
  q8 = sE 1750 lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-iI-iI-Z1-Z2-CZ12-Z3-CZ13-CZ23-CCZ123
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

-- pass [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3] [CCZ123]: 76 steps
lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-CCZ123 : ⟪ (ℓ "丒丘丞中九丮九丒丘丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丒丘丞中九丮九丒丘丞") ⟫ʷ
lem-pass-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3-vs-CCZ123 = derive (ℓ "丒丘丞中九丮九丒丘丞乜") (ℓ "乜丒丘丞中九丮九丒丘丞")
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
  q29 = wE 1 W
  q30 : Eqn
  q30 = wE 3 W
  q31 : Eqn
  q31 = wE 464 W
  q32 : Eqn
  q32 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q33 : Eqn
  q33 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q34 : Eqn
  q34 = wE 1935 W
  q35 : Eqn
  q35 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q36 : Eqn
  q36 = sE 1749 lem-pass-CKd30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q37 : Eqn
  q37 = sE 1748 lem-pass-CSd10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q38 : Eqn
  q38 = sE 1746 lem-pass-CK30-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q39 : Eqn
  q39 = sE 1747 lem-pass-CS10-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3
  q40 : Eqn
  q40 = wE 1936 W
  q41 : Eqn
  q41 = wE 151 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 X2 X3 CS03 TOFF012 CSd03 TOFF012 X1 X2 X3]: 132 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丘丞中九丮九丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞中九丮九丒丘丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-X3-CS03-TOFF012-CSd03-TOFF012-X1-X2-X3 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒丘丞中九丮九丒丘丞") (ℓ "丒丘丞中九丮九丒丘丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 31 q29 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q30 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q30 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q30 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q30 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q30 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q30 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q30 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q30 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q30 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q30 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q30 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q30 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q30 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q30 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q30 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q30 ∷
   rw 14 q31 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q30 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q30 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q30 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q30 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q30 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q30 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q30 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q30 ∷
   rw 5 q32 ∷
   rw 4 q32 ∷
   rw 3 q33 ∷
   rw 2 q32 ∷
   rw 1 q32 ∷
   rw 0 q32 ∷
   rw 1 q34 ∷
   rw⁻ 0 q32 ∷
   rw 3 q29 ∷
   re 1 3 (ℓ "乑") ∷
   rw⁻ 2 q35 ∷
   rw 5 q29 ∷
   re 3 3 (ℓ "乒") ∷
   rw 4 q30 ∷
   rw 3 q36 ∷
   rw 2 q37 ∷
   rw 1 q38 ∷
   rw 0 q39 ∷
   rw 14 q29 ∷
   re 13 1 (ℓ "乏久乏") ∷
   rw 15 q30 ∷
   rw 12 q35 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q30 ∷
   rw 10 q32 ∷
   rw 11 q40 ∷
   rw⁻ 10 q32 ∷
   rw⁻ 11 q32 ∷
   rw⁻ 12 q32 ∷
   rw⁻ 13 q33 ∷
   rw⁻ 14 q32 ∷
   rw⁻ 15 q32 ∷
   rw 18 q29 ∷
   re 16 3 (ℓ "乀") ∷
   rw 19 q29 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q29 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q29 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q29 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q29 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q29 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q29 ∷
   re 23 3 (ℓ "乑") ∷
   rw 24 q41 ∷
   rw 27 q29 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q29 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q29 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q29 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q29 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q29 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q29 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q29 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q29 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q29 ∷
   re 34 3 (ℓ "乀") ∷
   rw 37 q29 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q29 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q29 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q29 ∷
   re 38 3 (ℓ "乑") ∷
   rw 41 q29 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q29 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q30 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = sE 1742 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CX31-X3
  q43 : Eqn
  q43 = sE 1665 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-TOFF103-X3

-- Bar(SSSKSS;3,2->0) passes II-white units 1 0: 2 steps
lem-Bar⟨SSSKSS32-⟶0⟩-passes-II-white-units-1-0 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乓丞丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乓丞丞乡丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-Bar⟨SSSKSS32-⟶0⟩-passes-II-white-units-1-0 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乓丞丞乡丞") (ℓ "丞乓丞丞乡丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 0 q42 ∷
   rw 3 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = sE 1752 lem-pass-Z1-CZ12-CZ13-CCZ123-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [Z1 CZ12 CZ13 CCZ123]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Z1-CZ12-CZ13-CCZ123 : ⟪ (ℓ "中九丮九专丸丿乜") ⟫ʷ ≈ ⟪ (ℓ "专丸丿乜中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-Z1-CZ12-CZ13-CCZ123 = derive (ℓ "中九丮九专丸丿乜") (ℓ "专丸丿乜中九丮九")
  (rw⁻ 0 q44 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = sE 1222 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-CX21-X2
  q46 : Eqn
  q46 = sE 1678 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2

-- Bar(SSKSKK;2,3->0) passes II-white units 1 0: 2 steps
lem-Bar⟨SSKSKK23-⟶0⟩-passes-II-white-units-1-0 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乆丘丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘乆丘丘习丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-Bar⟨SSKSKK23-⟶0⟩-passes-II-white-units-1-0 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘乆丘丘习丘") (ℓ "丘乆丘丘习丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 0 q45 ∷
   rw 3 q46 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = eqn (ℓ "丌专") (ℓ "专丌") (low₁-comm (X) (Z))
  q48 : Eqn
  q48 = eqn (ℓ "丌丸") (ℓ "丸丌") (low₁-comm (X) (CZ))
  q49 : Eqn
  q49 = eqn (ℓ "丌丿") (ℓ "丿丌") (low₁-comm (X) ((Swap ↑ • CZ • Swap ↑)))
  q50 : Eqn
  q50 = eqn (ℓ "丌乜") (ℓ "乜丌") (low₁-comm (X) (CCZ))
  q51 : Eqn
  q51 = sE 1734 lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123
  q52 : Eqn
  q52 = wE 1990 W

-- pass [X0 X2 X3 CS13 TOFF102 CSd13 TOFF102 X0 X2 X3] [CCZ123]: 28 steps
lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CCZ123 : ⟪ (ℓ "丌丘丞丽习举习丌丘丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丌丘丞丽习举习丌丘丞") ⟫ʷ
lem-pass-X0-X2-X3-CS13-TOFF102-CSd13-TOFF102-X0-X2-X3-vs-CCZ123 = derive (ℓ "丌丘丞丽习举习丌丘丞乜") (ℓ "乜丌丘丞丽习举习丌丘丞")
  (rw 9 q1 ∷
   rw 8 q2 ∷
   rw 10 q3 ∷
   rw 7 q47 ∷
   rw 8 q48 ∷
   rw 9 q49 ∷
   rw 10 q50 ∷
   rw 3 q51 ∷
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
   rw 0 q47 ∷
   rw 1 q47 ∷
   rw 2 q48 ∷
   rw 3 q47 ∷
   rw 4 q49 ∷
   rw 5 q47 ∷
   rw 6 q48 ∷
   rw 7 q49 ∷
   rw 8 q50 ∷
   rw 0 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = sE 1743 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-CX21-X2
  q54 : Eqn
  q54 = sE 1685 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2

-- Bar(SSSKSS;2,3->0) passes II-white units 1 0: 2 steps
lem-Bar⟨SSSKSS23-⟶0⟩-passes-II-white-units-1-0 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乆丘丘习丘") ⟫ʷ ≈ ⟪ (ℓ "丘乆丘丘习丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-Bar⟨SSSKSS23-⟶0⟩-passes-II-white-units-1-0 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘乆丘丘习丘") (ℓ "丘乆丘丘习丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 0 q53 ∷
   rw 3 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = sE 1744 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CX32-X3
  q56 : Eqn
  q56 = sE 1664 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF203-X3

-- Bar(SSKSKK;3,1->0) passes II-white units 2 0: 2 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-II-white-units-2-0 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乖丞丞乤丞") ⟫ʷ ≈ ⟪ (ℓ "丞乖丞丞乤丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-II-white-units-2-0 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乖丞丞乤丞") (ℓ "丞乖丞丞乤丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 0 q55 ∷
   rw 3 q56 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = sE 1745 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CX32-X3
  q58 : Eqn
  q58 = sE 1682 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3

-- Bar(SSSKSS;3,1->0) passes II-white units 2 0: 2 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-II-white-units-2-0 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丞乤丞") ⟫ʷ ≈ ⟪ (ℓ "丞乖丞丞乤丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-II-white-units-2-0 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乖丞丞乤丞") (ℓ "丞乖丞丞乤丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q57 ∷
   rw 3 q58 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = sE 1751 lem-pass-CZ12-CCZ123-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [CZ12 CCZ123]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ12-CCZ123 : ⟪ (ℓ "九中九丮丸乜") ⟫ʷ ≈ ⟪ (ℓ "丸乜九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CZ12-CCZ123 = derive (ℓ "九中九丮丸乜") (ℓ "丸乜九中九丮")
  (rw⁻ 0 q59 ∷ []) Eq.refl
