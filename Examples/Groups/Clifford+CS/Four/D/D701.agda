{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD701 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D701 (W : Ws) (Sᴰ : SD701) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 38
  lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 0 Sᴰ
  lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : St 1901
  lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 1 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : St 1902
  lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 2 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : St 1903
  lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 3 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 : St 1904
  lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 4 Sᴰ
  lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : St 1905
  lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : St 1906
  lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = pickᴰ 6 Sᴰ
  lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : St 1907
  lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = pickᴰ 7 Sᴰ
  lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12 : St 1908
  lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 8 Sᴰ
  lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 : St 1909
  lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013 = pickᴰ 9 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS12 : St 1910
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS12 = pickᴰ 10 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd12 : St 1911
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd12 = pickᴰ 11 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0 : St 1912
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0 = pickᴰ 12 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0 : St 1913
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0 = pickᴰ 13 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 14 Sᴰ
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X1-X3-TOFF013-X1-X3 : St 1914
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X1-X3-TOFF013-X1-X3 = pickᴰ 15 Sᴰ
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF013-X3 : St 1915
  lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF013-X3 = pickᴰ 16 Sᴰ
  lem-C3-PP3 : St 1916
  lem-C3-PP3 = pickᴰ 17 Sᴰ
  lem-S2-at0213 : St 1917
  lem-S2-at0213 = pickᴰ 18 Sᴰ
  lem-S2-at1023 : St 1918
  lem-S2-at1023 = pickᴰ 19 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03 : St 1919
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03 = pickᴰ 20 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03 : St 1920
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03 = pickᴰ 21 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2 : St 1921
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2 = pickᴰ 22 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2 : St 1922
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2 = pickᴰ 23 Sᴰ
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3 : St 1923
  lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3 = pickᴰ 24 Sᴰ
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 : St 1924
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 25 Sᴰ
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1925
  lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 26 Sᴰ
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1926
  lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 27 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1927
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 28 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 1928
  lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 29 Sᴰ
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02 : St 1929
  lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02 = pickᴰ 30 Sᴰ
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 1930
  lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 31 Sᴰ
  lem-S2-ᵖ-1 : St 1931
  lem-S2-ᵖ-1 = pickᴰ 32 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 2040 W
  q4 : Eqn
  q4 = sE 1916 lem-C3-PP3
  q5 : Eqn
  q5 = wE 1358 W

-- R0: 19 steps
lem-R0 : ⟪ (ℓ "九中九中") ⟫ʷ ≈ ⟪ (ℓ "中九中九") ⟫ʷ
lem-R0 = derive (ℓ "九中九中") (ℓ "中九中九")
  (rw 4 q1 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   rw 4 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丮") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q2 ∷
   rw⁻ 0 q4 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q2 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q2 ∷
   rw 5 q5 ∷
   rw 4 q2 ∷ []) Eq.refl

private
  q6 : Eqn
  q6 = sE 1778 lem-S2
  q7 : Eqn
  q7 = sE 1927 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF013-CS02-TOFF013-CSd02
  q8 : Eqn
  q8 = sE 1778 lem-S2

-- pass [X3 TOFF012 CS03 TOFF012 CSd03 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丞九中九丮丞九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丞九中九丮丞") ⟫ʷ
lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丞九中九丮丞九中九丮") (ℓ "九中九丮丞九中九丮丞")
  (rw 6 q6 ∷
   rw 0 q7 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = sE 1922 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2
  q10 : Eqn
  q10 = sE 1912 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0
  q11 : Eqn
  q11 = sE 1920 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03
  q12 : Eqn
  q12 = sE 1913 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-Sd0
  q13 : Eqn
  q13 = sE 1919 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03

-- pass [TOFF012 CS03 TOFF012 CSd03] [X2 TOFF012 X2 S0 CSd03 X2 TOFF012 X2 Sd0 CS03]: 6 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 : ⟪ (ℓ "九中九丮丘九丘丈丮丘九丘三中") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丈丮丘九丘三中九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-TOFF012-X2-S0-CSd03-X2-TOFF012-X2-Sd0-CS03 = derive (ℓ "九中九丮丘九丘丈丮丘九丘三中") (ℓ "丘九丘丈丮丘九丘三中九中九丮")
  (rw 0 q9 ∷
   rw 3 q10 ∷
   rw 4 q11 ∷
   rw 5 q9 ∷
   rw 8 q12 ∷
   rw 9 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 1921 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2

-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X2 TOFF012 X1 X2 S0 CSd03 X1 X2 TOFF012 X1 X2 Sd0 CS03]: 6 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03 : ⟪ (ℓ "九中九丮丒丘九丒丘丈丮丒丘九丒丘三中") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘丈丮丒丘九丒丘三中九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X2-TOFF012-X1-X2-S0-CSd03-X1-X2-TOFF012-X1-X2-Sd0-CS03 = derive (ℓ "九中九丮丒丘九丒丘丈丮丒丘九丒丘三中") (ℓ "丒丘九丒丘丈丮丒丘九丒丘三中九中九丮")
  (rw 0 q14 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q14 ∷
   rw 12 q12 ∷
   rw 13 q13 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = sE 1918 lem-S2-at1023
  q16 : Eqn
  q16 = sE 1915 lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X3-TOFF013-X3
  q17 : Eqn
  q17 = sE 1918 lem-S2-at1023

-- pass [TOFF102 CS13 TOFF102 CSd13] [X3 TOFF013 X3]: 3 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3 : ⟪ (ℓ "习丽习举丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X3-TOFF013-X3 = derive (ℓ "习丽习举丞乞丞") (ℓ "丞乞丞习丽习举")
  (rw 0 q15 ∷
   rw 0 q16 ∷
   rw⁻ 3 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = sE 1925 lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [TOFF012 CS03 TOFF012 CSd03] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 1 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "九中九丮丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "九中九丮丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞九中九丮")
  (rw⁻ 0 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = sE 1914 lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-X1-X3-TOFF013-X1-X3

-- pass [TOFF102 CS13 TOFF102 CSd13] [X1 X3 TOFF013 X1 X3]: 3 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3 : ⟪ (ℓ "习丽习举丒丞乞丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-X1-X3-TOFF013-X1-X3 = derive (ℓ "习丽习举丒丞乞丒丞") (ℓ "丒丞乞丒丞习丽习举")
  (rw 0 q15 ∷
   rw 0 q19 ∷
   rw⁻ 5 q17 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = sE 1920 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd03

-- pass [CSd03] [TOFF012 CS03 TOFF012 CSd03]: 1 steps
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丮九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丮") ⟫ʷ
lem-pass-CSd03-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丮九中九丮") (ℓ "九中九丮丮")
  (rw⁻ 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = sE 1919 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03

-- pass [CS03] [TOFF012 CS03 TOFF012 CSd03]: 1 steps
lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "中九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮中") ⟫ʷ
lem-pass-CS03-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "中九中九丮") (ℓ "九中九丮中")
  (rw⁻ 0 q21 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = wE 5 W
  q23 : Eqn
  q23 = wE 2041 W
  q24 : Eqn
  q24 = wE 121 W
  q25 : Eqn
  q25 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q26 : Eqn
  q26 = wE 30 W
  q27 : Eqn
  q27 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q28 : Eqn
  q28 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q29 : Eqn
  q29 = wE 27 W
  q30 : Eqn
  q30 = wE 122 W
  q31 : Eqn
  q31 = wE 123 W
  q32 : Eqn
  q32 = wE 24 W
  q33 : Eqn
  q33 = wE 25 W
  q34 : Eqn
  q34 = wE 124 W
  q35 : Eqn
  q35 = wE 125 W
  q36 : Eqn
  q36 = wE 31 W
  q37 : Eqn
  q37 = wE 2042 W
  q38 : Eqn
  q38 = wE 1694 W
  q39 : Eqn
  q39 = sE 1917 lem-S2-at0213
  q40 : Eqn
  q40 = wE 227 W
  q41 : Eqn
  q41 = wE 1342 W

-- S2 @0213 ^-1: 141 steps
lem-S2-at0213-ᵖ-1 : ⟪ (ℓ "中九丮九") ⟫ʷ ≈ ⟪ (ℓ "丠也両也") ⟫ʷ
lem-S2-at0213-ᵖ-1 = derive (ℓ "中九丮九") (ℓ "丠也両也")
  (rw 4 q22 ∷
   rw 5 q23 ∷
   re 5 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 4 q24 ∷
   rw 5 q25 ∷
   rw 6 q26 ∷
   rw 7 q27 ∷
   rw 8 q26 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q28 ∷
   rw 10 q29 ∷
   rw 11 q28 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q24 ∷
   rw 11 q30 ∷
   rw 4 q22 ∷
   rw 5 q31 ∷
   rw 6 q25 ∷
   rw 7 q32 ∷
   rw 8 q27 ∷
   rw 9 q32 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q28 ∷
   rw 11 q33 ∷
   rw 12 q28 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q31 ∷
   rw 12 q34 ∷
   rw 5 q35 ∷
   re 5 8 (ℓ "乢") ∷
   re 4 3 (ℓ "也") ∷
   re 6 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 5 q24 ∷
   rw 6 q25 ∷
   rw 7 q26 ∷
   rw 8 q27 ∷
   rw 9 q26 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q28 ∷
   rw 11 q29 ∷
   rw 12 q28 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q24 ∷
   rw 12 q30 ∷
   rw 5 q22 ∷
   rw 6 q31 ∷
   rw 7 q25 ∷
   rw 8 q32 ∷
   rw 9 q27 ∷
   rw 10 q32 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q28 ∷
   rw 12 q33 ∷
   rw 13 q28 ∷
   re 11 3 (ℓ "丽") ∷
   rw 12 q31 ∷
   rw 13 q34 ∷
   rw 6 q35 ∷
   re 6 8 (ℓ "乢") ∷
   re 5 3 (ℓ "也") ∷
   rw 6 q36 ∷
   rw 5 q37 ∷
   rw 6 q22 ∷
   rw 7 q23 ∷
   re 7 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 6 q24 ∷
   rw 7 q25 ∷
   rw 8 q26 ∷
   rw 9 q27 ∷
   rw 10 q26 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q28 ∷
   rw 12 q29 ∷
   rw 13 q28 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q24 ∷
   rw 13 q30 ∷
   rw 6 q22 ∷
   rw 7 q31 ∷
   rw 8 q25 ∷
   rw 9 q32 ∷
   rw 10 q27 ∷
   rw 11 q32 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q28 ∷
   rw 13 q33 ∷
   rw 14 q28 ∷
   re 12 3 (ℓ "丽") ∷
   rw 13 q31 ∷
   rw 14 q34 ∷
   rw 7 q35 ∷
   re 7 8 (ℓ "乢") ∷
   re 6 3 (ℓ "也") ∷
   re 8 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 7 q24 ∷
   rw 8 q25 ∷
   rw 9 q26 ∷
   rw 10 q27 ∷
   rw 11 q26 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q28 ∷
   rw 13 q29 ∷
   rw 14 q28 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q24 ∷
   rw 14 q30 ∷
   rw 7 q22 ∷
   rw 8 q31 ∷
   rw 9 q25 ∷
   rw 10 q32 ∷
   rw 11 q27 ∷
   rw 12 q32 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q28 ∷
   rw 14 q33 ∷
   rw 15 q28 ∷
   re 13 3 (ℓ "丽") ∷
   rw 14 q31 ∷
   rw 15 q34 ∷
   rw 8 q35 ∷
   re 8 8 (ℓ "乢") ∷
   re 7 3 (ℓ "也") ∷
   rw 8 q36 ∷
   rw 7 q38 ∷
   rw⁻ 4 q39 ∷
   rw 3 q40 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q2 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q2 ∷
   rw 3 q5 ∷
   rw 2 q2 ∷
   rw 1 q40 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q2 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q2 ∷
   rw 1 q41 ∷
   rw 0 q2 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q43 : Eqn
  q43 = wE 173 W
  q44 : Eqn
  q44 = wE 2043 W
  q45 : Eqn
  q45 = wE 175 W
  q46 : Eqn
  q46 = sE 1926 lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q47 : Eqn
  q47 = sE 38 lem-pass-X3-CK30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q48 : Eqn
  q48 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q49 : Eqn
  q49 = wE 2044 W

-- pass [X3 CSd30 X3] [K0 TOFF012 CS03 TOFF012 CSd03 Kd0]: 45 steps
lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0 : ⟪ (ℓ "丞丮丞上九中九丮下") ⟫ʷ ≈ ⟪ (ℓ "上九中九丮下丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-K0-TOFF012-CS03-TOFF012-CSd03-Kd0 = derive (ℓ "丞丮丞上九中九丮下") (ℓ "上九中九丮下丞丮丞")
  (rw 4 q1 ∷
   rw 3 q42 ∷
   rw 2 q43 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q2 ∷
   rw 0 q43 ∷
   rw 1 q44 ∷
   rw⁻ 0 q42 ∷
   rw 1 q45 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q45 ∷
   rw 4 q45 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 6 q45 ∷
   rw 7 q45 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q45 ∷
   rw 10 q2 ∷
   rw 7 q46 ∷
   rw 4 q47 ∷
   rw 1 q46 ∷
   rw 15 q1 ∷
   rw 14 q48 ∷
   rw 13 q43 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q2 ∷
   rw 11 q43 ∷
   rw 10 q43 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q2 ∷
   rw 8 q43 ∷
   rw 7 q43 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q2 ∷
   rw 5 q43 ∷
   rw 6 q49 ∷
   rw⁻ 5 q48 ∷
   rw 6 q45 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q45 ∷
   rw 9 q2 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q51 : Eqn
  q51 = wE 2045 W
  q52 : Eqn
  q52 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q53 : Eqn
  q53 = wE 2046 W

-- pass [X3 CK30 X3] [S0 K0 TOFF012 CS03 TOFF012 CSd03 Kd0 Sd0]: 67 steps
lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0 : ⟪ (ℓ "丞乑丞丈上九中九丮下三") ⟫ʷ ≈ ⟪ (ℓ "丈上九中九丮下三丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-S0-K0-TOFF012-CS03-TOFF012-CSd03-Kd0-Sd0 = derive (ℓ "丞乑丞丈上九中九丮下三") (ℓ "丈上九中九丮下三丞乑丞")
  (rw 5 q1 ∷
   rw 4 q42 ∷
   rw 3 q50 ∷
   rw 2 q43 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw 3 q2 ∷
   rw 0 q43 ∷
   rw 1 q51 ∷
   rw⁻ 0 q50 ∷
   rw⁻ 1 q42 ∷
   rw 2 q45 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q45 ∷
   rw 5 q45 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q45 ∷
   rw 8 q45 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q45 ∷
   rw 11 q45 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q45 ∷
   rw 14 q45 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q45 ∷
   rw 17 q2 ∷
   rw 14 q47 ∷
   rw 11 q46 ∷
   rw 8 q46 ∷
   rw 5 q47 ∷
   rw 2 q46 ∷
   rw 23 q1 ∷
   rw 22 q52 ∷
   rw 21 q48 ∷
   rw 20 q43 ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw 21 q2 ∷
   rw 18 q43 ∷
   rw 17 q43 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q2 ∷
   rw 15 q43 ∷
   rw 14 q43 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q2 ∷
   rw 12 q43 ∷
   rw 11 q43 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q2 ∷
   rw 9 q43 ∷
   rw 8 q43 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q2 ∷
   rw 6 q43 ∷
   rw 7 q53 ∷
   rw⁻ 6 q48 ∷
   rw⁻ 7 q52 ∷
   rw 8 q45 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q45 ∷
   rw 11 q2 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 2047 W
  q55 : Eqn
  q55 = wE 2048 W

-- pass [X3 CSd30 X3] [Sd0 Kd0 Sd0 TOFF012 CS03 TOFF012 CSd03 S0 K0 S0]: 53 steps
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0 : ⟪ (ℓ "丞丮丞三下三九中九丮丈上丈") ⟫ʷ ≈ ⟪ (ℓ "三下三九中九丮丈上丈丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-Sd0-Kd0-Sd0-TOFF012-CS03-TOFF012-CSd03-S0-K0-S0 = derive (ℓ "丞丮丞三下三九中九丮丈上丈") (ℓ "三下三九中九丮丈上丈丞丮丞")
  (rw 6 q1 ∷
   rw 5 q52 ∷
   rw 4 q48 ∷
   rw 3 q52 ∷
   rw 2 q43 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q2 ∷
   rw 0 q43 ∷
   rw 1 q54 ∷
   rw⁻ 0 q52 ∷
   rw⁻ 1 q48 ∷
   rw⁻ 2 q52 ∷
   rw 3 q45 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q45 ∷
   rw 6 q45 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q45 ∷
   rw 9 q45 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q45 ∷
   rw 12 q2 ∷
   rw 9 q47 ∷
   rw 6 q46 ∷
   rw 3 q46 ∷
   rw 19 q1 ∷
   rw 18 q50 ∷
   rw 17 q42 ∷
   rw 16 q50 ∷
   rw 15 q43 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q2 ∷
   rw 13 q43 ∷
   rw 12 q43 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q2 ∷
   rw 10 q43 ∷
   rw 9 q43 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q2 ∷
   rw 7 q43 ∷
   rw 8 q55 ∷
   rw⁻ 7 q50 ∷
   rw⁻ 8 q42 ∷
   rw⁻ 9 q50 ∷
   rw 10 q45 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丮") ∷
   rw 12 q45 ∷
   rw 13 q2 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = wE 1357 W
  q57 : Eqn
  q57 = wE 45 W
  q58 : Eqn
  q58 = wE 231 W
  q59 : Eqn
  q59 = sE 1926 lem-pass-X3-CS30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 CS30 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞中丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞中丞中九丮九") (ℓ "中九丮九丞中丞")
  (rw 0 q1 ∷
   rw 1 q56 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q2 ∷
   rw 1 q57 ∷
   rw 2 q1 ∷
   rw 3 q58 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q2 ∷
   rw 3 q57 ∷
   rw⁻ 4 q59 ∷
   rw 12 q1 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q2 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q2 ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   rw 9 q40 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q2 ∷
   rw 9 q41 ∷
   rw 8 q2 ∷
   rw 7 q40 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = sE 1924 lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CS03-TOFF012-CSd03-TOFF012

-- pass [CS03 TOFF012 CSd03 TOFF012] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 1 steps
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "中九丮九丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞中九丮九") ⟫ʷ
lem-pass-CS03-TOFF012-CSd03-TOFF012-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "中九丮九丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞中九丮九")
  (rw⁻ 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = sE 1904 lem-pass-X3-CSd30-X3-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [X3 CSd30 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞丮丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞丮丞习丽习举") (ℓ "习丽习举丞丮丞")
  (rw 3 q15 ∷
   rw 0 q61 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = sE 1902 lem-pass-X3-CKd30-X3-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [X3 CKd30 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞乒丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞乒丞习丽习举") (ℓ "习丽习举丞乒丞")
  (rw 3 q15 ∷
   rw 0 q62 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = sE 1901 lem-pass-X3-CK30-X3-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [X3 CK30 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞乑丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞乑丞习丽习举") (ℓ "习丽习举丞乑丞")
  (rw 3 q15 ∷
   rw 0 q63 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = sE 1903 lem-pass-X3-CS30-X3-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [X3 CS30 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞中丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞中丞习丽习举") (ℓ "习丽习举丞中丞")
  (rw 3 q15 ∷
   rw 0 q64 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = sE 1923 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3
  q66 : Eqn
  q66 = sE 1910 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS12
  q67 : Eqn
  q67 = sE 1911 lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CSd12

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF103 X3 CS12 X3 TOFF103 X3 CSd12]: 4 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 : ⟪ (ℓ "九中九丮丞乡丞丶丞乡丞丷") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞丶丞乡丞丷九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF103-X3-CS12-X3-TOFF103-X3-CSd12 = derive (ℓ "九中九丮丞乡丞丶丞乡丞丷") (ℓ "丞乡丞丶丞乡丞丷九中九丮")
  (rw 0 q65 ∷
   rw 3 q66 ∷
   rw 4 q65 ∷
   rw 7 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = sE 1929 lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF013-CS02-TOFF013-CSd02

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [TOFF012 CS03 TOFF012 CSd03]: 3 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丞中九丮九丞九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丞中九丮九丞九中九丮") (ℓ "九中九丮丞中九丮九丞")
  (rw 6 q6 ∷
   rw 0 q68 ∷
   rw⁻ 0 q8 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = sE 1928 lem-pass-X2-CK20-X2-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X2 CK20 X2] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘乄丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘乄丘中九丮九") (ℓ "中九丮九丘乄丘")
  (rw 0 q1 ∷
   rw 1 q56 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q2 ∷
   rw 1 q57 ∷
   rw 2 q1 ∷
   rw 3 q58 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q2 ∷
   rw 3 q57 ∷
   rw⁻ 4 q69 ∷
   rw 12 q1 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q2 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q2 ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   rw 9 q40 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q2 ∷
   rw 9 q41 ∷
   rw 8 q2 ∷
   rw 7 q40 ∷ []) Eq.refl

-- pass [TOFF012 CS03 TOFF012 CSd03] [S0 CSd03]: 2 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03 : ⟪ (ℓ "九中九丮丈丮") ⟫ʷ ≈ ⟪ (ℓ "丈丮九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-S0-CSd03 = derive (ℓ "九中九丮丈丮") (ℓ "丈丮九中九丮")
  (rw 0 q10 ∷
   rw 1 q11 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = sE 1930 lem-pass-X3-CSd30-X3-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X3 CSd30 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞丮丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞丮丞中九丮九") (ℓ "中九丮九丞丮丞")
  (rw 0 q1 ∷
   rw 1 q56 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q2 ∷
   rw 1 q57 ∷
   rw 2 q1 ∷
   rw 3 q58 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q2 ∷
   rw 3 q57 ∷
   rw⁻ 4 q70 ∷
   rw 12 q1 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q2 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q2 ∷
   rw 11 q5 ∷
   rw 10 q2 ∷
   rw 9 q40 ∷
   rw 10 q1 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q2 ∷
   rw 9 q41 ∷
   rw 8 q2 ∷
   rw 7 q40 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = sE 1908 lem-pass-X3-CS31-X3-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [X3 CS31 X3] [TOFF102 CS13 TOFF102 CSd13]: 3 steps
lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丞丽丞习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丞丽丞习丽习举") (ℓ "习丽习举丞丽丞")
  (rw 3 q15 ∷
   rw 0 q71 ∷
   rw⁻ 0 q17 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = sE 1931 lem-S2-ᵖ-1
  q73 : Eqn
  q73 = sE 1907 lem-pass-X3-CS31-X3-vs-CS02-TOFF013-CSd02-TOFF013
  q74 : Eqn
  q74 = sE 1931 lem-S2-ᵖ-1

-- pass [X3 CS31 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞丽丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞丽丞") ⟫ʷ
lem-pass-X3-CS31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞丽丞中九丮九") (ℓ "中九丮九丞丽丞")
  (rw 3 q72 ∷
   rw 0 q73 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = sE 1905 lem-pass-X3-CK31-X3-vs-CS02-TOFF013-CSd02-TOFF013

-- pass [X3 CK31 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞乔丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞乔丞") ⟫ʷ
lem-pass-X3-CK31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞乔丞中九丮九") (ℓ "中九丮九丞乔丞")
  (rw 3 q72 ∷
   rw 0 q75 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = sE 1906 lem-pass-X3-CKd31-X3-vs-CS02-TOFF013-CSd02-TOFF013

-- pass [X3 CKd31 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞乕丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞乕丞") ⟫ʷ
lem-pass-X3-CKd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞乕丞中九丮九") (ℓ "中九丮九丞乕丞")
  (rw 3 q72 ∷
   rw 0 q76 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = sE 1909 lem-pass-X3-CSd31-X3-vs-CS02-TOFF013-CSd02-TOFF013

-- pass [X3 CSd31 X3] [CS03 TOFF012 CSd03 TOFF012]: 3 steps
lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞举丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞举丞") ⟫ʷ
lem-pass-X3-CSd31-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞举丞中九丮九") (ℓ "中九丮九丞举丞")
  (rw 3 q72 ∷
   rw 0 q77 ∷
   rw⁻ 0 q74 ∷ []) Eq.refl

-- pass [TOFF012 CS03 TOFF012 CSd03] [CS03 X2 TOFF012 X2 CSd03 X2 TOFF012 X2]: 4 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 : ⟪ (ℓ "九中九丮中丘九丘丮丘九丘") ⟫ʷ ≈ ⟪ (ℓ "中丘九丘丮丘九丘九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-CS03-X2-TOFF012-X2-CSd03-X2-TOFF012-X2 = derive (ℓ "九中九丮中丘九丘丮丘九丘") (ℓ "中丘九丘丮丘九丘九中九丮")
  (rw 0 q13 ∷
   rw 1 q9 ∷
   rw 4 q11 ∷
   rw 5 q9 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 871 W
  q79 : Eqn
  q79 = wE 1355 W
  q80 : Eqn
  q80 = wE 389 W
  q81 : Eqn
  q81 = wE 1356 W

-- pass [X2 CKd20 X2] [TOFF012 CS03 TOFF012 CSd03]: 7 steps
lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : ⟪ (ℓ "丘久丘九中九丮") ⟫ʷ ≈ ⟪ (ℓ "九中九丮丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = derive (ℓ "丘久丘九中九丮") (ℓ "九中九丮丘久丘")
  (rw 7 q78 ∷
   rw 8 q79 ∷
   rw 9 q78 ∷
   rw⁻ 3 q69 ∷
   rw 2 q80 ∷
   rw 1 q81 ∷
   rw 0 q80 ∷ []) Eq.refl
