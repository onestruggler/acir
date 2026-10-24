{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD662 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D662 (W : Ws) (Sᴰ : SD662) where

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
  lem-pass-CCZ123-vs-CS23 : St 1735
  lem-pass-CCZ123-vs-CS23 = pickᴰ 0 Sᴰ
  lem-pass-CCZ123-vs-CSd23 : St 1736
  lem-pass-CCZ123-vs-CSd23 = pickᴰ 1 Sᴰ
  lem-pass-CZ12-vs-CS23 : St 1738
  lem-pass-CZ12-vs-CS23 = pickᴰ 2 Sᴰ
  lem-pass-CZ12-vs-CSd23 : St 1739
  lem-pass-CZ12-vs-CSd23 = pickᴰ 3 Sᴰ
  lem-pass-CZ01-vs-CS23 : St 1755
  lem-pass-CZ01-vs-CS23 = pickᴰ 4 Sᴰ
  lem-pass-CCZ013-vs-CS23 : St 903
  lem-pass-CCZ013-vs-CS23 = pickᴰ 5 Sᴰ
  lem-pass-CCZ013-vs-CCZ123 : St 906
  lem-pass-CCZ013-vs-CCZ123 = pickᴰ 6 Sᴰ
  lem-pass-CCZ013-vs-TOFF201 : St 1741
  lem-pass-CCZ013-vs-TOFF201 = pickᴰ 7 Sᴰ

private
  q1 : Eqn
  q1 = wE 1521 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = wE 127 W
  q4 : Eqn
  q4 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 8 W
  q7 : Eqn
  q7 = wE 9 W
  q8 : Eqn
  q8 = wE 10 W
  q9 : Eqn
  q9 = wE 333 W
  q10 : Eqn
  q10 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 253 W
  q12 : Eqn
  q12 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q13 : Eqn
  q13 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q14 : Eqn
  q14 = wE 24 W
  q15 : Eqn
  q15 = wE 25 W
  q16 : Eqn
  q16 = wE 26 W
  q17 : Eqn
  q17 = wE 12 W
  q18 : Eqn
  q18 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q19 : Eqn
  q19 = wE 398 W
  q20 : Eqn
  q20 = wE 14 W
  q21 : Eqn
  q21 = wE 15 W
  q22 : Eqn
  q22 = wE 16 W
  q23 : Eqn
  q23 = wE 366 W
  q24 : Eqn
  q24 = wE 30 W
  q25 : Eqn
  q25 = wE 27 W
  q26 : Eqn
  q26 = wE 31 W
  q27 : Eqn
  q27 = wE 22 W
  q28 : Eqn
  q28 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q29 : Eqn
  q29 = wE 23 W
  q30 : Eqn
  q30 = wE 47 W
  q31 : Eqn
  q31 = wE 48 W
  q32 : Eqn
  q32 = wE 1 W
  q33 : Eqn
  q33 = wE 3 W
  q34 : Eqn
  q34 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q35 : Eqn
  q35 = wE 43 W
  q36 : Eqn
  q36 = wE 271 W
  q37 : Eqn
  q37 = wE 272 W
  q38 : Eqn
  q38 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q39 : Eqn
  q39 = wE 11 W
  q40 : Eqn
  q40 = eqn (ℓ "九乚九") (ℓ "乚乜") (ax toff-ccz)
  q41 : Eqn
  q41 = wE 28 W
  q42 : Eqn
  q42 = wE 29 W
  q43 : Eqn
  q43 = wE 20 W
  q44 : Eqn
  q44 = wE 21 W
  q45 : Eqn
  q45 = wE 49 W
  q46 : Eqn
  q46 = wE 51 W
  q47 : Eqn
  q47 = wE 1991 W
  q48 : Eqn
  q48 = sE 906 lem-pass-CCZ013-vs-CCZ123
  q49 : Eqn
  q49 = sE 1735 lem-pass-CCZ123-vs-CS23
  q50 : Eqn
  q50 = sE 903 lem-pass-CCZ013-vs-CS23
  q51 : Eqn
  q51 = sE 1738 lem-pass-CZ12-vs-CS23
  q52 : Eqn
  q52 = sE 1755 lem-pass-CZ01-vs-CS23
  q53 : Eqn
  q53 = sE 1741 lem-pass-CCZ013-vs-TOFF201
  q54 : Eqn
  q54 = wE 1992 W
  q55 : Eqn
  q55 = wE 1877 W
  q56 : Eqn
  q56 = wE 32 W
  q57 : Eqn
  q57 = sE 1736 lem-pass-CCZ123-vs-CSd23
  q58 : Eqn
  q58 = sE 1739 lem-pass-CZ12-vs-CSd23

-- pass [CZ12 CCZ123] [TOFF201 CS23 TOFF201 CSd23]: 806 steps
lem-pass-CZ12-CCZ123-vs-TOFF201-CS23-TOFF201-CSd23 : ⟪ (ℓ "丸乜乣义乣乊") ⟫ʷ ≈ ⟪ (ℓ "乣义乣乊丸乜") ⟫ʷ
lem-pass-CZ12-CCZ123-vs-TOFF201-CS23-TOFF201-CSd23 = derive (ℓ "丸乜乣义乣乊") (ℓ "乣义乣乊丸乜")
  (rw 1 q1 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 11 q3 ∷
   rw⁻ 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw⁻ 4 q4 ∷
   rw 5 q9 ∷
   re 5 8 (ℓ "乣") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw⁻ 9 q10 ∷
   rw 8 q8 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (ℓ "中") ∷
   rw 6 q11 ∷
   rw⁻ 5 q12 ∷
   rw 4 q11 ∷
   rw⁻ 3 q13 ∷
   rw 4 q2 ∷
   rw 5 q13 ∷
   rw 6 q14 ∷
   rw 7 q12 ∷
   rw 8 q14 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q10 ∷
   rw 10 q15 ∷
   rw 11 q10 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q16 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   re 2 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 9 q3 ∷
   rw⁻ 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw⁻ 2 q4 ∷
   rw 3 q9 ∷
   re 3 8 (ℓ "乣") ∷
   rw 6 q17 ∷
   re 5 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 12 q18 ∷
   rw 11 q19 ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 12 q20 ∷
   rw 9 q17 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q21 ∷
   rw 7 q17 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q22 ∷
   rw 5 q19 ∷
   rw 6 q23 ∷
   re 6 8 (ℓ "习") ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q13 ∷
   rw 5 q24 ∷
   rw 6 q12 ∷
   rw 7 q24 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q10 ∷
   rw 9 q25 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q26 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q27 ∷
   rw 10 q28 ∷
   rw 8 q29 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "丼丣丼") ∷
   rw 9 q20 ∷
   rw 6 q30 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 7 q20 ∷
   rw 4 q31 ∷
   rw 5 q32 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q33 ∷
   rw⁻ 7 q34 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q33 ∷
   rw⁻ 9 q34 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q33 ∷
   rw 6 q35 ∷
   re 6 5 (ℓ "乙") ∷
   re 5 3 (ℓ "乚") ∷
   re 3 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 10 q18 ∷
   rw 9 q19 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q20 ∷
   rw 7 q17 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q21 ∷
   rw 5 q17 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q22 ∷
   rw 3 q19 ∷
   rw 4 q23 ∷
   re 4 8 (ℓ "习") ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 13 q3 ∷
   rw 12 q36 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q8 ∷
   rw 6 q36 ∷
   rw 7 q37 ∷
   re 7 8 (ℓ "九") ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q32 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q34 ∷
   rw 9 q32 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q34 ∷
   rw 11 q32 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q33 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q10 ∷
   rw 10 q5 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q6 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw⁻ 9 q10 ∷
   rw 8 q7 ∷
   rw⁻ 7 q10 ∷
   re 8 3 (ℓ "丮") ∷
   rw 6 q6 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw⁻ 7 q10 ∷
   rw 6 q8 ∷
   rw⁻ 5 q10 ∷
   re 6 3 (ℓ "中") ∷
   rw 6 q32 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q33 ∷
   rw⁻ 8 q38 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 9 q33 ∷
   rw⁻ 10 q38 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q33 ∷
   rw 7 q39 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 11 q3 ∷
   rw 10 q36 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 4 q36 ∷
   rw 5 q37 ∷
   re 5 8 (ℓ "九") ∷
   rw 5 q40 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q32 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q34 ∷
   rw 9 q32 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q34 ∷
   rw 11 q32 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q33 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q10 ∷
   rw 5 q25 ∷
   rw 6 q10 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q41 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q10 ∷
   rw 7 q42 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "丮") ∷
   rw 7 q41 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q10 ∷
   rw 9 q15 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q32 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q33 ∷
   rw⁻ 6 q38 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 7 q33 ∷
   rw⁻ 8 q38 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q33 ∷
   rw 5 q39 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q13 ∷
   rw 6 q24 ∷
   rw 7 q12 ∷
   rw 8 q24 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q10 ∷
   rw 10 q25 ∷
   rw 11 q10 ∷
   re 9 3 (ℓ "中") ∷
   rw 5 q2 ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q12 ∷
   rw 9 q14 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q10 ∷
   rw 11 q15 ∷
   rw 12 q10 ∷
   re 10 3 (ℓ "丽") ∷
   rw 6 q16 ∷
   re 6 5 (ℓ "乜") ∷
   re 5 3 (ℓ "乛") ∷
   rw 6 q26 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q32 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q34 ∷
   rw 8 q32 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q34 ∷
   rw 10 q32 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q33 ∷
   rw 3 q43 ∷
   rw 6 q17 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q44 ∷
   rw 8 q17 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q27 ∷
   rw⁻ 9 q28 ∷
   rw 10 q29 ∷
   re 7 5 (ℓ "中") ∷
   rw 3 q2 ∷
   rw 4 q13 ∷
   rw 5 q14 ∷
   rw 6 q12 ∷
   rw 7 q14 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q10 ∷
   rw 9 q15 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q16 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q13 ∷
   rw 6 q24 ∷
   rw 7 q12 ∷
   rw 8 q24 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q10 ∷
   rw 10 q25 ∷
   rw 11 q10 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q26 ∷
   rw 4 q45 ∷
   re 6 1 (ℓ "丼丣丼") ∷
   rw 5 q20 ∷
   rw 6 q46 ∷
   re 8 1 (ℓ "丼丣丼") ∷
   rw 7 q20 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q27 ∷
   rw⁻ 10 q28 ∷
   rw 11 q29 ∷
   re 8 5 (ℓ "中") ∷
   rw 4 q32 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q33 ∷
   rw⁻ 6 q34 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q33 ∷
   rw⁻ 8 q34 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q33 ∷
   rw 5 q35 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 5 q20 ∷
   re 3 1 (ℓ "並乜並") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q13 ∷
   rw 4 q24 ∷
   rw 5 q12 ∷
   rw 6 q24 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q10 ∷
   rw 8 q25 ∷
   rw 9 q10 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q26 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw 4 q12 ∷
   rw 5 q14 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q10 ∷
   rw 7 q15 ∷
   rw 8 q10 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q16 ∷
   re 2 5 (ℓ "乜") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q32 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q34 ∷
   rw 8 q32 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q34 ∷
   rw 10 q32 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q33 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q10 ∷
   rw 4 q25 ∷
   rw 5 q10 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q41 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q10 ∷
   rw 6 q42 ∷
   rw 7 q10 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q41 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q10 ∷
   rw 8 q15 ∷
   rw 9 q10 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q32 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q33 ∷
   rw⁻ 5 q38 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 6 q33 ∷
   rw⁻ 7 q38 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q33 ∷
   rw 4 q39 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 4 q26 ∷
   rw 0 q47 ∷
   rw⁻ 3 q48 ∷
   rw 4 q49 ∷
   rw 3 q50 ∷
   rw 2 q51 ∷
   rw 1 q52 ∷
   rw 5 q1 ∷
   rw 9 q2 ∷
   re 8 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 15 q3 ∷
   rw⁻ 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q8 ∷
   rw⁻ 8 q4 ∷
   rw 9 q9 ∷
   re 9 8 (ℓ "乣") ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw⁻ 13 q10 ∷
   rw 12 q8 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (ℓ "中") ∷
   rw 10 q11 ∷
   rw⁻ 9 q12 ∷
   rw 8 q11 ∷
   rw⁻ 7 q13 ∷
   rw 8 q2 ∷
   rw 9 q13 ∷
   rw 10 q14 ∷
   rw 11 q12 ∷
   rw 12 q14 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q10 ∷
   rw 14 q15 ∷
   rw 15 q10 ∷
   re 13 3 (ℓ "丽") ∷
   rw 9 q16 ∷
   re 9 5 (ℓ "乜") ∷
   re 8 3 (ℓ "乛") ∷
   re 6 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 13 q3 ∷
   rw⁻ 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q8 ∷
   rw⁻ 6 q4 ∷
   rw 7 q9 ∷
   re 7 8 (ℓ "乣") ∷
   rw 10 q17 ∷
   re 9 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 16 q18 ∷
   rw 15 q19 ∷
   re 14 1 (ℓ "丼丠丼") ∷
   rw 16 q20 ∷
   rw 13 q17 ∷
   re 14 3 (ℓ "个") ∷
   rw 12 q21 ∷
   rw 11 q17 ∷
   re 12 3 (ℓ "个") ∷
   rw 10 q22 ∷
   rw 9 q19 ∷
   rw 10 q23 ∷
   re 10 8 (ℓ "习") ∷
   re 8 1 (ℓ "並乜並") ∷
   re 9 1 (ℓ "义丹乊丹丽") ∷
   rw 8 q13 ∷
   rw 9 q24 ∷
   rw 10 q12 ∷
   rw 11 q24 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q10 ∷
   rw 13 q25 ∷
   rw 14 q10 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q26 ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q27 ∷
   rw 14 q28 ∷
   rw 12 q29 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "丼丣丼") ∷
   rw 13 q20 ∷
   rw 10 q30 ∷
   re 9 1 (ℓ "丼丣丼") ∷
   rw 11 q20 ∷
   rw 8 q31 ∷
   rw 9 q32 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q33 ∷
   rw⁻ 11 q34 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q33 ∷
   rw⁻ 13 q34 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q33 ∷
   rw 10 q35 ∷
   re 10 5 (ℓ "乙") ∷
   re 9 3 (ℓ "乚") ∷
   re 7 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   re 12 1 (ℓ "丼丠丼") ∷
   rw 14 q20 ∷
   rw 11 q17 ∷
   re 12 3 (ℓ "个") ∷
   rw 10 q21 ∷
   rw 9 q17 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q22 ∷
   rw 7 q19 ∷
   rw 8 q23 ∷
   re 8 8 (ℓ "习") ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 17 q3 ∷
   rw 16 q36 ∷
   rw 15 q5 ∷
   rw 14 q6 ∷
   rw 13 q7 ∷
   rw 12 q6 ∷
   rw 11 q8 ∷
   rw 10 q36 ∷
   rw 11 q37 ∷
   re 11 8 (ℓ "九") ∷
   re 9 1 (ℓ "乏乙乏") ∷
   re 10 1 (ℓ "丶丣丷丣丧") ∷
   rw 11 q32 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q34 ∷
   rw 13 q32 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q34 ∷
   rw 15 q32 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q33 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q10 ∷
   rw 14 q5 ∷
   rw⁻ 13 q10 ∷
   re 14 3 (ℓ "丽") ∷
   rw 12 q6 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw⁻ 13 q10 ∷
   rw 12 q7 ∷
   rw⁻ 11 q10 ∷
   re 12 3 (ℓ "丮") ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw⁻ 11 q10 ∷
   rw 10 q8 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (ℓ "中") ∷
   rw 10 q32 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q33 ∷
   rw⁻ 12 q38 ∷
   re 14 1 (ℓ "乏丨乏") ∷
   rw 13 q33 ∷
   rw⁻ 14 q38 ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q33 ∷
   rw 11 q39 ∷
   re 11 5 (ℓ "乙") ∷
   re 10 3 (ℓ "乚") ∷
   re 8 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 15 q3 ∷
   rw 14 q36 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q8 ∷
   rw 8 q36 ∷
   rw 9 q37 ∷
   re 9 8 (ℓ "九") ∷
   rw 9 q40 ∷
   re 9 1 (ℓ "乏乙乏") ∷
   re 10 1 (ℓ "丶丣丷丣丧") ∷
   rw 11 q32 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q34 ∷
   rw 13 q32 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q34 ∷
   rw 15 q32 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q33 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q10 ∷
   rw 9 q25 ∷
   rw 10 q10 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q41 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q10 ∷
   rw 11 q42 ∷
   rw 12 q10 ∷
   re 10 3 (ℓ "丮") ∷
   rw 11 q41 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q10 ∷
   rw 13 q15 ∷
   rw 14 q10 ∷
   re 12 3 (ℓ "丽") ∷
   rw 8 q32 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q33 ∷
   rw⁻ 10 q38 ∷
   re 12 1 (ℓ "乏丨乏") ∷
   rw 11 q33 ∷
   rw⁻ 12 q38 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q33 ∷
   rw 9 q39 ∷
   re 9 5 (ℓ "乙") ∷
   re 8 3 (ℓ "乚") ∷
   re 10 1 (ℓ "义丹乊丹丽") ∷
   rw 9 q13 ∷
   rw 10 q24 ∷
   rw 11 q12 ∷
   rw 12 q24 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q10 ∷
   rw 14 q25 ∷
   rw 15 q10 ∷
   re 13 3 (ℓ "中") ∷
   rw 9 q2 ∷
   rw 10 q13 ∷
   rw 11 q14 ∷
   rw 12 q12 ∷
   rw 13 q14 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q10 ∷
   rw 15 q15 ∷
   rw 16 q10 ∷
   re 14 3 (ℓ "丽") ∷
   rw 10 q16 ∷
   re 10 5 (ℓ "乜") ∷
   re 9 3 (ℓ "乛") ∷
   rw 10 q26 ∷
   re 8 1 (ℓ "乏乙乏") ∷
   re 9 1 (ℓ "丶丣丷丣丧") ∷
   rw 10 q32 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q34 ∷
   rw 12 q32 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q34 ∷
   rw 14 q32 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q33 ∷
   rw 7 q43 ∷
   rw 10 q17 ∷
   re 8 3 (ℓ "个") ∷
   rw 9 q44 ∷
   rw 12 q17 ∷
   re 10 3 (ℓ "个") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q27 ∷
   rw⁻ 13 q28 ∷
   rw 14 q29 ∷
   re 11 5 (ℓ "中") ∷
   rw 7 q2 ∷
   rw 8 q13 ∷
   rw 9 q14 ∷
   rw 10 q12 ∷
   rw 11 q14 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q10 ∷
   rw 13 q15 ∷
   rw 14 q10 ∷
   re 12 3 (ℓ "丽") ∷
   rw 8 q16 ∷
   re 8 5 (ℓ "乜") ∷
   re 7 3 (ℓ "乛") ∷
   re 9 1 (ℓ "並乜並") ∷
   re 10 1 (ℓ "义丹乊丹丽") ∷
   rw 9 q13 ∷
   rw 10 q24 ∷
   rw 11 q12 ∷
   rw 12 q24 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q10 ∷
   rw 14 q25 ∷
   rw 15 q10 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q26 ∷
   rw 8 q45 ∷
   re 10 1 (ℓ "丼丣丼") ∷
   rw 9 q20 ∷
   rw 10 q46 ∷
   re 12 1 (ℓ "丼丣丼") ∷
   rw 11 q20 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 12 q27 ∷
   rw⁻ 14 q28 ∷
   rw 15 q29 ∷
   re 12 5 (ℓ "中") ∷
   rw 8 q32 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q33 ∷
   rw⁻ 10 q34 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q33 ∷
   rw⁻ 12 q34 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q33 ∷
   rw 9 q35 ∷
   re 9 5 (ℓ "乙") ∷
   re 8 3 (ℓ "乚") ∷
   rw 9 q20 ∷
   re 7 1 (ℓ "並乜並") ∷
   re 8 1 (ℓ "义丹乊丹丽") ∷
   rw 7 q13 ∷
   rw 8 q24 ∷
   rw 9 q12 ∷
   rw 10 q24 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q10 ∷
   rw 12 q25 ∷
   rw 13 q10 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q26 ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q12 ∷
   rw 9 q14 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q10 ∷
   rw 11 q15 ∷
   rw 12 q10 ∷
   re 10 3 (ℓ "丽") ∷
   rw 6 q16 ∷
   re 6 5 (ℓ "乜") ∷
   re 8 1 (ℓ "乏乙乏") ∷
   re 9 1 (ℓ "丶丣丷丣丧") ∷
   rw 10 q32 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 9 q34 ∷
   rw 12 q32 ∷
   re 10 3 (ℓ "举") ∷
   rw⁻ 11 q34 ∷
   rw 14 q32 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q33 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q10 ∷
   rw 8 q25 ∷
   rw 9 q10 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q41 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q10 ∷
   rw 10 q42 ∷
   rw 11 q10 ∷
   re 9 3 (ℓ "丮") ∷
   rw 10 q41 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q10 ∷
   rw 12 q15 ∷
   rw 13 q10 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q32 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q33 ∷
   rw⁻ 9 q38 ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw 10 q33 ∷
   rw⁻ 11 q38 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q33 ∷
   rw 8 q39 ∷
   re 8 5 (ℓ "乙") ∷
   re 7 3 (ℓ "乚") ∷
   rw 8 q26 ∷
   rw 4 q53 ∷
   rw 3 q47 ∷
   rw 2 q54 ∷
   rw⁻ 7 q48 ∷
   rw 3 q55 ∷
   rw 6 q32 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q32 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q34 ∷
   rw 9 q32 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q34 ∷
   rw 11 q32 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q33 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q33 ∷
   rw 8 q34 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q33 ∷
   rw 6 q34 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q33 ∷
   rw 6 q35 ∷
   re 6 5 (ℓ "乙") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q32 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q34 ∷
   rw 8 q32 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q34 ∷
   rw 10 q32 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q33 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q33 ∷
   rw 7 q34 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q33 ∷
   rw 5 q34 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q33 ∷
   rw 5 q35 ∷
   re 5 5 (ℓ "乙") ∷
   rw 5 q56 ∷
   rw 4 q33 ∷
   rw 4 q57 ∷
   rw 3 q58 ∷ []) Eq.refl
