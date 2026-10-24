{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD658 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D658 (W : Ws) (Sᴰ : SD658) where

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
  lem-pass-CCZ123-vs-CS13 : St 1333
  lem-pass-CCZ123-vs-CS13 = pickᴰ 0 Sᴰ
  lem-pass-CCZ123-vs-CSd13 : St 1334
  lem-pass-CCZ123-vs-CSd13 = pickᴰ 1 Sᴰ
  lem-pass-CZ02-vs-CSd13 : St 1729
  lem-pass-CZ02-vs-CSd13 = pickᴰ 2 Sᴰ
  lem-pass-CZ12-vs-CS13 : St 1335
  lem-pass-CZ12-vs-CS13 = pickᴰ 3 Sᴰ
  lem-pass-CZ12-vs-CSd13 : St 1336
  lem-pass-CZ12-vs-CSd13 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 : St 1730
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3 : St 1731
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3 = pickᴰ 6 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 : St 600
  lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102 = pickᴰ 7 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3 : St 1732
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3 = pickᴰ 8 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3 : St 1733
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3 = pickᴰ 9 Sᴰ
  lem-pass-CCZ023-vs-CSd13 : St 1612
  lem-pass-CCZ023-vs-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-CCZ123-vs-CCZ023 : St 922
  lem-pass-CCZ123-vs-CCZ023 = pickᴰ 11 Sᴰ
  lem-pass-CCZ023-vs-TOFF102 : St 1633
  lem-pass-CCZ023-vs-TOFF102 = pickᴰ 12 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2 : St 1678
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2 = pickᴰ 13 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 : St 1685
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 = pickᴰ 14 Sᴰ
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123 : St 1734
  lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123 = pickᴰ 15 Sᴰ

private
  q1 : Eqn
  q1 = sE 1333 lem-pass-CCZ123-vs-CS13
  q2 : Eqn
  q2 = sE 1335 lem-pass-CZ12-vs-CS13
  q3 : Eqn
  q3 = wE 1377 W
  q4 : Eqn
  q4 = wE 5 W
  q5 : Eqn
  q5 = wE 127 W
  q6 : Eqn
  q6 = wE 271 W
  q7 : Eqn
  q7 = wE 7 W
  q8 : Eqn
  q8 = wE 8 W
  q9 : Eqn
  q9 = wE 9 W
  q10 : Eqn
  q10 = wE 10 W
  q11 : Eqn
  q11 = wE 272 W
  q12 : Eqn
  q12 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 253 W
  q14 : Eqn
  q14 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q16 : Eqn
  q16 = wE 24 W
  q17 : Eqn
  q17 = wE 25 W
  q18 : Eqn
  q18 = wE 26 W
  q19 : Eqn
  q19 = wE 12 W
  q20 : Eqn
  q20 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q21 : Eqn
  q21 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q22 : Eqn
  q22 = wE 14 W
  q23 : Eqn
  q23 = wE 15 W
  q24 : Eqn
  q24 = wE 16 W
  q25 : Eqn
  q25 = wE 46 W
  q26 : Eqn
  q26 = wE 30 W
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = wE 31 W
  q29 : Eqn
  q29 = wE 22 W
  q30 : Eqn
  q30 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q31 : Eqn
  q31 = wE 23 W
  q32 : Eqn
  q32 = wE 47 W
  q33 : Eqn
  q33 = wE 48 W
  q34 : Eqn
  q34 = wE 1 W
  q35 : Eqn
  q35 = wE 3 W
  q36 : Eqn
  q36 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q37 : Eqn
  q37 = wE 43 W
  q38 : Eqn
  q38 = eqn (ℓ "九乚九") (ℓ "乚乜") (ax toff-ccz)
  q39 : Eqn
  q39 = wE 20 W
  q40 : Eqn
  q40 = wE 21 W
  q41 : Eqn
  q41 = wE 49 W
  q42 : Eqn
  q42 = wE 50 W
  q43 : Eqn
  q43 = wE 51 W
  q44 : Eqn
  q44 = wE 52 W
  q45 : Eqn
  q45 = wE 1806 W
  q46 : Eqn
  q46 = sE 922 lem-pass-CCZ123-vs-CCZ023
  q47 : Eqn
  q47 = sE 1334 lem-pass-CCZ123-vs-CSd13
  q48 : Eqn
  q48 = sE 1612 lem-pass-CCZ023-vs-CSd13
  q49 : Eqn
  q49 = sE 1336 lem-pass-CZ12-vs-CSd13
  q50 : Eqn
  q50 = sE 1729 lem-pass-CZ02-vs-CSd13
  q51 : Eqn
  q51 = sE 1633 lem-pass-CCZ023-vs-TOFF102
  q52 : Eqn
  q52 = wE 1984 W
  q53 : Eqn
  q53 = wE 1808 W
  q54 : Eqn
  q54 = wE 74 W
  q55 : Eqn
  q55 = wE 33 W

-- pass [CZ12 CCZ123] [CS13 TOFF102 CSd13 TOFF102]: 468 steps
lem-pass-CZ12-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 : ⟪ (ℓ "丸乜丽习举习") ⟫ʷ ≈ ⟪ (ℓ "丽习举习丸乜") ⟫ʷ
lem-pass-CZ12-CCZ123-vs-CS13-TOFF102-CSd13-TOFF102 = derive (ℓ "丸乜丽习举习") (ℓ "丽习举习丸乜")
  (rw 1 q1 ∷
   rw 0 q2 ∷
   rw 2 q3 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 12 q5 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q9 ∷
   rw 7 q8 ∷
   rw 6 q10 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   re 6 8 (ℓ "九") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw⁻ 10 q12 ∷
   rw 9 q10 ∷
   rw⁻ 8 q12 ∷
   re 9 3 (ℓ "中") ∷
   rw 7 q13 ∷
   rw⁻ 6 q14 ∷
   rw 5 q13 ∷
   rw⁻ 4 q15 ∷
   rw 5 q4 ∷
   rw 6 q15 ∷
   rw 7 q16 ∷
   rw 8 q14 ∷
   rw 9 q16 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q12 ∷
   rw 11 q17 ∷
   rw 12 q12 ∷
   re 10 3 (ℓ "丽") ∷
   rw 6 q18 ∷
   re 6 5 (ℓ "乜") ∷
   re 5 3 (ℓ "乛") ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   rw 8 q7 ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw 5 q8 ∷
   rw 4 q10 ∷
   rw 3 q6 ∷
   rw 4 q11 ∷
   re 4 8 (ℓ "九") ∷
   rw 7 q19 ∷
   re 6 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 13 q20 ∷
   rw 12 q21 ∷
   re 11 1 (ℓ "丼丠丼") ∷
   rw 13 q22 ∷
   rw 10 q19 ∷
   re 11 3 (ℓ "个") ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   re 9 3 (ℓ "个") ∷
   rw 7 q24 ∷
   rw 6 q21 ∷
   rw 7 q25 ∷
   re 7 8 (ℓ "九") ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q28 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 12 q29 ∷
   rw 11 q30 ∷
   rw 9 q31 ∷
   re 10 5 (ℓ "中") ∷
   re 8 1 (ℓ "丼丣丼") ∷
   rw 10 q22 ∷
   rw 7 q32 ∷
   re 6 1 (ℓ "丼丣丼") ∷
   rw 8 q22 ∷
   rw 5 q33 ∷
   rw 6 q34 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q35 ∷
   rw⁻ 8 q36 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q35 ∷
   rw⁻ 10 q36 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q35 ∷
   rw 7 q37 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   re 9 1 (ℓ "丼丠丼") ∷
   rw 11 q22 ∷
   rw 8 q19 ∷
   re 9 3 (ℓ "个") ∷
   rw 7 q23 ∷
   rw 6 q19 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q24 ∷
   rw 4 q21 ∷
   rw 5 q25 ∷
   re 5 8 (ℓ "九") ∷
   rw 5 q38 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q34 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q36 ∷
   rw 9 q34 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q36 ∷
   rw 11 q34 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q35 ∷
   rw 4 q39 ∷
   rw 7 q19 ∷
   re 5 3 (ℓ "个") ∷
   rw 6 q40 ∷
   rw 9 q19 ∷
   re 7 3 (ℓ "个") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q29 ∷
   rw⁻ 10 q30 ∷
   rw 11 q31 ∷
   re 8 5 (ℓ "中") ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q18 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q41 ∷
   rw 6 q42 ∷
   rw 7 q43 ∷
   rw 8 q42 ∷
   rw 9 q39 ∷
   rw 5 q44 ∷
   re 5 5 (ℓ "乜") ∷
   rw 6 q22 ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q28 ∷
   rw 3 q15 ∷
   rw 4 q16 ∷
   rw 5 q14 ∷
   rw 6 q16 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q12 ∷
   rw 8 q17 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q18 ∷
   re 3 5 (ℓ "乜") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q15 ∷
   rw 5 q26 ∷
   rw 6 q14 ∷
   rw 7 q26 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q12 ∷
   rw 9 q27 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q4 ∷
   rw 5 q15 ∷
   rw 6 q16 ∷
   rw 7 q14 ∷
   rw 8 q16 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q12 ∷
   rw 10 q17 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q18 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   rw 5 q28 ∷
   rw 1 q45 ∷
   rw 4 q46 ∷
   rw 5 q47 ∷
   rw 4 q48 ∷
   rw 3 q49 ∷
   rw 2 q50 ∷
   rw 6 q3 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q7 ∷
   rw 13 q8 ∷
   rw 12 q9 ∷
   rw 11 q8 ∷
   rw 10 q10 ∷
   rw 9 q6 ∷
   rw 10 q11 ∷
   re 10 8 (ℓ "九") ∷
   re 8 1 (ℓ "义丹乊丹丽") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw⁻ 14 q12 ∷
   rw 13 q10 ∷
   rw⁻ 12 q12 ∷
   re 13 3 (ℓ "中") ∷
   rw 11 q13 ∷
   rw⁻ 10 q14 ∷
   rw 9 q13 ∷
   rw⁻ 8 q15 ∷
   rw 9 q4 ∷
   rw 10 q15 ∷
   rw 11 q16 ∷
   rw 12 q14 ∷
   rw 13 q16 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 14 q12 ∷
   rw 15 q17 ∷
   rw 16 q12 ∷
   re 14 3 (ℓ "丽") ∷
   rw 10 q18 ∷
   re 10 5 (ℓ "乜") ∷
   re 9 3 (ℓ "乛") ∷
   re 7 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q8 ∷
   rw 10 q9 ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw 7 q6 ∷
   rw 8 q11 ∷
   re 8 8 (ℓ "九") ∷
   rw 11 q19 ∷
   re 10 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 17 q20 ∷
   rw 16 q21 ∷
   re 15 1 (ℓ "丼丠丼") ∷
   rw 17 q22 ∷
   rw 14 q19 ∷
   re 15 3 (ℓ "个") ∷
   rw 13 q23 ∷
   rw 12 q19 ∷
   re 13 3 (ℓ "个") ∷
   rw 11 q24 ∷
   rw 10 q21 ∷
   rw 11 q25 ∷
   re 11 8 (ℓ "九") ∷
   re 9 1 (ℓ "並乜並") ∷
   re 10 1 (ℓ "义丹乊丹丽") ∷
   rw 9 q15 ∷
   rw 10 q26 ∷
   rw 11 q14 ∷
   rw 12 q26 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q12 ∷
   rw 14 q27 ∷
   rw 15 q12 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q28 ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q29 ∷
   rw 15 q30 ∷
   rw 13 q31 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "丼丣丼") ∷
   rw 14 q22 ∷
   rw 11 q32 ∷
   re 10 1 (ℓ "丼丣丼") ∷
   rw 12 q22 ∷
   rw 9 q33 ∷
   rw 10 q34 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q35 ∷
   rw⁻ 12 q36 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q35 ∷
   rw⁻ 14 q36 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 15 q35 ∷
   rw 11 q37 ∷
   re 11 5 (ℓ "乙") ∷
   re 10 3 (ℓ "乚") ∷
   re 8 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 15 q20 ∷
   rw 14 q21 ∷
   re 13 1 (ℓ "丼丠丼") ∷
   rw 15 q22 ∷
   rw 12 q19 ∷
   re 13 3 (ℓ "个") ∷
   rw 11 q23 ∷
   rw 10 q19 ∷
   re 11 3 (ℓ "个") ∷
   rw 9 q24 ∷
   rw 8 q21 ∷
   rw 9 q25 ∷
   re 9 8 (ℓ "九") ∷
   rw 9 q38 ∷
   re 9 1 (ℓ "乏乙乏") ∷
   re 10 1 (ℓ "丶丣丷丣丧") ∷
   rw 11 q34 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q36 ∷
   rw 13 q34 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q36 ∷
   rw 15 q34 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q35 ∷
   rw 8 q39 ∷
   rw 11 q19 ∷
   re 9 3 (ℓ "个") ∷
   rw 10 q40 ∷
   rw 13 q19 ∷
   re 11 3 (ℓ "个") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 12 q29 ∷
   rw⁻ 14 q30 ∷
   rw 15 q31 ∷
   re 12 5 (ℓ "中") ∷
   rw 8 q4 ∷
   rw 9 q15 ∷
   rw 10 q16 ∷
   rw 11 q14 ∷
   rw 12 q16 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q12 ∷
   rw 14 q17 ∷
   rw 15 q12 ∷
   re 13 3 (ℓ "丽") ∷
   rw 9 q18 ∷
   re 9 5 (ℓ "乜") ∷
   re 8 3 (ℓ "乛") ∷
   re 10 1 (ℓ "义丹乊丹丽") ∷
   rw 9 q41 ∷
   rw 10 q42 ∷
   rw 11 q43 ∷
   rw 12 q42 ∷
   rw 13 q39 ∷
   rw 9 q44 ∷
   re 9 5 (ℓ "乜") ∷
   rw 10 q22 ∷
   re 8 1 (ℓ "並乜並") ∷
   re 9 1 (ℓ "义丹乊丹丽") ∷
   rw 8 q15 ∷
   rw 9 q26 ∷
   rw 10 q14 ∷
   rw 11 q26 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q12 ∷
   rw 13 q27 ∷
   rw 14 q12 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q28 ∷
   rw 7 q15 ∷
   rw 8 q16 ∷
   rw 9 q14 ∷
   rw 10 q16 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q12 ∷
   rw 12 q17 ∷
   rw 13 q12 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q18 ∷
   re 7 5 (ℓ "乜") ∷
   re 9 1 (ℓ "义丹乊丹丽") ∷
   rw 8 q15 ∷
   rw 9 q26 ∷
   rw 10 q14 ∷
   rw 11 q26 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q12 ∷
   rw 13 q27 ∷
   rw 14 q12 ∷
   re 12 3 (ℓ "中") ∷
   rw 8 q4 ∷
   rw 9 q15 ∷
   rw 10 q16 ∷
   rw 11 q14 ∷
   rw 12 q16 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q12 ∷
   rw 14 q17 ∷
   rw 15 q12 ∷
   re 13 3 (ℓ "丽") ∷
   rw 9 q18 ∷
   re 9 5 (ℓ "乜") ∷
   re 8 3 (ℓ "乛") ∷
   rw 9 q28 ∷
   rw 5 q51 ∷
   rw 4 q45 ∷
   rw 3 q52 ∷
   rw 8 q46 ∷
   rw 4 q53 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "並乜並") ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   rw 6 q15 ∷
   rw 7 q26 ∷
   rw 8 q14 ∷
   rw 9 q26 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q12 ∷
   rw 11 q27 ∷
   rw 12 q12 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q28 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q12 ∷
   rw 11 q7 ∷
   rw⁻ 10 q12 ∷
   re 11 3 (ℓ "丽") ∷
   rw 9 q54 ∷
   rw⁻ 8 q14 ∷
   rw 7 q54 ∷
   rw⁻ 6 q15 ∷
   rw 7 q18 ∷
   re 7 5 (ℓ "乜") ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q15 ∷
   rw 6 q26 ∷
   rw 7 q14 ∷
   rw 8 q26 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q12 ∷
   rw 10 q27 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q28 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q12 ∷
   rw 10 q7 ∷
   rw⁻ 9 q12 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q54 ∷
   rw⁻ 7 q14 ∷
   rw 6 q54 ∷
   rw⁻ 5 q15 ∷
   rw 6 q18 ∷
   re 6 5 (ℓ "乜") ∷
   rw 6 q55 ∷
   rw 5 q28 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = wE 1018 W
  q57 : Eqn
  q57 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q58 : Eqn
  q58 = wE 257 W
  q59 : Eqn
  q59 = wE 389 W
  q60 : Eqn
  q60 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q61 : Eqn
  q61 = wE 390 W
  q62 : Eqn
  q62 = wE 258 W
  q63 : Eqn
  q63 = sE 1730 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3
  q64 : Eqn
  q64 = sE 1678 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2
  q65 : Eqn
  q65 = sE 1731 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3
  q66 : Eqn
  q66 = sE 600 lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡-1⟩-CS13-TOFF102-CSd13-TOFF102

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 20 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞丽习举习丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丽习举习丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞丽习举习丘丞") (ℓ "丘丞丽习举习丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 32 q56 ∷
   rw 37 q56 ∷
   rw 42 q56 ∷
   rw 29 q57 ∷
   rw 30 q58 ∷
   rw 31 q59 ∷
   rw⁻ 33 q60 ∷
   rw⁻ 34 q57 ∷
   rw 35 q61 ∷
   rw 35 q57 ∷
   rw 36 q62 ∷
   rw 37 q59 ∷
   rw⁻ 39 q60 ∷
   rw⁻ 40 q57 ∷
   rw 41 q61 ∷
   rw 0 q63 ∷
   rw 3 q64 ∷
   rw 6 q65 ∷
   rw 9 q64 ∷
   rw⁻ 0 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 1985 W
  q68 : Eqn
  q68 = wE 1986 W
  q69 : Eqn
  q69 = wE 1987 W
  q70 : Eqn
  q70 = sE 1734 lem-pass-CS13-TOFF102-CSd13-TOFF102-vs-Z1-CZ12-CZ13-CCZ123
  q71 : Eqn
  q71 = eqn (ℓ "专丞") (ℓ "丞专") (low-comm ((Z ↑)) ((X ↑)))
  q72 : Eqn
  q72 = eqn (ℓ "丸丞") (ℓ "丞丸") (low₃-comm ((CZ ↑)) (X))
  q73 : Eqn
  q73 = wE 1988 W
  q74 : Eqn
  q74 = eqn (ℓ "专丘") (ℓ "丘专") (low-comm ((Z ↑)) (X))
  q75 : Eqn
  q75 = wE 1989 W
  q76 : Eqn
  q76 = wE 1990 W

-- pass [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3] [CCZ123]: 15 steps
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123 : ⟪ (ℓ "丘丞丽习举习丘丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丘丞丽习举习丘丞") ⟫ʷ
lem-pass-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3-vs-CCZ123 = derive (ℓ "丘丞丽习举习丘丞乜") (ℓ "乜丘丞丽习举习丘丞")
  (rw 7 q67 ∷
   rw 6 q68 ∷
   rw 8 q69 ∷
   rw 2 q70 ∷
   rw⁻ 1 q71 ∷
   rw⁻ 2 q72 ∷
   rw 3 q73 ∷
   rw 5 q67 ∷
   rw⁻ 0 q74 ∷
   rw 1 q68 ∷
   rw⁻ 3 q74 ∷
   rw 4 q75 ∷
   rw 5 q68 ∷
   rw 7 q69 ∷
   rw 0 q76 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = sE 1732 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3
  q78 : Eqn
  q78 = sE 1685 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2
  q79 : Eqn
  q79 = sE 1733 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 X3 CS13 TOFF102 CSd13 TOFF102 X2 X3]: 20 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丞丽习举习丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丽习举习丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-CS13-TOFF102-CSd13-TOFF102-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丞丽习举习丘丞") (ℓ "丘丞丽习举习丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 34 q56 ∷
   rw 39 q56 ∷
   rw 44 q56 ∷
   rw 31 q57 ∷
   rw 32 q58 ∷
   rw 33 q59 ∷
   rw⁻ 35 q60 ∷
   rw⁻ 36 q57 ∷
   rw 37 q61 ∷
   rw 37 q57 ∷
   rw 38 q62 ∷
   rw 39 q59 ∷
   rw⁻ 41 q60 ∷
   rw⁻ 42 q57 ∷
   rw 43 q61 ∷
   rw 0 q77 ∷
   rw 3 q78 ∷
   rw 6 q79 ∷
   rw 9 q78 ∷
   rw⁻ 0 q66 ∷ []) Eq.refl
