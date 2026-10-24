{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD661 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D661 (W : Ws) (Sᴰ : SD661) where

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
  lem-pass-CZ12-vs-CS13 : St 1335
  lem-pass-CZ12-vs-CS13 = pickᴰ 2 Sᴰ
  lem-pass-CZ12-vs-CSd13 : St 1336
  lem-pass-CZ12-vs-CSd13 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 : St 1730
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3 : St 1731
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3 : St 1732
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3 = pickᴰ 6 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3 : St 1733
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3 = pickᴰ 7 Sᴰ
  lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 : St 636
  lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 8 Sᴰ
  lem-pass-CZ02-vs-CS13 : St 1753
  lem-pass-CZ02-vs-CS13 = pickᴰ 9 Sᴰ
  lem-pass-CCZ123-vs-CCZ023 : St 922
  lem-pass-CCZ123-vs-CCZ023 = pickᴰ 10 Sᴰ
  lem-pass-CCZ023-vs-CS13 : St 908
  lem-pass-CCZ023-vs-CS13 = pickᴰ 11 Sᴰ
  lem-pass-CCZ023-vs-TOFF102 : St 1633
  lem-pass-CCZ023-vs-TOFF102 = pickᴰ 12 Sᴰ
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2 : St 1678
  lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2 = pickᴰ 13 Sᴰ
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 : St 1685
  lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2 = pickᴰ 14 Sᴰ
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123 : St 1754
  lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123 = pickᴰ 15 Sᴰ

private
  q1 : Eqn
  q1 = wE 1377 W
  q2 : Eqn
  q2 = wE 5 W
  q3 : Eqn
  q3 = wE 127 W
  q4 : Eqn
  q4 = wE 271 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = wE 8 W
  q7 : Eqn
  q7 = wE 9 W
  q8 : Eqn
  q8 = wE 10 W
  q9 : Eqn
  q9 = wE 272 W
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
  q19 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q20 : Eqn
  q20 = wE 14 W
  q21 : Eqn
  q21 = wE 15 W
  q22 : Eqn
  q22 = wE 16 W
  q23 : Eqn
  q23 = wE 46 W
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
  q36 = eqn (ℓ "九乚九") (ℓ "乚乜") (ax toff-ccz)
  q37 : Eqn
  q37 = wE 20 W
  q38 : Eqn
  q38 = wE 21 W
  q39 : Eqn
  q39 = wE 49 W
  q40 : Eqn
  q40 = wE 50 W
  q41 : Eqn
  q41 = wE 51 W
  q42 : Eqn
  q42 = wE 52 W
  q43 : Eqn
  q43 = wE 1806 W
  q44 : Eqn
  q44 = sE 922 lem-pass-CCZ123-vs-CCZ023
  q45 : Eqn
  q45 = sE 1333 lem-pass-CCZ123-vs-CS13
  q46 : Eqn
  q46 = sE 908 lem-pass-CCZ023-vs-CS13
  q47 : Eqn
  q47 = sE 1335 lem-pass-CZ12-vs-CS13
  q48 : Eqn
  q48 = sE 1753 lem-pass-CZ02-vs-CS13
  q49 : Eqn
  q49 = sE 1633 lem-pass-CCZ023-vs-TOFF102
  q50 : Eqn
  q50 = wE 1984 W
  q51 : Eqn
  q51 = wE 1808 W
  q52 : Eqn
  q52 = wE 74 W
  q53 : Eqn
  q53 = wE 33 W
  q54 : Eqn
  q54 = sE 1334 lem-pass-CCZ123-vs-CSd13
  q55 : Eqn
  q55 = sE 1336 lem-pass-CZ12-vs-CSd13

-- pass [CZ12 CCZ123] [TOFF102 CS13 TOFF102 CSd13]: 468 steps
lem-pass-CZ12-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丸乜习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举丸乜") ⟫ʷ
lem-pass-CZ12-CCZ123-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丸乜习丽习举") (ℓ "习丽习举丸乜")
  (rw 1 q1 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   rw 7 q7 ∷
   rw 6 q6 ∷
   rw 5 q8 ∷
   rw 4 q4 ∷
   rw 5 q9 ∷
   re 5 8 (ℓ "九") ∷
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
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q3 ∷
   rw 8 q4 ∷
   rw 7 q5 ∷
   rw 6 q6 ∷
   rw 5 q7 ∷
   rw 4 q6 ∷
   rw 3 q8 ∷
   rw 2 q4 ∷
   rw 3 q9 ∷
   re 3 8 (ℓ "九") ∷
   rw 6 q17 ∷
   re 5 1 (ℓ "上丶丣丷丣丧上一") ∷
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
   re 6 8 (ℓ "九") ∷
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
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
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
   re 4 8 (ℓ "九") ∷
   rw 4 q36 ∷
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
   rw 3 q37 ∷
   rw 6 q17 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q38 ∷
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
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q39 ∷
   rw 5 q40 ∷
   rw 6 q41 ∷
   rw 7 q40 ∷
   rw 8 q37 ∷
   rw 4 q42 ∷
   re 4 5 (ℓ "乜") ∷
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
   rw 4 q26 ∷
   rw 0 q43 ∷
   rw 3 q44 ∷
   rw 4 q45 ∷
   rw 3 q46 ∷
   rw 2 q47 ∷
   rw 1 q48 ∷
   rw 5 q1 ∷
   rw 9 q2 ∷
   re 8 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q6 ∷
   rw 11 q7 ∷
   rw 10 q6 ∷
   rw 9 q8 ∷
   rw 8 q4 ∷
   rw 9 q9 ∷
   re 9 8 (ℓ "九") ∷
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
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q7 ∷
   rw 8 q6 ∷
   rw 7 q8 ∷
   rw 6 q4 ∷
   rw 7 q9 ∷
   re 7 8 (ℓ "九") ∷
   rw 10 q17 ∷
   re 9 1 (ℓ "上丶丣丷丣丧上一") ∷
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
   re 10 8 (ℓ "九") ∷
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
   re 7 1 (ℓ "上丶丣丷丣丧上一") ∷
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
   re 8 8 (ℓ "九") ∷
   rw 8 q36 ∷
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
   rw 7 q37 ∷
   rw 10 q17 ∷
   re 8 3 (ℓ "个") ∷
   rw 9 q38 ∷
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
   re 9 1 (ℓ "义丹乊丹丽") ∷
   rw 8 q39 ∷
   rw 9 q40 ∷
   rw 10 q41 ∷
   rw 11 q40 ∷
   rw 12 q37 ∷
   rw 8 q42 ∷
   re 8 5 (ℓ "乜") ∷
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
   rw 8 q26 ∷
   rw 4 q49 ∷
   rw 3 q43 ∷
   rw 2 q50 ∷
   rw 7 q44 ∷
   rw 3 q51 ∷
   rw 6 q2 ∷
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
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q10 ∷
   rw 10 q5 ∷
   rw⁻ 9 q10 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q52 ∷
   rw⁻ 7 q12 ∷
   rw 6 q52 ∷
   rw⁻ 5 q13 ∷
   rw 6 q16 ∷
   re 6 5 (ℓ "乜") ∷
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
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q10 ∷
   rw 9 q5 ∷
   rw⁻ 8 q10 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q52 ∷
   rw⁻ 6 q12 ∷
   rw 5 q52 ∷
   rw⁻ 4 q13 ∷
   rw 5 q16 ∷
   re 5 5 (ℓ "乜") ∷
   rw 5 q53 ∷
   rw 4 q26 ∷
   rw 4 q54 ∷
   rw 3 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = wE 1018 W
  q57 : Eqn
  q57 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q58 : Eqn
  q58 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q59 : Eqn
  q59 = wE 390 W
  q60 : Eqn
  q60 = wE 257 W
  q61 : Eqn
  q61 = wE 389 W
  q62 : Eqn
  q62 = wE 258 W
  q63 : Eqn
  q63 = sE 1678 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-TOFF102-X2
  q64 : Eqn
  q64 = sE 1730 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CS13-X3
  q65 : Eqn
  q65 = sE 1731 lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X3-CSd13-X3
  q66 : Eqn
  q66 = sE 636 lem-distribute-Gad⟨t≡1-W≡⟨2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 20 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 32 q56 ∷
   rw 37 q56 ∷
   rw 42 q56 ∷
   rw⁻ 30 q57 ∷
   rw⁻ 31 q58 ∷
   rw 32 q59 ∷
   rw 32 q58 ∷
   rw 33 q60 ∷
   rw 34 q61 ∷
   rw⁻ 36 q57 ∷
   rw⁻ 37 q58 ∷
   rw 38 q59 ∷
   rw 38 q58 ∷
   rw 39 q62 ∷
   rw 40 q61 ∷
   rw 0 q63 ∷
   rw 3 q64 ∷
   rw 6 q63 ∷
   rw 9 q65 ∷
   rw⁻ 0 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 1985 W
  q68 : Eqn
  q68 = wE 1986 W
  q69 : Eqn
  q69 = wE 1987 W
  q70 : Eqn
  q70 = sE 1754 lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-Z1-CZ12-CZ13-CCZ123
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

-- pass [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3] [CCZ123]: 15 steps
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CCZ123 : ⟪ (ℓ "丘丞习丽习举丘丞乜") ⟫ʷ ≈ ⟪ (ℓ "乜丘丞习丽习举丘丞") ⟫ʷ
lem-pass-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3-vs-CCZ123 = derive (ℓ "丘丞习丽习举丘丞乜") (ℓ "乜丘丞习丽习举丘丞")
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
  q77 = sE 1685 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-TOFF102-X2
  q78 : Eqn
  q78 = sE 1732 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CS13-X3
  q79 : Eqn
  q79 = sE 1733 lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X3-CSd13-X3

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X2 X3 TOFF102 CS13 TOFF102 CSd13 X2 X3]: 20 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丞习丽习举丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞习丽习举丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X2-X3-TOFF102-CS13-TOFF102-CSd13-X2-X3 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丘丞习丽习举丘丞") (ℓ "丘丞习丽习举丘丞丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 34 q56 ∷
   rw 39 q56 ∷
   rw 44 q56 ∷
   rw⁻ 32 q57 ∷
   rw⁻ 33 q58 ∷
   rw 34 q59 ∷
   rw 34 q58 ∷
   rw 35 q60 ∷
   rw 36 q61 ∷
   rw⁻ 38 q57 ∷
   rw⁻ 39 q58 ∷
   rw 40 q59 ∷
   rw 40 q58 ∷
   rw 41 q62 ∷
   rw 42 q61 ∷
   rw 0 q77 ∷
   rw 3 q78 ∷
   rw 6 q77 ∷
   rw 9 q79 ∷
   rw⁻ 0 q66 ∷ []) Eq.refl
