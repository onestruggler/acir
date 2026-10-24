{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD621 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D621 (W : Ws) (Sᴰ : SD621) where

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
  lem-N23-D : St 1411
  lem-N23-D = pickᴰ 0 Sᴰ
  lem-comm-CCZ123-CCZ023 : St 8
  lem-comm-CCZ123-CCZ023 = pickᴰ 1 Sᴰ
  lem-comm-CCZ123-CCZ012 : St 1412
  lem-comm-CCZ123-CCZ012 = pickᴰ 2 Sᴰ
  lem-comm-CCZ012-CZ13 : St 573
  lem-comm-CCZ012-CZ13 = pickᴰ 3 Sᴰ
  lem-comm-CCZ013-CCZ012 : St 13
  lem-comm-CCZ013-CCZ012 = pickᴰ 4 Sᴰ
  lem-comm-CCZ013-CS12 : St 15
  lem-comm-CCZ013-CS12 = pickᴰ 5 Sᴰ
  lem-comm-CCZ123-CCZ013 : St 1413
  lem-comm-CCZ123-CCZ013 = pickᴰ 6 Sᴰ
  lem-CCZ123-passes-CKd10 : St 1414
  lem-CCZ123-passes-CKd10 = pickᴰ 7 Sᴰ
  lem-comm-CZ01-CCZ023 : St 1415
  lem-comm-CZ01-CCZ023 = pickᴰ 8 Sᴰ
  lem-comm-CZ01-CCZ123 : St 1416
  lem-comm-CZ01-CCZ123 = pickᴰ 9 Sᴰ
  lem-CCZ012-passes-PP3 : St 1417
  lem-CCZ012-passes-PP3 = pickᴰ 10 Sᴰ
  lem-CS12-passes-PP3 : St 1418
  lem-CS12-passes-PP3 = pickᴰ 11 Sᴰ
  lem-CS13-passes-PP3 : St 1419
  lem-CS13-passes-PP3 = pickᴰ 12 Sᴰ
  lem-CZ13-passes-PP3 : St 1420
  lem-CZ13-passes-PP3 = pickᴰ 13 Sᴰ
  lem-N23-PP3 : St 1421
  lem-N23-PP3 = pickᴰ 14 Sᴰ
  lem-CCZ013-passes-PP3 : St 1422
  lem-CCZ013-passes-PP3 = pickᴰ 15 Sᴰ
  lem-N32-PP3 : St 1423
  lem-N32-PP3 = pickᴰ 16 Sᴰ
  lem-CCZ123-passes-PP3 : St 1424
  lem-CCZ123-passes-PP3 = pickᴰ 17 Sᴰ
  lem-ROT≡cF : St 1425
  lem-ROT≡cF = pickᴰ 18 Sᴰ

private
  q1 : Eqn
  q1 = wE 1863 W
  q2 : Eqn
  q2 = sE 1421 lem-N23-PP3
  q3 : Eqn
  q3 = wE 105 W
  q4 : Eqn
  q4 = sE 1423 lem-N32-PP3
  q5 : Eqn
  q5 = wE 1864 W
  q6 : Eqn
  q6 = eqn (ℓ "乖乙乖") (ℓ "乙乚") (ax cx-ccz)
  q7 : Eqn
  q7 = wE 1865 W
  q8 : Eqn
  q8 = sE 1418 lem-CS12-passes-PP3
  q9 : Eqn
  q9 = sE 1419 lem-CS13-passes-PP3
  q10 : Eqn
  q10 = sE 1424 lem-CCZ123-passes-PP3
  q11 : Eqn
  q11 = sE 1417 lem-CCZ012-passes-PP3
  q12 : Eqn
  q12 = sE 1422 lem-CCZ013-passes-PP3
  q13 : Eqn
  q13 = sE 1420 lem-CZ13-passes-PP3
  q14 : Eqn
  q14 = wE 1187 W
  q15 : Eqn
  q15 = wE 259 W
  q16 : Eqn
  q16 = sE 1412 lem-comm-CCZ123-CCZ012
  q17 : Eqn
  q17 = sE 1413 lem-comm-CCZ123-CCZ013
  q18 : Eqn
  q18 = wE 1866 W
  q19 : Eqn
  q19 = sE 15 lem-comm-CCZ013-CS12
  q20 : Eqn
  q20 = wE 1 W
  q21 : Eqn
  q21 = wE 3 W
  q22 : Eqn
  q22 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q23 : Eqn
  q23 = wE 43 W
  q24 : Eqn
  q24 = wE 177 W
  q25 : Eqn
  q25 = wE 101 W
  q26 : Eqn
  q26 = sE 13 lem-comm-CCZ013-CCZ012
  q27 : Eqn
  q27 = wE 178 W
  q28 : Eqn
  q28 = sE 573 lem-comm-CCZ012-CZ13
  q29 : Eqn
  q29 = wE 1867 W
  q30 : Eqn
  q30 = wE 106 W
  q31 : Eqn
  q31 = wE 1868 W
  q32 : Eqn
  q32 = wE 32 W
  q33 : Eqn
  q33 = wE 33 W
  q34 : Eqn
  q34 = wE 1436 W
  q35 : Eqn
  q35 = sE 1424 lem-CCZ123-passes-PP3
  q36 : Eqn
  q36 = sE 1417 lem-CCZ012-passes-PP3
  q37 : Eqn
  q37 = sE 1418 lem-CS12-passes-PP3
  q38 : Eqn
  q38 = wE 42 W
  q39 : Eqn
  q39 = wE 1869 W
  q40 : Eqn
  q40 = sE 1411 lem-N23-D
  q41 : Eqn
  q41 = wE 1870 W
  q42 : Eqn
  q42 = wE 1871 W
  q43 : Eqn
  q43 = wE 1872 W
  q44 : Eqn
  q44 = wE 1873 W
  q45 : Eqn
  q45 = wE 1453 W

-- S3: 252 steps
lem-S3 : ⟪ (ℓ "乏九中九丮乏") ⟫ʷ ≈ ⟪ (ℓ "九中九丮") ⟫ʷ
lem-S3 = derive (ℓ "乏九中九丮乏") (ℓ "九中九丮")
  (rw 0 q1 ∷
   rw 7 q1 ∷
   rw 2 q2 ∷
   rw 6 q3 ∷
   rw 1 q4 ∷
   rw 11 q3 ∷
   rw 10 q3 ∷
   rw 8 q5 ∷
   rw 11 q6 ∷
   rw 13 q7 ∷
   rw⁻ 4 q8 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 6 q10 ∷
   rw⁻ 7 q11 ∷
   rw⁻ 8 q12 ∷
   rw⁻ 9 q10 ∷
   rw⁻ 10 q13 ∷
   rw 3 q14 ∷
   rw 4 q15 ∷
   rw 6 q16 ∷
   rw 7 q17 ∷
   rw 9 q18 ∷
   rw 2 q19 ∷
   rw 5 q20 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q21 ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q21 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q21 ∷
   rw 4 q22 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q21 ∷
   rw 4 q23 ∷
   re 4 5 (ℓ "乙") ∷
   rw 4 q24 ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "丽") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q20 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q22 ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q20 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q21 ∷
   rw 5 q23 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 5 q21 ∷
   rw 5 q16 ∷
   rw 6 q17 ∷
   rw 8 q18 ∷
   rw 1 q25 ∷
   rw 4 q26 ∷
   rw 7 q18 ∷
   rw 8 q20 ∷
   re 7 1 (ℓ "乏丸乏") ∷
   rw 9 q21 ∷
   re 6 1 (ℓ "乏乙乏") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q22 ∷
   rw 12 q20 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q21 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q21 ∷
   rw 9 q22 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q21 ∷
   rw 7 q23 ∷
   re 7 5 (ℓ "乙") ∷
   rw 7 q27 ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "丿") ∷
   re 8 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q22 ∷
   rw 13 q20 ∷
   re 11 3 (ℓ "中") ∷
   rw 7 q20 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q21 ∷
   rw⁻ 9 q22 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q21 ∷
   rw⁻ 11 q22 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 12 q21 ∷
   rw 8 q23 ∷
   re 8 5 (ℓ "乙") ∷
   re 7 3 (ℓ "乚") ∷
   rw 8 q21 ∷
   rw 7 q20 ∷
   re 6 1 (ℓ "乏丸乏") ∷
   rw 8 q21 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q21 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q21 ∷
   rw 8 q22 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q21 ∷
   rw 6 q23 ∷
   re 6 5 (ℓ "乙") ∷
   rw 6 q27 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "丿") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q22 ∷
   rw 12 q20 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q20 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q21 ∷
   rw⁻ 10 q22 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q21 ∷
   rw 7 q23 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   rw 7 q21 ∷
   rw 4 q28 ∷
   rw 3 q29 ∷
   rw 2 q29 ∷
   rw 1 q30 ∷
   rw 3 q31 ∷
   rw 7 q20 ∷
   re 6 1 (ℓ "乏乙乏") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q22 ∷
   rw 12 q20 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q21 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q21 ∷
   rw 9 q22 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q21 ∷
   rw 7 q23 ∷
   re 7 5 (ℓ "乙") ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q21 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q21 ∷
   rw 8 q22 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q21 ∷
   rw 6 q23 ∷
   re 6 5 (ℓ "乙") ∷
   rw 6 q32 ∷
   rw 5 q21 ∷
   rw 5 q33 ∷
   rw 2 q30 ∷
   rw 1 q34 ∷
   rw 3 q35 ∷
   rw 2 q36 ∷
   rw 1 q37 ∷
   rw 5 q38 ∷
   rw 0 q2 ∷
   rw 10 q38 ∷
   rw 9 q38 ∷
   rw 7 q39 ∷
   rw 8 q40 ∷
   rw 9 q41 ∷
   rw 6 q14 ∷
   rw 7 q16 ∷
   rw 9 q42 ∷
   rw 5 q24 ∷
   rw 8 q42 ∷
   rw 7 q27 ∷
   rw 6 q27 ∷
   rw 5 q43 ∷
   rw 4 q43 ∷
   rw 5 q44 ∷
   rw 6 q32 ∷
   rw 6 q33 ∷
   rw 4 q45 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = sE 1425 lem-ROT≡cF
  q47 : Eqn
  q47 = wE 873 W
  q48 : Eqn
  q48 = wE 1874 W
  q49 : Eqn
  q49 = wE 5 W
  q50 : Eqn
  q50 = wE 1106 W
  q51 : Eqn
  q51 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q52 : Eqn
  q52 = wE 30 W
  q53 : Eqn
  q53 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q54 : Eqn
  q54 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q55 : Eqn
  q55 = wE 27 W
  q56 : Eqn
  q56 = wE 31 W
  q57 : Eqn
  q57 = wE 7 W
  q58 : Eqn
  q58 = wE 74 W
  q59 : Eqn
  q59 = wE 26 W
  q60 : Eqn
  q60 = wE 1875 W
  q61 : Eqn
  q61 = wE 24 W
  q62 : Eqn
  q62 = wE 25 W
  q63 : Eqn
  q63 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q64 : Eqn
  q64 = wE 1876 W
  q65 : Eqn
  q65 = eqn (ℓ "丳之") (ℓ "之丳") (low-comm (CX₁₀) (CZ))
  q66 : Eqn
  q66 = wE 12 W
  q67 : Eqn
  q67 = wE 22 W
  q68 : Eqn
  q68 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q69 : Eqn
  q69 = wE 23 W
  q70 : Eqn
  q70 = wE 14 W
  q71 : Eqn
  q71 = wE 47 W
  q72 : Eqn
  q72 = wE 48 W
  q73 : Eqn
  q73 = wE 6 W
  q74 : Eqn
  q74 = wE 8 W
  q75 : Eqn
  q75 = wE 9 W
  q76 : Eqn
  q76 = wE 10 W
  q77 : Eqn
  q77 = wE 11 W
  q78 : Eqn
  q78 = wE 13 W
  q79 : Eqn
  q79 = wE 15 W
  q80 : Eqn
  q80 = wE 16 W
  q81 : Eqn
  q81 = wE 17 W
  q82 : Eqn
  q82 = wE 18 W
  q83 : Eqn
  q83 = wE 19 W
  q84 : Eqn
  q84 = wE 20 W
  q85 : Eqn
  q85 = wE 21 W
  q86 : Eqn
  q86 = wE 28 W
  q87 : Eqn
  q87 = wE 29 W
  q88 : Eqn
  q88 = wE 71 W
  q89 : Eqn
  q89 = wE 72 W
  q90 : Eqn
  q90 = wE 73 W
  q91 : Eqn
  q91 = wE 49 W
  q92 : Eqn
  q92 = wE 50 W
  q93 : Eqn
  q93 = wE 51 W
  q94 : Eqn
  q94 = wE 52 W
  q95 : Eqn
  q95 = sE 1415 lem-comm-CZ01-CCZ023
  q96 : Eqn
  q96 = sE 1416 lem-comm-CZ01-CCZ123
  q97 : Eqn
  q97 = eqn (ℓ "丢之") (ℓ "之丢") (low-comm (CZ) (CZ))
  q98 : Eqn
  q98 = wE 1877 W
  q99 : Eqn
  q99 = eqn (ℓ "丵之") (ℓ "之丵") (low-comm ((S ↑ • CK₁₀)) (CZ))
  q100 : Eqn
  q100 = sE 1414 lem-CCZ123-passes-CKd10
  q101 : Eqn
  q101 = wE 1878 W
  q102 : Eqn
  q102 = sE 8 lem-comm-CCZ123-CCZ023
  q103 : Eqn
  q103 = wE 1879 W
  q104 : Eqn
  q104 = sE 1425 lem-ROT≡cF

-- X0-ROT: 427 steps
lem-X0-ROT : ⟪ (ℓ "丌临乙习丿习乙丿与临乙习丿习乙丿丌") ⟫ʷ ≈ ⟪ (ℓ "临乙习丿习乙丿与临乙习丿习乙丿乜") ⟫ʷ
lem-X0-ROT = derive (ℓ "丌临乙习丿习乙丿与临乙习丿习乙丿丌") (ℓ "临乙习丿习乙丿与临乙习丿习乙丿乜")
  (rw 1 q46 ∷
   rw 4 q47 ∷
   rw 3 q47 ∷
   rw 2 q47 ∷
   rw 0 q48 ∷
   rw 6 q49 ∷
   rw 5 q50 ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q51 ∷
   rw 5 q52 ∷
   rw 6 q53 ∷
   rw 7 q52 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q54 ∷
   rw 9 q55 ∷
   rw 10 q54 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q56 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q54 ∷
   rw 9 q57 ∷
   rw⁻ 8 q54 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q58 ∷
   rw⁻ 6 q53 ∷
   rw 5 q58 ∷
   rw⁻ 4 q51 ∷
   rw 5 q59 ∷
   re 5 5 (ℓ "乜") ∷
   rw 3 q50 ∷
   rw 4 q60 ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q51 ∷
   rw 4 q52 ∷
   rw 5 q53 ∷
   rw 6 q52 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q54 ∷
   rw 8 q55 ∷
   rw 9 q54 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q49 ∷
   rw 4 q51 ∷
   rw 5 q61 ∷
   rw 6 q53 ∷
   rw 7 q61 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q54 ∷
   rw 9 q62 ∷
   rw 10 q54 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q59 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   rw 4 q63 ∷
   rw 5 q56 ∷
   rw 5 q64 ∷
   rw 11 q49 ∷
   rw 10 q50 ∷
   re 9 1 (ℓ "並乜並") ∷
   re 10 1 (ℓ "义丹乊丹丽") ∷
   rw 9 q51 ∷
   rw 10 q52 ∷
   rw 11 q53 ∷
   rw 12 q52 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q54 ∷
   rw 14 q55 ∷
   rw 15 q54 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q56 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q54 ∷
   rw 14 q57 ∷
   rw⁻ 13 q54 ∷
   re 14 3 (ℓ "丽") ∷
   rw 12 q58 ∷
   rw⁻ 11 q53 ∷
   rw 10 q58 ∷
   rw⁻ 9 q51 ∷
   rw 10 q59 ∷
   re 10 5 (ℓ "乜") ∷
   rw 8 q50 ∷
   rw 9 q60 ∷
   re 9 1 (ℓ "义丹乊丹丽") ∷
   rw 8 q51 ∷
   rw 9 q52 ∷
   rw 10 q53 ∷
   rw 11 q52 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q54 ∷
   rw 13 q55 ∷
   rw 14 q54 ∷
   re 12 3 (ℓ "中") ∷
   rw 8 q49 ∷
   rw 9 q51 ∷
   rw 10 q61 ∷
   rw 11 q53 ∷
   rw 12 q61 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 13 q54 ∷
   rw 14 q62 ∷
   rw 15 q54 ∷
   re 13 3 (ℓ "丽") ∷
   rw 9 q59 ∷
   re 9 5 (ℓ "乜") ∷
   re 8 3 (ℓ "乛") ∷
   rw 9 q63 ∷
   rw 10 q56 ∷
   rw⁻ 4 q65 ∷
   rw 5 q66 ∷
   rw 4 q66 ∷
   re 5 3 (ℓ "乃") ∷
   re 3 1 (ℓ "並乜並") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q51 ∷
   rw 4 q52 ∷
   rw 5 q53 ∷
   rw 6 q52 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q54 ∷
   rw 8 q55 ∷
   rw 9 q54 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q56 ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q67 ∷
   rw 9 q68 ∷
   rw 7 q69 ∷
   re 8 5 (ℓ "中") ∷
   re 6 1 (ℓ "丼丣丼") ∷
   rw 8 q70 ∷
   rw 5 q71 ∷
   re 4 1 (ℓ "丼丣丼") ∷
   rw 6 q70 ∷
   rw 3 q72 ∷
   rw 4 q20 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q21 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q21 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q21 ∷
   rw 5 q23 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 2 q66 ∷
   re 3 3 (ℓ "乃") ∷
   rw 6 q20 ∷
   rw 5 q20 ∷
   re 6 3 (ℓ "乐") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q20 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q22 ∷
   rw 8 q20 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q22 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q21 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q21 ∷
   rw 7 q22 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q21 ∷
   rw 5 q22 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q21 ∷
   rw 5 q23 ∷
   re 5 5 (ℓ "乙") ∷
   rw 3 q20 ∷
   re 4 3 (ℓ "乐") ∷
   rw 7 q49 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q54 ∷
   rw 7 q73 ∷
   rw⁻ 6 q54 ∷
   re 7 3 (ℓ "乓") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q57 ∷
   rw 8 q74 ∷
   rw 7 q75 ∷
   rw 6 q74 ∷
   rw 5 q76 ∷
   rw 6 q77 ∷
   re 6 5 (ℓ "乙") ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q54 ∷
   rw 5 q73 ∷
   rw⁻ 4 q54 ∷
   re 5 3 (ℓ "乓") ∷
   rw 8 q66 ∷
   rw 7 q78 ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 12 q70 ∷
   rw 9 q66 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q79 ∷
   rw 7 q66 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q80 ∷
   rw 7 q81 ∷
   re 7 5 (ℓ "乙") ∷
   rw 5 q78 ∷
   rw 6 q6 ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q82 ∷
   rw 8 q66 ∷
   re 6 3 (ℓ "个") ∷
   rw 7 q83 ∷
   rw 10 q66 ∷
   re 8 3 (ℓ "个") ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 9 q70 ∷
   rw 5 q81 ∷
   re 5 5 (ℓ "乙") ∷
   re 7 1 (ℓ "乏乙乏") ∷
   re 8 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q22 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q22 ∷
   rw 13 q20 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q21 ∷
   rw 6 q84 ∷
   rw 9 q66 ∷
   re 7 3 (ℓ "个") ∷
   rw 8 q85 ∷
   rw 11 q66 ∷
   re 9 3 (ℓ "个") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q67 ∷
   rw⁻ 12 q68 ∷
   rw 13 q69 ∷
   re 10 5 (ℓ "中") ∷
   rw 6 q49 ∷
   rw 7 q51 ∷
   rw 8 q61 ∷
   rw 9 q53 ∷
   rw 10 q61 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q54 ∷
   rw 12 q62 ∷
   rw 13 q54 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q59 ∷
   re 7 5 (ℓ "乜") ∷
   re 6 3 (ℓ "乛") ∷
   rw 7 q70 ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q55 ∷
   rw 5 q86 ∷
   rw 6 q87 ∷
   rw 7 q86 ∷
   rw 8 q62 ∷
   rw 4 q77 ∷
   re 4 5 (ℓ "乙") ∷
   re 6 1 (ℓ "並乜並") ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   rw 6 q51 ∷
   rw 7 q52 ∷
   rw 8 q53 ∷
   rw 9 q52 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q54 ∷
   rw 11 q55 ∷
   rw 12 q54 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q56 ∷
   rw 5 q51 ∷
   rw 6 q61 ∷
   rw 7 q53 ∷
   rw 8 q61 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q54 ∷
   rw 10 q62 ∷
   rw 11 q54 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q59 ∷
   re 5 5 (ℓ "乜") ∷
   rw 6 q56 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q20 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q21 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q21 ∷
   rw⁻ 7 q22 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q21 ∷
   rw 4 q23 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q88 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "乀") ∷
   rw 6 q89 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "乀") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q21 ∷
   rw 4 q90 ∷
   re 4 5 (ℓ "乜") ∷
   rw 5 q21 ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q20 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q22 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q22 ∷
   rw 9 q20 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q21 ∷
   rw 2 q84 ∷
   rw 5 q66 ∷
   re 3 3 (ℓ "个") ∷
   rw 4 q85 ∷
   rw 7 q66 ∷
   re 5 3 (ℓ "个") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q67 ∷
   rw⁻ 8 q68 ∷
   rw 9 q69 ∷
   re 6 5 (ℓ "中") ∷
   rw 2 q49 ∷
   rw 3 q51 ∷
   rw 4 q61 ∷
   rw 5 q53 ∷
   rw 6 q61 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q54 ∷
   rw 8 q62 ∷
   rw 9 q54 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q59 ∷
   re 3 5 (ℓ "乜") ∷
   re 2 3 (ℓ "乛") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q91 ∷
   rw 4 q92 ∷
   rw 5 q93 ∷
   rw 6 q92 ∷
   rw 7 q84 ∷
   rw 3 q94 ∷
   re 3 5 (ℓ "乜") ∷
   rw 4 q70 ∷
   rw 1 q95 ∷
   rw 2 q96 ∷
   rw 3 q97 ∷
   rw 4 q98 ∷
   rw⁻ 3 q99 ∷
   rw 2 q100 ∷
   rw 6 q49 ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q51 ∷
   rw 6 q52 ∷
   rw 7 q53 ∷
   rw 8 q52 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q54 ∷
   rw 10 q55 ∷
   rw 11 q54 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q56 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q54 ∷
   rw 10 q57 ∷
   rw⁻ 9 q54 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q58 ∷
   rw⁻ 7 q53 ∷
   rw 6 q58 ∷
   rw⁻ 5 q51 ∷
   rw 6 q59 ∷
   re 6 5 (ℓ "乜") ∷
   rw⁻ 4 q63 ∷
   rw 5 q101 ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q51 ∷
   rw 5 q52 ∷
   rw 6 q53 ∷
   rw 7 q52 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q54 ∷
   rw 9 q55 ∷
   rw 10 q54 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q49 ∷
   rw 5 q51 ∷
   rw 6 q61 ∷
   rw 7 q53 ∷
   rw 8 q61 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q54 ∷
   rw 10 q62 ∷
   rw 11 q54 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q59 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   rw 5 q63 ∷
   rw 6 q56 ∷
   rw 3 q102 ∷
   rw 5 q103 ∷
   rw⁻ 0 q104 ∷ []) Eq.refl
