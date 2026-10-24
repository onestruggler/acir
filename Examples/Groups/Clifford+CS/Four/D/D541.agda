{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD541 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D541 (W : Ws) (Sᴰ : SD541) where

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
  lem-pass-CCZ023-vs-CSd23 : St 857
  lem-pass-CCZ023-vs-CSd23 = pickᴰ 0 Sᴰ
  lem-pass-CCZ023-vs-CZ23 : St 855
  lem-pass-CCZ023-vs-CZ23 = pickᴰ 1 Sᴰ
  lem-pass-CSd03-vs-CS01 : St 858
  lem-pass-CSd03-vs-CS01 = pickᴰ 2 Sᴰ
  lem-pass-CSd03-vs-CSd01 : St 859
  lem-pass-CSd03-vs-CSd01 = pickᴰ 3 Sᴰ
  lem-pass-CSd23-vs-CS01 : St 860
  lem-pass-CSd23-vs-CS01 = pickᴰ 4 Sᴰ
  lem-pass-CCZ123-vs-CSd03 : St 861
  lem-pass-CCZ123-vs-CSd03 = pickᴰ 5 Sᴰ
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 : St 841
  lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 6 Sᴰ
  lem-pass-CCZ023-vs-CS01 : St 856
  lem-pass-CCZ023-vs-CS01 = pickᴰ 7 Sᴰ
  lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12 : St 862
  lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 8 Sᴰ
  lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13 : St 863
  lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 9 Sᴰ
  lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12 : St 864
  lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12 = pickᴰ 10 Sᴰ
  lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01 : St 865
  lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01 = pickᴰ 11 Sᴰ
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 849
  lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 12 Sᴰ
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 866
  lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 13 Sᴰ
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 850
  lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 14 Sᴰ
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 867
  lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 15 Sᴰ
  lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 852
  lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 16 Sᴰ
  lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 868
  lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 17 Sᴰ
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 869
  lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 18 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 : St 870
  lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03 = pickᴰ 19 Sᴰ
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 : St 853
  lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13 = pickᴰ 20 Sᴰ
  lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 : St 871
  lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 21 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = wE 121 W
  q3 : Eqn
  q3 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q4 : Eqn
  q4 = wE 30 W
  q5 : Eqn
  q5 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 27 W
  q8 : Eqn
  q8 = wE 122 W
  q9 : Eqn
  q9 = wE 31 W
  q10 : Eqn
  q10 = wE 127 W
  q11 : Eqn
  q11 = wE 118 W
  q12 : Eqn
  q12 = wE 7 W
  q13 : Eqn
  q13 = wE 74 W
  q14 : Eqn
  q14 = wE 125 W
  q15 : Eqn
  q15 = wE 76 W
  q16 : Eqn
  q16 = wE 1471 W
  q17 : Eqn
  q17 = wE 123 W
  q18 : Eqn
  q18 = wE 24 W
  q19 : Eqn
  q19 = wE 25 W
  q20 : Eqn
  q20 = wE 124 W
  q21 : Eqn
  q21 = wE 29 W
  q22 : Eqn
  q22 = wE 26 W
  q23 : Eqn
  q23 = sE 856 lem-pass-CCZ023-vs-CS01
  q24 : Eqn
  q24 = sE 860 lem-pass-CSd23-vs-CS01
  q25 : Eqn
  q25 = sE 858 lem-pass-CSd03-vs-CS01
  q26 : Eqn
  q26 = wE 1469 W
  q27 : Eqn
  q27 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q28 : Eqn
  q28 = wE 1472 W
  q29 : Eqn
  q29 = sE 857 lem-pass-CCZ023-vs-CSd23
  q30 : Eqn
  q30 = sE 855 lem-pass-CCZ023-vs-CZ23
  q31 : Eqn
  q31 = wE 1473 W
  q32 : Eqn
  q32 = wE 33 W
  q33 : Eqn
  q33 = sE 859 lem-pass-CSd03-vs-CSd01

-- pass [CSd03] [TOFF023 CS01 TOFF023 CSd01]: 417 steps
lem-pass-CSd03-vs-TOFF023-CS01-TOFF023-CSd01 : ⟪ (ℓ "丮也丠也両") ⟫ʷ ≈ ⟪ (ℓ "也丠也両丮") ⟫ʷ
lem-pass-CSd03-vs-TOFF023-CS01-TOFF023-CSd01 = derive (ℓ "丮也丠也両") (ℓ "也丠也両丮")
  (rw 2 q1 ∷
   re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q5 ∷
   rw 5 q4 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 7 q7 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q2 ∷
   rw 8 q8 ∷
   rw 9 q9 ∷
   rw 8 q10 ∷
   rw 7 q11 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q6 ∷
   rw 7 q12 ∷
   rw⁻ 6 q6 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q13 ∷
   rw⁻ 4 q5 ∷
   rw 3 q13 ∷
   rw⁻ 2 q3 ∷
   rw 1 q11 ∷
   rw 2 q14 ∷
   re 2 8 (ℓ "乢") ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q15 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "举") ∷
   rw 1 q16 ∷
   re 1 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q2 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q17 ∷
   rw 2 q3 ∷
   rw 3 q18 ∷
   rw 4 q5 ∷
   rw 5 q18 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q19 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q17 ∷
   rw 8 q20 ∷
   rw 1 q14 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q6 ∷
   rw 2 q21 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q5 ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q1 ∷
   rw 4 q3 ∷
   rw 5 q18 ∷
   rw 6 q5 ∷
   rw 7 q18 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 9 q19 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q22 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   rw 4 q9 ∷
   rw 3 q23 ∷
   rw 2 q24 ∷
   rw 1 q25 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "並乢並") ∷
   re 6 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 5 q2 ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q2 ∷
   rw 12 q8 ∷
   rw 13 q9 ∷
   rw 12 q10 ∷
   rw 11 q11 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q6 ∷
   rw 11 q12 ∷
   rw⁻ 10 q6 ∷
   re 11 3 (ℓ "丽") ∷
   rw 9 q13 ∷
   rw⁻ 8 q5 ∷
   rw 7 q13 ∷
   rw⁻ 6 q3 ∷
   rw 5 q11 ∷
   rw 6 q14 ∷
   re 6 8 (ℓ "乢") ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q9 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 5 q22 ∷
   re 5 5 (ℓ "乜") ∷
   rw 5 q26 ∷
   re 5 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q2 ∷
   rw 11 q8 ∷
   rw 4 q1 ∷
   rw 5 q17 ∷
   rw 6 q3 ∷
   rw 7 q18 ∷
   rw 8 q5 ∷
   rw 9 q18 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 11 q19 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "丽") ∷
   rw 11 q17 ∷
   rw 12 q20 ∷
   rw 5 q14 ∷
   re 5 8 (ℓ "乢") ∷
   re 4 3 (ℓ "也") ∷
   rw 5 q27 ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   rw 6 q3 ∷
   rw 7 q4 ∷
   rw 8 q5 ∷
   rw 9 q4 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q6 ∷
   rw 11 q7 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q1 ∷
   rw 7 q3 ∷
   rw 8 q18 ∷
   rw 9 q5 ∷
   rw 10 q18 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   rw 12 q19 ∷
   rw 13 q6 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q22 ∷
   re 7 5 (ℓ "乜") ∷
   re 6 3 (ℓ "乛") ∷
   rw 7 q9 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "並乢並") ∷
   re 5 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 4 q2 ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q2 ∷
   rw 11 q8 ∷
   rw 12 q9 ∷
   rw 11 q10 ∷
   rw 10 q11 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q6 ∷
   rw 10 q12 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q13 ∷
   rw⁻ 7 q5 ∷
   rw 6 q13 ∷
   rw⁻ 5 q3 ∷
   rw 4 q11 ∷
   rw 5 q14 ∷
   re 5 8 (ℓ "乢") ∷
   rw⁻ 3 q5 ∷
   rw 4 q28 ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 3 q1 ∷
   rw 4 q17 ∷
   rw 5 q3 ∷
   rw 6 q18 ∷
   rw 7 q5 ∷
   rw 8 q18 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 10 q19 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 10 q17 ∷
   rw 11 q20 ∷
   rw 4 q14 ∷
   re 4 8 (ℓ "乢") ∷
   re 3 3 (ℓ "也") ∷
   rw 4 q5 ∷
   rw 5 q9 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "並乢並") ∷
   re 4 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 3 q2 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q2 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q11 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 3 q11 ∷
   rw 4 q14 ∷
   re 4 8 (ℓ "乢") ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q15 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "举") ∷
   rw 3 q16 ∷
   re 3 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 2 q2 ∷
   rw 3 q3 ∷
   rw 4 q4 ∷
   rw 5 q5 ∷
   rw 6 q4 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 8 q7 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q2 ∷
   rw 9 q8 ∷
   rw 2 q1 ∷
   rw 3 q17 ∷
   rw 4 q3 ∷
   rw 5 q18 ∷
   rw 6 q5 ∷
   rw 7 q18 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 9 q19 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丽") ∷
   rw 9 q17 ∷
   rw 10 q20 ∷
   rw 3 q14 ∷
   re 3 8 (ℓ "乢") ∷
   re 2 3 (ℓ "也") ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q6 ∷
   rw 4 q21 ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q5 ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 5 q1 ∷
   rw 6 q3 ∷
   rw 7 q18 ∷
   rw 8 q5 ∷
   rw 9 q18 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 11 q19 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "丽") ∷
   rw 6 q22 ∷
   re 6 5 (ℓ "乜") ∷
   re 5 3 (ℓ "乛") ∷
   rw 6 q9 ∷
   rw 5 q29 ∷
   rw 6 q30 ∷
   rw 4 q31 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q3 ∷
   rw 6 q4 ∷
   rw 7 q5 ∷
   rw 8 q4 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q6 ∷
   rw 10 q7 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q9 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q6 ∷
   rw 10 q12 ∷
   rw⁻ 9 q6 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q13 ∷
   rw⁻ 7 q5 ∷
   rw 6 q13 ∷
   rw⁻ 5 q3 ∷
   rw 6 q22 ∷
   re 6 5 (ℓ "乜") ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q9 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw 5 q22 ∷
   re 5 5 (ℓ "乜") ∷
   rw 5 q32 ∷
   rw 4 q9 ∷
   rw 3 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 1 W
  q35 : Eqn
  q35 = wE 1357 W
  q36 : Eqn
  q36 = wE 3 W
  q37 : Eqn
  q37 = wE 45 W
  q38 : Eqn
  q38 = wE 231 W
  q39 : Eqn
  q39 = sE 841 lem-pass-X3-CKd30-X3-vs-TOFF012-CS03-TOFF012-CSd03
  q40 : Eqn
  q40 = wE 1358 W
  q41 : Eqn
  q41 = wE 227 W
  q42 : Eqn
  q42 = wE 1342 W

-- pass [X3 CKd30 X3] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丞乒丞中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丞乒丞中九丮九") (ℓ "中九丮九丞乒丞")
  (rw 0 q34 ∷
   rw 1 q35 ∷
   rw 2 q34 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q34 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q36 ∷
   rw 1 q37 ∷
   rw 2 q34 ∷
   rw 3 q38 ∷
   rw 4 q34 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q34 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q36 ∷
   rw 3 q37 ∷
   rw⁻ 4 q39 ∷
   rw 12 q34 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q36 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q36 ∷
   rw 11 q40 ∷
   rw 10 q36 ∷
   rw 9 q41 ∷
   rw 10 q34 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q36 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q36 ∷
   rw 9 q42 ∷
   rw 8 q36 ∷
   rw 7 q41 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = sE 870 lem-pass-X2-CSd20-X2-vs-TOFF012-CS03-TOFF012-CSd03

-- pass [X2 CSd20 X2] [CS03 TOFF012 CSd03 TOFF012]: 33 steps
lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 : ⟪ (ℓ "丘丨丘中九丮九") ⟫ʷ ≈ ⟪ (ℓ "中九丮九丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CS03-TOFF012-CSd03-TOFF012 = derive (ℓ "丘丨丘中九丮九") (ℓ "中九丮九丘丨丘")
  (rw 0 q34 ∷
   rw 1 q35 ∷
   rw 2 q34 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q34 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q36 ∷
   rw 1 q37 ∷
   rw 2 q34 ∷
   rw 3 q38 ∷
   rw 4 q34 ∷
   re 2 3 (ℓ "丮") ∷
   rw 5 q34 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q36 ∷
   rw 3 q37 ∷
   rw⁻ 4 q43 ∷
   rw 12 q34 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q36 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q36 ∷
   rw 11 q40 ∷
   rw 10 q36 ∷
   rw 9 q41 ∷
   rw 10 q34 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q36 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q36 ∷
   rw 9 q42 ∷
   rw 8 q36 ∷
   rw 7 q41 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 1474 W
  q45 : Eqn
  q45 = sE 868 lem-pass-X2-CS21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q46 : Eqn
  q46 = wE 1475 W

-- pass [CS21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丶丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丶") ⟫ʷ
lem-pass-CS21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丶丘中九丮九丘") (ℓ "丘中九丮九丘丶")
  (rw 0 q44 ∷
   rw 1 q45 ∷
   rw 5 q46 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 1476 W
  q48 : Eqn
  q48 = sE 866 lem-pass-X2-CK21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q49 : Eqn
  q49 = wE 1477 W

-- pass [CK21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "乇丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘乇") ⟫ʷ
lem-pass-CK21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "乇丘中九丮九丘") (ℓ "丘中九丮九丘乇")
  (rw 0 q47 ∷
   rw 1 q48 ∷
   rw 5 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 1478 W
  q51 : Eqn
  q51 = sE 867 lem-pass-X2-CKd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q52 : Eqn
  q52 = wE 1479 W

-- pass [CKd21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "么丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘么") ⟫ʷ
lem-pass-CKd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "么丘中九丮九丘") (ℓ "丘中九丮九丘么")
  (rw 0 q50 ∷
   rw 1 q51 ∷
   rw 5 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 1480 W
  q54 : Eqn
  q54 = sE 871 lem-pass-X2-CSd21-X2-vs-CS03-TOFF012-CSd03-TOFF012
  q55 : Eqn
  q55 = wE 1481 W

-- pass [CSd21] [X2 CS03 TOFF012 CSd03 TOFF012 X2]: 3 steps
lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 : ⟪ (ℓ "丷丘中九丮九丘") ⟫ʷ ≈ ⟪ (ℓ "丘中九丮九丘丷") ⟫ʷ
lem-pass-CSd21-vs-X2-CS03-TOFF012-CSd03-TOFF012-X2 = derive (ℓ "丷丘中九丮九丘") (ℓ "丘中九丮九丘丷")
  (rw 0 q53 ∷
   rw 1 q54 ∷
   rw 5 q55 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = wE 1482 W
  q57 : Eqn
  q57 = wE 1483 W
  q58 : Eqn
  q58 = sE 853 lem-pass-X2-CSd20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q59 : Eqn
  q59 = wE 1484 W

-- pass [X2 CSd20 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘丨丘与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘丨丘与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘丨丘")
  (rw 0 q56 ∷
   rw 0 q57 ∷
   rw 2 q58 ∷
   rw 6 q59 ∷
   rw 8 q56 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 1485 W
  q61 : Eqn
  q61 = wE 1486 W
  q62 : Eqn
  q62 = sE 850 lem-pass-X2-CKd20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q63 : Eqn
  q63 = wE 1487 W

-- pass [X2 CKd20 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘久丘与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘久丘与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘久丘")
  (rw 0 q60 ∷
   rw 0 q61 ∷
   rw 2 q62 ∷
   rw 6 q63 ∷
   rw 8 q60 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 1413 W
  q65 : Eqn
  q65 = wE 1488 W
  q66 : Eqn
  q66 = sE 849 lem-pass-X2-CK20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q67 : Eqn
  q67 = wE 1489 W

-- pass [X2 CK20 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘乄丘与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘乄丘与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘乄丘")
  (rw 0 q64 ∷
   rw 0 q65 ∷
   rw 2 q66 ∷
   rw 6 q67 ∷
   rw 8 q64 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 1490 W
  q69 : Eqn
  q69 = wE 1491 W
  q70 : Eqn
  q70 = sE 852 lem-pass-X2-CS20-X2-vs-TOFF102-CS13-TOFF102-CSd13
  q71 : Eqn
  q71 = wE 1492 W

-- pass [X2 CS20 X2] [S1 K1 TOFF102 CS13 TOFF102 CSd13 Kd1 Sd1]: 5 steps
lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 : ⟪ (ℓ "丘丧丘与丐习丽习举丑丏") ⟫ʷ ≈ ⟪ (ℓ "与丐习丽习举丑丏丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-S1-K1-TOFF102-CS13-TOFF102-CSd13-Kd1-Sd1 = derive (ℓ "丘丧丘与丐习丽习举丑丏") (ℓ "与丐习丽习举丑丏丘丧丘")
  (rw 0 q68 ∷
   rw 0 q69 ∷
   rw 2 q70 ∷
   rw 6 q71 ∷
   rw 8 q68 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 1493 W
  q73 : Eqn
  q73 = wE 1494 W

-- pass [X2 CS21 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X2-CS21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "丘丶丘丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "丘丶丘丞中九丮九丞") (ℓ "丞中九丮九丞丘丶丘")
  (rw 0 q72 ∷
   rw 1 q73 ∷
   rw 1 q45 ∷
   rw 5 q73 ∷
   rw 5 q72 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 1495 W
  q75 : Eqn
  q75 = wE 1496 W

-- pass [X2 CK21 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X2-CK21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "丘乇丘丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "丘乇丘丞中九丮九丞") (ℓ "丞中九丮九丞丘乇丘")
  (rw 0 q74 ∷
   rw 1 q75 ∷
   rw 1 q48 ∷
   rw 5 q75 ∷
   rw 5 q74 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 1497 W
  q77 : Eqn
  q77 = wE 1498 W

-- pass [X2 CKd21 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X2-CKd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "丘么丘丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "丘么丘丞中九丮九丞") (ℓ "丞中九丮九丞丘么丘")
  (rw 0 q76 ∷
   rw 1 q77 ∷
   rw 1 q51 ∷
   rw 5 q77 ∷
   rw 5 q76 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 1499 W
  q79 : Eqn
  q79 = wE 1500 W

-- pass [X2 CSd21 X2] [X3 CS03 TOFF012 CSd03 TOFF012 X3]: 5 steps
lem-pass-X2-CSd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 : ⟪ (ℓ "丘丷丘丞中九丮九丞") ⟫ʷ ≈ ⟪ (ℓ "丞中九丮九丞丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-X3-CS03-TOFF012-CSd03-TOFF012-X3 = derive (ℓ "丘丷丘丞中九丮九丞") (ℓ "丞中九丮九丞丘丷丘")
  (rw 0 q78 ∷
   rw 1 q79 ∷
   rw 1 q54 ∷
   rw 5 q79 ∷
   rw 5 q78 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = sE 863 lem-pass-S0-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [TOFF102 CS13 TOFF102 CSd13] [S0]: 1 steps
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0 : ⟪ (ℓ "习丽习举丈") ⟫ʷ ≈ ⟪ (ℓ "丈习丽习举") ⟫ʷ
lem-pass-TOFF102-CS13-TOFF102-CSd13-vs-S0 = derive (ℓ "习丽习举丈") (ℓ "丈习丽习举")
  (rw⁻ 0 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = sE 864 lem-pass-S0-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [TOFF103 CS12 TOFF103 CSd12] [S0]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-S0 : ⟪ (ℓ "乡丶乡丷丈") ⟫ʷ ≈ ⟪ (ℓ "丈乡丶乡丷") ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-S0 = derive (ℓ "乡丶乡丷丈") (ℓ "丈乡丶乡丷")
  (rw⁻ 0 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = sE 862 lem-pass-CSd03-vs-TOFF103-CS12-TOFF103-CSd12

-- pass [TOFF103 CS12 TOFF103 CSd12] [CSd03]: 1 steps
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd03 : ⟪ (ℓ "乡丶乡丷丮") ⟫ʷ ≈ ⟪ (ℓ "丮乡丶乡丷") ⟫ʷ
lem-pass-TOFF103-CS12-TOFF103-CSd12-vs-CSd03 = derive (ℓ "乡丶乡丷丮") (ℓ "丮乡丶乡丷")
  (rw⁻ 0 q82 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 128 W
  q84 : Eqn
  q84 = eqn (ℓ "丑乏") (ℓ "乏丑") (low-comm (((K • iI) ↑)) (Swap))
  q85 : Eqn
  q85 = wE 1448 W
  q86 : Eqn
  q86 = sE 861 lem-pass-CCZ123-vs-CSd03
  q87 : Eqn
  q87 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q88 : Eqn
  q88 = wE 1449 W
  q89 : Eqn
  q89 = wE 1437 W

-- pass [TOFF123] [CSd03]: 21 steps
lem-pass-TOFF123-vs-CSd03 : ⟪ (ℓ "乢丮") ⟫ʷ ≈ ⟪ (ℓ "丮乢") ⟫ʷ
lem-pass-TOFF123-vs-CSd03 = derive (ℓ "乢丮") (ℓ "丮乢")
  (rw 0 q83 ∷
   rw 4 q34 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q36 ∷
   rw 2 q84 ∷
   rw 3 q85 ∷
   rw 4 q34 ∷
   re 2 3 (ℓ "丮") ∷
   rw⁻ 3 q84 ∷
   rw 4 q36 ∷
   rw 1 q86 ∷
   rw 2 q34 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q36 ∷
   rw 0 q87 ∷
   rw 1 q88 ∷
   rw 2 q34 ∷
   re 0 3 (ℓ "丮") ∷
   rw⁻ 1 q87 ∷
   rw 2 q36 ∷
   rw 1 q89 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = sE 865 lem-pass-S0-vs-TOFF123-CS01-TOFF123-CSd01

-- pass [TOFF123 CS01 TOFF123 CSd01] [S0]: 1 steps
lem-pass-TOFF123-CS01-TOFF123-CSd01-vs-S0 : ⟪ (ℓ "乢丠乢両丈") ⟫ʷ ≈ ⟪ (ℓ "丈乢丠乢両") ⟫ʷ
lem-pass-TOFF123-CS01-TOFF123-CSd01-vs-S0 = derive (ℓ "乢丠乢両丈") (ℓ "丈乢丠乢両")
  (rw⁻ 0 q90 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = sE 869 lem-pass-X2-CS21-X2-vs-TOFF102-CS13-TOFF102-CSd13

-- pass [CS21] [X2 TOFF102 CS13 TOFF102 CSd13 X2]: 3 steps
lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 : ⟪ (ℓ "丶丘习丽习举丘") ⟫ʷ ≈ ⟪ (ℓ "丘习丽习举丘丶") ⟫ʷ
lem-pass-CS21-vs-X2-TOFF102-CS13-TOFF102-CSd13-X2 = derive (ℓ "丶丘习丽习举丘") (ℓ "丘习丽习举丘丶")
  (rw 0 q44 ∷
   rw 1 q91 ∷
   rw 5 q46 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 1501 W
  q93 : Eqn
  q93 = wE 1502 W

-- pass [X2 CSd21 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘丷丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘丷丘") ⟫ʷ
lem-pass-X2-CSd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘丷丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘丷丘")
  (rw 0 q79 ∷
   rw 0 q92 ∷
   rw 2 q54 ∷
   rw 6 q93 ∷
   rw 8 q79 ∷ []) Eq.refl

private
  q94 : Eqn
  q94 = wE 1503 W
  q95 : Eqn
  q95 = wE 1504 W

-- pass [X2 CKd21 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘么丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘么丘") ⟫ʷ
lem-pass-X2-CKd21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘么丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘么丘")
  (rw 0 q77 ∷
   rw 0 q94 ∷
   rw 2 q51 ∷
   rw 6 q95 ∷
   rw 8 q77 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = wE 1505 W
  q97 : Eqn
  q97 = wE 1506 W

-- pass [X2 CK21 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘乇丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘乇丘") ⟫ʷ
lem-pass-X2-CK21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘乇丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘乇丘")
  (rw 0 q75 ∷
   rw 0 q96 ∷
   rw 2 q48 ∷
   rw 6 q97 ∷
   rw 8 q75 ∷ []) Eq.refl

private
  q98 : Eqn
  q98 = wE 1507 W
  q99 : Eqn
  q99 = wE 1508 W

-- pass [X2 CS21 X2] [S0 K0 CS03 TOFF012 CSd03 TOFF012 Kd0 Sd0]: 5 steps
lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 : ⟪ (ℓ "丘丶丘丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "丈上中九丮九下三丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-S0-K0-CS03-TOFF012-CSd03-TOFF012-Kd0-Sd0 = derive (ℓ "丘丶丘丈上中九丮九下三") (ℓ "丈上中九丮九下三丘丶丘")
  (rw 0 q73 ∷
   rw 0 q98 ∷
   rw 2 q45 ∷
   rw 6 q99 ∷
   rw 8 q73 ∷ []) Eq.refl

-- pass [X2 CS21 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 5 steps
lem-pass-X2-CS21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (ℓ "丘丶丘丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞丘丶丘") ⟫ʷ
lem-pass-X2-CS21-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (ℓ "丘丶丘丞习丽习举丞") (ℓ "丞习丽习举丞丘丶丘")
  (rw 0 q72 ∷
   rw 1 q73 ∷
   rw 1 q91 ∷
   rw 5 q73 ∷
   rw 5 q72 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q101 : Eqn
  q101 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))

-- pass [X2 CS20 X2] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 25 steps
lem-pass-X2-CS20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (ℓ "丘丧丘丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (ℓ "丘丧丘丞习丽习举丞") (ℓ "丞习丽习举丞丘丧丘")
  (rw 4 q1 ∷
   rw⁻ 3 q100 ∷
   rw⁻ 2 q101 ∷
   rw 1 q12 ∷
   rw⁻ 0 q101 ∷
   rw 1 q72 ∷
   rw 0 q100 ∷
   rw 1 q101 ∷
   rw 2 q7 ∷
   rw 3 q101 ∷
   rw 4 q9 ∷
   rw 1 q68 ∷
   rw 1 q70 ∷
   rw 5 q68 ∷
   rw 9 q1 ∷
   rw⁻ 8 q100 ∷
   rw⁻ 7 q101 ∷
   rw 6 q12 ∷
   rw⁻ 5 q101 ∷
   rw 6 q72 ∷
   rw 5 q100 ∷
   rw 6 q101 ∷
   rw 7 q7 ∷
   rw 8 q101 ∷
   rw 9 q9 ∷ []) Eq.refl
