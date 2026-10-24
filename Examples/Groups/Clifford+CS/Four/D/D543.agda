{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD543 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D543 (W : Ws) (Sᴰ : SD543) where

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
  lem-pass-CS12-vs-CS03 : St 21
  lem-pass-CS12-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CS13-vs-CS02 : St 27
  lem-pass-CS13-vs-CS02 = pickᴰ 1 Sᴰ
  lem-pass-CS12-vs-CSd03 : St 34
  lem-pass-CS12-vs-CSd03 = pickᴰ 2 Sᴰ
  lem-pass-CCZ012-vs-CS02 : St 880
  lem-pass-CCZ012-vs-CS02 = pickᴰ 3 Sᴰ
  lem-pass-CCZ012-vs-CZ02 : St 872
  lem-pass-CCZ012-vs-CZ02 = pickᴰ 4 Sᴰ
  lem-pass-CCZ013-vs-CZ03 : St 881
  lem-pass-CCZ013-vs-CZ03 = pickᴰ 5 Sᴰ
  lem-pass-CS12-vs-CS13 : St 873
  lem-pass-CS12-vs-CS13 = pickᴰ 6 Sᴰ
  lem-pass-CS12-vs-CSd13 : St 874
  lem-pass-CS12-vs-CSd13 = pickᴰ 7 Sᴰ
  lem-pass-CS13-vs-CZ03 : St 882
  lem-pass-CS13-vs-CZ03 = pickᴰ 8 Sᴰ
  lem-pass-CSd12-vs-CS13 : St 876
  lem-pass-CSd12-vs-CS13 = pickᴰ 9 Sᴰ
  lem-pass-CSd12-vs-CSd13 : St 877
  lem-pass-CSd12-vs-CSd13 = pickᴰ 10 Sᴰ
  lem-pass-CSd13-vs-CZ03 : St 883
  lem-pass-CSd13-vs-CZ03 = pickᴰ 11 Sᴰ
  lem-pass-S1-vs-CS13 : St 884
  lem-pass-S1-vs-CS13 = pickᴰ 12 Sᴰ
  lem-pass-S1-vs-CSd13 : St 885
  lem-pass-S1-vs-CSd13 = pickᴰ 13 Sᴰ
  lem-pass-CCZ012-vs-CS13 : St 829
  lem-pass-CCZ012-vs-CS13 = pickᴰ 14 Sᴰ
  lem-pass-CCZ013-vs-CS12 : St 832
  lem-pass-CCZ013-vs-CS12 = pickᴰ 15 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 196 W
  q7 : Eqn
  q7 = wE 1511 W
  q8 : Eqn
  q8 = wE 43 W
  q9 : Eqn
  q9 = sE 832 lem-pass-CCZ013-vs-CS12
  q10 : Eqn
  q10 = sE 873 lem-pass-CS12-vs-CS13
  q11 : Eqn
  q11 = sE 21 lem-pass-CS12-vs-CS03
  q12 : Eqn
  q12 = wE 1512 W
  q13 : Eqn
  q13 = wE 1351 W
  q14 : Eqn
  q14 = sE 881 lem-pass-CCZ013-vs-CZ03
  q15 : Eqn
  q15 = sE 882 lem-pass-CS13-vs-CZ03
  q16 : Eqn
  q16 = wE 1513 W
  q17 : Eqn
  q17 = wE 32 W
  q18 : Eqn
  q18 = sE 876 lem-pass-CSd12-vs-CS13

-- pass [CS13] [TOFF103 CS12 TOFF103 CSd12]: 390 steps
lem-pass-CS13-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (ℓ "丽乡丶乡丷") ⟫ʷ ≈ ⟪ (ℓ "乡丶乡丷丽") ⟫ʷ
lem-pass-CS13-vs-TOFF103-CS12-TOFF103-CSd12 = derive (ℓ "丽乡丶乡丷") (ℓ "乡丶乡丷丽")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw 8 q4 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw 3 q3 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 1 q2 ∷
   rw 2 q6 ∷
   re 2 8 (ℓ "习") ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 4 q8 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 4 q5 ∷
   rw 3 q9 ∷
   rw⁻ 2 q10 ∷
   rw⁻ 1 q11 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏习乏") ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw 5 q2 ∷
   rw 6 q6 ∷
   re 6 8 (ℓ "习") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q5 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 5 q8 ∷
   re 5 5 (ℓ "乙") ∷
   rw 5 q12 ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q1 ∷
   rw⁻ 5 q2 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "习") ∷
   re 4 3 (ℓ "乡") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丯") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 7 q8 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   rw 7 q5 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 12 q5 ∷
   rw 11 q4 ∷
   rw 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 4 q2 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "习") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 4 q7 ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q1 ∷
   rw⁻ 4 q2 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "习") ∷
   re 3 3 (ℓ "乡") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 7 q8 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   rw 7 q5 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 3 q2 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "习") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   rw 3 q13 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q1 ∷
   rw⁻ 3 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q6 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q5 ∷
   rw 6 q14 ∷
   rw 5 q15 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丩乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 4 q16 ∷
   rw 3 q5 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q5 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 6 q8 ∷
   re 6 5 (ℓ "乙") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q5 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 5 q8 ∷
   re 5 5 (ℓ "乙") ∷
   rw 5 q17 ∷
   rw 4 q5 ∷
   rw⁻ 3 q18 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 1514 W
  q20 : Eqn
  q20 = sE 874 lem-pass-CS12-vs-CSd13
  q21 : Eqn
  q21 = sE 34 lem-pass-CS12-vs-CSd03
  q22 : Eqn
  q22 = wE 1352 W
  q23 : Eqn
  q23 = sE 883 lem-pass-CSd13-vs-CZ03
  q24 : Eqn
  q24 = wE 1515 W
  q25 : Eqn
  q25 = sE 877 lem-pass-CSd12-vs-CSd13

-- pass [CSd13] [TOFF103 CS12 TOFF103 CSd12]: 390 steps
lem-pass-CSd13-vs-TOFF103-CS12-TOFF103-CSd12 : ⟪ (ℓ "举乡丶乡丷") ⟫ʷ ≈ ⟪ (ℓ "乡丶乡丷举") ⟫ʷ
lem-pass-CSd13-vs-TOFF103-CS12-TOFF103-CSd12 = derive (ℓ "举乡丶乡丷") (ℓ "乡丶乡丷举")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏习乏") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q3 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 9 q5 ∷
   rw 8 q4 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw 3 q3 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 1 q2 ∷
   rw 2 q6 ∷
   re 2 8 (ℓ "习") ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q5 ∷
   rw 1 q19 ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q3 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q2 ∷
   rw⁻ 7 q4 ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q3 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q2 ∷
   rw⁻ 8 q4 ∷
   rw 1 q6 ∷
   re 1 8 (ℓ "习") ∷
   re 0 3 (ℓ "乡") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "举") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 4 q8 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 4 q5 ∷
   rw 3 q9 ∷
   rw⁻ 2 q20 ∷
   rw⁻ 1 q21 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏习乏") ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 5 q2 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q2 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   rw 9 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw 5 q2 ∷
   rw 6 q6 ∷
   re 6 8 (ℓ "习") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q5 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 5 q8 ∷
   re 5 5 (ℓ "乙") ∷
   rw 5 q12 ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q1 ∷
   rw⁻ 5 q2 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q3 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 12 q4 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "习") ∷
   re 4 3 (ℓ "乡") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丯") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 7 q8 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   rw 7 q5 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q2 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 12 q5 ∷
   rw 11 q4 ∷
   rw 10 q2 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 4 q2 ∷
   rw 5 q6 ∷
   re 5 8 (ℓ "习") ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw 4 q19 ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q1 ∷
   rw⁻ 4 q2 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q3 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q4 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "习") ∷
   re 3 3 (ℓ "乡") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丮") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q3 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q3 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 7 q8 ∷
   re 7 5 (ℓ "乙") ∷
   re 6 3 (ℓ "乚") ∷
   rw 7 q5 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏习乏") ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 11 q5 ∷
   rw 10 q4 ∷
   rw 9 q2 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 3 q2 ∷
   rw 4 q6 ∷
   re 4 8 (ℓ "习") ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q5 ∷
   rw 3 q22 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q2 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q3 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q2 ∷
   rw⁻ 9 q4 ∷
   rw 2 q1 ∷
   rw⁻ 3 q2 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 10 q4 ∷
   rw 3 q6 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q5 ∷
   rw 6 q14 ∷
   rw 5 q23 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丩乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q5 ∷
   rw 4 q24 ∷
   rw 3 q5 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q3 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q3 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q5 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 6 q8 ∷
   re 6 5 (ℓ "乙") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q3 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q3 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q5 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 5 q8 ∷
   re 5 5 (ℓ "乙") ∷
   rw 5 q17 ∷
   rw 4 q5 ∷
   rw⁻ 3 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1518 W
  q27 : Eqn
  q27 = sE 829 lem-pass-CCZ012-vs-CS13
  q28 : Eqn
  q28 = sE 27 lem-pass-CS13-vs-CS02
  q29 : Eqn
  q29 = sE 884 lem-pass-S1-vs-CS13
  q30 : Eqn
  q30 = sE 880 lem-pass-CCZ012-vs-CS02
  q31 : Eqn
  q31 = sE 872 lem-pass-CCZ012-vs-CZ02
  q32 : Eqn
  q32 = sE 885 lem-pass-S1-vs-CSd13

-- pass [S1] [TOFF102 CS13 TOFF102 CSd13]: 12 steps
lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "与习丽习举") ⟫ʷ ≈ ⟪ (ℓ "习丽习举与") ⟫ʷ
lem-pass-S1-vs-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "与习丽习举") (ℓ "习丽习举与")
  (rw 0 q26 ∷
   rw 3 q27 ∷
   rw⁻ 2 q28 ∷
   rw 1 q29 ∷
   rw 4 q12 ∷
   rw 3 q13 ∷
   rw 2 q26 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 4 q16 ∷
   rw 4 q17 ∷
   rw 3 q32 ∷ []) Eq.refl
