{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D012 (W : Ws) where

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

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 252 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 70 W
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 74 W
  q8 : Eqn
  q8 = wE 10 W
  q9 : Eqn
  q9 = wE 253 W
  q10 : Eqn
  q10 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q11 : Eqn
  q11 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q12 : Eqn
  q12 = wE 24 W
  q13 : Eqn
  q13 = wE 25 W
  q14 : Eqn
  q14 = wE 26 W
  q15 : Eqn
  q15 = wE 12 W
  q16 : Eqn
  q16 = wE 36 W
  q17 : Eqn
  q17 = wE 30 W
  q18 : Eqn
  q18 = wE 27 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = wE 22 W
  q21 : Eqn
  q21 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q22 : Eqn
  q22 = wE 23 W
  q23 : Eqn
  q23 = wE 14 W
  q24 : Eqn
  q24 = wE 47 W
  q25 : Eqn
  q25 = wE 48 W
  q26 : Eqn
  q26 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = wE 43 W
  q28 : Eqn
  q28 = wE 44 W
  q29 : Eqn
  q29 = eqn (ℓ "乖乙乖") (ℓ "乙乚") (ax cx-ccz)
  q30 : Eqn
  q30 = wE 20 W
  q31 : Eqn
  q31 = wE 21 W
  q32 : Eqn
  q32 = wE 18 W
  q33 : Eqn
  q33 = wE 19 W
  q34 : Eqn
  q34 = wE 17 W
  q35 : Eqn
  q35 = wE 28 W
  q36 : Eqn
  q36 = wE 29 W
  q37 : Eqn
  q37 = wE 11 W
  q38 : Eqn
  q38 = wE 33 W
  q39 : Eqn
  q39 = wE 32 W

-- comm CCZ012 CCZ123: 455 steps
lem-comm-CCZ012-CCZ123 : ⟪ (ℓ "乙乜") ⟫ʷ ≈ ⟪ (ℓ "乜乙") ⟫ʷ
lem-comm-CCZ012-CCZ123 = derive (ℓ "乙乜") (ℓ "乜乙")
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丰") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丰") ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 4 q1 ∷
   rw 5 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丰") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丰") ∷
   rw 6 q3 ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏个乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q7 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "乀") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw⁻ 9 q6 ∷
   rw 8 q8 ∷
   rw⁻ 7 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 6 q9 ∷
   rw⁻ 5 q10 ∷
   rw 4 q9 ∷
   rw⁻ 3 q11 ∷
   rw 4 q5 ∷
   rw 5 q11 ∷
   rw 6 q12 ∷
   rw 7 q10 ∷
   rw 8 q12 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 10 q13 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q14 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   re 2 1 (ℓ "乏个乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q7 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "乀") ∷
   rw 6 q15 ∷
   rw 5 q16 ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q11 ∷
   rw 5 q17 ∷
   rw 6 q10 ∷
   rw 7 q17 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q18 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q19 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q20 ∷
   rw 10 q21 ∷
   rw 8 q22 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "丼丣丼") ∷
   rw 9 q23 ∷
   rw 6 q24 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 7 q23 ∷
   rw 4 q25 ∷
   rw 5 q1 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q3 ∷
   rw⁻ 9 q26 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q3 ∷
   rw 6 q27 ∷
   re 6 5 (ℓ "乙") ∷
   re 5 3 (ℓ "乚") ∷
   rw 3 q16 ∷
   rw 7 q1 ∷
   rw 6 q28 ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q26 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q26 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q3 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q3 ∷
   rw 8 q26 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q3 ∷
   rw 6 q26 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 6 q27 ∷
   re 6 5 (ℓ "乙") ∷
   rw 4 q28 ∷
   rw 5 q29 ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q26 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q26 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q3 ∷
   rw⁻ 8 q26 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q3 ∷
   rw 5 q27 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   re 6 1 (ℓ "乏乙乏") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q26 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q26 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q3 ∷
   rw⁻ 8 q26 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q3 ∷
   rw 5 q27 ∷
   re 5 5 (ℓ "乙") ∷
   rw 6 q3 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q26 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q26 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q3 ∷
   rw 3 q30 ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q31 ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q20 ∷
   rw⁻ 9 q21 ∷
   rw 10 q22 ∷
   re 7 5 (ℓ "中") ∷
   rw 3 q5 ∷
   rw 4 q11 ∷
   rw 5 q12 ∷
   rw 6 q10 ∷
   rw 7 q12 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q6 ∷
   rw 9 q13 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q14 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q32 ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "个") ∷
   rw 6 q33 ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "个") ∷
   re 9 1 (ℓ "丼丠丼") ∷
   rw 8 q23 ∷
   rw 4 q34 ∷
   re 4 5 (ℓ "乙") ∷
   rw 5 q23 ∷
   re 3 1 (ℓ "並乜並") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q11 ∷
   rw 4 q17 ∷
   rw 5 q10 ∷
   rw 6 q17 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q6 ∷
   rw 8 q18 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q19 ∷
   rw 2 q11 ∷
   rw 3 q12 ∷
   rw 4 q10 ∷
   rw 5 q12 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q13 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q14 ∷
   re 2 5 (ℓ "乜") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q18 ∷
   rw 4 q35 ∷
   rw 5 q36 ∷
   rw 6 q35 ∷
   rw 7 q13 ∷
   rw 3 q37 ∷
   re 3 5 (ℓ "乙") ∷
   rw 4 q19 ∷
   rw 1 q38 ∷
   rw 0 q39 ∷
   rw 3 q5 ∷
   re 2 1 (ℓ "乏个乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q7 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "乀") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw⁻ 7 q6 ∷
   rw 6 q8 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 4 q9 ∷
   rw⁻ 3 q10 ∷
   rw 2 q9 ∷
   rw⁻ 1 q11 ∷
   rw 2 q5 ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   rw 5 q10 ∷
   rw 6 q12 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw 8 q13 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q14 ∷
   re 3 5 (ℓ "乜") ∷
   re 2 3 (ℓ "乛") ∷
   re 0 1 (ℓ "乏个乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q7 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "乀") ∷
   rw 4 q15 ∷
   rw 3 q16 ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q11 ∷
   rw 3 q17 ∷
   rw 4 q10 ∷
   rw 5 q17 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 7 q18 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q19 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q20 ∷
   rw 8 q21 ∷
   rw 6 q22 ∷
   re 7 5 (ℓ "中") ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 7 q23 ∷
   rw 4 q24 ∷
   re 3 1 (ℓ "丼丣丼") ∷
   rw 5 q23 ∷
   rw 2 q25 ∷
   rw 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   rw 4 q27 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 1 q16 ∷
   rw 5 q1 ∷
   rw 4 q28 ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q26 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q26 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q3 ∷
   rw 6 q26 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q3 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 4 q27 ∷
   re 4 5 (ℓ "乙") ∷
   rw 2 q28 ∷
   rw 3 q29 ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 2 q1 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   rw 3 q27 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q26 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q26 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   rw 3 q27 ∷
   re 3 5 (ℓ "乙") ∷
   rw 4 q3 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 1 q30 ∷
   rw 4 q15 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q31 ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q20 ∷
   rw⁻ 7 q21 ∷
   rw 8 q22 ∷
   re 5 5 (ℓ "中") ∷
   rw 1 q5 ∷
   rw 2 q11 ∷
   rw 3 q12 ∷
   rw 4 q10 ∷
   rw 5 q12 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q13 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q14 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q32 ∷
   rw 5 q15 ∷
   re 3 3 (ℓ "个") ∷
   rw 4 q33 ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "个") ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 6 q23 ∷
   rw 2 q34 ∷
   re 2 5 (ℓ "乙") ∷
   rw 3 q23 ∷
   re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q11 ∷
   rw 2 q17 ∷
   rw 3 q10 ∷
   rw 4 q17 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q18 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q19 ∷
   rw 0 q11 ∷
   rw 1 q12 ∷
   rw 2 q10 ∷
   rw 3 q12 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q6 ∷
   rw 5 q13 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "丽") ∷
   rw 0 q14 ∷
   re 0 5 (ℓ "乜") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 1 q18 ∷
   rw 2 q35 ∷
   rw 3 q36 ∷
   rw 4 q35 ∷
   rw 5 q13 ∷
   rw 1 q37 ∷
   re 1 5 (ℓ "乙") ∷
   rw 2 q19 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 254 W

-- pass [CCZ013] [CSd03]: 49 steps
lem-pass-CCZ013-vs-CSd03 : ⟪ (ℓ "乚丮") ⟫ʷ ≈ ⟪ (ℓ "丮乚") ⟫ʷ
lem-pass-CCZ013-vs-CSd03 = derive (ℓ "乚丮") (ℓ "丮乚")
  (rw 2 q1 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q3 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q26 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q26 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q3 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q3 ∷
   rw 3 q26 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q3 ∷
   rw 1 q26 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw 1 q27 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q40 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丮") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q26 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q26 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw⁻ 3 q26 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q3 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q3 ∷
   rw 2 q27 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q3 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 233 W

-- pass [X2 CS20 X2] [TOFF012]: 1 steps
lem-pass-X2-CS20-X2-vs-TOFF012 : ⟪ (ℓ "丘丧丘九") ⟫ʷ ≈ ⟪ (ℓ "九丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-TOFF012 = derive (ℓ "丘丧丘九") (ℓ "九丘丧丘")
  (rw 0 q41 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = wE 7 W
  q43 : Eqn
  q43 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q44 : Eqn
  q44 = wE 255 W

-- pass [X2 CS20 X2] [CS03]: 19 steps
lem-pass-X2-CS20-X2-vs-CS03 : ⟪ (ℓ "丘丧丘中") ⟫ʷ ≈ ⟪ (ℓ "中丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-CS03 = derive (ℓ "丘丧丘中") (ℓ "中丘丧丘")
  (rw 4 q5 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q42 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 2 q43 ∷
   rw 1 q42 ∷
   rw⁻ 0 q43 ∷
   rw 1 q44 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q6 ∷
   rw 1 q18 ∷
   rw 2 q6 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q43 ∷
   rw 2 q18 ∷
   rw 3 q43 ∷
   rw 4 q19 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 76 W
  q46 : Eqn
  q46 = wE 256 W

-- pass [X2 CS20 X2] [CSd03]: 19 steps
lem-pass-X2-CS20-X2-vs-CSd03 : ⟪ (ℓ "丘丧丘丮") ⟫ʷ ≈ ⟪ (ℓ "丮丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-CSd03 = derive (ℓ "丘丧丘丮") (ℓ "丮丘丧丘")
  (rw 4 q5 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q45 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 2 q43 ∷
   rw 1 q42 ∷
   rw⁻ 0 q43 ∷
   rw 1 q46 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q6 ∷
   rw 1 q36 ∷
   rw 2 q6 ∷
   re 0 3 (ℓ "丮") ∷
   rw 1 q43 ∷
   rw 2 q18 ∷
   rw 3 q43 ∷
   rw 4 q19 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 241 W

-- pass [X2 CS20 X2] [TOFF102]: 1 steps
lem-pass-X2-CS20-X2-vs-TOFF102 : ⟪ (ℓ "丘丧丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-TOFF102 = derive (ℓ "丘丧丘习") (ℓ "习丘丧丘")
  (rw 0 q47 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 257 W
  q49 : Eqn
  q49 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q50 : Eqn
  q50 = wE 49 W

-- pass [X2 CS20 X2] [CS13]: 17 steps
lem-pass-X2-CS20-X2-vs-CS13 : ⟪ (ℓ "丘丧丘丽") ⟫ʷ ≈ ⟪ (ℓ "丽丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-CS13 = derive (ℓ "丘丧丘丽") (ℓ "丽丘丧丘")
  (rw 2 q48 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "中") ∷
   re 2 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 5 q30 ∷
   rw 4 q49 ∷
   rw 3 q50 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   re 3 5 (ℓ "中") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 0 q48 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = wE 258 W
  q52 : Eqn
  q52 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q53 : Eqn
  q53 = wE 51 W

-- pass [X2 CS20 X2] [CSd13]: 17 steps
lem-pass-X2-CS20-X2-vs-CSd13 : ⟪ (ℓ "丘丧丘举") ⟫ʷ ≈ ⟪ (ℓ "举丘丧丘") ⟫ʷ
lem-pass-X2-CS20-X2-vs-CSd13 = derive (ℓ "丘丧丘举") (ℓ "举丘丧丘")
  (rw 2 q51 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "中") ∷
   re 2 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw 5 q31 ∷
   rw 4 q52 ∷
   rw 3 q53 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q3 ∷
   re 3 5 (ℓ "中") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   re 1 3 (ℓ "举") ∷
   rw 0 q51 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 240 W

-- pass [X2 CK20 X2] [TOFF102]: 1 steps
lem-pass-X2-CK20-X2-vs-TOFF102 : ⟪ (ℓ "丘乄丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-TOFF102 = derive (ℓ "丘乄丘习") (ℓ "习丘乄丘")
  (rw 0 q54 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))

-- pass [X2 CK20 X2] [CS13]: 17 steps
lem-pass-X2-CK20-X2-vs-CS13 : ⟪ (ℓ "丘乄丘丽") ⟫ʷ ≈ ⟪ (ℓ "丽丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-CS13 = derive (ℓ "丘乄丘丽") (ℓ "丽丘乄丘")
  (rw 2 q48 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "乑") ∷
   re 2 1 (ℓ "乏丼临丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 5 q30 ∷
   rw 4 q55 ∷
   rw 3 q50 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   re 3 5 (ℓ "乑") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 0 q48 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))

-- pass [X2 CK20 X2] [CSd13]: 17 steps
lem-pass-X2-CK20-X2-vs-CSd13 : ⟪ (ℓ "丘乄丘举") ⟫ʷ ≈ ⟪ (ℓ "举丘乄丘") ⟫ʷ
lem-pass-X2-CK20-X2-vs-CSd13 = derive (ℓ "丘乄丘举") (ℓ "举丘乄丘")
  (rw 2 q51 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "乑") ∷
   re 2 1 (ℓ "乏丼临丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw 5 q31 ∷
   rw 4 q56 ∷
   rw 3 q53 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q3 ∷
   re 3 5 (ℓ "乑") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q3 ∷
   re 1 3 (ℓ "举") ∷
   rw 0 q51 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 239 W

-- pass [X2 CKd20 X2] [TOFF102]: 1 steps
lem-pass-X2-CKd20-X2-vs-TOFF102 : ⟪ (ℓ "丘久丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-TOFF102 = derive (ℓ "丘久丘习") (ℓ "习丘久丘")
  (rw 0 q57 ∷ []) Eq.refl

private
  q58 : Eqn
  q58 = eqn (ℓ "丵义") (ℓ "义丵") (low-comm ((S ↑ • CK₁₀)) (CS))

-- pass [X2 CKd20 X2] [CS13]: 17 steps
lem-pass-X2-CKd20-X2-vs-CS13 : ⟪ (ℓ "丘久丘丽") ⟫ʷ ≈ ⟪ (ℓ "丽丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-CS13 = derive (ℓ "丘久丘丽") (ℓ "丽丘久丘")
  (rw 2 q48 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "乒") ∷
   re 2 1 (ℓ "乏丼丵丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 5 q30 ∷
   rw 4 q58 ∷
   rw 3 q50 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   re 3 5 (ℓ "乒") ∷
   re 3 1 (ℓ "乏久乏") ∷
   rw 5 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 0 q48 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = eqn (ℓ "丵乊") (ℓ "乊丵") (low-comm ((S ↑ • CK₁₀)) ((CS • CS • CS)))

-- pass [X2 CKd20 X2] [CSd13]: 17 steps
lem-pass-X2-CKd20-X2-vs-CSd13 : ⟪ (ℓ "丘久丘举") ⟫ʷ ≈ ⟪ (ℓ "举丘久丘") ⟫ʷ
lem-pass-X2-CKd20-X2-vs-CSd13 = derive (ℓ "丘久丘举") (ℓ "举丘久丘")
  (rw 2 q51 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "乒") ∷
   re 2 1 (ℓ "乏丼丵丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw 5 q31 ∷
   rw 4 q59 ∷
   rw 3 q53 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q3 ∷
   re 3 5 (ℓ "乒") ∷
   re 3 1 (ℓ "乏久乏") ∷
   rw 5 q3 ∷
   re 1 3 (ℓ "举") ∷
   rw 0 q51 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = wE 238 W

-- pass [X2 CSd20 X2] [TOFF102]: 1 steps
lem-pass-X2-CSd20-X2-vs-TOFF102 : ⟪ (ℓ "丘丨丘习") ⟫ʷ ≈ ⟪ (ℓ "习丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-TOFF102 = derive (ℓ "丘丨丘习") (ℓ "习丘丨丘")
  (rw 0 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))

-- pass [X2 CSd20 X2] [CS13]: 17 steps
lem-pass-X2-CSd20-X2-vs-CS13 : ⟪ (ℓ "丘丨丘丽") ⟫ʷ ≈ ⟪ (ℓ "丽丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CS13 = derive (ℓ "丘丨丘丽") (ℓ "丽丘丨丘")
  (rw 2 q48 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "丮") ∷
   re 2 1 (ℓ "乏丼両丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 5 q30 ∷
   rw 4 q61 ∷
   rw 3 q50 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   re 3 5 (ℓ "丮") ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 0 q48 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))

-- pass [X2 CSd20 X2] [CSd13]: 17 steps
lem-pass-X2-CSd20-X2-vs-CSd13 : ⟪ (ℓ "丘丨丘举") ⟫ʷ ≈ ⟪ (ℓ "举丘丨丘") ⟫ʷ
lem-pass-X2-CSd20-X2-vs-CSd13 = derive (ℓ "丘丨丘举") (ℓ "举丘丨丘")
  (rw 2 q51 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "丮") ∷
   re 2 1 (ℓ "乏丼両丼乏") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw 5 q31 ∷
   rw 4 q62 ∷
   rw 3 q53 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q3 ∷
   re 3 5 (ℓ "丮") ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q3 ∷
   re 1 3 (ℓ "举") ∷
   rw 0 q51 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 259 W

-- pass [CCZ123] [CS13]: 1 steps
lem-pass-CCZ123-vs-CS13 : ⟪ (ℓ "乜丽") ⟫ʷ ≈ ⟪ (ℓ "丽乜") ⟫ʷ
lem-pass-CCZ123-vs-CS13 = derive (ℓ "乜丽") (ℓ "丽乜")
  (rw 0 q63 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 260 W

-- pass [CCZ123] [CSd13]: 1 steps
lem-pass-CCZ123-vs-CSd13 : ⟪ (ℓ "乜举") ⟫ʷ ≈ ⟪ (ℓ "举乜") ⟫ʷ
lem-pass-CCZ123-vs-CSd13 = derive (ℓ "乜举") (ℓ "举乜")
  (rw 0 q64 ∷ []) Eq.refl
