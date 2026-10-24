{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D022 (W : Ws) where

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
  q1 = wE 252 W
  q2 : Eqn
  q2 = wE 70 W
  q3 : Eqn
  q3 = wE 5 W
  q4 : Eqn
  q4 = wE 74 W
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 10 W
  q7 : Eqn
  q7 = wE 253 W
  q8 : Eqn
  q8 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q9 : Eqn
  q9 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q10 : Eqn
  q10 = wE 24 W
  q11 : Eqn
  q11 = wE 25 W
  q12 : Eqn
  q12 = wE 26 W
  q13 : Eqn
  q13 = wE 12 W
  q14 : Eqn
  q14 = wE 414 W
  q15 : Eqn
  q15 = wE 30 W
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = wE 22 W
  q19 : Eqn
  q19 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = wE 23 W
  q21 : Eqn
  q21 = wE 14 W
  q22 : Eqn
  q22 = wE 47 W
  q23 : Eqn
  q23 = wE 48 W
  q24 : Eqn
  q24 = wE 1 W
  q25 : Eqn
  q25 = wE 3 W
  q26 : Eqn
  q26 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q27 : Eqn
  q27 = wE 43 W
  q28 : Eqn
  q28 = wE 13 W
  q29 : Eqn
  q29 = wE 15 W
  q30 : Eqn
  q30 = wE 16 W
  q31 : Eqn
  q31 = wE 17 W
  q32 : Eqn
  q32 = eqn (ℓ "乖乙乖") (ℓ "乙乚") (ax cx-ccz)
  q33 : Eqn
  q33 = wE 18 W
  q34 : Eqn
  q34 = wE 19 W
  q35 : Eqn
  q35 = wE 20 W
  q36 : Eqn
  q36 = wE 21 W
  q37 : Eqn
  q37 = wE 71 W
  q38 : Eqn
  q38 = wE 72 W
  q39 : Eqn
  q39 = wE 73 W
  q40 : Eqn
  q40 = wE 49 W
  q41 : Eqn
  q41 = wE 51 W
  q42 : Eqn
  q42 = wE 28 W
  q43 : Eqn
  q43 = wE 29 W
  q44 : Eqn
  q44 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q45 : Eqn
  q45 = wE 11 W
  q46 : Eqn
  q46 = wE 33 W
  q47 : Eqn
  q47 = wE 32 W

-- comm CCZ013 CCZ123: 741 steps
lem-comm-CCZ013-CCZ123 : ⟪ (ℓ "乚乜") ⟫ʷ ≈ ⟪ (ℓ "乜乚") ⟫ʷ
lem-comm-CCZ013-CCZ123 = derive (ℓ "乚乜") (ℓ "乜乚")
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q1 ∷
   rw 5 q3 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw⁻ 9 q5 ∷
   rw 8 q6 ∷
   rw⁻ 7 q5 ∷
   re 8 3 (ℓ "中") ∷
   rw 6 q7 ∷
   rw⁻ 5 q8 ∷
   rw 4 q7 ∷
   rw⁻ 3 q9 ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q8 ∷
   rw 8 q10 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw 10 q11 ∷
   rw 11 q5 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q12 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   rw 2 q4 ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q9 ∷
   rw 5 q15 ∷
   rw 6 q8 ∷
   rw 7 q15 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw 9 q16 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q17 ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q18 ∷
   rw 10 q19 ∷
   rw 8 q20 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "丼丣丼") ∷
   rw 9 q21 ∷
   rw 6 q22 ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 7 q21 ∷
   rw 4 q23 ∷
   rw 5 q24 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q25 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q25 ∷
   rw⁻ 9 q26 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 10 q25 ∷
   rw 6 q27 ∷
   re 6 5 (ℓ "乙") ∷
   re 5 3 (ℓ "乚") ∷
   rw 3 q14 ∷
   rw 7 q24 ∷
   rw 6 q24 ∷
   re 7 3 (ℓ "乓") ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q26 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q26 ∷
   rw 11 q24 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q25 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q25 ∷
   rw 8 q26 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q25 ∷
   rw 6 q26 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q25 ∷
   rw 6 q27 ∷
   re 6 5 (ℓ "乙") ∷
   rw 4 q24 ∷
   re 5 3 (ℓ "乓") ∷
   rw 8 q13 ∷
   rw 7 q28 ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 12 q21 ∷
   rw 9 q13 ∷
   re 10 3 (ℓ "个") ∷
   rw 8 q29 ∷
   rw 7 q13 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q30 ∷
   rw 7 q31 ∷
   re 7 5 (ℓ "乙") ∷
   rw 5 q28 ∷
   rw 6 q32 ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q33 ∷
   rw 8 q13 ∷
   re 6 3 (ℓ "个") ∷
   rw 7 q34 ∷
   rw 10 q13 ∷
   re 8 3 (ℓ "个") ∷
   re 10 1 (ℓ "丼丠丼") ∷
   rw 9 q21 ∷
   rw 5 q31 ∷
   re 5 5 (ℓ "乙") ∷
   re 7 1 (ℓ "乏乙乏") ∷
   re 8 1 (ℓ "丶丣丷丣丧") ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "丽") ∷
   rw⁻ 8 q26 ∷
   rw 11 q24 ∷
   re 9 3 (ℓ "举") ∷
   rw⁻ 10 q26 ∷
   rw 13 q24 ∷
   re 11 3 (ℓ "中") ∷
   rw 12 q25 ∷
   rw 6 q35 ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "个") ∷
   rw 8 q36 ∷
   rw 11 q13 ∷
   re 9 3 (ℓ "个") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q18 ∷
   rw⁻ 12 q19 ∷
   rw 13 q20 ∷
   re 10 5 (ℓ "中") ∷
   rw 6 q3 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 9 q8 ∷
   rw 10 q10 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw 12 q11 ∷
   rw 13 q5 ∷
   re 11 3 (ℓ "丽") ∷
   rw 7 q12 ∷
   re 7 5 (ℓ "乜") ∷
   re 6 3 (ℓ "乛") ∷
   rw 7 q21 ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q26 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q24 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q25 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q25 ∷
   rw⁻ 8 q26 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q25 ∷
   rw 5 q27 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   re 6 1 (ℓ "並乜並") ∷
   re 7 1 (ℓ "义丹乊丹丽") ∷
   rw 6 q9 ∷
   rw 7 q15 ∷
   rw 8 q8 ∷
   rw 9 q15 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q5 ∷
   rw 11 q16 ∷
   rw 12 q5 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q17 ∷
   rw 5 q37 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "丰") ∷
   rw 7 q38 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "丰") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q25 ∷
   rw 5 q3 ∷
   rw 6 q9 ∷
   re 8 1 (ℓ "乏个乏") ∷
   rw 7 q5 ∷
   rw 8 q10 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "乀") ∷
   rw 8 q8 ∷
   re 10 1 (ℓ "乏个乏") ∷
   rw 9 q5 ∷
   rw 10 q10 ∷
   rw 11 q5 ∷
   re 9 3 (ℓ "乀") ∷
   rw 10 q11 ∷
   rw 6 q39 ∷
   re 6 5 (ℓ "乜") ∷
   re 5 3 (ℓ "乛") ∷
   rw 6 q25 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q26 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q25 ∷
   rw 3 q35 ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q36 ∷
   rw 8 q13 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q18 ∷
   rw⁻ 9 q19 ∷
   rw 10 q20 ∷
   re 7 5 (ℓ "中") ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q8 ∷
   rw 7 q10 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw 9 q11 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q12 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   re 5 1 (ℓ "並乜並") ∷
   re 6 1 (ℓ "义丹乊丹丽") ∷
   rw 5 q9 ∷
   rw 6 q15 ∷
   rw 7 q8 ∷
   rw 8 q15 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q5 ∷
   rw 10 q16 ∷
   rw 11 q5 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q17 ∷
   rw 4 q40 ∷
   re 6 1 (ℓ "丼丣丼") ∷
   rw 5 q21 ∷
   rw 6 q41 ∷
   re 8 1 (ℓ "丼丣丼") ∷
   rw 7 q21 ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q18 ∷
   rw⁻ 10 q19 ∷
   rw 11 q20 ∷
   re 8 5 (ℓ "中") ∷
   rw 4 q24 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q25 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q25 ∷
   rw⁻ 8 q26 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q25 ∷
   rw 5 q27 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 5 q21 ∷
   re 3 1 (ℓ "並乜並") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q9 ∷
   rw 4 q15 ∷
   rw 5 q8 ∷
   rw 6 q15 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 8 q16 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q17 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q10 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q12 ∷
   re 2 5 (ℓ "乜") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q26 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q25 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw 4 q16 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q42 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw 6 q43 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丮") ∷
   rw 6 q42 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 8 q11 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q24 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q25 ∷
   rw⁻ 5 q44 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 6 q25 ∷
   rw⁻ 7 q44 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q25 ∷
   rw 4 q45 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 4 q17 ∷
   rw 1 q46 ∷
   rw 2 q24 ∷
   re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q24 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q26 ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q25 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q25 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q25 ∷
   rw 2 q26 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q25 ∷
   rw 2 q27 ∷
   re 2 5 (ℓ "乙") ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q24 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q26 ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q25 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q25 ∷
   rw 3 q26 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q25 ∷
   rw 1 q26 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q25 ∷
   rw 1 q27 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q47 ∷
   rw 0 q25 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw⁻ 7 q5 ∷
   rw 6 q6 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 4 q7 ∷
   rw⁻ 3 q8 ∷
   rw 2 q7 ∷
   rw⁻ 1 q9 ∷
   rw 2 q3 ∷
   rw 3 q9 ∷
   rw 4 q10 ∷
   rw 5 q8 ∷
   rw 6 q10 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 8 q11 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q12 ∷
   re 3 5 (ℓ "乜") ∷
   re 2 3 (ℓ "乛") ∷
   rw 0 q4 ∷
   rw 4 q13 ∷
   rw 3 q14 ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q9 ∷
   rw 3 q15 ∷
   rw 4 q8 ∷
   rw 5 q15 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q16 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q17 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q18 ∷
   rw 8 q19 ∷
   rw 6 q20 ∷
   re 7 5 (ℓ "中") ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 7 q21 ∷
   rw 4 q22 ∷
   re 3 1 (ℓ "丼丣丼") ∷
   rw 5 q21 ∷
   rw 2 q23 ∷
   rw 3 q24 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q25 ∷
   rw⁻ 5 q26 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q25 ∷
   rw⁻ 7 q26 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q25 ∷
   rw 4 q27 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   rw 1 q14 ∷
   rw 5 q24 ∷
   rw 4 q24 ∷
   re 5 3 (ℓ "乓") ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q26 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q26 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q25 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q25 ∷
   rw 6 q26 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q25 ∷
   rw 4 q26 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q25 ∷
   rw 4 q27 ∷
   re 4 5 (ℓ "乙") ∷
   rw 2 q24 ∷
   re 3 3 (ℓ "乓") ∷
   rw 6 q13 ∷
   rw 5 q28 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q21 ∷
   rw 7 q13 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q29 ∷
   rw 5 q13 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q30 ∷
   rw 5 q31 ∷
   re 5 5 (ℓ "乙") ∷
   rw 3 q28 ∷
   rw 4 q32 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q33 ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q34 ∷
   rw 8 q13 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q21 ∷
   rw 3 q31 ∷
   re 3 5 (ℓ "乙") ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q26 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q26 ∷
   rw 11 q24 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q25 ∷
   rw 4 q35 ∷
   rw 7 q13 ∷
   re 5 3 (ℓ "个") ∷
   rw 6 q36 ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "个") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q18 ∷
   rw⁻ 10 q19 ∷
   rw 11 q20 ∷
   re 8 5 (ℓ "中") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q10 ∷
   rw 7 q8 ∷
   rw 8 q10 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw 10 q11 ∷
   rw 11 q5 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q12 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   rw 5 q21 ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw 2 q24 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q25 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q25 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q25 ∷
   rw 3 q27 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q9 ∷
   rw 5 q15 ∷
   rw 6 q8 ∷
   rw 7 q15 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q5 ∷
   rw 9 q16 ∷
   rw 10 q5 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q17 ∷
   rw 3 q37 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "丰") ∷
   rw 5 q38 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "丰") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q25 ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   re 6 1 (ℓ "乏个乏") ∷
   rw 5 q5 ∷
   rw 6 q10 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "乀") ∷
   rw 6 q8 ∷
   re 8 1 (ℓ "乏个乏") ∷
   rw 7 q5 ∷
   rw 8 q10 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "乀") ∷
   rw 8 q11 ∷
   rw 4 q39 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   rw 4 q25 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q25 ∷
   rw 1 q35 ∷
   rw 4 q13 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q36 ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q18 ∷
   rw⁻ 7 q19 ∷
   rw 8 q20 ∷
   re 5 5 (ℓ "中") ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q10 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q11 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q12 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   re 3 1 (ℓ "並乜並") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q9 ∷
   rw 4 q15 ∷
   rw 5 q8 ∷
   rw 6 q15 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw 8 q16 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q17 ∷
   rw 2 q40 ∷
   re 4 1 (ℓ "丼丣丼") ∷
   rw 3 q21 ∷
   rw 4 q41 ∷
   re 6 1 (ℓ "丼丣丼") ∷
   rw 5 q21 ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q18 ∷
   rw⁻ 8 q19 ∷
   rw 9 q20 ∷
   re 6 5 (ℓ "中") ∷
   rw 2 q24 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q25 ∷
   rw⁻ 4 q26 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q25 ∷
   rw⁻ 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q25 ∷
   rw 3 q27 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   rw 3 q21 ∷
   re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q9 ∷
   rw 2 q15 ∷
   rw 3 q8 ∷
   rw 4 q15 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q16 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q17 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q8 ∷
   rw 3 q10 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   rw 5 q11 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "丽") ∷
   rw 0 q12 ∷
   re 0 5 (ℓ "乜") ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q24 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q26 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q26 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q25 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   rw 2 q16 ∷
   rw 3 q5 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q42 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw 4 q43 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q42 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q5 ∷
   rw 6 q11 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 1 q24 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 2 q25 ∷
   rw⁻ 3 q44 ∷
   re 5 1 (ℓ "乏丨乏") ∷
   rw 4 q25 ∷
   rw⁻ 5 q44 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q25 ∷
   rw 2 q45 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q17 ∷ []) Eq.refl

private
  q48 : Eqn
  q48 = wE 415 W

-- pass [CS02] [CZ01]: 1 steps
lem-pass-CS02-vs-CZ01 : ⟪ (ℓ "丧丢") ⟫ʷ ≈ ⟪ (ℓ "丢丧") ⟫ʷ
lem-pass-CS02-vs-CZ01 = derive (ℓ "丧丢") (ℓ "丢丧")
  (rw 0 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 7 W
  q50 : Eqn
  q50 = wE 416 W

-- pass [CS02] [CSd23]: 7 steps
lem-pass-CS02-vs-CSd23 : ⟪ (ℓ "丧乊") ⟫ʷ ≈ ⟪ (ℓ "乊丧") ⟫ʷ
lem-pass-CS02-vs-CSd23 = derive (ℓ "丧乊") (ℓ "乊丧")
  (rw 2 q3 ∷
   rw⁻ 1 q8 ∷
   rw 0 q49 ∷
   rw 1 q50 ∷
   rw 0 q8 ∷
   rw 1 q16 ∷
   rw 2 q17 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = wE 417 W

-- pass [CSd02] [CZ01]: 1 steps
lem-pass-CSd02-vs-CZ01 : ⟪ (ℓ "丨丢") ⟫ʷ ≈ ⟪ (ℓ "丢丨") ⟫ʷ
lem-pass-CSd02-vs-CZ01 = derive (ℓ "丨丢") (ℓ "丢丨")
  (rw 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = wE 76 W
  q53 : Eqn
  q53 = wE 418 W

-- pass [CSd02] [CSd23]: 7 steps
lem-pass-CSd02-vs-CSd23 : ⟪ (ℓ "丨乊") ⟫ʷ ≈ ⟪ (ℓ "乊丨") ⟫ʷ
lem-pass-CSd02-vs-CSd23 = derive (ℓ "丨乊") (ℓ "乊丨")
  (rw 2 q3 ∷
   rw⁻ 1 q8 ∷
   rw 0 q52 ∷
   rw 1 q53 ∷
   rw 0 q8 ∷
   rw 1 q43 ∷
   rw 2 q17 ∷ []) Eq.refl
