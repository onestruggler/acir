{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D005 (W : Ws) where

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
  q1 = wE 111 W
  q2 : Eqn
  q2 = wE 4 W
  q3 : Eqn
  q3 = wE 12 W
  q4 : Eqn
  q4 = wE 13 W
  q5 : Eqn
  q5 = wE 14 W
  q6 : Eqn
  q6 = wE 15 W
  q7 : Eqn
  q7 = wE 16 W
  q8 : Eqn
  q8 = wE 17 W
  q9 : Eqn
  q9 = eqn (ℓ "乖乙乖") (ℓ "乙乚") (ax cx-ccz)
  q10 : Eqn
  q10 = wE 18 W
  q11 : Eqn
  q11 = wE 19 W
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q14 : Eqn
  q14 = wE 3 W
  q15 : Eqn
  q15 = wE 20 W
  q16 : Eqn
  q16 = wE 21 W
  q17 : Eqn
  q17 = wE 22 W
  q18 : Eqn
  q18 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q19 : Eqn
  q19 = wE 23 W
  q20 : Eqn
  q20 = wE 5 W
  q21 : Eqn
  q21 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q22 : Eqn
  q22 = wE 24 W
  q23 : Eqn
  q23 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q24 : Eqn
  q24 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q25 : Eqn
  q25 = wE 25 W
  q26 : Eqn
  q26 = wE 26 W
  q27 : Eqn
  q27 = wE 32 W
  q28 : Eqn
  q28 = wE 30 W
  q29 : Eqn
  q29 = wE 27 W
  q30 : Eqn
  q30 = wE 31 W
  q31 : Eqn
  q31 = wE 7 W
  q32 : Eqn
  q32 = wE 74 W
  q33 : Eqn
  q33 = wE 33 W

-- comm CCZ023 CCZ012: 177 steps
lem-comm-CCZ023-CCZ012 : ⟪ (ℓ "乛乙") ⟫ʷ ≈ ⟪ (ℓ "乙乛") ⟫ʷ
lem-comm-CCZ023-CCZ012 = derive (ℓ "乛乙") (ℓ "乙乛")
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q1 ∷
   rw 5 q3 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 9 q5 ∷
   rw 6 q3 ∷
   re 7 3 (ℓ "个") ∷
   rw 5 q6 ∷
   rw 4 q3 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q7 ∷
   rw 4 q8 ∷
   re 4 5 (ℓ "乙") ∷
   rw 2 q4 ∷
   rw 3 q9 ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q10 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "个") ∷
   rw 4 q11 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "个") ∷
   re 7 1 (ℓ "丼丠丼") ∷
   rw 6 q5 ∷
   rw 2 q8 ∷
   re 2 5 (ℓ "乙") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q13 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q13 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q14 ∷
   rw 3 q15 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q16 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q17 ∷
   rw⁻ 9 q18 ∷
   rw 10 q19 ∷
   re 7 5 (ℓ "中") ∷
   rw 3 q20 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   rw 6 q23 ∷
   rw 7 q22 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q24 ∷
   rw 9 q25 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q26 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   rw 4 q5 ∷
   rw 1 q27 ∷
   rw 2 q20 ∷
   re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q21 ∷
   rw 2 q28 ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q24 ∷
   rw 6 q29 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q30 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q24 ∷
   rw 6 q31 ∷
   rw⁻ 5 q24 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q32 ∷
   rw⁻ 3 q23 ∷
   rw 2 q32 ∷
   rw⁻ 1 q21 ∷
   rw 2 q26 ∷
   re 2 5 (ℓ "乜") ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q21 ∷
   rw 1 q28 ∷
   rw 2 q23 ∷
   rw 3 q28 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q24 ∷
   rw 5 q29 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q30 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q24 ∷
   rw 5 q31 ∷
   rw⁻ 4 q24 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q32 ∷
   rw⁻ 2 q23 ∷
   rw 1 q32 ∷
   rw⁻ 0 q21 ∷
   rw 1 q26 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q33 ∷
   rw 0 q30 ∷
   rw 3 q3 ∷
   rw 2 q4 ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 7 q5 ∷
   rw 4 q3 ∷
   re 5 3 (ℓ "个") ∷
   rw 3 q6 ∷
   rw 2 q3 ∷
   re 3 3 (ℓ "个") ∷
   rw 1 q7 ∷
   rw 2 q8 ∷
   re 2 5 (ℓ "乙") ∷
   rw 0 q4 ∷
   rw 1 q9 ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 0 q10 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "个") ∷
   rw 2 q11 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "个") ∷
   re 5 1 (ℓ "丼丠丼") ∷
   rw 4 q5 ∷
   rw 0 q8 ∷
   re 0 5 (ℓ "乙") ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q12 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q13 ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q13 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q14 ∷
   rw 1 q15 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q16 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q17 ∷
   rw⁻ 7 q18 ∷
   rw 8 q19 ∷
   re 5 5 (ℓ "中") ∷
   rw 1 q20 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   rw 5 q22 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q24 ∷
   rw 7 q25 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q26 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 75 W
  q35 : Eqn
  q35 = wE 39 W
  q36 : Eqn
  q36 = wE 29 W
  q37 : Eqn
  q37 = wE 40 W
  q38 : Eqn
  q38 = wE 112 W
  q39 : Eqn
  q39 = wE 113 W
  q40 : Eqn
  q40 = eqn (ℓ "両乖") (ℓ "乖両") (low-comm ((CS • CS • CS)) (CX₁₀))
  q41 : Eqn
  q41 = wE 114 W
  q42 : Eqn
  q42 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q43 : Eqn
  q43 = wE 6 W
  q44 : Eqn
  q44 = wE 76 W
  q45 : Eqn
  q45 = wE 81 W

-- CCZ023 passes CX31: 131 steps
lem-CCZ023-passes-CX31 : ⟪ (ℓ "乛乓") ⟫ʷ ≈ ⟪ (ℓ "乓乛") ⟫ʷ
lem-CCZ023-passes-CX31 = derive (ℓ "乛乓") (ℓ "乓乛")
  (rw 1 q20 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q21 ∷
   rw 1 q28 ∷
   rw 2 q23 ∷
   rw 3 q28 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q24 ∷
   rw 5 q29 ∷
   rw 6 q24 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q30 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q24 ∷
   rw 5 q31 ∷
   rw⁻ 4 q24 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q32 ∷
   rw⁻ 2 q23 ∷
   rw 1 q32 ∷
   rw⁻ 0 q21 ∷
   rw 1 q26 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q34 ∷
   rw 0 q29 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 1 q24 ∷
   rw 2 q35 ∷
   rw 3 q24 ∷
   re 1 3 (ℓ "乐") ∷
   rw 2 q36 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 3 q24 ∷
   rw 4 q35 ∷
   rw 5 q24 ∷
   re 3 3 (ℓ "乐") ∷
   rw 4 q21 ∷
   rw 5 q30 ∷
   rw 4 q37 ∷
   rw 5 q12 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 6 q14 ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw 5 q14 ∷
   rw 4 q38 ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "乓") ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "乐") ∷
   rw 5 q14 ∷
   re 3 1 (ℓ "乏乆乏") ∷
   rw 2 q12 ∷
   re 3 3 (ℓ "丮") ∷
   re 3 1 (ℓ "乏丼両丼乏") ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "乓") ∷
   rw 6 q39 ∷
   rw 5 q40 ∷
   rw 4 q41 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 3 q14 ∷
   re 4 5 (ℓ "丮") ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q14 ∷
   re 2 3 (ℓ "乓") ∷
   rw 3 q12 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 4 q14 ∷
   re 1 1 (ℓ "乏乃乏") ∷
   rw 3 q14 ∷
   rw 2 q38 ∷
   rw 3 q12 ∷
   re 1 3 (ℓ "乓") ∷
   rw 4 q12 ∷
   re 2 3 (ℓ "乐") ∷
   rw 3 q14 ∷
   re 1 1 (ℓ "乏乆乏") ∷
   rw 0 q12 ∷
   re 1 3 (ℓ "中") ∷
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "乓") ∷
   rw 4 q39 ∷
   rw 3 q42 ∷
   rw 2 q41 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 1 q14 ∷
   re 2 5 (ℓ "中") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q14 ∷
   re 0 3 (ℓ "乓") ∷
   rw 6 q20 ∷
   rw⁻ 5 q21 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q24 ∷
   rw 5 q43 ∷
   rw⁻ 4 q24 ∷
   re 5 3 (ℓ "乓") ∷
   rw 3 q44 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw⁻ 4 q24 ∷
   rw 3 q43 ∷
   rw⁻ 2 q24 ∷
   re 3 3 (ℓ "乓") ∷
   rw 1 q31 ∷
   rw 2 q45 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q21 ∷
   rw 2 q28 ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q24 ∷
   rw 6 q29 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q20 ∷
   rw 2 q21 ∷
   rw 3 q22 ∷
   rw 4 q23 ∷
   rw 5 q22 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q24 ∷
   rw 7 q25 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q26 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q30 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = wE 115 W
  q47 : Eqn
  q47 = wE 70 W
  q48 : Eqn
  q48 = wE 36 W
  q49 : Eqn
  q49 = wE 47 W
  q50 : Eqn
  q50 = wE 48 W
  q51 : Eqn
  q51 = wE 43 W
  q52 : Eqn
  q52 = wE 44 W

-- comm CCZ012 CCZ023: 407 steps
lem-comm-CCZ012-CCZ023 : ⟪ (ℓ "乙乛") ⟫ʷ ≈ ⟪ (ℓ "乛乙") ⟫ʷ
lem-comm-CCZ012-CCZ023 = derive (ℓ "乙乛") (ℓ "乛乙")
  (rw 2 q46 ∷
   rw 3 q20 ∷
   rw 4 q47 ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q21 ∷
   rw 4 q28 ∷
   rw 5 q23 ∷
   rw 6 q28 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q24 ∷
   rw 8 q29 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q20 ∷
   rw 4 q21 ∷
   rw 5 q22 ∷
   rw 6 q23 ∷
   rw 7 q22 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q24 ∷
   rw 9 q25 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "丽") ∷
   rw 4 q26 ∷
   re 4 5 (ℓ "乜") ∷
   re 3 3 (ℓ "乛") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q21 ∷
   rw 5 q28 ∷
   rw 6 q23 ∷
   rw 7 q28 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q24 ∷
   rw 9 q29 ∷
   rw 10 q24 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q20 ∷
   rw 5 q21 ∷
   rw 6 q22 ∷
   rw 7 q23 ∷
   rw 8 q22 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q24 ∷
   rw 10 q25 ∷
   rw 11 q24 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q26 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   rw 5 q30 ∷
   rw 4 q46 ∷
   rw 5 q3 ∷
   rw 4 q48 ∷
   re 3 1 (ℓ "並乜並") ∷
   re 4 1 (ℓ "义丹乊丹丽") ∷
   rw 3 q21 ∷
   rw 4 q28 ∷
   rw 5 q23 ∷
   rw 6 q28 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q24 ∷
   rw 8 q29 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q30 ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q17 ∷
   rw 9 q18 ∷
   rw 7 q19 ∷
   re 8 5 (ℓ "中") ∷
   re 6 1 (ℓ "丼丣丼") ∷
   rw 8 q5 ∷
   rw 5 q49 ∷
   re 4 1 (ℓ "丼丣丼") ∷
   rw 6 q5 ∷
   rw 3 q50 ∷
   rw 4 q12 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q14 ∷
   rw⁻ 6 q13 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q14 ∷
   rw⁻ 8 q13 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q14 ∷
   rw 5 q51 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 2 q48 ∷
   rw 6 q12 ∷
   rw 5 q52 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q13 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q13 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q14 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q14 ∷
   rw 7 q13 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q14 ∷
   rw 5 q13 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q14 ∷
   rw 5 q51 ∷
   re 5 5 (ℓ "乙") ∷
   rw 3 q52 ∷
   rw 4 q9 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q13 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q12 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q14 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q14 ∷
   rw⁻ 7 q13 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q14 ∷
   rw 4 q51 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q13 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q13 ∷
   rw 11 q12 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q14 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q14 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q14 ∷
   rw⁻ 7 q13 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q14 ∷
   rw 4 q51 ∷
   re 4 5 (ℓ "乙") ∷
   rw 5 q14 ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q13 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q14 ∷
   rw 2 q15 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "个") ∷
   rw 4 q16 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "个") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q17 ∷
   rw⁻ 8 q18 ∷
   rw 9 q19 ∷
   re 6 5 (ℓ "中") ∷
   rw 2 q20 ∷
   rw 3 q21 ∷
   rw 4 q22 ∷
   rw 5 q23 ∷
   rw 6 q22 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q24 ∷
   rw 8 q25 ∷
   rw 9 q24 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q26 ∷
   re 3 5 (ℓ "乜") ∷
   re 2 3 (ℓ "乛") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q10 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q11 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q5 ∷
   rw 3 q8 ∷
   re 3 5 (ℓ "乙") ∷
   rw 4 q5 ∷
   rw 3 q20 ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q21 ∷
   rw 3 q28 ∷
   rw 4 q23 ∷
   rw 5 q28 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q24 ∷
   rw 7 q29 ∷
   rw 8 q24 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q30 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q24 ∷
   rw 7 q31 ∷
   rw⁻ 6 q24 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q32 ∷
   rw⁻ 4 q23 ∷
   rw 3 q32 ∷
   rw⁻ 2 q21 ∷
   rw 3 q26 ∷
   re 3 5 (ℓ "乜") ∷
   re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q21 ∷
   rw 2 q28 ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q24 ∷
   rw 6 q29 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q30 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q24 ∷
   rw 6 q31 ∷
   rw⁻ 5 q24 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q32 ∷
   rw⁻ 3 q23 ∷
   rw 2 q32 ∷
   rw⁻ 1 q21 ∷
   rw 2 q26 ∷
   re 2 5 (ℓ "乜") ∷
   rw 2 q33 ∷
   rw 1 q30 ∷
   rw 0 q27 ∷
   rw 3 q3 ∷
   rw 2 q48 ∷
   re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q21 ∷
   rw 2 q28 ∷
   rw 3 q23 ∷
   rw 4 q28 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q24 ∷
   rw 6 q29 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q30 ∷
   re 5 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q17 ∷
   rw 7 q18 ∷
   rw 5 q19 ∷
   re 6 5 (ℓ "中") ∷
   re 4 1 (ℓ "丼丣丼") ∷
   rw 6 q5 ∷
   rw 3 q49 ∷
   re 2 1 (ℓ "丼丣丼") ∷
   rw 4 q5 ∷
   rw 1 q50 ∷
   rw 2 q12 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q14 ∷
   rw⁻ 4 q13 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q14 ∷
   rw⁻ 6 q13 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q14 ∷
   rw 3 q51 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   rw 0 q48 ∷
   rw 4 q12 ∷
   rw 3 q52 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q12 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q13 ∷
   rw 6 q12 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q13 ∷
   rw 8 q12 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q14 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q14 ∷
   rw 5 q13 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q14 ∷
   rw 3 q13 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q14 ∷
   rw 3 q51 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q52 ∷
   rw 2 q9 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q12 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q13 ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q12 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q14 ∷
   rw⁻ 3 q13 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q14 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q14 ∷
   rw 2 q51 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q13 ∷
   rw 9 q12 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q14 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q14 ∷
   rw⁻ 3 q13 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q14 ∷
   rw⁻ 5 q13 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q14 ∷
   rw 2 q51 ∷
   re 2 5 (ℓ "乙") ∷
   rw 3 q14 ∷
   re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q12 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q13 ∷
   rw 5 q12 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q13 ∷
   rw 7 q12 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q14 ∷
   rw 0 q15 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "个") ∷
   rw 2 q16 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "个") ∷
   re 5 1 (ℓ "乏丼丠丼乏") ∷
   rw 4 q17 ∷
   rw⁻ 6 q18 ∷
   rw 7 q19 ∷
   re 4 5 (ℓ "中") ∷
   rw 0 q20 ∷
   rw 1 q21 ∷
   rw 2 q22 ∷
   rw 3 q23 ∷
   rw 4 q22 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q24 ∷
   rw 6 q25 ∷
   rw 7 q24 ∷
   re 5 3 (ℓ "丽") ∷
   rw 1 q26 ∷
   re 1 5 (ℓ "乜") ∷
   re 0 3 (ℓ "乛") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 1 q10 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q11 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 5 q5 ∷
   rw 1 q8 ∷
   re 1 5 (ℓ "乙") ∷
   rw 2 q5 ∷ []) Eq.refl
