{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D001 (W : Ws) where

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
  q2 = wE 2 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 4 W
  q5 : Eqn
  q5 = wE 5 W
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 6 W
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 8 W
  q10 : Eqn
  q10 = wE 9 W
  q11 : Eqn
  q11 = wE 10 W
  q12 : Eqn
  q12 = wE 11 W
  q13 : Eqn
  q13 = wE 12 W
  q14 : Eqn
  q14 = wE 13 W
  q15 : Eqn
  q15 = wE 14 W
  q16 : Eqn
  q16 = wE 15 W
  q17 : Eqn
  q17 = wE 16 W
  q18 : Eqn
  q18 = wE 17 W
  q19 : Eqn
  q19 = eqn (ℓ "乖乙乖") (ℓ "乙乚") (ax cx-ccz)
  q20 : Eqn
  q20 = wE 18 W
  q21 : Eqn
  q21 = wE 19 W
  q22 : Eqn
  q22 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q23 : Eqn
  q23 = wE 20 W
  q24 : Eqn
  q24 = wE 21 W
  q25 : Eqn
  q25 = wE 22 W
  q26 : Eqn
  q26 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q27 : Eqn
  q27 = wE 23 W
  q28 : Eqn
  q28 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q29 : Eqn
  q29 = wE 24 W
  q30 : Eqn
  q30 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q31 : Eqn
  q31 = wE 25 W
  q32 : Eqn
  q32 = wE 26 W
  q33 : Eqn
  q33 = wE 27 W
  q34 : Eqn
  q34 = wE 28 W
  q35 : Eqn
  q35 = wE 29 W
  q36 : Eqn
  q36 = wE 30 W
  q37 : Eqn
  q37 = wE 31 W
  q38 : Eqn
  q38 = wE 32 W
  q39 : Eqn
  q39 = wE 33 W

-- CCZ312-CCZ012: 243 steps
lem-CCZ312-CCZ012 : ⟪ (ℓ "乜乙") ⟫ʷ ≈ ⟪ (ℓ "乙乜") ⟫ʷ
lem-CCZ312-CCZ012 = derive (ℓ "乜乙") (ℓ "乙乜")
  (rw 2 q1 ∷
   rw 3 q2 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "乐") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乐") ∷
   rw 4 q3 ∷
   rw 3 q4 ∷
   rw 4 q1 ∷
   rw 5 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乐") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乐") ∷
   rw 6 q3 ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q7 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "乓") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q8 ∷
   rw 6 q9 ∷
   rw 5 q10 ∷
   rw 4 q9 ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   re 4 5 (ℓ "乙") ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q7 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "乓") ∷
   rw 6 q13 ∷
   rw 5 q14 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q15 ∷
   rw 7 q13 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q16 ∷
   rw 5 q13 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q17 ∷
   rw 5 q18 ∷
   re 5 5 (ℓ "乙") ∷
   rw 3 q14 ∷
   rw 4 q19 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q20 ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "个") ∷
   rw 5 q21 ∷
   rw 8 q13 ∷
   re 6 3 (ℓ "个") ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 7 q15 ∷
   rw 3 q18 ∷
   re 3 5 (ℓ "乙") ∷
   re 5 1 (ℓ "乏乙乏") ∷
   re 6 1 (ℓ "丶丣丷丣丧") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q22 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q22 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q3 ∷
   rw 4 q23 ∷
   rw 7 q13 ∷
   re 5 3 (ℓ "个") ∷
   rw 6 q24 ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "个") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 8 q25 ∷
   rw⁻ 10 q26 ∷
   rw 11 q27 ∷
   re 8 5 (ℓ "中") ∷
   rw 4 q5 ∷
   rw 5 q28 ∷
   rw 6 q29 ∷
   rw 7 q30 ∷
   rw 8 q29 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw 10 q31 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 5 q32 ∷
   re 5 5 (ℓ "乜") ∷
   re 4 3 (ℓ "乛") ∷
   rw 5 q15 ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q33 ∷
   rw 3 q34 ∷
   rw 4 q35 ∷
   rw 5 q34 ∷
   rw 6 q31 ∷
   rw 2 q12 ∷
   re 2 5 (ℓ "乙") ∷
   re 4 1 (ℓ "並乜並") ∷
   re 5 1 (ℓ "义丹乊丹丽") ∷
   rw 4 q28 ∷
   rw 5 q36 ∷
   rw 6 q30 ∷
   rw 7 q36 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q33 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q37 ∷
   rw 3 q28 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q29 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw 8 q31 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q32 ∷
   re 3 5 (ℓ "乜") ∷
   rw 4 q37 ∷
   rw 1 q38 ∷
   rw 0 q39 ∷
   rw 3 q5 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q7 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "乓") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q8 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   rw 2 q9 ∷
   rw 1 q11 ∷
   rw 2 q12 ∷
   re 2 5 (ℓ "乙") ∷
   re 0 1 (ℓ "乏乃乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q7 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "乓") ∷
   rw 4 q13 ∷
   rw 3 q14 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q15 ∷
   rw 5 q13 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q16 ∷
   rw 3 q13 ∷
   re 4 3 (ℓ "个") ∷
   rw 2 q17 ∷
   rw 3 q18 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q14 ∷
   rw 2 q19 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 1 q20 ∷
   rw 4 q13 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q21 ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 5 q15 ∷
   rw 1 q18 ∷
   re 1 5 (ℓ "乙") ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q22 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   rw 2 q23 ∷
   rw 5 q13 ∷
   re 3 3 (ℓ "个") ∷
   rw 4 q24 ∷
   rw 7 q13 ∷
   re 5 3 (ℓ "个") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 6 q25 ∷
   rw⁻ 8 q26 ∷
   rw 9 q27 ∷
   re 6 5 (ℓ "中") ∷
   rw 2 q5 ∷
   rw 3 q28 ∷
   rw 4 q29 ∷
   rw 5 q30 ∷
   rw 6 q29 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw 8 q31 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "丽") ∷
   rw 3 q32 ∷
   re 3 5 (ℓ "乜") ∷
   re 2 3 (ℓ "乛") ∷
   rw 3 q15 ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 0 q33 ∷
   rw 1 q34 ∷
   rw 2 q35 ∷
   rw 3 q34 ∷
   rw 4 q31 ∷
   rw 0 q12 ∷
   re 0 5 (ℓ "乙") ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q28 ∷
   rw 3 q36 ∷
   rw 4 q30 ∷
   rw 5 q36 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 7 q33 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q37 ∷
   rw 1 q28 ∷
   rw 2 q29 ∷
   rw 3 q30 ∷
   rw 4 q29 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q6 ∷
   rw 6 q31 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "丽") ∷
   rw 1 q32 ∷
   re 1 5 (ℓ "乜") ∷
   rw 2 q37 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 34 W
  q41 : Eqn
  q41 = wE 35 W
  q42 : Eqn
  q42 = wE 36 W
  q43 : Eqn
  q43 = eqn (ℓ "丳乌") (ℓ "乌丳") (low-comm (CX₁₀) (CX₀₁))
  q44 : Eqn
  q44 = wE 37 W
  q45 : Eqn
  q45 = wE 38 W
  q46 : Eqn
  q46 = wE 39 W
  q47 : Eqn
  q47 = wE 40 W
  q48 : Eqn
  q48 = wE 41 W

-- CCZ123-CX30: 61 steps
lem-CCZ123-CX30 : ⟪ (ℓ "乜乐") ⟫ʷ ≈ ⟪ (ℓ "乐乜") ⟫ʷ
lem-CCZ123-CX30 = derive (ℓ "乜乐") (ℓ "乐乜")
  (rw 0 q40 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏乃乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q3 ∷
   rw 5 q41 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乐") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q3 ∷
   re 4 1 (ℓ "乏丼丳丼乏") ∷
   rw 3 q1 ∷
   re 4 3 (ℓ "乀") ∷
   rw 4 q42 ∷
   rw⁻ 5 q43 ∷
   rw 6 q44 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 9 q3 ∷
   re 3 5 (ℓ "乐") ∷
   rw 4 q5 ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q7 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "乓") ∷
   rw⁻ 2 q30 ∷
   rw 3 q45 ∷
   re 3 1 (ℓ "乏乆乏") ∷
   rw 2 q6 ∷
   rw 3 q46 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "乐") ∷
   rw 3 q30 ∷
   rw 4 q37 ∷
   re 2 1 (ℓ "乏丼丳丼乏") ∷
   rw 1 q1 ∷
   re 2 3 (ℓ "乀") ∷
   rw 2 q42 ∷
   rw⁻ 3 q43 ∷
   rw 4 q44 ∷
   re 5 1 (ℓ "乏丹乏") ∷
   rw 7 q3 ∷
   re 1 5 (ℓ "乐") ∷
   rw 2 q5 ∷
   re 1 1 (ℓ "乏乃乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q7 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "乓") ∷
   rw⁻ 0 q28 ∷
   rw 1 q47 ∷
   re 1 1 (ℓ "乏乆乏") ∷
   rw 0 q6 ∷
   rw 1 q46 ∷
   rw 2 q6 ∷
   re 0 3 (ℓ "乐") ∷
   rw 1 q28 ∷
   rw 2 q37 ∷
   rw 1 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 42 W
  q50 : Eqn
  q50 = wE 43 W
  q51 : Eqn
  q51 = wE 44 W

-- comm CCZ012 CCZ013: 229 steps
lem-comm-CCZ012-CCZ013 : ⟪ (ℓ "乙乚") ⟫ʷ ≈ ⟪ (ℓ "乚乙") ⟫ʷ
lem-comm-CCZ012-CCZ013 = derive (ℓ "乙乚") (ℓ "乚乙")
  (rw 2 q49 ∷
   rw 3 q1 ∷
   rw 4 q4 ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q22 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q22 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   rw 4 q50 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q22 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q3 ∷
   rw⁻ 8 q22 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q3 ∷
   rw 5 q50 ∷
   re 5 5 (ℓ "乙") ∷
   re 4 3 (ℓ "乚") ∷
   rw 5 q3 ∷
   rw 4 q49 ∷
   rw 5 q1 ∷
   rw 4 q51 ∷
   re 3 1 (ℓ "乏乙乏") ∷
   re 4 1 (ℓ "丶丣丷丣丧") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q22 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q3 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q3 ∷
   rw 6 q22 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q3 ∷
   rw 4 q22 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 4 q50 ∷
   re 4 5 (ℓ "乙") ∷
   rw 2 q51 ∷
   rw 3 q19 ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 2 q1 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   rw 3 q50 ∷
   re 3 5 (ℓ "乙") ∷
   re 2 3 (ℓ "乚") ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q22 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   rw 3 q50 ∷
   re 3 5 (ℓ "乙") ∷
   rw 4 q3 ∷
   rw 3 q1 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   rw 5 q22 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q3 ∷
   rw 3 q22 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 3 q50 ∷
   re 3 5 (ℓ "乙") ∷
   re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q22 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   rw 4 q22 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q3 ∷
   rw 2 q22 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 2 q50 ∷
   re 2 5 (ℓ "乙") ∷
   rw 2 q38 ∷
   rw 1 q3 ∷
   rw 0 q38 ∷
   rw 3 q1 ∷
   rw 2 q51 ∷
   re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q22 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   rw 4 q22 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q3 ∷
   rw 2 q22 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 2 q50 ∷
   re 2 5 (ℓ "乙") ∷
   rw 0 q51 ∷
   rw 1 q19 ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q22 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 0 q1 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q3 ∷
   rw⁻ 2 q22 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   rw 1 q50 ∷
   re 1 5 (ℓ "乙") ∷
   re 0 3 (ℓ "乚") ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q3 ∷
   rw⁻ 2 q22 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   rw 1 q50 ∷
   re 1 5 (ℓ "乙") ∷
   rw 2 q3 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = wE 45 W
  q53 : Eqn
  q53 = eqn (ℓ "九乚九") (ℓ "乚乜") (ax toff-ccz)

-- CCZ013-T: 2 steps
lem-CCZ013-T : ⟪ (ℓ "乚九") ⟫ʷ ≈ ⟪ (ℓ "九乚乜") ⟫ʷ
lem-CCZ013-T = derive (ℓ "乚九") (ℓ "九乚乜")
  (rw 0 q52 ∷
   rw 1 q53 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = eqn (ℓ "一丼") (ℓ "丼一") (low₁-comm (iI) (Swap))
  q55 : Eqn
  q55 = eqn (ℓ "上丼") (ℓ "丼上") (low₁-comm (K) (Swap))
  q56 : Eqn
  q56 = wE 46 W
  q57 : Eqn
  q57 = wE 47 W
  q58 : Eqn
  q58 = wE 48 W
  q59 : Eqn
  q59 = wE 49 W
  q60 : Eqn
  q60 = wE 50 W
  q61 : Eqn
  q61 = wE 51 W
  q62 : Eqn
  q62 = wE 52 W

-- CCZ023-T: 110 steps
lem-CCZ023-T : ⟪ (ℓ "乛九") ⟫ʷ ≈ ⟪ (ℓ "九乛乜") ⟫ʷ
lem-CCZ023-T = derive (ℓ "乛九") (ℓ "九乛乜")
  (rw 0 q52 ∷
   rw 4 q13 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 10 q54 ∷
   rw 9 q55 ∷
   re 8 1 (ℓ "丼丠丼") ∷
   rw 10 q15 ∷
   rw 7 q13 ∷
   re 8 3 (ℓ "个") ∷
   rw 6 q16 ∷
   rw 5 q13 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q17 ∷
   rw 3 q55 ∷
   rw 4 q56 ∷
   re 4 8 (ℓ "九") ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q28 ∷
   rw 3 q36 ∷
   rw 4 q30 ∷
   rw 5 q36 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 7 q33 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q37 ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 9 q25 ∷
   rw 8 q26 ∷
   rw 6 q27 ∷
   re 7 5 (ℓ "中") ∷
   re 5 1 (ℓ "丼丣丼") ∷
   rw 7 q15 ∷
   rw 4 q57 ∷
   re 3 1 (ℓ "丼丣丼") ∷
   rw 5 q15 ∷
   rw 2 q58 ∷
   rw 3 q1 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q22 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   rw 4 q50 ∷
   re 4 5 (ℓ "乙") ∷
   re 3 3 (ℓ "乚") ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw 8 q54 ∷
   rw 7 q55 ∷
   re 6 1 (ℓ "丼丠丼") ∷
   rw 8 q15 ∷
   rw 5 q13 ∷
   re 6 3 (ℓ "个") ∷
   rw 4 q16 ∷
   rw 3 q13 ∷
   re 4 3 (ℓ "个") ∷
   rw 2 q17 ∷
   rw 1 q55 ∷
   rw 2 q56 ∷
   re 2 8 (ℓ "九") ∷
   rw 2 q53 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 1 q23 ∷
   rw 4 q13 ∷
   re 2 3 (ℓ "个") ∷
   rw 3 q24 ∷
   rw 6 q13 ∷
   re 4 3 (ℓ "个") ∷
   re 6 1 (ℓ "乏丼丠丼乏") ∷
   rw 5 q25 ∷
   rw⁻ 7 q26 ∷
   rw 8 q27 ∷
   re 5 5 (ℓ "中") ∷
   rw 1 q5 ∷
   rw 2 q28 ∷
   rw 3 q29 ∷
   rw 4 q30 ∷
   rw 5 q29 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q31 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q32 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q59 ∷
   rw 3 q60 ∷
   rw 4 q61 ∷
   rw 5 q60 ∷
   rw 6 q23 ∷
   rw 2 q62 ∷
   re 2 5 (ℓ "乜") ∷
   rw 3 q15 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 53 W
  q64 : Eqn
  q64 = eqn (ℓ "上乖") (ℓ "乖上") (low₁-comm (K) ((CX₁₀ ↑)))
  q65 : Eqn
  q65 = eqn (ℓ "下乖") (ℓ "乖下") (low₁-comm ((K • iI)) ((CX₁₀ ↑)))
  q66 : Eqn
  q66 = wE 54 W
  q67 : Eqn
  q67 = wE 55 W
  q68 : Eqn
  q68 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q69 : Eqn
  q69 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q70 : Eqn
  q70 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q71 : Eqn
  q71 = wE 56 W

-- N32-T: 59 steps
lem-N32-T : ⟪ (ℓ "乖九乖") ⟫ʷ ≈ ⟪ (ℓ "九乞") ⟫ʷ
lem-N32-T = derive (ℓ "乖九乖") (ℓ "九乞")
  (rw 1 q63 ∷
   rw⁻ 0 q64 ∷
   rw 3 q65 ∷
   rw 1 q19 ∷
   rw 2 q66 ∷
   rw 0 q67 ∷
   rw 4 q1 ∷
   rw 3 q68 ∷
   re 2 1 (ℓ "乏乙乏") ∷
   re 3 1 (ℓ "丶丣丷丣丧") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q3 ∷
   rw 5 q22 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q3 ∷
   rw 3 q22 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 3 q50 ∷
   re 3 5 (ℓ "乙") ∷
   rw 1 q69 ∷
   rw 2 q67 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q69 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q22 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q22 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q69 ∷
   rw⁻ 8 q70 ∷
   rw 1 q1 ∷
   rw⁻ 2 q69 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw⁻ 4 q22 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q3 ∷
   rw⁻ 6 q22 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   rw⁻ 8 q69 ∷
   rw⁻ 9 q70 ∷
   rw 2 q71 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q3 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 57 W
  q73 : Eqn
  q73 = eqn (ℓ "上乌") (ℓ "乌上") (low₁-comm (K) ((CX₀₁ ↑)))
  q74 : Eqn
  q74 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q75 : Eqn
  q75 = wE 58 W
  q76 : Eqn
  q76 = eqn (ℓ "両乌") (ℓ "乌両") (low-comm ((CS • CS • CS)) (CX₀₁))
  q77 : Eqn
  q77 = eqn (ℓ "並乌") (ℓ "乌並") (low-comm (Swap) (CX₀₁))
  q78 : Eqn
  q78 = wE 59 W
  q79 : Eqn
  q79 = eqn (ℓ "下乌") (ℓ "乌下") (low₁-comm ((K • iI)) ((CX₀₁ ↑)))
  q80 : Eqn
  q80 = wE 60 W
  q81 : Eqn
  q81 = wE 61 W

-- N23-T: 16 steps
lem-N23-T : ⟪ (ℓ "乌九乌") ⟫ʷ ≈ ⟪ (ℓ "九") ⟫ʷ
lem-N23-T = derive (ℓ "乌九乌") (ℓ "九")
  (rw 1 q72 ∷
   rw⁻ 0 q73 ∷
   rw⁻ 1 q74 ∷
   rw 2 q75 ∷
   rw⁻ 3 q76 ∷
   rw 4 q75 ∷
   rw 7 q5 ∷
   rw 6 q8 ∷
   rw⁻ 5 q77 ∷
   rw 6 q78 ∷
   rw 5 q33 ∷
   rw 6 q77 ∷
   rw 7 q37 ∷
   rw⁻ 6 q79 ∷
   rw 7 q80 ∷
   rw 0 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 62 W
  q83 : Eqn
  q83 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q84 : Eqn
  q84 = wE 63 W

-- SW-T-SW: 59 steps
lem-SW-T-SW : ⟪ (ℓ "乏九乏") ⟫ʷ ≈ ⟪ (ℓ "乞") ⟫ʷ
lem-SW-T-SW = derive (ℓ "乏九乏") (ℓ "乞")
  (rw 1 q72 ∷
   rw⁻ 0 q69 ∷
   rw⁻ 1 q26 ∷
   rw 2 q82 ∷
   rw⁻ 3 q83 ∷
   rw 4 q82 ∷
   rw 7 q5 ∷
   rw 6 q8 ∷
   rw⁻ 5 q6 ∷
   rw 6 q84 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q33 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q6 ∷
   rw 7 q37 ∷
   rw⁻ 6 q68 ∷
   rw 7 q3 ∷
   rw 7 q1 ∷
   rw 6 q68 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 6 q3 ∷
   rw 3 q83 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 4 q3 ∷
   rw 1 q26 ∷
   rw 0 q69 ∷
   rw 1 q81 ∷
   re 1 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 0 q69 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q22 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q22 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q69 ∷
   rw⁻ 7 q70 ∷
   rw 0 q1 ∷
   rw⁻ 1 q69 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q3 ∷
   rw⁻ 3 q22 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q3 ∷
   rw⁻ 5 q22 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q3 ∷
   rw⁻ 7 q69 ∷
   rw⁻ 8 q70 ∷
   rw 1 q71 ∷
   re 1 8 (ℓ "九") ∷
   re 0 3 (ℓ "乞") ∷
   rw 1 q3 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 64 W
  q86 : Eqn
  q86 = eqn (ℓ "上丽") (ℓ "丽上") (low₁-comm (K) ((Swap ↑ • CS • Swap ↑)))
  q87 : Eqn
  q87 = wE 65 W
  q88 : Eqn
  q88 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q89 : Eqn
  q89 = wE 66 W
  q90 : Eqn
  q90 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))
  q91 : Eqn
  q91 = wE 67 W
  q92 : Eqn
  q92 = eqn (ℓ "下丽") (ℓ "丽下") (low₁-comm ((K • iI)) ((Swap ↑ • CS • Swap ↑)))
  q93 : Eqn
  q93 = wE 68 W

-- CS13 passes T: 25 steps
lem-CS13-passes-T : ⟪ (ℓ "丽九") ⟫ʷ ≈ ⟪ (ℓ "九丽") ⟫ʷ
lem-CS13-passes-T = derive (ℓ "丽九") (ℓ "九丽")
  (rw 1 q85 ∷
   rw⁻ 0 q86 ∷
   re 2 1 (ℓ "丼丠丼") ∷
   rw 1 q87 ∷
   rw⁻ 2 q88 ∷
   rw 3 q58 ∷
   re 1 3 (ℓ "丧") ∷
   rw 2 q89 ∷
   re 4 1 (ℓ "丼両丼") ∷
   rw 3 q87 ∷
   rw⁻ 4 q90 ∷
   rw 5 q58 ∷
   re 3 3 (ℓ "丨") ∷
   rw 4 q89 ∷
   rw 7 q1 ∷
   rw 6 q26 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 6 q91 ∷
   rw⁻ 5 q26 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q3 ∷
   rw⁻ 6 q92 ∷
   rw 0 q93 ∷ []) Eq.refl
