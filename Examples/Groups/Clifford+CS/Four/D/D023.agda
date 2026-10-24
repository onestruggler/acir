{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D023 (W : Ws) where

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
open import Examples.Groups.Clifford+CS.Canonical using (can-≈)

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
  q15 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q17 : Eqn
  q17 = wE 419 W
  q18 : Eqn
  q18 = wE 123 W
  q19 : Eqn
  q19 = wE 24 W
  q20 : Eqn
  q20 = wE 25 W
  q21 : Eqn
  q21 = wE 124 W

-- pass [X3 CK32 X3] [TOFF023]: 67 steps
lem-pass-X3-CK32-X3-vs-TOFF023 : ⟪ (ℓ "丞乗丞也") ⟫ʷ ≈ ⟪ (ℓ "也丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF023 = derive (ℓ "丞乗丞也") (ℓ "也丞乗丞")
  (rw 4 q1 ∷
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
   rw⁻ 2 q15 ∷
   rw⁻ 1 q16 ∷
   rw⁻ 0 q15 ∷
   rw 1 q17 ∷
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
   rw 1 q18 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q18 ∷
   rw 8 q21 ∷
   rw 1 q14 ∷
   re 1 8 (ℓ "乢") ∷
   re 0 3 (ℓ "也") ∷
   rw 1 q15 ∷
   rw 2 q16 ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q22 : Eqn
  q22 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))

-- pass [X3 CK32 X3] [CS01]: 3 steps
lem-pass-X3-CK32-X3-vs-CS01 : ⟪ (ℓ "丞乗丞丠") ⟫ʷ ≈ ⟪ (ℓ "丠丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-CS01 = derive (ℓ "丞乗丞丠") (ℓ "丠丞乗丞")
  (rw⁻ 2 q22 ∷
   rw⁻ 1 q23 ∷
   rw⁻ 0 q22 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = eqn (ℓ "両丞") (ℓ "丞両") (low-comm ((CS • CS • CS)) ((X ↑)))
  q25 : Eqn
  q25 = eqn (ℓ "両乗") (ℓ "乗両") (low-comm ((CS • CS • CS)) (CK₁₀))

-- pass [X3 CK32 X3] [CSd01]: 3 steps
lem-pass-X3-CK32-X3-vs-CSd01 : ⟪ (ℓ "丞乗丞両") ⟫ʷ ≈ ⟪ (ℓ "両丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-CSd01 = derive (ℓ "丞乗丞両") (ℓ "両丞乗丞")
  (rw⁻ 2 q24 ∷
   rw⁻ 1 q25 ∷
   rw⁻ 0 q24 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = eqn (ℓ "一") (ℓ "七") (trans (can-≈ (iI)) (sym (can-≈ ((iI ↑ ↑ ↑)))))
  q27 : Eqn
  q27 = wE 420 W
  q28 : Eqn
  q28 = eqn (ℓ "七") (ℓ "一") (trans (can-≈ ((iI ↑ ↑ ↑))) (sym (can-≈ (iI))))

-- pass [CS13] [iI]: 3 steps
lem-pass-CS13-vs-iI : ⟪ (ℓ "丽一") ⟫ʷ ≈ ⟪ (ℓ "一丽") ⟫ʷ
lem-pass-CS13-vs-iI = derive (ℓ "丽一") (ℓ "一丽")
  (rw 1 q26 ∷
   rw 0 q27 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 421 W

-- pass [CS13] [Sd3]: 1 steps
lem-pass-CS13-vs-Sd3 : ⟪ (ℓ "丽丛") ⟫ʷ ≈ ⟪ (ℓ "丛丽") ⟫ʷ
lem-pass-CS13-vs-Sd3 = derive (ℓ "丽丛") (ℓ "丛丽")
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 422 W

-- pass [CS13] [S3]: 1 steps
lem-pass-CS13-vs-S3 : ⟪ (ℓ "丽业") ⟫ʷ ≈ ⟪ (ℓ "业丽") ⟫ʷ
lem-pass-CS13-vs-S3 = derive (ℓ "丽业") (ℓ "业丽")
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 1 W
  q32 : Eqn
  q32 = wE 173 W
  q33 : Eqn
  q33 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q34 : Eqn
  q34 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q35 : Eqn
  q35 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q36 : Eqn
  q36 = wE 3 W
  q37 : Eqn
  q37 = wE 56 W
  q38 : Eqn
  q38 = wE 423 W
  q39 : Eqn
  q39 = wE 175 W

-- pass [CS13] [X3 TOFF013 X3]: 65 steps
lem-pass-CS13-vs-X3-TOFF013-X3 : ⟪ (ℓ "丽丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞丽") ⟫ʷ
lem-pass-CS13-vs-X3-TOFF013-X3 = derive (ℓ "丽丞乞丞") (ℓ "丞乞丞丽")
  (rw 4 q31 ∷
   rw 3 q32 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q33 ∷
   rw 5 q31 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q34 ∷
   rw 7 q31 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q34 ∷
   rw 9 q31 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q33 ∷
   rw⁻ 9 q35 ∷
   rw 10 q36 ∷
   rw 9 q35 ∷
   rw 8 q33 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q36 ∷
   rw 6 q34 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q36 ∷
   rw 4 q34 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q36 ∷
   rw 2 q33 ∷
   rw 3 q37 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q32 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q36 ∷
   rw 1 q38 ∷
   rw 0 q39 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q33 ∷
   rw 4 q31 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q34 ∷
   rw 6 q31 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q34 ∷
   rw 8 q31 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q33 ∷
   rw⁻ 8 q35 ∷
   rw 1 q31 ∷
   rw⁻ 2 q33 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q36 ∷
   rw⁻ 4 q34 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q36 ∷
   rw⁻ 6 q34 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q36 ∷
   rw⁻ 8 q33 ∷
   rw⁻ 9 q35 ∷
   rw 2 q37 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q39 ∷
   rw 5 q31 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q36 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 26 W
  q41 : Eqn
  q41 = wE 75 W
  q42 : Eqn
  q42 = wE 39 W
  q43 : Eqn
  q43 = wE 29 W
  q44 : Eqn
  q44 = wE 91 W
  q45 : Eqn
  q45 = wE 424 W
  q46 : Eqn
  q46 = wE 20 W
  q47 : Eqn
  q47 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))
  q48 : Eqn
  q48 = wE 49 W
  q49 : Eqn
  q49 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q50 : Eqn
  q50 = wE 6 W
  q51 : Eqn
  q51 = wE 76 W
  q52 : Eqn
  q52 = wE 81 W

-- comm CCZ023 CS13: 131 steps
lem-comm-CCZ023-CS13 : ⟪ (ℓ "乛丽") ⟫ʷ ≈ ⟪ (ℓ "丽乛") ⟫ʷ
lem-comm-CCZ023-CS13 = derive (ℓ "乛丽") (ℓ "丽乛")
  (rw 1 q1 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q3 ∷
   rw 1 q4 ∷
   rw 2 q5 ∷
   rw 3 q4 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q6 ∷
   rw 5 q7 ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q9 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q12 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q13 ∷
   rw⁻ 2 q5 ∷
   rw 1 q13 ∷
   rw⁻ 0 q3 ∷
   rw 1 q40 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q41 ∷
   rw 0 q7 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 1 q6 ∷
   rw 2 q42 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "乐") ∷
   rw 2 q43 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 3 q6 ∷
   rw 4 q42 ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "乐") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 4 q44 ∷
   rw 5 q31 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q36 ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw 5 q36 ∷
   rw 4 q45 ∷
   rw 5 q31 ∷
   re 3 3 (ℓ "丽") ∷
   rw 6 q31 ∷
   re 4 3 (ℓ "乐") ∷
   rw 5 q36 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q31 ∷
   re 3 3 (ℓ "丮") ∷
   re 3 1 (ℓ "乏丼両丼乏") ∷
   rw 9 q31 ∷
   re 7 3 (ℓ "丽") ∷
   rw 6 q46 ∷
   rw 5 q47 ∷
   rw 4 q48 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q36 ∷
   re 4 5 (ℓ "丮") ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q36 ∷
   re 2 3 (ℓ "丽") ∷
   rw 3 q31 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q36 ∷
   re 1 1 (ℓ "乏乃乏") ∷
   rw 3 q36 ∷
   rw 2 q45 ∷
   rw 3 q31 ∷
   re 1 3 (ℓ "丽") ∷
   rw 4 q31 ∷
   re 2 3 (ℓ "乐") ∷
   rw 3 q36 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q31 ∷
   re 1 3 (ℓ "中") ∷
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q31 ∷
   re 5 3 (ℓ "丽") ∷
   rw 4 q46 ∷
   rw 3 q49 ∷
   rw 2 q48 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q36 ∷
   re 2 5 (ℓ "中") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q36 ∷
   re 0 3 (ℓ "丽") ∷
   rw 6 q1 ∷
   rw⁻ 5 q3 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q50 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "乓") ∷
   rw 3 q51 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q50 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "乓") ∷
   rw 1 q12 ∷
   rw 2 q52 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q40 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q54 : Eqn
  q54 = wE 425 W

-- pass [CS13] [CSd01]: 9 steps
lem-pass-CS13-vs-CSd01 : ⟪ (ℓ "丽両") ⟫ʷ ≈ ⟪ (ℓ "両丽") ⟫ʷ
lem-pass-CS13-vs-CSd01 = derive (ℓ "丽両") (ℓ "両丽")
  (rw 2 q31 ∷
   rw 1 q53 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q36 ∷
   rw 1 q54 ∷
   rw⁻ 0 q53 ∷
   rw 3 q31 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q36 ∷ []) Eq.refl

private
  q55 : Eqn
  q55 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q56 : Eqn
  q56 = wE 67 W

-- pass [CS13] [CS01]: 9 steps
lem-pass-CS13-vs-CS01 : ⟪ (ℓ "丽丠") ⟫ʷ ≈ ⟪ (ℓ "丠丽") ⟫ʷ
lem-pass-CS13-vs-CS01 = derive (ℓ "丽丠") (ℓ "丠丽")
  (rw 2 q31 ∷
   rw 1 q55 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q36 ∷
   rw 1 q56 ∷
   rw⁻ 0 q55 ∷
   rw 3 q31 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q36 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q58 : Eqn
  q58 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q59 : Eqn
  q59 = wE 393 W
  q60 : Eqn
  q60 = wE 394 W

-- b2g 1011R2: 4 steps
lem-b2g-1011R2 : ⟪ (ℓ "丌丘丞且世义乣乊乣丗丕丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞") ⟫ʷ
lem-b2g-1011R2 = derive (ℓ "丌丘丞且世义乣乊乣丗丕丌丘丞") (ℓ "丌丞丕丗且且义乣乊乣丕丕世且丌丞")
  (rw 1 q57 ∷
   rw 11 q58 ∷
   rw 2 q59 ∷
   rw 10 q60 ∷ []) Eq.refl

private
  q61 : Eqn
  q61 = wE 426 W

-- pass [CS23] [iI]: 3 steps
lem-pass-CS23-vs-iI : ⟪ (ℓ "义一") ⟫ʷ ≈ ⟪ (ℓ "一义") ⟫ʷ
lem-pass-CS23-vs-iI = derive (ℓ "义一") (ℓ "一义")
  (rw 1 q26 ∷
   rw 0 q61 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 427 W

-- pass [CS23] [Sd3]: 1 steps
lem-pass-CS23-vs-Sd3 : ⟪ (ℓ "义丛") ⟫ʷ ≈ ⟪ (ℓ "丛义") ⟫ʷ
lem-pass-CS23-vs-Sd3 = derive (ℓ "义丛") (ℓ "丛义")
  (rw 0 q62 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 428 W

-- pass [CS23] [S3]: 1 steps
lem-pass-CS23-vs-S3 : ⟪ (ℓ "义业") ⟫ʷ ≈ ⟪ (ℓ "业义") ⟫ʷ
lem-pass-CS23-vs-S3 = derive (ℓ "义业") (ℓ "业义")
  (rw 0 q63 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 429 W

-- pass [TOFF201] [iI]: 1 steps
lem-pass-TOFF201-vs-iI : ⟪ (ℓ "乣一") ⟫ʷ ≈ ⟪ (ℓ "一乣") ⟫ʷ
lem-pass-TOFF201-vs-iI = derive (ℓ "乣一") (ℓ "一乣")
  (rw 0 q64 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 430 W

-- pass [CSd23] [iI]: 3 steps
lem-pass-CSd23-vs-iI : ⟪ (ℓ "乊一") ⟫ʷ ≈ ⟪ (ℓ "一乊") ⟫ʷ
lem-pass-CSd23-vs-iI = derive (ℓ "乊一") (ℓ "一乊")
  (rw 1 q26 ∷
   rw 0 q65 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 431 W

-- pass [Sd0] [CSd23]: 1 steps
lem-pass-Sd0-vs-CSd23 : ⟪ (ℓ "三乊") ⟫ʷ ≈ ⟪ (ℓ "乊三") ⟫ʷ
lem-pass-Sd0-vs-CSd23 = derive (ℓ "三乊") (ℓ "乊三")
  (rw 0 q66 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 432 W

-- pass [Sd3] [CSd23]: 1 steps
lem-pass-Sd3-vs-CSd23 : ⟪ (ℓ "丛乊") ⟫ʷ ≈ ⟪ (ℓ "乊丛") ⟫ʷ
lem-pass-Sd3-vs-CSd23 = derive (ℓ "丛乊") (ℓ "乊丛")
  (rw 0 q67 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = wE 433 W

-- pass [CS03] [CSd23]: 15 steps
lem-pass-CS03-vs-CSd23 : ⟪ (ℓ "中乊") ⟫ʷ ≈ ⟪ (ℓ "乊中") ⟫ʷ
lem-pass-CS03-vs-CSd23 = derive (ℓ "中乊") (ℓ "乊中")
  (rw 2 q1 ∷
   rw⁻ 1 q5 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q12 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q68 ∷
   rw 0 q5 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q6 ∷
   rw 2 q7 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q9 ∷ []) Eq.refl

private
  q69 : Eqn
  q69 = eqn (ℓ "並丛") (ℓ "丛並") (low-comm (Swap) (((S • S • S) ↑)))
  q70 : Eqn
  q70 = wE 434 W
  q71 : Eqn
  q71 = wE 435 W
  q72 : Eqn
  q72 = wE 436 W
  q73 : Eqn
  q73 = wE 437 W
  q74 : Eqn
  q74 = wE 316 W

-- pass [CS23] [iI Sd0 Sd3 CS03]: 23 steps
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 : ⟪ (ℓ "义一三丛中") ⟫ʷ ≈ ⟪ (ℓ "一三丛中义") ⟫ʷ
lem-pass-CS23-vs-iI-Sd0-Sd3-CS03 = derive (ℓ "义一三丛中") (ℓ "一三丛中义")
  (rw 5 q1 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q12 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 3 q69 ∷
   rw 2 q70 ∷
   rw 1 q71 ∷
   rw⁻ 0 q3 ∷
   rw 2 q26 ∷
   rw 1 q72 ∷
   rw 1 q28 ∷
   rw 0 q73 ∷
   rw 1 q74 ∷
   rw 2 q69 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷ []) Eq.refl

private
  q75 : Eqn
  q75 = wE 438 W

-- pass [TOFF201] [Sd0]: 1 steps
lem-pass-TOFF201-vs-Sd0 : ⟪ (ℓ "乣三") ⟫ʷ ≈ ⟪ (ℓ "三乣") ⟫ʷ
lem-pass-TOFF201-vs-Sd0 = derive (ℓ "乣三") (ℓ "三乣")
  (rw 0 q75 ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = eqn (ℓ "乣丛") (ℓ "丛乣") (low₃-comm (Toffᵗ) ((S • S • S)))

-- pass [TOFF201] [Sd3]: 1 steps
lem-pass-TOFF201-vs-Sd3 : ⟪ (ℓ "乣丛") ⟫ʷ ≈ ⟪ (ℓ "丛乣") ⟫ʷ
lem-pass-TOFF201-vs-Sd3 = derive (ℓ "乣丛") (ℓ "丛乣")
  (rw 0 q76 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 439 W

-- pass [CSd23] [iI Sd0 Sd3 CS03]: 23 steps
lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 : ⟪ (ℓ "乊一三丛中") ⟫ʷ ≈ ⟪ (ℓ "一三丛中乊") ⟫ʷ
lem-pass-CSd23-vs-iI-Sd0-Sd3-CS03 = derive (ℓ "乊一三丛中") (ℓ "一三丛中乊")
  (rw 5 q1 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q12 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 3 q69 ∷
   rw 2 q70 ∷
   rw 1 q71 ∷
   rw⁻ 0 q5 ∷
   rw 2 q26 ∷
   rw 1 q77 ∷
   rw 1 q28 ∷
   rw 0 q73 ∷
   rw 1 q74 ∷
   rw 2 q69 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw 4 q7 ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q5 ∷
   rw 5 q9 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 440 W

-- pass [CS23] [S2]: 1 steps
lem-pass-CS23-vs-S2 : ⟪ (ℓ "义且") ⟫ʷ ≈ ⟪ (ℓ "且义") ⟫ʷ
lem-pass-CS23-vs-S2 = derive (ℓ "义且") (ℓ "且义")
  (rw 0 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 441 W

-- pass [CS23] [Sd2]: 1 steps
lem-pass-CS23-vs-Sd2 : ⟪ (ℓ "义丕") ⟫ʷ ≈ ⟪ (ℓ "丕义") ⟫ʷ
lem-pass-CS23-vs-Sd2 = derive (ℓ "义丕") (ℓ "丕义")
  (rw 0 q79 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 442 W

-- pass [CS23] [S1]: 1 steps
lem-pass-CS23-vs-S1 : ⟪ (ℓ "义与") ⟫ʷ ≈ ⟪ (ℓ "与义") ⟫ʷ
lem-pass-CS23-vs-S1 = derive (ℓ "义与") (ℓ "与义")
  (rw 0 q80 ∷ []) Eq.refl

private
  q81 : Eqn
  q81 = wE 443 W

-- pass [CS23] [Sd1]: 1 steps
lem-pass-CS23-vs-Sd1 : ⟪ (ℓ "义丏") ⟫ʷ ≈ ⟪ (ℓ "丏义") ⟫ʷ
lem-pass-CS23-vs-Sd1 = derive (ℓ "义丏") (ℓ "丏义")
  (rw 0 q81 ∷ []) Eq.refl

private
  q82 : Eqn
  q82 = wE 444 W

-- pass [CCZ012] [CS01]: 1 steps
lem-pass-CCZ012-vs-CS01 : ⟪ (ℓ "乙丠") ⟫ʷ ≈ ⟪ (ℓ "丠乙") ⟫ʷ
lem-pass-CCZ012-vs-CS01 = derive (ℓ "乙丠") (ℓ "丠乙")
  (rw 0 q82 ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 445 W

-- pass [S2] [CSd23]: 1 steps
lem-pass-S2-vs-CSd23 : ⟪ (ℓ "且乊") ⟫ʷ ≈ ⟪ (ℓ "乊且") ⟫ʷ
lem-pass-S2-vs-CSd23 = derive (ℓ "且乊") (ℓ "乊且")
  (rw 0 q83 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 446 W

-- pass [CCZ012] [CSd01]: 1 steps
lem-pass-CCZ012-vs-CSd01 : ⟪ (ℓ "乙両") ⟫ʷ ≈ ⟪ (ℓ "両乙") ⟫ʷ
lem-pass-CCZ012-vs-CSd01 = derive (ℓ "乙両") (ℓ "両乙")
  (rw 0 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 447 W

-- pass [Sd2] [CSd23]: 1 steps
lem-pass-Sd2-vs-CSd23 : ⟪ (ℓ "丕乊") ⟫ʷ ≈ ⟪ (ℓ "乊丕") ⟫ʷ
lem-pass-Sd2-vs-CSd23 = derive (ℓ "丕乊") (ℓ "乊丕")
  (rw 0 q85 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q87 : Eqn
  q87 = wE 334 W
  q88 : Eqn
  q88 = wE 140 W
  q89 : Eqn
  q89 = wE 448 W
  q90 : Eqn
  q90 = wE 142 W

-- pass [X3 CK30 X3] [TOFF203]: 75 steps
lem-pass-X3-CK30-X3-vs-TOFF203 : ⟪ (ℓ "丞乑丞乤") ⟫ʷ ≈ ⟪ (ℓ "乤丞乑丞") ⟫ʷ
lem-pass-X3-CK30-X3-vs-TOFF203 = derive (ℓ "丞乑丞乤") (ℓ "乤丞乑丞")
  (rw 4 q1 ∷
   re 3 1 (ℓ "並乥並") ∷
   re 4 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 3 q86 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q86 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q86 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q86 ∷
   rw 4 q87 ∷
   re 4 8 (ℓ "乥") ∷
   rw⁻ 2 q15 ∷
   re 1 1 (ℓ "乏乄乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q88 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "乔") ∷
   rw⁻ 0 q15 ∷
   rw 1 q89 ∷
   re 1 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 0 q86 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q86 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q86 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q86 ∷
   rw 8 q21 ∷
   rw 1 q87 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q15 ∷
   re 3 1 (ℓ "乏乇乏") ∷
   rw 2 q6 ∷
   rw 3 q90 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "乑") ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = wE 449 W

-- pass [X3 CS30 X3] [TOFF203]: 75 steps
lem-pass-X3-CS30-X3-vs-TOFF203 : ⟪ (ℓ "丞中丞乤") ⟫ʷ ≈ ⟪ (ℓ "乤丞中丞") ⟫ʷ
lem-pass-X3-CS30-X3-vs-TOFF203 = derive (ℓ "丞中丞乤") (ℓ "乤丞中丞")
  (rw 4 q1 ∷
   re 3 1 (ℓ "並乥並") ∷
   re 4 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 3 q86 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q86 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q86 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q86 ∷
   rw 4 q87 ∷
   re 4 8 (ℓ "乥") ∷
   rw⁻ 2 q15 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q12 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 0 q15 ∷
   rw 1 q91 ∷
   re 1 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 0 q86 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q86 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q86 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q86 ∷
   rw 8 q21 ∷
   rw 1 q87 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q15 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q6 ∷
   rw 3 q7 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q92 : Eqn
  q92 = wE 450 W

-- pass [X3 CSd30 X3] [TOFF203]: 75 steps
lem-pass-X3-CSd30-X3-vs-TOFF203 : ⟪ (ℓ "丞丮丞乤") ⟫ʷ ≈ ⟪ (ℓ "乤丞丮丞") ⟫ʷ
lem-pass-X3-CSd30-X3-vs-TOFF203 = derive (ℓ "丞丮丞乤") (ℓ "乤丞丮丞")
  (rw 4 q1 ∷
   re 3 1 (ℓ "並乥並") ∷
   re 4 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 3 q86 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q86 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q86 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q86 ∷
   rw 4 q87 ∷
   re 4 8 (ℓ "乥") ∷
   rw⁻ 2 q15 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q51 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 0 q15 ∷
   rw 1 q92 ∷
   re 1 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 0 q86 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q86 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q86 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q86 ∷
   rw 8 q21 ∷
   rw 1 q87 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q15 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q6 ∷
   rw 3 q43 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "丮") ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q93 : Eqn
  q93 = wE 137 W
  q94 : Eqn
  q94 = wE 451 W
  q95 : Eqn
  q95 = wE 139 W

-- pass [X3 CKd30 X3] [TOFF203]: 75 steps
lem-pass-X3-CKd30-X3-vs-TOFF203 : ⟪ (ℓ "丞乒丞乤") ⟫ʷ ≈ ⟪ (ℓ "乤丞乒丞") ⟫ʷ
lem-pass-X3-CKd30-X3-vs-TOFF203 = derive (ℓ "丞乒丞乤") (ℓ "乤丞乒丞")
  (rw 4 q1 ∷
   re 3 1 (ℓ "並乥並") ∷
   re 4 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 3 q86 ∷
   rw 4 q3 ∷
   rw 5 q4 ∷
   rw 6 q5 ∷
   rw 7 q4 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q6 ∷
   rw 9 q7 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q86 ∷
   rw 10 q8 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw⁻ 9 q86 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q12 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "丽") ∷
   rw 7 q13 ∷
   rw⁻ 6 q5 ∷
   rw 5 q13 ∷
   rw⁻ 4 q3 ∷
   rw⁻ 3 q86 ∷
   rw 4 q87 ∷
   re 4 8 (ℓ "乥") ∷
   rw⁻ 2 q15 ∷
   re 1 1 (ℓ "乏久乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q93 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "乕") ∷
   rw⁻ 0 q15 ∷
   rw 1 q94 ∷
   re 1 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 0 q86 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q4 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw 6 q7 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q86 ∷
   rw 7 q8 ∷
   rw 0 q1 ∷
   rw 1 q86 ∷
   rw 2 q3 ∷
   rw 3 q19 ∷
   rw 4 q5 ∷
   rw 5 q19 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 7 q20 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "丽") ∷
   rw 7 q86 ∷
   rw 8 q21 ∷
   rw 1 q87 ∷
   re 1 8 (ℓ "乥") ∷
   re 0 3 (ℓ "乤") ∷
   rw 1 q15 ∷
   re 3 1 (ℓ "乏么乏") ∷
   rw 2 q6 ∷
   rw 3 q95 ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "乒") ∷
   rw 3 q15 ∷
   rw 4 q9 ∷ []) Eq.refl

private
  q96 : Eqn
  q96 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q97 : Eqn
  q97 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q98 : Eqn
  q98 = wE 452 W
  q99 : Eqn
  q99 = wE 453 W

-- b2g 0111R1: 4 steps
lem-b2g-0111R1 : ⟪ (ℓ "丒丘丞与丐丽习举习丑丏丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞") ⟫ʷ
lem-b2g-0111R1 = derive (ℓ "丒丘丞与丐丽习举习丑丏丒丘丞") (ℓ "丘丞丏丑与与丽习举习丏丏丐与丘丞")
  (rw 0 q96 ∷
   rw 1 q97 ∷
   rw 2 q98 ∷
   rw 10 q99 ∷ []) Eq.refl

private
  q100 : Eqn
  q100 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))
  q101 : Eqn
  q101 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q102 : Eqn
  q102 = wE 391 W
  q103 : Eqn
  q103 = wE 392 W

-- b2g 1111R0: 5 steps
lem-b2g-1111R0 : ⟪ (ℓ "丌丒丘丞丈上中九丮九下三丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞") ⟫ʷ
lem-b2g-1111R0 = derive (ℓ "丌丒丘丞丈上中九丮九下三丌丒丘丞") (ℓ "丒丘丞三下丈丈中九丮九三三上丈丒丘丞")
  (rw 0 q100 ∷
   rw 1 q58 ∷
   rw 2 q101 ∷
   rw 3 q102 ∷
   rw 11 q103 ∷ []) Eq.refl

private
  q104 : Eqn
  q104 = wE 454 W

-- pass [X1 CSd10 X1] [TOFF012]: 1 steps
lem-pass-X1-CSd10-X1-vs-TOFF012 : ⟪ (ℓ "丒両丒九") ⟫ʷ ≈ ⟪ (ℓ "九丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-TOFF012 = derive (ℓ "丒両丒九") (ℓ "九丒両丒")
  (rw 0 q104 ∷ []) Eq.refl

private
  q105 : Eqn
  q105 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q106 : Eqn
  q106 = wE 455 W

-- pass [X1 CSd10 X1] [CS03]: 13 steps
lem-pass-X1-CSd10-X1-vs-CS03 : ⟪ (ℓ "丒両丒中") ⟫ʷ ≈ ⟪ (ℓ "中丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CS03 = derive (ℓ "丒両丒中") (ℓ "中丒両丒")
  (rw 4 q31 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q36 ∷
   rw 2 q105 ∷
   rw 1 q53 ∷
   rw 0 q105 ∷
   rw 1 q106 ∷
   rw 2 q31 ∷
   re 0 3 (ℓ "中") ∷
   rw⁻ 1 q105 ∷
   rw⁻ 2 q53 ∷
   rw⁻ 3 q105 ∷
   rw 4 q36 ∷ []) Eq.refl

private
  q107 : Eqn
  q107 = wE 456 W

-- pass [X1 CSd10 X1] [CSd03]: 13 steps
lem-pass-X1-CSd10-X1-vs-CSd03 : ⟪ (ℓ "丒両丒丮") ⟫ʷ ≈ ⟪ (ℓ "丮丒両丒") ⟫ʷ
lem-pass-X1-CSd10-X1-vs-CSd03 = derive (ℓ "丒両丒丮") (ℓ "丮丒両丒")
  (rw 4 q31 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q36 ∷
   rw 2 q105 ∷
   rw 1 q53 ∷
   rw 0 q105 ∷
   rw 1 q107 ∷
   rw 2 q31 ∷
   re 0 3 (ℓ "丮") ∷
   rw⁻ 1 q105 ∷
   rw⁻ 2 q53 ∷
   rw⁻ 3 q105 ∷
   rw 4 q36 ∷ []) Eq.refl

private
  q108 : Eqn
  q108 = wE 100 W
  q109 : Eqn
  q109 = wE 416 W
  q110 : Eqn
  q110 = wE 457 W
  q111 : Eqn
  q111 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q112 : Eqn
  q112 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q113 : Eqn
  q113 = wE 104 W

-- comm CCZ012 CSd23: 19 steps
lem-comm-CCZ012-CSd23 : ⟪ (ℓ "乙乊") ⟫ʷ ≈ ⟪ (ℓ "乊乙") ⟫ʷ
lem-comm-CCZ012-CSd23 = derive (ℓ "乙乊") (ℓ "乊乙")
  (rw 0 q108 ∷
   rw 4 q109 ∷
   rw 5 q1 ∷
   rw⁻ 4 q5 ∷
   rw 3 q50 ∷
   rw 4 q110 ∷
   rw 3 q5 ∷
   rw 4 q42 ∷
   rw 5 q9 ∷
   rw 2 q111 ∷
   rw 3 q1 ∷
   rw⁻ 2 q5 ∷
   rw 1 q50 ∷
   rw 2 q110 ∷
   rw 1 q5 ∷
   rw 2 q42 ∷
   rw 3 q9 ∷
   rw 0 q112 ∷
   rw 1 q113 ∷ []) Eq.refl
