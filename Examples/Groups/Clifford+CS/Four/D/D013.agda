{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D013 (W : Ws) where

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
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = wE 30 W
  q4 : Eqn
  q4 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 27 W
  q7 : Eqn
  q7 = wE 31 W
  q8 : Eqn
  q8 = wE 7 W
  q9 : Eqn
  q9 = wE 74 W
  q10 : Eqn
  q10 = wE 26 W
  q11 : Eqn
  q11 = wE 75 W
  q12 : Eqn
  q12 = wE 39 W
  q13 : Eqn
  q13 = wE 29 W
  q14 : Eqn
  q14 = wE 82 W
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = wE 3 W
  q17 : Eqn
  q17 = wE 261 W
  q18 : Eqn
  q18 = wE 21 W
  q19 : Eqn
  q19 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))
  q20 : Eqn
  q20 = wE 51 W
  q21 : Eqn
  q21 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q22 : Eqn
  q22 = wE 6 W
  q23 : Eqn
  q23 = wE 76 W
  q24 : Eqn
  q24 = wE 81 W
  q25 : Eqn
  q25 = wE 24 W
  q26 : Eqn
  q26 = wE 25 W

-- comm CCZ023 CSd13: 131 steps
lem-comm-CCZ023-CSd13 : ⟪ (ℓ "乛举") ⟫ʷ ≈ ⟪ (ℓ "举乛") ⟫ʷ
lem-comm-CCZ023-CSd13 = derive (ℓ "乛举") (ℓ "举乛")
  (rw 1 q1 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q11 ∷
   rw 0 q6 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 1 q5 ∷
   rw 2 q12 ∷
   rw 3 q5 ∷
   re 1 3 (ℓ "乐") ∷
   rw 2 q13 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 3 q5 ∷
   rw 4 q12 ∷
   rw 5 q5 ∷
   re 3 3 (ℓ "乐") ∷
   rw 4 q2 ∷
   rw 5 q7 ∷
   rw 4 q14 ∷
   rw 5 q15 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q16 ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   rw 5 q15 ∷
   re 3 3 (ℓ "举") ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "乐") ∷
   rw 5 q16 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q15 ∷
   re 3 3 (ℓ "丮") ∷
   re 3 1 (ℓ "乏丼両丼乏") ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "举") ∷
   rw 6 q18 ∷
   rw 5 q19 ∷
   rw 4 q20 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q16 ∷
   re 4 5 (ℓ "丮") ∷
   re 4 1 (ℓ "乏丨乏") ∷
   rw 6 q16 ∷
   re 2 3 (ℓ "举") ∷
   rw 3 q15 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q16 ∷
   re 1 1 (ℓ "乏乃乏") ∷
   rw 3 q16 ∷
   rw 2 q17 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "举") ∷
   rw 4 q15 ∷
   re 2 3 (ℓ "乐") ∷
   rw 3 q16 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q15 ∷
   re 1 3 (ℓ "中") ∷
   re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "举") ∷
   rw 4 q18 ∷
   rw 3 q21 ∷
   rw 2 q20 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q16 ∷
   re 2 5 (ℓ "中") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q16 ∷
   re 0 3 (ℓ "举") ∷
   rw 6 q1 ∷
   rw⁻ 5 q2 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q22 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "乓") ∷
   rw 3 q23 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw⁻ 4 q5 ∷
   rw 3 q22 ∷
   rw⁻ 2 q5 ∷
   re 3 3 (ℓ "乓") ∷
   rw 1 q8 ∷
   rw 2 q24 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q10 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 262 W

-- pass [CS03] [CSd03]: 11 steps
lem-pass-CS03-vs-CSd03 : ⟪ (ℓ "中丮") ⟫ʷ ≈ ⟪ (ℓ "丮中") ⟫ʷ
lem-pass-CS03-vs-CSd03 = derive (ℓ "中丮") (ℓ "丮中")
  (rw 2 q15 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q16 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q16 ∷
   rw 1 q27 ∷
   rw 2 q15 ∷
   re 0 3 (ℓ "丮") ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q29 : Eqn
  q29 = wE 263 W

-- pass [CS03] [S0 CSd03]: 13 steps
lem-pass-CS03-vs-S0-CSd03 : ⟪ (ℓ "中丈丮") ⟫ʷ ≈ ⟪ (ℓ "丈丮中") ⟫ʷ
lem-pass-CS03-vs-S0-CSd03 = derive (ℓ "中丈丮") (ℓ "丈丮中")
  (rw 3 q15 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q16 ∷
   rw 1 q28 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q16 ∷
   rw 1 q29 ∷
   rw⁻ 0 q28 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "丮") ∷
   rw 4 q15 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q16 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 183 W

-- pass [S0] [CS02]: 1 steps
lem-pass-S0-vs-CS02 : ⟪ (ℓ "丈丧") ⟫ʷ ≈ ⟪ (ℓ "丧丈") ⟫ʷ
lem-pass-S0-vs-CS02 = derive (ℓ "丈丧") (ℓ "丧丈")
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 184 W

-- pass [S0] [CSd02]: 1 steps
lem-pass-S0-vs-CSd02 : ⟪ (ℓ "丈丨") ⟫ʷ ≈ ⟪ (ℓ "丨丈") ⟫ʷ
lem-pass-S0-vs-CSd02 = derive (ℓ "丈丨") (ℓ "丨丈")
  (rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 163 W
  q33 : Eqn
  q33 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q34 : Eqn
  q34 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q35 : Eqn
  q35 = wE 245 W
  q36 : Eqn
  q36 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q37 : Eqn
  q37 = wE 264 W
  q38 : Eqn
  q38 = wE 166 W

-- comm CCZ023 CS01: 83 steps
lem-comm-CCZ023-CS01 : ⟪ (ℓ "乛丠") ⟫ʷ ≈ ⟪ (ℓ "丠乛") ⟫ʷ
lem-comm-CCZ023-CS01 = derive (ℓ "乛丠") (ℓ "丠乛")
  (rw 1 q1 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q32 ∷
   rw 0 q6 ∷
   rw 1 q33 ∷
   rw 2 q13 ∷
   rw 3 q33 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   rw 6 q15 ∷
   rw 5 q34 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q16 ∷
   rw 5 q35 ∷
   rw⁻ 4 q34 ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q16 ∷
   rw⁻ 3 q36 ∷
   rw 2 q37 ∷
   rw⁻ 1 q36 ∷
   rw 0 q35 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q5 ∷
   rw 6 q8 ∷
   rw⁻ 5 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 4 q33 ∷
   rw 3 q23 ∷
   rw⁻ 2 q33 ∷
   rw 1 q8 ∷
   rw 2 q38 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q10 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))

-- pass [CS23] [CS01]: 1 steps
lem-pass-CS23-vs-CS01 : ⟪ (ℓ "义丠") ⟫ʷ ≈ ⟪ (ℓ "丠义") ⟫ʷ
lem-pass-CS23-vs-CS01 = derive (ℓ "义丠") (ℓ "丠义")
  (rw⁻ 0 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = wE 265 W

-- pass [S0] [CS01]: 1 steps
lem-pass-S0-vs-CS01 : ⟪ (ℓ "丈丠") ⟫ʷ ≈ ⟪ (ℓ "丠丈") ⟫ʷ
lem-pass-S0-vs-CS01 = derive (ℓ "丈丠") (ℓ "丠丈")
  (rw 0 q40 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 266 W

-- pass [CCZ023] [CS23]: 51 steps
lem-pass-CCZ023-vs-CS23 : ⟪ (ℓ "乛义") ⟫ʷ ≈ ⟪ (ℓ "义乛") ⟫ʷ
lem-pass-CCZ023-vs-CS23 = derive (ℓ "乛义") (ℓ "义乛")
  (rw 2 q1 ∷
   rw⁻ 1 q2 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q41 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q10 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q42 : Eqn
  q42 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q43 : Eqn
  q43 = wE 267 W

-- pass [CCZ023] [CZ23]: 51 steps
lem-pass-CCZ023-vs-CZ23 : ⟪ (ℓ "乛之") ⟫ʷ ≈ ⟪ (ℓ "之乛") ⟫ʷ
lem-pass-CCZ023-vs-CZ23 = derive (ℓ "乛之") (ℓ "之乛")
  (rw 2 q1 ∷
   rw⁻ 1 q42 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q43 ∷
   rw 0 q42 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q10 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 268 W

-- pass [S0] [CSd01]: 1 steps
lem-pass-S0-vs-CSd01 : ⟪ (ℓ "丈両") ⟫ʷ ≈ ⟪ (ℓ "両丈") ⟫ʷ
lem-pass-S0-vs-CSd01 = derive (ℓ "丈両") (ℓ "両丈")
  (rw 0 q44 ∷ []) Eq.refl

-- pass [CSd23] [CS01]: 1 steps
lem-pass-CSd23-vs-CS01 : ⟪ (ℓ "乊丠") ⟫ʷ ≈ ⟪ (ℓ "丠乊") ⟫ʷ
lem-pass-CSd23-vs-CS01 = derive (ℓ "乊丠") (ℓ "丠乊")
  (rw⁻ 0 q21 ∷ []) Eq.refl

-- pass [CSd03] [CS01]: 9 steps
lem-pass-CSd03-vs-CS01 : ⟪ (ℓ "丮丠") ⟫ʷ ≈ ⟪ (ℓ "丠丮") ⟫ʷ
lem-pass-CSd03-vs-CS01 = derive (ℓ "丮丠") (ℓ "丠丮")
  (rw 2 q15 ∷
   rw 1 q34 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q16 ∷
   rw 1 q37 ∷
   rw⁻ 0 q34 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q16 ∷ []) Eq.refl

private
  q45 : Eqn
  q45 = wE 269 W

-- pass [CCZ023] [CSd23]: 51 steps
lem-pass-CCZ023-vs-CSd23 : ⟪ (ℓ "乛乊") ⟫ʷ ≈ ⟪ (ℓ "乊乛") ⟫ʷ
lem-pass-CCZ023-vs-CSd23 = derive (ℓ "乛乊") (ℓ "乊乛")
  (rw 2 q1 ∷
   rw⁻ 1 q4 ∷
   re 0 1 (ℓ "並乜並") ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q2 ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   rw 6 q5 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q5 ∷
   rw 5 q8 ∷
   rw⁻ 4 q5 ∷
   re 5 3 (ℓ "丽") ∷
   rw 3 q9 ∷
   rw⁻ 2 q4 ∷
   rw 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q10 ∷
   re 1 5 (ℓ "乜") ∷
   rw 1 q45 ∷
   rw 0 q4 ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q2 ∷
   rw 2 q3 ∷
   rw 3 q4 ∷
   rw 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 6 q6 ∷
   rw 7 q5 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q1 ∷
   rw 2 q2 ∷
   rw 3 q25 ∷
   rw 4 q4 ∷
   rw 5 q25 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 7 q26 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "丽") ∷
   rw 2 q10 ∷
   re 2 5 (ℓ "乜") ∷
   re 1 3 (ℓ "乛") ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q46 : Eqn
  q46 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q47 : Eqn
  q47 = wE 270 W

-- pass [CSd03] [CSd01]: 9 steps
lem-pass-CSd03-vs-CSd01 : ⟪ (ℓ "丮両") ⟫ʷ ≈ ⟪ (ℓ "両丮") ⟫ʷ
lem-pass-CSd03-vs-CSd01 = derive (ℓ "丮両") (ℓ "両丮")
  (rw 2 q15 ∷
   rw 1 q46 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q16 ∷
   rw 1 q47 ∷
   rw⁻ 0 q46 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q16 ∷ []) Eq.refl
