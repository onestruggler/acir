{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D009 (W : Ws) where

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
  q1 = wE 65 W
  q2 : Eqn
  q2 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q3 : Eqn
  q3 = wE 48 W

-- pass [CS13] [CS02]: 5 steps
lem-pass-CS13-vs-CS02 : ⟪ (ℓ "丽丧") ⟫ʷ ≈ ⟪ (ℓ "丧丽") ⟫ʷ
lem-pass-CS13-vs-CS02 = derive (ℓ "丽丧") (ℓ "丧丽")
  (re 1 1 (ℓ "丼丠丼") ∷
   rw 0 q1 ∷
   rw⁻ 1 q2 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "丧") ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 1 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q7 : Eqn
  q7 = wE 43 W
  q8 : Eqn
  q8 = wE 177 W

-- pass [CCZ013] [CS13]: 49 steps
lem-pass-CCZ013-vs-CS13 : ⟪ (ℓ "乚丽") ⟫ʷ ≈ ⟪ (ℓ "丽乚") ⟫ʷ
lem-pass-CCZ013-vs-CS13 = derive (ℓ "乚丽") (ℓ "丽乚")
  (rw 2 q4 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q6 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 3 q6 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw 1 q6 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q8 ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丽") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q6 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 2 q7 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 187 W

-- pass [TOFF012] [X1 X2 TOFF012 X1 X2]: 1 steps
lem-pass-TOFF012-vs-X1-X2-TOFF012-X1-X2 : ⟪ (ℓ "九丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘九") ⟫ʷ
lem-pass-TOFF012-vs-X1-X2-TOFF012-X1-X2 = derive (ℓ "九丒丘九丒丘") (ℓ "丒丘九丒丘九")
  (rw 0 q9 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = eqn (ℓ "不乏") (ℓ "乏不") (low₁-comm (Z) ((Swap ↑)))
  q11 : Eqn
  q11 = wE 188 W

-- pass [CCZ013] [Z0]: 47 steps
lem-pass-CCZ013-vs-Z0 : ⟪ (ℓ "乚不") ⟫ʷ ≈ ⟪ (ℓ "不乚") ⟫ʷ
lem-pass-CCZ013-vs-Z0 = derive (ℓ "乚不") (ℓ "不乚")
  (rw 2 q4 ∷
   rw 1 q10 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q6 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 3 q6 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw 1 q6 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q11 ∷
   rw⁻ 0 q10 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q6 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 2 q7 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 85 W
  q13 : Eqn
  q13 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q14 : Eqn
  q14 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = wE 189 W
  q17 : Eqn
  q17 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = wE 190 W
  q20 : Eqn
  q20 = wE 191 W
  q21 : Eqn
  q21 = wE 27 W
  q22 : Eqn
  q22 = wE 31 W
  q23 : Eqn
  q23 = wE 13 W
  q24 : Eqn
  q24 = eqn (ℓ "丢乖") (ℓ "乖丢") (low-comm (CZ) (CX₁₀))
  q25 : Eqn
  q25 = wE 78 W
  q26 : Eqn
  q26 = wE 192 W
  q27 : Eqn
  q27 = wE 193 W
  q28 : Eqn
  q28 = wE 89 W

-- comm CCZ013 CZ02: 91 steps
lem-comm-CCZ013-CZ02 : ⟪ (ℓ "乚丩") ⟫ʷ ≈ ⟪ (ℓ "丩乚") ⟫ʷ
lem-comm-CCZ013-CZ02 = derive (ℓ "乚丩") (ℓ "丩乚")
  (rw 1 q4 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q6 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 3 q6 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw 1 q6 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q12 ∷
   rw⁻ 0 q13 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "乓") ∷
   rw⁻ 2 q14 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "乓") ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q5 ∷
   rw 6 q15 ∷
   rw 5 q16 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q17 ∷
   rw 5 q18 ∷
   rw⁻ 4 q17 ∷
   re 5 3 (ℓ "丽") ∷
   rw 5 q19 ∷
   rw 4 q20 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q17 ∷
   rw 6 q21 ∷
   rw 7 q17 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q22 ∷
   re 4 1 (ℓ "丼丢丼") ∷
   rw 3 q23 ∷
   rw⁻ 4 q24 ∷
   rw 5 q25 ∷
   re 3 3 (ℓ "丩") ∷
   rw 2 q26 ∷
   re 2 1 (ℓ "丼丢丼") ∷
   rw 1 q23 ∷
   rw⁻ 2 q24 ∷
   rw 3 q25 ∷
   re 1 3 (ℓ "丩") ∷
   rw 0 q27 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏乆乏") ∷
   rw 6 q5 ∷
   rw 3 q14 ∷
   re 2 1 (ℓ "乏乆乏") ∷
   rw 4 q5 ∷
   rw 1 q13 ∷
   rw 2 q28 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q6 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 2 q7 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 194 W

-- pass [CS02] [X1 X2 TOFF012 X1 X2]: 1 steps
lem-pass-CS02-vs-X1-X2-TOFF012-X1-X2 : ⟪ (ℓ "丧丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘丧") ⟫ʷ
lem-pass-CS02-vs-X1-X2-TOFF012-X1-X2 = derive (ℓ "丧丒丘九丒丘") (ℓ "丒丘九丒丘丧")
  (rw 0 q29 ∷ []) Eq.refl

private
  q30 : Eqn
  q30 = wE 195 W

-- pass [CSd02] [X1 X2 TOFF012 X1 X2]: 1 steps
lem-pass-CSd02-vs-X1-X2-TOFF012-X1-X2 : ⟪ (ℓ "丨丒丘九丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘九丒丘丨") ⟫ʷ
lem-pass-CSd02-vs-X1-X2-TOFF012-X1-X2 = derive (ℓ "丨丒丘九丒丘") (ℓ "丒丘九丒丘丨")
  (rw 0 q30 ∷ []) Eq.refl

private
  q31 : Eqn
  q31 = wE 173 W
  q32 : Eqn
  q32 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q33 : Eqn
  q33 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q34 : Eqn
  q34 = wE 56 W
  q35 : Eqn
  q35 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q36 : Eqn
  q36 = wE 196 W
  q37 : Eqn
  q37 = wE 197 W
  q38 : Eqn
  q38 = wE 175 W

-- pass [TOFF103] [X3 TOFF013 X3]: 115 steps
lem-pass-TOFF103-vs-X3-TOFF013-X3 : ⟪ (ℓ "乡丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞乡") ⟫ʷ
lem-pass-TOFF103-vs-X3-TOFF013-X3 = derive (ℓ "乡丞乞丞") (ℓ "丞乞丞乡")
  (rw 4 q4 ∷
   rw 3 q31 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q32 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q6 ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q32 ∷
   rw⁻ 9 q33 ∷
   rw 10 q5 ∷
   rw 9 q33 ∷
   rw 8 q32 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw 6 q6 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw 4 q6 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 2 q32 ∷
   rw 3 q34 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q31 ∷
   re 0 1 (ℓ "乏习乏") ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q35 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q35 ∷
   rw⁻ 7 q33 ∷
   rw 8 q5 ∷
   rw 7 q33 ∷
   rw 6 q35 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 4 q6 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw 2 q6 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 1 8 (ℓ "习") ∷
   rw 1 q37 ∷
   rw 0 q38 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q32 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q6 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q32 ∷
   rw⁻ 8 q33 ∷
   rw 1 q4 ∷
   rw⁻ 2 q32 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw⁻ 4 q6 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q32 ∷
   rw⁻ 9 q33 ∷
   rw 2 q34 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q38 ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q35 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q6 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q6 ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q35 ∷
   rw⁻ 10 q33 ∷
   rw 3 q4 ∷
   rw⁻ 4 q35 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw⁻ 6 q6 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q6 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q35 ∷
   rw⁻ 11 q33 ∷
   rw 4 q36 ∷
   re 4 8 (ℓ "习") ∷
   re 3 3 (ℓ "乡") ∷
   rw 4 q5 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = wE 100 W
  q40 : Eqn
  q40 = wE 198 W
  q41 : Eqn
  q41 = wE 21 W
  q42 : Eqn
  q42 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q43 : Eqn
  q43 = wE 51 W
  q44 : Eqn
  q44 = wE 199 W
  q45 : Eqn
  q45 = wE 200 W
  q46 : Eqn
  q46 = wE 104 W

-- comm CCZ013 CSd12: 85 steps
lem-comm-CCZ013-CSd12 : ⟪ (ℓ "乚丷") ⟫ʷ ≈ ⟪ (ℓ "丷乚") ⟫ʷ
lem-comm-CCZ013-CSd12 = derive (ℓ "乚丷") (ℓ "丷乚")
  (rw 1 q4 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q6 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q6 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 3 q6 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw 1 q6 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q7 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q39 ∷
   rw⁻ 0 q13 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "乐") ∷
   rw⁻ 2 q14 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "乐") ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q5 ∷
   rw 4 q40 ∷
   re 3 1 (ℓ "乏丼丳丼乏") ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "举") ∷
   rw 6 q41 ∷
   rw 5 q42 ∷
   rw 4 q43 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   re 4 5 (ℓ "乐") ∷
   rw 2 q44 ∷
   re 1 1 (ℓ "乏丼丳丼乏") ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "举") ∷
   rw 4 q41 ∷
   rw 3 q42 ∷
   rw 2 q43 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q5 ∷
   re 2 5 (ℓ "乐") ∷
   rw 0 q45 ∷
   rw 6 q4 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏乃乏") ∷
   rw 6 q5 ∷
   rw 3 q14 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw 4 q5 ∷
   rw 1 q13 ∷
   rw 2 q46 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw⁻ 3 q6 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 2 q7 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 20 W
  q48 : Eqn
  q48 = eqn (ℓ "両义") (ℓ "义両") (low-comm ((CS • CS • CS)) (CS))
  q49 : Eqn
  q49 = wE 49 W

-- pass [CSd02] [CS13]: 15 steps
lem-pass-CSd02-vs-CS13 : ⟪ (ℓ "丨丽") ⟫ʷ ≈ ⟪ (ℓ "丽丨") ⟫ʷ
lem-pass-CSd02-vs-CS13 = derive (ℓ "丨丽") (ℓ "丽丨")
  (re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q4 ∷
   re 1 3 (ℓ "丮") ∷
   re 1 1 (ℓ "乏丼両丼乏") ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "丽") ∷
   rw 4 q47 ∷
   rw 3 q48 ∷
   rw 2 q49 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q5 ∷
   re 2 5 (ℓ "丮") ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q5 ∷
   re 0 3 (ℓ "丽") ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = eqn (ℓ "両乊") (ℓ "乊両") (low-comm ((CS • CS • CS)) ((CS • CS • CS)))

-- pass [CSd02] [CSd13]: 15 steps
lem-pass-CSd02-vs-CSd13 : ⟪ (ℓ "丨举") ⟫ʷ ≈ ⟪ (ℓ "举丨") ⟫ʷ
lem-pass-CSd02-vs-CSd13 = derive (ℓ "丨举") (ℓ "举丨")
  (re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q4 ∷
   re 1 3 (ℓ "丮") ∷
   re 1 1 (ℓ "乏丼両丼乏") ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "举") ∷
   rw 4 q41 ∷
   rw 3 q50 ∷
   rw 2 q43 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q5 ∷
   re 2 5 (ℓ "丮") ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q5 ∷
   re 0 3 (ℓ "举") ∷ []) Eq.refl

-- pass [TOFF102] [X2 TOFF012 X2]: 1 steps
lem-pass-TOFF102-vs-X2-TOFF012-X2 : ⟪ (ℓ "习丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘习") ⟫ʷ
lem-pass-TOFF102-vs-X2-TOFF012-X2 = derive (ℓ "习丘九丘") (ℓ "丘九丘习")
  (rw 0 q37 ∷ []) Eq.refl

private
  q51 : Eqn
  q51 = wE 201 W

-- pass [TOFF102] [S0]: 1 steps
lem-pass-TOFF102-vs-S0 : ⟪ (ℓ "习丈") ⟫ʷ ≈ ⟪ (ℓ "丈习") ⟫ʷ
lem-pass-TOFF102-vs-S0 = derive (ℓ "习丈") (ℓ "丈习")
  (rw 0 q51 ∷ []) Eq.refl

private
  q52 : Eqn
  q52 = wE 202 W

-- pass [TOFF102] [Sd0]: 1 steps
lem-pass-TOFF102-vs-Sd0 : ⟪ (ℓ "习三") ⟫ʷ ≈ ⟪ (ℓ "三习") ⟫ʷ
lem-pass-TOFF102-vs-Sd0 = derive (ℓ "习三") (ℓ "三习")
  (rw 0 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 93 W
  q54 : Eqn
  q54 = eqn (ℓ "丳义") (ℓ "义丳") (low-comm (CX₁₀) (CS))
  q55 : Eqn
  q55 = wE 102 W
  q56 : Eqn
  q56 = wE 103 W

-- comm CCZ012 CS13: 51 steps
lem-comm-CCZ012-CS13 : ⟪ (ℓ "乙丽") ⟫ʷ ≈ ⟪ (ℓ "丽乙") ⟫ʷ
lem-comm-CCZ012-CS13 = derive (ℓ "乙丽") (ℓ "丽乙")
  (rw 0 q39 ∷
   rw 4 q53 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   re 4 3 (ℓ "乐") ∷
   re 4 1 (ℓ "乏丼丳丼乏") ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "丽") ∷
   rw 7 q47 ∷
   rw 6 q54 ∷
   rw 5 q49 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   re 5 5 (ℓ "乐") ∷
   re 5 1 (ℓ "乏乃乏") ∷
   rw 7 q5 ∷
   re 3 3 (ℓ "丽") ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q5 ∷
   rw 2 q14 ∷
   rw 3 q55 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q14 ∷
   rw 4 q5 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q4 ∷
   re 2 3 (ℓ "乐") ∷
   re 2 1 (ℓ "乏丼丳丼乏") ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "丽") ∷
   rw 5 q47 ∷
   rw 4 q54 ∷
   rw 3 q49 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   re 3 5 (ℓ "乐") ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw 5 q5 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q4 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw 0 q13 ∷
   rw 1 q56 ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q13 ∷
   rw 2 q5 ∷
   rw 1 q46 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q58 : Eqn
  q58 = wE 203 W

-- pass [CS13] [S0]: 9 steps
lem-pass-CS13-vs-S0 : ⟪ (ℓ "丽丈") ⟫ʷ ≈ ⟪ (ℓ "丈丽") ⟫ʷ
lem-pass-CS13-vs-S0 = derive (ℓ "丽丈") (ℓ "丈丽")
  (rw 2 q4 ∷
   rw 1 q57 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q58 ∷
   rw⁻ 0 q57 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 80 W

-- pass [CS13] [CSd03]: 11 steps
lem-pass-CS13-vs-CSd03 : ⟪ (ℓ "丽丮") ⟫ʷ ≈ ⟪ (ℓ "丮丽") ⟫ʷ
lem-pass-CS13-vs-CSd03 = derive (ℓ "丽丮") (ℓ "丮丽")
  (rw 2 q4 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q59 ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丮") ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q60 : Eqn
  q60 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q61 : Eqn
  q61 = wE 204 W

-- pass [CS13] [Sd0]: 9 steps
lem-pass-CS13-vs-Sd0 : ⟪ (ℓ "丽三") ⟫ʷ ≈ ⟪ (ℓ "三丽") ⟫ʷ
lem-pass-CS13-vs-Sd0 = derive (ℓ "丽三") (ℓ "三丽")
  (rw 2 q4 ∷
   rw 1 q60 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q61 ∷
   rw⁻ 0 q60 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q62 : Eqn
  q62 = wE 205 W

-- pass [CS13] [CS03]: 11 steps
lem-pass-CS13-vs-CS03 : ⟪ (ℓ "丽中") ⟫ʷ ≈ ⟪ (ℓ "中丽") ⟫ʷ
lem-pass-CS13-vs-CS03 = derive (ℓ "丽中") (ℓ "中丽")
  (rw 2 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q5 ∷
   rw 1 q62 ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q63 : Eqn
  q63 = wE 86 W

-- comm CCZ012 CSd13: 51 steps
lem-comm-CCZ012-CSd13 : ⟪ (ℓ "乙举") ⟫ʷ ≈ ⟪ (ℓ "举乙") ⟫ʷ
lem-comm-CCZ012-CSd13 = derive (ℓ "乙举") (ℓ "举乙")
  (rw 0 q39 ∷
   rw 4 q63 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 3 q4 ∷
   re 4 3 (ℓ "乐") ∷
   re 4 1 (ℓ "乏丼丳丼乏") ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "举") ∷
   rw 7 q41 ∷
   rw 6 q42 ∷
   rw 5 q43 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   re 5 5 (ℓ "乐") ∷
   re 5 1 (ℓ "乏乃乏") ∷
   rw 7 q5 ∷
   re 3 3 (ℓ "举") ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw 2 q14 ∷
   rw 3 q44 ∷
   rw 4 q4 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q14 ∷
   rw 4 q5 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q4 ∷
   re 2 3 (ℓ "乐") ∷
   re 2 1 (ℓ "乏丼丳丼乏") ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "举") ∷
   rw 5 q41 ∷
   rw 4 q42 ∷
   rw 3 q43 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 2 q5 ∷
   re 3 5 (ℓ "乐") ∷
   re 3 1 (ℓ "乏乃乏") ∷
   rw 5 q5 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q4 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   rw 0 q13 ∷
   rw 1 q45 ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "举") ∷
   rw⁻ 1 q13 ∷
   rw 2 q5 ∷
   rw 1 q46 ∷ []) Eq.refl

private
  q64 : Eqn
  q64 = wE 206 W

-- pass [CSd13] [S0]: 9 steps
lem-pass-CSd13-vs-S0 : ⟪ (ℓ "举丈") ⟫ʷ ≈ ⟪ (ℓ "丈举") ⟫ʷ
lem-pass-CSd13-vs-S0 = derive (ℓ "举丈") (ℓ "丈举")
  (rw 2 q4 ∷
   rw 1 q57 ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q5 ∷
   rw 1 q64 ∷
   rw⁻ 0 q57 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 79 W

-- pass [CSd13] [CSd03]: 11 steps
lem-pass-CSd13-vs-CSd03 : ⟪ (ℓ "举丮") ⟫ʷ ≈ ⟪ (ℓ "丮举") ⟫ʷ
lem-pass-CSd13-vs-CSd03 = derive (ℓ "举丮") (ℓ "丮举")
  (rw 2 q4 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q5 ∷
   rw 1 q65 ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "丮") ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 207 W

-- pass [CSd13] [Sd0]: 9 steps
lem-pass-CSd13-vs-Sd0 : ⟪ (ℓ "举三") ⟫ʷ ≈ ⟪ (ℓ "三举") ⟫ʷ
lem-pass-CSd13-vs-Sd0 = derive (ℓ "举三") (ℓ "三举")
  (rw 2 q4 ∷
   rw 1 q60 ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q5 ∷
   rw 1 q66 ∷
   rw⁻ 0 q60 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q67 : Eqn
  q67 = wE 208 W

-- pass [CSd13] [CS03]: 11 steps
lem-pass-CSd13-vs-CS03 : ⟪ (ℓ "举中") ⟫ʷ ≈ ⟪ (ℓ "中举") ⟫ʷ
lem-pass-CSd13-vs-CS03 = derive (ℓ "举中") (ℓ "中举")
  (rw 2 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏丷乏") ∷
   rw 2 q5 ∷
   rw 1 q67 ∷
   rw 2 q4 ∷
   re 0 3 (ℓ "中") ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q68 : Eqn
  q68 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q69 : Eqn
  q69 = wE 209 W

-- pass [TOFF103] [X1 X3 TOFF013 X1 X3]: 119 steps
lem-pass-TOFF103-vs-X1-X3-TOFF013-X1-X3 : ⟪ (ℓ "乡丒丞乞丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞乞丒丞乡") ⟫ʷ
lem-pass-TOFF103-vs-X1-X3-TOFF013-X1-X3 = derive (ℓ "乡丒丞乞丒丞") (ℓ "丒丞乞丒丞乡")
  (rw 6 q4 ∷
   rw 5 q31 ∷
   rw 4 q68 ∷
   re 3 1 (ℓ "乏九乏") ∷
   re 4 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 3 q32 ∷
   rw 6 q4 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q6 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q6 ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q32 ∷
   rw⁻ 10 q33 ∷
   rw 11 q5 ∷
   rw 10 q33 ∷
   rw 9 q32 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q5 ∷
   rw 7 q6 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   rw 5 q6 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 3 q32 ∷
   rw 4 q34 ∷
   re 4 8 (ℓ "九") ∷
   rw 2 q31 ∷
   rw 1 q68 ∷
   re 0 1 (ℓ "乏习乏") ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q35 ∷
   rw 3 q4 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q6 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q35 ∷
   rw⁻ 7 q33 ∷
   rw 8 q5 ∷
   rw 7 q33 ∷
   rw 6 q35 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 4 q6 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   rw 2 q6 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q5 ∷
   rw 0 q35 ∷
   rw 1 q36 ∷
   re 1 8 (ℓ "习") ∷
   rw 1 q69 ∷
   rw⁻ 0 q68 ∷
   rw 1 q38 ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q32 ∷
   rw 5 q4 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q6 ∷
   rw 7 q4 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q6 ∷
   rw 9 q4 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q32 ∷
   rw⁻ 9 q33 ∷
   rw 2 q4 ∷
   rw⁻ 3 q32 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q5 ∷
   rw⁻ 5 q6 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   rw⁻ 7 q6 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q5 ∷
   rw⁻ 9 q32 ∷
   rw⁻ 10 q33 ∷
   rw 3 q34 ∷
   re 3 8 (ℓ "九") ∷
   re 2 3 (ℓ "乞") ∷
   rw⁻ 3 q68 ∷
   rw 4 q38 ∷
   re 6 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 5 q35 ∷
   rw 8 q4 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q6 ∷
   rw 10 q4 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q6 ∷
   rw 12 q4 ∷
   re 10 3 (ℓ "中") ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q33 ∷
   rw 5 q4 ∷
   rw⁻ 6 q35 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q5 ∷
   rw⁻ 8 q6 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   rw⁻ 10 q6 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   rw⁻ 12 q35 ∷
   rw⁻ 13 q33 ∷
   rw 6 q36 ∷
   re 6 8 (ℓ "习") ∷
   re 5 3 (ℓ "乡") ∷
   rw 6 q5 ∷ []) Eq.refl

private
  q70 : Eqn
  q70 = wE 210 W

-- pass [S2] [CS13]: 1 steps
lem-pass-S2-vs-CS13 : ⟪ (ℓ "且丽") ⟫ʷ ≈ ⟪ (ℓ "丽且") ⟫ʷ
lem-pass-S2-vs-CS13 = derive (ℓ "且丽") (ℓ "丽且")
  (rw 0 q70 ∷ []) Eq.refl

private
  q71 : Eqn
  q71 = wE 211 W

-- pass [S2] [CSd13]: 1 steps
lem-pass-S2-vs-CSd13 : ⟪ (ℓ "且举") ⟫ʷ ≈ ⟪ (ℓ "举且") ⟫ʷ
lem-pass-S2-vs-CSd13 = derive (ℓ "且举") (ℓ "举且")
  (rw 0 q71 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 212 W

-- pass [Sd2] [CS13]: 1 steps
lem-pass-Sd2-vs-CS13 : ⟪ (ℓ "丕丽") ⟫ʷ ≈ ⟪ (ℓ "丽丕") ⟫ʷ
lem-pass-Sd2-vs-CS13 = derive (ℓ "丕丽") (ℓ "丽丕")
  (rw 0 q72 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = wE 213 W

-- pass [Sd2] [CSd13]: 1 steps
lem-pass-Sd2-vs-CSd13 : ⟪ (ℓ "丕举") ⟫ʷ ≈ ⟪ (ℓ "举丕") ⟫ʷ
lem-pass-Sd2-vs-CSd13 = derive (ℓ "丕举") (ℓ "举丕")
  (rw 0 q73 ∷ []) Eq.refl

private
  q74 : Eqn
  q74 = wE 96 W
  q75 : Eqn
  q75 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q76 : Eqn
  q76 = wE 97 W

-- pass [CZ12] [CS03]: 9 steps
lem-pass-CZ12-vs-CS03 : ⟪ (ℓ "丸中") ⟫ʷ ≈ ⟪ (ℓ "中丸") ⟫ʷ
lem-pass-CZ12-vs-CS03 = derive (ℓ "丸中") (ℓ "中丸")
  (re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 0 q4 ∷
   re 1 3 (ℓ "丿") ∷
   rw 1 q74 ∷
   rw⁻ 2 q75 ∷
   rw 3 q76 ∷
   re 4 1 (ℓ "乏丸乏") ∷
   rw 6 q5 ∷
   re 0 5 (ℓ "中") ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 214 W

-- pass [CCZ012] [Sd0]: 1 steps
lem-pass-CCZ012-vs-Sd0 : ⟪ (ℓ "乙三") ⟫ʷ ≈ ⟪ (ℓ "三乙") ⟫ʷ
lem-pass-CCZ012-vs-Sd0 = derive (ℓ "乙三") (ℓ "三乙")
  (rw 0 q77 ∷ []) Eq.refl

-- pass [CS12] [Sd0]: 1 steps
lem-pass-CS12-vs-Sd0 : ⟪ (ℓ "丶三") ⟫ʷ ≈ ⟪ (ℓ "三丶") ⟫ʷ
lem-pass-CS12-vs-Sd0 = derive (ℓ "丶三") (ℓ "三丶")
  (rw 0 q61 ∷ []) Eq.refl
