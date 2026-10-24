{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D008 (W : Ws) where

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
  q1 = wE 148 W
  q2 : Eqn
  q2 = wE 149 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = eqn (ℓ "上乏") (ℓ "乏上") (low₁-comm (K) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "三乏") (ℓ "乏三") (low₁-comm ((S • S • S)) ((Swap ↑)))
  q6 : Eqn
  q6 = eqn (ℓ "下乏") (ℓ "乏下") (low₁-comm ((K • iI)) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = eqn (ℓ "丈乏") (ℓ "乏丈") (low₁-comm (S) ((Swap ↑)))
  q9 : Eqn
  q9 = wE 150 W
  q10 : Eqn
  q10 = wE 151 W
  q11 : Eqn
  q11 = wE 152 W
  q12 : Eqn
  q12 = wE 153 W
  q13 : Eqn
  q13 = eqn (ℓ "九业") (ℓ "业九") (low₃-comm (Toff) (S))
  q14 : Eqn
  q14 = wE 154 W
  q15 : Eqn
  q15 = wE 155 W
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = wE 140 W
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = wE 137 W
  q20 : Eqn
  q20 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q21 : Eqn
  q21 = wE 6 W
  q22 : Eqn
  q22 = wE 156 W
  q23 : Eqn
  q23 = wE 139 W
  q24 : Eqn
  q24 = wE 27 W
  q25 : Eqn
  q25 = wE 142 W
  q26 : Eqn
  q26 = wE 39 W
  q27 : Eqn
  q27 = wE 31 W
  q28 : Eqn
  q28 = wE 157 W
  q29 : Eqn
  q29 = eqn (ℓ "丳乌") (ℓ "乌丳") (low-comm (CX₁₀) (CX₀₁))
  q30 : Eqn
  q30 = wE 158 W
  q31 : Eqn
  q31 = wE 76 W
  q32 : Eqn
  q32 = wE 159 W
  q33 : Eqn
  q33 = wE 29 W
  q34 : Eqn
  q34 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q35 : Eqn
  q35 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q36 : Eqn
  q36 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q37 : Eqn
  q37 = wE 160 W
  q38 : Eqn
  q38 = wE 161 W
  q39 : Eqn
  q39 = wE 162 W

-- PU: 117 steps
lem-PU : ⟪ (ℓ "下丈上九中九丮下三上") ⟫ʷ ≈ ⟪ (ℓ "九乑九乒") ⟫ʷ
lem-PU = derive (ℓ "下丈上九中九丮下三上") (ℓ "九乑九乒")
  (rw 6 q1 ∷
   rw 5 q1 ∷
   rw 4 q1 ∷
   rw 0 q2 ∷
   rw 8 q3 ∷
   rw 7 q4 ∷
   rw 6 q5 ∷
   rw 5 q6 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 3 q4 ∷
   rw 2 q8 ∷
   rw 1 q6 ∷
   rw 2 q9 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "乑") ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "乐") ∷
   rw 3 q10 ∷
   rw 4 q7 ∷
   rw 4 q2 ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   rw 10 q5 ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q7 ∷
   rw 7 q4 ∷
   rw 6 q8 ∷
   rw 5 q6 ∷
   rw 6 q11 ∷
   rw 5 q12 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乐") ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "乒") ∷
   rw 8 q7 ∷
   rw⁻ 3 q13 ∷
   rw 4 q14 ∷
   rw 3 q15 ∷
   rw 6 q16 ∷
   rw 5 q17 ∷
   rw 4 q18 ∷
   rw 3 q19 ∷
   re 2 1 (ℓ "乏乃乏") ∷
   rw⁻ 4 q20 ∷
   rw 3 q21 ∷
   rw⁻ 2 q20 ∷
   re 3 3 (ℓ "乓") ∷
   rw 3 q22 ∷
   rw 2 q23 ∷
   rw 3 q24 ∷
   rw 4 q25 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 5 q20 ∷
   rw 6 q26 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "乐") ∷
   rw 6 q27 ∷
   re 5 1 (ℓ "乏丼丳丼乏") ∷
   rw 11 q3 ∷
   re 9 3 (ℓ "乀") ∷
   rw 8 q28 ∷
   rw 7 q29 ∷
   rw 6 q30 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 5 q7 ∷
   re 6 5 (ℓ "乐") ∷
   rw 10 q16 ∷
   rw 9 q17 ∷
   rw 8 q31 ∷
   rw 7 q19 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q20 ∷
   rw 7 q21 ∷
   rw⁻ 6 q20 ∷
   re 7 3 (ℓ "乓") ∷
   rw 7 q32 ∷
   rw 6 q23 ∷
   rw 7 q33 ∷
   rw 8 q25 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q20 ∷
   rw 10 q26 ∷
   rw 11 q20 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q27 ∷
   re 9 1 (ℓ "乏丼丳丼乏") ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "乀") ∷
   rw 12 q28 ∷
   rw 11 q29 ∷
   rw 10 q30 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 9 q7 ∷
   re 10 5 (ℓ "乐") ∷
   rw 14 q3 ∷
   rw 13 q34 ∷
   rw 12 q35 ∷
   rw 11 q36 ∷
   re 10 1 (ℓ "乏乃乏") ∷
   rw 12 q7 ∷
   rw 11 q37 ∷
   rw⁻ 10 q36 ∷
   rw⁻ 11 q35 ∷
   rw⁻ 12 q34 ∷
   rw 15 q3 ∷
   re 13 3 (ℓ "乐") ∷
   rw 14 q7 ∷
   rw 15 q3 ∷
   re 14 1 (ℓ "乏乃乏") ∷
   rw 16 q7 ∷
   re 13 1 (ℓ "乏乃乏") ∷
   rw 15 q7 ∷
   rw 14 q38 ∷
   rw 13 q7 ∷
   rw 2 q39 ∷ []) Eq.refl

-- PUinv: 117 steps
lem-PUinv : ⟪ (ℓ "下丈上中九丮九下三上") ⟫ʷ ≈ ⟪ (ℓ "乑九乒九") ⟫ʷ
lem-PUinv = derive (ℓ "下丈上中九丮九下三上") (ℓ "乑九乒九")
  (rw 6 q1 ∷
   rw 5 q1 ∷
   rw 4 q1 ∷
   rw 7 q3 ∷
   rw 6 q4 ∷
   rw 5 q5 ∷
   rw 4 q6 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   rw 2 q4 ∷
   rw 1 q8 ∷
   rw 0 q6 ∷
   rw 1 q9 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "乑") ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "乐") ∷
   rw 2 q10 ∷
   rw 3 q7 ∷
   rw 3 q2 ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   rw 8 q6 ∷
   re 7 1 (ℓ "乏丨乏") ∷
   rw 9 q7 ∷
   rw 6 q4 ∷
   rw 5 q8 ∷
   rw 4 q6 ∷
   rw 5 q11 ∷
   rw 4 q12 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "乐") ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乒") ∷
   rw 7 q7 ∷
   rw 7 q2 ∷
   rw⁻ 2 q13 ∷
   rw 3 q14 ∷
   rw 2 q15 ∷
   rw 5 q16 ∷
   rw 4 q17 ∷
   rw 3 q18 ∷
   rw 2 q19 ∷
   re 1 1 (ℓ "乏乃乏") ∷
   rw⁻ 3 q20 ∷
   rw 2 q21 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (ℓ "乓") ∷
   rw 2 q22 ∷
   rw 1 q23 ∷
   rw 2 q24 ∷
   rw 3 q25 ∷
   re 5 1 (ℓ "乏乆乏") ∷
   rw 4 q20 ∷
   rw 5 q26 ∷
   rw 6 q20 ∷
   re 4 3 (ℓ "乐") ∷
   rw 5 q27 ∷
   re 4 1 (ℓ "乏丼丳丼乏") ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "乀") ∷
   rw 7 q28 ∷
   rw 6 q29 ∷
   rw 5 q30 ∷
   re 5 1 (ℓ "乏丹乏") ∷
   rw 4 q7 ∷
   re 5 5 (ℓ "乐") ∷
   rw 9 q16 ∷
   rw 8 q17 ∷
   rw 7 q31 ∷
   rw 6 q19 ∷
   re 5 1 (ℓ "乏乃乏") ∷
   rw⁻ 7 q20 ∷
   rw 6 q21 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (ℓ "乓") ∷
   rw 6 q32 ∷
   rw 5 q23 ∷
   rw 6 q33 ∷
   rw 7 q25 ∷
   re 9 1 (ℓ "乏乆乏") ∷
   rw 8 q20 ∷
   rw 9 q26 ∷
   rw 10 q20 ∷
   re 8 3 (ℓ "乐") ∷
   rw 9 q27 ∷
   re 8 1 (ℓ "乏丼丳丼乏") ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "乀") ∷
   rw 11 q28 ∷
   rw 10 q29 ∷
   rw 9 q30 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 8 q7 ∷
   re 9 5 (ℓ "乐") ∷
   rw 13 q3 ∷
   rw 12 q34 ∷
   rw 11 q35 ∷
   rw 10 q36 ∷
   re 9 1 (ℓ "乏乃乏") ∷
   rw 11 q7 ∷
   rw 10 q37 ∷
   rw⁻ 9 q36 ∷
   rw⁻ 10 q35 ∷
   rw⁻ 11 q34 ∷
   rw 14 q3 ∷
   re 12 3 (ℓ "乐") ∷
   rw 13 q7 ∷
   rw 14 q3 ∷
   re 13 1 (ℓ "乏乃乏") ∷
   rw 15 q7 ∷
   re 12 1 (ℓ "乏乃乏") ∷
   rw 14 q7 ∷
   rw 13 q38 ∷
   rw 12 q7 ∷
   rw 1 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q41 : Eqn
  q41 = wE 30 W
  q42 : Eqn
  q42 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q43 : Eqn
  q43 = wE 74 W
  q44 : Eqn
  q44 = wE 26 W
  q45 : Eqn
  q45 = wE 163 W
  q46 : Eqn
  q46 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q47 : Eqn
  q47 = wE 164 W
  q48 : Eqn
  q48 = eqn (ℓ "丢乖") (ℓ "乖丢") (low-comm (CZ) (CX₁₀))
  q49 : Eqn
  q49 = wE 165 W
  q50 : Eqn
  q50 = eqn (ℓ "丢乏") (ℓ "乏丢") (low-comm (CZ) (Swap))
  q51 : Eqn
  q51 = wE 166 W
  q52 : Eqn
  q52 = wE 24 W
  q53 : Eqn
  q53 = wE 25 W

-- comm CZ01 CCZ023: 83 steps
lem-comm-CZ01-CCZ023 : ⟪ (ℓ "丢乛") ⟫ʷ ≈ ⟪ (ℓ "乛丢") ⟫ʷ
lem-comm-CZ01-CCZ023 = derive (ℓ "丢乛") (ℓ "乛丢")
  (rw 2 q16 ∷
   re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q40 ∷
   rw 2 q41 ∷
   rw 3 q42 ∷
   rw 4 q41 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q20 ∷
   rw 6 q24 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q27 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q20 ∷
   rw 6 q18 ∷
   rw⁻ 5 q20 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q43 ∷
   rw⁻ 3 q42 ∷
   rw 2 q43 ∷
   rw⁻ 1 q40 ∷
   rw 2 q44 ∷
   re 2 5 (ℓ "乜") ∷
   rw 2 q45 ∷
   rw 1 q24 ∷
   rw 2 q46 ∷
   rw 3 q33 ∷
   rw 4 q46 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q20 ∷
   rw 6 q24 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q27 ∷
   rw 0 q47 ∷
   rw 1 q48 ∷
   rw 2 q49 ∷
   rw 3 q48 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 4 q50 ∷
   rw 5 q47 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   rw⁻ 5 q50 ∷
   rw 6 q7 ∷
   rw 5 q16 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q20 ∷
   rw 5 q18 ∷
   rw⁻ 4 q20 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 3 q46 ∷
   rw 2 q31 ∷
   rw⁻ 1 q46 ∷
   rw 0 q18 ∷
   rw 1 q51 ∷
   re 1 1 (ℓ "义丹乊丹丽") ∷
   rw 0 q40 ∷
   rw 1 q41 ∷
   rw 2 q42 ∷
   rw 3 q41 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q20 ∷
   rw 5 q24 ∷
   rw 6 q20 ∷
   re 4 3 (ℓ "中") ∷
   rw 0 q16 ∷
   rw 1 q40 ∷
   rw 2 q52 ∷
   rw 3 q42 ∷
   rw 4 q52 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 5 q20 ∷
   rw 6 q53 ∷
   rw 7 q20 ∷
   re 5 3 (ℓ "丽") ∷
   rw 1 q44 ∷
   re 1 5 (ℓ "乜") ∷
   re 0 3 (ℓ "乛") ∷
   rw 1 q27 ∷ []) Eq.refl

private
  q54 : Eqn
  q54 = wE 167 W
  q55 : Eqn
  q55 = wE 168 W

-- comm CZ01 CCZ123: 15 steps
lem-comm-CZ01-CCZ123 : ⟪ (ℓ "丢乜") ⟫ʷ ≈ ⟪ (ℓ "乜丢") ⟫ʷ
lem-comm-CZ01-CCZ123 = derive (ℓ "丢乜") (ℓ "乜丢")
  (rw 1 q45 ∷
   rw 0 q54 ∷
   rw 1 q48 ∷
   rw 2 q55 ∷
   rw 3 q48 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 4 q50 ∷
   rw 5 q54 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q50 ∷
   rw 6 q7 ∷
   rw 0 q51 ∷ []) Eq.refl

private
  q56 : Eqn
  q56 = wE 169 W
  q57 : Eqn
  q57 = eqn (ℓ "丵乖") (ℓ "乖丵") (low-comm ((S ↑ • CK₁₀)) (CX₁₀))
  q58 : Eqn
  q58 = wE 170 W

-- CCZ123 passes CKd10: 15 steps
lem-CCZ123-passes-CKd10 : ⟪ (ℓ "乜丵") ⟫ʷ ≈ ⟪ (ℓ "丵乜") ⟫ʷ
lem-CCZ123-passes-CKd10 = derive (ℓ "乜丵") (ℓ "丵乜")
  (rw 0 q45 ∷
   rw 6 q3 ∷
   rw 5 q36 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 5 q56 ∷
   rw⁻ 4 q36 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "丽") ∷
   rw 6 q7 ∷
   rw⁻ 3 q57 ∷
   rw 2 q58 ∷
   rw⁻ 1 q57 ∷
   rw 0 q56 ∷
   rw 1 q51 ∷ []) Eq.refl

private
  q59 : Eqn
  q59 = wE 12 W
  q60 : Eqn
  q60 = wE 171 W
  q61 : Eqn
  q61 = wE 22 W
  q62 : Eqn
  q62 = wE 23 W
  q63 : Eqn
  q63 = wE 14 W
  q64 : Eqn
  q64 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))

-- SW12-PP: 17 steps
lem-SW12-PP : ⟪ (ℓ "丼九中九丮丼") ⟫ʷ ≈ ⟪ (ℓ "九中九丮") ⟫ʷ
lem-SW12-PP = derive (ℓ "丼九中九丮丼") (ℓ "九中九丮")
  (rw 4 q59 ∷
   rw 3 q59 ∷
   rw 2 q59 ∷
   rw 0 q60 ∷
   re 2 1 (ℓ "乏丼丠丼乏") ∷
   rw 1 q61 ∷
   rw⁻ 3 q35 ∷
   rw 4 q62 ∷
   re 1 5 (ℓ "中") ∷
   rw 2 q63 ∷
   rw 2 q60 ∷
   re 4 1 (ℓ "乏丼両丼乏") ∷
   rw 3 q61 ∷
   rw⁻ 5 q64 ∷
   rw 6 q62 ∷
   re 3 5 (ℓ "丮") ∷
   rw 4 q63 ∷ []) Eq.refl

private
  q65 : Eqn
  q65 = wE 172 W

-- pass [CCZ012] [CZ01]: 1 steps
lem-pass-CCZ012-vs-CZ01 : ⟪ (ℓ "乙丢") ⟫ʷ ≈ ⟪ (ℓ "丢乙") ⟫ʷ
lem-pass-CCZ012-vs-CZ01 = derive (ℓ "乙丢") (ℓ "丢乙")
  (rw 0 q65 ∷ []) Eq.refl

private
  q66 : Eqn
  q66 = wE 173 W
  q67 : Eqn
  q67 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q68 : Eqn
  q68 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q69 : Eqn
  q69 = wE 56 W
  q70 : Eqn
  q70 = wE 174 W
  q71 : Eqn
  q71 = wE 175 W

-- pass [CS03] [X3 TOFF013 X3]: 65 steps
lem-pass-CS03-vs-X3-TOFF013-X3 : ⟪ (ℓ "中丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞中") ⟫ʷ
lem-pass-CS03-vs-X3-TOFF013-X3 = derive (ℓ "中丞乞丞") (ℓ "丞乞丞中")
  (rw 4 q3 ∷
   rw 3 q66 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q4 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q67 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q68 ∷
   rw 10 q7 ∷
   rw 9 q68 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q7 ∷
   rw 6 q67 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q7 ∷
   rw 4 q67 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q7 ∷
   rw 2 q4 ∷
   rw 3 q69 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q66 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q7 ∷
   rw 1 q70 ∷
   rw 0 q71 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q4 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q67 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q68 ∷
   rw 1 q3 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q7 ∷
   rw⁻ 4 q67 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q7 ∷
   rw⁻ 6 q67 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q68 ∷
   rw 2 q69 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q71 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q7 ∷ []) Eq.refl

private
  q72 : Eqn
  q72 = wE 176 W

-- pass [CSd03] [X3 TOFF013 X3]: 65 steps
lem-pass-CSd03-vs-X3-TOFF013-X3 : ⟪ (ℓ "丮丞乞丞") ⟫ʷ ≈ ⟪ (ℓ "丞乞丞丮") ⟫ʷ
lem-pass-CSd03-vs-X3-TOFF013-X3 = derive (ℓ "丮丞乞丞") (ℓ "丞乞丞丮")
  (rw 4 q3 ∷
   rw 3 q66 ∷
   re 2 1 (ℓ "乏九乏") ∷
   re 3 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 2 q4 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q67 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q68 ∷
   rw 10 q7 ∷
   rw 9 q68 ∷
   rw 8 q4 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q7 ∷
   rw 6 q67 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q7 ∷
   rw 4 q67 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q7 ∷
   rw 2 q4 ∷
   rw 3 q69 ∷
   re 3 8 (ℓ "九") ∷
   rw 1 q66 ∷
   re 0 1 (ℓ "乏丨乏") ∷
   rw 2 q7 ∷
   rw 1 q72 ∷
   rw 0 q71 ∷
   re 2 1 (ℓ "上丶丣丷丣丧上一") ∷
   rw⁻ 1 q4 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q67 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q4 ∷
   rw⁻ 8 q68 ∷
   rw 1 q3 ∷
   rw⁻ 2 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q7 ∷
   rw⁻ 4 q67 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q7 ∷
   rw⁻ 6 q67 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q68 ∷
   rw 2 q69 ∷
   re 2 8 (ℓ "九") ∷
   re 1 3 (ℓ "乞") ∷
   rw 2 q71 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "丮") ∷
   rw 4 q7 ∷ []) Eq.refl

private
  q73 : Eqn
  q73 = wE 65 W
  q74 : Eqn
  q74 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q75 : Eqn
  q75 = wE 48 W

-- pass [CS12] [CS03]: 9 steps
lem-pass-CS12-vs-CS03 : ⟪ (ℓ "丶中") ⟫ʷ ≈ ⟪ (ℓ "中丶") ⟫ʷ
lem-pass-CS12-vs-CS03 = derive (ℓ "丶中") (ℓ "中丶")
  (re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q73 ∷
   rw⁻ 2 q74 ∷
   rw 3 q75 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   re 0 5 (ℓ "中") ∷ []) Eq.refl

private
  q76 : Eqn
  q76 = wE 93 W

-- pass [CS02] [CS03]: 15 steps
lem-pass-CS02-vs-CS03 : ⟪ (ℓ "丧中") ⟫ʷ ≈ ⟪ (ℓ "中丧") ⟫ʷ
lem-pass-CS02-vs-CS03 = derive (ℓ "丧中") (ℓ "中丧")
  (rw 2 q16 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q20 ∷
   rw 2 q18 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (ℓ "丽") ∷
   rw 0 q18 ∷
   rw 1 q76 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q20 ∷
   rw 1 q24 ∷
   rw 2 q20 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q24 ∷
   rw 2 q27 ∷ []) Eq.refl

private
  q77 : Eqn
  q77 = wE 177 W

-- pass [CCZ012] [CS12]: 1 steps
lem-pass-CCZ012-vs-CS12 : ⟪ (ℓ "乙丶") ⟫ʷ ≈ ⟪ (ℓ "丶乙") ⟫ʷ
lem-pass-CCZ012-vs-CS12 = derive (ℓ "乙丶") (ℓ "丶乙")
  (rw 0 q77 ∷ []) Eq.refl

private
  q78 : Eqn
  q78 = wE 178 W

-- pass [CCZ012] [CZ12]: 1 steps
lem-pass-CCZ012-vs-CZ12 : ⟪ (ℓ "乙丸") ⟫ʷ ≈ ⟪ (ℓ "丸乙") ⟫ʷ
lem-pass-CCZ012-vs-CZ12 = derive (ℓ "乙丸") (ℓ "丸乙")
  (rw 0 q78 ∷ []) Eq.refl

private
  q79 : Eqn
  q79 = wE 86 W

-- pass [CS02] [CSd03]: 15 steps
lem-pass-CS02-vs-CSd03 : ⟪ (ℓ "丧丮") ⟫ʷ ≈ ⟪ (ℓ "丮丧") ⟫ʷ
lem-pass-CS02-vs-CSd03 = derive (ℓ "丧丮") (ℓ "丮丧")
  (rw 2 q16 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw⁻ 3 q20 ∷
   rw 2 q31 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (ℓ "举") ∷
   rw 0 q18 ∷
   rw 1 q79 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q20 ∷
   rw 1 q33 ∷
   rw 2 q20 ∷
   re 0 3 (ℓ "丮") ∷
   rw 1 q24 ∷
   rw 2 q27 ∷ []) Eq.refl

private
  q80 : Eqn
  q80 = wE 84 W
  q81 : Eqn
  q81 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q82 : Eqn
  q82 = wE 47 W

-- pass [CSd12] [CS03]: 9 steps
lem-pass-CSd12-vs-CS03 : ⟪ (ℓ "丷中") ⟫ʷ ≈ ⟪ (ℓ "中丷") ⟫ʷ
lem-pass-CSd12-vs-CS03 = derive (ℓ "丷中") (ℓ "中丷")
  (re 1 1 (ℓ "乏丼丠丼乏") ∷
   rw 0 q3 ∷
   re 1 3 (ℓ "举") ∷
   rw 1 q80 ∷
   rw⁻ 2 q81 ∷
   rw 3 q82 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q7 ∷
   re 0 5 (ℓ "中") ∷ []) Eq.refl

private
  q83 : Eqn
  q83 = wE 179 W

-- pass [CSd02] [CS03]: 15 steps
lem-pass-CSd02-vs-CS03 : ⟪ (ℓ "丨中") ⟫ʷ ≈ ⟪ (ℓ "中丨") ⟫ʷ
lem-pass-CSd02-vs-CS03 = derive (ℓ "丨中") (ℓ "中丨")
  (rw 2 q16 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q20 ∷
   rw 2 q18 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (ℓ "丽") ∷
   rw 0 q31 ∷
   rw 1 q83 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 0 q20 ∷
   rw 1 q24 ∷
   rw 2 q20 ∷
   re 0 3 (ℓ "中") ∷
   rw 1 q33 ∷
   rw 2 q27 ∷ []) Eq.refl

private
  q84 : Eqn
  q84 = wE 180 W

-- pass [CCZ012] [CSd12]: 1 steps
lem-pass-CCZ012-vs-CSd12 : ⟪ (ℓ "乙丷") ⟫ʷ ≈ ⟪ (ℓ "丷乙") ⟫ʷ
lem-pass-CCZ012-vs-CSd12 = derive (ℓ "乙丷") (ℓ "丷乙")
  (rw 0 q84 ∷ []) Eq.refl

private
  q85 : Eqn
  q85 = wE 181 W

-- pass [CSd02] [CSd03]: 15 steps
lem-pass-CSd02-vs-CSd03 : ⟪ (ℓ "丨丮") ⟫ʷ ≈ ⟪ (ℓ "丮丨") ⟫ʷ
lem-pass-CSd02-vs-CSd03 = derive (ℓ "丨丮") (ℓ "丮丨")
  (rw 2 q16 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw⁻ 3 q20 ∷
   rw 2 q31 ∷
   rw⁻ 1 q20 ∷
   re 2 3 (ℓ "举") ∷
   rw 0 q31 ∷
   rw 1 q85 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q20 ∷
   rw 1 q33 ∷
   rw 2 q20 ∷
   re 0 3 (ℓ "丮") ∷
   rw 1 q33 ∷
   rw 2 q27 ∷ []) Eq.refl

private
  q86 : Eqn
  q86 = wE 182 W

-- pass [TOFF012] [X2 TOFF012 X2]: 1 steps
lem-pass-TOFF012-vs-X2-TOFF012-X2 : ⟪ (ℓ "九丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘九") ⟫ʷ
lem-pass-TOFF012-vs-X2-TOFF012-X2 = derive (ℓ "九丘九丘") (ℓ "丘九丘九")
  (rw 0 q86 ∷ []) Eq.refl

private
  q87 : Eqn
  q87 = wE 43 W

-- pass [CCZ013] [CZ01]: 47 steps
lem-pass-CCZ013-vs-CZ01 : ⟪ (ℓ "乚丢") ⟫ʷ ≈ ⟪ (ℓ "丢乚") ⟫ʷ
lem-pass-CCZ013-vs-CZ01 = derive (ℓ "乚丢") (ℓ "丢乚")
  (rw 2 q3 ∷
   rw 1 q50 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q67 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 3 q67 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw 1 q67 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw 1 q87 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q65 ∷
   rw⁻ 0 q50 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q67 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q3 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw⁻ 3 q67 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw⁻ 5 q67 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 2 q87 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q7 ∷ []) Eq.refl

-- pass [CS02] [X2 TOFF012 X2]: 1 steps
lem-pass-CS02-vs-X2-TOFF012-X2 : ⟪ (ℓ "丧丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丧") ⟫ʷ
lem-pass-CS02-vs-X2-TOFF012-X2 = derive (ℓ "丧丘九丘") (ℓ "丘九丘丧")
  (rw 0 q70 ∷ []) Eq.refl

-- pass [CSd02] [X2 TOFF012 X2]: 1 steps
lem-pass-CSd02-vs-X2-TOFF012-X2 : ⟪ (ℓ "丨丘九丘") ⟫ʷ ≈ ⟪ (ℓ "丘九丘丨") ⟫ʷ
lem-pass-CSd02-vs-X2-TOFF012-X2 = derive (ℓ "丨丘九丘") (ℓ "丘九丘丨")
  (rw 0 q72 ∷ []) Eq.refl

private
  q88 : Eqn
  q88 = wE 183 W

-- pass [S0] [CS03]: 9 steps
lem-pass-S0-vs-CS03 : ⟪ (ℓ "丈中") ⟫ʷ ≈ ⟪ (ℓ "中丈") ⟫ʷ
lem-pass-S0-vs-CS03 = derive (ℓ "丈中") (ℓ "中丈")
  (rw 2 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q7 ∷
   rw 0 q8 ∷
   rw 1 q88 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "中") ∷
   rw⁻ 1 q8 ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q89 : Eqn
  q89 = wE 184 W

-- pass [S0] [CSd03]: 9 steps
lem-pass-S0-vs-CSd03 : ⟪ (ℓ "丈丮") ⟫ʷ ≈ ⟪ (ℓ "丮丈") ⟫ʷ
lem-pass-S0-vs-CSd03 = derive (ℓ "丈丮") (ℓ "丮丈")
  (rw 2 q3 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q7 ∷
   rw 0 q8 ∷
   rw 1 q89 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "丮") ∷
   rw⁻ 1 q8 ∷
   rw 2 q7 ∷ []) Eq.refl

-- pass [CSd13] [CS02]: 5 steps
lem-pass-CSd13-vs-CS02 : ⟪ (ℓ "举丧") ⟫ʷ ≈ ⟪ (ℓ "丧举") ⟫ʷ
lem-pass-CSd13-vs-CS02 = derive (ℓ "举丧") (ℓ "丧举")
  (re 1 1 (ℓ "丼丠丼") ∷
   rw 0 q80 ∷
   rw⁻ 1 q81 ∷
   rw 2 q82 ∷
   re 0 3 (ℓ "丧") ∷ []) Eq.refl

-- pass [CCZ013] [CSd13]: 49 steps
lem-pass-CCZ013-vs-CSd13 : ⟪ (ℓ "乚举") ⟫ʷ ≈ ⟪ (ℓ "举乚") ⟫ʷ
lem-pass-CCZ013-vs-CSd13 = derive (ℓ "乚举") (ℓ "举乚")
  (rw 2 q3 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q7 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q67 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 3 q67 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw 1 q67 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw 1 q87 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q84 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "举") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q67 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q3 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw⁻ 3 q67 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw⁻ 5 q67 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 2 q87 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q7 ∷ []) Eq.refl

-- pass [CCZ013] [CZ13]: 49 steps
lem-pass-CCZ013-vs-CZ13 : ⟪ (ℓ "乚丿") ⟫ʷ ≈ ⟪ (ℓ "丿乚") ⟫ʷ
lem-pass-CCZ013-vs-CZ13 = derive (ℓ "乚丿") (ℓ "丿乚")
  (rw 2 q3 ∷
   re 1 1 (ℓ "乏丸乏") ∷
   rw 3 q7 ∷
   re 0 1 (ℓ "乏乙乏") ∷
   re 1 1 (ℓ "丶丣丷丣丧") ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q67 ∷
   rw 4 q3 ∷
   re 2 3 (ℓ "举") ∷
   rw⁻ 3 q67 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   rw 5 q7 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 3 q67 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw 1 q67 ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw 1 q87 ∷
   re 1 5 (ℓ "乙") ∷
   rw 1 q78 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "丿") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q67 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q67 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q3 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw⁻ 3 q67 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q7 ∷
   rw⁻ 5 q67 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   rw 2 q87 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q90 : Eqn
  q90 = wE 185 W

-- pass [Sd0] [CS03]: 9 steps
lem-pass-Sd0-vs-CS03 : ⟪ (ℓ "三中") ⟫ʷ ≈ ⟪ (ℓ "中三") ⟫ʷ
lem-pass-Sd0-vs-CS03 = derive (ℓ "三中") (ℓ "中三")
  (rw 2 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q7 ∷
   rw 0 q5 ∷
   rw 1 q90 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "中") ∷
   rw⁻ 1 q5 ∷
   rw 2 q7 ∷ []) Eq.refl

private
  q91 : Eqn
  q91 = wE 186 W

-- pass [Sd0] [CSd03]: 9 steps
lem-pass-Sd0-vs-CSd03 : ⟪ (ℓ "三丮") ⟫ʷ ≈ ⟪ (ℓ "丮三") ⟫ʷ
lem-pass-Sd0-vs-CSd03 = derive (ℓ "三丮") (ℓ "丮三")
  (rw 2 q3 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q7 ∷
   rw 0 q5 ∷
   rw 1 q91 ∷
   rw 2 q3 ∷
   re 0 3 (ℓ "丮") ∷
   rw⁻ 1 q5 ∷
   rw 2 q7 ∷ []) Eq.refl
