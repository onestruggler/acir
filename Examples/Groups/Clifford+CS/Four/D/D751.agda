{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD751 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D751 (W : Ws) (Sᴰ : SD751) where

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
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 : St 1117
  lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012 = pickᴰ 0 Sᴰ
  lem-X0-ROT : St 2668
  lem-X0-ROT = pickᴰ 1 Sᴰ
  lem-S2 : St 1778
  lem-S2 = pickᴰ 2 Sᴰ
  lem-C⟨SU'S⟩ : St 2669
  lem-C⟨SU'S⟩ = pickᴰ 3 Sᴰ
  lem-C⟨U'SU'⟩ : St 2670
  lem-C⟨U'SU'⟩ = pickᴰ 4 Sᴰ
  lem-PP-flip-ᵖ-1 : St 2671
  lem-PP-flip-ᵖ-1 = pickᴰ 5 Sᴰ
  lem-PP4 : St 2672
  lem-PP4 = pickᴰ 6 Sᴰ
  lem-ROT2≡E : St 2673
  lem-ROT2≡E = pickᴰ 7 Sᴰ
  lem-merge3 : St 2674
  lem-merge3 = pickᴰ 8 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : St 2675
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = pickᴰ 9 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : St 2676
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = pickᴰ 10 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 : St 2677
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 = pickᴰ 11 Sᴰ
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : St 2678
  lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = pickᴰ 12 Sᴰ
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : St 2679
  lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = pickᴰ 13 Sᴰ

private
  q1 : Eqn
  q1 = sE 2668 lem-X0-ROT
  q2 : Eqn
  q2 = sE 2673 lem-ROT2≡E
  q3 : Eqn
  q3 = wE 33 W

-- ROT-inv: 3 steps
lem-ROT-inv : ⟪ (ℓ "临乙习丿习乙丿与临乙习丿习乙丿丌临乙习丿习乙丿与临乙习丿习乙丿丌") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-ROT-inv = derive (ℓ "临乙习丿习乙丿与临乙习丿习乙丿丌临乙习丿习乙丿与临乙习丿习乙丿丌") []
  (rw 15 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = sE 2672 lem-PP4
  q5 : Eqn
  q5 = wE 227 W
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 1358 W
  q9 : Eqn
  q9 = wE 1342 W

-- PPi=PP3^3: 17 steps
lem-PPi≡PP3ᵖ3 : ⟪ (ℓ "中九丮九") ⟫ʷ ≈ ⟪ (ℓ "九中九丮九中九丮九中九丮") ⟫ʷ
lem-PPi≡PP3ᵖ3 = derive (ℓ "中九丮九") (ℓ "九中九丮九中九丮九中九丮")
  (rw⁻ 4 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q7 ∷
   rw 3 q8 ∷
   rw 2 q7 ∷
   rw 1 q5 ∷
   rw 2 q6 ∷
   re 1 1 (ℓ "乏丨乏") ∷
   rw 3 q7 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q7 ∷
   rw 1 q9 ∷
   rw 0 q7 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = sE 1778 lem-S2
  q11 : Eqn
  q11 = sE 2678 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3
  q12 : Eqn
  q12 = sE 1778 lem-S2

-- pass [TOFF012 CS03 TOFF012 CSd03] [X3 TOFF102 CS13 TOFF102 CSd13 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 : ⟪ (ℓ "九中九丮丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丞习丽习举丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X3-TOFF102-CS13-TOFF102-CSd13-X3 = derive (ℓ "九中九丮丞习丽习举丞") (ℓ "丞习丽习举丞九中九丮")
  (rw 0 q10 ∷
   rw 0 q11 ∷
   rw⁻ 6 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = sE 2677 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X1 X3 TOFF102 CS13 TOFF102 CSd13 X1 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 : ⟪ (ℓ "九中九丮丒丞习丽习举丒丞") ⟫ʷ ≈ ⟪ (ℓ "丒丞习丽习举丒丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X1-X3-TOFF102-CS13-TOFF102-CSd13-X1-X3 = derive (ℓ "九中九丮丒丞习丽习举丒丞") (ℓ "丒丞习丽习举丒丞九中九丮")
  (rw 0 q10 ∷
   rw 0 q13 ∷
   rw⁻ 8 q12 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = sE 2676 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X3 TOFF102 CS13 TOFF102 CSd13 X0 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 : ⟪ (ℓ "九中九丮丌丞习丽习举丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞习丽习举丌丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X3-TOFF102-CS13-TOFF102-CSd13-X0-X3 = derive (ℓ "九中九丮丌丞习丽习举丌丞") (ℓ "丌丞习丽习举丌丞九中九丮")
  (rw 0 q10 ∷
   rw 0 q14 ∷
   rw⁻ 8 q12 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = sE 2675 lem-pass-TOFF013-CS02-TOFF013-CSd02-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3

-- pass [TOFF012 CS03 TOFF012 CSd03] [X0 X1 X3 TOFF102 CS13 TOFF102 CSd13 X0 X1 X3]: 3 steps
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 : ⟪ (ℓ "九中九丮丌丒丞习丽习举丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞习丽习举丌丒丞九中九丮") ⟫ʷ
lem-pass-TOFF012-CS03-TOFF012-CSd03-vs-X0-X1-X3-TOFF102-CS13-TOFF102-CSd13-X0-X1-X3 = derive (ℓ "九中九丮丌丒丞习丽习举丌丒丞") (ℓ "丌丒丞习丽习举丌丒丞九中九丮")
  (rw 0 q10 ∷
   rw 0 q15 ∷
   rw⁻ 10 q12 ∷ []) Eq.refl

private
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 9 W
  q20 : Eqn
  q20 = wE 127 W
  q21 : Eqn
  q21 = wE 271 W
  q22 : Eqn
  q22 = wE 7 W
  q23 : Eqn
  q23 = wE 8 W
  q24 : Eqn
  q24 = wE 10 W
  q25 : Eqn
  q25 = wE 272 W
  q26 : Eqn
  q26 = sE 2674 lem-merge3
  q27 : Eqn
  q27 = wE 27 W
  q28 : Eqn
  q28 = wE 28 W
  q29 : Eqn
  q29 = wE 29 W
  q30 : Eqn
  q30 = wE 25 W
  q31 : Eqn
  q31 = wE 11 W
  q32 : Eqn
  q32 = wE 31 W

-- merge3 @1023: 78 steps
lem-merge3-at1023 : ⟪ (ℓ "习丽习举丞习丽习举丞") ⟫ʷ ≈ ⟪ (ℓ "丧乙") ⟫ʷ
lem-merge3-at1023 = derive (ℓ "习丽习举丞习丽习举丞") (ℓ "丧乙")
  (rw 10 q16 ∷
   rw⁻ 9 q17 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw⁻ 10 q18 ∷
   rw 9 q19 ∷
   rw⁻ 8 q18 ∷
   re 9 3 (ℓ "丮") ∷
   re 7 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 14 q20 ∷
   rw 13 q21 ∷
   rw 12 q22 ∷
   rw 11 q23 ∷
   rw 10 q19 ∷
   rw 9 q23 ∷
   rw 8 q24 ∷
   rw 7 q21 ∷
   rw 8 q25 ∷
   re 8 8 (ℓ "九") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw⁻ 8 q18 ∷
   rw 7 q24 ∷
   rw⁻ 6 q18 ∷
   re 7 3 (ℓ "中") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 12 q20 ∷
   rw 11 q21 ∷
   rw 10 q22 ∷
   rw 9 q23 ∷
   rw 8 q19 ∷
   rw 7 q23 ∷
   rw 6 q24 ∷
   rw 5 q21 ∷
   rw 6 q25 ∷
   re 6 8 (ℓ "九") ∷
   rw⁻ 4 q17 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw⁻ 5 q18 ∷
   rw 4 q19 ∷
   rw⁻ 3 q18 ∷
   re 4 3 (ℓ "丮") ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 9 q20 ∷
   rw 8 q21 ∷
   rw 7 q22 ∷
   rw 6 q23 ∷
   rw 5 q19 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 2 q21 ∷
   rw 3 q25 ∷
   re 3 8 (ℓ "九") ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw⁻ 3 q18 ∷
   rw 2 q24 ∷
   rw⁻ 1 q18 ∷
   re 2 3 (ℓ "中") ∷
   re 0 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw 7 q20 ∷
   rw 6 q21 ∷
   rw 5 q22 ∷
   rw 4 q23 ∷
   rw 3 q19 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 0 q21 ∷
   rw 1 q25 ∷
   re 1 8 (ℓ "九") ∷
   rw 1 q26 ∷
   rw 0 q27 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 1 q27 ∷
   rw 2 q28 ∷
   rw 3 q29 ∷
   rw 4 q28 ∷
   rw 5 q30 ∷
   rw 1 q31 ∷
   re 1 5 (ℓ "乙") ∷
   rw 2 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 225 W
  q34 : Eqn
  q34 = wE 45 W
  q35 : Eqn
  q35 = wE 1357 W
  q36 : Eqn
  q36 = wE 231 W

-- PP-g: 19 steps
lem-PP-g : ⟪ (ℓ "九中九丮") ⟫ʷ ≈ ⟪ (ℓ "丶乙丞中九丮九丞") ⟫ʷ
lem-PP-g = derive (ℓ "九中九丮") (ℓ "丶乙丞中九丮九丞")
  (rw 4 q33 ∷
   rw 5 q34 ∷
   rw 6 q6 ∷
   rw 7 q35 ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "丮") ∷
   rw 8 q7 ∷
   rw 7 q34 ∷
   rw 8 q6 ∷
   rw 9 q36 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "丮") ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q7 ∷
   rw 9 q33 ∷
   rw 0 q26 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = sE 2679 lem-pass-X3-TOFF012-CS03-TOFF012-CSd03-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0
  q38 : Eqn
  q38 = wE 390 W

-- pass [X3 CS03 TOFF012 CSd03 TOFF012 X3] [Kd0 TOFF012 CS03 TOFF012 CSd03 K0]: 37 steps
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 : ⟪ (ℓ "丞中九丮九丞下九中九丮上") ⟫ʷ ≈ ⟪ (ℓ "下九中九丮上丞中九丮九丞") ⟫ʷ
lem-pass-X3-CS03-TOFF012-CSd03-TOFF012-X3-vs-Kd0-TOFF012-CS03-TOFF012-CSd03-K0 = derive (ℓ "丞中九丮九丞下九中九丮上") (ℓ "下九中九丮上丞中九丮九丞")
  (rw 12 q33 ∷
   rw 13 q34 ∷
   rw 14 q6 ∷
   rw 15 q35 ∷
   rw 16 q6 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q6 ∷
   re 15 3 (ℓ "丮") ∷
   rw 16 q7 ∷
   rw 15 q34 ∷
   rw 16 q6 ∷
   rw 17 q36 ∷
   rw 18 q6 ∷
   re 16 3 (ℓ "丮") ∷
   rw 19 q6 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q7 ∷
   rw 17 q33 ∷
   rw⁻ 6 q37 ∷
   rw 5 q38 ∷
   rw 4 q5 ∷
   rw 5 q6 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q7 ∷
   re 3 1 (ℓ "乏丨乏") ∷
   rw 5 q7 ∷
   rw 4 q8 ∷
   rw 3 q7 ∷
   rw 2 q5 ∷
   rw 3 q6 ∷
   re 2 1 (ℓ "乏丨乏") ∷
   rw 4 q7 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q7 ∷
   rw 2 q9 ∷
   rw 1 q7 ∷
   rw 0 q38 ∷ []) Eq.refl

private
  q39 : Eqn
  q39 = sE 2669 lem-C⟨SU'S⟩
  q40 : Eqn
  q40 = wE 2473 W
  q41 : Eqn
  q41 = wE 2474 W
  q42 : Eqn
  q42 = sE 2670 lem-C⟨U'SU'⟩

-- REL0: 56 steps
lem-REL0 : ⟪ (ℓ "九中九丮下三九中九丮丈上") ⟫ʷ ≈ ⟪ (ℓ "三下三九中九丮丈上丈") ⟫ʷ
lem-REL0 = derive (ℓ "九中九丮下三九中九丮丈上") (ℓ "三下三九中九丮丈上丈")
  (rw⁻ 0 q39 ∷
   rw 6 q6 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q7 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   re 2 1 (ℓ "乏久乏") ∷
   rw 4 q7 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q7 ∷
   rw 2 q40 ∷
   rw 3 q6 ∷
   re 1 3 (ℓ "乒") ∷
   rw 4 q6 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q6 ∷
   re 3 3 (ℓ "乑") ∷
   rw 6 q6 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "乒") ∷
   rw 8 q6 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q7 ∷
   rw 14 q6 ∷
   re 13 1 (ℓ "乏丨乏") ∷
   rw 15 q7 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q7 ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw 13 q7 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw 12 q7 ∷
   re 9 1 (ℓ "乏丨乏") ∷
   rw 11 q7 ∷
   rw 10 q41 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "乒") ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "丮") ∷
   rw 13 q6 ∷
   re 11 3 (ℓ "乑") ∷
   rw 14 q6 ∷
   re 12 3 (ℓ "丮") ∷
   rw 15 q6 ∷
   re 13 3 (ℓ "乒") ∷
   rw 16 q6 ∷
   re 14 3 (ℓ "丮") ∷
   rw 17 q6 ∷
   re 15 3 (ℓ "乑") ∷
   rw 16 q7 ∷
   rw 0 q42 ∷ []) Eq.refl

private
  q43 : Eqn
  q43 = wE 2475 W
  q44 : Eqn
  q44 = wE 2476 W
  q45 : Eqn
  q45 = wE 2477 W
  q46 : Eqn
  q46 = sE 1117 lem-pass-S0-vs-CS03-TOFF012-CSd03-TOFF012
  q47 : Eqn
  q47 = wE 2478 W
  q48 : Eqn
  q48 = sE 2671 lem-PP-flip-ᵖ-1

-- spell Gad(t=0, W=(), d=SK, e=-1) -> Gad(t=0, W=(), d=SdKdSd, e=1): 8 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ : ⟪ (ℓ "丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "三下三九中九丮丈上丈") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKdSd-e≡1⟩ = derive (ℓ "丈上中九丮九下三") (ℓ "三下三九中九丮丈上丈")
  (rw 0 q43 ∷
   rw 12 q44 ∷
   rw 3 q45 ∷
   rw 6 q46 ∷
   rw 5 q46 ∷
   rw 4 q46 ∷
   rw 8 q47 ∷
   rw 3 q48 ∷ []) Eq.refl

private
  q49 : Eqn
  q49 = wE 2479 W
  q50 : Eqn
  q50 = wE 2480 W
  q51 : Eqn
  q51 = wE 2481 W
  q52 : Eqn
  q52 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q53 : Eqn
  q53 = wE 1739 W
  q54 : Eqn
  q54 = wE 1738 W
  q55 : Eqn
  q55 = wE 1740 W
  q56 : Eqn
  q56 = wE 2482 W

-- spell Gad(t=0, W=(), d=SK, e=-1) -> Gad(t=0, W=(), d=SdKSS, e=1): 47 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩ : ⟪ (ℓ "丈上中九丮九下三") ⟫ʷ ≈ ⟪ (ℓ "三上丈丈九中九丮三三下丈") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡SK-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡SdKSS-e≡1⟩ = derive (ℓ "丈上中九丮九下三") (ℓ "三上丈丈九中九丮三三下丈")
  (rw 0 q49 ∷
   rw 14 q50 ∷
   rw 4 q51 ∷
   rw 10 q6 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q7 ∷
   rw 8 q52 ∷
   rw 9 q53 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q52 ∷
   rw 10 q7 ∷
   rw 9 q54 ∷
   rw 12 q6 ∷
   re 11 1 (ℓ "乏丨乏") ∷
   rw 13 q7 ∷
   rw 10 q52 ∷
   rw 11 q55 ∷
   rw 12 q6 ∷
   re 10 3 (ℓ "丮") ∷
   rw⁻ 11 q52 ∷
   rw 12 q7 ∷
   rw 11 q54 ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q7 ∷
   rw 7 q52 ∷
   rw 8 q53 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q52 ∷
   rw 9 q7 ∷
   rw 8 q54 ∷
   rw 11 q6 ∷
   re 10 1 (ℓ "乏丨乏") ∷
   rw 12 q7 ∷
   rw 9 q52 ∷
   rw 10 q55 ∷
   rw 11 q6 ∷
   re 9 3 (ℓ "丮") ∷
   rw⁻ 10 q52 ∷
   rw 11 q7 ∷
   rw 10 q54 ∷
   rw 6 q46 ∷
   rw 5 q46 ∷
   rw 9 q56 ∷
   rw 4 q48 ∷ []) Eq.refl

private
  q57 : Eqn
  q57 = wE 2483 W
  q58 : Eqn
  q58 = wE 2484 W
  q59 : Eqn
  q59 = wE 2485 W
  q60 : Eqn
  q60 = wE 2486 W

-- spell Gad(t=0, W=(), d=1, e=-1) -> Gad(t=0, W=(), d=KSSK, e=1): 25 steps
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ : ⟪ (ℓ "中九丮九") ⟫ʷ ≈ ⟪ (ℓ "上丈丈上九中九丮下三三下") ⟫ʷ
lem-spell-Gad⟨t≡0-W≡⟨⟩-d≡1-e≡-1⟩--⟶-Gad⟨t≡0-W≡⟨⟩-d≡KSSK-e≡1⟩ = derive (ℓ "中九丮九") (ℓ "上丈丈上九中九丮下三三下")
  (rw 0 q57 ∷
   rw 12 q58 ∷
   rw 4 q59 ∷
   rw 7 q6 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q7 ∷
   rw 5 q52 ∷
   rw 6 q53 ∷
   rw 7 q6 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q52 ∷
   rw 7 q7 ∷
   rw 6 q54 ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丨乏") ∷
   rw 10 q7 ∷
   rw 7 q52 ∷
   rw 8 q55 ∷
   rw 9 q6 ∷
   re 7 3 (ℓ "丮") ∷
   rw⁻ 8 q52 ∷
   rw 9 q7 ∷
   rw 8 q54 ∷
   rw 9 q60 ∷
   rw 4 q48 ∷ []) Eq.refl
