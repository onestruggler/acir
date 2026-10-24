{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D388 (W : Ws) where

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
  q1 = wE 1102 W
  q2 : Eqn
  q2 = eqn (ℓ "习丞") (ℓ "丞习") (low₃-comm ((K ↑ • CCZ • K ↑ • iI)) (X))
  q3 : Eqn
  q3 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q5 : Eqn
  q5 = wE 390 W
  q6 : Eqn
  q6 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "丌丽") (ℓ "丽丌") (low₁-comm (X) ((Swap ↑ • CS • Swap ↑)))
  q8 : Eqn
  q8 = wE 387 W
  q9 : Eqn
  q9 = wE 257 W
  q10 : Eqn
  q10 = wE 389 W
  q11 : Eqn
  q11 = eqn (ℓ "丌举") (ℓ "举丌") (low₁-comm (X) ((Swap ↑ • (CS • CS • CS) • Swap ↑)))
  q12 : Eqn
  q12 = wE 258 W

-- distribute Gad(t=1, W=(0, 2, 3), d=1, e=1) TOFF102 CS13 TOFF102 CSd13: 25 steps
lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 : ⟪ (ℓ "丌丘丞习丽习举丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘习丌丘丞丽丞丌丘习丌丘丞举丞") ⟫ʷ
lem-distribute-Gad⟨t≡1-W≡⟨0-2-3⟩-d≡1-e≡1⟩-TOFF102-CS13-TOFF102-CSd13 = derive (ℓ "丌丘丞习丽习举丌丘丞") (ℓ "丌丘习丌丘丞丽丞丌丘习丌丘丞举丞")
  (rw 4 q1 ∷
   rw 11 q1 ∷
   rw 18 q1 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q3 ∷
   rw⁻ 4 q4 ∷
   rw 5 q5 ∷
   rw 5 q6 ∷
   rw 6 q3 ∷
   rw 7 q7 ∷
   rw 8 q8 ∷
   rw 5 q4 ∷
   rw 6 q9 ∷
   rw 7 q10 ∷
   rw⁻ 10 q2 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q4 ∷
   rw 13 q5 ∷
   rw 13 q6 ∷
   rw 14 q3 ∷
   rw 15 q11 ∷
   rw 16 q8 ∷
   rw 13 q4 ∷
   rw 14 q12 ∷
   rw 15 q10 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1108 W
  q14 : Eqn
  q14 = wE 1109 W

-- b2g 1011PP2: 4 steps
lem-b2g-1011PP2 : ⟪ (ℓ "丌丘丞乣义乣乊丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞世且且丗乣义乣乊世丕丕丗丌丞") ⟫ʷ
lem-b2g-1011PP2 = derive (ℓ "丌丘丞乣义乣乊丌丘丞") (ℓ "丌丞世且且丗乣义乣乊世丕丕丗丌丞")
  (rw 1 q4 ∷
   rw 7 q6 ∷
   rw 2 q13 ∷
   rw 10 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q16 : Eqn
  q16 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))
  q18 : Eqn
  q18 = wE 1110 W
  q19 : Eqn
  q19 = wE 1111 W

-- b2g 1111PP1: 5 steps
lem-b2g-1111PP1 : ⟪ (ℓ "丌丒丘丞习丽习举丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞") ⟫ʷ
lem-b2g-1111PP1 = derive (ℓ "丌丒丘丞习丽习举丌丒丘丞") (ℓ "丌丘丞丐与与丑习丽习举丐丏丏丑丌丘丞")
  (rw 1 q15 ∷
   rw 2 q16 ∷
   rw 8 q17 ∷
   rw 3 q18 ∷
   rw 11 q19 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 950 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [X1 CK12 X1]: 1 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CK12-X1 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丒为丒") ⟫ʷ ≈ ⟪ (ℓ "丒为丒丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CK12-X1 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丒为丒") (ℓ "丒为丒丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 0 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 656 W
  q22 : Eqn
  q22 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q23 : Eqn
  q23 = eqn (ℓ "临之") (ℓ "之临") (low-comm (CK₁₀) (CZ))
  q24 : Eqn
  q24 = wE 908 W
  q25 : Eqn
  q25 = eqn (ℓ "与之") (ℓ "之与") (low-comm ((S ↑)) (CZ))
  q26 : Eqn
  q26 = wE 5 W
  q27 : Eqn
  q27 = eqn (ℓ "並之") (ℓ "之並") (low-comm (Swap) (CZ))
  q28 : Eqn
  q28 = wE 7 W
  q29 : Eqn
  q29 = wE 909 W
  q30 : Eqn
  q30 = wE 27 W
  q31 : Eqn
  q31 = wE 31 W
  q32 : Eqn
  q32 = wE 140 W
  q33 : Eqn
  q33 = wE 911 W
  q34 : Eqn
  q34 = wE 142 W
  q35 : Eqn
  q35 = wE 655 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CZ23]: 69 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CZ23 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧之") ⟫ʷ ≈ ⟪ (ℓ "之丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CZ23 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧之") (ℓ "之丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 0 q21 ∷
   rw 30 q22 ∷
   rw 29 q22 ∷
   rw 28 q23 ∷
   rw 27 q22 ∷
   rw 26 q22 ∷
   rw 25 q22 ∷
   rw 24 q24 ∷
   rw 23 q22 ∷
   rw 22 q22 ∷
   rw 21 q22 ∷
   rw 20 q22 ∷
   rw 19 q22 ∷
   rw 18 q22 ∷
   rw 17 q22 ∷
   rw 16 q22 ∷
   rw 15 q22 ∷
   rw 14 q25 ∷
   rw 13 q23 ∷
   rw 12 q22 ∷
   rw 11 q22 ∷
   rw 10 q22 ∷
   rw 9 q22 ∷
   rw 8 q22 ∷
   rw 7 q22 ∷
   rw 6 q24 ∷
   rw 7 q26 ∷
   rw⁻ 6 q27 ∷
   rw 5 q28 ∷
   rw 6 q29 ∷
   rw 5 q27 ∷
   rw 6 q30 ∷
   rw 7 q31 ∷
   rw 6 q26 ∷
   rw⁻ 5 q27 ∷
   rw 4 q28 ∷
   rw 5 q29 ∷
   rw 4 q27 ∷
   rw 5 q30 ∷
   rw 6 q31 ∷
   rw 5 q26 ∷
   rw⁻ 4 q27 ∷
   rw 3 q32 ∷
   rw 4 q33 ∷
   rw 3 q27 ∷
   rw 4 q34 ∷
   rw 5 q31 ∷
   rw 4 q26 ∷
   rw⁻ 3 q27 ∷
   rw 2 q28 ∷
   rw 3 q29 ∷
   rw 2 q27 ∷
   rw 3 q30 ∷
   rw 4 q31 ∷
   rw 3 q26 ∷
   rw⁻ 2 q27 ∷
   rw 1 q28 ∷
   rw 2 q29 ∷
   rw 1 q27 ∷
   rw 2 q30 ∷
   rw 3 q31 ∷
   rw 2 q26 ∷
   rw⁻ 1 q27 ∷
   rw 0 q28 ∷
   rw 1 q29 ∷
   rw 0 q27 ∷
   rw 1 q30 ∷
   rw 2 q31 ∷
   rw 1 q35 ∷ []) Eq.refl

private
  q36 : Eqn
  q36 = wE 951 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CS12]: 1 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS12 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丶") ⟫ʷ ≈ ⟪ (ℓ "丶丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS12 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丶") (ℓ "丶丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 0 q36 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 1 W
  q38 : Eqn
  q38 = wE 20 W
  q39 : Eqn
  q39 = eqn (ℓ "丠义") (ℓ "义丠") (low-comm (CS) (CS))
  q40 : Eqn
  q40 = wE 49 W
  q41 : Eqn
  q41 = wE 3 W
  q42 : Eqn
  q42 = eqn (ℓ "临义") (ℓ "义临") (low-comm (CK₁₀) (CS))
  q43 : Eqn
  q43 = wE 695 W
  q44 : Eqn
  q44 = wE 210 W
  q45 : Eqn
  q45 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q46 : Eqn
  q46 = wE 103 W
  q47 : Eqn
  q47 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q48 : Eqn
  q48 = wE 607 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [CS13]: 387 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS13 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丽") ⟫ʷ ≈ ⟪ (ℓ "丽丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS13 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丽") (ℓ "丽丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q37 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q37 ∷
   re 35 3 (ℓ "丽") ∷
   rw 34 q38 ∷
   rw 33 q39 ∷
   rw 32 q40 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q41 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q41 ∷
   re 30 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q37 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q37 ∷
   re 34 3 (ℓ "丽") ∷
   rw 33 q38 ∷
   rw 32 q39 ∷
   rw 31 q40 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q41 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q41 ∷
   re 29 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q37 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q37 ∷
   re 33 3 (ℓ "丽") ∷
   rw 32 q38 ∷
   rw 31 q42 ∷
   rw 30 q40 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q41 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q41 ∷
   re 28 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q37 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q37 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q38 ∷
   rw 30 q39 ∷
   rw 29 q40 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q41 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q41 ∷
   re 27 3 (ℓ "丽") ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q37 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q37 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q38 ∷
   rw 29 q39 ∷
   rw 28 q40 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q41 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q41 ∷
   re 26 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 25 q37 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q37 ∷
   re 30 3 (ℓ "丽") ∷
   rw 29 q38 ∷
   rw 28 q39 ∷
   rw 27 q40 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q41 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q41 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q43 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q37 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q37 ∷
   re 28 3 (ℓ "丽") ∷
   rw 27 q38 ∷
   rw 26 q39 ∷
   rw 25 q40 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q41 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q41 ∷
   re 23 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q37 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q37 ∷
   re 27 3 (ℓ "丽") ∷
   rw 26 q38 ∷
   rw 25 q39 ∷
   rw 24 q40 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q41 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q41 ∷
   re 22 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q37 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q37 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q38 ∷
   rw 24 q39 ∷
   rw 23 q40 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q41 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q41 ∷
   re 21 3 (ℓ "丽") ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q37 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q37 ∷
   re 25 3 (ℓ "丽") ∷
   rw 24 q38 ∷
   rw 23 q39 ∷
   rw 22 q40 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q41 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q41 ∷
   re 20 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q37 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q37 ∷
   re 24 3 (ℓ "丽") ∷
   rw 23 q38 ∷
   rw 22 q39 ∷
   rw 21 q40 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q41 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q41 ∷
   re 19 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q37 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q37 ∷
   re 23 3 (ℓ "丽") ∷
   rw 22 q38 ∷
   rw 21 q39 ∷
   rw 20 q40 ∷
   re 20 1 (ℓ "乏丶乏") ∷
   rw 19 q41 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q41 ∷
   re 18 3 (ℓ "丽") ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q37 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q37 ∷
   re 22 3 (ℓ "丽") ∷
   rw 21 q38 ∷
   rw 20 q39 ∷
   rw 19 q40 ∷
   re 19 1 (ℓ "乏丶乏") ∷
   rw 18 q41 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q41 ∷
   re 17 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q37 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q37 ∷
   re 21 3 (ℓ "丽") ∷
   rw 20 q38 ∷
   rw 19 q39 ∷
   rw 18 q40 ∷
   re 18 1 (ℓ "乏丶乏") ∷
   rw 17 q41 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q41 ∷
   re 16 3 (ℓ "丽") ∷
   re 16 1 (ℓ "乏丶乏") ∷
   rw 15 q37 ∷
   re 16 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q37 ∷
   re 20 3 (ℓ "丽") ∷
   rw 19 q38 ∷
   rw 18 q39 ∷
   rw 17 q40 ∷
   re 17 1 (ℓ "乏丶乏") ∷
   rw 16 q41 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q41 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q44 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q37 ∷
   re 14 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q37 ∷
   re 18 3 (ℓ "丽") ∷
   rw 17 q38 ∷
   rw 16 q42 ∷
   rw 15 q40 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q41 ∷
   re 15 5 (ℓ "乑") ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q41 ∷
   re 13 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q37 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q37 ∷
   re 17 3 (ℓ "丽") ∷
   rw 16 q38 ∷
   rw 15 q39 ∷
   rw 14 q40 ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q41 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q41 ∷
   re 12 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q37 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q37 ∷
   re 16 3 (ℓ "丽") ∷
   rw 15 q38 ∷
   rw 14 q39 ∷
   rw 13 q40 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q41 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q41 ∷
   re 11 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q37 ∷
   re 11 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q37 ∷
   re 15 3 (ℓ "丽") ∷
   rw 14 q38 ∷
   rw 13 q39 ∷
   rw 12 q40 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q41 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q41 ∷
   re 10 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q37 ∷
   re 10 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q37 ∷
   re 14 3 (ℓ "丽") ∷
   rw 13 q38 ∷
   rw 12 q39 ∷
   rw 11 q40 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q41 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q41 ∷
   re 9 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q37 ∷
   re 9 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q37 ∷
   re 13 3 (ℓ "丽") ∷
   rw 12 q38 ∷
   rw 11 q39 ∷
   rw 10 q40 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q41 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q41 ∷
   re 8 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q37 ∷
   re 8 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q37 ∷
   re 12 3 (ℓ "丽") ∷
   rw 11 q38 ∷
   rw 10 q39 ∷
   rw 9 q40 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q41 ∷
   re 9 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q41 ∷
   re 7 3 (ℓ "丽") ∷
   rw 6 q43 ∷
   rw 7 q37 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q41 ∷
   rw 5 q45 ∷
   rw 6 q46 ∷
   rw 7 q37 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q45 ∷
   rw 7 q41 ∷
   rw 6 q37 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q41 ∷
   rw 4 q45 ∷
   rw 5 q46 ∷
   rw 6 q37 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q45 ∷
   rw 6 q41 ∷
   rw 5 q37 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q41 ∷
   rw 3 q47 ∷
   rw 4 q48 ∷
   rw 5 q37 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q47 ∷
   rw 5 q41 ∷
   rw 4 q37 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 5 q41 ∷
   rw 2 q45 ∷
   rw 3 q46 ∷
   rw 4 q37 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q45 ∷
   rw 4 q41 ∷
   rw 3 q37 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 4 q41 ∷
   rw 1 q45 ∷
   rw 2 q46 ∷
   rw 3 q37 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q45 ∷
   rw 3 q41 ∷
   rw 2 q37 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q41 ∷
   rw 0 q45 ∷
   rw 1 q46 ∷
   rw 2 q37 ∷
   re 0 3 (ℓ "丽") ∷
   rw⁻ 1 q45 ∷
   rw 2 q41 ∷ []) Eq.refl
