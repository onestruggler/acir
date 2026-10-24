{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD689 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D689 (W : Ws) (Sᴰ : SD689) where

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
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ : St 1831
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩ = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 772 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q6 : Eqn
  q6 = wE 6 W
  q7 : Eqn
  q7 = wE 481 W
  q8 : Eqn
  q8 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q9 : Eqn
  q9 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q10 : Eqn
  q10 = wE 2024 W
  q11 : Eqn
  q11 = wE 121 W
  q12 : Eqn
  q12 = wE 30 W
  q13 : Eqn
  q13 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 122 W
  q16 : Eqn
  q16 = wE 123 W
  q17 : Eqn
  q17 = wE 24 W
  q18 : Eqn
  q18 = wE 25 W
  q19 : Eqn
  q19 = wE 124 W
  q20 : Eqn
  q20 = wE 125 W
  q21 : Eqn
  q21 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q22 : Eqn
  q22 = wE 334 W
  q23 : Eqn
  q23 = wE 142 W
  q24 : Eqn
  q24 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q25 : Eqn
  q25 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q26 : Eqn
  q26 = wE 31 W
  q27 : Eqn
  q27 = sE 1831 lem-Bar⟨SSKSKK31-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~30-⟶2⟩
  q28 : Eqn
  q28 = wE 127 W
  q29 : Eqn
  q29 = wE 118 W
  q30 : Eqn
  q30 = wE 74 W
  q31 : Eqn
  q31 = wE 140 W
  q32 : Eqn
  q32 = wE 2025 W
  q33 : Eqn
  q33 = wE 39 W
  q34 : Eqn
  q34 = wE 329 W
  q35 : Eqn
  q35 = wE 315 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X3]: 567 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞") ⟫ʷ ≈ ⟪ (ℓ "丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞") (ℓ "丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 60 q1 ∷
   rw⁻ 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   re 52 1 (ℓ "乏乃乏") ∷
   rw⁻ 54 q5 ∷
   rw 53 q6 ∷
   rw⁻ 52 q5 ∷
   re 53 3 (ℓ "乓") ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q7 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw 40 q7 ∷
   rw 39 q3 ∷
   rw 38 q7 ∷
   rw 37 q3 ∷
   re 36 1 (ℓ "乏乃乏") ∷
   rw⁻ 38 q5 ∷
   rw 37 q6 ∷
   rw⁻ 36 q5 ∷
   re 37 3 (ℓ "乓") ∷
   rw⁻ 35 q8 ∷
   rw⁻ 34 q8 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 32 q8 ∷
   rw⁻ 31 q9 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 29 q2 ∷
   rw 30 q10 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 30 q11 ∷
   rw 31 q9 ∷
   rw 32 q12 ∷
   rw 33 q13 ∷
   rw 34 q12 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q5 ∷
   rw 36 q14 ∷
   rw 37 q5 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q11 ∷
   rw 37 q15 ∷
   rw 30 q1 ∷
   rw 31 q16 ∷
   rw 32 q9 ∷
   rw 33 q17 ∷
   rw 34 q13 ∷
   rw 35 q17 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 36 q5 ∷
   rw 37 q18 ∷
   rw 38 q5 ∷
   re 36 3 (ℓ "丽") ∷
   rw 37 q16 ∷
   rw 38 q19 ∷
   rw 31 q20 ∷
   re 31 8 (ℓ "乢") ∷
   re 30 3 (ℓ "也") ∷
   rw 31 q2 ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 33 q21 ∷
   rw 34 q9 ∷
   rw 35 q12 ∷
   rw 36 q13 ∷
   rw 37 q12 ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q5 ∷
   rw 39 q14 ∷
   rw 40 q5 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q21 ∷
   rw 40 q15 ∷
   rw 33 q1 ∷
   rw 34 q21 ∷
   rw 35 q9 ∷
   rw 36 q17 ∷
   rw 37 q13 ∷
   rw 38 q17 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q5 ∷
   rw 40 q18 ∷
   rw 41 q5 ∷
   re 39 3 (ℓ "丽") ∷
   rw 40 q21 ∷
   rw 41 q19 ∷
   rw 34 q22 ∷
   re 34 8 (ℓ "乥") ∷
   re 33 3 (ℓ "乤") ∷
   rw 34 q2 ∷
   rw 35 q2 ∷
   re 37 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 36 q11 ∷
   rw 37 q9 ∷
   rw 38 q12 ∷
   rw 39 q13 ∷
   rw 40 q12 ∷
   re 42 1 (ℓ "乏丶乏") ∷
   rw 41 q5 ∷
   rw 42 q14 ∷
   rw 43 q5 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q11 ∷
   rw 43 q15 ∷
   rw 36 q1 ∷
   rw 37 q16 ∷
   rw 38 q9 ∷
   rw 39 q17 ∷
   rw 40 q13 ∷
   rw 41 q17 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 42 q5 ∷
   rw 43 q18 ∷
   rw 44 q5 ∷
   re 42 3 (ℓ "丽") ∷
   rw 43 q16 ∷
   rw 44 q19 ∷
   rw 37 q20 ∷
   re 37 8 (ℓ "乢") ∷
   re 36 3 (ℓ "也") ∷
   rw 37 q2 ∷
   rw 38 q2 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q5 ∷
   rw 40 q14 ∷
   rw 41 q5 ∷
   re 39 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丶乏") ∷
   rw 40 q5 ∷
   rw 41 q14 ∷
   rw 42 q5 ∷
   re 40 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏乇乏") ∷
   rw 41 q5 ∷
   rw 42 q23 ∷
   rw 43 q5 ∷
   re 41 3 (ℓ "乑") ∷
   re 43 1 (ℓ "乏丶乏") ∷
   rw 42 q5 ∷
   rw 43 q14 ∷
   rw 44 q5 ∷
   re 42 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏乇乏") ∷
   rw 43 q5 ∷
   rw 44 q23 ∷
   rw 45 q5 ∷
   re 43 3 (ℓ "乑") ∷
   re 45 1 (ℓ "乏乇乏") ∷
   rw 44 q5 ∷
   rw 45 q23 ∷
   rw 46 q5 ∷
   re 44 3 (ℓ "乑") ∷
   rw 45 q24 ∷
   rw 46 q23 ∷
   rw 47 q25 ∷
   rw 48 q23 ∷
   rw 49 q25 ∷
   rw 50 q14 ∷
   rw 51 q14 ∷
   rw 52 q14 ∷
   rw 53 q23 ∷
   rw 54 q25 ∷
   rw 55 q14 ∷
   rw 56 q14 ∷
   rw 57 q14 ∷
   rw 58 q14 ∷
   rw 59 q14 ∷
   rw 60 q14 ∷
   rw 61 q24 ∷
   rw 62 q14 ∷
   rw 63 q14 ∷
   rw 64 q23 ∷
   rw 65 q14 ∷
   rw 66 q23 ∷
   rw 67 q23 ∷
   rw 68 q2 ∷
   rw 69 q2 ∷
   re 71 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 70 q11 ∷
   rw 71 q9 ∷
   rw 72 q12 ∷
   rw 73 q13 ∷
   rw 74 q12 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q5 ∷
   rw 76 q14 ∷
   rw 77 q5 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q11 ∷
   rw 77 q15 ∷
   rw 70 q1 ∷
   rw 71 q16 ∷
   rw 72 q9 ∷
   rw 73 q17 ∷
   rw 74 q13 ∷
   rw 75 q17 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 76 q5 ∷
   rw 77 q18 ∷
   rw 78 q5 ∷
   re 76 3 (ℓ "丽") ∷
   rw 77 q16 ∷
   rw 78 q19 ∷
   rw 71 q20 ∷
   re 71 8 (ℓ "乢") ∷
   re 70 3 (ℓ "也") ∷
   rw 71 q2 ∷
   rw 72 q2 ∷
   re 74 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 73 q21 ∷
   rw 74 q9 ∷
   rw 75 q12 ∷
   rw 76 q13 ∷
   rw 77 q12 ∷
   re 79 1 (ℓ "乏丶乏") ∷
   rw 78 q5 ∷
   rw 79 q14 ∷
   rw 80 q5 ∷
   re 78 3 (ℓ "中") ∷
   rw 79 q21 ∷
   rw 80 q15 ∷
   rw 73 q1 ∷
   rw 74 q21 ∷
   rw 75 q9 ∷
   rw 76 q17 ∷
   rw 77 q13 ∷
   rw 78 q17 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 79 q5 ∷
   rw 80 q18 ∷
   rw 81 q5 ∷
   re 79 3 (ℓ "丽") ∷
   rw 80 q21 ∷
   rw 81 q19 ∷
   rw 74 q22 ∷
   re 74 8 (ℓ "乥") ∷
   re 73 3 (ℓ "乤") ∷
   rw 74 q2 ∷
   rw 75 q2 ∷
   re 77 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 76 q11 ∷
   rw 77 q9 ∷
   rw 78 q12 ∷
   rw 79 q13 ∷
   rw 80 q12 ∷
   re 82 1 (ℓ "乏丶乏") ∷
   rw 81 q5 ∷
   rw 82 q14 ∷
   rw 83 q5 ∷
   re 81 3 (ℓ "中") ∷
   rw 82 q11 ∷
   rw 83 q15 ∷
   rw 76 q1 ∷
   rw 77 q16 ∷
   rw 78 q9 ∷
   rw 79 q17 ∷
   rw 80 q13 ∷
   rw 81 q17 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 82 q5 ∷
   rw 83 q18 ∷
   rw 84 q5 ∷
   re 82 3 (ℓ "丽") ∷
   rw 83 q16 ∷
   rw 84 q19 ∷
   rw 77 q20 ∷
   re 77 8 (ℓ "乢") ∷
   re 76 3 (ℓ "也") ∷
   rw 77 q2 ∷
   rw 78 q26 ∷
   rw 0 q27 ∷
   rw 49 q1 ∷
   rw⁻ 48 q2 ∷
   re 47 1 (ℓ "並乢並") ∷
   re 48 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 47 q11 ∷
   rw 48 q9 ∷
   rw 49 q12 ∷
   rw 50 q13 ∷
   rw 51 q12 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q5 ∷
   rw 53 q14 ∷
   rw 54 q5 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q11 ∷
   rw 54 q15 ∷
   rw 55 q26 ∷
   rw 54 q28 ∷
   rw 53 q29 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw⁻ 54 q5 ∷
   rw 53 q4 ∷
   rw⁻ 52 q5 ∷
   re 53 3 (ℓ "丽") ∷
   rw 51 q30 ∷
   rw⁻ 50 q13 ∷
   rw 49 q30 ∷
   rw⁻ 48 q9 ∷
   rw 47 q29 ∷
   rw 48 q20 ∷
   re 48 8 (ℓ "乢") ∷
   rw⁻ 46 q2 ∷
   rw⁻ 45 q2 ∷
   re 44 1 (ℓ "並乥並") ∷
   re 45 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 44 q21 ∷
   rw 45 q9 ∷
   rw 46 q12 ∷
   rw 47 q13 ∷
   rw 48 q12 ∷
   re 50 1 (ℓ "乏丶乏") ∷
   rw 49 q5 ∷
   rw 50 q14 ∷
   rw 51 q5 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q21 ∷
   rw 51 q15 ∷
   rw 52 q26 ∷
   rw 51 q28 ∷
   rw⁻ 50 q21 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw⁻ 51 q5 ∷
   rw 50 q4 ∷
   rw⁻ 49 q5 ∷
   re 50 3 (ℓ "丽") ∷
   rw 48 q30 ∷
   rw⁻ 47 q13 ∷
   rw 46 q30 ∷
   rw⁻ 45 q9 ∷
   rw⁻ 44 q21 ∷
   rw 45 q22 ∷
   re 45 8 (ℓ "乥") ∷
   rw⁻ 43 q2 ∷
   rw⁻ 42 q2 ∷
   re 41 1 (ℓ "並乢並") ∷
   re 42 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 41 q11 ∷
   rw 42 q9 ∷
   rw 43 q12 ∷
   rw 44 q13 ∷
   rw 45 q12 ∷
   re 47 1 (ℓ "乏丶乏") ∷
   rw 46 q5 ∷
   rw 47 q14 ∷
   rw 48 q5 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q11 ∷
   rw 48 q15 ∷
   rw 49 q26 ∷
   rw 48 q28 ∷
   rw 47 q29 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw⁻ 48 q5 ∷
   rw 47 q4 ∷
   rw⁻ 46 q5 ∷
   re 47 3 (ℓ "丽") ∷
   rw 45 q30 ∷
   rw⁻ 44 q13 ∷
   rw 43 q30 ∷
   rw⁻ 42 q9 ∷
   rw 41 q29 ∷
   rw 42 q20 ∷
   re 42 8 (ℓ "乢") ∷
   rw⁻ 40 q2 ∷
   rw⁻ 39 q2 ∷
   rw 38 q31 ∷
   rw 37 q31 ∷
   rw 36 q4 ∷
   rw 35 q31 ∷
   rw 34 q4 ∷
   rw 33 q4 ∷
   rw⁻ 32 q24 ∷
   rw 31 q4 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw⁻ 25 q25 ∷
   rw 24 q31 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw⁻ 20 q25 ∷
   rw 19 q31 ∷
   rw⁻ 18 q25 ∷
   rw 17 q31 ∷
   rw⁻ 16 q24 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q5 ∷
   rw 16 q31 ∷
   rw⁻ 15 q5 ∷
   re 16 3 (ℓ "乔") ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw⁻ 16 q5 ∷
   rw 15 q31 ∷
   rw⁻ 14 q5 ∷
   re 15 3 (ℓ "乔") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw⁻ 15 q5 ∷
   rw 14 q4 ∷
   rw⁻ 13 q5 ∷
   re 14 3 (ℓ "丽") ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw⁻ 14 q5 ∷
   rw 13 q31 ∷
   rw⁻ 12 q5 ∷
   re 13 3 (ℓ "乔") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q5 ∷
   rw 12 q4 ∷
   rw⁻ 11 q5 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q5 ∷
   rw 11 q4 ∷
   rw⁻ 10 q5 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q2 ∷
   re 7 1 (ℓ "並乢並") ∷
   re 8 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 7 q11 ∷
   rw 8 q9 ∷
   rw 9 q12 ∷
   rw 10 q13 ∷
   rw 11 q12 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q5 ∷
   rw 13 q14 ∷
   rw 14 q5 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q11 ∷
   rw 14 q15 ∷
   rw 15 q26 ∷
   rw 14 q28 ∷
   rw 13 q29 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q5 ∷
   rw 13 q4 ∷
   rw⁻ 12 q5 ∷
   re 13 3 (ℓ "丽") ∷
   rw 11 q30 ∷
   rw⁻ 10 q13 ∷
   rw 9 q30 ∷
   rw⁻ 8 q9 ∷
   rw 7 q29 ∷
   rw 8 q20 ∷
   re 8 8 (ℓ "乢") ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   re 4 1 (ℓ "並乥並") ∷
   re 5 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 4 q21 ∷
   rw 5 q9 ∷
   rw 6 q12 ∷
   rw 7 q13 ∷
   rw 8 q12 ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q5 ∷
   rw 10 q14 ∷
   rw 11 q5 ∷
   re 9 3 (ℓ "中") ∷
   rw 10 q21 ∷
   rw 11 q15 ∷
   rw 12 q26 ∷
   rw 11 q28 ∷
   rw⁻ 10 q21 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q5 ∷
   rw 10 q4 ∷
   rw⁻ 9 q5 ∷
   re 10 3 (ℓ "丽") ∷
   rw 8 q30 ∷
   rw⁻ 7 q13 ∷
   rw 6 q30 ∷
   rw⁻ 5 q9 ∷
   rw⁻ 4 q21 ∷
   rw 5 q22 ∷
   re 5 8 (ℓ "乥") ∷
   rw⁻ 3 q2 ∷
   rw⁻ 2 q2 ∷
   re 1 1 (ℓ "並乢並") ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q11 ∷
   rw 2 q9 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q12 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q5 ∷
   rw 7 q14 ∷
   rw 8 q5 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q11 ∷
   rw 8 q15 ∷
   rw 9 q26 ∷
   rw 8 q28 ∷
   rw 7 q29 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q5 ∷
   rw 7 q4 ∷
   rw⁻ 6 q5 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q30 ∷
   rw⁻ 4 q13 ∷
   rw 3 q30 ∷
   rw⁻ 2 q9 ∷
   rw 1 q29 ∷
   rw 2 q20 ∷
   re 2 8 (ℓ "乢") ∷
   rw⁻ 0 q2 ∷
   rw 1 q32 ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q9 ∷
   rw 3 q8 ∷
   rw 4 q9 ∷
   rw 5 q8 ∷
   rw 6 q8 ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 7 q5 ∷
   rw 8 q33 ∷
   rw 9 q5 ∷
   re 7 3 (ℓ "乐") ∷
   rw 8 q34 ∷
   rw 9 q35 ∷
   rw 10 q34 ∷
   rw 11 q35 ∷
   rw 12 q14 ∷
   rw 13 q14 ∷
   rw 14 q14 ∷
   rw 15 q34 ∷
   rw 16 q35 ∷
   rw 17 q14 ∷
   rw 18 q14 ∷
   rw 19 q14 ∷
   rw 20 q14 ∷
   rw 21 q14 ∷
   rw 22 q14 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q5 ∷
   rw 24 q33 ∷
   rw 25 q5 ∷
   re 23 3 (ℓ "乐") ∷
   rw 24 q14 ∷
   rw 25 q14 ∷
   rw 26 q34 ∷
   rw 27 q14 ∷
   rw 28 q34 ∷
   rw 29 q34 ∷
   rw 30 q2 ∷
   rw 31 q26 ∷ []) Eq.refl
