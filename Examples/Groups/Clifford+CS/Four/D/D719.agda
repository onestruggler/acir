{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD719 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D719 (W : Ws) (Sᴰ : SD719) where

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
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 : St 2108
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q4 : Eqn
  q4 = wE 1106 W
  q5 : Eqn
  q5 = wE 772 W
  q6 : Eqn
  q6 = wE 7 W
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 6 W
  q9 : Eqn
  q9 = wE 481 W
  q10 : Eqn
  q10 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q11 : Eqn
  q11 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q12 : Eqn
  q12 = wE 1642 W
  q13 : Eqn
  q13 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q14 : Eqn
  q14 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q15 : Eqn
  q15 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q16 : Eqn
  q16 = wE 39 W
  q17 : Eqn
  q17 = wE 27 W
  q18 : Eqn
  q18 = wE 315 W
  q19 : Eqn
  q19 = wE 329 W
  q20 : Eqn
  q20 = wE 31 W
  q21 : Eqn
  q21 = sE 2108 lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3
  q22 : Eqn
  q22 = wE 1643 W
  q23 : Eqn
  q23 = wE 317 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X0 X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X0 X2 X3]: 297 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X0-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丌丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘丞") (ℓ "丌丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 66 q1 ∷
   rw⁻ 65 q2 ∷
   rw⁻ 64 q3 ∷
   rw 63 q4 ∷
   rw 62 q5 ∷
   rw 61 q5 ∷
   rw 60 q6 ∷
   rw 59 q5 ∷
   rw 58 q6 ∷
   rw 57 q6 ∷
   re 56 1 (ℓ "乏乃乏") ∷
   rw⁻ 58 q7 ∷
   rw 57 q8 ∷
   rw⁻ 56 q7 ∷
   re 57 3 (ℓ "乓") ∷
   rw 55 q6 ∷
   rw 54 q6 ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   rw 51 q6 ∷
   rw 50 q6 ∷
   rw 49 q9 ∷
   rw 48 q5 ∷
   rw 47 q6 ∷
   rw 46 q6 ∷
   rw 45 q6 ∷
   rw 44 q9 ∷
   rw 43 q5 ∷
   rw 42 q9 ∷
   rw 41 q5 ∷
   re 40 1 (ℓ "乏乃乏") ∷
   rw⁻ 42 q7 ∷
   rw 41 q8 ∷
   rw⁻ 40 q7 ∷
   re 41 3 (ℓ "乓") ∷
   rw⁻ 39 q10 ∷
   rw⁻ 38 q10 ∷
   rw⁻ 37 q11 ∷
   rw⁻ 36 q10 ∷
   rw⁻ 35 q11 ∷
   rw⁻ 34 q11 ∷
   rw⁻ 33 q2 ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw 32 q12 ∷
   rw 31 q2 ∷
   rw 32 q10 ∷
   rw 33 q11 ∷
   rw 34 q11 ∷
   rw 35 q13 ∷
   rw 36 q2 ∷
   rw 37 q2 ∷
   rw 38 q14 ∷
   rw 39 q13 ∷
   rw 40 q11 ∷
   rw 41 q11 ∷
   rw 42 q2 ∷
   rw 43 q2 ∷
   rw 44 q10 ∷
   rw 45 q15 ∷
   rw 46 q10 ∷
   rw 47 q15 ∷
   rw 48 q11 ∷
   rw 49 q11 ∷
   rw 50 q11 ∷
   rw 51 q10 ∷
   rw 52 q15 ∷
   rw 53 q11 ∷
   rw 54 q11 ∷
   rw 55 q11 ∷
   rw 56 q11 ∷
   rw 57 q11 ∷
   rw 58 q11 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q7 ∷
   rw 60 q16 ∷
   rw 61 q7 ∷
   re 59 3 (ℓ "乐") ∷
   rw 60 q17 ∷
   rw 61 q17 ∷
   rw 62 q17 ∷
   rw 63 q17 ∷
   rw 64 q17 ∷
   rw 65 q17 ∷
   rw 66 q17 ∷
   rw 67 q17 ∷
   rw 68 q17 ∷
   rw 69 q17 ∷
   rw 70 q17 ∷
   rw 71 q17 ∷
   rw 72 q17 ∷
   rw 73 q17 ∷
   rw 74 q17 ∷
   rw 75 q17 ∷
   rw 76 q17 ∷
   rw 77 q17 ∷
   rw 78 q18 ∷
   rw 79 q18 ∷
   rw 80 q18 ∷
   rw 81 q19 ∷
   rw 82 q18 ∷
   rw 83 q17 ∷
   rw 84 q17 ∷
   rw 85 q17 ∷
   rw 86 q17 ∷
   rw 87 q17 ∷
   rw 88 q17 ∷
   rw 89 q17 ∷
   rw 90 q17 ∷
   rw 91 q17 ∷
   rw 92 q18 ∷
   rw 93 q18 ∷
   rw 94 q18 ∷
   rw 95 q19 ∷
   rw 96 q18 ∷
   rw 97 q18 ∷
   rw 98 q18 ∷
   rw 99 q18 ∷
   rw 100 q19 ∷
   rw 101 q18 ∷
   re 103 1 (ℓ "乏乆乏") ∷
   rw 102 q7 ∷
   rw 103 q16 ∷
   rw 104 q7 ∷
   re 102 3 (ℓ "乐") ∷
   rw 103 q19 ∷
   rw 104 q18 ∷
   rw 105 q19 ∷
   rw 106 q18 ∷
   rw 107 q17 ∷
   rw 108 q17 ∷
   rw 109 q17 ∷
   rw 110 q19 ∷
   rw 111 q18 ∷
   rw 112 q17 ∷
   rw 113 q17 ∷
   rw 114 q17 ∷
   rw 115 q17 ∷
   rw 116 q17 ∷
   rw 117 q17 ∷
   rw 118 q2 ∷
   rw 119 q2 ∷
   rw 120 q10 ∷
   rw 121 q11 ∷
   rw 122 q11 ∷
   rw 123 q13 ∷
   rw 124 q2 ∷
   rw 125 q20 ∷
   rw 0 q21 ∷
   rw 94 q1 ∷
   rw⁻ 93 q2 ∷
   rw⁻ 92 q13 ∷
   rw⁻ 91 q11 ∷
   rw⁻ 90 q11 ∷
   rw⁻ 89 q10 ∷
   rw⁻ 88 q2 ∷
   rw⁻ 87 q2 ∷
   rw 86 q6 ∷
   rw 85 q6 ∷
   rw 84 q6 ∷
   rw 83 q6 ∷
   rw 82 q6 ∷
   rw 81 q6 ∷
   rw 80 q9 ∷
   rw 79 q5 ∷
   rw 78 q6 ∷
   rw 77 q6 ∷
   rw 76 q6 ∷
   rw 75 q9 ∷
   rw 74 q5 ∷
   rw 73 q9 ∷
   rw 72 q5 ∷
   re 71 1 (ℓ "乏乃乏") ∷
   rw⁻ 73 q7 ∷
   rw 72 q8 ∷
   rw⁻ 71 q7 ∷
   re 72 3 (ℓ "乓") ∷
   rw 70 q9 ∷
   rw 69 q5 ∷
   rw 68 q9 ∷
   rw 67 q9 ∷
   rw 66 q9 ∷
   rw 65 q9 ∷
   rw 64 q5 ∷
   rw 63 q9 ∷
   rw 62 q9 ∷
   rw 61 q9 ∷
   rw 60 q6 ∷
   rw 59 q6 ∷
   rw 58 q6 ∷
   rw 57 q6 ∷
   rw 56 q6 ∷
   rw 55 q6 ∷
   rw 54 q6 ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   rw 51 q9 ∷
   rw 50 q5 ∷
   rw 49 q9 ∷
   rw 48 q9 ∷
   rw 47 q9 ∷
   rw 46 q6 ∷
   rw 45 q6 ∷
   rw 44 q6 ∷
   rw 43 q6 ∷
   rw 42 q6 ∷
   rw 41 q6 ∷
   rw 40 q6 ∷
   rw 39 q6 ∷
   rw 38 q6 ∷
   rw 37 q6 ∷
   rw 36 q6 ∷
   rw 35 q6 ∷
   rw 34 q6 ∷
   rw 33 q6 ∷
   rw 32 q6 ∷
   rw 31 q6 ∷
   rw 30 q6 ∷
   rw 29 q6 ∷
   re 28 1 (ℓ "乏乃乏") ∷
   rw⁻ 30 q7 ∷
   rw 29 q8 ∷
   rw⁻ 28 q7 ∷
   re 29 3 (ℓ "乓") ∷
   rw⁻ 27 q11 ∷
   rw⁻ 26 q11 ∷
   rw⁻ 25 q11 ∷
   rw⁻ 24 q11 ∷
   rw⁻ 23 q11 ∷
   rw⁻ 22 q11 ∷
   rw⁻ 21 q15 ∷
   rw⁻ 20 q10 ∷
   rw⁻ 19 q11 ∷
   rw⁻ 18 q11 ∷
   rw⁻ 17 q11 ∷
   rw⁻ 16 q15 ∷
   rw⁻ 15 q10 ∷
   rw⁻ 14 q15 ∷
   rw⁻ 13 q10 ∷
   rw⁻ 12 q2 ∷
   rw⁻ 11 q2 ∷
   rw⁻ 10 q11 ∷
   rw⁻ 9 q11 ∷
   rw⁻ 8 q13 ∷
   rw⁻ 7 q14 ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 4 q13 ∷
   rw⁻ 3 q11 ∷
   rw⁻ 2 q11 ∷
   rw⁻ 1 q10 ∷
   rw⁻ 0 q2 ∷
   rw 1 q22 ∷
   rw 0 q23 ∷
   rw 1 q3 ∷
   rw 2 q2 ∷
   rw 3 q11 ∷
   rw 4 q11 ∷
   rw 5 q10 ∷
   rw 6 q11 ∷
   rw 7 q10 ∷
   rw 8 q10 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q7 ∷
   rw 10 q16 ∷
   rw 11 q7 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q19 ∷
   rw 11 q18 ∷
   rw 12 q19 ∷
   rw 13 q18 ∷
   rw 14 q17 ∷
   rw 15 q17 ∷
   rw 16 q17 ∷
   rw 17 q19 ∷
   rw 18 q18 ∷
   rw 19 q17 ∷
   rw 20 q17 ∷
   rw 21 q17 ∷
   rw 22 q17 ∷
   rw 23 q17 ∷
   rw 24 q17 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q7 ∷
   rw 26 q16 ∷
   rw 27 q7 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q17 ∷
   rw 27 q17 ∷
   rw 28 q19 ∷
   rw 29 q17 ∷
   rw 30 q19 ∷
   rw 31 q19 ∷
   rw 32 q23 ∷
   rw 33 q3 ∷
   rw 34 q2 ∷
   rw 35 q20 ∷ []) Eq.refl
