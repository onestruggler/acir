{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D285 (W : Ws) where

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
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = wE 481 W
  q5 : Eqn
  q5 = wE 772 W
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 6 W
  q8 : Eqn
  q8 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q9 : Eqn
  q9 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q10 : Eqn
  q10 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q11 : Eqn
  q11 = wE 140 W
  q12 : Eqn
  q12 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q13 : Eqn
  q13 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q14 : Eqn
  q14 = wE 870 W
  q15 : Eqn
  q15 = wE 39 W
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 315 W
  q18 : Eqn
  q18 = wE 329 W
  q19 : Eqn
  q19 = wE 142 W
  q20 : Eqn
  q20 = wE 31 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX30 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 S0 S0 S0 CK02 S0 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 X3]: 277 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞") (ℓ "丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 105 q1 ∷
   rw⁻ 104 q2 ∷
   rw 103 q3 ∷
   rw 102 q3 ∷
   rw 101 q3 ∷
   rw 100 q3 ∷
   rw 99 q3 ∷
   rw 98 q3 ∷
   rw 97 q4 ∷
   rw 96 q5 ∷
   rw 95 q3 ∷
   rw 94 q3 ∷
   rw 93 q3 ∷
   rw 92 q4 ∷
   rw 91 q5 ∷
   rw 90 q4 ∷
   rw 89 q5 ∷
   re 88 1 (ℓ "乏乃乏") ∷
   rw⁻ 90 q6 ∷
   rw 89 q7 ∷
   rw⁻ 88 q6 ∷
   re 89 3 (ℓ "乓") ∷
   rw 87 q4 ∷
   rw 86 q5 ∷
   rw 85 q4 ∷
   rw 84 q4 ∷
   rw 83 q4 ∷
   rw 82 q4 ∷
   rw 81 q5 ∷
   rw 80 q4 ∷
   rw 79 q4 ∷
   rw 78 q4 ∷
   rw 77 q3 ∷
   rw 76 q3 ∷
   rw 75 q3 ∷
   rw 74 q3 ∷
   rw 73 q3 ∷
   rw 72 q3 ∷
   rw 71 q3 ∷
   rw 70 q3 ∷
   rw 69 q3 ∷
   rw 68 q4 ∷
   rw 67 q5 ∷
   rw 66 q4 ∷
   rw 65 q4 ∷
   rw 64 q4 ∷
   rw 63 q3 ∷
   rw 62 q3 ∷
   rw 61 q3 ∷
   rw 60 q3 ∷
   rw 59 q3 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q3 ∷
   rw 55 q3 ∷
   rw 54 q3 ∷
   rw 53 q3 ∷
   rw 52 q3 ∷
   rw 51 q3 ∷
   rw 50 q3 ∷
   rw 49 q3 ∷
   rw 48 q3 ∷
   rw 47 q3 ∷
   rw 46 q3 ∷
   re 45 1 (ℓ "乏乃乏") ∷
   rw⁻ 47 q6 ∷
   rw 46 q7 ∷
   rw⁻ 45 q6 ∷
   re 46 3 (ℓ "乓") ∷
   rw⁻ 44 q8 ∷
   rw⁻ 43 q8 ∷
   rw⁻ 42 q8 ∷
   rw⁻ 41 q8 ∷
   rw⁻ 40 q8 ∷
   rw⁻ 39 q8 ∷
   rw⁻ 38 q9 ∷
   rw⁻ 37 q10 ∷
   rw⁻ 36 q8 ∷
   rw⁻ 35 q8 ∷
   rw⁻ 34 q8 ∷
   rw⁻ 33 q9 ∷
   rw⁻ 32 q10 ∷
   rw⁻ 31 q9 ∷
   rw⁻ 30 q10 ∷
   rw⁻ 29 q2 ∷
   rw 28 q11 ∷
   rw 27 q11 ∷
   rw 26 q3 ∷
   rw 25 q11 ∷
   rw 24 q3 ∷
   rw 23 q3 ∷
   rw⁻ 22 q12 ∷
   rw 21 q3 ∷
   rw 20 q3 ∷
   rw 19 q3 ∷
   rw 18 q3 ∷
   rw 17 q3 ∷
   rw 16 q3 ∷
   rw⁻ 15 q13 ∷
   rw 14 q11 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw⁻ 10 q13 ∷
   rw 9 q11 ∷
   rw⁻ 8 q13 ∷
   rw 7 q11 ∷
   rw⁻ 6 q12 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q6 ∷
   rw 6 q11 ∷
   rw⁻ 5 q6 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q6 ∷
   rw 5 q11 ∷
   rw⁻ 4 q6 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q6 ∷
   rw 4 q3 ∷
   rw⁻ 3 q6 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q6 ∷
   rw 3 q11 ∷
   rw⁻ 2 q6 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q6 ∷
   rw 2 q3 ∷
   rw⁻ 1 q6 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q6 ∷
   rw 1 q3 ∷
   rw⁻ 0 q6 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q14 ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q9 ∷
   rw 5 q8 ∷
   rw 6 q8 ∷
   rw 7 q8 ∷
   rw 8 q10 ∷
   rw 9 q9 ∷
   rw 10 q8 ∷
   rw 11 q8 ∷
   rw 12 q8 ∷
   rw 13 q8 ∷
   rw 14 q8 ∷
   rw 15 q8 ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q6 ∷
   rw 17 q15 ∷
   rw 18 q6 ∷
   re 16 3 (ℓ "乐") ∷
   rw 17 q16 ∷
   rw 18 q16 ∷
   rw 19 q16 ∷
   rw 20 q16 ∷
   rw 21 q16 ∷
   rw 22 q16 ∷
   rw 23 q16 ∷
   rw 24 q16 ∷
   rw 25 q16 ∷
   rw 26 q16 ∷
   rw 27 q16 ∷
   rw 28 q16 ∷
   rw 29 q16 ∷
   rw 30 q16 ∷
   rw 31 q16 ∷
   rw 32 q16 ∷
   rw 33 q16 ∷
   rw 34 q16 ∷
   rw 35 q17 ∷
   rw 36 q17 ∷
   rw 37 q17 ∷
   rw 38 q18 ∷
   rw 39 q17 ∷
   rw 40 q16 ∷
   rw 41 q16 ∷
   rw 42 q16 ∷
   rw 43 q16 ∷
   rw 44 q16 ∷
   rw 45 q16 ∷
   rw 46 q16 ∷
   rw 47 q16 ∷
   rw 48 q16 ∷
   rw 49 q17 ∷
   rw 50 q17 ∷
   rw 51 q17 ∷
   rw 52 q18 ∷
   rw 53 q17 ∷
   rw 54 q17 ∷
   rw 55 q17 ∷
   rw 56 q17 ∷
   rw 57 q18 ∷
   rw 58 q17 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q6 ∷
   rw 60 q15 ∷
   rw 61 q6 ∷
   re 59 3 (ℓ "乐") ∷
   rw 60 q18 ∷
   rw 61 q17 ∷
   rw 62 q18 ∷
   rw 63 q17 ∷
   rw 64 q16 ∷
   rw 65 q16 ∷
   rw 66 q16 ∷
   rw 67 q18 ∷
   rw 68 q17 ∷
   rw 69 q16 ∷
   rw 70 q16 ∷
   rw 71 q16 ∷
   rw 72 q16 ∷
   rw 73 q16 ∷
   rw 74 q16 ∷
   rw 75 q2 ∷
   re 77 1 (ℓ "乏丶乏") ∷
   rw 76 q6 ∷
   rw 77 q16 ∷
   rw 78 q6 ∷
   re 76 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丶乏") ∷
   rw 77 q6 ∷
   rw 78 q16 ∷
   rw 79 q6 ∷
   re 77 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏乇乏") ∷
   rw 78 q6 ∷
   rw 79 q19 ∷
   rw 80 q6 ∷
   re 78 3 (ℓ "乑") ∷
   re 80 1 (ℓ "乏丶乏") ∷
   rw 79 q6 ∷
   rw 80 q16 ∷
   rw 81 q6 ∷
   re 79 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏乇乏") ∷
   rw 80 q6 ∷
   rw 81 q19 ∷
   rw 82 q6 ∷
   re 80 3 (ℓ "乑") ∷
   re 82 1 (ℓ "乏乇乏") ∷
   rw 81 q6 ∷
   rw 82 q19 ∷
   rw 83 q6 ∷
   re 81 3 (ℓ "乑") ∷
   rw 82 q12 ∷
   rw 83 q19 ∷
   rw 84 q13 ∷
   rw 85 q19 ∷
   rw 86 q13 ∷
   rw 87 q16 ∷
   rw 88 q16 ∷
   rw 89 q16 ∷
   rw 90 q19 ∷
   rw 91 q13 ∷
   rw 92 q16 ∷
   rw 93 q16 ∷
   rw 94 q16 ∷
   rw 95 q16 ∷
   rw 96 q16 ∷
   rw 97 q16 ∷
   rw 98 q12 ∷
   rw 99 q16 ∷
   rw 100 q16 ∷
   rw 101 q19 ∷
   rw 102 q16 ∷
   rw 103 q19 ∷
   rw 104 q19 ∷
   rw 105 q20 ∷ []) Eq.refl
