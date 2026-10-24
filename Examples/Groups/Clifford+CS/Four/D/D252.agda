{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D252 (W : Ws) where

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
  q3 = wE 140 W
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q6 : Eqn
  q6 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 828 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20 X3]: 219 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞") (ℓ "丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 60 q1 ∷
   rw⁻ 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q4 ∷
   rw⁻ 52 q5 ∷
   rw 51 q4 ∷
   rw 50 q4 ∷
   rw 49 q4 ∷
   rw 48 q4 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw⁻ 45 q6 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q4 ∷
   rw 41 q4 ∷
   rw⁻ 40 q6 ∷
   rw 39 q3 ∷
   rw⁻ 38 q6 ∷
   rw 37 q3 ∷
   rw⁻ 36 q5 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q3 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "乔") ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q7 ∷
   rw 35 q3 ∷
   rw⁻ 34 q7 ∷
   re 35 3 (ℓ "乔") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q7 ∷
   rw 34 q4 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw⁻ 34 q7 ∷
   rw 33 q3 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (ℓ "乔") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q7 ∷
   rw 32 q4 ∷
   rw⁻ 31 q7 ∷
   re 32 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q7 ∷
   rw 31 q4 ∷
   rw⁻ 30 q7 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q4 ∷
   rw⁻ 22 q5 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw⁻ 15 q6 ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw⁻ 10 q6 ∷
   rw 9 q3 ∷
   rw⁻ 8 q6 ∷
   rw 7 q3 ∷
   rw⁻ 6 q5 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q7 ∷
   rw 6 q3 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q7 ∷
   rw 5 q3 ∷
   rw⁻ 4 q7 ∷
   re 5 3 (ℓ "乔") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q7 ∷
   rw 4 q4 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw⁻ 4 q7 ∷
   rw 3 q3 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (ℓ "乔") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q7 ∷
   rw 2 q4 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q7 ∷
   rw 1 q4 ∷
   rw⁻ 0 q7 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q7 ∷
   rw 2 q9 ∷
   rw 3 q7 ∷
   re 1 3 (ℓ "中") ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q7 ∷
   rw 3 q9 ∷
   rw 4 q7 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q7 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷
   re 3 3 (ℓ "乑") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q7 ∷
   rw 5 q9 ∷
   rw 6 q7 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q7 ∷
   rw 6 q10 ∷
   rw 7 q7 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q7 ∷
   rw 7 q10 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q5 ∷
   rw 8 q10 ∷
   rw 9 q6 ∷
   rw 10 q10 ∷
   rw 11 q6 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q10 ∷
   rw 16 q6 ∷
   rw 17 q9 ∷
   rw 18 q9 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q5 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q10 ∷
   rw 27 q9 ∷
   rw 28 q10 ∷
   rw 29 q10 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q7 ∷
   rw 32 q9 ∷
   rw 33 q7 ∷
   re 31 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q7 ∷
   rw 33 q9 ∷
   rw 34 q7 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q7 ∷
   rw 34 q10 ∷
   rw 35 q7 ∷
   re 33 3 (ℓ "乑") ∷
   re 35 1 (ℓ "乏丶乏") ∷
   rw 34 q7 ∷
   rw 35 q9 ∷
   rw 36 q7 ∷
   re 34 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q7 ∷
   rw 36 q10 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "乑") ∷
   re 37 1 (ℓ "乏乇乏") ∷
   rw 36 q7 ∷
   rw 37 q10 ∷
   rw 38 q7 ∷
   re 36 3 (ℓ "乑") ∷
   rw 37 q5 ∷
   rw 38 q10 ∷
   rw 39 q6 ∷
   rw 40 q10 ∷
   rw 41 q6 ∷
   rw 42 q9 ∷
   rw 43 q9 ∷
   rw 44 q9 ∷
   rw 45 q10 ∷
   rw 46 q6 ∷
   rw 47 q9 ∷
   rw 48 q9 ∷
   rw 49 q9 ∷
   rw 50 q9 ∷
   rw 51 q9 ∷
   rw 52 q9 ∷
   rw 53 q5 ∷
   rw 54 q9 ∷
   rw 55 q9 ∷
   rw 56 q10 ∷
   rw 57 q9 ∷
   rw 58 q10 ∷
   rw 59 q10 ∷
   rw 60 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q13 : Eqn
  q13 = wE 137 W
  q14 : Eqn
  q14 = wE 829 W
  q15 : Eqn
  q15 = wE 139 W
  q16 : Eqn
  q16 = wE 1 W
  q17 : Eqn
  q17 = wE 107 W
  q18 : Eqn
  q18 = eqn (ℓ "丵之") (ℓ "之丵") (low-comm ((S ↑ • CK₁₀)) (CZ))
  q19 : Eqn
  q19 = wE 108 W
  q20 : Eqn
  q20 = wE 3 W
  q21 : Eqn
  q21 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q22 : Eqn
  q22 = eqn (ℓ "临之") (ℓ "之临") (low-comm (CK₁₀) (CZ))
  q23 : Eqn
  q23 = wE 830 W
  q24 : Eqn
  q24 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q25 : Eqn
  q25 = wE 831 W
  q26 : Eqn
  q26 = wE 157 W
  q27 : Eqn
  q27 = eqn (ℓ "丵乌") (ℓ "乌丵") (low-comm ((S ↑ • CK₁₀)) (CX₀₁))
  q28 : Eqn
  q28 = wE 158 W
  q29 : Eqn
  q29 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q30 : Eqn
  q30 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q31 : Eqn
  q31 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q32 : Eqn
  q32 = wE 832 W
  q33 : Eqn
  q33 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q34 : Eqn
  q34 = wE 833 W

-- groups [CK30 CS03 CS03 CKd30] [X3 CK32 X3 CZ12 CS13 CS23 CX12 CSd23 CX12 X3 CKd32 X3]: 319 steps
lem-groups-CK30-CS03-CS03-CKd30-vs-X3-CK32-X3-CZ12-CS13-CS23-CX12-CSd23-CX12-X3-CKd32-X3 : ⟪ (ℓ "乑中中乒丞乗丞丸丽义丹乊丹丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞丸丽义丹乊丹丞乘丞乑中中乒") ⟫ʷ
lem-groups-CK30-CS03-CS03-CKd30-vs-X3-CK32-X3-CZ12-CS13-CS23-CX12-CSd23-CX12-X3-CKd32-X3 = derive (ℓ "乑中中乒丞乗丞丸丽义丹乊丹丞乘丞") (ℓ "丞乗丞丸丽义丹乊丹丞乘丞乑中中乒")
  (rw 7 q1 ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q12 ∷
   rw⁻ 4 q2 ∷
   re 3 1 (ℓ "乏久乏") ∷
   rw⁻ 5 q7 ∷
   rw 4 q13 ∷
   rw⁻ 3 q7 ∷
   re 4 3 (ℓ "乕") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q7 ∷
   rw 3 q4 ∷
   rw⁻ 2 q7 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q7 ∷
   rw 2 q4 ∷
   rw⁻ 1 q7 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏乄乏") ∷
   rw⁻ 2 q7 ∷
   rw 1 q3 ∷
   rw⁻ 0 q7 ∷
   re 1 3 (ℓ "乔") ∷
   rw 1 q14 ∷
   rw 0 q2 ∷
   rw 1 q12 ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏乇乏") ∷
   rw 3 q7 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷
   re 3 3 (ℓ "乑") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q7 ∷
   rw 5 q9 ∷
   rw 6 q7 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q7 ∷
   rw 6 q9 ∷
   rw 7 q7 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏么乏") ∷
   rw 6 q7 ∷
   rw 7 q15 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "乒") ∷
   rw 7 q11 ∷
   re 6 1 (ℓ "乏丼丵丼乏") ∷
   rw 12 q16 ∷
   re 10 3 (ℓ "丿") ∷
   rw 9 q17 ∷
   rw 8 q18 ∷
   rw 7 q19 ∷
   re 7 1 (ℓ "乏丸乏") ∷
   rw 6 q20 ∷
   re 7 5 (ℓ "乒") ∷
   re 5 1 (ℓ "乏丼丠丼乏") ∷
   rw 11 q16 ∷
   re 9 3 (ℓ "丿") ∷
   rw 8 q17 ∷
   rw 7 q21 ∷
   rw 6 q19 ∷
   re 6 1 (ℓ "乏丸乏") ∷
   rw 5 q20 ∷
   re 6 5 (ℓ "中") ∷
   re 4 1 (ℓ "乏丼丠丼乏") ∷
   rw 10 q16 ∷
   re 8 3 (ℓ "丿") ∷
   rw 7 q17 ∷
   rw 6 q21 ∷
   rw 5 q19 ∷
   re 5 1 (ℓ "乏丸乏") ∷
   rw 4 q20 ∷
   re 5 5 (ℓ "中") ∷
   re 3 1 (ℓ "乏丼临丼乏") ∷
   rw 9 q16 ∷
   re 7 3 (ℓ "丿") ∷
   rw 6 q17 ∷
   rw 5 q22 ∷
   rw 4 q19 ∷
   re 4 1 (ℓ "乏丸乏") ∷
   rw 3 q20 ∷
   re 4 5 (ℓ "乑") ∷
   rw 9 q16 ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q20 ∷
   re 7 1 (ℓ "乏久乏") ∷
   rw 9 q20 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw 8 q20 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q20 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q20 ∷
   rw 5 q23 ∷
   rw 6 q16 ∷
   re 4 3 (ℓ "丽") ∷
   rw 7 q16 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q16 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q16 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q16 ∷
   re 8 3 (ℓ "乒") ∷
   rw 9 q20 ∷
   rw 10 q1 ∷
   rw⁻ 9 q24 ∷
   re 8 1 (ℓ "乏久乏") ∷
   rw⁻ 10 q7 ∷
   rw 9 q13 ∷
   rw⁻ 8 q7 ∷
   re 9 3 (ℓ "乕") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q7 ∷
   rw 8 q4 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (ℓ "丽") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q7 ∷
   rw 7 q4 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (ℓ "丽") ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q7 ∷
   rw 6 q3 ∷
   rw⁻ 5 q7 ∷
   re 6 3 (ℓ "乔") ∷
   rw 6 q25 ∷
   rw 5 q24 ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q7 ∷
   rw 7 q10 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 8 q9 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q7 ∷
   rw 9 q9 ∷
   rw 10 q7 ∷
   re 8 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏么乏") ∷
   rw 9 q7 ∷
   rw 10 q15 ∷
   rw 11 q7 ∷
   re 9 3 (ℓ "乒") ∷
   rw 10 q11 ∷
   re 9 1 (ℓ "乏丼丵丼乏") ∷
   rw 15 q16 ∷
   re 13 3 (ℓ "乀") ∷
   rw 12 q26 ∷
   rw 11 q27 ∷
   rw 10 q28 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 9 q20 ∷
   re 10 5 (ℓ "乒") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q16 ∷
   re 12 3 (ℓ "乀") ∷
   rw 11 q26 ∷
   rw 10 q29 ∷
   rw 9 q28 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 8 q20 ∷
   re 9 5 (ℓ "中") ∷
   re 7 1 (ℓ "乏丼丠丼乏") ∷
   rw 13 q16 ∷
   re 11 3 (ℓ "乀") ∷
   rw 10 q26 ∷
   rw 9 q29 ∷
   rw 8 q28 ∷
   re 8 1 (ℓ "乏丹乏") ∷
   rw 7 q20 ∷
   re 8 5 (ℓ "中") ∷
   re 6 1 (ℓ "乏丼临丼乏") ∷
   rw 12 q16 ∷
   re 10 3 (ℓ "乀") ∷
   rw 9 q26 ∷
   rw 8 q30 ∷
   rw 7 q28 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 6 q20 ∷
   re 7 5 (ℓ "乑") ∷
   rw 12 q1 ∷
   rw⁻ 11 q31 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw⁻ 12 q7 ∷
   rw 11 q13 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (ℓ "乕") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q7 ∷
   rw 10 q4 ∷
   rw⁻ 9 q7 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q7 ∷
   rw 9 q4 ∷
   rw⁻ 8 q7 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw⁻ 9 q7 ∷
   rw 8 q3 ∷
   rw⁻ 7 q7 ∷
   re 8 3 (ℓ "乔") ∷
   rw 8 q32 ∷
   rw 7 q31 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q7 ∷
   rw 9 q10 ∷
   rw 10 q7 ∷
   re 8 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q7 ∷
   rw 10 q9 ∷
   rw 11 q7 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q7 ∷
   rw 11 q9 ∷
   rw 12 q7 ∷
   re 10 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏么乏") ∷
   rw 11 q7 ∷
   rw 12 q15 ∷
   rw 13 q7 ∷
   re 11 3 (ℓ "乒") ∷
   rw 12 q11 ∷
   re 11 1 (ℓ "乏丼丵丼乏") ∷
   rw 17 q16 ∷
   re 15 3 (ℓ "乀") ∷
   rw 14 q26 ∷
   rw 13 q27 ∷
   rw 12 q28 ∷
   re 12 1 (ℓ "乏丹乏") ∷
   rw 11 q20 ∷
   re 12 5 (ℓ "乒") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q16 ∷
   re 14 3 (ℓ "乀") ∷
   rw 13 q26 ∷
   rw 12 q29 ∷
   rw 11 q28 ∷
   re 11 1 (ℓ "乏丹乏") ∷
   rw 10 q20 ∷
   re 11 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q16 ∷
   re 13 3 (ℓ "乀") ∷
   rw 12 q26 ∷
   rw 11 q29 ∷
   rw 10 q28 ∷
   re 10 1 (ℓ "乏丹乏") ∷
   rw 9 q20 ∷
   re 10 5 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼临丼乏") ∷
   rw 14 q16 ∷
   re 12 3 (ℓ "乀") ∷
   rw 11 q26 ∷
   rw 10 q30 ∷
   rw 9 q28 ∷
   re 9 1 (ℓ "乏丹乏") ∷
   rw 8 q20 ∷
   re 9 5 (ℓ "乑") ∷
   rw 16 q1 ∷
   rw⁻ 15 q2 ∷
   rw⁻ 14 q33 ∷
   rw⁻ 13 q2 ∷
   re 12 1 (ℓ "乏久乏") ∷
   rw⁻ 14 q7 ∷
   rw 13 q13 ∷
   rw⁻ 12 q7 ∷
   re 13 3 (ℓ "乕") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q7 ∷
   rw 12 q4 ∷
   rw⁻ 11 q7 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw⁻ 12 q7 ∷
   rw 11 q4 ∷
   rw⁻ 10 q7 ∷
   re 11 3 (ℓ "丽") ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw⁻ 11 q7 ∷
   rw 10 q3 ∷
   rw⁻ 9 q7 ∷
   re 10 3 (ℓ "乔") ∷
   rw 10 q34 ∷
   rw 9 q2 ∷
   rw 10 q33 ∷
   rw 11 q2 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q7 ∷
   rw 13 q10 ∷
   rw 14 q7 ∷
   re 12 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏丶乏") ∷
   rw 13 q7 ∷
   rw 14 q9 ∷
   rw 15 q7 ∷
   re 13 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q7 ∷
   rw 15 q9 ∷
   rw 16 q7 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏么乏") ∷
   rw 15 q7 ∷
   rw 16 q15 ∷
   rw 17 q7 ∷
   re 15 3 (ℓ "乒") ∷
   rw 16 q11 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 834 W

-- pass [TOFF213] [X3 TOFF213 X3]: 1 steps
lem-pass-TOFF213-vs-X3-TOFF213-X3 : ⟪ (ℓ "乥丞乥丞") ⟫ʷ ≈ ⟪ (ℓ "丞乥丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X3-TOFF213-X3 = derive (ℓ "乥丞乥丞") (ℓ "丞乥丞乥")
  (rw 0 q35 ∷ []) Eq.refl
