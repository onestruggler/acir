{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D287 (W : Ws) where

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
  q1 = eqn (ℓ "丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑") (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄乨丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中乨丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") (trans (by-assoc Eq.refl) (trans (ax lf) (by-assoc Eq.refl)))
  q2 : Eqn
  q2 = wE 225 W
  q3 : Eqn
  q3 = wE 871 W
  q4 : Eqn
  q4 = wE 872 W
  q5 : Eqn
  q5 = wE 873 W
  q6 : Eqn
  q6 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q7 : Eqn
  q7 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q8 : Eqn
  q8 = eqn (ℓ "丹丞") (ℓ "丞丹") (low₃-comm ((CX₀₁ ↑)) (X))
  q9 : Eqn
  q9 = eqn (ℓ "乄丞") (ℓ "丞乄") (low₃-comm ((Swap ↑ • CK₁₀ • Swap ↑)) (X))
  q10 : Eqn
  q10 = eqn (ℓ "且丞") (ℓ "丞且") (low₃-comm ((S ↑ ↑)) (X))
  q11 : Eqn
  q11 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q12 : Eqn
  q12 = wE 390 W
  q13 : Eqn
  q13 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q14 : Eqn
  q14 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))
  q16 : Eqn
  q16 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "丌乨") (ℓ "乨丌") (low₁-comm (X) (Toffᵗ))
  q18 : Eqn
  q18 = wE 387 W
  q19 : Eqn
  q19 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q20 : Eqn
  q20 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q21 : Eqn
  q21 = eqn (ℓ "丠丘") (ℓ "丘丠") (low-comm (CS) (X))
  q22 : Eqn
  q22 = eqn (ℓ "临丘") (ℓ "丘临") (low-comm (CK₁₀) (X))
  q23 : Eqn
  q23 = wE 874 W
  q24 : Eqn
  q24 = wE 5 W
  q25 : Eqn
  q25 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q26 : Eqn
  q26 = wE 7 W
  q27 : Eqn
  q27 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q28 : Eqn
  q28 = wE 257 W
  q29 : Eqn
  q29 = wE 27 W
  q30 : Eqn
  q30 = wE 31 W
  q31 : Eqn
  q31 = wE 140 W
  q32 : Eqn
  q32 = wE 875 W
  q33 : Eqn
  q33 = wE 142 W
  q34 : Eqn
  q34 = eqn (ℓ "丘业") (ℓ "业丘") (low₃-comm ((X ↑ ↑)) (S))
  q35 : Eqn
  q35 = wE 389 W

-- kk pieces X0 X1 X2 X3 CS01 CS01 CK10 CS01 CX12 CS02 CS02 CS02 CK20 S2  at 1: 702 steps
lem-kk-pieces-X0-X1-X2-X3-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2--at-1 : ⟪ (ℓ "丌丒丘丞丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丒丘丒丘丞乨丒丘丞丌丒丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丞丒丘丞乨丒丘丞丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞") ⟫ʷ
lem-kk-pieces-X0-X1-X2-X3-CS01-CS01-CK10-CS01-CX12-CS02-CS02-CS02-CK20-S2--at-1 = derive (ℓ "丌丒丘丞丠丠临丠丹丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乑丧丧丧且乄丧丧丧丧丧丧丹丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且且乄丧丧丧丧丧丧丧丧丧丹丠丠丠与临丠丠丠丠丠丠业乑丌丒丘丞") (ℓ "丌丒丘丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丒丘丒丘丞乨丒丘丞丌丒丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丞丒丘丞乨丒丘丞丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞")
  (rw 4 q1 ∷
   rw 33 q2 ∷
   rw 34 q3 ∷
   rw 35 q4 ∷
   rw 36 q5 ∷
   rw 42 q2 ∷
   rw 43 q3 ∷
   rw 44 q4 ∷
   rw 45 q5 ∷
   rw 81 q2 ∷
   rw 82 q3 ∷
   rw 83 q4 ∷
   rw 84 q5 ∷
   rw 90 q2 ∷
   rw 91 q3 ∷
   rw 92 q4 ∷
   rw 93 q5 ∷
   rw⁻ 3 q6 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q7 ∷
   rw⁻ 6 q6 ∷
   rw⁻ 7 q7 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 9 q8 ∷
   rw⁻ 10 q9 ∷
   rw⁻ 11 q10 ∷
   rw⁻ 12 q9 ∷
   rw⁻ 13 q10 ∷
   rw⁻ 14 q11 ∷
   rw⁻ 15 q11 ∷
   rw⁻ 16 q11 ∷
   rw⁻ 17 q9 ∷
   rw⁻ 18 q10 ∷
   rw⁻ 19 q11 ∷
   rw⁻ 20 q11 ∷
   rw⁻ 21 q11 ∷
   rw⁻ 22 q11 ∷
   rw⁻ 23 q11 ∷
   rw⁻ 24 q11 ∷
   rw⁻ 25 q8 ∷
   rw⁻ 26 q11 ∷
   rw⁻ 27 q11 ∷
   rw⁻ 28 q9 ∷
   rw⁻ 29 q11 ∷
   rw⁻ 30 q9 ∷
   rw⁻ 31 q9 ∷
   rw 32 q12 ∷
   rw⁻ 32 q13 ∷
   rw⁻ 33 q14 ∷
   rw⁻ 32 q15 ∷
   rw 35 q15 ∷
   rw 36 q14 ∷
   rw 37 q16 ∷
   rw 38 q17 ∷
   rw 39 q16 ∷
   rw 40 q14 ∷
   rw 41 q15 ∷
   rw 42 q18 ∷
   rw⁻ 39 q19 ∷
   rw⁻ 40 q20 ∷
   rw⁻ 39 q13 ∷
   rw 44 q19 ∷
   rw⁻ 45 q21 ∷
   rw⁻ 46 q21 ∷
   rw⁻ 47 q21 ∷
   rw⁻ 48 q22 ∷
   rw⁻ 49 q21 ∷
   rw⁻ 50 q21 ∷
   rw 51 q23 ∷
   rw 54 q24 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw⁻ 55 q25 ∷
   rw 54 q26 ∷
   rw⁻ 53 q25 ∷
   re 54 3 (ℓ "丽") ∷
   rw⁻ 52 q27 ∷
   rw 53 q28 ∷
   re 53 1 (ℓ "乏丶乏") ∷
   rw 52 q25 ∷
   rw 53 q29 ∷
   rw 54 q25 ∷
   re 52 3 (ℓ "中") ∷
   rw 53 q27 ∷
   rw 54 q30 ∷
   rw 55 q24 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw⁻ 56 q25 ∷
   rw 55 q26 ∷
   rw⁻ 54 q25 ∷
   re 55 3 (ℓ "丽") ∷
   rw⁻ 53 q27 ∷
   rw 54 q28 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q25 ∷
   rw 54 q29 ∷
   rw 55 q25 ∷
   re 53 3 (ℓ "中") ∷
   rw 54 q27 ∷
   rw 55 q30 ∷
   rw 56 q24 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw⁻ 57 q25 ∷
   rw 56 q26 ∷
   rw⁻ 55 q25 ∷
   re 56 3 (ℓ "丽") ∷
   rw⁻ 54 q27 ∷
   rw 55 q28 ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q25 ∷
   rw 55 q29 ∷
   rw 56 q25 ∷
   re 54 3 (ℓ "中") ∷
   rw 55 q27 ∷
   rw 56 q30 ∷
   rw 57 q24 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw⁻ 58 q25 ∷
   rw 57 q26 ∷
   rw⁻ 56 q25 ∷
   re 57 3 (ℓ "丽") ∷
   rw⁻ 55 q27 ∷
   rw 56 q28 ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q25 ∷
   rw 56 q29 ∷
   rw 57 q25 ∷
   re 55 3 (ℓ "中") ∷
   rw 56 q27 ∷
   rw 57 q30 ∷
   rw 58 q24 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw⁻ 59 q25 ∷
   rw 58 q26 ∷
   rw⁻ 57 q25 ∷
   re 58 3 (ℓ "丽") ∷
   rw⁻ 56 q27 ∷
   rw 57 q28 ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q25 ∷
   rw 57 q29 ∷
   rw 58 q25 ∷
   re 56 3 (ℓ "中") ∷
   rw 57 q27 ∷
   rw 58 q30 ∷
   rw 59 q24 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw⁻ 60 q25 ∷
   rw 59 q26 ∷
   rw⁻ 58 q25 ∷
   re 59 3 (ℓ "丽") ∷
   rw⁻ 57 q27 ∷
   rw 58 q28 ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q25 ∷
   rw 58 q29 ∷
   rw 59 q25 ∷
   re 57 3 (ℓ "中") ∷
   rw 58 q27 ∷
   rw 59 q30 ∷
   rw 60 q24 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw⁻ 61 q25 ∷
   rw 60 q31 ∷
   rw⁻ 59 q25 ∷
   re 60 3 (ℓ "乔") ∷
   rw⁻ 58 q27 ∷
   rw 59 q32 ∷
   re 59 1 (ℓ "乏乇乏") ∷
   rw 58 q25 ∷
   rw 59 q33 ∷
   rw 60 q25 ∷
   re 58 3 (ℓ "乑") ∷
   rw 59 q27 ∷
   rw 60 q30 ∷
   rw 59 q34 ∷
   rw 62 q24 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw⁻ 63 q25 ∷
   rw 62 q26 ∷
   rw⁻ 61 q25 ∷
   re 62 3 (ℓ "丽") ∷
   rw⁻ 60 q27 ∷
   rw 61 q28 ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 60 q25 ∷
   rw 61 q29 ∷
   rw 62 q25 ∷
   re 60 3 (ℓ "中") ∷
   rw 61 q27 ∷
   rw 62 q30 ∷
   rw 63 q24 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q25 ∷
   rw 63 q26 ∷
   rw⁻ 62 q25 ∷
   re 63 3 (ℓ "丽") ∷
   rw⁻ 61 q27 ∷
   rw 62 q28 ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q25 ∷
   rw 62 q29 ∷
   rw 63 q25 ∷
   re 61 3 (ℓ "中") ∷
   rw 62 q27 ∷
   rw 63 q30 ∷
   rw 64 q24 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q25 ∷
   rw 64 q26 ∷
   rw⁻ 63 q25 ∷
   re 64 3 (ℓ "丽") ∷
   rw⁻ 62 q27 ∷
   rw 63 q28 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q25 ∷
   rw 63 q29 ∷
   rw 64 q25 ∷
   re 62 3 (ℓ "中") ∷
   rw 63 q27 ∷
   rw 64 q30 ∷
   rw 65 q24 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw⁻ 66 q25 ∷
   rw 65 q26 ∷
   rw⁻ 64 q25 ∷
   re 65 3 (ℓ "丽") ∷
   rw⁻ 63 q27 ∷
   rw 64 q28 ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q25 ∷
   rw 64 q29 ∷
   rw 65 q25 ∷
   re 63 3 (ℓ "中") ∷
   rw 64 q27 ∷
   rw 65 q30 ∷
   rw 66 q24 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q25 ∷
   rw 66 q26 ∷
   rw⁻ 65 q25 ∷
   re 66 3 (ℓ "丽") ∷
   rw⁻ 64 q27 ∷
   rw 65 q28 ∷
   re 65 1 (ℓ "乏丶乏") ∷
   rw 64 q25 ∷
   rw 65 q29 ∷
   rw 66 q25 ∷
   re 64 3 (ℓ "中") ∷
   rw 65 q27 ∷
   rw 66 q30 ∷
   rw 67 q24 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw⁻ 68 q25 ∷
   rw 67 q26 ∷
   rw⁻ 66 q25 ∷
   re 67 3 (ℓ "丽") ∷
   rw⁻ 65 q27 ∷
   rw 66 q28 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q25 ∷
   rw 66 q29 ∷
   rw 67 q25 ∷
   re 65 3 (ℓ "中") ∷
   rw 66 q27 ∷
   rw 67 q30 ∷
   rw 68 q24 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw⁻ 69 q25 ∷
   rw 68 q26 ∷
   rw⁻ 67 q25 ∷
   re 68 3 (ℓ "丽") ∷
   rw⁻ 66 q27 ∷
   rw 67 q28 ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q25 ∷
   rw 67 q29 ∷
   rw 68 q25 ∷
   re 66 3 (ℓ "中") ∷
   rw 67 q27 ∷
   rw 68 q30 ∷
   rw 69 q24 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw⁻ 70 q25 ∷
   rw 69 q26 ∷
   rw⁻ 68 q25 ∷
   re 69 3 (ℓ "丽") ∷
   rw⁻ 67 q27 ∷
   rw 68 q28 ∷
   re 68 1 (ℓ "乏丶乏") ∷
   rw 67 q25 ∷
   rw 68 q29 ∷
   rw 69 q25 ∷
   re 67 3 (ℓ "中") ∷
   rw 68 q27 ∷
   rw 69 q30 ∷
   rw 70 q24 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw⁻ 71 q25 ∷
   rw 70 q26 ∷
   rw⁻ 69 q25 ∷
   re 70 3 (ℓ "丽") ∷
   rw⁻ 68 q27 ∷
   rw 69 q28 ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q25 ∷
   rw 69 q29 ∷
   rw 70 q25 ∷
   re 68 3 (ℓ "中") ∷
   rw 69 q27 ∷
   rw 70 q30 ∷
   rw 69 q23 ∷
   rw 72 q24 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw⁻ 73 q25 ∷
   rw 72 q26 ∷
   rw⁻ 71 q25 ∷
   re 72 3 (ℓ "丽") ∷
   rw⁻ 70 q27 ∷
   rw 71 q28 ∷
   re 71 1 (ℓ "乏丶乏") ∷
   rw 70 q25 ∷
   rw 71 q29 ∷
   rw 72 q25 ∷
   re 70 3 (ℓ "中") ∷
   rw 71 q27 ∷
   rw 72 q30 ∷
   rw 73 q24 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw⁻ 74 q25 ∷
   rw 73 q26 ∷
   rw⁻ 72 q25 ∷
   re 73 3 (ℓ "丽") ∷
   rw⁻ 71 q27 ∷
   rw 72 q28 ∷
   re 72 1 (ℓ "乏丶乏") ∷
   rw 71 q25 ∷
   rw 72 q29 ∷
   rw 73 q25 ∷
   re 71 3 (ℓ "中") ∷
   rw 72 q27 ∷
   rw 73 q30 ∷
   rw 74 q24 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw⁻ 75 q25 ∷
   rw 74 q26 ∷
   rw⁻ 73 q25 ∷
   re 74 3 (ℓ "丽") ∷
   rw⁻ 72 q27 ∷
   rw 73 q28 ∷
   re 73 1 (ℓ "乏丶乏") ∷
   rw 72 q25 ∷
   rw 73 q29 ∷
   rw 74 q25 ∷
   re 72 3 (ℓ "中") ∷
   rw 73 q27 ∷
   rw 74 q30 ∷
   rw 75 q24 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw⁻ 76 q25 ∷
   rw 75 q31 ∷
   rw⁻ 74 q25 ∷
   re 75 3 (ℓ "乔") ∷
   rw⁻ 73 q27 ∷
   rw 74 q32 ∷
   re 74 1 (ℓ "乏乇乏") ∷
   rw 73 q25 ∷
   rw 74 q33 ∷
   rw 75 q25 ∷
   re 73 3 (ℓ "乑") ∷
   rw 74 q27 ∷
   rw 75 q30 ∷
   rw 76 q24 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw⁻ 77 q25 ∷
   rw 76 q26 ∷
   rw⁻ 75 q25 ∷
   re 76 3 (ℓ "丽") ∷
   rw⁻ 74 q27 ∷
   rw 75 q28 ∷
   re 75 1 (ℓ "乏丶乏") ∷
   rw 74 q25 ∷
   rw 75 q29 ∷
   rw 76 q25 ∷
   re 74 3 (ℓ "中") ∷
   rw 75 q27 ∷
   rw 76 q30 ∷
   rw 77 q24 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw⁻ 78 q25 ∷
   rw 77 q26 ∷
   rw⁻ 76 q25 ∷
   re 77 3 (ℓ "丽") ∷
   rw⁻ 75 q27 ∷
   rw 76 q28 ∷
   re 76 1 (ℓ "乏丶乏") ∷
   rw 75 q25 ∷
   rw 76 q29 ∷
   rw 77 q25 ∷
   re 75 3 (ℓ "中") ∷
   rw 76 q27 ∷
   rw 77 q30 ∷
   rw 76 q19 ∷
   rw 77 q35 ∷
   rw⁻ 76 q20 ∷
   rw⁻ 77 q16 ∷
   rw⁻ 76 q15 ∷
   rw 79 q15 ∷
   rw 80 q14 ∷
   rw 81 q16 ∷
   rw 82 q17 ∷
   rw 83 q16 ∷
   rw 84 q14 ∷
   rw 85 q15 ∷
   rw 86 q18 ∷
   rw⁻ 83 q19 ∷
   rw⁻ 84 q20 ∷
   rw⁻ 83 q13 ∷
   rw 88 q19 ∷
   rw⁻ 89 q21 ∷
   rw⁻ 90 q21 ∷
   rw⁻ 91 q22 ∷
   rw⁻ 92 q21 ∷
   rw⁻ 93 q22 ∷
   rw⁻ 94 q22 ∷
   rw 95 q23 ∷
   rw 98 q24 ∷
   re 97 1 (ℓ "乏乄乏") ∷
   rw⁻ 99 q25 ∷
   rw 98 q31 ∷
   rw⁻ 97 q25 ∷
   re 98 3 (ℓ "乔") ∷
   rw⁻ 96 q27 ∷
   rw 97 q32 ∷
   re 97 1 (ℓ "乏乇乏") ∷
   rw 96 q25 ∷
   rw 97 q33 ∷
   rw 98 q25 ∷
   re 96 3 (ℓ "乑") ∷
   rw 97 q27 ∷
   rw 98 q30 ∷
   rw 97 q34 ∷
   rw 100 q24 ∷
   re 99 1 (ℓ "乏乄乏") ∷
   rw⁻ 101 q25 ∷
   rw 100 q31 ∷
   rw⁻ 99 q25 ∷
   re 100 3 (ℓ "乔") ∷
   rw⁻ 98 q27 ∷
   rw 99 q32 ∷
   re 99 1 (ℓ "乏乇乏") ∷
   rw 98 q25 ∷
   rw 99 q33 ∷
   rw 100 q25 ∷
   re 98 3 (ℓ "乑") ∷
   rw 99 q27 ∷
   rw 100 q30 ∷
   rw 99 q34 ∷
   rw 102 q24 ∷
   re 101 1 (ℓ "乏丧乏") ∷
   rw⁻ 103 q25 ∷
   rw 102 q26 ∷
   rw⁻ 101 q25 ∷
   re 102 3 (ℓ "丽") ∷
   rw⁻ 100 q27 ∷
   rw 101 q28 ∷
   re 101 1 (ℓ "乏丶乏") ∷
   rw 100 q25 ∷
   rw 101 q29 ∷
   rw 102 q25 ∷
   re 100 3 (ℓ "中") ∷
   rw 101 q27 ∷
   rw 102 q30 ∷
   rw 103 q24 ∷
   re 102 1 (ℓ "乏丧乏") ∷
   rw⁻ 104 q25 ∷
   rw 103 q26 ∷
   rw⁻ 102 q25 ∷
   re 103 3 (ℓ "丽") ∷
   rw⁻ 101 q27 ∷
   rw 102 q28 ∷
   re 102 1 (ℓ "乏丶乏") ∷
   rw 101 q25 ∷
   rw 102 q29 ∷
   rw 103 q25 ∷
   re 101 3 (ℓ "中") ∷
   rw 102 q27 ∷
   rw 103 q30 ∷
   rw 104 q24 ∷
   re 103 1 (ℓ "乏丧乏") ∷
   rw⁻ 105 q25 ∷
   rw 104 q26 ∷
   rw⁻ 103 q25 ∷
   re 104 3 (ℓ "丽") ∷
   rw⁻ 102 q27 ∷
   rw 103 q28 ∷
   re 103 1 (ℓ "乏丶乏") ∷
   rw 102 q25 ∷
   rw 103 q29 ∷
   rw 104 q25 ∷
   re 102 3 (ℓ "中") ∷
   rw 103 q27 ∷
   rw 104 q30 ∷
   rw 105 q24 ∷
   re 104 1 (ℓ "乏乄乏") ∷
   rw⁻ 106 q25 ∷
   rw 105 q31 ∷
   rw⁻ 104 q25 ∷
   re 105 3 (ℓ "乔") ∷
   rw⁻ 103 q27 ∷
   rw 104 q32 ∷
   re 104 1 (ℓ "乏乇乏") ∷
   rw 103 q25 ∷
   rw 104 q33 ∷
   rw 105 q25 ∷
   re 103 3 (ℓ "乑") ∷
   rw 104 q27 ∷
   rw 105 q30 ∷
   rw 104 q34 ∷
   rw 107 q24 ∷
   re 106 1 (ℓ "乏丧乏") ∷
   rw⁻ 108 q25 ∷
   rw 107 q26 ∷
   rw⁻ 106 q25 ∷
   re 107 3 (ℓ "丽") ∷
   rw⁻ 105 q27 ∷
   rw 106 q28 ∷
   re 106 1 (ℓ "乏丶乏") ∷
   rw 105 q25 ∷
   rw 106 q29 ∷
   rw 107 q25 ∷
   re 105 3 (ℓ "中") ∷
   rw 106 q27 ∷
   rw 107 q30 ∷
   rw 108 q24 ∷
   re 107 1 (ℓ "乏丧乏") ∷
   rw⁻ 109 q25 ∷
   rw 108 q26 ∷
   rw⁻ 107 q25 ∷
   re 108 3 (ℓ "丽") ∷
   rw⁻ 106 q27 ∷
   rw 107 q28 ∷
   re 107 1 (ℓ "乏丶乏") ∷
   rw 106 q25 ∷
   rw 107 q29 ∷
   rw 108 q25 ∷
   re 106 3 (ℓ "中") ∷
   rw 107 q27 ∷
   rw 108 q30 ∷
   rw 109 q24 ∷
   re 108 1 (ℓ "乏丧乏") ∷
   rw⁻ 110 q25 ∷
   rw 109 q26 ∷
   rw⁻ 108 q25 ∷
   re 109 3 (ℓ "丽") ∷
   rw⁻ 107 q27 ∷
   rw 108 q28 ∷
   re 108 1 (ℓ "乏丶乏") ∷
   rw 107 q25 ∷
   rw 108 q29 ∷
   rw 109 q25 ∷
   re 107 3 (ℓ "中") ∷
   rw 108 q27 ∷
   rw 109 q30 ∷
   rw 110 q24 ∷
   re 109 1 (ℓ "乏丧乏") ∷
   rw⁻ 111 q25 ∷
   rw 110 q26 ∷
   rw⁻ 109 q25 ∷
   re 110 3 (ℓ "丽") ∷
   rw⁻ 108 q27 ∷
   rw 109 q28 ∷
   re 109 1 (ℓ "乏丶乏") ∷
   rw 108 q25 ∷
   rw 109 q29 ∷
   rw 110 q25 ∷
   re 108 3 (ℓ "中") ∷
   rw 109 q27 ∷
   rw 110 q30 ∷
   rw 111 q24 ∷
   re 110 1 (ℓ "乏丧乏") ∷
   rw⁻ 112 q25 ∷
   rw 111 q26 ∷
   rw⁻ 110 q25 ∷
   re 111 3 (ℓ "丽") ∷
   rw⁻ 109 q27 ∷
   rw 110 q28 ∷
   re 110 1 (ℓ "乏丶乏") ∷
   rw 109 q25 ∷
   rw 110 q29 ∷
   rw 111 q25 ∷
   re 109 3 (ℓ "中") ∷
   rw 110 q27 ∷
   rw 111 q30 ∷
   rw 112 q24 ∷
   re 111 1 (ℓ "乏丧乏") ∷
   rw⁻ 113 q25 ∷
   rw 112 q26 ∷
   rw⁻ 111 q25 ∷
   re 112 3 (ℓ "丽") ∷
   rw⁻ 110 q27 ∷
   rw 111 q28 ∷
   re 111 1 (ℓ "乏丶乏") ∷
   rw 110 q25 ∷
   rw 111 q29 ∷
   rw 112 q25 ∷
   re 110 3 (ℓ "中") ∷
   rw 111 q27 ∷
   rw 112 q30 ∷
   rw 111 q23 ∷
   rw 114 q24 ∷
   re 113 1 (ℓ "乏丧乏") ∷
   rw⁻ 115 q25 ∷
   rw 114 q26 ∷
   rw⁻ 113 q25 ∷
   re 114 3 (ℓ "丽") ∷
   rw⁻ 112 q27 ∷
   rw 113 q28 ∷
   re 113 1 (ℓ "乏丶乏") ∷
   rw 112 q25 ∷
   rw 113 q29 ∷
   rw 114 q25 ∷
   re 112 3 (ℓ "中") ∷
   rw 113 q27 ∷
   rw 114 q30 ∷
   rw 115 q24 ∷
   re 114 1 (ℓ "乏丧乏") ∷
   rw⁻ 116 q25 ∷
   rw 115 q26 ∷
   rw⁻ 114 q25 ∷
   re 115 3 (ℓ "丽") ∷
   rw⁻ 113 q27 ∷
   rw 114 q28 ∷
   re 114 1 (ℓ "乏丶乏") ∷
   rw 113 q25 ∷
   rw 114 q29 ∷
   rw 115 q25 ∷
   re 113 3 (ℓ "中") ∷
   rw 114 q27 ∷
   rw 115 q30 ∷
   rw 116 q24 ∷
   re 115 1 (ℓ "乏乄乏") ∷
   rw⁻ 117 q25 ∷
   rw 116 q31 ∷
   rw⁻ 115 q25 ∷
   re 116 3 (ℓ "乔") ∷
   rw⁻ 114 q27 ∷
   rw 115 q32 ∷
   re 115 1 (ℓ "乏乇乏") ∷
   rw 114 q25 ∷
   rw 115 q33 ∷
   rw 116 q25 ∷
   re 114 3 (ℓ "乑") ∷
   rw 115 q27 ∷
   rw 116 q30 ∷
   rw 117 q24 ∷
   re 116 1 (ℓ "乏丧乏") ∷
   rw⁻ 118 q25 ∷
   rw 117 q26 ∷
   rw⁻ 116 q25 ∷
   re 117 3 (ℓ "丽") ∷
   rw⁻ 115 q27 ∷
   rw 116 q28 ∷
   re 116 1 (ℓ "乏丶乏") ∷
   rw 115 q25 ∷
   rw 116 q29 ∷
   rw 117 q25 ∷
   re 115 3 (ℓ "中") ∷
   rw 116 q27 ∷
   rw 117 q30 ∷
   rw 118 q24 ∷
   re 117 1 (ℓ "乏乄乏") ∷
   rw⁻ 119 q25 ∷
   rw 118 q31 ∷
   rw⁻ 117 q25 ∷
   re 118 3 (ℓ "乔") ∷
   rw⁻ 116 q27 ∷
   rw 117 q32 ∷
   re 117 1 (ℓ "乏乇乏") ∷
   rw 116 q25 ∷
   rw 117 q33 ∷
   rw 118 q25 ∷
   re 116 3 (ℓ "乑") ∷
   rw 117 q27 ∷
   rw 118 q30 ∷
   rw 119 q24 ∷
   re 118 1 (ℓ "乏乄乏") ∷
   rw⁻ 120 q25 ∷
   rw 119 q31 ∷
   rw⁻ 118 q25 ∷
   re 119 3 (ℓ "乔") ∷
   rw⁻ 117 q27 ∷
   rw 118 q32 ∷
   re 118 1 (ℓ "乏乇乏") ∷
   rw 117 q25 ∷
   rw 118 q33 ∷
   rw 119 q25 ∷
   re 117 3 (ℓ "乑") ∷
   rw 118 q27 ∷
   rw 119 q30 ∷
   rw⁻ 118 q14 ∷
   rw⁻ 119 q13 ∷
   rw 120 q35 ∷ []) Eq.refl
