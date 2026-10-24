{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D370 (W : Ws) where

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
  q3 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = wE 140 W
  q6 : Eqn
  q6 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 1006 W
  q9 : Eqn
  q9 = wE 27 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 31 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CS03 X3]: 127 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CS03-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞中丞") (ℓ "丞中丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "丽") ∷
   rw⁻ 31 q2 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw⁻ 24 q6 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw⁻ 14 q7 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q3 ∷
   rw 5 q4 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q5 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q3 ∷
   rw 2 q4 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q3 ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q8 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丶乏") ∷
   rw 1 q3 ∷
   rw 2 q9 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 6 q9 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q3 ∷
   rw 7 q10 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q7 ∷
   rw 18 q9 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q6 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q9 ∷
   rw 31 q10 ∷
   rw 32 q9 ∷
   rw 33 q9 ∷
   rw 34 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 76 W
  q13 : Eqn
  q13 = wE 1007 W
  q14 : Eqn
  q14 = wE 29 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CSd03 X3]: 127 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd03-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CSd03-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞丮丞") (ℓ "丞丮丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 34 q1 ∷
   rw⁻ 33 q2 ∷
   re 32 1 (ℓ "乏丨乏") ∷
   rw⁻ 34 q3 ∷
   rw 33 q12 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (ℓ "举") ∷
   rw⁻ 31 q2 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q4 ∷
   rw 26 q4 ∷
   rw 25 q4 ∷
   rw⁻ 24 q6 ∷
   rw 23 q4 ∷
   rw 22 q4 ∷
   rw 21 q4 ∷
   rw 20 q4 ∷
   rw 19 q4 ∷
   rw 18 q4 ∷
   rw 17 q4 ∷
   rw 16 q4 ∷
   rw 15 q4 ∷
   rw⁻ 14 q7 ∷
   rw 13 q5 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw 8 q4 ∷
   rw 7 q4 ∷
   rw⁻ 6 q6 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q3 ∷
   rw 6 q4 ∷
   rw⁻ 5 q3 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q3 ∷
   rw 5 q4 ∷
   rw⁻ 4 q3 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q3 ∷
   rw 4 q5 ∷
   rw⁻ 3 q3 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q3 ∷
   rw 3 q4 ∷
   rw⁻ 2 q3 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q3 ∷
   rw 2 q4 ∷
   rw⁻ 1 q3 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q3 ∷
   rw 1 q4 ∷
   rw⁻ 0 q3 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q13 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q3 ∷
   rw 2 q14 ∷
   rw 3 q3 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q2 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q3 ∷
   rw 4 q9 ∷
   rw 5 q3 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw 6 q3 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q3 ∷
   rw 6 q9 ∷
   rw 7 q3 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q3 ∷
   rw 7 q10 ∷
   rw 8 q3 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 9 q3 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q3 ∷
   rw 9 q9 ∷
   rw 10 q3 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   rw 10 q9 ∷
   rw 11 q9 ∷
   rw 12 q9 ∷
   rw 13 q9 ∷
   rw 14 q9 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q7 ∷
   rw 18 q9 ∷
   rw 19 q9 ∷
   rw 20 q9 ∷
   rw 21 q9 ∷
   rw 22 q9 ∷
   rw 23 q9 ∷
   rw 24 q9 ∷
   rw 25 q9 ∷
   rw 26 q9 ∷
   rw 27 q6 ∷
   rw 28 q9 ∷
   rw 29 q9 ∷
   rw 30 q9 ∷
   rw 31 q10 ∷
   rw 32 q9 ∷
   rw 33 q9 ∷
   rw 34 q11 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = wE 1 W
  q16 : Eqn
  q16 = wE 173 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q19 : Eqn
  q19 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q21 : Eqn
  q21 = wE 1008 W
  q22 : Eqn
  q22 = wE 175 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS03 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS03-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中丞") (ℓ "丞中丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q15 ∷
   rw 31 q16 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q17 ∷
   rw 29 q16 ∷
   rw 28 q18 ∷
   rw 27 q18 ∷
   rw 26 q19 ∷
   rw 25 q18 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q17 ∷
   rw 21 q19 ∷
   rw 20 q19 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   rw 17 q19 ∷
   rw 16 q19 ∷
   rw 15 q20 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q18 ∷
   rw 8 q20 ∷
   rw 7 q18 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q17 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q17 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q17 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q17 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q17 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q17 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q17 ∷
   rw 1 q21 ∷
   rw 0 q22 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q22 ∷
   rw 5 q15 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q15 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q18 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q18 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q19 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q18 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q19 ∷
   rw⁻ 24 q19 ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "乓") ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 31 q18 ∷
   rw 32 q17 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1009 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CSd03 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CSd03-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丮丞") (ℓ "丞丮丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q15 ∷
   rw 31 q16 ∷
   re 30 1 (ℓ "乏丨乏") ∷
   rw 32 q17 ∷
   rw 29 q16 ∷
   rw 28 q18 ∷
   rw 27 q18 ∷
   rw 26 q19 ∷
   rw 25 q18 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q17 ∷
   rw 21 q19 ∷
   rw 20 q19 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   rw 17 q19 ∷
   rw 16 q19 ∷
   rw 15 q20 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q18 ∷
   rw 8 q20 ∷
   rw 7 q18 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q17 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q17 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q17 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q17 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q17 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q17 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q17 ∷
   rw 1 q23 ∷
   rw 0 q22 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q22 ∷
   rw 5 q15 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q15 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q18 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q18 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q19 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q18 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q19 ∷
   rw⁻ 24 q19 ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "乓") ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 31 q18 ∷
   rw 32 q17 ∷ []) Eq.refl

private
  q24 : Eqn
  q24 = wE 404 W

-- pass [X3 CKd32 X3] [TOFF123]: 1 steps
lem-pass-X3-CKd32-X3-vs-TOFF123 : ⟪ (ℓ "丞乘丞乢") ⟫ʷ ≈ ⟪ (ℓ "乢丞乘丞") ⟫ʷ
lem-pass-X3-CKd32-X3-vs-TOFF123 = derive (ℓ "丞乘丞乢") (ℓ "乢丞乘丞")
  (rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 1010 W

-- pass [CCZ123] [X3 CS13 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CS13-X3 : ⟪ (ℓ "乜丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CS13-X3 = derive (ℓ "乜丞丽丞") (ℓ "丞丽丞乜")
  (rw 0 q25 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1011 W

-- pass [CCZ123] [X3 CK31 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CK31-X3 : ⟪ (ℓ "乜丞乔丞") ⟫ʷ ≈ ⟪ (ℓ "丞乔丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CK31-X3 = derive (ℓ "乜丞乔丞") (ℓ "丞乔丞乜")
  (rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 1012 W

-- pass [CZ12] [CS13]: 1 steps
lem-pass-CZ12-vs-CS13 : ⟪ (ℓ "丸丽") ⟫ʷ ≈ ⟪ (ℓ "丽丸") ⟫ʷ
lem-pass-CZ12-vs-CS13 = derive (ℓ "丸丽") (ℓ "丽丸")
  (rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = wE 1013 W

-- pass [CZ12] [CSd13]: 1 steps
lem-pass-CZ12-vs-CSd13 : ⟪ (ℓ "丸举") ⟫ʷ ≈ ⟪ (ℓ "举丸") ⟫ʷ
lem-pass-CZ12-vs-CSd13 = derive (ℓ "丸举") (ℓ "举丸")
  (rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 21 W
  q30 : Eqn
  q30 = eqn (ℓ "丢乊") (ℓ "乊丢") (low-comm (CZ) ((CS • CS • CS)))
  q31 : Eqn
  q31 = wE 51 W

-- pass [CZ02] [CSd13]: 15 steps
lem-pass-CZ02-vs-CSd13 : ⟪ (ℓ "丩举") ⟫ʷ ≈ ⟪ (ℓ "举丩") ⟫ʷ
lem-pass-CZ02-vs-CSd13 = derive (ℓ "丩举") (ℓ "举丩")
  (re 1 1 (ℓ "乏丷乏") ∷
   rw 0 q15 ∷
   re 1 3 (ℓ "丯") ∷
   re 1 1 (ℓ "乏丼丢丼乏") ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "举") ∷
   rw 4 q29 ∷
   rw 3 q30 ∷
   rw 2 q31 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 1 q17 ∷
   re 2 5 (ℓ "丯") ∷
   re 2 1 (ℓ "乏丩乏") ∷
   rw 4 q17 ∷
   re 0 3 (ℓ "举") ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = wE 1014 W

-- pass [CCZ123] [X3 CKd31 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CKd31-X3 : ⟪ (ℓ "乜丞乕丞") ⟫ʷ ≈ ⟪ (ℓ "丞乕丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CKd31-X3 = derive (ℓ "乜丞乕丞") (ℓ "丞乕丞乜")
  (rw 0 q32 ∷ []) Eq.refl

private
  q33 : Eqn
  q33 = wE 1015 W

-- pass [CCZ123] [X3 CSd13 X3]: 1 steps
lem-pass-CCZ123-vs-X3-CSd13-X3 : ⟪ (ℓ "乜丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞乜") ⟫ʷ
lem-pass-CCZ123-vs-X3-CSd13-X3 = derive (ℓ "乜丞举丞") (ℓ "丞举丞乜")
  (rw 0 q33 ∷ []) Eq.refl

private
  q34 : Eqn
  q34 = wE 419 W

-- pass [X3 CK32 X3] [TOFF123]: 1 steps
lem-pass-X3-CK32-X3-vs-TOFF123 : ⟪ (ℓ "丞乗丞乢") ⟫ʷ ≈ ⟪ (ℓ "乢丞乗丞") ⟫ʷ
lem-pass-X3-CK32-X3-vs-TOFF123 = derive (ℓ "丞乗丞乢") (ℓ "乢丞乗丞")
  (rw 0 q34 ∷ []) Eq.refl

private
  q35 : Eqn
  q35 = wE 1016 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CS13 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丞") ⟫ʷ ≈ ⟪ (ℓ "丞丽丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CS13-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞丽丞") (ℓ "丞丽丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q15 ∷
   rw 31 q16 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q17 ∷
   rw 29 q16 ∷
   rw 28 q18 ∷
   rw 27 q18 ∷
   rw 26 q19 ∷
   rw 25 q18 ∷
   rw 24 q19 ∷
   rw 23 q19 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q17 ∷
   rw 21 q19 ∷
   rw 20 q19 ∷
   rw 19 q19 ∷
   rw 18 q19 ∷
   rw 17 q19 ∷
   rw 16 q19 ∷
   rw 15 q20 ∷
   rw 14 q18 ∷
   rw 13 q19 ∷
   rw 12 q19 ∷
   rw 11 q19 ∷
   rw 10 q20 ∷
   rw 9 q18 ∷
   rw 8 q20 ∷
   rw 7 q18 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q17 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q17 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q17 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q17 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q17 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q17 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q17 ∷
   rw 1 q35 ∷
   rw 0 q22 ∷
   rw 3 q15 ∷
   re 1 3 (ℓ "丽") ∷
   rw 2 q22 ∷
   rw 5 q15 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q15 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q15 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q15 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q15 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q15 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q15 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q18 ∷
   rw⁻ 11 q20 ∷
   rw⁻ 12 q18 ∷
   rw⁻ 13 q20 ∷
   rw⁻ 14 q19 ∷
   rw⁻ 15 q19 ∷
   rw⁻ 16 q19 ∷
   rw⁻ 17 q18 ∷
   rw⁻ 18 q20 ∷
   rw⁻ 19 q19 ∷
   rw⁻ 20 q19 ∷
   rw⁻ 21 q19 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 23 q19 ∷
   rw⁻ 24 q19 ∷
   rw 27 q15 ∷
   re 25 3 (ℓ "乓") ∷
   rw⁻ 26 q19 ∷
   rw⁻ 27 q19 ∷
   rw⁻ 28 q18 ∷
   rw⁻ 29 q19 ∷
   rw⁻ 30 q18 ∷
   rw⁻ 31 q18 ∷
   rw 32 q17 ∷ []) Eq.refl
