{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD636 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D636 (W : Ws) (Sᴰ : SD636) where

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
  lem-pass-X0-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-vs-X3-TOFF213-X3 : St 1532
  lem-pass-X0-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-vs-X3-TOFF213-X3 = pickᴰ 0 Sᴰ
  lem-pass-X0-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X0-vs-X3-TOFF213-X3 : St 1533
  lem-pass-X0-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X0-vs-X3-TOFF213-X3 = pickᴰ 1 Sᴰ

private
  q1 : Eqn
  q1 = wE 1389 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 173 W
  q4 : Eqn
  q4 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q9 : Eqn
  q9 = wE 1918 W
  q10 : Eqn
  q10 = wE 175 W
  q11 : Eqn
  q11 = sE 1532 lem-pass-X0-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-vs-X3-TOFF213-X3
  q12 : Eqn
  q12 = wE 1919 W
  q13 : Eqn
  q13 = wE 1392 W

-- pass [TOFF213] [X0 X3 CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10 X0 X3]: 173 steps
lem-pass-TOFF213-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 : ⟪ (ℓ "乥丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X0-X3-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-X0-X3 = derive (ℓ "乥丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞") (ℓ "丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞乥")
  (rw 0 q1 ∷
   rw 38 q2 ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw 33 q6 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   rw 30 q6 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 31 q7 ∷
   rw 28 q6 ∷
   rw 27 q6 ∷
   rw 26 q6 ∷
   rw 25 q6 ∷
   rw 24 q6 ∷
   rw 23 q6 ∷
   rw 22 q8 ∷
   rw 21 q5 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q8 ∷
   rw 16 q5 ∷
   rw 15 q8 ∷
   rw 14 q5 ∷
   re 13 1 (ℓ "乏乆乏") ∷
   rw 15 q7 ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw 14 q7 ∷
   re 11 1 (ℓ "乏乄乏") ∷
   rw 13 q7 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q7 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q7 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q7 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q7 ∷
   rw 6 q3 ∷
   rw 5 q4 ∷
   rw 4 q3 ∷
   rw 5 q9 ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q2 ∷
   re 9 3 (ℓ "乑") ∷
   rw 12 q2 ∷
   re 10 3 (ℓ "乑") ∷
   rw 13 q2 ∷
   re 11 3 (ℓ "乓") ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q8 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q8 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q6 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q8 ∷
   rw⁻ 21 q6 ∷
   rw⁻ 22 q6 ∷
   rw⁻ 23 q6 ∷
   rw⁻ 24 q6 ∷
   rw⁻ 25 q6 ∷
   rw⁻ 26 q6 ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 28 q6 ∷
   rw⁻ 29 q6 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 31 q6 ∷
   rw⁻ 32 q5 ∷
   rw⁻ 33 q5 ∷
   rw⁻ 34 q4 ∷
   rw 35 q10 ∷
   rw 36 q7 ∷
   rw⁻ 1 q11 ∷
   rw 32 q2 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q6 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q7 ∷
   rw 23 q6 ∷
   rw 22 q6 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q8 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q6 ∷
   rw 13 q6 ∷
   rw 12 q8 ∷
   rw 11 q5 ∷
   rw 10 q8 ∷
   rw 9 q5 ∷
   re 8 1 (ℓ "乏乆乏") ∷
   rw 10 q7 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q7 ∷
   re 6 1 (ℓ "乏乄乏") ∷
   rw 8 q7 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q7 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q7 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q7 ∷
   rw 1 q4 ∷
   rw 0 q3 ∷
   rw 1 q12 ∷
   rw⁻ 0 q4 ∷
   rw 1 q10 ∷
   rw 4 q2 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "乑") ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q2 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "乓") ∷
   rw⁻ 9 q5 ∷
   rw⁻ 10 q8 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q8 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 14 q6 ∷
   rw⁻ 15 q6 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q8 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q6 ∷
   rw⁻ 20 q6 ∷
   rw⁻ 21 q6 ∷
   rw⁻ 22 q6 ∷
   rw⁻ 23 q6 ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "乓") ∷
   rw⁻ 25 q6 ∷
   rw⁻ 26 q6 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 31 q4 ∷
   rw 32 q10 ∷
   rw 33 q10 ∷
   rw 34 q7 ∷
   rw 33 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q16 : Eqn
  q16 = wE 1106 W
  q17 : Eqn
  q17 = wE 7 W
  q18 : Eqn
  q18 = wE 140 W
  q19 : Eqn
  q19 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q20 : Eqn
  q20 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q21 : Eqn
  q21 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 1920 W
  q23 : Eqn
  q23 = wE 317 W
  q24 : Eqn
  q24 = wE 27 W
  q25 : Eqn
  q25 = wE 142 W
  q26 : Eqn
  q26 = wE 31 W
  q27 : Eqn
  q27 = sE 1533 lem-pass-X0-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X0-vs-X3-TOFF213-X3
  q28 : Eqn
  q28 = wE 1921 W

-- pass [TOFF213] [X0 X3 CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02 X0 X3]: 245 steps
lem-pass-TOFF213-vs-X0-X3-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X0-X3 : ⟪ (ℓ "乥丌丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丌丞乥") ⟫ʷ
lem-pass-TOFF213-vs-X0-X3-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-X0-X3 = derive (ℓ "乥丌丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丌丞") (ℓ "丌丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丌丞乥")
  (rw 0 q1 ∷
   rw 40 q14 ∷
   rw⁻ 39 q15 ∷
   rw 38 q16 ∷
   rw 37 q17 ∷
   rw 36 q17 ∷
   rw 35 q18 ∷
   rw 34 q17 ∷
   rw 33 q17 ∷
   rw 32 q17 ∷
   rw⁻ 31 q19 ∷
   rw 30 q17 ∷
   rw 29 q17 ∷
   rw 28 q17 ∷
   rw 27 q17 ∷
   rw 26 q17 ∷
   rw 25 q17 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   rw 22 q17 ∷
   rw⁻ 21 q20 ∷
   rw 20 q18 ∷
   rw 19 q17 ∷
   rw 18 q17 ∷
   rw 17 q17 ∷
   rw 16 q17 ∷
   rw 15 q17 ∷
   rw 14 q17 ∷
   rw⁻ 13 q19 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q21 ∷
   rw 13 q17 ∷
   rw⁻ 12 q21 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q21 ∷
   rw 12 q17 ∷
   rw⁻ 11 q21 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw⁻ 12 q21 ∷
   rw 11 q18 ∷
   rw⁻ 10 q21 ∷
   re 11 3 (ℓ "乔") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q21 ∷
   rw 10 q17 ∷
   rw⁻ 9 q21 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q21 ∷
   rw 9 q17 ∷
   rw⁻ 8 q21 ∷
   re 9 3 (ℓ "丽") ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q21 ∷
   rw 8 q17 ∷
   rw⁻ 7 q21 ∷
   re 8 3 (ℓ "丽") ∷
   rw⁻ 6 q15 ∷
   rw 5 q16 ∷
   rw⁻ 4 q15 ∷
   rw 5 q22 ∷
   rw 4 q23 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q21 ∷
   rw 6 q24 ∷
   rw 7 q21 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q21 ∷
   rw 7 q24 ∷
   rw 8 q21 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 9 q21 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q21 ∷
   rw 9 q25 ∷
   rw 10 q21 ∷
   re 8 3 (ℓ "乑") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 9 q21 ∷
   rw 10 q24 ∷
   rw 11 q21 ∷
   re 9 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 10 q21 ∷
   rw 11 q24 ∷
   rw 12 q21 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q19 ∷
   rw 12 q24 ∷
   rw 13 q24 ∷
   rw 14 q24 ∷
   rw 15 q24 ∷
   rw 16 q24 ∷
   rw 17 q24 ∷
   rw 18 q25 ∷
   rw 19 q20 ∷
   rw 20 q24 ∷
   rw 21 q24 ∷
   rw 22 q24 ∷
   rw 23 q24 ∷
   rw 24 q24 ∷
   rw 25 q24 ∷
   rw 26 q24 ∷
   rw 27 q24 ∷
   rw 28 q24 ∷
   rw 29 q19 ∷
   rw 30 q24 ∷
   rw 31 q24 ∷
   rw 32 q24 ∷
   rw 33 q25 ∷
   rw 34 q24 ∷
   rw 35 q24 ∷
   rw 36 q23 ∷
   rw 37 q15 ∷
   rw 38 q26 ∷
   rw⁻ 1 q27 ∷
   rw 34 q14 ∷
   rw 33 q16 ∷
   rw 32 q17 ∷
   rw 31 q17 ∷
   rw 30 q18 ∷
   rw 29 q17 ∷
   rw 28 q17 ∷
   rw 27 q17 ∷
   rw⁻ 26 q19 ∷
   rw 25 q17 ∷
   rw 24 q17 ∷
   rw 23 q17 ∷
   rw 22 q17 ∷
   rw 21 q17 ∷
   rw 20 q17 ∷
   rw 19 q17 ∷
   rw 18 q17 ∷
   rw 17 q17 ∷
   rw⁻ 16 q20 ∷
   rw 15 q18 ∷
   rw 14 q17 ∷
   rw 13 q17 ∷
   rw 12 q17 ∷
   rw 11 q17 ∷
   rw 10 q17 ∷
   rw 9 q17 ∷
   rw⁻ 8 q19 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw⁻ 9 q21 ∷
   rw 8 q17 ∷
   rw⁻ 7 q21 ∷
   re 8 3 (ℓ "丽") ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q21 ∷
   rw 7 q17 ∷
   rw⁻ 6 q21 ∷
   re 7 3 (ℓ "丽") ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw⁻ 7 q21 ∷
   rw 6 q18 ∷
   rw⁻ 5 q21 ∷
   re 6 3 (ℓ "乔") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q21 ∷
   rw 5 q17 ∷
   rw⁻ 4 q21 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw⁻ 5 q21 ∷
   rw 4 q17 ∷
   rw⁻ 3 q21 ∷
   re 4 3 (ℓ "丽") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q21 ∷
   rw 3 q17 ∷
   rw⁻ 2 q21 ∷
   re 3 3 (ℓ "丽") ∷
   rw 1 q16 ∷
   rw⁻ 0 q15 ∷
   rw 1 q28 ∷
   rw 0 q23 ∷
   rw 1 q15 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q21 ∷
   rw 3 q24 ∷
   rw 4 q21 ∷
   re 2 3 (ℓ "中") ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q21 ∷
   rw 4 q24 ∷
   rw 5 q21 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q21 ∷
   rw 5 q24 ∷
   rw 6 q21 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏乇乏") ∷
   rw 5 q21 ∷
   rw 6 q25 ∷
   rw 7 q21 ∷
   re 5 3 (ℓ "乑") ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q21 ∷
   rw 7 q24 ∷
   rw 8 q21 ∷
   re 6 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q21 ∷
   rw 8 q24 ∷
   rw 9 q21 ∷
   re 7 3 (ℓ "中") ∷
   rw 8 q19 ∷
   rw 9 q24 ∷
   rw 10 q24 ∷
   rw 11 q24 ∷
   rw 12 q24 ∷
   rw 13 q24 ∷
   rw 14 q24 ∷
   rw 15 q25 ∷
   rw 16 q20 ∷
   rw 17 q24 ∷
   rw 18 q24 ∷
   rw 19 q24 ∷
   rw 20 q24 ∷
   rw 21 q24 ∷
   rw 22 q24 ∷
   rw 23 q24 ∷
   rw 24 q24 ∷
   rw 25 q24 ∷
   rw 26 q19 ∷
   rw 27 q24 ∷
   rw 28 q24 ∷
   rw 29 q24 ∷
   rw 30 q25 ∷
   rw 31 q24 ∷
   rw 32 q24 ∷
   rw 33 q23 ∷
   rw 34 q15 ∷
   rw 35 q15 ∷
   rw 36 q26 ∷
   rw 35 q13 ∷ []) Eq.refl
