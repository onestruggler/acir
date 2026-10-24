{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D075 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = wE 582 W
  q8 : Eqn
  q8 = wE 175 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 CK31 X3]: 85 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK31-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乔丞") ⟫ʷ ≈ ⟪ (ℓ "丞乔丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-CK31-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乔丞") (ℓ "丞乔丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q3 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q3 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q3 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q3 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乔") ∷
   rw 2 q8 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乑") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q4 ∷
   rw⁻ 13 q6 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw⁻ 23 q5 ∷
   rw⁻ 24 q5 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乓") ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q5 ∷
   rw⁻ 30 q4 ∷
   rw⁻ 31 q4 ∷
   rw 32 q3 ∷ []) Eq.refl

private
  q9 : Eqn
  q9 = wE 583 W
  q10 : Eqn
  q10 = wE 151 W
  q11 : Eqn
  q11 = wE 107 W
  q12 : Eqn
  q12 = eqn (ℓ "临之") (ℓ "之临") (low-comm (CK₁₀) (CZ))
  q13 : Eqn
  q13 = wE 108 W
  q14 : Eqn
  q14 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q15 : Eqn
  q15 = wE 584 W
  q16 : Eqn
  q16 = eqn (ℓ "丸业") (ℓ "业丸") (low₃-comm ((CZ ↑)) (S))
  q17 : Eqn
  q17 = wE 585 W
  q18 : Eqn
  q18 = wE 110 W
  q19 : Eqn
  q19 = wE 464 W
  q20 : Eqn
  q20 = wE 586 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [CZ12]: 351 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CZ12 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丸") ⟫ʷ ≈ ⟪ (ℓ "丸中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CZ12 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丸") (ℓ "丸中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q1 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q3 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q3 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q3 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q3 ∷
   rw 1 q9 ∷
   rw⁻ 0 q5 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q4 ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乀") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乑") ∷
   rw 8 q10 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乑") ∷
   rw 10 q10 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乑") ∷
   rw 15 q10 ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "乀") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乑") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乑") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乑") ∷
   rw 29 q3 ∷
   re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丿") ∷
   rw 31 q11 ∷
   rw 30 q12 ∷
   rw 29 q13 ∷
   re 29 1 (ℓ "乏丸乏") ∷
   rw 28 q3 ∷
   re 29 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丿") ∷
   rw 30 q11 ∷
   rw 29 q12 ∷
   rw 28 q13 ∷
   re 28 1 (ℓ "乏丸乏") ∷
   rw 27 q3 ∷
   re 28 5 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "丿") ∷
   rw 29 q11 ∷
   rw 28 q14 ∷
   rw 27 q13 ∷
   re 27 1 (ℓ "乏丸乏") ∷
   rw 26 q3 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼临丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "丿") ∷
   rw 28 q11 ∷
   rw 27 q12 ∷
   rw 26 q13 ∷
   re 26 1 (ℓ "乏丸乏") ∷
   rw 25 q3 ∷
   re 26 5 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丿") ∷
   rw 27 q11 ∷
   rw 26 q14 ∷
   rw 25 q13 ∷
   re 25 1 (ℓ "乏丸乏") ∷
   rw 24 q3 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丿") ∷
   rw 26 q11 ∷
   rw 25 q14 ∷
   rw 24 q13 ∷
   re 24 1 (ℓ "乏丸乏") ∷
   rw 23 q3 ∷
   re 24 5 (ℓ "中") ∷
   rw 22 q15 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丿") ∷
   rw 24 q11 ∷
   rw 23 q14 ∷
   rw 22 q13 ∷
   re 22 1 (ℓ "乏丸乏") ∷
   rw 21 q3 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丿") ∷
   rw 23 q11 ∷
   rw 22 q14 ∷
   rw 21 q13 ∷
   re 21 1 (ℓ "乏丸乏") ∷
   rw 20 q3 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丿") ∷
   rw 22 q11 ∷
   rw 21 q14 ∷
   rw 20 q13 ∷
   re 20 1 (ℓ "乏丸乏") ∷
   rw 19 q3 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丿") ∷
   rw 21 q11 ∷
   rw 20 q14 ∷
   rw 19 q13 ∷
   re 19 1 (ℓ "乏丸乏") ∷
   rw 18 q3 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丿") ∷
   rw 20 q11 ∷
   rw 19 q14 ∷
   rw 18 q13 ∷
   re 18 1 (ℓ "乏丸乏") ∷
   rw 17 q3 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丿") ∷
   rw 19 q11 ∷
   rw 18 q14 ∷
   rw 17 q13 ∷
   re 17 1 (ℓ "乏丸乏") ∷
   rw 16 q3 ∷
   re 17 5 (ℓ "中") ∷
   rw⁻ 15 q16 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "丿") ∷
   rw 17 q11 ∷
   rw 16 q12 ∷
   rw 15 q13 ∷
   re 15 1 (ℓ "乏丸乏") ∷
   rw 14 q3 ∷
   re 15 5 (ℓ "乑") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丿") ∷
   rw 16 q11 ∷
   rw 15 q14 ∷
   rw 14 q13 ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 13 q3 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丿") ∷
   rw 15 q11 ∷
   rw 14 q14 ∷
   rw 13 q13 ∷
   re 13 1 (ℓ "乏丸乏") ∷
   rw 12 q3 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丿") ∷
   rw 14 q11 ∷
   rw 13 q14 ∷
   rw 12 q13 ∷
   re 12 1 (ℓ "乏丸乏") ∷
   rw 11 q3 ∷
   re 12 5 (ℓ "中") ∷
   rw⁻ 10 q16 ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "丿") ∷
   rw 12 q11 ∷
   rw 11 q12 ∷
   rw 10 q13 ∷
   re 10 1 (ℓ "乏丸乏") ∷
   rw 9 q3 ∷
   re 10 5 (ℓ "乑") ∷
   rw⁻ 8 q16 ∷
   re 7 1 (ℓ "乏丼临丼乏") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "丿") ∷
   rw 10 q11 ∷
   rw 9 q12 ∷
   rw 8 q13 ∷
   re 8 1 (ℓ "乏丸乏") ∷
   rw 7 q3 ∷
   re 8 5 (ℓ "乑") ∷
   rw 6 q15 ∷
   rw 5 q17 ∷
   rw 4 q17 ∷
   rw 3 q18 ∷
   rw 2 q17 ∷
   rw 1 q18 ∷
   rw 0 q18 ∷
   rw 30 q1 ∷
   re 29 1 (ℓ "乏乄乏") ∷
   rw 31 q3 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q3 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q3 ∷
   re 26 1 (ℓ "乏乄乏") ∷
   rw 28 q3 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q3 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q3 ∷
   re 23 1 (ℓ "乏丹乏") ∷
   rw 25 q3 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q3 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q3 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q3 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q3 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q3 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q3 ∷
   rw 16 q19 ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q3 ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q3 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q3 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q3 ∷
   rw 11 q19 ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw 12 q3 ∷
   rw 9 q19 ∷
   re 8 1 (ℓ "乏乄乏") ∷
   rw 10 q3 ∷
   re 7 1 (ℓ "乏丹乏") ∷
   rw 9 q3 ∷
   rw 6 q4 ∷
   rw 5 q4 ∷
   rw 4 q5 ∷
   rw 3 q4 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw 2 q20 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乑") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乓") ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乓") ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   rw 30 q3 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 587 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [CS13]: 81 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS13 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丽") ⟫ʷ ≈ ⟪ (ℓ "丽中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-CS13 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丽") (ℓ "丽中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 30 q1 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q3 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q3 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q3 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q3 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q3 ∷
   rw 1 q21 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "丽") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乑") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乓") ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q5 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乓") ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 26 q4 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q4 ∷
   rw⁻ 29 q4 ∷
   rw 30 q3 ∷ []) Eq.refl
