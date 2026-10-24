{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D186 (W : Ws) where

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
  q3 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 196 W
  q8 : Eqn
  q8 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q9 : Eqn
  q9 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = wE 767 W
  q12 : Eqn
  q12 = wE 175 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 TOFF103 X3]: 135 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF103-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乡丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF103-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乡丞") (ℓ "丞乡丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏习乏") ∷
   re 31 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 30 q3 ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丽") ∷
   rw⁻ 32 q4 ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "举") ∷
   rw⁻ 34 q4 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw⁻ 36 q3 ∷
   rw⁻ 37 q5 ∷
   rw 38 q6 ∷
   rw 37 q5 ∷
   rw 36 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q6 ∷
   rw 34 q4 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 35 q6 ∷
   rw 32 q4 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q6 ∷
   rw 30 q3 ∷
   rw 31 q7 ∷
   re 31 8 (ℓ "习") ∷
   rw 29 q2 ∷
   rw 28 q8 ∷
   rw 27 q8 ∷
   rw 26 q9 ∷
   rw 25 q8 ∷
   rw 24 q9 ∷
   rw 23 q9 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q6 ∷
   rw 21 q9 ∷
   rw 20 q9 ∷
   rw 19 q9 ∷
   rw 18 q9 ∷
   rw 17 q9 ∷
   rw 16 q9 ∷
   rw 15 q10 ∷
   rw 14 q8 ∷
   rw 13 q9 ∷
   rw 12 q9 ∷
   rw 11 q9 ∷
   rw 10 q10 ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw 7 q8 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q6 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q6 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q6 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q6 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q6 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q6 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q6 ∷
   rw 1 q11 ∷
   rw 0 q12 ∷
   re 2 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 1 q3 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "丽") ∷
   rw⁻ 3 q4 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw⁻ 5 q4 ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw 1 q1 ∷
   rw⁻ 2 q3 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw⁻ 4 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q3 ∷
   rw⁻ 9 q5 ∷
   rw 2 q7 ∷
   re 2 8 (ℓ "习") ∷
   re 1 3 (ℓ "乡") ∷
   rw 2 q12 ∷
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
   rw⁻ 10 q8 ∷
   rw⁻ 11 q10 ∷
   rw⁻ 12 q8 ∷
   rw⁻ 13 q10 ∷
   rw⁻ 14 q9 ∷
   rw⁻ 15 q9 ∷
   rw⁻ 16 q9 ∷
   rw⁻ 17 q8 ∷
   rw⁻ 18 q10 ∷
   rw⁻ 19 q9 ∷
   rw⁻ 20 q9 ∷
   rw⁻ 21 q9 ∷
   rw⁻ 22 q9 ∷
   rw⁻ 23 q9 ∷
   rw⁻ 24 q9 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乓") ∷
   rw⁻ 26 q9 ∷
   rw⁻ 27 q9 ∷
   rw⁻ 28 q8 ∷
   rw⁻ 29 q9 ∷
   rw⁻ 30 q8 ∷
   rw⁻ 31 q8 ∷
   rw 32 q6 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 768 W

-- groups [CK32 CS23 CS23 CKd32] [X3 TOFF123 X3]: 1 steps
lem-groups-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 : ⟪ (ℓ "乗义义乘丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞乗义义乘") ⟫ʷ
lem-groups-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 = derive (ℓ "乗义义乘丞乢丞") (ℓ "丞乢丞乗义义乘")
  (rw 0 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q15 : Eqn
  q15 = wE 359 W
  q16 : Eqn
  q16 = eqn (ℓ "两乗") (ℓ "乗两") (low-comm (CK₀₁) (CK₁₀))
  q17 : Eqn
  q17 = wE 361 W
  q18 : Eqn
  q18 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q19 : Eqn
  q19 = eqn (ℓ "丠乗") (ℓ "乗丠") (low-comm (CS) (CK₁₀))
  q20 : Eqn
  q20 = wE 769 W
  q21 : Eqn
  q21 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "丈乔") (ℓ "乔丈") (low₁-comm (S) ((Swap ↑ • CK₁₀ • Swap ↑)))
  q23 : Eqn
  q23 = wE 770 W
  q24 : Eqn
  q24 = wE 771 W

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02] [X3 CK31 X3]: 351 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CK31-X3 : ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乔丞") ⟫ʷ ≈ ⟪ (ℓ "丞乔丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫") ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CK31-X3 = derive (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乔丞") (ℓ "丞乔丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫")
  (rw 28 q14 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丼两丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "乔") ∷
   rw 33 q15 ∷
   rw 32 q16 ∷
   rw 31 q17 ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q6 ∷
   re 31 5 (ℓ "丱") ∷
   re 31 1 (ℓ "乏丫乏") ∷
   rw 33 q6 ∷
   re 29 3 (ℓ "乔") ∷
   rw 30 q14 ∷
   rw 27 q14 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q1 ∷
   re 29 3 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丼两丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "乔") ∷
   rw 32 q15 ∷
   rw 31 q16 ∷
   rw 30 q17 ∷
   re 30 1 (ℓ "乏乇乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "乔") ∷
   rw 29 q14 ∷
   rw 26 q18 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "乔") ∷
   rw 31 q15 ∷
   rw 30 q19 ∷
   rw 29 q17 ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "乔") ∷
   rw 28 q18 ∷
   rw 25 q14 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "丱") ∷
   re 27 1 (ℓ "乏丼两丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乔") ∷
   rw 30 q15 ∷
   rw 29 q16 ∷
   rw 28 q17 ∷
   re 28 1 (ℓ "乏乇乏") ∷
   rw 27 q6 ∷
   re 28 5 (ℓ "丱") ∷
   re 28 1 (ℓ "乏丫乏") ∷
   rw 30 q6 ∷
   re 26 3 (ℓ "乔") ∷
   rw 27 q14 ∷
   rw 24 q18 ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乔") ∷
   rw 29 q15 ∷
   rw 28 q19 ∷
   rw 27 q17 ∷
   re 27 1 (ℓ "乏乇乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "乔") ∷
   rw 26 q18 ∷
   rw 23 q18 ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 24 q1 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乔") ∷
   rw 28 q15 ∷
   rw 27 q19 ∷
   rw 26 q17 ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 25 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 24 3 (ℓ "乔") ∷
   rw 25 q18 ∷
   rw 26 q1 ∷
   rw 25 q2 ∷
   re 24 1 (ℓ "乏乇乏") ∷
   rw 26 q6 ∷
   rw 23 q2 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw 24 q6 ∷
   rw 23 q20 ∷
   rw 22 q12 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乔") ∷
   rw 24 q12 ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q6 ∷
   rw 21 q18 ∷
   re 23 1 (ℓ "乏乇乏") ∷
   rw 22 q1 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乔") ∷
   rw 26 q15 ∷
   rw 25 q19 ∷
   rw 24 q17 ∷
   re 24 1 (ℓ "乏乇乏") ∷
   rw 23 q6 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q6 ∷
   re 22 3 (ℓ "乔") ∷
   rw 23 q18 ∷
   rw 20 q18 ∷
   re 22 1 (ℓ "乏乇乏") ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "乔") ∷
   rw 25 q15 ∷
   rw 24 q19 ∷
   rw 23 q17 ∷
   re 23 1 (ℓ "乏乇乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "乔") ∷
   rw 22 q18 ∷
   rw 19 q18 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q1 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乔") ∷
   rw 24 q15 ∷
   rw 23 q19 ∷
   rw 22 q17 ∷
   re 22 1 (ℓ "乏乇乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "乔") ∷
   rw 21 q18 ∷
   rw 18 q18 ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q1 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "乔") ∷
   rw 23 q15 ∷
   rw 22 q19 ∷
   rw 21 q17 ∷
   re 21 1 (ℓ "乏乇乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 19 3 (ℓ "乔") ∷
   rw 20 q18 ∷
   rw 17 q18 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q1 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乔") ∷
   rw 22 q15 ∷
   rw 21 q19 ∷
   rw 20 q17 ∷
   re 20 1 (ℓ "乏乇乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 18 3 (ℓ "乔") ∷
   rw 19 q18 ∷
   rw 16 q18 ∷
   re 18 1 (ℓ "乏乇乏") ∷
   rw 17 q1 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "乔") ∷
   rw 21 q15 ∷
   rw 20 q19 ∷
   rw 19 q17 ∷
   re 19 1 (ℓ "乏乇乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "乔") ∷
   rw 18 q18 ∷
   rw 15 q21 ∷
   rw 16 q22 ∷
   rw 17 q21 ∷
   rw 14 q14 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q1 ∷
   re 16 3 (ℓ "丱") ∷
   re 16 1 (ℓ "乏丼两丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "乔") ∷
   rw 19 q15 ∷
   rw 18 q16 ∷
   rw 17 q17 ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q6 ∷
   re 17 5 (ℓ "丱") ∷
   re 17 1 (ℓ "乏丫乏") ∷
   rw 19 q6 ∷
   re 15 3 (ℓ "乔") ∷
   rw 16 q14 ∷
   rw 13 q18 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q1 ∷
   re 15 3 (ℓ "中") ∷
   re 15 1 (ℓ "乏丼丠丼乏") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乔") ∷
   rw 18 q15 ∷
   rw 17 q19 ∷
   rw 16 q17 ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q6 ∷
   re 16 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q6 ∷
   re 14 3 (ℓ "乔") ∷
   rw 15 q18 ∷
   rw 12 q18 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q1 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "乔") ∷
   rw 17 q15 ∷
   rw 16 q19 ∷
   rw 15 q17 ∷
   re 15 1 (ℓ "乏乇乏") ∷
   rw 14 q6 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q6 ∷
   re 13 3 (ℓ "乔") ∷
   rw 14 q18 ∷
   rw 11 q18 ∷
   re 13 1 (ℓ "乏乇乏") ∷
   rw 12 q1 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乔") ∷
   rw 16 q15 ∷
   rw 15 q19 ∷
   rw 14 q17 ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q6 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q6 ∷
   re 12 3 (ℓ "乔") ∷
   rw 13 q18 ∷
   rw 10 q21 ∷
   rw 11 q22 ∷
   rw 12 q21 ∷
   rw 9 q14 ∷
   re 11 1 (ℓ "乏乇乏") ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "丱") ∷
   re 11 1 (ℓ "乏丼两丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "乔") ∷
   rw 14 q15 ∷
   rw 13 q16 ∷
   rw 12 q17 ∷
   re 12 1 (ℓ "乏乇乏") ∷
   rw 11 q6 ∷
   re 12 5 (ℓ "丱") ∷
   re 12 1 (ℓ "乏丫乏") ∷
   rw 14 q6 ∷
   re 10 3 (ℓ "乔") ∷
   rw 11 q14 ∷
   rw 8 q21 ∷
   rw 9 q22 ∷
   rw 10 q21 ∷
   rw 7 q14 ∷
   re 9 1 (ℓ "乏乇乏") ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "丱") ∷
   re 9 1 (ℓ "乏丼两丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乔") ∷
   rw 12 q15 ∷
   rw 11 q16 ∷
   rw 10 q17 ∷
   re 10 1 (ℓ "乏乇乏") ∷
   rw 9 q6 ∷
   re 10 5 (ℓ "丱") ∷
   re 10 1 (ℓ "乏丫乏") ∷
   rw 12 q6 ∷
   re 8 3 (ℓ "乔") ∷
   rw 9 q14 ∷
   rw 10 q1 ∷
   rw 9 q2 ∷
   re 8 1 (ℓ "乏乇乏") ∷
   rw 10 q6 ∷
   rw 7 q2 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw 8 q6 ∷
   rw 7 q20 ∷
   rw 6 q12 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "乔") ∷
   rw 8 q12 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q6 ∷
   rw 5 q23 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 2 q23 ∷
   rw 1 q24 ∷
   rw 0 q24 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 5 W
  q26 : Eqn
  q26 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q28 : Eqn
  q28 = wE 772 W
  q29 : Eqn
  q29 = wE 7 W
  q30 : Eqn
  q30 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q31 : Eqn
  q31 = wE 6 W
  q32 : Eqn
  q32 = wE 481 W
  q33 : Eqn
  q33 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q34 : Eqn
  q34 = wE 773 W
  q35 : Eqn
  q35 = wE 39 W
  q36 : Eqn
  q36 = wE 329 W
  q37 : Eqn
  q37 = wE 315 W
  q38 : Eqn
  q38 = wE 27 W
  q39 : Eqn
  q39 = wE 31 W

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02] [X3 CK32 X3]: 83 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CK32-X3 : ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乗丞") ⟫ʷ ≈ ⟪ (ℓ "丞乗丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫") ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CK32-X3 = derive (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乗丞") (ℓ "丞乗丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫")
  (rw 32 q25 ∷
   rw⁻ 31 q26 ∷
   rw⁻ 30 q27 ∷
   rw⁻ 29 q26 ∷
   rw 28 q28 ∷
   rw 27 q28 ∷
   rw 26 q29 ∷
   rw 25 q28 ∷
   rw 24 q29 ∷
   rw 23 q29 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw⁻ 24 q30 ∷
   rw 23 q31 ∷
   rw⁻ 22 q30 ∷
   re 23 3 (ℓ "乓") ∷
   rw 21 q29 ∷
   rw 20 q29 ∷
   rw 19 q29 ∷
   rw 18 q29 ∷
   rw 17 q29 ∷
   rw 16 q29 ∷
   rw 15 q32 ∷
   rw 14 q28 ∷
   rw 13 q29 ∷
   rw 12 q29 ∷
   rw 11 q29 ∷
   rw 10 q32 ∷
   rw 9 q28 ∷
   rw 8 q32 ∷
   rw 7 q28 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q30 ∷
   rw 7 q31 ∷
   rw⁻ 6 q30 ∷
   re 7 3 (ℓ "乓") ∷
   rw⁻ 5 q27 ∷
   rw⁻ 4 q27 ∷
   rw⁻ 3 q33 ∷
   rw⁻ 2 q27 ∷
   rw⁻ 1 q33 ∷
   rw⁻ 0 q33 ∷
   rw 1 q34 ∷
   rw 0 q26 ∷
   rw 1 q27 ∷
   rw 2 q26 ∷
   rw 3 q33 ∷
   rw 4 q33 ∷
   rw 5 q27 ∷
   rw 6 q33 ∷
   rw 7 q27 ∷
   rw 8 q27 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q30 ∷
   rw 10 q35 ∷
   rw 11 q30 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q36 ∷
   rw 11 q37 ∷
   rw 12 q36 ∷
   rw 13 q37 ∷
   rw 14 q38 ∷
   rw 15 q38 ∷
   rw 16 q38 ∷
   rw 17 q36 ∷
   rw 18 q37 ∷
   rw 19 q38 ∷
   rw 20 q38 ∷
   rw 21 q38 ∷
   rw 22 q38 ∷
   rw 23 q38 ∷
   rw 24 q38 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q30 ∷
   rw 26 q35 ∷
   rw 27 q30 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q38 ∷
   rw 27 q38 ∷
   rw 28 q36 ∷
   rw 29 q38 ∷
   rw 30 q36 ∷
   rw 31 q36 ∷
   rw 32 q39 ∷ []) Eq.refl
