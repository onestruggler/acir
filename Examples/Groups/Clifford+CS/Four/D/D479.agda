{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D479 (W : Ws) where

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
  q1 = wE 1257 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 107 W
  q4 : Eqn
  q4 = eqn (ℓ "两之") (ℓ "之两") (low-comm (CK₀₁) (CZ))
  q5 : Eqn
  q5 = wE 108 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = eqn (ℓ "丠之") (ℓ "之丠") (low-comm (CS) (CZ))
  q8 : Eqn
  q8 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q9 : Eqn
  q9 = wE 1258 W
  q10 : Eqn
  q10 = eqn (ℓ "丈丿") (ℓ "丿丈") (low₁-comm (S) ((Swap ↑ • CZ • Swap ↑)))
  q11 : Eqn
  q11 = wE 1259 W
  q12 : Eqn
  q12 = wE 106 W
  q13 : Eqn
  q13 = wE 1260 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12] [CZ13]: 299 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-CZ13 : ⟪ (ℓ "丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丿") ⟫ʷ ≈ ⟪ (ℓ "丿丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-CZ13 = derive (ℓ "丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丿") (ℓ "丿丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为")
  (rw 0 q1 ∷
   re 29 1 (ℓ "乏丸乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丼两丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "丿") ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏丸乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丫乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "丿") ∷
   re 28 1 (ℓ "乏丸乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "丱") ∷
   re 28 1 (ℓ "乏丼两丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "丿") ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏丸乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "丱") ∷
   re 29 1 (ℓ "乏丫乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "丿") ∷
   re 27 1 (ℓ "乏丸乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "丿") ∷
   rw 30 q3 ∷
   rw 29 q7 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏丸乏") ∷
   rw 27 q6 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q6 ∷
   re 26 3 (ℓ "丿") ∷
   re 26 1 (ℓ "乏丸乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "丱") ∷
   re 26 1 (ℓ "乏丼两丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "丿") ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏丸乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "丱") ∷
   re 27 1 (ℓ "乏丫乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "丿") ∷
   re 25 1 (ℓ "乏丸乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "丿") ∷
   rw 28 q3 ∷
   rw 27 q7 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏丸乏") ∷
   rw 25 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 24 3 (ℓ "丿") ∷
   re 24 1 (ℓ "乏丸乏") ∷
   rw 23 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "丿") ∷
   rw 27 q3 ∷
   rw 26 q7 ∷
   rw 25 q5 ∷
   re 25 1 (ℓ "乏丸乏") ∷
   rw 24 q6 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q6 ∷
   re 23 3 (ℓ "丿") ∷
   rw 24 q2 ∷
   re 23 1 (ℓ "乏丸乏") ∷
   rw 25 q6 ∷
   rw 22 q8 ∷
   rw 23 q9 ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "丿") ∷
   rw⁻ 23 q8 ∷
   rw 24 q6 ∷
   re 22 1 (ℓ "乏丸乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "丿") ∷
   rw 25 q3 ∷
   rw 24 q7 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏丸乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "丿") ∷
   re 21 1 (ℓ "乏丸乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "丿") ∷
   rw 24 q3 ∷
   rw 23 q7 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏丸乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "丿") ∷
   re 20 1 (ℓ "乏丸乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "丿") ∷
   rw 23 q3 ∷
   rw 22 q7 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏丸乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 19 3 (ℓ "丿") ∷
   re 19 1 (ℓ "乏丸乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "丿") ∷
   rw 22 q3 ∷
   rw 21 q7 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏丸乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 18 3 (ℓ "丿") ∷
   re 18 1 (ℓ "乏丸乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "丿") ∷
   rw 21 q3 ∷
   rw 20 q7 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏丸乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "丿") ∷
   re 17 1 (ℓ "乏丸乏") ∷
   rw 16 q2 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q2 ∷
   re 21 3 (ℓ "丿") ∷
   rw 20 q3 ∷
   rw 19 q7 ∷
   rw 18 q5 ∷
   re 18 1 (ℓ "乏丸乏") ∷
   rw 17 q6 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q6 ∷
   re 16 3 (ℓ "丿") ∷
   rw 15 q10 ∷
   re 15 1 (ℓ "乏丸乏") ∷
   rw 14 q2 ∷
   re 15 3 (ℓ "丱") ∷
   re 15 1 (ℓ "乏丼两丼乏") ∷
   rw 21 q2 ∷
   re 19 3 (ℓ "丿") ∷
   rw 18 q3 ∷
   rw 17 q4 ∷
   rw 16 q5 ∷
   re 16 1 (ℓ "乏丸乏") ∷
   rw 15 q6 ∷
   re 16 5 (ℓ "丱") ∷
   re 16 1 (ℓ "乏丫乏") ∷
   rw 18 q6 ∷
   re 14 3 (ℓ "丿") ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 13 q2 ∷
   re 14 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏丼丠丼乏") ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "丿") ∷
   rw 17 q3 ∷
   rw 16 q7 ∷
   rw 15 q5 ∷
   re 15 1 (ℓ "乏丸乏") ∷
   rw 14 q6 ∷
   re 15 5 (ℓ "中") ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q6 ∷
   re 13 3 (ℓ "丿") ∷
   re 13 1 (ℓ "乏丸乏") ∷
   rw 12 q2 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q2 ∷
   re 17 3 (ℓ "丿") ∷
   rw 16 q3 ∷
   rw 15 q7 ∷
   rw 14 q5 ∷
   re 14 1 (ℓ "乏丸乏") ∷
   rw 13 q6 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q6 ∷
   re 12 3 (ℓ "丿") ∷
   re 12 1 (ℓ "乏丸乏") ∷
   rw 11 q2 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "丿") ∷
   rw 15 q3 ∷
   rw 14 q7 ∷
   rw 13 q5 ∷
   re 13 1 (ℓ "乏丸乏") ∷
   rw 12 q6 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q6 ∷
   re 11 3 (ℓ "丿") ∷
   rw 10 q10 ∷
   re 10 1 (ℓ "乏丸乏") ∷
   rw 9 q2 ∷
   re 10 3 (ℓ "丱") ∷
   re 10 1 (ℓ "乏丼两丼乏") ∷
   rw 16 q2 ∷
   re 14 3 (ℓ "丿") ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   rw 11 q5 ∷
   re 11 1 (ℓ "乏丸乏") ∷
   rw 10 q6 ∷
   re 11 5 (ℓ "丱") ∷
   re 11 1 (ℓ "乏丫乏") ∷
   rw 13 q6 ∷
   re 9 3 (ℓ "丿") ∷
   rw 8 q10 ∷
   re 8 1 (ℓ "乏丸乏") ∷
   rw 7 q2 ∷
   re 8 3 (ℓ "丱") ∷
   re 8 1 (ℓ "乏丼两丼乏") ∷
   rw 14 q2 ∷
   re 12 3 (ℓ "丿") ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   rw 9 q5 ∷
   re 9 1 (ℓ "乏丸乏") ∷
   rw 8 q6 ∷
   re 9 5 (ℓ "丱") ∷
   re 9 1 (ℓ "乏丫乏") ∷
   rw 11 q6 ∷
   re 7 3 (ℓ "丿") ∷
   rw 8 q2 ∷
   re 7 1 (ℓ "乏丸乏") ∷
   rw 9 q6 ∷
   rw 6 q8 ∷
   rw 7 q9 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "丿") ∷
   rw⁻ 7 q8 ∷
   rw 8 q6 ∷
   rw 5 q11 ∷
   rw 4 q11 ∷
   rw 3 q12 ∷
   rw 2 q11 ∷
   rw 1 q12 ∷
   rw 0 q12 ∷
   rw 1 q13 ∷ []) Eq.refl

private
  q14 : Eqn
  q14 = wE 1261 W

-- pass [CS02 CS02 CK02 CS02 CK02 CK02 CX01 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX01 CS12 CS12 CK12 CS12 CK12 CK12] [CS01]: 1 steps
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-CS01 : ⟪ (ℓ "丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丠") ⟫ʷ ≈ ⟪ (ℓ "丠丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为") ⟫ʷ
lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-vs-CS01 = derive (ℓ "丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为丠") (ℓ "丠丧丧丫丧丫丫丣为与为与丶丶丶为与丶丶丶丶丶丶丣丶丶为丶为为")
  (rw 0 q14 ∷ []) Eq.refl
