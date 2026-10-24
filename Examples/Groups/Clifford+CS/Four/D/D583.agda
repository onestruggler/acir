{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD583 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D583 (W : Ws) (Sᴰ : SD583) where

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
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3 : St 1021
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 464 W
  q7 : Eqn
  q7 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q8 : Eqn
  q8 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q9 : Eqn
  q9 = wE 1650 W
  q10 : Eqn
  q10 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "両乏") (ℓ "乏両") (low-comm ((CS • CS • CS)) (Swap))
  q12 : Eqn
  q12 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q13 : Eqn
  q13 = wE 151 W
  q14 : Eqn
  q14 = sE 1021 lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3
  q15 : Eqn
  q15 = wE 1651 W
  q16 : Eqn
  q16 = wE 175 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X1 X3 CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30 X0 X1 X3]: 393 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X3-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-X0-X1-X3 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞") (ℓ "丌丒丞丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丌丒丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中")
  (rw 66 q1 ∷
   rw 65 q2 ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   re 62 1 (ℓ "乏乄乏") ∷
   rw 64 q5 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 63 q5 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q5 ∷
   re 59 1 (ℓ "乏乄乏") ∷
   rw 61 q5 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q5 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q5 ∷
   re 56 1 (ℓ "乏丹乏") ∷
   rw 58 q5 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q5 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q5 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q5 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q5 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q5 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q5 ∷
   rw 49 q6 ∷
   re 48 1 (ℓ "乏乄乏") ∷
   rw 50 q5 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q5 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q5 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q5 ∷
   rw 44 q6 ∷
   re 43 1 (ℓ "乏乄乏") ∷
   rw 45 q5 ∷
   rw 42 q6 ∷
   re 41 1 (ℓ "乏乄乏") ∷
   rw 43 q5 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 42 q5 ∷
   rw 39 q7 ∷
   rw 38 q7 ∷
   rw 37 q8 ∷
   rw 36 q7 ∷
   rw 35 q8 ∷
   rw 34 q8 ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 32 q9 ∷
   rw⁻ 31 q3 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q8 ∷
   rw⁻ 34 q8 ∷
   rw⁻ 35 q10 ∷
   rw⁻ 36 q3 ∷
   rw⁻ 37 q3 ∷
   rw⁻ 38 q11 ∷
   rw⁻ 39 q10 ∷
   rw⁻ 40 q8 ∷
   rw⁻ 41 q8 ∷
   rw⁻ 42 q3 ∷
   rw⁻ 43 q3 ∷
   rw⁻ 44 q7 ∷
   rw⁻ 45 q12 ∷
   rw⁻ 46 q7 ∷
   rw⁻ 47 q12 ∷
   rw⁻ 48 q8 ∷
   rw⁻ 49 q8 ∷
   rw⁻ 50 q8 ∷
   rw⁻ 51 q7 ∷
   rw⁻ 52 q12 ∷
   rw⁻ 53 q8 ∷
   rw⁻ 54 q8 ∷
   rw⁻ 55 q8 ∷
   rw⁻ 56 q8 ∷
   rw⁻ 57 q8 ∷
   rw⁻ 58 q8 ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乀") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "中") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "中") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "中") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "中") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "中") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "中") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "中") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "中") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "中") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "中") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "中") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "中") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "中") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "中") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "中") ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "中") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "中") ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "中") ∷
   rw 78 q13 ∷
   rw 79 q13 ∷
   rw 80 q13 ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "乑") ∷
   rw 82 q13 ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "中") ∷
   rw 89 q1 ∷
   re 87 3 (ℓ "中") ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "中") ∷
   rw 91 q1 ∷
   re 89 3 (ℓ "中") ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "中") ∷
   rw 93 q1 ∷
   re 91 3 (ℓ "中") ∷
   rw 92 q13 ∷
   rw 93 q13 ∷
   rw 94 q13 ∷
   rw 97 q1 ∷
   re 95 3 (ℓ "乑") ∷
   rw 96 q13 ∷
   rw 97 q13 ∷
   rw 98 q13 ∷
   rw 99 q13 ∷
   rw 102 q1 ∷
   re 100 3 (ℓ "乑") ∷
   rw 101 q13 ∷
   rw 104 q1 ∷
   re 102 3 (ℓ "乀") ∷
   rw 105 q1 ∷
   re 103 3 (ℓ "乑") ∷
   rw 104 q13 ∷
   rw 107 q1 ∷
   re 105 3 (ℓ "乑") ∷
   rw 106 q13 ∷
   rw 109 q1 ∷
   re 107 3 (ℓ "中") ∷
   rw 110 q1 ∷
   re 108 3 (ℓ "中") ∷
   rw 111 q1 ∷
   re 109 3 (ℓ "中") ∷
   rw 112 q1 ∷
   re 110 3 (ℓ "乑") ∷
   rw 111 q13 ∷
   rw 114 q1 ∷
   re 112 3 (ℓ "中") ∷
   rw 115 q1 ∷
   re 113 3 (ℓ "中") ∷
   rw 116 q1 ∷
   re 114 3 (ℓ "中") ∷
   rw 117 q1 ∷
   re 115 3 (ℓ "中") ∷
   rw 118 q1 ∷
   re 116 3 (ℓ "中") ∷
   rw 119 q1 ∷
   re 117 3 (ℓ "中") ∷
   rw⁻ 118 q3 ∷
   rw⁻ 119 q3 ∷
   rw⁻ 120 q7 ∷
   rw⁻ 121 q8 ∷
   rw⁻ 122 q8 ∷
   rw⁻ 123 q10 ∷
   rw⁻ 124 q3 ∷
   rw 125 q5 ∷
   rw 0 q14 ∷
   rw 94 q1 ∷
   rw 93 q3 ∷
   rw 92 q10 ∷
   rw 91 q8 ∷
   rw 90 q8 ∷
   rw 89 q7 ∷
   rw 88 q3 ∷
   rw 87 q3 ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q5 ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q5 ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q5 ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q5 ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q5 ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q5 ∷
   rw 80 q6 ∷
   re 79 1 (ℓ "乏乄乏") ∷
   rw 81 q5 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q5 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q5 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q5 ∷
   rw 75 q6 ∷
   re 74 1 (ℓ "乏乄乏") ∷
   rw 76 q5 ∷
   rw 73 q6 ∷
   re 72 1 (ℓ "乏乄乏") ∷
   rw 74 q5 ∷
   re 71 1 (ℓ "乏丹乏") ∷
   rw 73 q5 ∷
   rw 70 q6 ∷
   re 69 1 (ℓ "乏乄乏") ∷
   rw 71 q5 ∷
   rw 68 q6 ∷
   rw 67 q6 ∷
   rw 66 q6 ∷
   rw 65 q6 ∷
   re 64 1 (ℓ "乏乄乏") ∷
   rw 66 q5 ∷
   rw 63 q6 ∷
   rw 62 q6 ∷
   rw 61 q6 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q5 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q5 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q5 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q5 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q5 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q5 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q5 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q5 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q5 ∷
   rw 51 q6 ∷
   re 50 1 (ℓ "乏乄乏") ∷
   rw 52 q5 ∷
   rw 49 q6 ∷
   rw 48 q6 ∷
   rw 47 q6 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q5 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q5 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q5 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q5 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q5 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q5 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q5 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q5 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q5 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q5 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q5 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q5 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q5 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q5 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q5 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   re 28 1 (ℓ "乏丹乏") ∷
   rw 30 q5 ∷
   rw 27 q8 ∷
   rw 26 q8 ∷
   rw 25 q8 ∷
   rw 24 q8 ∷
   rw 23 q8 ∷
   rw 22 q8 ∷
   rw 21 q12 ∷
   rw 20 q7 ∷
   rw 19 q8 ∷
   rw 18 q8 ∷
   rw 17 q8 ∷
   rw 16 q12 ∷
   rw 15 q7 ∷
   rw 14 q12 ∷
   rw 13 q7 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q8 ∷
   rw 9 q8 ∷
   rw 8 q10 ∷
   rw 7 q11 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   rw 4 q10 ∷
   rw 3 q8 ∷
   rw 2 q8 ∷
   rw 1 q7 ∷
   rw 0 q3 ∷
   rw 1 q15 ∷
   rw⁻ 0 q4 ∷
   rw⁻ 1 q3 ∷
   rw 2 q16 ∷
   rw⁻ 3 q8 ∷
   rw⁻ 4 q8 ∷
   rw⁻ 5 q7 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q7 ∷
   rw⁻ 8 q7 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乀") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q13 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q13 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q13 ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "中") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "中") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "中") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "中") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "乀") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "乑") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乑") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乑") ∷
   rw⁻ 32 q4 ∷
   rw⁻ 33 q3 ∷
   rw 34 q16 ∷
   rw 35 q5 ∷ []) Eq.refl
