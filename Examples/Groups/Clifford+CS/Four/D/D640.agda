{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD640 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D640 (W : Ws) (Sᴰ : SD640) where

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
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 : St 1546
  lem-Bar⟨SSKSKK12-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 = pickᴰ 0 Sᴰ

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
  q7 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q9 : Eqn
  q9 = wE 1648 W
  q10 : Eqn
  q10 = eqn (ℓ "丵乏") (ℓ "乏丵") (low-comm ((S ↑ • CK₁₀)) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = sE 1546 lem-Bar⟨SSKSKK12-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3
  q14 : Eqn
  q14 = wE 1649 W
  q15 : Eqn
  q15 = wE 175 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [X0 X1 X3 CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03 X0 X1 X3]: 469 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丒丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌丒丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丞丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丌丒丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丞") (ℓ "丌丒丞丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丌丒丞丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 66 q1 ∷
   rw 65 q2 ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q5 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q5 ∷
   re 60 1 (ℓ "乏乄乏") ∷
   rw 62 q5 ∷
   re 59 1 (ℓ "乏丧乏") ∷
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
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q5 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q5 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q5 ∷
   rw 46 q6 ∷
   re 45 1 (ℓ "乏乄乏") ∷
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
   re 38 1 (ℓ "乏丹乏") ∷
   rw 40 q5 ∷
   rw 37 q7 ∷
   rw 36 q7 ∷
   rw 35 q8 ∷
   rw 34 q7 ∷
   rw 33 q7 ∷
   rw 32 q7 ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 30 q9 ∷
   rw⁻ 29 q3 ∷
   rw⁻ 30 q8 ∷
   rw⁻ 31 q7 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q10 ∷
   rw⁻ 34 q3 ∷
   rw⁻ 35 q3 ∷
   rw⁻ 36 q7 ∷
   rw⁻ 37 q7 ∷
   rw⁻ 38 q8 ∷
   rw⁻ 39 q7 ∷
   rw⁻ 40 q3 ∷
   rw⁻ 41 q3 ∷
   rw⁻ 42 q7 ∷
   rw⁻ 43 q7 ∷
   rw⁻ 44 q7 ∷
   rw⁻ 45 q7 ∷
   rw⁻ 46 q7 ∷
   rw⁻ 47 q7 ∷
   rw⁻ 48 q8 ∷
   rw⁻ 49 q11 ∷
   rw⁻ 50 q7 ∷
   rw⁻ 51 q7 ∷
   rw⁻ 52 q7 ∷
   rw⁻ 53 q7 ∷
   rw⁻ 54 q7 ∷
   rw⁻ 55 q7 ∷
   rw⁻ 56 q7 ∷
   rw⁻ 57 q7 ∷
   rw⁻ 58 q7 ∷
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
   rw 80 q1 ∷
   re 78 3 (ℓ "中") ∷
   rw 81 q1 ∷
   re 79 3 (ℓ "中") ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "中") ∷
   rw 83 q1 ∷
   re 81 3 (ℓ "中") ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "中") ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "中") ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "中") ∷
   rw 87 q1 ∷
   re 85 3 (ℓ "中") ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "中") ∷
   rw 87 q12 ∷
   rw 88 q12 ∷
   rw 89 q12 ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "乑") ∷
   rw 91 q12 ∷
   rw 94 q1 ∷
   re 92 3 (ℓ "中") ∷
   rw 95 q1 ∷
   re 93 3 (ℓ "中") ∷
   rw 96 q1 ∷
   re 94 3 (ℓ "中") ∷
   rw 97 q1 ∷
   re 95 3 (ℓ "中") ∷
   rw 98 q1 ∷
   re 96 3 (ℓ "中") ∷
   rw 99 q1 ∷
   re 97 3 (ℓ "中") ∷
   rw 100 q1 ∷
   re 98 3 (ℓ "中") ∷
   rw 101 q1 ∷
   re 99 3 (ℓ "中") ∷
   rw 102 q1 ∷
   re 100 3 (ℓ "中") ∷
   rw 103 q1 ∷
   re 101 3 (ℓ "中") ∷
   rw 104 q1 ∷
   re 102 3 (ℓ "中") ∷
   rw 105 q1 ∷
   re 103 3 (ℓ "中") ∷
   rw 106 q1 ∷
   re 104 3 (ℓ "中") ∷
   rw 107 q1 ∷
   re 105 3 (ℓ "中") ∷
   rw 108 q1 ∷
   re 106 3 (ℓ "中") ∷
   rw 109 q1 ∷
   re 107 3 (ℓ "中") ∷
   rw 110 q1 ∷
   re 108 3 (ℓ "中") ∷
   rw 111 q1 ∷
   re 109 3 (ℓ "中") ∷
   rw 112 q1 ∷
   re 110 3 (ℓ "乀") ∷
   rw 113 q1 ∷
   re 111 3 (ℓ "中") ∷
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
   re 117 3 (ℓ "乑") ∷
   rw 118 q12 ∷
   rw 121 q1 ∷
   re 119 3 (ℓ "中") ∷
   rw 122 q1 ∷
   re 120 3 (ℓ "中") ∷
   rw 123 q1 ∷
   re 121 3 (ℓ "中") ∷
   rw 124 q1 ∷
   re 122 3 (ℓ "中") ∷
   rw 125 q1 ∷
   re 123 3 (ℓ "中") ∷
   rw 126 q1 ∷
   re 124 3 (ℓ "中") ∷
   rw 127 q1 ∷
   re 125 3 (ℓ "中") ∷
   rw 128 q1 ∷
   re 126 3 (ℓ "中") ∷
   rw 129 q1 ∷
   re 127 3 (ℓ "中") ∷
   rw⁻ 128 q3 ∷
   rw⁻ 129 q3 ∷
   rw⁻ 130 q8 ∷
   rw⁻ 131 q7 ∷
   rw⁻ 132 q7 ∷
   rw⁻ 133 q10 ∷
   rw⁻ 134 q3 ∷
   rw 135 q5 ∷
   rw 0 q13 ∷
   rw 106 q1 ∷
   rw 105 q3 ∷
   rw 104 q10 ∷
   rw 103 q7 ∷
   rw 102 q7 ∷
   rw 101 q8 ∷
   rw 100 q3 ∷
   rw 99 q3 ∷
   re 98 1 (ℓ "乏丧乏") ∷
   rw 100 q5 ∷
   re 97 1 (ℓ "乏丧乏") ∷
   rw 99 q5 ∷
   re 96 1 (ℓ "乏丧乏") ∷
   rw 98 q5 ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw 97 q5 ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw 96 q5 ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw 95 q5 ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw 94 q5 ∷
   re 91 1 (ℓ "乏丧乏") ∷
   rw 93 q5 ∷
   re 90 1 (ℓ "乏丧乏") ∷
   rw 92 q5 ∷
   rw 89 q6 ∷
   re 88 1 (ℓ "乏乄乏") ∷
   rw 90 q5 ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q5 ∷
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
   re 81 1 (ℓ "乏丹乏") ∷
   rw 83 q5 ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q5 ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q5 ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q5 ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q5 ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q5 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q5 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q5 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q5 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q5 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q5 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q5 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q5 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q5 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q5 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q5 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q5 ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q5 ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q5 ∷
   rw 62 q6 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 63 q5 ∷
   rw 60 q6 ∷
   rw 59 q6 ∷
   rw 58 q6 ∷
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
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q5 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q5 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q5 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q5 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q5 ∷
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
   re 30 1 (ℓ "乏丹乏") ∷
   rw 32 q5 ∷
   rw 29 q7 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q7 ∷
   rw 24 q7 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q11 ∷
   rw 19 q8 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   rw 14 q7 ∷
   rw 13 q7 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   rw 4 q10 ∷
   rw 3 q7 ∷
   rw 2 q7 ∷
   rw 1 q8 ∷
   rw 0 q3 ∷
   rw 1 q14 ∷
   rw⁻ 0 q4 ∷
   rw⁻ 1 q3 ∷
   rw 2 q15 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 5 q7 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q7 ∷
   rw⁻ 8 q7 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乀") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q12 ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
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
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乀") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "乑") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw⁻ 34 q4 ∷
   rw⁻ 35 q3 ∷
   rw 36 q15 ∷
   rw 37 q5 ∷ []) Eq.refl
