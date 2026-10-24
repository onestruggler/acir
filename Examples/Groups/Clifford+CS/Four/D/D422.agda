{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D422 (W : Ws) where

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
  q2 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "丳乏") (ℓ "乏丳") (low-comm (CX₁₀) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = wE 464 W
  q6 : Eqn
  q6 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = wE 1152 W
  q9 : Eqn
  q9 = wE 151 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK30 CK30] [X1 CX10 X1]: 107 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX10-X1 : ⟪ (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丳丒") ⟫ʷ ≈ ⟪ (ℓ "丒丳丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-CX10-X1 = derive (ℓ "丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑丒丳丒") (ℓ "丒丳丒丠丠临丠临临乀乑业乑业中中中乑业中中中中中中乀中中乑中乑乑")
  (rw 32 q1 ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q2 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q4 ∷
   re 27 1 (ℓ "乏乄乏") ∷
   rw 29 q4 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q4 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw 27 q4 ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q4 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q4 ∷
   re 22 1 (ℓ "乏丹乏") ∷
   rw 24 q4 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q4 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q4 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q4 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q4 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q4 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q4 ∷
   rw 15 q5 ∷
   re 14 1 (ℓ "乏乄乏") ∷
   rw 16 q4 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q4 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q4 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q4 ∷
   rw 10 q5 ∷
   re 9 1 (ℓ "乏乄乏") ∷
   rw 11 q4 ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "乏乄乏") ∷
   rw 9 q4 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q4 ∷
   rw 5 q6 ∷
   rw 4 q6 ∷
   rw 3 q7 ∷
   rw 2 q6 ∷
   rw 1 q7 ∷
   rw 0 q7 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q3 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 5 q6 ∷
   rw⁻ 6 q7 ∷
   rw⁻ 7 q6 ∷
   rw⁻ 8 q6 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乀") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 11 q9 ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乑") ∷
   rw 13 q9 ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "中") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "乑") ∷
   rw 18 q9 ∷
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
   rw 32 q4 ∷ []) Eq.refl

private
  q10 : Eqn
  q10 = wE 1153 W
  q11 : Eqn
  q11 = wE 1154 W
  q12 : Eqn
  q12 = eqn (ℓ "丒乖") (ℓ "乖丒") (low-comm ((X ↑)) (CX₁₀))
  q13 : Eqn
  q13 = eqn (ℓ "丳乖") (ℓ "乖丳") (low-comm (CX₁₀) (CX₁₀))
  q14 : Eqn
  q14 = wE 1155 W
  q15 : Eqn
  q15 = wE 1156 W
  q16 : Eqn
  q16 = wE 1157 W
  q17 : Eqn
  q17 = wE 1158 W

-- pass [TOFF213] [X1 CX10 X1]: 25 steps
lem-pass-TOFF213-vs-X1-CX10-X1 : ⟪ (ℓ "乥丒丳丒") ⟫ʷ ≈ ⟪ (ℓ "丒丳丒乥") ⟫ʷ
lem-pass-TOFF213-vs-X1-CX10-X1 = derive (ℓ "乥丒丳丒") (ℓ "丒丳丒乥")
  (rw 0 q10 ∷
   rw 6 q11 ∷
   rw⁻ 5 q12 ∷
   rw⁻ 6 q13 ∷
   rw⁻ 7 q12 ∷
   rw 4 q14 ∷
   rw⁻ 3 q12 ∷
   rw⁻ 4 q13 ∷
   rw⁻ 5 q12 ∷
   rw 2 q15 ∷
   rw 5 q1 ∷
   rw 4 q2 ∷
   rw 3 q3 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q4 ∷
   rw 2 q15 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "丽") ∷
   rw 5 q4 ∷
   rw 0 q16 ∷
   rw 3 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = wE 1159 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX12 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CS02 CK20 CS02 CS02] [X1 CX10 X1]: 1 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CX10-X1 : ⟪ (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丒丳丒") ⟫ʷ ≈ ⟪ (ℓ "丒丳丒丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-X1-CX10-X1 = derive (ℓ "丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧丒丳丒") (ℓ "丒丳丒丠丠丠临丠丠丹丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧丹丧丧丧乄丧丧")
  (rw 0 q18 ∷ []) Eq.refl

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [X1 CX10 X1]: 1 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CX10-X1 : ⟪ (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丳丒") ⟫ʷ ≈ ⟪ (ℓ "丒丳丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-X1-CX10-X1 = derive (ℓ "丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄丒丳丒") (ℓ "丒丳丒丠丠临丠临临丹乄且乄且丧丧丧乄且丧丧丧丧丧丧丹丧丧乄丧乄乄")
  (rw 0 q8 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 452 W
  q20 : Eqn
  q20 = wE 453 W

-- b2g 0100R1: 2 steps
lem-b2g-0100R1 : ⟪ (ℓ "丒与丐丽习举习丑丏丒") ⟫ʷ ≈ ⟪ (ℓ "丏丑与与丽习举习丏丏丐与") ⟫ʷ
lem-b2g-0100R1 = derive (ℓ "丒与丐丽习举习丑丏丒") (ℓ "丏丑与与丽习举习丏丏丐与")
  (rw 0 q19 ∷
   rw 8 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 173 W
  q22 : Eqn
  q22 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q23 : Eqn
  q23 = wE 1098 W
  q24 : Eqn
  q24 = wE 175 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CSd03 X3]: 89 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd03-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮丞") ⟫ʷ ≈ ⟪ (ℓ "丞丮丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd03-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞丮丞") (ℓ "丞丮丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 34 q1 ∷
   rw 33 q21 ∷
   re 32 1 (ℓ "乏丨乏") ∷
   rw 34 q4 ∷
   rw 31 q21 ∷
   rw 30 q7 ∷
   rw 29 q7 ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q7 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q4 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   rw 14 q22 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   rw 9 q7 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q23 ∷
   rw 0 q24 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "丮") ∷
   rw 2 q24 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q7 ∷
   rw⁻ 12 q7 ∷
   rw⁻ 13 q7 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q22 ∷
   rw⁻ 18 q7 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 21 q7 ∷
   rw⁻ 22 q7 ∷
   rw⁻ 23 q7 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 25 q7 ∷
   rw⁻ 26 q7 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 28 q7 ∷
   rw⁻ 29 q7 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q6 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q7 ∷
   rw 34 q4 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = wE 1099 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CS03 X3]: 89 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞中丞") ⟫ʷ ≈ ⟪ (ℓ "丞中丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS03-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞中丞") (ℓ "丞中丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 34 q1 ∷
   rw 33 q21 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q4 ∷
   rw 31 q21 ∷
   rw 30 q7 ∷
   rw 29 q7 ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q7 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q4 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   rw 14 q22 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   rw 9 q7 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q25 ∷
   rw 0 q24 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q24 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q7 ∷
   rw⁻ 12 q7 ∷
   rw⁻ 13 q7 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q22 ∷
   rw⁻ 18 q7 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 21 q7 ∷
   rw⁻ 22 q7 ∷
   rw⁻ 23 q7 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 25 q7 ∷
   rw⁻ 26 q7 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 28 q7 ∷
   rw⁻ 29 q7 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q6 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q7 ∷
   rw 34 q4 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1087 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CSd13 X3]: 89 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞举丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CSd13-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞举丞") (ℓ "丞举丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 34 q1 ∷
   rw 33 q21 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 34 q4 ∷
   rw 31 q21 ∷
   rw 30 q7 ∷
   rw 29 q7 ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q7 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q4 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   rw 14 q22 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   rw 9 q7 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q26 ∷
   rw 0 q24 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "举") ∷
   rw 2 q24 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q7 ∷
   rw⁻ 12 q7 ∷
   rw⁻ 13 q7 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q22 ∷
   rw⁻ 18 q7 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 21 q7 ∷
   rw⁻ 22 q7 ∷
   rw⁻ 23 q7 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 25 q7 ∷
   rw⁻ 26 q7 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 28 q7 ∷
   rw⁻ 29 q7 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q6 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q7 ∷
   rw 34 q4 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 658 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CKd31 X3]: 89 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd31-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乕丞") ⟫ʷ ≈ ⟪ (ℓ "丞乕丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CKd31-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乕丞") (ℓ "丞乕丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 34 q1 ∷
   rw 33 q21 ∷
   re 32 1 (ℓ "乏么乏") ∷
   rw 34 q4 ∷
   rw 31 q21 ∷
   rw 30 q7 ∷
   rw 29 q7 ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q7 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q4 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q7 ∷
   rw 19 q7 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   rw 14 q22 ∷
   rw 13 q6 ∷
   rw 12 q7 ∷
   rw 11 q7 ∷
   rw 10 q7 ∷
   rw 9 q7 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q4 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q4 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q4 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q4 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q4 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q4 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q4 ∷
   rw 1 q27 ∷
   rw 0 q24 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乕") ∷
   rw 2 q24 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 10 q7 ∷
   rw⁻ 11 q7 ∷
   rw⁻ 12 q7 ∷
   rw⁻ 13 q7 ∷
   rw⁻ 14 q7 ∷
   rw⁻ 15 q7 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q22 ∷
   rw⁻ 18 q7 ∷
   rw⁻ 19 q7 ∷
   rw⁻ 20 q7 ∷
   rw⁻ 21 q7 ∷
   rw⁻ 22 q7 ∷
   rw⁻ 23 q7 ∷
   rw⁻ 24 q7 ∷
   rw⁻ 25 q7 ∷
   rw⁻ 26 q7 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 28 q7 ∷
   rw⁻ 29 q7 ∷
   rw⁻ 30 q7 ∷
   rw⁻ 31 q6 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q7 ∷
   rw 34 q4 ∷ []) Eq.refl
