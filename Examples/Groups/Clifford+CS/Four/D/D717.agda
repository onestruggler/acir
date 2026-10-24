{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD717 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D717 (W : Ws) (Sᴰ : SD717) where

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
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 : St 2104
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 : St 2105
  lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 : St 2106
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 = pickᴰ 2 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q4 : Eqn
  q4 = wE 772 W
  q5 : Eqn
  q5 = wE 7 W
  q6 : Eqn
  q6 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q7 : Eqn
  q7 = wE 6 W
  q8 : Eqn
  q8 = wE 481 W
  q9 : Eqn
  q9 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q10 : Eqn
  q10 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q11 : Eqn
  q11 = wE 1618 W
  q12 : Eqn
  q12 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q13 : Eqn
  q13 = wE 39 W
  q14 : Eqn
  q14 = wE 329 W
  q15 : Eqn
  q15 = wE 315 W
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 31 W
  q18 : Eqn
  q18 = sE 2106 lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3
  q19 : Eqn
  q19 = wE 1619 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X2 X3]: 191 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞") (ℓ "丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 64 q1 ∷
   rw⁻ 63 q2 ∷
   rw⁻ 62 q3 ∷
   rw 61 q4 ∷
   rw 60 q4 ∷
   rw 59 q5 ∷
   rw 58 q4 ∷
   rw 57 q5 ∷
   rw 56 q5 ∷
   re 55 1 (ℓ "乏乃乏") ∷
   rw⁻ 57 q6 ∷
   rw 56 q7 ∷
   rw⁻ 55 q6 ∷
   re 56 3 (ℓ "乓") ∷
   rw 54 q5 ∷
   rw 53 q5 ∷
   rw 52 q5 ∷
   rw 51 q5 ∷
   rw 50 q5 ∷
   rw 49 q5 ∷
   rw 48 q8 ∷
   rw 47 q4 ∷
   rw 46 q5 ∷
   rw 45 q5 ∷
   rw 44 q5 ∷
   rw 43 q8 ∷
   rw 42 q4 ∷
   rw 41 q8 ∷
   rw 40 q4 ∷
   re 39 1 (ℓ "乏乃乏") ∷
   rw⁻ 41 q6 ∷
   rw 40 q7 ∷
   rw⁻ 39 q6 ∷
   re 40 3 (ℓ "乓") ∷
   rw⁻ 38 q9 ∷
   rw⁻ 37 q9 ∷
   rw⁻ 36 q10 ∷
   rw⁻ 35 q9 ∷
   rw⁻ 34 q10 ∷
   rw⁻ 33 q10 ∷
   rw⁻ 32 q2 ∷
   rw⁻ 31 q3 ∷
   rw 32 q11 ∷
   rw 31 q2 ∷
   rw 32 q9 ∷
   rw 33 q10 ∷
   rw 34 q10 ∷
   rw 35 q12 ∷
   rw 36 q2 ∷
   rw 37 q2 ∷
   rw 38 q10 ∷
   rw 39 q10 ∷
   rw 40 q9 ∷
   rw 41 q10 ∷
   rw 42 q9 ∷
   rw 43 q9 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q6 ∷
   rw 45 q13 ∷
   rw 46 q6 ∷
   re 44 3 (ℓ "乐") ∷
   rw 45 q14 ∷
   rw 46 q15 ∷
   rw 47 q14 ∷
   rw 48 q15 ∷
   rw 49 q16 ∷
   rw 50 q16 ∷
   rw 51 q16 ∷
   rw 52 q14 ∷
   rw 53 q15 ∷
   rw 54 q16 ∷
   rw 55 q16 ∷
   rw 56 q16 ∷
   rw 57 q16 ∷
   rw 58 q16 ∷
   rw 59 q16 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q6 ∷
   rw 61 q13 ∷
   rw 62 q6 ∷
   re 60 3 (ℓ "乐") ∷
   rw 61 q16 ∷
   rw 62 q16 ∷
   rw 63 q14 ∷
   rw 64 q16 ∷
   rw 65 q14 ∷
   rw 66 q14 ∷
   rw 67 q2 ∷
   rw 68 q2 ∷
   rw 69 q9 ∷
   rw 70 q10 ∷
   rw 71 q10 ∷
   rw 72 q12 ∷
   rw 73 q2 ∷
   rw 74 q17 ∷
   rw 0 q18 ∷
   rw 43 q1 ∷
   rw⁻ 42 q2 ∷
   rw⁻ 41 q12 ∷
   rw⁻ 40 q10 ∷
   rw⁻ 39 q10 ∷
   rw⁻ 38 q9 ∷
   rw⁻ 37 q2 ∷
   rw⁻ 36 q2 ∷
   rw 35 q4 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   re 29 1 (ℓ "乏乃乏") ∷
   rw⁻ 31 q6 ∷
   rw 30 q7 ∷
   rw⁻ 29 q6 ∷
   re 30 3 (ℓ "乓") ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   rw 22 q8 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q8 ∷
   rw 16 q4 ∷
   rw 15 q8 ∷
   rw 14 q4 ∷
   re 13 1 (ℓ "乏乃乏") ∷
   rw⁻ 15 q6 ∷
   rw 14 q7 ∷
   rw⁻ 13 q6 ∷
   re 14 3 (ℓ "乓") ∷
   rw⁻ 12 q9 ∷
   rw⁻ 11 q9 ∷
   rw⁻ 10 q10 ∷
   rw⁻ 9 q9 ∷
   rw⁻ 8 q10 ∷
   rw⁻ 7 q10 ∷
   rw⁻ 6 q2 ∷
   rw⁻ 5 q2 ∷
   rw⁻ 4 q12 ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q10 ∷
   rw⁻ 1 q9 ∷
   rw⁻ 0 q2 ∷
   rw 1 q19 ∷
   rw 0 q3 ∷
   rw 1 q2 ∷
   rw 2 q10 ∷
   rw 3 q10 ∷
   rw 4 q9 ∷
   rw 5 q10 ∷
   rw 6 q9 ∷
   rw 7 q9 ∷
   re 9 1 (ℓ "乏乆乏") ∷
   rw 8 q6 ∷
   rw 9 q13 ∷
   rw 10 q6 ∷
   re 8 3 (ℓ "乐") ∷
   rw 9 q14 ∷
   rw 10 q15 ∷
   rw 11 q14 ∷
   rw 12 q15 ∷
   rw 13 q16 ∷
   rw 14 q16 ∷
   rw 15 q16 ∷
   rw 16 q14 ∷
   rw 17 q15 ∷
   rw 18 q16 ∷
   rw 19 q16 ∷
   rw 20 q16 ∷
   rw 21 q16 ∷
   rw 22 q16 ∷
   rw 23 q16 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q6 ∷
   rw 25 q13 ∷
   rw 26 q6 ∷
   re 24 3 (ℓ "乐") ∷
   rw 25 q16 ∷
   rw 26 q16 ∷
   rw 27 q14 ∷
   rw 28 q16 ∷
   rw 29 q14 ∷
   rw 30 q14 ∷
   rw 31 q3 ∷
   rw 32 q2 ∷
   rw 33 q17 ∷ []) Eq.refl

private
  q20 : Eqn
  q20 = wE 1628 W
  q21 : Eqn
  q21 = sE 2104 lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2
  q22 : Eqn
  q22 = wE 1629 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X1 X2]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘") (ℓ "丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q20 ∷
   rw 0 q21 ∷
   rw 0 q22 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = sE 2105 lem-Bar⟨SSSKSS23-⟶0⟩-passes-factors-of-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2

-- pass [CS02 CS02 CS02 CK20 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CS03 CK30 CS03 CS03] [X1 X2 CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01 X1 X2]: 3 steps
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 : ⟪ (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘") ⟫ʷ ≈ ⟪ (ℓ "丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中") ⟫ʷ
lem-pass-CS02-CS02-CS02-CK20-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-X2-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-X1-X2 = derive (ℓ "丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘") (ℓ "丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘丧丧丧乄丧丧乌中中中中中中乑业中中中中中中中中中乌中中中乑中中")
  (rw 31 q20 ∷
   rw 0 q23 ∷
   rw 0 q22 ∷ []) Eq.refl
