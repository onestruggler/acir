{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD634 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D634 (W : Ws) (Sᴰ : SD634) where

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
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-III-units-1 : St 1518
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-III-units-1 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 : St 1519
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 = pickᴰ 1 Sᴰ
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-III-units-3 : St 1520
  lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-III-units-3 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 : St 1521
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 = pickᴰ 3 Sᴰ
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3 : St 1522
  lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3 = pickᴰ 4 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~31-⟶2⟩ : St 1523
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~31-⟶2⟩ = pickᴰ 5 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSSKSS~31-⟶2⟩ : St 1524
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSSKSS~31-⟶2⟩ = pickᴰ 6 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-III-units-2 : St 1525
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-III-units-2 = pickᴰ 7 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 : St 1526
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 = pickᴰ 8 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-X3 : St 1527
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-X3 = pickᴰ 9 Sᴰ

private
  q1 : Eqn
  q1 = wE 1618 W
  q2 : Eqn
  q2 = sE 1519 lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3
  q3 : Eqn
  q3 = wE 1619 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12 X2 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞") (ℓ "丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 29 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 1906 W
  q5 : Eqn
  q5 = sE 1518 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-III-units-1
  q6 : Eqn
  q6 = wE 1907 W

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02] [X3 TOFF123 X3]: 3 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-TOFF123-X3 : ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫") ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-TOFF123-X3 = derive (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乢丞") (ℓ "丞乢丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫")
  (rw 29 q4 ∷
   rw 0 q5 ∷
   rw 0 q6 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q9 : Eqn
  q9 = eqn (ℓ "並世") (ℓ "世並") (low-comm (Swap) (K))
  q10 : Eqn
  q10 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q11 : Eqn
  q11 = wE 30 W
  q12 : Eqn
  q12 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q13 : Eqn
  q13 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q14 : Eqn
  q14 = wE 27 W
  q15 : Eqn
  q15 = wE 122 W
  q16 : Eqn
  q16 = wE 31 W
  q17 : Eqn
  q17 = wE 127 W
  q18 : Eqn
  q18 = wE 7 W
  q19 : Eqn
  q19 = wE 74 W
  q20 : Eqn
  q20 = wE 334 W
  q21 : Eqn
  q21 = wE 1886 W
  q22 : Eqn
  q22 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q23 : Eqn
  q23 = wE 142 W
  q24 : Eqn
  q24 = wE 121 W
  q25 : Eqn
  q25 = wE 123 W
  q26 : Eqn
  q26 = wE 24 W
  q27 : Eqn
  q27 = wE 25 W
  q28 : Eqn
  q28 = wE 124 W
  q29 : Eqn
  q29 = wE 125 W
  q30 : Eqn
  q30 = wE 139 W
  q31 : Eqn
  q31 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q32 : Eqn
  q32 = sE 1525 lem-Bar⟨SSSKSS31-⟶0⟩-passes-III-units-2
  q33 : Eqn
  q33 = wE 137 W
  q34 : Eqn
  q34 = wE 118 W
  q35 : Eqn
  q35 = wE 140 W
  q36 : Eqn
  q36 = wE 1887 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 TOFF203 X3]: 171 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乤丞") ⟫ʷ ≈ ⟪ (ℓ "丞乤丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞乤丞") (ℓ "丞乤丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 34 q7 ∷
   rw⁻ 33 q8 ∷
   re 32 1 (ℓ "並乥並") ∷
   re 33 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 32 q9 ∷
   rw 33 q10 ∷
   rw 34 q11 ∷
   rw 35 q12 ∷
   rw 36 q11 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q13 ∷
   rw 38 q14 ∷
   rw 39 q13 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q9 ∷
   rw 39 q15 ∷
   rw 40 q16 ∷
   rw 39 q17 ∷
   rw⁻ 38 q9 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw⁻ 39 q13 ∷
   rw 38 q18 ∷
   rw⁻ 37 q13 ∷
   re 38 3 (ℓ "丽") ∷
   rw 36 q19 ∷
   rw⁻ 35 q12 ∷
   rw 34 q19 ∷
   rw⁻ 33 q10 ∷
   rw⁻ 32 q9 ∷
   rw 33 q20 ∷
   re 33 8 (ℓ "乥") ∷
   rw⁻ 31 q8 ∷
   rw 32 q21 ∷
   rw 31 q8 ∷
   rw 32 q22 ∷
   rw 33 q8 ∷
   rw 34 q8 ∷
   re 36 1 (ℓ "乏乇乏") ∷
   rw 35 q13 ∷
   rw 36 q23 ∷
   rw 37 q13 ∷
   re 35 3 (ℓ "乑") ∷
   rw 36 q8 ∷
   rw 37 q8 ∷
   re 39 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 38 q24 ∷
   rw 39 q10 ∷
   rw 40 q11 ∷
   rw 41 q12 ∷
   rw 42 q11 ∷
   re 44 1 (ℓ "乏丶乏") ∷
   rw 43 q13 ∷
   rw 44 q14 ∷
   rw 45 q13 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q24 ∷
   rw 45 q15 ∷
   rw 38 q7 ∷
   rw 39 q25 ∷
   rw 40 q10 ∷
   rw 41 q26 ∷
   rw 42 q12 ∷
   rw 43 q26 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 44 q13 ∷
   rw 45 q27 ∷
   rw 46 q13 ∷
   re 44 3 (ℓ "丽") ∷
   rw 45 q25 ∷
   rw 46 q28 ∷
   rw 39 q29 ∷
   re 39 8 (ℓ "乢") ∷
   re 38 3 (ℓ "也") ∷
   rw 39 q8 ∷
   rw 40 q8 ∷
   re 42 1 (ℓ "乏么乏") ∷
   rw 41 q13 ∷
   rw 42 q30 ∷
   rw 43 q13 ∷
   re 41 3 (ℓ "乒") ∷
   rw 42 q8 ∷
   rw 43 q8 ∷
   rw 44 q31 ∷
   rw 45 q8 ∷
   rw 46 q16 ∷
   rw 0 q32 ∷
   rw 15 q7 ∷
   rw⁻ 14 q8 ∷
   rw⁻ 13 q31 ∷
   rw⁻ 12 q8 ∷
   rw⁻ 11 q8 ∷
   re 10 1 (ℓ "乏久乏") ∷
   rw⁻ 12 q13 ∷
   rw 11 q33 ∷
   rw⁻ 10 q13 ∷
   re 11 3 (ℓ "乕") ∷
   rw⁻ 9 q8 ∷
   rw⁻ 8 q8 ∷
   re 7 1 (ℓ "並乢並") ∷
   re 8 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 7 q24 ∷
   rw 8 q10 ∷
   rw 9 q11 ∷
   rw 10 q12 ∷
   rw 11 q11 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q13 ∷
   rw 13 q14 ∷
   rw 14 q13 ∷
   re 12 3 (ℓ "中") ∷
   rw 13 q24 ∷
   rw 14 q15 ∷
   rw 15 q16 ∷
   rw 14 q17 ∷
   rw 13 q34 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q13 ∷
   rw 13 q18 ∷
   rw⁻ 12 q13 ∷
   re 13 3 (ℓ "丽") ∷
   rw 11 q19 ∷
   rw⁻ 10 q12 ∷
   rw 9 q19 ∷
   rw⁻ 8 q10 ∷
   rw 7 q34 ∷
   rw 8 q29 ∷
   re 8 8 (ℓ "乢") ∷
   rw⁻ 6 q8 ∷
   rw⁻ 5 q8 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw⁻ 6 q13 ∷
   rw 5 q35 ∷
   rw⁻ 4 q13 ∷
   re 5 3 (ℓ "乔") ∷
   rw⁻ 3 q8 ∷
   rw⁻ 2 q8 ∷
   rw⁻ 1 q22 ∷
   rw⁻ 0 q8 ∷
   rw 1 q36 ∷
   rw 0 q8 ∷
   re 2 1 (ℓ "世义丹乊丹丽世丁") ∷
   rw 1 q9 ∷
   rw 2 q10 ∷
   rw 3 q11 ∷
   rw 4 q12 ∷
   rw 5 q11 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q13 ∷
   rw 7 q14 ∷
   rw 8 q13 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q9 ∷
   rw 8 q15 ∷
   rw 1 q7 ∷
   rw 2 q9 ∷
   rw 3 q10 ∷
   rw 4 q26 ∷
   rw 5 q12 ∷
   rw 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q13 ∷
   rw 8 q27 ∷
   rw 9 q13 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q9 ∷
   rw 9 q28 ∷
   rw 2 q20 ∷
   re 2 8 (ℓ "乥") ∷
   re 1 3 (ℓ "乤") ∷
   rw 2 q8 ∷
   rw 3 q16 ∷ []) Eq.refl

private
  q37 : Eqn
  q37 = wE 1904 W
  q38 : Eqn
  q38 = sE 1527 lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-X3
  q39 : Eqn
  q39 = wE 1905 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 CS23 CS23 CS23 CK32 CS23 CS23 CX31 CS12 CS12 CS12 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CS12 CK12 CS12 CS12 X2 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丘丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丘丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞") (ℓ "丘丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 31 q37 ∷
   rw 0 q38 ∷
   rw 0 q39 ∷ []) Eq.refl

private
  q40 : Eqn
  q40 = sE 1526 lem-Bar⟨SSSKSS31-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12 X2 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞") (ℓ "丘丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 31 q1 ∷
   rw 0 q40 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = wE 1908 W
  q42 : Eqn
  q42 = sE 1524 lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSSKSS~31-⟶2⟩
  q43 : Eqn
  q43 = wE 1909 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS23 CS23 CS23 CK32 CS23 CS23 CX31 CS12 CS12 CS12 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CS12 CK12 CS12 CS12 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞") ⟫ʷ ≈ ⟪ (ℓ "丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞") (ℓ "丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q41 ∷
   rw 0 q42 ∷
   rw 0 q43 ∷ []) Eq.refl

private
  q44 : Eqn
  q44 = wE 1910 W
  q45 : Eqn
  q45 = sE 1523 lem-Bar⟨SSKSKK32-⟶0⟩-passes-Fredkin-WBar⟨SSKSKK~31-⟶2⟩
  q46 : Eqn
  q46 = wE 1911 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞") ⟫ʷ ≈ ⟪ (ℓ "丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞") (ℓ "丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q44 ∷
   rw 0 q45 ∷
   rw 0 q46 ∷ []) Eq.refl

private
  q47 : Eqn
  q47 = wE 1912 W
  q48 : Eqn
  q48 = sE 1522 lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3
  q49 : Eqn
  q49 = wE 1913 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X1 X2 X3 CS12 CS12 CS12 CK21 CS12 CS12 CX23 CS13 CS13 CS13 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CS13 CK31 CS13 CS13 X1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS12-CS12-CS12-CK21-CS12-CS12-CX23-CS13-CS13-CS13-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CS13-CK31-CS13-CS13-X1-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞") (ℓ "丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q47 ∷
   rw 0 q48 ∷
   rw 0 q49 ∷ []) Eq.refl

private
  q50 : Eqn
  q50 = wE 1914 W
  q51 : Eqn
  q51 = sE 1521 lem-Bar⟨SSKSKK23-⟶0⟩-passes-factors-of-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3
  q52 : Eqn
  q52 = wE 1915 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [X1 X2 X3 CS12 CS12 CK21 CS12 CK21 CK21 CX23 CK31 S3 CK31 S3 CS13 CS13 CS13 CK31 S3 CS13 CS13 CS13 CS13 CS13 CS13 CX23 CS13 CS13 CK31 CS13 CK31 CK31 X1 X2 X3]: 3 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-X1-X2-X3-CS12-CS12-CK21-CS12-CK21-CK21-CX23-CK31-S3-CK31-S3-CS13-CS13-CS13-CK31-S3-CS13-CS13-CS13-CS13-CS13-CS13-CX23-CS13-CS13-CK31-CS13-CK31-CK31-X1-X2-X3 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞") (ℓ "丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (rw 29 q50 ∷
   rw 0 q51 ∷
   rw 0 q52 ∷ []) Eq.refl

private
  q53 : Eqn
  q53 = wE 1896 W
  q54 : Eqn
  q54 = sE 1520 lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'20-⟶1⟩-passes-III-units-3
  q55 : Eqn
  q55 = wE 1897 W

-- pass [CS12 CS12 CK21 CS12 CK21 CK21 CX20 CK01 S0 CK01 S0 CS01 CS01 CS01 CK01 S0 CS01 CS01 CS01 CS01 CS01 CS01 CX20 CS01 CS01 CK01 CS01 CK01 CK01] [X2 TOFF312 X2]: 3 steps
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-TOFF312-X2 : ⟪ (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乨丘") ⟫ʷ ≈ ⟪ (ℓ "丘乨丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两") ⟫ʷ
lem-pass-CS12-CS12-CK21-CS12-CK21-CK21-CX20-CK01-S0-CK01-S0-CS01-CS01-CS01-CK01-S0-CS01-CS01-CS01-CS01-CS01-CS01-CX20-CS01-CS01-CK01-CS01-CK01-CK01-vs-X2-TOFF312-X2 = derive (ℓ "丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丘乨丘") (ℓ "丘乨丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两")
  (rw 29 q53 ∷
   rw 0 q54 ∷
   rw 0 q55 ∷ []) Eq.refl
