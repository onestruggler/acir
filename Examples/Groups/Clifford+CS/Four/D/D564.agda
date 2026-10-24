{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD564 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D564 (W : Ws) (Sᴰ : SD564) where

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
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-1-2 : St 977
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-1-2 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-2-1 : St 978
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-2-1 = pickᴰ 1 Sᴰ
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 : St 979
  lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 = pickᴰ 2 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSKSKK~31-⟶2⟩ : St 980
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSKSKK~31-⟶2⟩ = pickᴰ 3 Sᴰ
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSSKSS~31-⟶2⟩ : St 981
  lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSSKSS~31-⟶2⟩ = pickᴰ 4 Sᴰ
  lem-LF-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK31-CS12-CS12-CS12-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-S2-S2-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS01-CS01-CS01-S0-CK01-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK31-at-2 : St 982
  lem-LF-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK31-CS12-CS12-CS12-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-S2-S2-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS01-CS01-CS01-S0-CK01-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK31-at-2 = pickᴰ 5 Sᴰ

private
  q1 : Eqn
  q1 = wE 1579 W
  q2 : Eqn
  q2 = sE 981 lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSSKSS~31-⟶2⟩
  q3 : Eqn
  q3 = wE 1580 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CS23 CS23 CS23 CK32 CS23 CS23 CX31 CS12 CS12 CS12 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CS12 CK12 CS12 CS12 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞") ⟫ʷ ≈ ⟪ (ℓ "丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞") (ℓ "丞义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 31 q1 ∷
   rw 0 q2 ∷
   rw 0 q3 ∷ []) Eq.refl

private
  q4 : Eqn
  q4 = wE 1581 W
  q5 : Eqn
  q5 = sE 980 lem-Bar⟨SSSKSS31-⟶0⟩-passes-comm-WBar⟨SSKSKK~31-⟶2⟩
  q6 : Eqn
  q6 = wE 1582 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX31 CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CS01 CK10 CS01 CS01] [X3 CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12 X3]: 3 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3 : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞") ⟫ʷ ≈ ⟪ (ℓ "丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X3 = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞") (ℓ "丞义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 31 q4 ∷
   rw 0 q5 ∷
   rw 0 q6 ∷ []) Eq.refl

private
  q7 : Eqn
  q7 = wE 5 W
  q8 : Eqn
  q8 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q9 : Eqn
  q9 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q10 : Eqn
  q10 = wE 772 W
  q11 : Eqn
  q11 = wE 7 W
  q12 : Eqn
  q12 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q13 : Eqn
  q13 = wE 6 W
  q14 : Eqn
  q14 = wE 481 W
  q15 : Eqn
  q15 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q16 : Eqn
  q16 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q17 : Eqn
  q17 = wE 1618 W
  q18 : Eqn
  q18 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q19 : Eqn
  q19 = wE 39 W
  q20 : Eqn
  q20 = wE 329 W
  q21 : Eqn
  q21 = wE 315 W
  q22 : Eqn
  q22 = wE 27 W
  q23 : Eqn
  q23 = wE 31 W
  q24 : Eqn
  q24 = sE 979 lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3
  q25 : Eqn
  q25 = wE 1619 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X2 X3 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X2 X3]: 191 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞") ⟫ʷ ≈ ⟪ (ℓ "丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X2-X3-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X2-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞") (ℓ "丘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丘丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 62 q7 ∷
   rw⁻ 61 q8 ∷
   rw⁻ 60 q9 ∷
   rw 59 q10 ∷
   rw 58 q10 ∷
   rw 57 q11 ∷
   rw 56 q10 ∷
   rw 55 q11 ∷
   rw 54 q11 ∷
   re 53 1 (ℓ "乏乃乏") ∷
   rw⁻ 55 q12 ∷
   rw 54 q13 ∷
   rw⁻ 53 q12 ∷
   re 54 3 (ℓ "乓") ∷
   rw 52 q11 ∷
   rw 51 q11 ∷
   rw 50 q11 ∷
   rw 49 q11 ∷
   rw 48 q11 ∷
   rw 47 q11 ∷
   rw 46 q14 ∷
   rw 45 q10 ∷
   rw 44 q11 ∷
   rw 43 q11 ∷
   rw 42 q11 ∷
   rw 41 q14 ∷
   rw 40 q10 ∷
   rw 39 q14 ∷
   rw 38 q10 ∷
   re 37 1 (ℓ "乏乃乏") ∷
   rw⁻ 39 q12 ∷
   rw 38 q13 ∷
   rw⁻ 37 q12 ∷
   re 38 3 (ℓ "乓") ∷
   rw⁻ 36 q15 ∷
   rw⁻ 35 q15 ∷
   rw⁻ 34 q16 ∷
   rw⁻ 33 q15 ∷
   rw⁻ 32 q16 ∷
   rw⁻ 31 q16 ∷
   rw⁻ 30 q8 ∷
   rw⁻ 29 q9 ∷
   rw 30 q17 ∷
   rw 29 q8 ∷
   rw 30 q15 ∷
   rw 31 q16 ∷
   rw 32 q16 ∷
   rw 33 q18 ∷
   rw 34 q8 ∷
   rw 35 q8 ∷
   rw 36 q16 ∷
   rw 37 q16 ∷
   rw 38 q15 ∷
   rw 39 q16 ∷
   rw 40 q15 ∷
   rw 41 q15 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q12 ∷
   rw 43 q19 ∷
   rw 44 q12 ∷
   re 42 3 (ℓ "乐") ∷
   rw 43 q20 ∷
   rw 44 q21 ∷
   rw 45 q20 ∷
   rw 46 q21 ∷
   rw 47 q22 ∷
   rw 48 q22 ∷
   rw 49 q22 ∷
   rw 50 q20 ∷
   rw 51 q21 ∷
   rw 52 q22 ∷
   rw 53 q22 ∷
   rw 54 q22 ∷
   rw 55 q22 ∷
   rw 56 q22 ∷
   rw 57 q22 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q12 ∷
   rw 59 q19 ∷
   rw 60 q12 ∷
   re 58 3 (ℓ "乐") ∷
   rw 59 q22 ∷
   rw 60 q22 ∷
   rw 61 q20 ∷
   rw 62 q22 ∷
   rw 63 q20 ∷
   rw 64 q20 ∷
   rw 65 q8 ∷
   rw 66 q8 ∷
   rw 67 q15 ∷
   rw 68 q16 ∷
   rw 69 q16 ∷
   rw 70 q18 ∷
   rw 71 q8 ∷
   rw 72 q23 ∷
   rw 0 q24 ∷
   rw 43 q7 ∷
   rw⁻ 42 q8 ∷
   rw⁻ 41 q18 ∷
   rw⁻ 40 q16 ∷
   rw⁻ 39 q16 ∷
   rw⁻ 38 q15 ∷
   rw⁻ 37 q8 ∷
   rw⁻ 36 q8 ∷
   rw 35 q10 ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q10 ∷
   rw 31 q11 ∷
   rw 30 q11 ∷
   re 29 1 (ℓ "乏乃乏") ∷
   rw⁻ 31 q12 ∷
   rw 30 q13 ∷
   rw⁻ 29 q12 ∷
   re 30 3 (ℓ "乓") ∷
   rw 28 q11 ∷
   rw 27 q11 ∷
   rw 26 q11 ∷
   rw 25 q11 ∷
   rw 24 q11 ∷
   rw 23 q11 ∷
   rw 22 q14 ∷
   rw 21 q10 ∷
   rw 20 q11 ∷
   rw 19 q11 ∷
   rw 18 q11 ∷
   rw 17 q14 ∷
   rw 16 q10 ∷
   rw 15 q14 ∷
   rw 14 q10 ∷
   re 13 1 (ℓ "乏乃乏") ∷
   rw⁻ 15 q12 ∷
   rw 14 q13 ∷
   rw⁻ 13 q12 ∷
   re 14 3 (ℓ "乓") ∷
   rw⁻ 12 q15 ∷
   rw⁻ 11 q15 ∷
   rw⁻ 10 q16 ∷
   rw⁻ 9 q15 ∷
   rw⁻ 8 q16 ∷
   rw⁻ 7 q16 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 5 q8 ∷
   rw⁻ 4 q18 ∷
   rw⁻ 3 q16 ∷
   rw⁻ 2 q16 ∷
   rw⁻ 1 q15 ∷
   rw⁻ 0 q8 ∷
   rw 1 q25 ∷
   rw 0 q9 ∷
   rw 1 q8 ∷
   rw 2 q16 ∷
   rw 3 q16 ∷
   rw 4 q15 ∷
   rw 5 q16 ∷
   rw 6 q15 ∷
   rw 7 q15 ∷
   re 9 1 (ℓ "乏乆乏") ∷
   rw 8 q12 ∷
   rw 9 q19 ∷
   rw 10 q12 ∷
   re 8 3 (ℓ "乐") ∷
   rw 9 q20 ∷
   rw 10 q21 ∷
   rw 11 q20 ∷
   rw 12 q21 ∷
   rw 13 q22 ∷
   rw 14 q22 ∷
   rw 15 q22 ∷
   rw 16 q20 ∷
   rw 17 q21 ∷
   rw 18 q22 ∷
   rw 19 q22 ∷
   rw 20 q22 ∷
   rw 21 q22 ∷
   rw 22 q22 ∷
   rw 23 q22 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q12 ∷
   rw 25 q19 ∷
   rw 26 q12 ∷
   re 24 3 (ℓ "乐") ∷
   rw 25 q22 ∷
   rw 26 q22 ∷
   rw 27 q20 ∷
   rw 28 q22 ∷
   rw 29 q20 ∷
   rw 30 q20 ∷
   rw 31 q9 ∷
   rw 32 q8 ∷
   rw 33 q23 ∷ []) Eq.refl

private
  q26 : Eqn
  q26 = wE 1620 W
  q27 : Eqn
  q27 = sE 978 lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-2-1
  q28 : Eqn
  q28 = wE 1621 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF213 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF213-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乥丞") ⟫ʷ ≈ ⟪ (ℓ "丞乥丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF213-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乥丞") (ℓ "丞乥丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q26 ∷
   rw 0 q27 ∷
   rw 0 q28 ∷ []) Eq.refl

private
  q29 : Eqn
  q29 = wE 1622 W
  q30 : Eqn
  q30 = sE 977 lem-Bar⟨SSKSKK32-⟶0⟩-passes-II/IV-units-1-2
  q31 : Eqn
  q31 = wE 1623 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX32 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CK20 CS02 CK20 CK20] [X3 TOFF123 X3]: 3 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF123-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF123-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乢丞") (ℓ "丞乢丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 29 q29 ∷
   rw 0 q30 ∷
   rw 0 q31 ∷ []) Eq.refl

private
  q32 : Eqn
  q32 = sE 982 lem-LF-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CK21-CS12-CK31-CS12-CS12-CS12-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-S2-S2-S2-S2-CK21-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX02-CS01-CS01-CS01-S0-CK01-CS01-CS01-CS01-CS01-CS01-CS01-S3-CK31-at-2
  q33 : Eqn
  q33 = wE 225 W
  q34 : Eqn
  q34 = wE 871 W
  q35 : Eqn
  q35 = wE 872 W
  q36 : Eqn
  q36 = eqn (ℓ "丶丞") (ℓ "丞丶") (low₃-comm ((CS ↑)) (X))
  q37 : Eqn
  q37 = eqn (ℓ "乇丞") (ℓ "丞乇") (low₃-comm ((CK₁₀ ↑)) (X))
  q38 : Eqn
  q38 = eqn (ℓ "乃丞") (ℓ "丞乃") (low₃-comm ((Swap ↑ • CX₁₀ • Swap ↑)) (X))
  q39 : Eqn
  q39 = eqn (ℓ "两丞") (ℓ "丞两") (low-comm (CK₀₁) ((X ↑)))
  q40 : Eqn
  q40 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q41 : Eqn
  q41 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q42 : Eqn
  q42 = wE 390 W
  q43 : Eqn
  q43 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q44 : Eqn
  q44 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q45 : Eqn
  q45 = wE 217 W
  q46 : Eqn
  q46 = eqn (ℓ "丌乨") (ℓ "乨丌") (low₁-comm (X) (Toffᵗ))
  q47 : Eqn
  q47 = wE 1106 W
  q48 : Eqn
  q48 = wE 388 W
  q49 : Eqn
  q49 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))

-- kk pieces X1 X2 X3 CS01 CS01 CK01 CS01 CX02 CS12 CS12 CS12 CK21 S2 CS1 at 2: 69 steps
lem-kk-pieces-X1-X2-X3-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS1-at-2 : ⟪ (ℓ "丒丘丞丠丠两丠个丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乔丶丶丶且乇丶丶丶丶丶丶个丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶个丠丠丠丈两丠丠丠丠丠丠业乔丒丘丞") ⟫ʷ ≈ ⟪ (ℓ "丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘丘丞乧丘丞丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞丘丞乧丘丞丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞") ⟫ʷ
lem-kk-pieces-X1-X2-X3-CS01-CS01-CK01-CS01-CX02-CS12-CS12-CS12-CK21-S2-CS1-at-2 = derive (ℓ "丒丘丞丠丠两丠个丶丶丶乇且丶丶丶丶丶丶个丶丶乇丶乔丶丶丶且乇丶丶丶丶丶丶个丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶且且且且乇丶丶丶丶丶丶丶丶丶个丠丠丠丈两丠丠丠丠丠丠业乔丒丘丞") (ℓ "丒丘丶丶乇丶乇乇乃两丈两丈丠丠丠两丈丠丠丠丠丠丠乃丠丠两丠两两丒丘丘丞乧丘丞丒丘丞丶丶丶乇丶丶乌丽丽丽丽丽丽乔业丽丽丽丽丽丽丽丽丽乌丽丽丽乔丽丽丒丘丞丘丞乧丘丞丒丘丞丶丶乇丶乇乇乌乔业乔业丽丽丽乔业丽丽丽丽丽丽乌丽丽乔丽乔乔丒丘丞")
  (rw 3 q32 ∷
   rw 32 q33 ∷
   rw 33 q34 ∷
   rw 34 q35 ∷
   rw 39 q33 ∷
   rw 40 q34 ∷
   rw 41 q35 ∷
   rw 76 q33 ∷
   rw 77 q34 ∷
   rw 78 q35 ∷
   rw 83 q33 ∷
   rw 84 q34 ∷
   rw 85 q35 ∷
   rw⁻ 2 q36 ∷
   rw⁻ 3 q36 ∷
   rw⁻ 4 q37 ∷
   rw⁻ 5 q36 ∷
   rw⁻ 6 q37 ∷
   rw⁻ 7 q37 ∷
   rw⁻ 8 q38 ∷
   rw⁻ 9 q39 ∷
   rw⁻ 10 q40 ∷
   rw⁻ 11 q39 ∷
   rw⁻ 12 q40 ∷
   rw⁻ 13 q41 ∷
   rw⁻ 14 q41 ∷
   rw⁻ 15 q41 ∷
   rw⁻ 16 q39 ∷
   rw⁻ 17 q40 ∷
   rw⁻ 18 q41 ∷
   rw⁻ 19 q41 ∷
   rw⁻ 20 q41 ∷
   rw⁻ 21 q41 ∷
   rw⁻ 22 q41 ∷
   rw⁻ 23 q41 ∷
   rw⁻ 24 q38 ∷
   rw⁻ 25 q41 ∷
   rw⁻ 26 q41 ∷
   rw⁻ 27 q39 ∷
   rw⁻ 28 q41 ∷
   rw⁻ 29 q39 ∷
   rw⁻ 30 q39 ∷
   rw 31 q42 ∷
   rw⁻ 31 q43 ∷
   rw 33 q43 ∷
   rw 34 q44 ∷
   re 36 1 (ℓ "並乨並") ∷
   rw 35 q45 ∷
   rw 36 q46 ∷
   rw 37 q47 ∷
   re 35 3 (ℓ "乧") ∷
   rw 36 q44 ∷
   rw 37 q43 ∷
   rw 38 q48 ∷
   rw⁻ 36 q49 ∷
   rw⁻ 72 q49 ∷
   rw⁻ 73 q44 ∷
   rw⁻ 72 q43 ∷
   rw 75 q43 ∷
   rw 76 q44 ∷
   re 78 1 (ℓ "並乨並") ∷
   rw 77 q45 ∷
   rw 78 q46 ∷
   rw 79 q47 ∷
   re 77 3 (ℓ "乧") ∷
   rw 78 q44 ∷
   rw 79 q43 ∷
   rw 80 q48 ∷
   rw⁻ 78 q49 ∷ []) Eq.refl
