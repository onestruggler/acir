{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD574 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D574 (W : Ws) (Sᴰ : SD574) where

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
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1 : St 1004
  lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1 = pickᴰ 0 Sᴰ
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3 : St 1005
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3 = pickᴰ 1 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 196 W
  q9 : Eqn
  q9 = wE 1640 W
  q10 : Eqn
  q10 = wE 175 W
  q11 : Eqn
  q11 = sE 1005 lem-Bar⟨SSKSKK31-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3
  q12 : Eqn
  q12 = wE 1641 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X0 X3 TOFF103 X0 X3]: 135 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞乡丌丞") ⟫ʷ ≈ ⟪ (ℓ "丌丞乡丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X0-X3-TOFF103-X0-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丌丞乡丌丞") (ℓ "丌丞乡丌丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 34 q1 ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   re 31 1 (ℓ "乏习乏") ∷
   re 32 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 31 q4 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丽") ∷
   rw⁻ 33 q5 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "举") ∷
   rw⁻ 35 q5 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw⁻ 37 q4 ∷
   rw⁻ 38 q6 ∷
   rw 39 q7 ∷
   rw 38 q6 ∷
   rw 37 q4 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q7 ∷
   rw 35 q5 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 36 q7 ∷
   rw 33 q5 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 34 q7 ∷
   rw 31 q4 ∷
   rw 32 q8 ∷
   re 32 8 (ℓ "习") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乓") ∷
   rw 31 q10 ∷
   rw 32 q10 ∷
   re 34 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 33 q4 ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丽") ∷
   rw⁻ 35 q5 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "举") ∷
   rw⁻ 37 q5 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw⁻ 39 q4 ∷
   rw⁻ 40 q6 ∷
   rw 33 q1 ∷
   rw⁻ 34 q4 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw⁻ 36 q5 ∷
   re 38 1 (ℓ "乏丷乏") ∷
   rw 37 q7 ∷
   rw⁻ 38 q5 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 39 q7 ∷
   rw⁻ 40 q4 ∷
   rw⁻ 41 q6 ∷
   rw 34 q8 ∷
   re 34 8 (ℓ "习") ∷
   re 33 3 (ℓ "乡") ∷
   rw 34 q10 ∷
   rw 35 q7 ∷
   rw 0 q11 ∷
   rw 6 q1 ∷
   rw 5 q2 ∷
   re 4 1 (ℓ "乏习乏") ∷
   re 5 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 4 q4 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "丽") ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "举") ∷
   rw⁻ 8 q5 ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw⁻ 10 q4 ∷
   rw⁻ 11 q6 ∷
   rw 12 q7 ∷
   rw 11 q6 ∷
   rw 10 q4 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q7 ∷
   rw 8 q5 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 9 q7 ∷
   rw 6 q5 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 7 q7 ∷
   rw 4 q4 ∷
   rw 5 q8 ∷
   re 5 8 (ℓ "习") ∷
   rw 3 q2 ∷
   rw 2 q2 ∷
   re 1 1 (ℓ "乏乆乏") ∷
   rw 3 q7 ∷
   rw 0 q2 ∷
   rw 1 q12 ∷
   rw⁻ 0 q3 ∷
   rw 1 q10 ∷
   re 3 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 2 q4 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "丽") ∷
   rw⁻ 4 q5 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw⁻ 6 q5 ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw⁻ 8 q4 ∷
   rw⁻ 9 q6 ∷
   rw 2 q1 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q7 ∷
   rw⁻ 5 q5 ∷
   re 7 1 (ℓ "乏丷乏") ∷
   rw 6 q7 ∷
   rw⁻ 7 q5 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 8 q7 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q6 ∷
   rw 3 q8 ∷
   re 3 8 (ℓ "习") ∷
   re 2 3 (ℓ "乡") ∷
   rw⁻ 3 q3 ∷
   rw 4 q10 ∷
   rw 5 q7 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = wE 1610 W
  q14 : Eqn
  q14 = sE 1004 lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1
  q15 : Eqn
  q15 = wE 1611 W

-- pass [CK32 S3 CK32 S3 CS23 CS23 CS23 CK32 S3 CS23 CS23 CS23 CS23 CS23 CS23 CX30 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 S0 S0 S0 CK02 S0 S0 S0 S0 CK02 S0 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02] [X3 TOFF213 X3]: 3 steps
lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF213-X3 : ⟪ (ℓ "乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乥丞") ⟫ʷ ≈ ⟪ (ℓ "丞乥丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧") ⟫ʷ
lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF213-X3 = derive (ℓ "乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乥丞") (ℓ "丞乥丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧")
  (rw 74 q13 ∷
   rw 0 q14 ∷
   rw 0 q15 ∷ []) Eq.refl
