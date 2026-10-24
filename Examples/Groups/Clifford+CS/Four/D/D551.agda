{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD551 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D551 (W : Ws) (Sᴰ : SD551) where

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
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2 : St 931
  lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q3 : Eqn
  q3 = wE 121 W
  q4 : Eqn
  q4 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q5 : Eqn
  q5 = wE 30 W
  q6 : Eqn
  q6 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 27 W
  q9 : Eqn
  q9 = wE 122 W
  q10 : Eqn
  q10 = wE 31 W
  q11 : Eqn
  q11 = wE 127 W
  q12 : Eqn
  q12 = wE 118 W
  q13 : Eqn
  q13 = wE 7 W
  q14 : Eqn
  q14 = wE 74 W
  q15 : Eqn
  q15 = wE 125 W
  q16 : Eqn
  q16 = wE 1575 W
  q17 : Eqn
  q17 = wE 29 W
  q18 : Eqn
  q18 = wE 139 W
  q19 : Eqn
  q19 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q20 : Eqn
  q20 = eqn (ℓ "並丕") (ℓ "丕並") (low-comm (Swap) ((S • S • S)))
  q21 : Eqn
  q21 = sE 931 lem-Bar⟨SSKSKK31-⟶0⟩-passes-white-iX-via-V2-conjugates-2
  q22 : Eqn
  q22 = wE 76 W
  q23 : Eqn
  q23 = wE 137 W
  q24 : Eqn
  q24 = wE 1576 W
  q25 : Eqn
  q25 = wE 123 W
  q26 : Eqn
  q26 = wE 24 W
  q27 : Eqn
  q27 = wE 25 W
  q28 : Eqn
  q28 = wE 124 W

-- pass [CS03 CS03 CK30 CS03 CK30 CK30 CX31 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX31 CS01 CS01 CK10 CS01 CK10 CK10] [X3 TOFF023 X3]: 315 steps
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF023-X3 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞也丞") ⟫ʷ ≈ ⟪ (ℓ "丞也丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX31-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CK10-CS01-CK10-CK10-vs-X3-TOFF023-X3 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞也丞") (ℓ "丞也丞中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 32 q1 ∷
   rw⁻ 31 q2 ∷
   re 30 1 (ℓ "並乢並") ∷
   re 31 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 30 q3 ∷
   rw 31 q4 ∷
   rw 32 q5 ∷
   rw 33 q6 ∷
   rw 34 q5 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q7 ∷
   rw 36 q8 ∷
   rw 37 q7 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q3 ∷
   rw 37 q9 ∷
   rw 38 q10 ∷
   rw 37 q11 ∷
   rw 36 q12 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw⁻ 37 q7 ∷
   rw 36 q13 ∷
   rw⁻ 35 q7 ∷
   re 36 3 (ℓ "丽") ∷
   rw 34 q14 ∷
   rw⁻ 33 q6 ∷
   rw 32 q14 ∷
   rw⁻ 31 q4 ∷
   rw 30 q12 ∷
   rw 31 q15 ∷
   re 31 8 (ℓ "乢") ∷
   rw⁻ 29 q2 ∷
   rw 30 q16 ∷
   rw 29 q2 ∷
   rw 30 q6 ∷
   rw 31 q2 ∷
   rw 32 q17 ∷
   rw 33 q18 ∷
   rw 34 q17 ∷
   rw 35 q17 ∷
   rw 36 q2 ∷
   rw 37 q19 ∷
   rw 38 q2 ∷
   rw 39 q17 ∷
   rw 40 q17 ∷
   rw 41 q17 ∷
   rw 42 q17 ∷
   rw 43 q17 ∷
   rw 44 q17 ∷
   rw 45 q20 ∷
   rw 46 q18 ∷
   rw 47 q17 ∷
   rw 48 q17 ∷
   rw 49 q17 ∷
   rw 50 q2 ∷
   rw 51 q19 ∷
   rw 52 q2 ∷
   rw 53 q2 ∷
   re 55 1 (ℓ "乏丷乏") ∷
   rw 54 q7 ∷
   rw 55 q17 ∷
   rw 56 q7 ∷
   re 54 3 (ℓ "丮") ∷
   re 56 1 (ℓ "乏么乏") ∷
   rw 55 q7 ∷
   rw 56 q18 ∷
   rw 57 q7 ∷
   re 55 3 (ℓ "乒") ∷
   re 57 1 (ℓ "乏丷乏") ∷
   rw 56 q7 ∷
   rw 57 q17 ∷
   rw 58 q7 ∷
   re 56 3 (ℓ "丮") ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q7 ∷
   rw 58 q17 ∷
   rw 59 q7 ∷
   re 57 3 (ℓ "丮") ∷
   rw 58 q2 ∷
   rw 59 q2 ∷
   re 61 1 (ℓ "乏丶乏") ∷
   rw 60 q7 ∷
   rw 61 q8 ∷
   rw 62 q7 ∷
   re 60 3 (ℓ "中") ∷
   re 62 1 (ℓ "乏丶乏") ∷
   rw 61 q7 ∷
   rw 62 q8 ∷
   rw 63 q7 ∷
   re 61 3 (ℓ "中") ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q7 ∷
   rw 63 q8 ∷
   rw 64 q7 ∷
   re 62 3 (ℓ "中") ∷
   rw 63 q2 ∷
   rw 64 q17 ∷
   rw 65 q18 ∷
   rw 66 q17 ∷
   rw 67 q17 ∷
   rw 68 q2 ∷
   rw 69 q19 ∷
   rw 70 q2 ∷
   rw 71 q17 ∷
   rw 72 q17 ∷
   rw 73 q17 ∷
   rw 74 q17 ∷
   rw 75 q17 ∷
   rw 76 q17 ∷
   rw 77 q20 ∷
   rw 78 q18 ∷
   rw 79 q17 ∷
   rw 80 q17 ∷
   rw 81 q17 ∷
   rw 82 q2 ∷
   rw 83 q19 ∷
   rw 84 q2 ∷
   rw 85 q2 ∷
   re 87 1 (ℓ "乏丷乏") ∷
   rw 86 q7 ∷
   rw 87 q17 ∷
   rw 88 q7 ∷
   re 86 3 (ℓ "丮") ∷
   re 88 1 (ℓ "乏么乏") ∷
   rw 87 q7 ∷
   rw 88 q18 ∷
   rw 89 q7 ∷
   re 87 3 (ℓ "乒") ∷
   re 89 1 (ℓ "乏丷乏") ∷
   rw 88 q7 ∷
   rw 89 q17 ∷
   rw 90 q7 ∷
   re 88 3 (ℓ "丮") ∷
   re 90 1 (ℓ "乏丷乏") ∷
   rw 89 q7 ∷
   rw 90 q17 ∷
   rw 91 q7 ∷
   re 89 3 (ℓ "丮") ∷
   rw 90 q2 ∷
   rw 91 q2 ∷
   re 93 1 (ℓ "乏丷乏") ∷
   rw 92 q7 ∷
   rw 93 q17 ∷
   rw 94 q7 ∷
   re 92 3 (ℓ "丮") ∷
   re 94 1 (ℓ "乏丷乏") ∷
   rw 93 q7 ∷
   rw 94 q17 ∷
   rw 95 q7 ∷
   re 93 3 (ℓ "丮") ∷
   re 95 1 (ℓ "乏丷乏") ∷
   rw 94 q7 ∷
   rw 95 q17 ∷
   rw 96 q7 ∷
   re 94 3 (ℓ "丮") ∷
   rw 95 q2 ∷
   rw 96 q10 ∷
   rw 0 q21 ∷
   rw 67 q1 ∷
   rw⁻ 66 q2 ∷
   re 65 1 (ℓ "乏丨乏") ∷
   rw⁻ 67 q7 ∷
   rw 66 q22 ∷
   rw⁻ 65 q7 ∷
   re 66 3 (ℓ "举") ∷
   re 64 1 (ℓ "乏丨乏") ∷
   rw⁻ 66 q7 ∷
   rw 65 q22 ∷
   rw⁻ 64 q7 ∷
   re 65 3 (ℓ "举") ∷
   re 63 1 (ℓ "乏丨乏") ∷
   rw⁻ 65 q7 ∷
   rw 64 q22 ∷
   rw⁻ 63 q7 ∷
   re 64 3 (ℓ "举") ∷
   rw⁻ 62 q2 ∷
   rw⁻ 61 q2 ∷
   re 60 1 (ℓ "乏丨乏") ∷
   rw⁻ 62 q7 ∷
   rw 61 q22 ∷
   rw⁻ 60 q7 ∷
   re 61 3 (ℓ "举") ∷
   re 59 1 (ℓ "乏丨乏") ∷
   rw⁻ 61 q7 ∷
   rw 60 q22 ∷
   rw⁻ 59 q7 ∷
   re 60 3 (ℓ "举") ∷
   re 58 1 (ℓ "乏久乏") ∷
   rw⁻ 60 q7 ∷
   rw 59 q23 ∷
   rw⁻ 58 q7 ∷
   re 59 3 (ℓ "乕") ∷
   re 57 1 (ℓ "乏丨乏") ∷
   rw⁻ 59 q7 ∷
   rw 58 q22 ∷
   rw⁻ 57 q7 ∷
   re 58 3 (ℓ "举") ∷
   rw⁻ 56 q2 ∷
   rw⁻ 55 q2 ∷
   rw⁻ 54 q19 ∷
   rw⁻ 53 q2 ∷
   rw 52 q22 ∷
   rw 51 q22 ∷
   rw 50 q22 ∷
   rw 49 q23 ∷
   rw⁻ 48 q20 ∷
   rw 47 q22 ∷
   rw 46 q22 ∷
   rw 45 q22 ∷
   rw 44 q22 ∷
   rw 43 q22 ∷
   rw 42 q22 ∷
   rw⁻ 41 q2 ∷
   rw⁻ 40 q19 ∷
   rw⁻ 39 q2 ∷
   rw 38 q22 ∷
   rw 37 q22 ∷
   rw 36 q23 ∷
   rw 35 q22 ∷
   rw⁻ 34 q2 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw⁻ 35 q7 ∷
   rw 34 q13 ∷
   rw⁻ 33 q7 ∷
   re 34 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q7 ∷
   rw 33 q13 ∷
   rw⁻ 32 q7 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw⁻ 33 q7 ∷
   rw 32 q13 ∷
   rw⁻ 31 q7 ∷
   re 32 3 (ℓ "丽") ∷
   rw⁻ 30 q2 ∷
   rw⁻ 29 q2 ∷
   re 28 1 (ℓ "乏丨乏") ∷
   rw⁻ 30 q7 ∷
   rw 29 q22 ∷
   rw⁻ 28 q7 ∷
   re 29 3 (ℓ "举") ∷
   re 27 1 (ℓ "乏丨乏") ∷
   rw⁻ 29 q7 ∷
   rw 28 q22 ∷
   rw⁻ 27 q7 ∷
   re 28 3 (ℓ "举") ∷
   re 26 1 (ℓ "乏久乏") ∷
   rw⁻ 28 q7 ∷
   rw 27 q23 ∷
   rw⁻ 26 q7 ∷
   re 27 3 (ℓ "乕") ∷
   re 25 1 (ℓ "乏丨乏") ∷
   rw⁻ 27 q7 ∷
   rw 26 q22 ∷
   rw⁻ 25 q7 ∷
   re 26 3 (ℓ "举") ∷
   rw⁻ 24 q2 ∷
   rw⁻ 23 q2 ∷
   rw⁻ 22 q19 ∷
   rw⁻ 21 q2 ∷
   rw 20 q22 ∷
   rw 19 q22 ∷
   rw 18 q22 ∷
   rw 17 q23 ∷
   rw⁻ 16 q20 ∷
   rw 15 q22 ∷
   rw 14 q22 ∷
   rw 13 q22 ∷
   rw 12 q22 ∷
   rw 11 q22 ∷
   rw 10 q22 ∷
   rw⁻ 9 q2 ∷
   rw⁻ 8 q19 ∷
   rw⁻ 7 q2 ∷
   rw 6 q22 ∷
   rw 5 q22 ∷
   rw 4 q23 ∷
   rw 3 q22 ∷
   rw⁻ 2 q2 ∷
   rw⁻ 1 q6 ∷
   rw⁻ 0 q2 ∷
   rw 1 q24 ∷
   rw 0 q2 ∷
   re 2 1 (ℓ "丐义丹乊丹丽丐丁") ∷
   rw 1 q3 ∷
   rw 2 q4 ∷
   rw 3 q5 ∷
   rw 4 q6 ∷
   rw 5 q5 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q7 ∷
   rw 7 q8 ∷
   rw 8 q7 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q3 ∷
   rw 8 q9 ∷
   rw 1 q1 ∷
   rw 2 q25 ∷
   rw 3 q4 ∷
   rw 4 q26 ∷
   rw 5 q6 ∷
   rw 6 q26 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 7 q7 ∷
   rw 8 q27 ∷
   rw 9 q7 ∷
   re 7 3 (ℓ "丽") ∷
   rw 8 q25 ∷
   rw 9 q28 ∷
   rw 2 q15 ∷
   re 2 8 (ℓ "乢") ∷
   re 1 3 (ℓ "也") ∷
   rw 2 q2 ∷
   rw 3 q10 ∷ []) Eq.refl
