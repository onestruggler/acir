{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD656 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D656 (W : Ws) (Sᴰ : SD656) where

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
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CX31-X3 : St 1702
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CX31-X3 = pickᴰ 0 Sᴰ
  lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 : St 975
  lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 = pickᴰ 1 Sᴰ
  lem-pass-CSd23-CKd32-CS23-CS23-vs-X3-TOFF123-X3 : St 1703
  lem-pass-CSd23-CKd32-CS23-CS23-vs-X3-TOFF123-X3 = pickᴰ 2 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF023-X3 : St 1286
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF023-X3 = pickᴰ 3 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X3 : St 1704
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X3 = pickᴰ 4 Sᴰ
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3 : St 1655
  lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3 = pickᴰ 5 Sᴰ
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3 : St 1682
  lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3 = pickᴰ 6 Sᴰ
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF123-X3 : St 1705
  lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF123-X3 = pickᴰ 7 Sᴰ

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (ℓ "並丘") (ℓ "丘並") (low-comm (Swap) (X))
  q3 : Eqn
  q3 = wE 1106 W
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
  q11 = wE 1978 W
  q12 : Eqn
  q12 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q13 : Eqn
  q13 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q14 : Eqn
  q14 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q15 : Eqn
  q15 = wE 39 W
  q16 : Eqn
  q16 = wE 27 W
  q17 : Eqn
  q17 = wE 315 W
  q18 : Eqn
  q18 = wE 329 W
  q19 : Eqn
  q19 = wE 31 W
  q20 : Eqn
  q20 = sE 975 lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3
  q21 : Eqn
  q21 = sE 1705 lem-pass-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX30-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S0-S0-S0-CK02-S0-S0-S0-S0-CK02-S0-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-vs-X3-TOFF123-X3
  q22 : Eqn
  q22 = sE 1703 lem-pass-CSd23-CKd32-CS23-CS23-vs-X3-TOFF123-X3
  q23 : Eqn
  q23 = wE 1979 W
  q24 : Eqn
  q24 = wE 317 W

-- pass [X0 X2 CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02 X0 X2] [X3 TOFF123 X3]: 280 steps
lem-pass-X0-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-vs-X3-TOFF123-X3 : ⟪ (ℓ "丌丘义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞丌丘义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘") ⟫ʷ
lem-pass-X0-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-X0-X2-vs-X3-TOFF123-X3 = derive (ℓ "丌丘义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘丞乢丞") (ℓ "丞乢丞丌丘义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丌丘")
  (rw 33 q1 ∷
   rw⁻ 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q5 ∷
   re 24 1 (ℓ "乏乃乏") ∷
   rw⁻ 26 q6 ∷
   rw 25 q7 ∷
   rw⁻ 24 q6 ∷
   re 25 3 (ℓ "乓") ∷
   rw 23 q5 ∷
   rw 22 q5 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q8 ∷
   rw 16 q4 ∷
   rw 15 q5 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q8 ∷
   rw 11 q4 ∷
   rw 10 q8 ∷
   rw 9 q4 ∷
   re 8 1 (ℓ "乏乃乏") ∷
   rw⁻ 10 q6 ∷
   rw 9 q7 ∷
   rw⁻ 8 q6 ∷
   re 9 3 (ℓ "乓") ∷
   rw⁻ 7 q9 ∷
   rw⁻ 6 q9 ∷
   rw⁻ 5 q10 ∷
   rw⁻ 4 q9 ∷
   rw⁻ 3 q10 ∷
   rw⁻ 2 q10 ∷
   rw⁻ 1 q2 ∷
   rw 0 q3 ∷
   rw 1 q11 ∷
   rw 0 q9 ∷
   rw 1 q10 ∷
   rw 2 q10 ∷
   rw 3 q12 ∷
   rw 4 q13 ∷
   rw 5 q12 ∷
   rw 6 q10 ∷
   rw 7 q10 ∷
   rw 8 q9 ∷
   rw 9 q14 ∷
   rw 10 q9 ∷
   rw 11 q14 ∷
   rw 12 q10 ∷
   rw 13 q10 ∷
   rw 14 q10 ∷
   rw 15 q9 ∷
   rw 16 q14 ∷
   rw 17 q10 ∷
   rw 18 q10 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q6 ∷
   rw 24 q15 ∷
   rw 25 q6 ∷
   re 23 3 (ℓ "乐") ∷
   rw 24 q16 ∷
   rw 25 q16 ∷
   rw 26 q16 ∷
   rw 27 q16 ∷
   rw 28 q16 ∷
   rw 29 q16 ∷
   rw 30 q16 ∷
   rw 31 q16 ∷
   rw 32 q16 ∷
   rw 33 q16 ∷
   rw 34 q16 ∷
   rw 35 q16 ∷
   rw 36 q16 ∷
   rw 37 q16 ∷
   rw 38 q16 ∷
   rw 39 q16 ∷
   rw 40 q16 ∷
   rw 41 q16 ∷
   rw 42 q17 ∷
   rw 43 q17 ∷
   rw 44 q17 ∷
   rw 45 q18 ∷
   rw 46 q17 ∷
   rw 47 q16 ∷
   rw 48 q16 ∷
   rw 49 q16 ∷
   rw 50 q16 ∷
   rw 51 q16 ∷
   rw 52 q16 ∷
   rw 53 q16 ∷
   rw 54 q16 ∷
   rw 55 q16 ∷
   rw 56 q17 ∷
   rw 57 q17 ∷
   rw 58 q17 ∷
   rw 59 q18 ∷
   rw 60 q17 ∷
   rw 61 q17 ∷
   rw 62 q17 ∷
   rw 63 q17 ∷
   rw 64 q18 ∷
   rw 65 q17 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q6 ∷
   rw 67 q15 ∷
   rw 68 q6 ∷
   re 66 3 (ℓ "乐") ∷
   rw 67 q18 ∷
   rw 68 q17 ∷
   rw 69 q18 ∷
   rw 70 q17 ∷
   rw 71 q16 ∷
   rw 72 q16 ∷
   rw 73 q16 ∷
   rw 74 q18 ∷
   rw 75 q17 ∷
   rw 76 q16 ∷
   rw 77 q16 ∷
   rw 78 q16 ∷
   rw 79 q16 ∷
   rw 80 q16 ∷
   rw 81 q16 ∷
   rw 82 q9 ∷
   rw 83 q10 ∷
   rw 84 q10 ∷
   rw 85 q12 ∷
   rw 86 q19 ∷
   rw 82 q20 ∷
   rw 8 q21 ∷
   rw 4 q22 ∷
   rw 0 q20 ∷
   rw 89 q1 ∷
   rw⁻ 88 q12 ∷
   rw⁻ 87 q10 ∷
   rw⁻ 86 q10 ∷
   rw⁻ 85 q9 ∷
   rw 84 q5 ∷
   rw 83 q5 ∷
   rw 82 q5 ∷
   rw 81 q5 ∷
   rw 80 q5 ∷
   rw 79 q5 ∷
   rw 78 q8 ∷
   rw 77 q4 ∷
   rw 76 q5 ∷
   rw 75 q5 ∷
   rw 74 q5 ∷
   rw 73 q8 ∷
   rw 72 q4 ∷
   rw 71 q8 ∷
   rw 70 q4 ∷
   re 69 1 (ℓ "乏乃乏") ∷
   rw⁻ 71 q6 ∷
   rw 70 q7 ∷
   rw⁻ 69 q6 ∷
   re 70 3 (ℓ "乓") ∷
   rw 68 q8 ∷
   rw 67 q4 ∷
   rw 66 q8 ∷
   rw 65 q8 ∷
   rw 64 q8 ∷
   rw 63 q8 ∷
   rw 62 q4 ∷
   rw 61 q8 ∷
   rw 60 q8 ∷
   rw 59 q8 ∷
   rw 58 q5 ∷
   rw 57 q5 ∷
   rw 56 q5 ∷
   rw 55 q5 ∷
   rw 54 q5 ∷
   rw 53 q5 ∷
   rw 52 q5 ∷
   rw 51 q5 ∷
   rw 50 q5 ∷
   rw 49 q8 ∷
   rw 48 q4 ∷
   rw 47 q8 ∷
   rw 46 q8 ∷
   rw 45 q8 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw 41 q5 ∷
   rw 40 q5 ∷
   rw 39 q5 ∷
   rw 38 q5 ∷
   rw 37 q5 ∷
   rw 36 q5 ∷
   rw 35 q5 ∷
   rw 34 q5 ∷
   rw 33 q5 ∷
   rw 32 q5 ∷
   rw 31 q5 ∷
   rw 30 q5 ∷
   rw 29 q5 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   re 26 1 (ℓ "乏乃乏") ∷
   rw⁻ 28 q6 ∷
   rw 27 q7 ∷
   rw⁻ 26 q6 ∷
   re 27 3 (ℓ "乓") ∷
   rw⁻ 25 q10 ∷
   rw⁻ 24 q10 ∷
   rw⁻ 23 q10 ∷
   rw⁻ 22 q10 ∷
   rw⁻ 21 q10 ∷
   rw⁻ 20 q10 ∷
   rw⁻ 19 q14 ∷
   rw⁻ 18 q9 ∷
   rw⁻ 17 q10 ∷
   rw⁻ 16 q10 ∷
   rw⁻ 15 q10 ∷
   rw⁻ 14 q14 ∷
   rw⁻ 13 q9 ∷
   rw⁻ 12 q14 ∷
   rw⁻ 11 q9 ∷
   rw⁻ 10 q10 ∷
   rw⁻ 9 q10 ∷
   rw⁻ 8 q12 ∷
   rw⁻ 7 q13 ∷
   rw⁻ 6 q12 ∷
   rw⁻ 5 q10 ∷
   rw⁻ 4 q10 ∷
   rw⁻ 3 q9 ∷
   rw 4 q23 ∷
   rw 3 q24 ∷
   rw 4 q2 ∷
   rw 5 q10 ∷
   rw 6 q10 ∷
   rw 7 q9 ∷
   rw 8 q10 ∷
   rw 9 q9 ∷
   rw 10 q9 ∷
   re 12 1 (ℓ "乏乆乏") ∷
   rw 11 q6 ∷
   rw 12 q15 ∷
   rw 13 q6 ∷
   re 11 3 (ℓ "乐") ∷
   rw 12 q18 ∷
   rw 13 q17 ∷
   rw 14 q18 ∷
   rw 15 q17 ∷
   rw 16 q16 ∷
   rw 17 q16 ∷
   rw 18 q16 ∷
   rw 19 q18 ∷
   rw 20 q17 ∷
   rw 21 q16 ∷
   rw 22 q16 ∷
   rw 23 q16 ∷
   rw 24 q16 ∷
   rw 25 q16 ∷
   rw 26 q16 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q6 ∷
   rw 28 q15 ∷
   rw 29 q6 ∷
   re 27 3 (ℓ "乐") ∷
   rw 28 q16 ∷
   rw 29 q16 ∷
   rw 30 q18 ∷
   rw 31 q16 ∷
   rw 32 q18 ∷
   rw 33 q18 ∷
   rw 34 q24 ∷
   rw 35 q2 ∷
   rw 36 q19 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 1286 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF023-X3
  q26 : Eqn
  q26 = sE 1682 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-TOFF203-X3
  q27 : Eqn
  q27 = sE 1704 lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX31-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX31-CS01-CS01-CS01-CK10-CS01-CS01-vs-X3-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-S2-S2-S2-CK20-S2-S2-S2-S2-CK20-S2-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-X3

-- Bar(SSSKSS;3,1->0) passes Fredkin WBar(KiKiSSSKiSSSSSS;~3,0->2): 7 steps
lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~30-⟶2⟩ : ⟪ (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞也丞丞乤丞丞也丞丞乑业乑业中中中乑业中中中中中中乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧丧丧乄且丧丧丧丧丧丧丞丞也丞丞乤丞丞也丞") ⟫ʷ ≈ ⟪ (ℓ "丞也丞丞乤丞丞也丞丞乑业乑业中中中乑业中中中中中中乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧丧丧乄且丧丧丧丧丧丧丞丞也丞丞乤丞丞也丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠") ⟫ʷ
lem-Bar⟨SSSKSS31-⟶0⟩-passes-Fredkin-WBar⟨KiKiSSSKiSSSSSS~30-⟶2⟩ = derive (ℓ "中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠丞也丞丞乤丞丞也丞丞乑业乑业中中中乑业中中中中中中乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧丧丧乄且丧丧丧丧丧丧丞丞也丞丞乤丞丞也丞") (ℓ "丞也丞丞乤丞丞也丞丞乑业乑业中中中乑业中中中中中中乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧丧丧乄且丧丧丧丧丧丧丞丞也丞丞乤丞丞也丞中中中乑中中乓丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乓丠丠丠临丠丠")
  (rw 0 q25 ∷
   rw 3 q26 ∷
   rw 6 q25 ∷
   rw 9 q27 ∷
   rw 85 q25 ∷
   rw 88 q26 ∷
   rw 91 q25 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 1702 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-CX31-X3
  q29 : Eqn
  q29 = sE 1655 lem-pass-CS03-CS03-CK30-CS03-CK30-CK30-CX32-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CK20-CS02-CK20-CK20-vs-X3-TOFF103-X3

-- Bar(SSKSKK;3,2->0) passes factors of X0 X3 TOFF103 X0 X3: 2 steps
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3 : ⟪ (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乓丞丞乡丞") ⟫ʷ ≈ ⟪ (ℓ "丞乓丞丞乡丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄") ⟫ʷ
lem-Bar⟨SSKSKK32-⟶0⟩-passes-factors-of-X0-X3-TOFF103-X0-X3 = derive (ℓ "中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄丞乓丞丞乡丞") (ℓ "丞乓丞丞乡丞中中乑中乑乑乖乄且乄且丧丧丧乄且丧丧丧丧丧丧乖丧丧乄丧乄乄")
  (rw 0 q28 ∷
   rw 3 q29 ∷ []) Eq.refl
