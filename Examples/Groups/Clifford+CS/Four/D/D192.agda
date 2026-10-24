{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D192 (W : Ws) where

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
  q1 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q2 : Eqn
  q2 = wE 785 W
  q3 : Eqn
  q3 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q5 : Eqn
  q5 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q6 : Eqn
  q6 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q7 : Eqn
  q7 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q8 : Eqn
  q8 = wE 39 W
  q9 : Eqn
  q9 = wE 329 W
  q10 : Eqn
  q10 = wE 315 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 5 W
  q14 : Eqn
  q14 = wE 772 W
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 6 W
  q17 : Eqn
  q17 = wE 481 W
  q18 : Eqn
  q18 = wE 787 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->2) passes white iX via V2 conjugates 1 part5: 134 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part5 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞义义並乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞乊乘乊乊丞並丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part5 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞义义並乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞乊乘乊乊丞並丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫")
  (rw⁻ 57 q1 ∷
   rw⁻ 56 q1 ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 57 q4 ∷
   rw 58 q5 ∷
   rw 59 q4 ∷
   rw 60 q4 ∷
   rw 61 q3 ∷
   rw 62 q1 ∷
   rw 63 q1 ∷
   rw 64 q6 ∷
   rw 65 q1 ∷
   rw 66 q6 ∷
   rw 67 q6 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q7 ∷
   rw 69 q8 ∷
   rw 70 q7 ∷
   re 68 3 (ℓ "乐") ∷
   rw 69 q9 ∷
   rw 70 q10 ∷
   rw 71 q9 ∷
   rw 72 q10 ∷
   rw 73 q11 ∷
   rw 74 q11 ∷
   rw 75 q11 ∷
   rw 76 q9 ∷
   rw 77 q10 ∷
   rw 78 q11 ∷
   rw 79 q11 ∷
   rw 80 q11 ∷
   rw 81 q11 ∷
   rw 82 q11 ∷
   rw 83 q11 ∷
   re 85 1 (ℓ "乏乆乏") ∷
   rw 84 q7 ∷
   rw 85 q8 ∷
   rw 86 q7 ∷
   re 84 3 (ℓ "乐") ∷
   rw 85 q11 ∷
   rw 86 q11 ∷
   rw 87 q9 ∷
   rw 88 q11 ∷
   rw 89 q9 ∷
   rw 90 q9 ∷
   rw 91 q12 ∷
   rw 96 q13 ∷
   rw⁻ 95 q3 ∷
   rw⁻ 94 q4 ∷
   rw⁻ 93 q4 ∷
   rw⁻ 92 q4 ∷
   rw⁻ 91 q3 ∷
   rw 90 q14 ∷
   rw 89 q14 ∷
   rw 88 q15 ∷
   rw 87 q14 ∷
   rw 86 q15 ∷
   rw 85 q15 ∷
   re 84 1 (ℓ "乏乃乏") ∷
   rw⁻ 86 q7 ∷
   rw 85 q16 ∷
   rw⁻ 84 q7 ∷
   re 85 3 (ℓ "乓") ∷
   rw 83 q15 ∷
   rw 82 q15 ∷
   rw 81 q15 ∷
   rw 80 q15 ∷
   rw 79 q15 ∷
   rw 78 q15 ∷
   rw 77 q17 ∷
   rw 76 q14 ∷
   rw 75 q15 ∷
   rw 74 q15 ∷
   rw 73 q15 ∷
   rw 72 q17 ∷
   rw 71 q14 ∷
   rw 70 q17 ∷
   rw 69 q14 ∷
   re 68 1 (ℓ "乏乃乏") ∷
   rw⁻ 70 q7 ∷
   rw 69 q16 ∷
   rw⁻ 68 q7 ∷
   re 69 3 (ℓ "乓") ∷
   rw⁻ 67 q6 ∷
   rw⁻ 66 q6 ∷
   rw⁻ 65 q1 ∷
   rw⁻ 64 q6 ∷
   rw⁻ 63 q1 ∷
   rw⁻ 62 q1 ∷
   rw 63 q18 ∷
   rw 62 q3 ∷
   rw 63 q4 ∷
   rw 64 q4 ∷
   rw 65 q4 ∷
   rw 66 q3 ∷
   rw 67 q1 ∷
   rw 68 q1 ∷
   rw 69 q6 ∷
   rw 70 q1 ∷
   rw 71 q6 ∷
   rw 72 q6 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q7 ∷
   rw 74 q8 ∷
   rw 75 q7 ∷
   re 73 3 (ℓ "乐") ∷
   rw 74 q9 ∷
   rw 75 q10 ∷
   rw 76 q9 ∷
   rw 77 q10 ∷
   rw 78 q11 ∷
   rw 79 q11 ∷
   rw 80 q11 ∷
   rw 81 q9 ∷
   rw 82 q10 ∷
   rw 83 q11 ∷
   rw 84 q11 ∷
   rw 85 q11 ∷
   rw 86 q11 ∷
   rw 87 q11 ∷
   rw 88 q11 ∷
   re 90 1 (ℓ "乏乆乏") ∷
   rw 89 q7 ∷
   rw 90 q8 ∷
   rw 91 q7 ∷
   re 89 3 (ℓ "乐") ∷
   rw 90 q11 ∷
   rw 91 q11 ∷
   rw 92 q9 ∷
   rw 93 q11 ∷
   rw 94 q9 ∷
   rw 95 q9 ∷
   rw 96 q12 ∷ []) Eq.refl

private
  q19 : Eqn
  q19 = wE 788 W

-- pass [CS23 CS23 CK32 CS23 CK32 CK32 CX30 CK02 S0 CK02 S0 CS02 CS02 CS02 CK02 S0 CS02 CS02 CS02 CS02 CS02 CS02 CX30 CS02 CS02 CK02 CS02 CK02 CK02] [X3 CKd32 X3]: 83 steps
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CKd32-X3 : ⟪ (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫") ⟫ʷ
lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX30-CK02-S0-CK02-S0-CS02-CS02-CS02-CK02-S0-CS02-CS02-CS02-CS02-CS02-CS02-CX30-CS02-CS02-CK02-CS02-CK02-CK02-vs-X3-CKd32-X3 = derive (ℓ "义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫丞乘丞") (ℓ "丞乘丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丫丫")
  (rw 32 q13 ∷
   rw⁻ 31 q3 ∷
   rw⁻ 30 q5 ∷
   rw⁻ 29 q3 ∷
   rw 28 q14 ∷
   rw 27 q14 ∷
   rw 26 q15 ∷
   rw 25 q14 ∷
   rw 24 q15 ∷
   rw 23 q15 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw⁻ 24 q7 ∷
   rw 23 q16 ∷
   rw⁻ 22 q7 ∷
   re 23 3 (ℓ "乓") ∷
   rw 21 q15 ∷
   rw 20 q15 ∷
   rw 19 q15 ∷
   rw 18 q15 ∷
   rw 17 q15 ∷
   rw 16 q15 ∷
   rw 15 q17 ∷
   rw 14 q14 ∷
   rw 13 q15 ∷
   rw 12 q15 ∷
   rw 11 q15 ∷
   rw 10 q17 ∷
   rw 9 q14 ∷
   rw 8 q17 ∷
   rw 7 q14 ∷
   re 6 1 (ℓ "乏乃乏") ∷
   rw⁻ 8 q7 ∷
   rw 7 q16 ∷
   rw⁻ 6 q7 ∷
   re 7 3 (ℓ "乓") ∷
   rw⁻ 5 q6 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 3 q1 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 1 q1 ∷
   rw⁻ 0 q1 ∷
   rw 1 q19 ∷
   rw 0 q3 ∷
   rw 1 q5 ∷
   rw 2 q3 ∷
   rw 3 q1 ∷
   rw 4 q1 ∷
   rw 5 q6 ∷
   rw 6 q1 ∷
   rw 7 q6 ∷
   rw 8 q6 ∷
   re 10 1 (ℓ "乏乆乏") ∷
   rw 9 q7 ∷
   rw 10 q8 ∷
   rw 11 q7 ∷
   re 9 3 (ℓ "乐") ∷
   rw 10 q9 ∷
   rw 11 q10 ∷
   rw 12 q9 ∷
   rw 13 q10 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   rw 16 q11 ∷
   rw 17 q9 ∷
   rw 18 q10 ∷
   rw 19 q11 ∷
   rw 20 q11 ∷
   rw 21 q11 ∷
   rw 22 q11 ∷
   rw 23 q11 ∷
   rw 24 q11 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q7 ∷
   rw 26 q8 ∷
   rw 27 q7 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q11 ∷
   rw 27 q11 ∷
   rw 28 q9 ∷
   rw 29 q11 ∷
   rw 30 q9 ∷
   rw 31 q9 ∷
   rw 32 q12 ∷ []) Eq.refl
