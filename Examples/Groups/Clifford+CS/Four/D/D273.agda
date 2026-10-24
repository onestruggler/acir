{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D273 (W : Ws) where

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
  q1 = wE 113 W
  q2 : Eqn
  q2 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q3 : Eqn
  q3 = wE 114 W
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 779 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = wE 858 W
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q14 : Eqn
  q14 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q15 : Eqn
  q15 = wE 7 W
  q16 : Eqn
  q16 = wE 481 W
  q17 : Eqn
  q17 = wE 772 W
  q18 : Eqn
  q18 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 6 W
  q20 : Eqn
  q20 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q21 : Eqn
  q21 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q23 : Eqn
  q23 = wE 861 W
  q24 : Eqn
  q24 = wE 39 W
  q25 : Eqn
  q25 = wE 27 W
  q26 : Eqn
  q26 = wE 315 W
  q27 : Eqn
  q27 = wE 329 W
  q28 : Eqn
  q28 = wE 31 W
  q29 : Eqn
  q29 = wE 862 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part5: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part5 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丞乏乏丼丠丼乏乆乏乏乏丞丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧並丶並丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part5 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丞乏乏丼丠丼乏乆乏乏乏丞丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧並丶並丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞")
  (re 50 3 (ℓ "乓") ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   rw 47 q3 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q4 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q4 ∷
   re 45 3 (ℓ "乓") ∷
   rw 46 q5 ∷
   rw 43 q5 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q6 ∷
   re 45 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q6 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q1 ∷
   rw 47 q2 ∷
   rw 46 q3 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q4 ∷
   re 46 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q4 ∷
   re 44 3 (ℓ "乓") ∷
   rw 45 q5 ∷
   rw 42 q5 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q6 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q6 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q1 ∷
   rw 46 q2 ∷
   rw 45 q3 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q4 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q4 ∷
   re 43 3 (ℓ "乓") ∷
   rw 44 q5 ∷
   rw 41 q5 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q6 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q6 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q1 ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q4 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q4 ∷
   re 42 3 (ℓ "乓") ∷
   rw 43 q5 ∷
   rw 40 q5 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q6 ∷
   re 42 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q6 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q1 ∷
   rw 44 q2 ∷
   rw 43 q3 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q4 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q4 ∷
   re 41 3 (ℓ "乓") ∷
   rw 42 q5 ∷
   rw 39 q5 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q6 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q6 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q1 ∷
   rw 43 q2 ∷
   rw 42 q3 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q4 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q4 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q5 ∷
   rw 38 q5 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q6 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q6 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q1 ∷
   rw 42 q2 ∷
   rw 41 q3 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q4 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q4 ∷
   re 39 3 (ℓ "乓") ∷
   rw 40 q5 ∷
   rw 37 q5 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q6 ∷
   re 39 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q6 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   rw 40 q3 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q4 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q4 ∷
   re 38 3 (ℓ "乓") ∷
   rw 39 q5 ∷
   rw 40 q6 ∷
   rw 39 q7 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 40 q4 ∷
   rw 37 q7 ∷
   re 36 1 (ℓ "乏乃乏") ∷
   rw 38 q4 ∷
   rw 37 q8 ∷
   rw 36 q9 ∷
   rw 39 q6 ∷
   re 37 3 (ℓ "乓") ∷
   rw 38 q9 ∷
   rw 41 q6 ∷
   re 39 3 (ℓ "乐") ∷
   rw 40 q4 ∷
   rw 21 q10 ∷
   rw 104 q11 ∷
   rw⁻ 103 q12 ∷
   rw⁻ 102 q13 ∷
   rw⁻ 101 q13 ∷
   rw⁻ 100 q14 ∷
   rw⁻ 99 q13 ∷
   rw⁻ 98 q12 ∷
   rw 97 q15 ∷
   rw 96 q15 ∷
   rw 95 q15 ∷
   rw 94 q15 ∷
   rw 93 q15 ∷
   rw 92 q15 ∷
   rw 91 q16 ∷
   rw 90 q17 ∷
   rw 89 q15 ∷
   rw 88 q15 ∷
   rw 87 q15 ∷
   rw 86 q16 ∷
   rw 85 q17 ∷
   rw 84 q16 ∷
   rw 83 q17 ∷
   re 82 1 (ℓ "乏乃乏") ∷
   rw⁻ 84 q18 ∷
   rw 83 q19 ∷
   rw⁻ 82 q18 ∷
   re 83 3 (ℓ "乓") ∷
   rw 81 q16 ∷
   rw 80 q17 ∷
   rw 79 q16 ∷
   rw 78 q16 ∷
   rw 77 q16 ∷
   rw 76 q16 ∷
   rw 75 q17 ∷
   rw 74 q16 ∷
   rw 73 q16 ∷
   rw 72 q16 ∷
   rw 71 q15 ∷
   rw 70 q15 ∷
   rw 69 q15 ∷
   rw 68 q15 ∷
   rw 67 q15 ∷
   rw 66 q15 ∷
   rw 65 q15 ∷
   rw 64 q15 ∷
   rw 63 q15 ∷
   rw 62 q16 ∷
   rw 61 q17 ∷
   rw 60 q16 ∷
   rw 59 q16 ∷
   rw 58 q16 ∷
   rw 57 q15 ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q15 ∷
   rw 51 q15 ∷
   rw 50 q15 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   rw 45 q15 ∷
   rw 44 q15 ∷
   rw 43 q15 ∷
   rw 42 q15 ∷
   rw 41 q15 ∷
   rw 40 q15 ∷
   re 39 1 (ℓ "乏乃乏") ∷
   rw⁻ 41 q18 ∷
   rw 40 q19 ∷
   rw⁻ 39 q18 ∷
   re 40 3 (ℓ "乓") ∷
   rw⁻ 38 q20 ∷
   rw⁻ 37 q20 ∷
   rw⁻ 36 q20 ∷
   rw⁻ 35 q20 ∷
   rw⁻ 34 q20 ∷
   rw⁻ 33 q20 ∷
   rw⁻ 32 q21 ∷
   rw⁻ 31 q22 ∷
   rw⁻ 30 q20 ∷
   rw⁻ 29 q20 ∷
   rw⁻ 28 q20 ∷
   rw⁻ 27 q21 ∷
   rw⁻ 26 q22 ∷
   rw⁻ 25 q21 ∷
   rw⁻ 24 q22 ∷
   rw 25 q23 ∷
   rw 24 q12 ∷
   rw 25 q13 ∷
   rw 26 q14 ∷
   rw 27 q13 ∷
   rw 28 q13 ∷
   rw 29 q12 ∷
   rw 30 q22 ∷
   rw 31 q21 ∷
   rw 32 q22 ∷
   rw 33 q21 ∷
   rw 34 q20 ∷
   rw 35 q20 ∷
   rw 36 q20 ∷
   rw 37 q22 ∷
   rw 38 q21 ∷
   rw 39 q20 ∷
   rw 40 q20 ∷
   rw 41 q20 ∷
   rw 42 q20 ∷
   rw 43 q20 ∷
   rw 44 q20 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q18 ∷
   rw 46 q24 ∷
   rw 47 q18 ∷
   re 45 3 (ℓ "乐") ∷
   rw 46 q25 ∷
   rw 47 q25 ∷
   rw 48 q25 ∷
   rw 49 q25 ∷
   rw 50 q25 ∷
   rw 51 q25 ∷
   rw 52 q25 ∷
   rw 53 q25 ∷
   rw 54 q25 ∷
   rw 55 q25 ∷
   rw 56 q25 ∷
   rw 57 q25 ∷
   rw 58 q25 ∷
   rw 59 q25 ∷
   rw 60 q25 ∷
   rw 61 q25 ∷
   rw 62 q25 ∷
   rw 63 q25 ∷
   rw 64 q26 ∷
   rw 65 q26 ∷
   rw 66 q26 ∷
   rw 67 q27 ∷
   rw 68 q26 ∷
   rw 69 q25 ∷
   rw 70 q25 ∷
   rw 71 q25 ∷
   rw 72 q25 ∷
   rw 73 q25 ∷
   rw 74 q25 ∷
   rw 75 q25 ∷
   rw 76 q25 ∷
   rw 77 q25 ∷
   rw 78 q26 ∷
   rw 79 q26 ∷
   rw 80 q26 ∷
   rw 81 q27 ∷
   rw 82 q26 ∷
   rw 83 q26 ∷
   rw 84 q26 ∷
   rw 85 q26 ∷
   rw 86 q27 ∷
   rw 87 q26 ∷
   re 89 1 (ℓ "乏乆乏") ∷
   rw 88 q18 ∷
   rw 89 q24 ∷
   rw 90 q18 ∷
   re 88 3 (ℓ "乐") ∷
   rw 89 q27 ∷
   rw 90 q26 ∷
   rw 91 q27 ∷
   rw 92 q26 ∷
   rw 93 q25 ∷
   rw 94 q25 ∷
   rw 95 q25 ∷
   rw 96 q27 ∷
   rw 97 q26 ∷
   rw 98 q25 ∷
   rw 99 q25 ∷
   rw 100 q25 ∷
   rw 101 q25 ∷
   rw 102 q25 ∷
   rw 103 q25 ∷
   rw 104 q28 ∷
   rw 109 q11 ∷
   rw⁻ 108 q12 ∷
   rw⁻ 107 q20 ∷
   rw⁻ 106 q20 ∷
   rw⁻ 105 q20 ∷
   rw⁻ 104 q12 ∷
   rw 103 q15 ∷
   rw 102 q15 ∷
   rw 101 q15 ∷
   rw 100 q15 ∷
   rw 99 q15 ∷
   rw 98 q15 ∷
   rw 97 q16 ∷
   rw 96 q17 ∷
   rw 95 q15 ∷
   rw 94 q15 ∷
   rw 93 q15 ∷
   rw 92 q16 ∷
   rw 91 q17 ∷
   rw 90 q16 ∷
   rw 89 q17 ∷
   re 88 1 (ℓ "乏乃乏") ∷
   rw⁻ 90 q18 ∷
   rw 89 q19 ∷
   rw⁻ 88 q18 ∷
   re 89 3 (ℓ "乓") ∷
   rw 87 q16 ∷
   rw 86 q17 ∷
   rw 85 q16 ∷
   rw 84 q16 ∷
   rw 83 q16 ∷
   rw 82 q16 ∷
   rw 81 q17 ∷
   rw 80 q16 ∷
   rw 79 q16 ∷
   rw 78 q16 ∷
   rw 77 q15 ∷
   rw 76 q15 ∷
   rw 75 q15 ∷
   rw 74 q15 ∷
   rw 73 q15 ∷
   rw 72 q15 ∷
   rw 71 q15 ∷
   rw 70 q15 ∷
   rw 69 q15 ∷
   rw 68 q16 ∷
   rw 67 q17 ∷
   rw 66 q16 ∷
   rw 65 q16 ∷
   rw 64 q16 ∷
   rw 63 q15 ∷
   rw 62 q15 ∷
   rw 61 q15 ∷
   rw 60 q15 ∷
   rw 59 q15 ∷
   rw 58 q15 ∷
   rw 57 q15 ∷
   rw 56 q15 ∷
   rw 55 q15 ∷
   rw 54 q15 ∷
   rw 53 q15 ∷
   rw 52 q15 ∷
   rw 51 q15 ∷
   rw 50 q15 ∷
   rw 49 q15 ∷
   rw 48 q15 ∷
   rw 47 q15 ∷
   rw 46 q15 ∷
   re 45 1 (ℓ "乏乃乏") ∷
   rw⁻ 47 q18 ∷
   rw 46 q19 ∷
   rw⁻ 45 q18 ∷
   re 46 3 (ℓ "乓") ∷
   rw⁻ 44 q20 ∷
   rw⁻ 43 q20 ∷
   rw⁻ 42 q20 ∷
   rw⁻ 41 q20 ∷
   rw⁻ 40 q20 ∷
   rw⁻ 39 q20 ∷
   rw⁻ 38 q21 ∷
   rw⁻ 37 q22 ∷
   rw⁻ 36 q20 ∷
   rw⁻ 35 q20 ∷
   rw⁻ 34 q20 ∷
   rw⁻ 33 q21 ∷
   rw⁻ 32 q22 ∷
   rw⁻ 31 q21 ∷
   rw⁻ 30 q22 ∷
   rw 31 q29 ∷
   rw 30 q12 ∷
   rw 31 q20 ∷
   rw 32 q20 ∷
   rw 33 q20 ∷
   rw 34 q12 ∷
   rw 35 q22 ∷
   rw 36 q21 ∷
   rw 37 q22 ∷
   rw 38 q21 ∷
   rw 39 q20 ∷
   rw 40 q20 ∷
   rw 41 q20 ∷
   rw 42 q22 ∷
   rw 43 q21 ∷
   rw 44 q20 ∷
   rw 45 q20 ∷
   rw 46 q20 ∷
   rw 47 q20 ∷
   rw 48 q20 ∷
   rw 49 q20 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q18 ∷
   rw 51 q24 ∷
   rw 52 q18 ∷
   re 50 3 (ℓ "乐") ∷
   rw 51 q25 ∷
   rw 52 q25 ∷
   rw 53 q25 ∷
   rw 54 q25 ∷
   rw 55 q25 ∷
   rw 56 q25 ∷
   rw 57 q25 ∷
   rw 58 q25 ∷
   rw 59 q25 ∷
   rw 60 q25 ∷
   rw 61 q25 ∷
   rw 62 q25 ∷
   rw 63 q25 ∷
   rw 64 q25 ∷
   rw 65 q25 ∷
   rw 66 q25 ∷
   rw 67 q25 ∷
   rw 68 q25 ∷
   rw 69 q26 ∷
   rw 70 q26 ∷
   rw 71 q26 ∷
   rw 72 q27 ∷
   rw 73 q26 ∷
   rw 74 q25 ∷
   rw 75 q25 ∷
   rw 76 q25 ∷
   rw 77 q25 ∷
   rw 78 q25 ∷
   rw 79 q25 ∷
   rw 80 q25 ∷
   rw 81 q25 ∷
   rw 82 q25 ∷
   rw 83 q26 ∷
   rw 84 q26 ∷
   rw 85 q26 ∷
   rw 86 q27 ∷
   rw 87 q26 ∷
   rw 88 q26 ∷
   rw 89 q26 ∷
   rw 90 q26 ∷
   rw 91 q27 ∷
   rw 92 q26 ∷
   re 94 1 (ℓ "乏乆乏") ∷
   rw 93 q18 ∷
   rw 94 q24 ∷
   rw 95 q18 ∷
   re 93 3 (ℓ "乐") ∷
   rw 94 q27 ∷
   rw 95 q26 ∷
   rw 96 q27 ∷
   rw 97 q26 ∷
   rw 98 q25 ∷
   rw 99 q25 ∷
   rw 100 q25 ∷
   rw 101 q27 ∷
   rw 102 q26 ∷
   rw 103 q25 ∷
   rw 104 q25 ∷
   rw 105 q25 ∷
   rw 106 q25 ∷
   rw 107 q25 ∷ []) Eq.refl
