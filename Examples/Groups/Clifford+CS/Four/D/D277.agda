{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D277 (W : Ws) where

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
  q1 = wE 3 W
  q2 : Eqn
  q2 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q3 : Eqn
  q3 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q4 : Eqn
  q4 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q5 : Eqn
  q5 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q6 : Eqn
  q6 = wE 1 W
  q7 : Eqn
  q7 = wE 113 W
  q8 : Eqn
  q8 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q9 : Eqn
  q9 = wE 114 W
  q10 : Eqn
  q10 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q11 : Eqn
  q11 = wE 173 W
  q12 : Eqn
  q12 = wE 779 W
  q13 : Eqn
  q13 = wE 175 W
  q14 : Eqn
  q14 = wE 858 W
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q18 : Eqn
  q18 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q19 : Eqn
  q19 = wE 7 W
  q20 : Eqn
  q20 = wE 481 W
  q21 : Eqn
  q21 = wE 772 W
  q22 : Eqn
  q22 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q23 : Eqn
  q23 = wE 6 W
  q24 : Eqn
  q24 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q25 : Eqn
  q25 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q26 : Eqn
  q26 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q27 : Eqn
  q27 = wE 861 W
  q28 : Eqn
  q28 = wE 39 W
  q29 : Eqn
  q29 = wE 27 W
  q30 : Eqn
  q30 = wE 315 W
  q31 : Eqn
  q31 = wE 329 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part9: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part9 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丞乏乏乓丼丠丼乏乏丞丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧並丶丶丶丶丶丶与与与为与与与与为与乓为与为与丶丶丶为与丶丶丶丶丶丶並丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part9 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丞乏乏乓丼丠丼乏乏丞丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧並丶丶丶丶丶丶与与与为与与与与为与乓为与为与丶丶丶为与丶丶丶丶丶丶並丞乊乊乊丞")
  (re 95 1 (ℓ "乏乆乏") ∷
   rw 94 q1 ∷
   re 95 5 (ℓ "中") ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw 97 q1 ∷
   re 93 3 (ℓ "乓") ∷
   rw 94 q2 ∷
   rw 91 q3 ∷
   rw 92 q4 ∷
   rw 93 q3 ∷
   rw 90 q5 ∷
   re 92 1 (ℓ "乏乆乏") ∷
   rw 91 q6 ∷
   re 92 3 (ℓ "丱") ∷
   re 92 1 (ℓ "乏丼两丼乏") ∷
   rw 98 q6 ∷
   re 96 3 (ℓ "乓") ∷
   rw 95 q7 ∷
   rw 94 q8 ∷
   rw 93 q9 ∷
   re 93 1 (ℓ "乏乆乏") ∷
   rw 92 q1 ∷
   re 93 5 (ℓ "丱") ∷
   re 93 1 (ℓ "乏丫乏") ∷
   rw 95 q1 ∷
   re 91 3 (ℓ "乓") ∷
   rw 92 q5 ∷
   rw 89 q3 ∷
   rw 90 q4 ∷
   rw 91 q3 ∷
   rw 88 q3 ∷
   rw 89 q4 ∷
   rw 90 q3 ∷
   rw 87 q3 ∷
   rw 88 q4 ∷
   rw 89 q3 ∷
   rw 86 q2 ∷
   re 88 1 (ℓ "乏乆乏") ∷
   rw 87 q6 ∷
   re 88 3 (ℓ "中") ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 94 q6 ∷
   re 92 3 (ℓ "乓") ∷
   rw 91 q7 ∷
   rw 90 q10 ∷
   rw 89 q9 ∷
   re 89 1 (ℓ "乏乆乏") ∷
   rw 88 q1 ∷
   re 89 5 (ℓ "中") ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 91 q1 ∷
   re 87 3 (ℓ "乓") ∷
   rw 88 q2 ∷
   rw 85 q2 ∷
   re 87 1 (ℓ "乏乆乏") ∷
   rw 86 q6 ∷
   re 87 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷
   rw 93 q6 ∷
   re 91 3 (ℓ "乓") ∷
   rw 90 q7 ∷
   rw 89 q10 ∷
   rw 88 q9 ∷
   re 88 1 (ℓ "乏乆乏") ∷
   rw 87 q1 ∷
   re 88 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q1 ∷
   re 86 3 (ℓ "乓") ∷
   rw 87 q2 ∷
   rw 84 q2 ∷
   re 86 1 (ℓ "乏乆乏") ∷
   rw 85 q6 ∷
   re 86 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 92 q6 ∷
   re 90 3 (ℓ "乓") ∷
   rw 89 q7 ∷
   rw 88 q10 ∷
   rw 87 q9 ∷
   re 87 1 (ℓ "乏乆乏") ∷
   rw 86 q1 ∷
   re 87 5 (ℓ "中") ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q1 ∷
   re 85 3 (ℓ "乓") ∷
   rw 86 q2 ∷
   rw 83 q2 ∷
   re 85 1 (ℓ "乏乆乏") ∷
   rw 84 q6 ∷
   re 85 3 (ℓ "中") ∷
   re 85 1 (ℓ "乏丼丠丼乏") ∷
   rw 91 q6 ∷
   re 89 3 (ℓ "乓") ∷
   rw 88 q7 ∷
   rw 87 q10 ∷
   rw 86 q9 ∷
   re 86 1 (ℓ "乏乆乏") ∷
   rw 85 q1 ∷
   re 86 5 (ℓ "中") ∷
   re 86 1 (ℓ "乏丧乏") ∷
   rw 88 q1 ∷
   re 84 3 (ℓ "乓") ∷
   rw 85 q2 ∷
   rw 82 q2 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q6 ∷
   re 84 3 (ℓ "中") ∷
   re 84 1 (ℓ "乏丼丠丼乏") ∷
   rw 90 q6 ∷
   re 88 3 (ℓ "乓") ∷
   rw 87 q7 ∷
   rw 86 q10 ∷
   rw 85 q9 ∷
   re 85 1 (ℓ "乏乆乏") ∷
   rw 84 q1 ∷
   re 85 5 (ℓ "中") ∷
   re 85 1 (ℓ "乏丧乏") ∷
   rw 87 q1 ∷
   re 83 3 (ℓ "乓") ∷
   rw 84 q2 ∷
   rw 81 q2 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q6 ∷
   re 83 3 (ℓ "中") ∷
   re 83 1 (ℓ "乏丼丠丼乏") ∷
   rw 89 q6 ∷
   re 87 3 (ℓ "乓") ∷
   rw 86 q7 ∷
   rw 85 q10 ∷
   rw 84 q9 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q1 ∷
   re 84 5 (ℓ "中") ∷
   re 84 1 (ℓ "乏丧乏") ∷
   rw 86 q1 ∷
   re 82 3 (ℓ "乓") ∷
   rw 83 q2 ∷
   rw 80 q2 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q6 ∷
   re 82 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q6 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q7 ∷
   rw 84 q10 ∷
   rw 83 q9 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q1 ∷
   re 83 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q1 ∷
   re 81 3 (ℓ "乓") ∷
   rw 82 q2 ∷
   rw 79 q2 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q6 ∷
   re 81 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q6 ∷
   re 85 3 (ℓ "乓") ∷
   rw 84 q7 ∷
   rw 83 q10 ∷
   rw 82 q9 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q1 ∷
   re 82 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q1 ∷
   re 80 3 (ℓ "乓") ∷
   rw 81 q2 ∷
   rw 78 q2 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q6 ∷
   re 80 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q6 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q7 ∷
   rw 82 q10 ∷
   rw 81 q9 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q1 ∷
   re 81 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q1 ∷
   re 79 3 (ℓ "乓") ∷
   rw 80 q2 ∷
   rw 77 q2 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q6 ∷
   re 79 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q6 ∷
   re 83 3 (ℓ "乓") ∷
   rw 82 q7 ∷
   rw 81 q10 ∷
   rw 80 q9 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q1 ∷
   re 80 5 (ℓ "中") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q1 ∷
   re 78 3 (ℓ "乓") ∷
   rw 79 q2 ∷
   rw 76 q2 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q6 ∷
   re 78 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q6 ∷
   re 82 3 (ℓ "乓") ∷
   rw 81 q7 ∷
   rw 80 q10 ∷
   rw 79 q9 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q1 ∷
   re 79 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q1 ∷
   re 77 3 (ℓ "乓") ∷
   rw 78 q2 ∷
   rw 75 q2 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q6 ∷
   re 77 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q6 ∷
   re 81 3 (ℓ "乓") ∷
   rw 80 q7 ∷
   rw 79 q10 ∷
   rw 78 q9 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q1 ∷
   re 78 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q1 ∷
   re 76 3 (ℓ "乓") ∷
   rw 77 q2 ∷
   rw 74 q2 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q6 ∷
   re 76 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q6 ∷
   re 80 3 (ℓ "乓") ∷
   rw 79 q7 ∷
   rw 78 q10 ∷
   rw 77 q9 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q1 ∷
   re 77 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q1 ∷
   re 75 3 (ℓ "乓") ∷
   rw 76 q2 ∷
   rw 73 q2 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q6 ∷
   re 75 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q6 ∷
   re 79 3 (ℓ "乓") ∷
   rw 78 q7 ∷
   rw 77 q10 ∷
   rw 76 q9 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q1 ∷
   re 76 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q1 ∷
   re 74 3 (ℓ "乓") ∷
   rw 75 q2 ∷
   rw 72 q2 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q6 ∷
   re 74 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q6 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q7 ∷
   rw 76 q10 ∷
   rw 75 q9 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q1 ∷
   re 75 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q1 ∷
   re 73 3 (ℓ "乓") ∷
   rw 74 q2 ∷
   rw 71 q2 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q6 ∷
   re 73 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q6 ∷
   re 77 3 (ℓ "乓") ∷
   rw 76 q7 ∷
   rw 75 q10 ∷
   rw 74 q9 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q1 ∷
   re 74 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q1 ∷
   re 72 3 (ℓ "乓") ∷
   rw 73 q2 ∷
   rw 70 q2 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q6 ∷
   re 72 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q6 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q7 ∷
   rw 74 q10 ∷
   rw 73 q9 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q1 ∷
   re 73 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q1 ∷
   re 71 3 (ℓ "乓") ∷
   rw 72 q2 ∷
   rw 69 q2 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q6 ∷
   re 71 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q6 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q7 ∷
   rw 73 q10 ∷
   rw 72 q9 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q1 ∷
   re 72 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q1 ∷
   re 70 3 (ℓ "乓") ∷
   rw 71 q2 ∷
   rw 72 q6 ∷
   rw 71 q11 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 72 q1 ∷
   rw 69 q11 ∷
   re 68 1 (ℓ "乏乃乏") ∷
   rw 70 q1 ∷
   rw 69 q12 ∷
   rw 68 q13 ∷
   rw 71 q6 ∷
   re 69 3 (ℓ "乓") ∷
   rw 70 q13 ∷
   rw 73 q6 ∷
   re 71 3 (ℓ "乐") ∷
   rw 72 q1 ∷
   rw 53 q14 ∷
   rw 136 q15 ∷
   rw⁻ 135 q16 ∷
   rw⁻ 134 q17 ∷
   rw⁻ 133 q17 ∷
   rw⁻ 132 q18 ∷
   rw⁻ 131 q17 ∷
   rw⁻ 130 q16 ∷
   rw 129 q19 ∷
   rw 128 q19 ∷
   rw 127 q19 ∷
   rw 126 q19 ∷
   rw 125 q19 ∷
   rw 124 q19 ∷
   rw 123 q20 ∷
   rw 122 q21 ∷
   rw 121 q19 ∷
   rw 120 q19 ∷
   rw 119 q19 ∷
   rw 118 q20 ∷
   rw 117 q21 ∷
   rw 116 q20 ∷
   rw 115 q21 ∷
   re 114 1 (ℓ "乏乃乏") ∷
   rw⁻ 116 q22 ∷
   rw 115 q23 ∷
   rw⁻ 114 q22 ∷
   re 115 3 (ℓ "乓") ∷
   rw 113 q20 ∷
   rw 112 q21 ∷
   rw 111 q20 ∷
   rw 110 q20 ∷
   rw 109 q20 ∷
   rw 108 q20 ∷
   rw 107 q21 ∷
   rw 106 q20 ∷
   rw 105 q20 ∷
   rw 104 q20 ∷
   rw 103 q19 ∷
   rw 102 q19 ∷
   rw 101 q19 ∷
   rw 100 q19 ∷
   rw 99 q19 ∷
   rw 98 q19 ∷
   rw 97 q19 ∷
   rw 96 q19 ∷
   rw 95 q19 ∷
   rw 94 q20 ∷
   rw 93 q21 ∷
   rw 92 q20 ∷
   rw 91 q20 ∷
   rw 90 q20 ∷
   rw 89 q19 ∷
   rw 88 q19 ∷
   rw 87 q19 ∷
   rw 86 q19 ∷
   rw 85 q19 ∷
   rw 84 q19 ∷
   rw 83 q19 ∷
   rw 82 q19 ∷
   rw 81 q19 ∷
   rw 80 q19 ∷
   rw 79 q19 ∷
   rw 78 q19 ∷
   rw 77 q19 ∷
   rw 76 q19 ∷
   rw 75 q19 ∷
   rw 74 q19 ∷
   rw 73 q19 ∷
   rw 72 q19 ∷
   re 71 1 (ℓ "乏乃乏") ∷
   rw⁻ 73 q22 ∷
   rw 72 q23 ∷
   rw⁻ 71 q22 ∷
   re 72 3 (ℓ "乓") ∷
   rw⁻ 70 q24 ∷
   rw⁻ 69 q24 ∷
   rw⁻ 68 q24 ∷
   rw⁻ 67 q24 ∷
   rw⁻ 66 q24 ∷
   rw⁻ 65 q24 ∷
   rw⁻ 64 q25 ∷
   rw⁻ 63 q26 ∷
   rw⁻ 62 q24 ∷
   rw⁻ 61 q24 ∷
   rw⁻ 60 q24 ∷
   rw⁻ 59 q25 ∷
   rw⁻ 58 q26 ∷
   rw⁻ 57 q25 ∷
   rw⁻ 56 q26 ∷
   rw 57 q27 ∷
   rw 56 q16 ∷
   rw 57 q17 ∷
   rw 58 q18 ∷
   rw 59 q17 ∷
   rw 60 q17 ∷
   rw 61 q16 ∷
   rw 62 q26 ∷
   rw 63 q25 ∷
   rw 64 q26 ∷
   rw 65 q25 ∷
   rw 66 q24 ∷
   rw 67 q24 ∷
   rw 68 q24 ∷
   rw 69 q26 ∷
   rw 70 q25 ∷
   rw 71 q24 ∷
   rw 72 q24 ∷
   rw 73 q24 ∷
   rw 74 q24 ∷
   rw 75 q24 ∷
   rw 76 q24 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q22 ∷
   rw 78 q28 ∷
   rw 79 q22 ∷
   re 77 3 (ℓ "乐") ∷
   rw 78 q29 ∷
   rw 79 q29 ∷
   rw 80 q29 ∷
   rw 81 q29 ∷
   rw 82 q29 ∷
   rw 83 q29 ∷
   rw 84 q29 ∷
   rw 85 q29 ∷
   rw 86 q29 ∷
   rw 87 q29 ∷
   rw 88 q29 ∷
   rw 89 q29 ∷
   rw 90 q29 ∷
   rw 91 q29 ∷
   rw 92 q29 ∷
   rw 93 q29 ∷
   rw 94 q29 ∷
   rw 95 q29 ∷
   rw 96 q30 ∷
   rw 97 q30 ∷
   rw 98 q30 ∷
   rw 99 q31 ∷
   rw 100 q30 ∷
   rw 101 q29 ∷
   rw 102 q29 ∷
   rw 103 q29 ∷ []) Eq.refl
