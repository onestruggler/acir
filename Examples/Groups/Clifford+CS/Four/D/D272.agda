{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D272 (W : Ws) where

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
  q2 = wE 113 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q4 : Eqn
  q4 = wE 114 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q7 : Eqn
  q7 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q8 : Eqn
  q8 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q9 : Eqn
  q9 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q10 : Eqn
  q10 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q11 : Eqn
  q11 = wE 173 W
  q12 : Eqn
  q12 = wE 779 W
  q13 : Eqn
  q13 = wE 175 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丞乏乏丼丠丼乏乆乏丞丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丞乏乏丼丠丼乏乆乏乏乏丞丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丞乏乏丼丠丼乏乆乏丞丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丞乏乏丼丠丼乏乆乏乏乏丞丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞")
  (rw 93 q1 ∷
   re 91 3 (ℓ "乓") ∷
   rw 90 q2 ∷
   rw 89 q3 ∷
   rw 88 q4 ∷
   re 88 1 (ℓ "乏乆乏") ∷
   rw 87 q5 ∷
   re 88 5 (ℓ "中") ∷
   re 88 1 (ℓ "乏丧乏") ∷
   rw 90 q5 ∷
   re 86 3 (ℓ "乓") ∷
   rw 87 q6 ∷
   rw 84 q6 ∷
   re 86 1 (ℓ "乏乆乏") ∷
   rw 85 q1 ∷
   re 86 3 (ℓ "中") ∷
   re 86 1 (ℓ "乏丼丠丼乏") ∷
   rw 92 q1 ∷
   re 90 3 (ℓ "乓") ∷
   rw 89 q2 ∷
   rw 88 q3 ∷
   rw 87 q4 ∷
   re 87 1 (ℓ "乏乆乏") ∷
   rw 86 q5 ∷
   re 87 5 (ℓ "中") ∷
   re 87 1 (ℓ "乏丧乏") ∷
   rw 89 q5 ∷
   re 85 3 (ℓ "乓") ∷
   rw 86 q6 ∷
   rw 83 q7 ∷
   rw 84 q8 ∷
   rw 85 q7 ∷
   rw 82 q9 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q1 ∷
   re 84 3 (ℓ "丱") ∷
   re 84 1 (ℓ "乏丼两丼乏") ∷
   rw 90 q1 ∷
   re 88 3 (ℓ "乓") ∷
   rw 87 q2 ∷
   rw 86 q10 ∷
   rw 85 q4 ∷
   re 85 1 (ℓ "乏乆乏") ∷
   rw 84 q5 ∷
   re 85 5 (ℓ "丱") ∷
   re 85 1 (ℓ "乏丫乏") ∷
   rw 87 q5 ∷
   re 83 3 (ℓ "乓") ∷
   rw 84 q9 ∷
   rw 81 q7 ∷
   rw 82 q8 ∷
   rw 83 q7 ∷
   rw 80 q9 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q1 ∷
   re 82 3 (ℓ "丱") ∷
   re 82 1 (ℓ "乏丼两丼乏") ∷
   rw 88 q1 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q2 ∷
   rw 84 q10 ∷
   rw 83 q4 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q5 ∷
   re 83 5 (ℓ "丱") ∷
   re 83 1 (ℓ "乏丫乏") ∷
   rw 85 q5 ∷
   re 81 3 (ℓ "乓") ∷
   rw 82 q9 ∷
   rw 83 q1 ∷
   rw 82 q11 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 83 q5 ∷
   rw 80 q11 ∷
   re 79 1 (ℓ "乏乃乏") ∷
   rw 81 q5 ∷
   rw 80 q12 ∷
   rw 79 q13 ∷
   rw 82 q1 ∷
   re 80 3 (ℓ "乓") ∷
   rw 81 q13 ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "乐") ∷
   rw 83 q5 ∷
   rw 78 q7 ∷
   rw 79 q8 ∷
   rw 80 q7 ∷
   rw 77 q9 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q1 ∷
   re 79 3 (ℓ "丱") ∷
   re 79 1 (ℓ "乏丼两丼乏") ∷
   rw 85 q1 ∷
   re 83 3 (ℓ "乓") ∷
   rw 82 q2 ∷
   rw 81 q10 ∷
   rw 80 q4 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q5 ∷
   re 80 5 (ℓ "丱") ∷
   re 80 1 (ℓ "乏丫乏") ∷
   rw 82 q5 ∷
   re 78 3 (ℓ "乓") ∷
   rw 79 q9 ∷
   rw 76 q7 ∷
   rw 77 q8 ∷
   rw 78 q7 ∷
   rw 75 q7 ∷
   rw 76 q8 ∷
   rw 77 q7 ∷
   rw 74 q7 ∷
   rw 75 q8 ∷
   rw 76 q7 ∷
   rw 73 q7 ∷
   rw 74 q8 ∷
   rw 75 q7 ∷
   rw 72 q9 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q1 ∷
   re 74 3 (ℓ "丱") ∷
   re 74 1 (ℓ "乏丼两丼乏") ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q2 ∷
   rw 76 q10 ∷
   rw 75 q4 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q5 ∷
   re 75 5 (ℓ "丱") ∷
   re 75 1 (ℓ "乏丫乏") ∷
   rw 77 q5 ∷
   re 73 3 (ℓ "乓") ∷
   rw 74 q9 ∷
   rw 71 q7 ∷
   rw 72 q8 ∷
   rw 73 q7 ∷
   rw 70 q7 ∷
   rw 71 q8 ∷
   rw 72 q7 ∷
   rw 69 q7 ∷
   rw 70 q8 ∷
   rw 71 q7 ∷
   rw 68 q6 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q1 ∷
   re 70 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏丼丠丼乏") ∷
   rw 76 q1 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q2 ∷
   rw 72 q3 ∷
   rw 71 q4 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q5 ∷
   re 71 5 (ℓ "中") ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q5 ∷
   re 69 3 (ℓ "乓") ∷
   rw 70 q6 ∷
   rw 67 q6 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q1 ∷
   re 69 3 (ℓ "中") ∷
   re 69 1 (ℓ "乏丼丠丼乏") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "乓") ∷
   rw 72 q2 ∷
   rw 71 q3 ∷
   rw 70 q4 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q5 ∷
   re 70 5 (ℓ "中") ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q5 ∷
   re 68 3 (ℓ "乓") ∷
   rw 69 q6 ∷
   rw 66 q6 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q1 ∷
   re 68 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q2 ∷
   rw 70 q3 ∷
   rw 69 q4 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q5 ∷
   re 69 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q5 ∷
   re 67 3 (ℓ "乓") ∷
   rw 68 q6 ∷
   rw 65 q6 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q1 ∷
   re 67 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q2 ∷
   rw 69 q3 ∷
   rw 68 q4 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q5 ∷
   re 68 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q5 ∷
   re 66 3 (ℓ "乓") ∷
   rw 67 q6 ∷
   rw 64 q6 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q1 ∷
   re 66 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q2 ∷
   rw 68 q3 ∷
   rw 67 q4 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q5 ∷
   re 67 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q5 ∷
   re 65 3 (ℓ "乓") ∷
   rw 66 q6 ∷
   rw 63 q6 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q1 ∷
   re 65 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q2 ∷
   rw 67 q3 ∷
   rw 66 q4 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q5 ∷
   re 66 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q5 ∷
   re 64 3 (ℓ "乓") ∷
   rw 65 q6 ∷
   rw 62 q6 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q1 ∷
   re 64 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q2 ∷
   rw 66 q3 ∷
   rw 65 q4 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q5 ∷
   re 65 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q5 ∷
   re 63 3 (ℓ "乓") ∷
   rw 64 q6 ∷
   rw 61 q6 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q1 ∷
   re 63 3 (ℓ "中") ∷
   re 63 1 (ℓ "乏丼丠丼乏") ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乓") ∷
   rw 66 q2 ∷
   rw 65 q3 ∷
   rw 64 q4 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q5 ∷
   re 64 5 (ℓ "中") ∷
   re 64 1 (ℓ "乏丧乏") ∷
   rw 66 q5 ∷
   re 62 3 (ℓ "乓") ∷
   rw 63 q6 ∷
   rw 60 q6 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q1 ∷
   re 62 3 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q2 ∷
   rw 64 q3 ∷
   rw 63 q4 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q5 ∷
   re 63 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q5 ∷
   re 61 3 (ℓ "乓") ∷
   rw 62 q6 ∷
   rw 59 q7 ∷
   rw 60 q8 ∷
   rw 61 q7 ∷
   rw 58 q9 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q1 ∷
   re 60 3 (ℓ "丱") ∷
   re 60 1 (ℓ "乏丼两丼乏") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q2 ∷
   rw 62 q10 ∷
   rw 61 q4 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q5 ∷
   re 61 5 (ℓ "丱") ∷
   re 61 1 (ℓ "乏丫乏") ∷
   rw 63 q5 ∷
   re 59 3 (ℓ "乓") ∷
   rw 60 q9 ∷
   rw 57 q7 ∷
   rw 58 q8 ∷
   rw 59 q7 ∷
   rw 56 q7 ∷
   rw 57 q8 ∷
   rw 58 q7 ∷
   rw 55 q7 ∷
   rw 56 q8 ∷
   rw 57 q7 ∷
   rw 54 q6 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q1 ∷
   re 56 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "乓") ∷
   rw 59 q2 ∷
   rw 58 q3 ∷
   rw 57 q4 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q5 ∷
   re 57 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q5 ∷
   re 55 3 (ℓ "乓") ∷
   rw 56 q6 ∷
   rw 53 q6 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q1 ∷
   re 55 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乓") ∷
   rw 58 q2 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q5 ∷
   re 56 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q5 ∷
   re 54 3 (ℓ "乓") ∷
   rw 55 q6 ∷
   rw 52 q6 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q1 ∷
   re 54 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "乓") ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 55 q4 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q5 ∷
   re 55 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q5 ∷
   re 53 3 (ℓ "乓") ∷
   rw 54 q6 ∷
   rw 51 q6 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q1 ∷
   re 53 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q2 ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q5 ∷
   re 54 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q5 ∷
   re 52 3 (ℓ "乓") ∷
   rw 53 q6 ∷
   rw 50 q6 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q1 ∷
   re 52 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q2 ∷
   rw 54 q3 ∷
   rw 53 q4 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q5 ∷
   re 53 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q5 ∷
   re 51 3 (ℓ "乓") ∷
   rw 52 q6 ∷
   rw 49 q6 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q1 ∷
   re 51 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q2 ∷
   rw 53 q3 ∷
   rw 52 q4 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q5 ∷
   re 52 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q5 ∷
   re 50 3 (ℓ "乓") ∷
   rw 51 q6 ∷
   rw 48 q6 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q1 ∷
   re 50 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q2 ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q5 ∷
   re 51 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q5 ∷
   re 49 3 (ℓ "乓") ∷
   rw 50 q6 ∷
   rw 47 q6 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q1 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q2 ∷
   rw 51 q3 ∷
   rw 50 q4 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q5 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q5 ∷
   re 48 3 (ℓ "乓") ∷
   rw 49 q6 ∷
   rw 46 q6 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q1 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q2 ∷
   rw 50 q3 ∷
   rw 49 q4 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q5 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q5 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q6 ∷
   rw 45 q6 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q1 ∷
   re 47 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q2 ∷
   rw 49 q3 ∷
   rw 48 q4 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q5 ∷
   re 48 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q5 ∷
   re 46 3 (ℓ "乓") ∷
   rw 47 q6 ∷
   rw 44 q6 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q1 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q1 ∷ []) Eq.refl
