{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D270 (W : Ws) where

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
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 113 W
  q5 : Eqn
  q5 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q6 : Eqn
  q6 = wE 114 W
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

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part2: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2 : ⟪ (ℓ "丞举丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丞乏乆中乏丞丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丞乏乆乏丧乏乏丞丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2 = derive (ℓ "丞举丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丞乏乆中乏丞丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丞乏乆乏丧乏乏丞丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞")
  (re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q1 ∷
   re 73 3 (ℓ "乓") ∷
   rw 74 q2 ∷
   rw 71 q2 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q3 ∷
   re 73 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q3 ∷
   re 77 3 (ℓ "乓") ∷
   rw 76 q4 ∷
   rw 75 q5 ∷
   rw 74 q6 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q1 ∷
   re 74 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q1 ∷
   re 72 3 (ℓ "乓") ∷
   rw 73 q2 ∷
   rw 70 q2 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q3 ∷
   re 72 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q3 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q4 ∷
   rw 74 q5 ∷
   rw 73 q6 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q1 ∷
   re 73 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q1 ∷
   re 71 3 (ℓ "乓") ∷
   rw 72 q2 ∷
   rw 69 q7 ∷
   rw 70 q8 ∷
   rw 71 q7 ∷
   rw 68 q9 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q3 ∷
   re 70 3 (ℓ "丱") ∷
   re 70 1 (ℓ "乏丼两丼乏") ∷
   rw 76 q3 ∷
   re 74 3 (ℓ "乓") ∷
   rw 73 q4 ∷
   rw 72 q10 ∷
   rw 71 q6 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q1 ∷
   re 71 5 (ℓ "丱") ∷
   re 71 1 (ℓ "乏丫乏") ∷
   rw 73 q1 ∷
   re 69 3 (ℓ "乓") ∷
   rw 70 q9 ∷
   rw 67 q7 ∷
   rw 68 q8 ∷
   rw 69 q7 ∷
   rw 66 q9 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q3 ∷
   re 68 3 (ℓ "丱") ∷
   re 68 1 (ℓ "乏丼两丼乏") ∷
   rw 74 q3 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q4 ∷
   rw 70 q10 ∷
   rw 69 q6 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q1 ∷
   re 69 5 (ℓ "丱") ∷
   re 69 1 (ℓ "乏丫乏") ∷
   rw 71 q1 ∷
   re 67 3 (ℓ "乓") ∷
   rw 68 q9 ∷
   rw 69 q3 ∷
   rw 68 q11 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 69 q1 ∷
   rw 66 q11 ∷
   re 65 1 (ℓ "乏乃乏") ∷
   rw 67 q1 ∷
   rw 66 q12 ∷
   rw 65 q13 ∷
   rw 68 q3 ∷
   re 66 3 (ℓ "乓") ∷
   rw 67 q13 ∷
   rw 70 q3 ∷
   re 68 3 (ℓ "乐") ∷
   rw 69 q1 ∷
   rw 64 q7 ∷
   rw 65 q8 ∷
   rw 66 q7 ∷
   rw 63 q9 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q3 ∷
   re 65 3 (ℓ "丱") ∷
   re 65 1 (ℓ "乏丼两丼乏") ∷
   rw 71 q3 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q4 ∷
   rw 67 q10 ∷
   rw 66 q6 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q1 ∷
   re 66 5 (ℓ "丱") ∷
   re 66 1 (ℓ "乏丫乏") ∷
   rw 68 q1 ∷
   re 64 3 (ℓ "乓") ∷
   rw 65 q9 ∷
   rw 62 q7 ∷
   rw 63 q8 ∷
   rw 64 q7 ∷
   rw 61 q7 ∷
   rw 62 q8 ∷
   rw 63 q7 ∷
   rw 60 q7 ∷
   rw 61 q8 ∷
   rw 62 q7 ∷
   rw 59 q7 ∷
   rw 60 q8 ∷
   rw 61 q7 ∷
   rw 58 q9 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q3 ∷
   re 60 3 (ℓ "丱") ∷
   re 60 1 (ℓ "乏丼两丼乏") ∷
   rw 66 q3 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q4 ∷
   rw 62 q10 ∷
   rw 61 q6 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q1 ∷
   re 61 5 (ℓ "丱") ∷
   re 61 1 (ℓ "乏丫乏") ∷
   rw 63 q1 ∷
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
   rw 54 q2 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q3 ∷
   re 56 3 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 62 q3 ∷
   re 60 3 (ℓ "乓") ∷
   rw 59 q4 ∷
   rw 58 q5 ∷
   rw 57 q6 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q1 ∷
   re 57 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q1 ∷
   re 55 3 (ℓ "乓") ∷
   rw 56 q2 ∷
   rw 53 q2 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q3 ∷
   re 55 3 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 61 q3 ∷
   re 59 3 (ℓ "乓") ∷
   rw 58 q4 ∷
   rw 57 q5 ∷
   rw 56 q6 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q1 ∷
   re 56 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q1 ∷
   re 54 3 (ℓ "乓") ∷
   rw 55 q2 ∷
   rw 52 q2 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q3 ∷
   re 54 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q3 ∷
   re 58 3 (ℓ "乓") ∷
   rw 57 q4 ∷
   rw 56 q5 ∷
   rw 55 q6 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q1 ∷
   re 55 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q1 ∷
   re 53 3 (ℓ "乓") ∷
   rw 54 q2 ∷
   rw 51 q2 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q3 ∷
   re 53 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q3 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q4 ∷
   rw 55 q5 ∷
   rw 54 q6 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q1 ∷
   re 54 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q1 ∷
   re 52 3 (ℓ "乓") ∷
   rw 53 q2 ∷
   rw 50 q2 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q3 ∷
   re 52 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q3 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q4 ∷
   rw 54 q5 ∷
   rw 53 q6 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q1 ∷
   re 53 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q1 ∷
   re 51 3 (ℓ "乓") ∷
   rw 52 q2 ∷
   rw 49 q2 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q3 ∷
   re 51 3 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q3 ∷
   re 55 3 (ℓ "乓") ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   rw 52 q6 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q1 ∷
   re 52 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q1 ∷
   re 50 3 (ℓ "乓") ∷
   rw 51 q2 ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q3 ∷
   re 50 3 (ℓ "中") ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q3 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q4 ∷
   rw 52 q5 ∷
   rw 51 q6 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q1 ∷
   re 51 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q1 ∷
   re 49 3 (ℓ "乓") ∷
   rw 50 q2 ∷
   rw 47 q2 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q3 ∷
   re 49 3 (ℓ "中") ∷
   re 49 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q3 ∷
   re 53 3 (ℓ "乓") ∷
   rw 52 q4 ∷
   rw 51 q5 ∷
   rw 50 q6 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q1 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q1 ∷
   re 48 3 (ℓ "乓") ∷
   rw 49 q2 ∷
   rw 46 q2 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q3 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q3 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   rw 49 q6 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q1 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q1 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q2 ∷
   rw 45 q7 ∷
   rw 46 q8 ∷
   rw 47 q7 ∷
   rw 44 q9 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q3 ∷
   re 46 3 (ℓ "丱") ∷
   re 46 1 (ℓ "乏丼两丼乏") ∷
   rw 52 q3 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q4 ∷
   rw 48 q10 ∷
   rw 47 q6 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q1 ∷
   re 47 5 (ℓ "丱") ∷
   re 47 1 (ℓ "乏丫乏") ∷
   rw 49 q1 ∷
   re 45 3 (ℓ "乓") ∷
   rw 46 q9 ∷
   rw 43 q7 ∷
   rw 44 q8 ∷
   rw 45 q7 ∷
   rw 42 q7 ∷
   rw 43 q8 ∷
   rw 44 q7 ∷
   rw 41 q7 ∷
   rw 42 q8 ∷
   rw 43 q7 ∷
   rw 40 q2 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q3 ∷
   re 42 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q3 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   rw 43 q6 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q1 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q1 ∷
   re 41 3 (ℓ "乓") ∷
   rw 42 q2 ∷
   rw 39 q2 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q3 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q3 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q4 ∷
   rw 43 q5 ∷
   rw 42 q6 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q1 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q1 ∷
   re 40 3 (ℓ "乓") ∷
   rw 41 q2 ∷
   rw 38 q2 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q3 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q3 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   rw 41 q6 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q1 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q1 ∷
   re 39 3 (ℓ "乓") ∷
   rw 40 q2 ∷
   rw 37 q2 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q3 ∷
   re 39 3 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q3 ∷
   re 43 3 (ℓ "乓") ∷
   rw 42 q4 ∷
   rw 41 q5 ∷
   rw 40 q6 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q1 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q1 ∷
   re 38 3 (ℓ "乓") ∷
   rw 39 q2 ∷
   rw 36 q2 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q3 ∷
   re 38 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q3 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q4 ∷
   rw 40 q5 ∷
   rw 39 q6 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q1 ∷
   re 39 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q1 ∷
   re 37 3 (ℓ "乓") ∷
   rw 38 q2 ∷
   rw 35 q2 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q3 ∷
   re 37 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q3 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q4 ∷
   rw 39 q5 ∷
   rw 38 q6 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q1 ∷
   re 38 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q1 ∷
   re 36 3 (ℓ "乓") ∷
   rw 37 q2 ∷
   rw 34 q2 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q3 ∷
   re 36 3 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q3 ∷
   re 40 3 (ℓ "乓") ∷
   rw 39 q4 ∷
   rw 38 q5 ∷
   rw 37 q6 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q1 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q1 ∷
   re 35 3 (ℓ "乓") ∷
   rw 36 q2 ∷
   rw 33 q2 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q3 ∷
   re 35 3 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q4 ∷
   rw 37 q5 ∷
   rw 36 q6 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 35 q1 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q1 ∷
   re 34 3 (ℓ "乓") ∷
   rw 35 q2 ∷
   rw 32 q2 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q3 ∷
   re 34 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q4 ∷
   rw 36 q5 ∷
   rw 35 q6 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q1 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q1 ∷
   re 33 3 (ℓ "乓") ∷
   rw 34 q2 ∷
   rw 31 q2 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q3 ∷
   re 33 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   rw 34 q6 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q1 ∷
   re 34 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丧乏") ∷ []) Eq.refl
