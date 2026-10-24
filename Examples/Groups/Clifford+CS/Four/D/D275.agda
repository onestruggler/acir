{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D275 (W : Ws) where

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
  q14 : Eqn
  q14 = wE 858 W
  q15 : Eqn
  q15 = wE 783 W
  q16 : Eqn
  q16 = wE 21 W
  q17 : Eqn
  q17 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q18 : Eqn
  q18 = wE 51 W
  q19 : Eqn
  q19 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q20 : Eqn
  q20 = wE 782 W
  q21 : Eqn
  q21 = wE 353 W
  q22 : Eqn
  q22 = eqn (ℓ "丳乎") (ℓ "乎丳") (low-comm (CX₁₀) ((S • CK₀₁)))
  q23 : Eqn
  q23 = wE 358 W
  q24 : Eqn
  q24 = wE 859 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part7: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part7 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丞丧乓丞丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞乗业乗业义义义乗业义义义义义义丷丷丷乏丼乊丳丼乏丷丷丏主丷丷丷丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part7 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丞丧乓丞丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞乗业乗业义义义乗业义义义义义义丷丷丷乏丼乊丳丼乏丷丷丏主丷丷丷丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乓丞丞乊乘乊乊丞丞乊乊乊丞")
  (re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q1 ∷
   re 80 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q1 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q2 ∷
   rw 82 q3 ∷
   rw 81 q4 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q5 ∷
   re 81 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q5 ∷
   re 79 3 (ℓ "乓") ∷
   rw 80 q6 ∷
   rw 77 q7 ∷
   rw 78 q8 ∷
   rw 79 q7 ∷
   rw 76 q9 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q1 ∷
   re 78 3 (ℓ "丱") ∷
   re 78 1 (ℓ "乏丼两丼乏") ∷
   rw 84 q1 ∷
   re 82 3 (ℓ "乓") ∷
   rw 81 q2 ∷
   rw 80 q10 ∷
   rw 79 q4 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q5 ∷
   re 79 5 (ℓ "丱") ∷
   re 79 1 (ℓ "乏丫乏") ∷
   rw 81 q5 ∷
   re 77 3 (ℓ "乓") ∷
   rw 78 q9 ∷
   rw 75 q7 ∷
   rw 76 q8 ∷
   rw 77 q7 ∷
   rw 74 q7 ∷
   rw 75 q8 ∷
   rw 76 q7 ∷
   rw 73 q7 ∷
   rw 74 q8 ∷
   rw 75 q7 ∷
   rw 72 q6 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q1 ∷
   re 74 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q1 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q2 ∷
   rw 76 q3 ∷
   rw 75 q4 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q5 ∷
   re 75 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q5 ∷
   re 73 3 (ℓ "乓") ∷
   rw 74 q6 ∷
   rw 71 q6 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q1 ∷
   re 73 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "乓") ∷
   rw 76 q2 ∷
   rw 75 q3 ∷
   rw 74 q4 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q5 ∷
   re 74 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q5 ∷
   re 72 3 (ℓ "乓") ∷
   rw 73 q6 ∷
   rw 70 q6 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q1 ∷
   re 72 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q2 ∷
   rw 74 q3 ∷
   rw 73 q4 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q5 ∷
   re 73 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q5 ∷
   re 71 3 (ℓ "乓") ∷
   rw 72 q6 ∷
   rw 69 q6 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q1 ∷
   re 71 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q2 ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q5 ∷
   re 72 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q5 ∷
   re 70 3 (ℓ "乓") ∷
   rw 71 q6 ∷
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
   rw 59 q6 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q1 ∷
   re 61 3 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "乓") ∷
   rw 64 q2 ∷
   rw 63 q3 ∷
   rw 62 q4 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q5 ∷
   re 62 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q5 ∷
   re 60 3 (ℓ "乓") ∷
   rw 61 q6 ∷
   rw 58 q6 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q1 ∷
   re 60 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q2 ∷
   rw 62 q3 ∷
   rw 61 q4 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q5 ∷
   re 61 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q5 ∷
   re 59 3 (ℓ "乓") ∷
   rw 60 q6 ∷
   rw 57 q6 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "乓") ∷
   rw 62 q2 ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q5 ∷
   re 60 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q5 ∷
   re 58 3 (ℓ "乓") ∷
   rw 59 q6 ∷
   rw 56 q6 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乓") ∷
   rw 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q4 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q5 ∷
   re 59 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q5 ∷
   re 57 3 (ℓ "乓") ∷
   rw 58 q6 ∷
   rw 55 q6 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q1 ∷
   re 57 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q2 ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q5 ∷
   re 58 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q5 ∷
   re 56 3 (ℓ "乓") ∷
   rw 57 q6 ∷
   rw 58 q1 ∷
   rw 57 q11 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 58 q5 ∷
   rw 55 q11 ∷
   re 54 1 (ℓ "乏乃乏") ∷
   rw 56 q5 ∷
   rw 55 q12 ∷
   rw 54 q13 ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "乓") ∷
   rw 56 q13 ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "乐") ∷
   rw 58 q5 ∷
   rw 39 q14 ∷
   rw 101 q15 ∷
   re 100 1 (ℓ "乏丼丳丼乏") ∷
   rw 106 q1 ∷
   re 104 3 (ℓ "举") ∷
   rw 103 q16 ∷
   rw 102 q17 ∷
   rw 101 q18 ∷
   re 101 1 (ℓ "乏丷乏") ∷
   rw 100 q5 ∷
   re 101 5 (ℓ "乐") ∷
   re 101 1 (ℓ "乏丼丳丼乏") ∷
   rw 107 q1 ∷
   re 105 3 (ℓ "举") ∷
   rw 104 q16 ∷
   rw 103 q17 ∷
   rw 102 q18 ∷
   re 102 1 (ℓ "乏丷乏") ∷
   rw 101 q5 ∷
   re 102 5 (ℓ "乐") ∷
   re 102 1 (ℓ "乏丼丳丼乏") ∷
   rw 108 q1 ∷
   re 106 3 (ℓ "举") ∷
   rw 105 q16 ∷
   rw 104 q17 ∷
   rw 103 q18 ∷
   re 103 1 (ℓ "乏丷乏") ∷
   rw 102 q5 ∷
   re 103 5 (ℓ "乐") ∷
   re 103 1 (ℓ "乏丼丳丼乏") ∷
   rw 109 q1 ∷
   re 107 3 (ℓ "举") ∷
   rw 106 q16 ∷
   rw 105 q17 ∷
   rw 104 q18 ∷
   re 104 1 (ℓ "乏丷乏") ∷
   rw 103 q5 ∷
   re 104 5 (ℓ "乐") ∷
   re 104 1 (ℓ "乏丼丳丼乏") ∷
   rw 110 q1 ∷
   re 108 3 (ℓ "举") ∷
   rw 107 q16 ∷
   rw 106 q17 ∷
   rw 105 q18 ∷
   re 105 1 (ℓ "乏丷乏") ∷
   rw 104 q5 ∷
   re 105 5 (ℓ "乐") ∷
   re 105 1 (ℓ "乏丼丳丼乏") ∷
   rw 111 q1 ∷
   re 109 3 (ℓ "举") ∷
   rw 108 q16 ∷
   rw 107 q17 ∷
   rw 106 q18 ∷
   re 106 1 (ℓ "乏丷乏") ∷
   rw 105 q5 ∷
   re 106 5 (ℓ "乐") ∷
   rw 108 q1 ∷
   rw 107 q19 ∷
   re 106 1 (ℓ "乏乃乏") ∷
   rw 108 q5 ∷
   rw 107 q20 ∷
   rw⁻ 106 q19 ∷
   rw 109 q1 ∷
   re 107 3 (ℓ "乐") ∷
   rw 108 q5 ∷
   re 107 1 (ℓ "乏丼丳丼乏") ∷
   rw 113 q1 ∷
   re 111 3 (ℓ "乂") ∷
   rw 110 q21 ∷
   rw 109 q22 ∷
   rw 108 q23 ∷
   re 108 1 (ℓ "乏主乏") ∷
   rw 107 q5 ∷
   re 108 5 (ℓ "乐") ∷
   re 108 1 (ℓ "乏丼丳丼乏") ∷
   rw 114 q1 ∷
   re 112 3 (ℓ "举") ∷
   rw 111 q16 ∷
   rw 110 q17 ∷
   rw 109 q18 ∷
   re 109 1 (ℓ "乏丷乏") ∷
   rw 108 q5 ∷
   re 109 5 (ℓ "乐") ∷
   re 109 1 (ℓ "乏丼丳丼乏") ∷
   rw 115 q1 ∷
   re 113 3 (ℓ "举") ∷
   rw 112 q16 ∷
   rw 111 q17 ∷
   rw 110 q18 ∷
   re 110 1 (ℓ "乏丷乏") ∷
   rw 109 q5 ∷
   re 110 5 (ℓ "乐") ∷
   re 110 1 (ℓ "乏丼丳丼乏") ∷
   rw 116 q1 ∷
   re 114 3 (ℓ "举") ∷
   rw 113 q16 ∷
   rw 112 q17 ∷
   rw 111 q18 ∷
   re 111 1 (ℓ "乏丷乏") ∷
   rw 110 q5 ∷
   re 111 5 (ℓ "乐") ∷
   rw 58 q24 ∷
   re 57 1 (ℓ "乏丼丳丼乏") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "举") ∷
   rw 60 q16 ∷
   rw 59 q17 ∷
   rw 58 q18 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q5 ∷
   re 58 5 (ℓ "乐") ∷
   re 58 1 (ℓ "乏丼丳丼乏") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "举") ∷
   rw 61 q16 ∷
   rw 60 q17 ∷
   rw 59 q18 ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 58 q5 ∷
   re 59 5 (ℓ "乐") ∷
   re 59 1 (ℓ "乏丼丳丼乏") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "举") ∷
   rw 62 q16 ∷
   rw 61 q17 ∷
   rw 60 q18 ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q5 ∷
   re 60 5 (ℓ "乐") ∷
   re 60 1 (ℓ "乏丼丳丼乏") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "举") ∷
   rw 63 q16 ∷
   rw 62 q17 ∷ []) Eq.refl
