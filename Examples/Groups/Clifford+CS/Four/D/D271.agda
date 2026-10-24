{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D271 (W : Ws) where

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
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 779 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = wE 858 W
  q11 : Eqn
  q11 = wE 783 W
  q12 : Eqn
  q12 = wE 21 W
  q13 : Eqn
  q13 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q14 : Eqn
  q14 = wE 51 W
  q15 : Eqn
  q15 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q16 : Eqn
  q16 = wE 782 W
  q17 : Eqn
  q17 = wE 353 W
  q18 : Eqn
  q18 = eqn (ℓ "丳乎") (ℓ "乎丳") (low-comm (CX₁₀) ((S • CK₀₁)))
  q19 : Eqn
  q19 = wE 358 W
  q20 : Eqn
  q20 = wE 859 W
  q21 : Eqn
  q21 = wE 860 W
  q22 : Eqn
  q22 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q24 : Eqn
  q24 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q25 : Eqn
  q25 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (ℓ "丞举丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丞乏乆乏丧乏乏丞丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丞乏乏丼丠丼乏乆乏丞丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (ℓ "丞举丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丞乏乆乏丧乏乏丞丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丞乏乏丼丠丼乏乆乏丞丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞")
  (rw 36 q1 ∷
   re 32 3 (ℓ "乓") ∷
   rw 33 q2 ∷
   rw 30 q2 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q3 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "乓") ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   rw 33 q6 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q1 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q1 ∷
   re 31 3 (ℓ "乓") ∷
   rw 32 q2 ∷
   rw 29 q2 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q3 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   rw 32 q6 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q1 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q1 ∷
   re 30 3 (ℓ "乓") ∷
   rw 31 q2 ∷
   rw 28 q2 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q3 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q6 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q1 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q1 ∷
   re 29 3 (ℓ "乓") ∷
   rw 30 q2 ∷
   rw 27 q2 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q3 ∷
   re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   rw 30 q6 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q1 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q1 ∷
   re 28 3 (ℓ "乓") ∷
   rw 29 q2 ∷
   rw 26 q2 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q3 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   rw 29 q6 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q1 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q1 ∷
   re 27 3 (ℓ "乓") ∷
   rw 28 q2 ∷
   rw 25 q2 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q3 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   rw 28 q6 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q1 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q1 ∷
   re 26 3 (ℓ "乓") ∷
   rw 27 q2 ∷
   rw 24 q2 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q3 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   rw 27 q6 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q1 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q1 ∷
   re 25 3 (ℓ "乓") ∷
   rw 26 q2 ∷
   rw 23 q2 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q3 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "乓") ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q1 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q1 ∷
   re 24 3 (ℓ "乓") ∷
   rw 25 q2 ∷
   rw 26 q3 ∷
   rw 25 q7 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 26 q1 ∷
   rw 23 q7 ∷
   re 22 1 (ℓ "乏乃乏") ∷
   rw 24 q1 ∷
   rw 23 q8 ∷
   rw 22 q9 ∷
   rw 25 q3 ∷
   re 23 3 (ℓ "乓") ∷
   rw 24 q9 ∷
   rw 27 q3 ∷
   re 25 3 (ℓ "乐") ∷
   rw 26 q1 ∷
   rw 7 q10 ∷
   rw 69 q11 ∷
   re 68 1 (ℓ "乏丼丳丼乏") ∷
   rw 74 q3 ∷
   re 72 3 (ℓ "举") ∷
   rw 71 q12 ∷
   rw 70 q13 ∷
   rw 69 q14 ∷
   re 69 1 (ℓ "乏丷乏") ∷
   rw 68 q1 ∷
   re 69 5 (ℓ "乐") ∷
   re 69 1 (ℓ "乏丼丳丼乏") ∷
   rw 75 q3 ∷
   re 73 3 (ℓ "举") ∷
   rw 72 q12 ∷
   rw 71 q13 ∷
   rw 70 q14 ∷
   re 70 1 (ℓ "乏丷乏") ∷
   rw 69 q1 ∷
   re 70 5 (ℓ "乐") ∷
   re 70 1 (ℓ "乏丼丳丼乏") ∷
   rw 76 q3 ∷
   re 74 3 (ℓ "举") ∷
   rw 73 q12 ∷
   rw 72 q13 ∷
   rw 71 q14 ∷
   re 71 1 (ℓ "乏丷乏") ∷
   rw 70 q1 ∷
   re 71 5 (ℓ "乐") ∷
   re 71 1 (ℓ "乏丼丳丼乏") ∷
   rw 77 q3 ∷
   re 75 3 (ℓ "举") ∷
   rw 74 q12 ∷
   rw 73 q13 ∷
   rw 72 q14 ∷
   re 72 1 (ℓ "乏丷乏") ∷
   rw 71 q1 ∷
   re 72 5 (ℓ "乐") ∷
   re 72 1 (ℓ "乏丼丳丼乏") ∷
   rw 78 q3 ∷
   re 76 3 (ℓ "举") ∷
   rw 75 q12 ∷
   rw 74 q13 ∷
   rw 73 q14 ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 72 q1 ∷
   re 73 5 (ℓ "乐") ∷
   re 73 1 (ℓ "乏丼丳丼乏") ∷
   rw 79 q3 ∷
   re 77 3 (ℓ "举") ∷
   rw 76 q12 ∷
   rw 75 q13 ∷
   rw 74 q14 ∷
   re 74 1 (ℓ "乏丷乏") ∷
   rw 73 q1 ∷
   re 74 5 (ℓ "乐") ∷
   rw 76 q3 ∷
   rw 75 q15 ∷
   re 74 1 (ℓ "乏乃乏") ∷
   rw 76 q1 ∷
   rw 75 q16 ∷
   rw⁻ 74 q15 ∷
   rw 77 q3 ∷
   re 75 3 (ℓ "乐") ∷
   rw 76 q1 ∷
   re 75 1 (ℓ "乏丼丳丼乏") ∷
   rw 81 q3 ∷
   re 79 3 (ℓ "乂") ∷
   rw 78 q17 ∷
   rw 77 q18 ∷
   rw 76 q19 ∷
   re 76 1 (ℓ "乏主乏") ∷
   rw 75 q1 ∷
   re 76 5 (ℓ "乐") ∷
   re 76 1 (ℓ "乏丼丳丼乏") ∷
   rw 82 q3 ∷
   re 80 3 (ℓ "举") ∷
   rw 79 q12 ∷
   rw 78 q13 ∷
   rw 77 q14 ∷
   re 77 1 (ℓ "乏丷乏") ∷
   rw 76 q1 ∷
   re 77 5 (ℓ "乐") ∷
   re 77 1 (ℓ "乏丼丳丼乏") ∷
   rw 83 q3 ∷
   re 81 3 (ℓ "举") ∷
   rw 80 q12 ∷
   rw 79 q13 ∷
   rw 78 q14 ∷
   re 78 1 (ℓ "乏丷乏") ∷
   rw 77 q1 ∷
   re 78 5 (ℓ "乐") ∷
   re 78 1 (ℓ "乏丼丳丼乏") ∷
   rw 84 q3 ∷
   re 82 3 (ℓ "举") ∷
   rw 81 q12 ∷
   rw 80 q13 ∷
   rw 79 q14 ∷
   re 79 1 (ℓ "乏丷乏") ∷
   rw 78 q1 ∷
   re 79 5 (ℓ "乐") ∷
   rw 26 q20 ∷
   re 25 1 (ℓ "乏丼丳丼乏") ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q12 ∷
   rw 27 q13 ∷
   rw 26 q14 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q1 ∷
   re 26 5 (ℓ "乐") ∷
   re 26 1 (ℓ "乏丼丳丼乏") ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q12 ∷
   rw 28 q13 ∷
   rw 27 q14 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q1 ∷
   re 27 5 (ℓ "乐") ∷
   re 27 1 (ℓ "乏丼丳丼乏") ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q12 ∷
   rw 29 q13 ∷
   rw 28 q14 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q1 ∷
   re 28 5 (ℓ "乐") ∷
   re 28 1 (ℓ "乏丼丳丼乏") ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q12 ∷
   rw 30 q13 ∷
   rw 29 q14 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q1 ∷
   re 29 5 (ℓ "乐") ∷
   re 29 1 (ℓ "乏丼丳丼乏") ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q12 ∷
   rw 31 q13 ∷
   rw 30 q14 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q1 ∷
   re 30 5 (ℓ "乐") ∷
   re 30 1 (ℓ "乏丼丳丼乏") ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q12 ∷
   rw 32 q13 ∷
   rw 31 q14 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q1 ∷
   re 31 5 (ℓ "乐") ∷
   rw 33 q3 ∷
   rw 32 q15 ∷
   re 31 1 (ℓ "乏乃乏") ∷
   rw 33 q1 ∷
   rw 32 q16 ∷
   rw⁻ 31 q15 ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "乐") ∷
   rw 33 q1 ∷
   re 32 1 (ℓ "乏丼丳丼乏") ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "乂") ∷
   rw 35 q17 ∷
   rw 34 q18 ∷
   rw 33 q19 ∷
   re 33 1 (ℓ "乏主乏") ∷
   rw 32 q1 ∷
   re 33 5 (ℓ "乐") ∷
   re 33 1 (ℓ "乏丼丳丼乏") ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "举") ∷
   rw 36 q12 ∷
   rw 35 q13 ∷
   rw 34 q14 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 33 q1 ∷
   re 34 5 (ℓ "乐") ∷
   re 34 1 (ℓ "乏丼丳丼乏") ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "举") ∷
   rw 37 q12 ∷
   rw 36 q13 ∷
   rw 35 q14 ∷
   re 35 1 (ℓ "乏丷乏") ∷
   rw 34 q1 ∷
   re 35 5 (ℓ "乐") ∷
   re 35 1 (ℓ "乏丼丳丼乏") ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "举") ∷
   rw 38 q12 ∷
   rw 37 q13 ∷
   rw 36 q14 ∷
   re 36 1 (ℓ "乏丷乏") ∷
   rw 35 q1 ∷
   re 36 5 (ℓ "乐") ∷
   rw 10 q21 ∷
   rw 94 q2 ∷
   re 96 1 (ℓ "乏乆乏") ∷
   rw 95 q3 ∷
   re 96 3 (ℓ "中") ∷
   re 96 1 (ℓ "乏丼丠丼乏") ∷
   rw 102 q3 ∷
   re 100 3 (ℓ "乓") ∷
   rw 99 q4 ∷
   rw 98 q5 ∷
   rw 97 q6 ∷
   re 97 1 (ℓ "乏乆乏") ∷
   rw 96 q1 ∷
   re 97 5 (ℓ "中") ∷
   re 97 1 (ℓ "乏丧乏") ∷
   rw 99 q1 ∷
   re 95 3 (ℓ "乓") ∷
   rw 96 q2 ∷
   rw 93 q2 ∷
   re 95 1 (ℓ "乏乆乏") ∷
   rw 94 q3 ∷
   re 95 3 (ℓ "中") ∷
   re 95 1 (ℓ "乏丼丠丼乏") ∷
   rw 101 q3 ∷
   re 99 3 (ℓ "乓") ∷
   rw 98 q4 ∷
   rw 97 q5 ∷
   rw 96 q6 ∷
   re 96 1 (ℓ "乏乆乏") ∷
   rw 95 q1 ∷
   re 96 5 (ℓ "中") ∷
   re 96 1 (ℓ "乏丧乏") ∷
   rw 98 q1 ∷
   re 94 3 (ℓ "乓") ∷
   rw 95 q2 ∷
   rw 92 q2 ∷
   re 94 1 (ℓ "乏乆乏") ∷
   rw 93 q3 ∷
   re 94 3 (ℓ "中") ∷
   re 94 1 (ℓ "乏丼丠丼乏") ∷
   rw 100 q3 ∷
   re 98 3 (ℓ "乓") ∷
   rw 97 q4 ∷
   rw 96 q5 ∷
   rw 95 q6 ∷
   re 95 1 (ℓ "乏乆乏") ∷
   rw 94 q1 ∷
   re 95 5 (ℓ "中") ∷
   re 95 1 (ℓ "乏丧乏") ∷
   rw 97 q1 ∷
   re 93 3 (ℓ "乓") ∷
   rw 94 q2 ∷
   rw 91 q2 ∷
   re 93 1 (ℓ "乏乆乏") ∷
   rw 92 q3 ∷
   re 93 3 (ℓ "中") ∷
   re 93 1 (ℓ "乏丼丠丼乏") ∷
   rw 99 q3 ∷
   re 97 3 (ℓ "乓") ∷
   rw 96 q4 ∷
   rw 95 q5 ∷
   rw 94 q6 ∷
   re 94 1 (ℓ "乏乆乏") ∷
   rw 93 q1 ∷
   re 94 5 (ℓ "中") ∷
   re 94 1 (ℓ "乏丧乏") ∷
   rw 96 q1 ∷
   re 92 3 (ℓ "乓") ∷
   rw 93 q2 ∷
   rw 90 q2 ∷
   re 92 1 (ℓ "乏乆乏") ∷
   rw 91 q3 ∷
   re 92 3 (ℓ "中") ∷
   re 92 1 (ℓ "乏丼丠丼乏") ∷
   rw 98 q3 ∷
   re 96 3 (ℓ "乓") ∷
   rw 95 q4 ∷
   rw 94 q5 ∷
   rw 93 q6 ∷
   re 93 1 (ℓ "乏乆乏") ∷
   rw 92 q1 ∷
   re 93 5 (ℓ "中") ∷
   re 93 1 (ℓ "乏丧乏") ∷
   rw 95 q1 ∷
   re 91 3 (ℓ "乓") ∷
   rw 92 q2 ∷
   rw 89 q2 ∷
   re 91 1 (ℓ "乏乆乏") ∷
   rw 90 q3 ∷
   re 91 3 (ℓ "中") ∷
   re 91 1 (ℓ "乏丼丠丼乏") ∷
   rw 97 q3 ∷
   re 95 3 (ℓ "乓") ∷
   rw 94 q4 ∷
   rw 93 q5 ∷
   rw 92 q6 ∷
   re 92 1 (ℓ "乏乆乏") ∷
   rw 91 q1 ∷
   re 92 5 (ℓ "中") ∷
   re 92 1 (ℓ "乏丧乏") ∷
   rw 94 q1 ∷
   re 90 3 (ℓ "乓") ∷
   rw 91 q2 ∷
   rw 88 q22 ∷
   rw 89 q23 ∷
   rw 90 q22 ∷
   rw 87 q24 ∷
   re 89 1 (ℓ "乏乆乏") ∷
   rw 88 q3 ∷
   re 89 3 (ℓ "丱") ∷
   re 89 1 (ℓ "乏丼两丼乏") ∷
   rw 95 q3 ∷
   re 93 3 (ℓ "乓") ∷
   rw 92 q4 ∷
   rw 91 q25 ∷
   rw 90 q6 ∷
   re 90 1 (ℓ "乏乆乏") ∷
   rw 89 q1 ∷
   re 90 5 (ℓ "丱") ∷
   re 90 1 (ℓ "乏丫乏") ∷
   rw 92 q1 ∷
   re 88 3 (ℓ "乓") ∷
   rw 89 q24 ∷
   rw 86 q2 ∷
   re 88 1 (ℓ "乏乆乏") ∷
   rw 87 q3 ∷
   re 88 3 (ℓ "中") ∷
   re 88 1 (ℓ "乏丼丠丼乏") ∷
   rw 94 q3 ∷
   re 92 3 (ℓ "乓") ∷
   rw 91 q4 ∷
   rw 90 q5 ∷
   rw 89 q6 ∷
   re 89 1 (ℓ "乏乆乏") ∷
   rw 88 q1 ∷
   re 89 5 (ℓ "中") ∷
   re 89 1 (ℓ "乏丧乏") ∷
   rw 91 q1 ∷
   re 87 3 (ℓ "乓") ∷
   rw 88 q2 ∷
   rw 85 q2 ∷
   re 87 1 (ℓ "乏乆乏") ∷
   rw 86 q3 ∷
   re 87 3 (ℓ "中") ∷
   re 87 1 (ℓ "乏丼丠丼乏") ∷ []) Eq.refl
