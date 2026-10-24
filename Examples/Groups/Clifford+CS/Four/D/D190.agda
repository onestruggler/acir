{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D190 (W : Ws) where

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
  q2 = wE 353 W
  q3 : Eqn
  q3 = eqn (ℓ "丳乎") (ℓ "乎丳") (low-comm (CX₁₀) ((S • CK₀₁)))
  q4 : Eqn
  q4 = wE 358 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 21 W
  q7 : Eqn
  q7 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q8 : Eqn
  q8 = wE 51 W
  q9 : Eqn
  q9 = wE 777 W
  q10 : Eqn
  q10 = wE 778 W
  q11 : Eqn
  q11 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q12 : Eqn
  q12 = wE 113 W
  q13 : Eqn
  q13 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q14 : Eqn
  q14 = wE 114 W
  q15 : Eqn
  q15 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q16 : Eqn
  q16 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q17 : Eqn
  q17 = wE 173 W
  q18 : Eqn
  q18 = wE 779 W
  q19 : Eqn
  q19 = wE 175 W
  q20 : Eqn
  q20 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q21 : Eqn
  q21 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q22 : Eqn
  q22 = wE 780 W
  q23 : Eqn
  q23 = wE 781 W
  q24 : Eqn
  q24 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q25 : Eqn
  q25 = wE 782 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->2) passes white iX via V2 conjugates 1 part3: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷乐主丷丷丧丧丫丧丫丫丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷乏乏丷乏丼丳丼乏丷丧丧丫丧丫丫丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part3 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷乐主丷丷丧丧丫丧丫丫丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷乏乏丷乏丼丳丼乏丷丧丧丫丧丫丫丞乓丞丞乊乘乊乊丞丞乊乊乊丞")
  (re 58 1 (ℓ "乏丼丳丼乏") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乂") ∷
   rw 61 q2 ∷
   rw 60 q3 ∷
   rw 59 q4 ∷
   re 59 1 (ℓ "乏主乏") ∷
   rw 58 q5 ∷
   re 59 5 (ℓ "乐") ∷
   re 59 1 (ℓ "乏丼丳丼乏") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "举") ∷
   rw 62 q6 ∷
   rw 61 q7 ∷
   rw 60 q8 ∷
   re 60 1 (ℓ "乏丷乏") ∷
   rw 59 q5 ∷
   re 60 5 (ℓ "乐") ∷
   re 60 1 (ℓ "乏丼丳丼乏") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "举") ∷
   rw 63 q6 ∷
   rw 62 q7 ∷
   rw 61 q8 ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q5 ∷
   re 61 5 (ℓ "乐") ∷
   rw 42 q9 ∷
   re 41 1 (ℓ "乏丼丳丼乏") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "举") ∷
   rw 44 q6 ∷
   rw 43 q7 ∷
   rw 42 q8 ∷
   re 42 1 (ℓ "乏丷乏") ∷
   rw 41 q5 ∷
   re 42 5 (ℓ "乐") ∷
   re 42 1 (ℓ "乏丼丳丼乏") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "乂") ∷
   rw 45 q2 ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   re 43 1 (ℓ "乏主乏") ∷
   rw 42 q5 ∷
   re 43 5 (ℓ "乐") ∷
   re 43 1 (ℓ "乏丼丳丼乏") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "举") ∷
   rw 46 q6 ∷
   rw 45 q7 ∷
   rw 44 q8 ∷
   re 44 1 (ℓ "乏丷乏") ∷
   rw 43 q5 ∷
   re 44 5 (ℓ "乐") ∷
   re 44 1 (ℓ "乏丼丳丼乏") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "举") ∷
   rw 47 q6 ∷
   rw 46 q7 ∷
   rw 45 q8 ∷
   re 45 1 (ℓ "乏丷乏") ∷
   rw 44 q5 ∷
   re 45 5 (ℓ "乐") ∷
   rw 35 q10 ∷
   rw 67 q11 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q1 ∷
   re 69 3 (ℓ "丱") ∷
   re 69 1 (ℓ "乏丼两丼乏") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "乓") ∷
   rw 72 q12 ∷
   rw 71 q13 ∷
   rw 70 q14 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q5 ∷
   re 70 5 (ℓ "丱") ∷
   re 70 1 (ℓ "乏丫乏") ∷
   rw 72 q5 ∷
   re 68 3 (ℓ "乓") ∷
   rw 69 q11 ∷
   rw 66 q11 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q1 ∷
   re 68 3 (ℓ "丱") ∷
   re 68 1 (ℓ "乏丼两丼乏") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q12 ∷
   rw 70 q13 ∷
   rw 69 q14 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q5 ∷
   re 69 5 (ℓ "丱") ∷
   re 69 1 (ℓ "乏丫乏") ∷
   rw 71 q5 ∷
   re 67 3 (ℓ "乓") ∷
   rw 68 q11 ∷
   rw 65 q15 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q1 ∷
   re 67 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q12 ∷
   rw 69 q16 ∷
   rw 68 q14 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q5 ∷
   re 68 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q5 ∷
   re 66 3 (ℓ "乓") ∷
   rw 67 q15 ∷
   rw 64 q11 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q1 ∷
   re 66 3 (ℓ "丱") ∷
   re 66 1 (ℓ "乏丼两丼乏") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q12 ∷
   rw 68 q13 ∷
   rw 67 q14 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q5 ∷
   re 67 5 (ℓ "丱") ∷
   re 67 1 (ℓ "乏丫乏") ∷
   rw 69 q5 ∷
   re 65 3 (ℓ "乓") ∷
   rw 66 q11 ∷
   rw 63 q15 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q1 ∷
   re 65 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏丼丠丼乏") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "乓") ∷
   rw 68 q12 ∷
   rw 67 q16 ∷
   rw 66 q14 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q5 ∷
   re 66 5 (ℓ "中") ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q5 ∷
   re 64 3 (ℓ "乓") ∷
   rw 65 q15 ∷
   rw 62 q15 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q1 ∷
   re 64 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q12 ∷
   rw 66 q16 ∷
   rw 65 q14 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q5 ∷
   re 65 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q5 ∷
   re 63 3 (ℓ "乓") ∷
   rw 64 q15 ∷
   rw 65 q1 ∷
   rw 64 q17 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 65 q5 ∷
   rw 62 q17 ∷
   re 61 1 (ℓ "乏乃乏") ∷
   rw 63 q5 ∷
   rw 62 q18 ∷
   rw 61 q19 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乓") ∷
   rw 63 q19 ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乐") ∷
   rw 65 q5 ∷
   rw 60 q15 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q1 ∷
   re 62 3 (ℓ "中") ∷
   re 62 1 (ℓ "乏丼丠丼乏") ∷
   rw 68 q1 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q12 ∷
   rw 64 q16 ∷
   rw 63 q14 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q5 ∷
   re 63 5 (ℓ "中") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw 65 q5 ∷
   re 61 3 (ℓ "乓") ∷
   rw 62 q15 ∷
   rw 59 q15 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q1 ∷
   re 61 3 (ℓ "中") ∷
   re 61 1 (ℓ "乏丼丠丼乏") ∷
   rw 67 q1 ∷
   re 65 3 (ℓ "乓") ∷
   rw 64 q12 ∷
   rw 63 q16 ∷
   rw 62 q14 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q5 ∷
   re 62 5 (ℓ "中") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw 64 q5 ∷
   re 60 3 (ℓ "乓") ∷
   rw 61 q15 ∷
   rw 58 q15 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q1 ∷
   re 60 3 (ℓ "中") ∷
   re 60 1 (ℓ "乏丼丠丼乏") ∷
   rw 66 q1 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q12 ∷
   rw 62 q16 ∷
   rw 61 q14 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q5 ∷
   re 61 5 (ℓ "中") ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q5 ∷
   re 59 3 (ℓ "乓") ∷
   rw 60 q15 ∷
   rw 57 q15 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "中") ∷
   re 59 1 (ℓ "乏丼丠丼乏") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "乓") ∷
   rw 62 q12 ∷
   rw 61 q16 ∷
   rw 60 q14 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q5 ∷
   re 60 5 (ℓ "中") ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q5 ∷
   re 58 3 (ℓ "乓") ∷
   rw 59 q15 ∷
   rw 56 q15 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乓") ∷
   rw 61 q12 ∷
   rw 60 q16 ∷
   rw 59 q14 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 58 q5 ∷
   re 59 5 (ℓ "中") ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q5 ∷
   re 57 3 (ℓ "乓") ∷
   rw 58 q15 ∷
   rw 55 q15 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q1 ∷
   re 57 3 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q12 ∷
   rw 59 q16 ∷
   rw 58 q14 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q5 ∷
   re 58 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q5 ∷
   re 56 3 (ℓ "乓") ∷
   rw 57 q15 ∷
   rw 54 q20 ∷
   rw 55 q21 ∷
   rw 56 q20 ∷
   rw 53 q11 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q1 ∷
   re 55 3 (ℓ "丱") ∷
   re 55 1 (ℓ "乏丼两丼乏") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "乓") ∷
   rw 58 q12 ∷
   rw 57 q13 ∷
   rw 56 q14 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 55 q5 ∷
   re 56 5 (ℓ "丱") ∷
   re 56 1 (ℓ "乏丫乏") ∷
   rw 58 q5 ∷
   re 54 3 (ℓ "乓") ∷
   rw 55 q11 ∷
   rw 52 q15 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q1 ∷
   re 54 3 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "乓") ∷
   rw 57 q12 ∷
   rw 56 q16 ∷
   rw 55 q14 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 54 q5 ∷
   re 55 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q5 ∷
   re 53 3 (ℓ "乓") ∷
   rw 54 q15 ∷
   rw 51 q15 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q1 ∷
   re 53 3 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "乓") ∷
   rw 56 q12 ∷
   rw 55 q16 ∷
   rw 54 q14 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 53 q5 ∷
   re 54 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q5 ∷
   re 52 3 (ℓ "乓") ∷
   rw 53 q15 ∷
   rw 50 q15 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q1 ∷
   re 52 3 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q12 ∷
   rw 54 q16 ∷
   rw 53 q14 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q5 ∷
   re 53 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q5 ∷
   re 51 3 (ℓ "乓") ∷
   rw 52 q15 ∷
   rw 49 q20 ∷
   rw 50 q21 ∷
   rw 51 q20 ∷
   rw 48 q11 ∷
   re 50 1 (ℓ "乏乆乏") ∷
   rw 49 q1 ∷
   re 50 3 (ℓ "丱") ∷
   re 50 1 (ℓ "乏丼两丼乏") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "乓") ∷
   rw 53 q12 ∷
   rw 52 q13 ∷
   rw 51 q14 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 50 q5 ∷
   re 51 5 (ℓ "丱") ∷
   re 51 1 (ℓ "乏丫乏") ∷
   rw 53 q5 ∷
   re 49 3 (ℓ "乓") ∷
   rw 50 q11 ∷
   rw 47 q20 ∷
   rw 48 q21 ∷
   rw 49 q20 ∷
   rw 46 q11 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q1 ∷
   re 48 3 (ℓ "丱") ∷
   re 48 1 (ℓ "乏丼两丼乏") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q12 ∷
   rw 50 q13 ∷
   rw 49 q14 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q5 ∷
   re 49 5 (ℓ "丱") ∷
   re 49 1 (ℓ "乏丫乏") ∷
   rw 51 q5 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q11 ∷
   rw 49 q1 ∷
   rw 48 q17 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 49 q5 ∷
   rw 46 q17 ∷
   re 45 1 (ℓ "乏乃乏") ∷
   rw 47 q5 ∷
   rw 46 q18 ∷
   rw 45 q19 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "乓") ∷
   rw 47 q19 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乐") ∷
   rw 49 q5 ∷
   rw 39 q22 ∷
   rw 65 q23 ∷
   re 64 1 (ℓ "乏丼丳丼乏") ∷
   rw 70 q1 ∷
   re 68 3 (ℓ "举") ∷
   rw 67 q6 ∷
   rw 66 q7 ∷
   rw 65 q8 ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q5 ∷
   re 65 5 (ℓ "乐") ∷
   re 65 1 (ℓ "乏丼丳丼乏") ∷
   rw 71 q1 ∷
   re 69 3 (ℓ "举") ∷
   rw 68 q6 ∷
   rw 67 q7 ∷
   rw 66 q8 ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q5 ∷
   re 66 5 (ℓ "乐") ∷
   re 66 1 (ℓ "乏丼丳丼乏") ∷
   rw 72 q1 ∷
   re 70 3 (ℓ "举") ∷
   rw 69 q6 ∷
   rw 68 q7 ∷
   rw 67 q8 ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 66 q5 ∷
   re 67 5 (ℓ "乐") ∷
   re 67 1 (ℓ "乏丼丳丼乏") ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "举") ∷
   rw 70 q6 ∷
   rw 69 q7 ∷
   rw 68 q8 ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 67 q5 ∷
   re 68 5 (ℓ "乐") ∷
   re 68 1 (ℓ "乏丼丳丼乏") ∷
   rw 74 q1 ∷
   re 72 3 (ℓ "举") ∷
   rw 71 q6 ∷
   rw 70 q7 ∷
   rw 69 q8 ∷
   re 69 1 (ℓ "乏丷乏") ∷
   rw 68 q5 ∷
   re 69 5 (ℓ "乐") ∷
   re 69 1 (ℓ "乏丼丳丼乏") ∷
   rw 75 q1 ∷
   re 73 3 (ℓ "举") ∷
   rw 72 q6 ∷
   rw 71 q7 ∷
   rw 70 q8 ∷
   re 70 1 (ℓ "乏丷乏") ∷
   rw 69 q5 ∷
   re 70 5 (ℓ "乐") ∷
   rw 72 q1 ∷
   rw 71 q24 ∷
   re 70 1 (ℓ "乏乃乏") ∷
   rw 72 q5 ∷
   rw 71 q25 ∷
   rw⁻ 70 q24 ∷
   rw 73 q1 ∷
   re 71 3 (ℓ "乐") ∷
   rw 72 q5 ∷
   re 71 1 (ℓ "乏丼丳丼乏") ∷
   rw 77 q1 ∷
   re 75 3 (ℓ "乂") ∷
   rw 74 q2 ∷
   rw 73 q3 ∷
   rw 72 q4 ∷
   re 72 1 (ℓ "乏主乏") ∷
   rw 71 q5 ∷
   re 72 5 (ℓ "乐") ∷
   re 72 1 (ℓ "乏丼丳丼乏") ∷
   rw 78 q1 ∷
   re 76 3 (ℓ "举") ∷
   rw 75 q6 ∷
   rw 74 q7 ∷
   rw 73 q8 ∷
   re 73 1 (ℓ "乏丷乏") ∷
   rw 72 q5 ∷
   re 73 5 (ℓ "乐") ∷
   re 73 1 (ℓ "乏丼丳丼乏") ∷
   rw 79 q1 ∷
   re 77 3 (ℓ "举") ∷
   rw 76 q6 ∷
   rw 75 q7 ∷
   rw 74 q8 ∷
   re 74 1 (ℓ "乏丷乏") ∷ []) Eq.refl
