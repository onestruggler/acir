{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D276 (W : Ws) where

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
  q1 = wE 51 W
  q2 : Eqn
  q2 = wE 3 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 21 W
  q5 : Eqn
  q5 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q6 : Eqn
  q6 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q7 : Eqn
  q7 = wE 782 W
  q8 : Eqn
  q8 = wE 353 W
  q9 : Eqn
  q9 = eqn (ℓ "丳乎") (ℓ "乎丳") (low-comm (CX₁₀) ((S • CK₀₁)))
  q10 : Eqn
  q10 = wE 358 W
  q11 : Eqn
  q11 = wE 860 W
  q12 : Eqn
  q12 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q13 : Eqn
  q13 = wE 113 W
  q14 : Eqn
  q14 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q15 : Eqn
  q15 = wE 114 W
  q16 : Eqn
  q16 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q19 : Eqn
  q19 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q20 : Eqn
  q20 = wE 173 W
  q21 : Eqn
  q21 = wE 779 W
  q22 : Eqn
  q22 = wE 175 W

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part8: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part8 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞乗业乗业义义义乗业义义义义义义丷丷丷乏丼乊丳丼乏丷丷丏主丷丷丷丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丞乏乏乓丼丠丼乏乏丞丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part8 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞乗业乗业义义义乗业义义义义义义丷丷丷乏丼乊丳丼乏丷丷丏主丷丷丷丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丞乏乏乓丼丠丼乏乏丞丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丞乊乘乊乊丞丞乊乊乊丞")
  (rw 61 q1 ∷
   re 61 1 (ℓ "乏丷乏") ∷
   rw 60 q2 ∷
   re 61 5 (ℓ "乐") ∷
   re 61 1 (ℓ "乏丼丳丼乏") ∷
   rw 67 q3 ∷
   re 65 3 (ℓ "举") ∷
   rw 64 q4 ∷
   rw 63 q5 ∷
   rw 62 q1 ∷
   re 62 1 (ℓ "乏丷乏") ∷
   rw 61 q2 ∷
   re 62 5 (ℓ "乐") ∷
   re 62 1 (ℓ "乏丼丳丼乏") ∷
   rw 68 q3 ∷
   re 66 3 (ℓ "举") ∷
   rw 65 q4 ∷
   rw 64 q5 ∷
   rw 63 q1 ∷
   re 63 1 (ℓ "乏丷乏") ∷
   rw 62 q2 ∷
   re 63 5 (ℓ "乐") ∷
   rw 65 q3 ∷
   rw 64 q6 ∷
   re 63 1 (ℓ "乏乃乏") ∷
   rw 65 q2 ∷
   rw 64 q7 ∷
   rw⁻ 63 q6 ∷
   rw 66 q3 ∷
   re 64 3 (ℓ "乐") ∷
   rw 65 q2 ∷
   re 64 1 (ℓ "乏丼丳丼乏") ∷
   rw 70 q3 ∷
   re 68 3 (ℓ "乂") ∷
   rw 67 q8 ∷
   rw 66 q9 ∷
   rw 65 q10 ∷
   re 65 1 (ℓ "乏主乏") ∷
   rw 64 q2 ∷
   re 65 5 (ℓ "乐") ∷
   re 65 1 (ℓ "乏丼丳丼乏") ∷
   rw 71 q3 ∷
   re 69 3 (ℓ "举") ∷
   rw 68 q4 ∷
   rw 67 q5 ∷
   rw 66 q1 ∷
   re 66 1 (ℓ "乏丷乏") ∷
   rw 65 q2 ∷
   re 66 5 (ℓ "乐") ∷
   re 66 1 (ℓ "乏丼丳丼乏") ∷
   rw 72 q3 ∷
   re 70 3 (ℓ "举") ∷
   rw 69 q4 ∷
   rw 68 q5 ∷
   rw 67 q1 ∷
   re 67 1 (ℓ "乏丷乏") ∷
   rw 66 q2 ∷
   re 67 5 (ℓ "乐") ∷
   re 67 1 (ℓ "乏丼丳丼乏") ∷
   rw 73 q3 ∷
   re 71 3 (ℓ "举") ∷
   rw 70 q4 ∷
   rw 69 q5 ∷
   rw 68 q1 ∷
   re 68 1 (ℓ "乏丷乏") ∷
   rw 67 q2 ∷
   re 68 5 (ℓ "乐") ∷
   rw 42 q11 ∷
   rw 126 q12 ∷
   re 128 1 (ℓ "乏乆乏") ∷
   rw 127 q3 ∷
   re 128 3 (ℓ "中") ∷
   re 128 1 (ℓ "乏丼丠丼乏") ∷
   rw 134 q3 ∷
   re 132 3 (ℓ "乓") ∷
   rw 131 q13 ∷
   rw 130 q14 ∷
   rw 129 q15 ∷
   re 129 1 (ℓ "乏乆乏") ∷
   rw 128 q2 ∷
   re 129 5 (ℓ "中") ∷
   re 129 1 (ℓ "乏丧乏") ∷
   rw 131 q2 ∷
   re 127 3 (ℓ "乓") ∷
   rw 128 q12 ∷
   rw 125 q12 ∷
   re 127 1 (ℓ "乏乆乏") ∷
   rw 126 q3 ∷
   re 127 3 (ℓ "中") ∷
   re 127 1 (ℓ "乏丼丠丼乏") ∷
   rw 133 q3 ∷
   re 131 3 (ℓ "乓") ∷
   rw 130 q13 ∷
   rw 129 q14 ∷
   rw 128 q15 ∷
   re 128 1 (ℓ "乏乆乏") ∷
   rw 127 q2 ∷
   re 128 5 (ℓ "中") ∷
   re 128 1 (ℓ "乏丧乏") ∷
   rw 130 q2 ∷
   re 126 3 (ℓ "乓") ∷
   rw 127 q12 ∷
   rw 124 q12 ∷
   re 126 1 (ℓ "乏乆乏") ∷
   rw 125 q3 ∷
   re 126 3 (ℓ "中") ∷
   re 126 1 (ℓ "乏丼丠丼乏") ∷
   rw 132 q3 ∷
   re 130 3 (ℓ "乓") ∷
   rw 129 q13 ∷
   rw 128 q14 ∷
   rw 127 q15 ∷
   re 127 1 (ℓ "乏乆乏") ∷
   rw 126 q2 ∷
   re 127 5 (ℓ "中") ∷
   re 127 1 (ℓ "乏丧乏") ∷
   rw 129 q2 ∷
   re 125 3 (ℓ "乓") ∷
   rw 126 q12 ∷
   rw 123 q12 ∷
   re 125 1 (ℓ "乏乆乏") ∷
   rw 124 q3 ∷
   re 125 3 (ℓ "中") ∷
   re 125 1 (ℓ "乏丼丠丼乏") ∷
   rw 131 q3 ∷
   re 129 3 (ℓ "乓") ∷
   rw 128 q13 ∷
   rw 127 q14 ∷
   rw 126 q15 ∷
   re 126 1 (ℓ "乏乆乏") ∷
   rw 125 q2 ∷
   re 126 5 (ℓ "中") ∷
   re 126 1 (ℓ "乏丧乏") ∷
   rw 128 q2 ∷
   re 124 3 (ℓ "乓") ∷
   rw 125 q12 ∷
   rw 122 q12 ∷
   re 124 1 (ℓ "乏乆乏") ∷
   rw 123 q3 ∷
   re 124 3 (ℓ "中") ∷
   re 124 1 (ℓ "乏丼丠丼乏") ∷
   rw 130 q3 ∷
   re 128 3 (ℓ "乓") ∷
   rw 127 q13 ∷
   rw 126 q14 ∷
   rw 125 q15 ∷
   re 125 1 (ℓ "乏乆乏") ∷
   rw 124 q2 ∷
   re 125 5 (ℓ "中") ∷
   re 125 1 (ℓ "乏丧乏") ∷
   rw 127 q2 ∷
   re 123 3 (ℓ "乓") ∷
   rw 124 q12 ∷
   rw 121 q12 ∷
   re 123 1 (ℓ "乏乆乏") ∷
   rw 122 q3 ∷
   re 123 3 (ℓ "中") ∷
   re 123 1 (ℓ "乏丼丠丼乏") ∷
   rw 129 q3 ∷
   re 127 3 (ℓ "乓") ∷
   rw 126 q13 ∷
   rw 125 q14 ∷
   rw 124 q15 ∷
   re 124 1 (ℓ "乏乆乏") ∷
   rw 123 q2 ∷
   re 124 5 (ℓ "中") ∷
   re 124 1 (ℓ "乏丧乏") ∷
   rw 126 q2 ∷
   re 122 3 (ℓ "乓") ∷
   rw 123 q12 ∷
   rw 120 q16 ∷
   rw 121 q17 ∷
   rw 122 q16 ∷
   rw 119 q18 ∷
   re 121 1 (ℓ "乏乆乏") ∷
   rw 120 q3 ∷
   re 121 3 (ℓ "丱") ∷
   re 121 1 (ℓ "乏丼两丼乏") ∷
   rw 127 q3 ∷
   re 125 3 (ℓ "乓") ∷
   rw 124 q13 ∷
   rw 123 q19 ∷
   rw 122 q15 ∷
   re 122 1 (ℓ "乏乆乏") ∷
   rw 121 q2 ∷
   re 122 5 (ℓ "丱") ∷
   re 122 1 (ℓ "乏丫乏") ∷
   rw 124 q2 ∷
   re 120 3 (ℓ "乓") ∷
   rw 121 q18 ∷
   rw 118 q12 ∷
   re 120 1 (ℓ "乏乆乏") ∷
   rw 119 q3 ∷
   re 120 3 (ℓ "中") ∷
   re 120 1 (ℓ "乏丼丠丼乏") ∷
   rw 126 q3 ∷
   re 124 3 (ℓ "乓") ∷
   rw 123 q13 ∷
   rw 122 q14 ∷
   rw 121 q15 ∷
   re 121 1 (ℓ "乏乆乏") ∷
   rw 120 q2 ∷
   re 121 5 (ℓ "中") ∷
   re 121 1 (ℓ "乏丧乏") ∷
   rw 123 q2 ∷
   re 119 3 (ℓ "乓") ∷
   rw 120 q12 ∷
   rw 117 q12 ∷
   re 119 1 (ℓ "乏乆乏") ∷
   rw 118 q3 ∷
   re 119 3 (ℓ "中") ∷
   re 119 1 (ℓ "乏丼丠丼乏") ∷
   rw 125 q3 ∷
   re 123 3 (ℓ "乓") ∷
   rw 122 q13 ∷
   rw 121 q14 ∷
   rw 120 q15 ∷
   re 120 1 (ℓ "乏乆乏") ∷
   rw 119 q2 ∷
   re 120 5 (ℓ "中") ∷
   re 120 1 (ℓ "乏丧乏") ∷
   rw 122 q2 ∷
   re 118 3 (ℓ "乓") ∷
   rw 119 q12 ∷
   rw 116 q12 ∷
   re 118 1 (ℓ "乏乆乏") ∷
   rw 117 q3 ∷
   re 118 3 (ℓ "中") ∷
   re 118 1 (ℓ "乏丼丠丼乏") ∷
   rw 124 q3 ∷
   re 122 3 (ℓ "乓") ∷
   rw 121 q13 ∷
   rw 120 q14 ∷
   rw 119 q15 ∷
   re 119 1 (ℓ "乏乆乏") ∷
   rw 118 q2 ∷
   re 119 5 (ℓ "中") ∷
   re 119 1 (ℓ "乏丧乏") ∷
   rw 121 q2 ∷
   re 117 3 (ℓ "乓") ∷
   rw 118 q12 ∷
   rw 115 q16 ∷
   rw 116 q17 ∷
   rw 117 q16 ∷
   rw 114 q18 ∷
   re 116 1 (ℓ "乏乆乏") ∷
   rw 115 q3 ∷
   re 116 3 (ℓ "丱") ∷
   re 116 1 (ℓ "乏丼两丼乏") ∷
   rw 122 q3 ∷
   re 120 3 (ℓ "乓") ∷
   rw 119 q13 ∷
   rw 118 q19 ∷
   rw 117 q15 ∷
   re 117 1 (ℓ "乏乆乏") ∷
   rw 116 q2 ∷
   re 117 5 (ℓ "丱") ∷
   re 117 1 (ℓ "乏丫乏") ∷
   rw 119 q2 ∷
   re 115 3 (ℓ "乓") ∷
   rw 116 q18 ∷
   rw 113 q16 ∷
   rw 114 q17 ∷
   rw 115 q16 ∷
   rw 112 q18 ∷
   re 114 1 (ℓ "乏乆乏") ∷
   rw 113 q3 ∷
   re 114 3 (ℓ "丱") ∷
   re 114 1 (ℓ "乏丼两丼乏") ∷
   rw 120 q3 ∷
   re 118 3 (ℓ "乓") ∷
   rw 117 q13 ∷
   rw 116 q19 ∷
   rw 115 q15 ∷
   re 115 1 (ℓ "乏乆乏") ∷
   rw 114 q2 ∷
   re 115 5 (ℓ "丱") ∷
   re 115 1 (ℓ "乏丫乏") ∷
   rw 117 q2 ∷
   re 113 3 (ℓ "乓") ∷
   rw 114 q18 ∷
   rw 115 q3 ∷
   rw 114 q20 ∷
   re 113 1 (ℓ "乏乆乏") ∷
   rw 115 q2 ∷
   rw 112 q20 ∷
   re 111 1 (ℓ "乏乃乏") ∷
   rw 113 q2 ∷
   rw 112 q21 ∷
   rw 111 q22 ∷
   rw 114 q3 ∷
   re 112 3 (ℓ "乓") ∷
   rw 113 q22 ∷
   rw 116 q3 ∷
   re 114 3 (ℓ "乐") ∷
   rw 115 q2 ∷
   rw 110 q16 ∷
   rw 111 q17 ∷
   rw 112 q16 ∷
   rw 109 q18 ∷
   re 111 1 (ℓ "乏乆乏") ∷
   rw 110 q3 ∷
   re 111 3 (ℓ "丱") ∷
   re 111 1 (ℓ "乏丼两丼乏") ∷
   rw 117 q3 ∷
   re 115 3 (ℓ "乓") ∷
   rw 114 q13 ∷
   rw 113 q19 ∷
   rw 112 q15 ∷
   re 112 1 (ℓ "乏乆乏") ∷
   rw 111 q2 ∷
   re 112 5 (ℓ "丱") ∷
   re 112 1 (ℓ "乏丫乏") ∷
   rw 114 q2 ∷
   re 110 3 (ℓ "乓") ∷
   rw 111 q18 ∷
   rw 108 q16 ∷
   rw 109 q17 ∷
   rw 110 q16 ∷
   rw 107 q16 ∷
   rw 108 q17 ∷
   rw 109 q16 ∷
   rw 106 q16 ∷
   rw 107 q17 ∷
   rw 108 q16 ∷
   rw 105 q16 ∷
   rw 106 q17 ∷
   rw 107 q16 ∷
   rw 104 q18 ∷
   re 106 1 (ℓ "乏乆乏") ∷
   rw 105 q3 ∷
   re 106 3 (ℓ "丱") ∷
   re 106 1 (ℓ "乏丼两丼乏") ∷
   rw 112 q3 ∷
   re 110 3 (ℓ "乓") ∷
   rw 109 q13 ∷
   rw 108 q19 ∷
   rw 107 q15 ∷
   re 107 1 (ℓ "乏乆乏") ∷
   rw 106 q2 ∷
   re 107 5 (ℓ "丱") ∷
   re 107 1 (ℓ "乏丫乏") ∷
   rw 109 q2 ∷
   re 105 3 (ℓ "乓") ∷
   rw 106 q18 ∷
   rw 103 q16 ∷
   rw 104 q17 ∷
   rw 105 q16 ∷
   rw 102 q16 ∷
   rw 103 q17 ∷
   rw 104 q16 ∷
   rw 101 q16 ∷
   rw 102 q17 ∷
   rw 103 q16 ∷
   rw 100 q12 ∷
   re 102 1 (ℓ "乏乆乏") ∷
   rw 101 q3 ∷
   re 102 3 (ℓ "中") ∷
   re 102 1 (ℓ "乏丼丠丼乏") ∷
   rw 108 q3 ∷
   re 106 3 (ℓ "乓") ∷
   rw 105 q13 ∷
   rw 104 q14 ∷
   rw 103 q15 ∷
   re 103 1 (ℓ "乏乆乏") ∷
   rw 102 q2 ∷
   re 103 5 (ℓ "中") ∷
   re 103 1 (ℓ "乏丧乏") ∷
   rw 105 q2 ∷
   re 101 3 (ℓ "乓") ∷
   rw 102 q12 ∷
   rw 99 q12 ∷
   re 101 1 (ℓ "乏乆乏") ∷
   rw 100 q3 ∷
   re 101 3 (ℓ "中") ∷
   re 101 1 (ℓ "乏丼丠丼乏") ∷
   rw 107 q3 ∷
   re 105 3 (ℓ "乓") ∷
   rw 104 q13 ∷
   rw 103 q14 ∷
   rw 102 q15 ∷
   re 102 1 (ℓ "乏乆乏") ∷
   rw 101 q2 ∷
   re 102 5 (ℓ "中") ∷
   re 102 1 (ℓ "乏丧乏") ∷
   rw 104 q2 ∷
   re 100 3 (ℓ "乓") ∷
   rw 101 q12 ∷
   rw 98 q12 ∷
   re 100 1 (ℓ "乏乆乏") ∷
   rw 99 q3 ∷
   re 100 3 (ℓ "中") ∷
   re 100 1 (ℓ "乏丼丠丼乏") ∷
   rw 106 q3 ∷
   re 104 3 (ℓ "乓") ∷
   rw 103 q13 ∷
   rw 102 q14 ∷
   rw 101 q15 ∷
   re 101 1 (ℓ "乏乆乏") ∷
   rw 100 q2 ∷
   re 101 5 (ℓ "中") ∷
   re 101 1 (ℓ "乏丧乏") ∷
   rw 103 q2 ∷
   re 99 3 (ℓ "乓") ∷
   rw 100 q12 ∷
   rw 97 q12 ∷
   re 99 1 (ℓ "乏乆乏") ∷
   rw 98 q3 ∷
   re 99 3 (ℓ "中") ∷
   re 99 1 (ℓ "乏丼丠丼乏") ∷
   rw 105 q3 ∷
   re 103 3 (ℓ "乓") ∷
   rw 102 q13 ∷
   rw 101 q14 ∷
   rw 100 q15 ∷
   re 100 1 (ℓ "乏乆乏") ∷
   rw 99 q2 ∷
   re 100 5 (ℓ "中") ∷
   re 100 1 (ℓ "乏丧乏") ∷
   rw 102 q2 ∷
   re 98 3 (ℓ "乓") ∷
   rw 99 q12 ∷
   rw 96 q12 ∷
   re 98 1 (ℓ "乏乆乏") ∷
   rw 97 q3 ∷
   re 98 3 (ℓ "中") ∷
   re 98 1 (ℓ "乏丼丠丼乏") ∷
   rw 104 q3 ∷
   re 102 3 (ℓ "乓") ∷
   rw 101 q13 ∷
   rw 100 q14 ∷
   rw 99 q15 ∷
   re 99 1 (ℓ "乏乆乏") ∷
   rw 98 q2 ∷
   re 99 5 (ℓ "中") ∷
   re 99 1 (ℓ "乏丧乏") ∷
   rw 101 q2 ∷
   re 97 3 (ℓ "乓") ∷
   rw 98 q12 ∷
   rw 95 q12 ∷
   re 97 1 (ℓ "乏乆乏") ∷
   rw 96 q3 ∷
   re 97 3 (ℓ "中") ∷
   re 97 1 (ℓ "乏丼丠丼乏") ∷
   rw 103 q3 ∷
   re 101 3 (ℓ "乓") ∷
   rw 100 q13 ∷
   rw 99 q14 ∷
   rw 98 q15 ∷
   re 98 1 (ℓ "乏乆乏") ∷
   rw 97 q2 ∷
   re 98 5 (ℓ "中") ∷
   re 98 1 (ℓ "乏丧乏") ∷
   rw 100 q2 ∷
   re 96 3 (ℓ "乓") ∷
   rw 97 q12 ∷
   rw 94 q12 ∷
   re 96 1 (ℓ "乏乆乏") ∷
   rw 95 q3 ∷
   re 96 3 (ℓ "中") ∷
   re 96 1 (ℓ "乏丼丠丼乏") ∷
   rw 102 q3 ∷
   re 100 3 (ℓ "乓") ∷
   rw 99 q13 ∷
   rw 98 q14 ∷
   rw 97 q15 ∷
   re 97 1 (ℓ "乏乆乏") ∷
   rw 96 q2 ∷
   re 97 5 (ℓ "中") ∷
   re 97 1 (ℓ "乏丧乏") ∷
   rw 99 q2 ∷
   re 95 3 (ℓ "乓") ∷
   rw 96 q12 ∷
   rw 93 q12 ∷
   re 95 1 (ℓ "乏乆乏") ∷
   rw 94 q3 ∷
   re 95 3 (ℓ "中") ∷
   re 95 1 (ℓ "乏丼丠丼乏") ∷
   rw 101 q3 ∷
   re 99 3 (ℓ "乓") ∷
   rw 98 q13 ∷
   rw 97 q14 ∷
   rw 96 q15 ∷
   re 96 1 (ℓ "乏乆乏") ∷
   rw 95 q2 ∷
   re 96 5 (ℓ "中") ∷
   re 96 1 (ℓ "乏丧乏") ∷
   rw 98 q2 ∷
   re 94 3 (ℓ "乓") ∷
   rw 95 q12 ∷
   rw 92 q12 ∷
   re 94 1 (ℓ "乏乆乏") ∷
   rw 93 q3 ∷
   re 94 3 (ℓ "中") ∷
   re 94 1 (ℓ "乏丼丠丼乏") ∷
   rw 100 q3 ∷
   re 98 3 (ℓ "乓") ∷
   rw 97 q13 ∷
   rw 96 q14 ∷
   rw 95 q15 ∷ []) Eq.refl
