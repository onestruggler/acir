{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D191 (W : Ws) where

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
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 21 W
  q4 : Eqn
  q4 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 51 W
  q6 : Eqn
  q6 = wE 783 W
  q7 : Eqn
  q7 = eqn (ℓ "丏乏") (ℓ "乏丏") (low-comm (((S • S • S) ↑)) (Swap))
  q8 : Eqn
  q8 = wE 782 W
  q9 : Eqn
  q9 = wE 353 W
  q10 : Eqn
  q10 = eqn (ℓ "丳乎") (ℓ "乎丳") (low-comm (CX₁₀) ((S • CK₀₁)))
  q11 : Eqn
  q11 = wE 358 W
  q12 : Eqn
  q12 = wE 784 W
  q13 : Eqn
  q13 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q14 : Eqn
  q14 = wE 113 W
  q15 : Eqn
  q15 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q16 : Eqn
  q16 = wE 114 W
  q17 : Eqn
  q17 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q18 : Eqn
  q18 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q19 : Eqn
  q19 = wE 173 W
  q20 : Eqn
  q20 = wE 779 W
  q21 : Eqn
  q21 = wE 175 W
  q22 : Eqn
  q22 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q24 : Eqn
  q24 = wE 780 W
  q25 : Eqn
  q25 = wE 5 W
  q26 : Eqn
  q26 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q27 : Eqn
  q27 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q28 : Eqn
  q28 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q29 : Eqn
  q29 = wE 772 W
  q30 : Eqn
  q30 = wE 7 W
  q31 : Eqn
  q31 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q32 : Eqn
  q32 = wE 6 W
  q33 : Eqn
  q33 = wE 481 W
  q34 : Eqn
  q34 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q35 : Eqn
  q35 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->2) passes white iX via V2 conjugates 1 part4: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷乏乏丷乏丼丳丼乏丷丧丧丫丧丫丫丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞义义並乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞乊乘乊乊丞並丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part4 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷乏乏丷乏丼丳丼乏丷丧丧丫丧丫丫丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞义义並乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丞乊乘乊乊丞並丞乊乊乊丞")
  (rw 73 q1 ∷
   re 74 5 (ℓ "乐") ∷
   re 74 1 (ℓ "乏丼丳丼乏") ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "举") ∷
   rw 77 q3 ∷
   rw 76 q4 ∷
   rw 75 q5 ∷
   re 75 1 (ℓ "乏丷乏") ∷
   rw 74 q1 ∷
   re 75 5 (ℓ "乐") ∷
   rw 49 q6 ∷
   re 48 1 (ℓ "乏丼丳丼乏") ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "举") ∷
   rw 51 q3 ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   re 49 1 (ℓ "乏丷乏") ∷
   rw 48 q1 ∷
   re 49 5 (ℓ "乐") ∷
   re 49 1 (ℓ "乏丼丳丼乏") ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "举") ∷
   rw 52 q3 ∷
   rw 51 q4 ∷
   rw 50 q5 ∷
   re 50 1 (ℓ "乏丷乏") ∷
   rw 49 q1 ∷
   re 50 5 (ℓ "乐") ∷
   re 50 1 (ℓ "乏丼丳丼乏") ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "举") ∷
   rw 53 q3 ∷
   rw 52 q4 ∷
   rw 51 q5 ∷
   re 51 1 (ℓ "乏丷乏") ∷
   rw 50 q1 ∷
   re 51 5 (ℓ "乐") ∷
   re 51 1 (ℓ "乏丼丳丼乏") ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "举") ∷
   rw 54 q3 ∷
   rw 53 q4 ∷
   rw 52 q5 ∷
   re 52 1 (ℓ "乏丷乏") ∷
   rw 51 q1 ∷
   re 52 5 (ℓ "乐") ∷
   re 52 1 (ℓ "乏丼丳丼乏") ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "举") ∷
   rw 55 q3 ∷
   rw 54 q4 ∷
   rw 53 q5 ∷
   re 53 1 (ℓ "乏丷乏") ∷
   rw 52 q1 ∷
   re 53 5 (ℓ "乐") ∷
   re 53 1 (ℓ "乏丼丳丼乏") ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "举") ∷
   rw 56 q3 ∷
   rw 55 q4 ∷
   rw 54 q5 ∷
   re 54 1 (ℓ "乏丷乏") ∷
   rw 53 q1 ∷
   re 54 5 (ℓ "乐") ∷
   rw 56 q2 ∷
   rw 55 q7 ∷
   re 54 1 (ℓ "乏乃乏") ∷
   rw 56 q1 ∷
   rw 55 q8 ∷
   rw⁻ 54 q7 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "乐") ∷
   rw 56 q1 ∷
   re 55 1 (ℓ "乏丼丳丼乏") ∷
   rw 61 q2 ∷
   re 59 3 (ℓ "乂") ∷
   rw 58 q9 ∷
   rw 57 q10 ∷
   rw 56 q11 ∷
   re 56 1 (ℓ "乏主乏") ∷
   rw 55 q1 ∷
   re 56 5 (ℓ "乐") ∷
   re 56 1 (ℓ "乏丼丳丼乏") ∷
   rw 62 q2 ∷
   re 60 3 (ℓ "举") ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   rw 57 q5 ∷
   re 57 1 (ℓ "乏丷乏") ∷
   rw 56 q1 ∷
   re 57 5 (ℓ "乐") ∷
   re 57 1 (ℓ "乏丼丳丼乏") ∷
   rw 63 q2 ∷
   re 61 3 (ℓ "举") ∷
   rw 60 q3 ∷
   rw 59 q4 ∷
   rw 58 q5 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q1 ∷
   re 58 5 (ℓ "乐") ∷
   re 58 1 (ℓ "乏丼丳丼乏") ∷
   rw 64 q2 ∷
   re 62 3 (ℓ "举") ∷
   rw 61 q3 ∷
   rw 60 q4 ∷
   rw 59 q5 ∷
   re 59 1 (ℓ "乏丷乏") ∷
   rw 58 q1 ∷
   re 59 5 (ℓ "乐") ∷
   rw 42 q12 ∷
   rw 81 q13 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q2 ∷
   re 83 3 (ℓ "丱") ∷
   re 83 1 (ℓ "乏丼两丼乏") ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "乓") ∷
   rw 86 q14 ∷
   rw 85 q15 ∷
   rw 84 q16 ∷
   re 84 1 (ℓ "乏乆乏") ∷
   rw 83 q1 ∷
   re 84 5 (ℓ "丱") ∷
   re 84 1 (ℓ "乏丫乏") ∷
   rw 86 q1 ∷
   re 82 3 (ℓ "乓") ∷
   rw 83 q13 ∷
   rw 80 q13 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q2 ∷
   re 82 3 (ℓ "丱") ∷
   re 82 1 (ℓ "乏丼两丼乏") ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q14 ∷
   rw 84 q15 ∷
   rw 83 q16 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q1 ∷
   re 83 5 (ℓ "丱") ∷
   re 83 1 (ℓ "乏丫乏") ∷
   rw 85 q1 ∷
   re 81 3 (ℓ "乓") ∷
   rw 82 q13 ∷
   rw 79 q17 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q2 ∷
   re 81 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q2 ∷
   re 85 3 (ℓ "乓") ∷
   rw 84 q14 ∷
   rw 83 q18 ∷
   rw 82 q16 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q1 ∷
   re 82 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q1 ∷
   re 80 3 (ℓ "乓") ∷
   rw 81 q17 ∷
   rw 78 q13 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q2 ∷
   re 80 3 (ℓ "丱") ∷
   re 80 1 (ℓ "乏丼两丼乏") ∷
   rw 86 q2 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q14 ∷
   rw 82 q15 ∷
   rw 81 q16 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q1 ∷
   re 81 5 (ℓ "丱") ∷
   re 81 1 (ℓ "乏丫乏") ∷
   rw 83 q1 ∷
   re 79 3 (ℓ "乓") ∷
   rw 80 q13 ∷
   rw 77 q17 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q2 ∷
   re 79 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q2 ∷
   re 83 3 (ℓ "乓") ∷
   rw 82 q14 ∷
   rw 81 q18 ∷
   rw 80 q16 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q1 ∷
   re 80 5 (ℓ "中") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q1 ∷
   re 78 3 (ℓ "乓") ∷
   rw 79 q17 ∷
   rw 76 q17 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q2 ∷
   re 78 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q2 ∷
   re 82 3 (ℓ "乓") ∷
   rw 81 q14 ∷
   rw 80 q18 ∷
   rw 79 q16 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q1 ∷
   re 79 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q1 ∷
   re 77 3 (ℓ "乓") ∷
   rw 78 q17 ∷
   rw 79 q2 ∷
   rw 78 q19 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 79 q1 ∷
   rw 76 q19 ∷
   re 75 1 (ℓ "乏乃乏") ∷
   rw 77 q1 ∷
   rw 76 q20 ∷
   rw 75 q21 ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "乓") ∷
   rw 77 q21 ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "乐") ∷
   rw 79 q1 ∷
   rw 74 q17 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q2 ∷
   re 76 3 (ℓ "中") ∷
   re 76 1 (ℓ "乏丼丠丼乏") ∷
   rw 82 q2 ∷
   re 80 3 (ℓ "乓") ∷
   rw 79 q14 ∷
   rw 78 q18 ∷
   rw 77 q16 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q1 ∷
   re 77 5 (ℓ "中") ∷
   re 77 1 (ℓ "乏丧乏") ∷
   rw 79 q1 ∷
   re 75 3 (ℓ "乓") ∷
   rw 76 q17 ∷
   rw 73 q17 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q2 ∷
   re 75 3 (ℓ "中") ∷
   re 75 1 (ℓ "乏丼丠丼乏") ∷
   rw 81 q2 ∷
   re 79 3 (ℓ "乓") ∷
   rw 78 q14 ∷
   rw 77 q18 ∷
   rw 76 q16 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q1 ∷
   re 76 5 (ℓ "中") ∷
   re 76 1 (ℓ "乏丧乏") ∷
   rw 78 q1 ∷
   re 74 3 (ℓ "乓") ∷
   rw 75 q17 ∷
   rw 72 q17 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q2 ∷
   re 74 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q14 ∷
   rw 76 q18 ∷
   rw 75 q16 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q1 ∷
   re 75 5 (ℓ "中") ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q1 ∷
   re 73 3 (ℓ "乓") ∷
   rw 74 q17 ∷
   rw 71 q17 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q2 ∷
   re 73 3 (ℓ "中") ∷
   re 73 1 (ℓ "乏丼丠丼乏") ∷
   rw 79 q2 ∷
   re 77 3 (ℓ "乓") ∷
   rw 76 q14 ∷
   rw 75 q18 ∷
   rw 74 q16 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q1 ∷
   re 74 5 (ℓ "中") ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q1 ∷
   re 72 3 (ℓ "乓") ∷
   rw 73 q17 ∷
   rw 70 q17 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q2 ∷
   re 72 3 (ℓ "中") ∷
   re 72 1 (ℓ "乏丼丠丼乏") ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "乓") ∷
   rw 75 q14 ∷
   rw 74 q18 ∷
   rw 73 q16 ∷
   re 73 1 (ℓ "乏乆乏") ∷
   rw 72 q1 ∷
   re 73 5 (ℓ "中") ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q1 ∷
   re 71 3 (ℓ "乓") ∷
   rw 72 q17 ∷
   rw 69 q17 ∷
   re 71 1 (ℓ "乏乆乏") ∷
   rw 70 q2 ∷
   re 71 3 (ℓ "中") ∷
   re 71 1 (ℓ "乏丼丠丼乏") ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "乓") ∷
   rw 74 q14 ∷
   rw 73 q18 ∷
   rw 72 q16 ∷
   re 72 1 (ℓ "乏乆乏") ∷
   rw 71 q1 ∷
   re 72 5 (ℓ "中") ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q1 ∷
   re 70 3 (ℓ "乓") ∷
   rw 71 q17 ∷
   rw 68 q22 ∷
   rw 69 q23 ∷
   rw 70 q22 ∷
   rw 67 q13 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q2 ∷
   re 69 3 (ℓ "丱") ∷
   re 69 1 (ℓ "乏丼两丼乏") ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "乓") ∷
   rw 72 q14 ∷
   rw 71 q15 ∷
   rw 70 q16 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 69 q1 ∷
   re 70 5 (ℓ "丱") ∷
   re 70 1 (ℓ "乏丫乏") ∷
   rw 72 q1 ∷
   re 68 3 (ℓ "乓") ∷
   rw 69 q13 ∷
   rw 66 q17 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q2 ∷
   re 68 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏丼丠丼乏") ∷
   rw 74 q2 ∷
   re 72 3 (ℓ "乓") ∷
   rw 71 q14 ∷
   rw 70 q18 ∷
   rw 69 q16 ∷
   re 69 1 (ℓ "乏乆乏") ∷
   rw 68 q1 ∷
   re 69 5 (ℓ "中") ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q1 ∷
   re 67 3 (ℓ "乓") ∷
   rw 68 q17 ∷
   rw 65 q17 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q2 ∷
   re 67 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丼丠丼乏") ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "乓") ∷
   rw 70 q14 ∷
   rw 69 q18 ∷
   rw 68 q16 ∷
   re 68 1 (ℓ "乏乆乏") ∷
   rw 67 q1 ∷
   re 68 5 (ℓ "中") ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q1 ∷
   re 66 3 (ℓ "乓") ∷
   rw 67 q17 ∷
   rw 64 q17 ∷
   re 66 1 (ℓ "乏乆乏") ∷
   rw 65 q2 ∷
   re 66 3 (ℓ "中") ∷
   re 66 1 (ℓ "乏丼丠丼乏") ∷
   rw 72 q2 ∷
   re 70 3 (ℓ "乓") ∷
   rw 69 q14 ∷
   rw 68 q18 ∷
   rw 67 q16 ∷
   re 67 1 (ℓ "乏乆乏") ∷
   rw 66 q1 ∷
   re 67 5 (ℓ "中") ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q1 ∷
   re 65 3 (ℓ "乓") ∷
   rw 66 q17 ∷
   rw 63 q22 ∷
   rw 64 q23 ∷
   rw 65 q22 ∷
   rw 62 q13 ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q2 ∷
   re 64 3 (ℓ "丱") ∷
   re 64 1 (ℓ "乏丼两丼乏") ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q14 ∷
   rw 66 q15 ∷
   rw 65 q16 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q1 ∷
   re 65 5 (ℓ "丱") ∷
   re 65 1 (ℓ "乏丫乏") ∷
   rw 67 q1 ∷
   re 63 3 (ℓ "乓") ∷
   rw 64 q13 ∷
   rw 61 q22 ∷
   rw 62 q23 ∷
   rw 63 q22 ∷
   rw 60 q13 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q2 ∷
   re 62 3 (ℓ "丱") ∷
   re 62 1 (ℓ "乏丼两丼乏") ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q14 ∷
   rw 64 q15 ∷
   rw 63 q16 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q1 ∷
   re 63 5 (ℓ "丱") ∷
   re 63 1 (ℓ "乏丫乏") ∷
   rw 65 q1 ∷
   re 61 3 (ℓ "乓") ∷
   rw 62 q13 ∷
   rw 63 q2 ∷
   rw 62 q19 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 63 q1 ∷
   rw 60 q19 ∷
   re 59 1 (ℓ "乏乃乏") ∷
   rw 61 q1 ∷
   rw 60 q20 ∷
   rw 59 q21 ∷
   rw 62 q2 ∷
   re 60 3 (ℓ "乓") ∷
   rw 61 q21 ∷
   rw 64 q2 ∷
   re 62 3 (ℓ "乐") ∷
   rw 63 q1 ∷
   rw 53 q24 ∷
   rw 91 q25 ∷
   rw⁻ 90 q26 ∷
   rw⁻ 89 q27 ∷
   rw⁻ 88 q27 ∷
   rw⁻ 87 q28 ∷
   rw⁻ 86 q27 ∷
   rw⁻ 85 q26 ∷
   rw 84 q29 ∷
   rw 83 q29 ∷
   rw 82 q30 ∷
   rw 81 q29 ∷
   rw 80 q30 ∷
   rw 79 q30 ∷
   re 78 1 (ℓ "乏乃乏") ∷
   rw⁻ 80 q31 ∷
   rw 79 q32 ∷
   rw⁻ 78 q31 ∷
   re 79 3 (ℓ "乓") ∷
   rw 77 q30 ∷
   rw 76 q30 ∷
   rw 75 q30 ∷
   rw 74 q30 ∷
   rw 73 q30 ∷
   rw 72 q30 ∷
   rw 71 q33 ∷
   rw 70 q29 ∷
   rw 69 q30 ∷
   rw 68 q30 ∷
   rw 67 q30 ∷
   rw 66 q33 ∷
   rw 65 q29 ∷
   rw 64 q33 ∷
   rw 63 q29 ∷
   re 62 1 (ℓ "乏乃乏") ∷
   rw⁻ 64 q31 ∷
   rw 63 q32 ∷
   rw⁻ 62 q31 ∷
   re 63 3 (ℓ "乓") ∷
   rw⁻ 61 q34 ∷
   rw⁻ 60 q34 ∷
   rw⁻ 59 q35 ∷
   rw⁻ 58 q34 ∷ []) Eq.refl
