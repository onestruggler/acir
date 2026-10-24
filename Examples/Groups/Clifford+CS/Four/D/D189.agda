{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D189 (W : Ws) where

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
  q1 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
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
  q7 = wE 3 W
  q8 : Eqn
  q8 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))
  q9 : Eqn
  q9 = wE 173 W
  q10 : Eqn
  q10 = wE 779 W
  q11 : Eqn
  q11 = wE 175 W
  q12 : Eqn
  q12 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q14 : Eqn
  q14 = wE 780 W
  q15 : Eqn
  q15 = wE 5 W
  q16 : Eqn
  q16 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q18 : Eqn
  q18 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q19 : Eqn
  q19 = wE 772 W
  q20 : Eqn
  q20 = wE 7 W
  q21 : Eqn
  q21 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 6 W
  q23 : Eqn
  q23 = wE 481 W
  q24 : Eqn
  q24 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q25 : Eqn
  q25 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q26 : Eqn
  q26 = wE 785 W
  q27 : Eqn
  q27 = wE 39 W
  q28 : Eqn
  q28 = wE 329 W
  q29 : Eqn
  q29 = wE 315 W
  q30 : Eqn
  q30 = wE 27 W
  q31 : Eqn
  q31 = wE 31 W
  q32 : Eqn
  q32 = wE 786 W
  q33 : Eqn
  q33 = wE 776 W
  q34 : Eqn
  q34 = wE 21 W
  q35 : Eqn
  q35 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q36 : Eqn
  q36 = wE 51 W

-- Bar(['S', 'S', 'K', 'S', 'K', 'K'];3,0->2) passes white iX via V2 conjugates 1 part2: 500 steps
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2 : ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丞乏乆乏丫丞丫丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷乐主丷丷丧丧丫丧丫丫丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'S'-'S'-'K'-'S'-'K'-'K'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part2 = derive (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧乐丧丧丫丧丞乏乆乏丫丞丫丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞义义乗义乗乗乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷乐主丷丷丧丧丫丧丫丫丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞")
  (re 49 3 (ℓ "乓") ∷
   rw 50 q1 ∷
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
   rw 49 q7 ∷
   re 50 5 (ℓ "中") ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q7 ∷
   re 48 3 (ℓ "乓") ∷
   rw 49 q2 ∷
   rw 46 q1 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q3 ∷
   re 48 3 (ℓ "丱") ∷
   re 48 1 (ℓ "乏丼两丼乏") ∷
   rw 54 q3 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q4 ∷
   rw 50 q8 ∷
   rw 49 q6 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q7 ∷
   re 49 5 (ℓ "丱") ∷
   re 49 1 (ℓ "乏丫乏") ∷
   rw 51 q7 ∷
   re 47 3 (ℓ "乓") ∷
   rw 48 q1 ∷
   rw 45 q2 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q3 ∷
   re 47 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   rw 48 q6 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q7 ∷
   re 48 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q7 ∷
   re 46 3 (ℓ "乓") ∷
   rw 47 q2 ∷
   rw 44 q2 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q3 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q3 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q4 ∷
   rw 48 q5 ∷
   rw 47 q6 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q7 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q7 ∷
   re 45 3 (ℓ "乓") ∷
   rw 46 q2 ∷
   rw 47 q3 ∷
   rw 46 q9 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 47 q7 ∷
   rw 44 q9 ∷
   re 43 1 (ℓ "乏乃乏") ∷
   rw 45 q7 ∷
   rw 44 q10 ∷
   rw 43 q11 ∷
   rw 46 q3 ∷
   re 44 3 (ℓ "乓") ∷
   rw 45 q11 ∷
   rw 48 q3 ∷
   re 46 3 (ℓ "乐") ∷
   rw 47 q7 ∷
   rw 42 q2 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q3 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q3 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q4 ∷
   rw 46 q5 ∷
   rw 45 q6 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q7 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q7 ∷
   re 43 3 (ℓ "乓") ∷
   rw 44 q2 ∷
   rw 41 q2 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q3 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q3 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q4 ∷
   rw 45 q5 ∷
   rw 44 q6 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q7 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q7 ∷
   re 42 3 (ℓ "乓") ∷
   rw 43 q2 ∷
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
   rw 42 q7 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q7 ∷
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
   rw 41 q7 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q7 ∷
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
   rw 40 q7 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q7 ∷
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
   rw 39 q7 ∷
   re 40 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q7 ∷
   re 38 3 (ℓ "乓") ∷
   rw 39 q2 ∷
   rw 36 q12 ∷
   rw 37 q13 ∷
   rw 38 q12 ∷
   rw 35 q1 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q3 ∷
   re 37 3 (ℓ "丱") ∷
   re 37 1 (ℓ "乏丼两丼乏") ∷
   rw 43 q3 ∷
   re 41 3 (ℓ "乓") ∷
   rw 40 q4 ∷
   rw 39 q8 ∷
   rw 38 q6 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q7 ∷
   re 38 5 (ℓ "丱") ∷
   re 38 1 (ℓ "乏丫乏") ∷
   rw 40 q7 ∷
   re 36 3 (ℓ "乓") ∷
   rw 37 q1 ∷
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
   rw 36 q7 ∷
   re 37 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q7 ∷
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
   rw 35 q7 ∷
   re 36 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q7 ∷
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
   rw 34 q7 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q7 ∷
   re 33 3 (ℓ "乓") ∷
   rw 34 q2 ∷
   rw 31 q12 ∷
   rw 32 q13 ∷
   rw 33 q12 ∷
   rw 30 q1 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q3 ∷
   re 32 3 (ℓ "丱") ∷
   re 32 1 (ℓ "乏丼两丼乏") ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "乓") ∷
   rw 35 q4 ∷
   rw 34 q8 ∷
   rw 33 q6 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q7 ∷
   re 33 5 (ℓ "丱") ∷
   re 33 1 (ℓ "乏丫乏") ∷
   rw 35 q7 ∷
   re 31 3 (ℓ "乓") ∷
   rw 32 q1 ∷
   rw 29 q12 ∷
   rw 30 q13 ∷
   rw 31 q12 ∷
   rw 28 q1 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q3 ∷
   re 30 3 (ℓ "丱") ∷
   re 30 1 (ℓ "乏丼两丼乏") ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q4 ∷
   rw 32 q8 ∷
   rw 31 q6 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q7 ∷
   re 31 5 (ℓ "丱") ∷
   re 31 1 (ℓ "乏丫乏") ∷
   rw 33 q7 ∷
   re 29 3 (ℓ "乓") ∷
   rw 30 q1 ∷
   rw 31 q3 ∷
   rw 30 q9 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 31 q7 ∷
   rw 28 q9 ∷
   re 27 1 (ℓ "乏乃乏") ∷
   rw 29 q7 ∷
   rw 28 q10 ∷
   rw 27 q11 ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "乓") ∷
   rw 29 q11 ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "乐") ∷
   rw 31 q7 ∷
   rw 21 q14 ∷
   rw 59 q15 ∷
   rw⁻ 58 q16 ∷
   rw⁻ 57 q17 ∷
   rw⁻ 56 q17 ∷
   rw⁻ 55 q18 ∷
   rw⁻ 54 q17 ∷
   rw⁻ 53 q16 ∷
   rw 52 q19 ∷
   rw 51 q19 ∷
   rw 50 q20 ∷
   rw 49 q19 ∷
   rw 48 q20 ∷
   rw 47 q20 ∷
   re 46 1 (ℓ "乏乃乏") ∷
   rw⁻ 48 q21 ∷
   rw 47 q22 ∷
   rw⁻ 46 q21 ∷
   re 47 3 (ℓ "乓") ∷
   rw 45 q20 ∷
   rw 44 q20 ∷
   rw 43 q20 ∷
   rw 42 q20 ∷
   rw 41 q20 ∷
   rw 40 q20 ∷
   rw 39 q23 ∷
   rw 38 q19 ∷
   rw 37 q20 ∷
   rw 36 q20 ∷
   rw 35 q20 ∷
   rw 34 q23 ∷
   rw 33 q19 ∷
   rw 32 q23 ∷
   rw 31 q19 ∷
   re 30 1 (ℓ "乏乃乏") ∷
   rw⁻ 32 q21 ∷
   rw 31 q22 ∷
   rw⁻ 30 q21 ∷
   re 31 3 (ℓ "乓") ∷
   rw⁻ 29 q24 ∷
   rw⁻ 28 q24 ∷
   rw⁻ 27 q25 ∷
   rw⁻ 26 q24 ∷
   rw⁻ 25 q25 ∷
   rw⁻ 24 q25 ∷
   rw 25 q26 ∷
   rw 24 q16 ∷
   rw 25 q17 ∷
   rw 26 q18 ∷
   rw 27 q17 ∷
   rw 28 q17 ∷
   rw 29 q16 ∷
   rw 30 q25 ∷
   rw 31 q25 ∷
   rw 32 q24 ∷
   rw 33 q25 ∷
   rw 34 q24 ∷
   rw 35 q24 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 36 q21 ∷
   rw 37 q27 ∷
   rw 38 q21 ∷
   re 36 3 (ℓ "乐") ∷
   rw 37 q28 ∷
   rw 38 q29 ∷
   rw 39 q28 ∷
   rw 40 q29 ∷
   rw 41 q30 ∷
   rw 42 q30 ∷
   rw 43 q30 ∷
   rw 44 q28 ∷
   rw 45 q29 ∷
   rw 46 q30 ∷
   rw 47 q30 ∷
   rw 48 q30 ∷
   rw 49 q30 ∷
   rw 50 q30 ∷
   rw 51 q30 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q21 ∷
   rw 53 q27 ∷
   rw 54 q21 ∷
   re 52 3 (ℓ "乐") ∷
   rw 53 q30 ∷
   rw 54 q30 ∷
   rw 55 q28 ∷
   rw 56 q30 ∷
   rw 57 q28 ∷
   rw 58 q28 ∷
   rw 59 q31 ∷
   rw 64 q15 ∷
   rw⁻ 63 q16 ∷
   rw⁻ 62 q25 ∷
   rw⁻ 61 q25 ∷
   rw⁻ 60 q25 ∷
   rw⁻ 59 q16 ∷
   rw 58 q19 ∷
   rw 57 q19 ∷
   rw 56 q20 ∷
   rw 55 q19 ∷
   rw 54 q20 ∷
   rw 53 q20 ∷
   re 52 1 (ℓ "乏乃乏") ∷
   rw⁻ 54 q21 ∷
   rw 53 q22 ∷
   rw⁻ 52 q21 ∷
   re 53 3 (ℓ "乓") ∷
   rw 51 q20 ∷
   rw 50 q20 ∷
   rw 49 q20 ∷
   rw 48 q20 ∷
   rw 47 q20 ∷
   rw 46 q20 ∷
   rw 45 q23 ∷
   rw 44 q19 ∷
   rw 43 q20 ∷
   rw 42 q20 ∷
   rw 41 q20 ∷
   rw 40 q23 ∷
   rw 39 q19 ∷
   rw 38 q23 ∷
   rw 37 q19 ∷
   re 36 1 (ℓ "乏乃乏") ∷
   rw⁻ 38 q21 ∷
   rw 37 q22 ∷
   rw⁻ 36 q21 ∷
   re 37 3 (ℓ "乓") ∷
   rw⁻ 35 q24 ∷
   rw⁻ 34 q24 ∷
   rw⁻ 33 q25 ∷
   rw⁻ 32 q24 ∷
   rw⁻ 31 q25 ∷
   rw⁻ 30 q25 ∷
   rw 31 q32 ∷
   rw 30 q16 ∷
   rw 31 q25 ∷
   rw 32 q25 ∷
   rw 33 q25 ∷
   rw 34 q16 ∷
   rw 35 q25 ∷
   rw 36 q25 ∷
   rw 37 q24 ∷
   rw 38 q25 ∷
   rw 39 q24 ∷
   rw 40 q24 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q21 ∷
   rw 42 q27 ∷
   rw 43 q21 ∷
   re 41 3 (ℓ "乐") ∷
   rw 42 q28 ∷
   rw 43 q29 ∷
   rw 44 q28 ∷
   rw 45 q29 ∷
   rw 46 q30 ∷
   rw 47 q30 ∷
   rw 48 q30 ∷
   rw 49 q28 ∷
   rw 50 q29 ∷
   rw 51 q30 ∷
   rw 52 q30 ∷
   rw 53 q30 ∷
   rw 54 q30 ∷
   rw 55 q30 ∷
   rw 56 q30 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q21 ∷
   rw 58 q27 ∷
   rw 59 q21 ∷
   re 57 3 (ℓ "乐") ∷
   rw 58 q30 ∷
   rw 59 q30 ∷
   rw 60 q28 ∷
   rw 61 q30 ∷
   rw 62 q28 ∷
   rw 63 q28 ∷
   rw 64 q31 ∷
   rw 58 q33 ∷
   re 57 1 (ℓ "乏丼丳丼乏") ∷
   rw 63 q3 ∷
   re 61 3 (ℓ "举") ∷
   rw 60 q34 ∷
   rw 59 q35 ∷
   rw 58 q36 ∷
   re 58 1 (ℓ "乏丷乏") ∷
   rw 57 q7 ∷
   re 58 5 (ℓ "乐") ∷ []) Eq.refl
