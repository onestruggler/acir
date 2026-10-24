{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D269 (W : Ws) where

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
  q1 = eqn (ℓ "丧丞") (ℓ "丞丧") (low₃-comm ((Swap ↑ • CS • Swap ↑)) (X))
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = wE 21 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q5 : Eqn
  q5 = wE 51 W
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 173 W
  q8 : Eqn
  q8 = wE 774 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = wE 855 W
  q11 : Eqn
  q11 = wE 777 W
  q12 : Eqn
  q12 = eqn (ℓ "丳乊") (ℓ "乊丳") (low-comm (CX₁₀) ((CS • CS • CS)))
  q13 : Eqn
  q13 = wE 353 W
  q14 : Eqn
  q14 = eqn (ℓ "丳乎") (ℓ "乎丳") (low-comm (CX₁₀) ((S • CK₀₁)))
  q15 : Eqn
  q15 = wE 358 W
  q16 : Eqn
  q16 = wE 856 W
  q17 : Eqn
  q17 = wE 857 W
  q18 : Eqn
  q18 = wE 113 W
  q19 : Eqn
  q19 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q20 : Eqn
  q20 = wE 114 W
  q21 : Eqn
  q21 = eqn (ℓ "丈丞") (ℓ "丞丈") (low₁-comm (S) ((X ↑ ↑)))
  q22 : Eqn
  q22 = eqn (ℓ "丈乓") (ℓ "乓丈") (low₁-comm (S) ((Swap ↑ • CX₁₀ • Swap ↑)))
  q23 : Eqn
  q23 = eqn (ℓ "丫丞") (ℓ "丞丫") (low₃-comm ((Swap ↑ • CK₀₁ • Swap ↑)) (X))
  q24 : Eqn
  q24 = eqn (ℓ "两乖") (ℓ "乖两") (low-comm (CK₀₁) (CX₁₀))

-- Bar(['K', 'i', 'K', 'i', 'S', 'S', 'S', 'K', 'i', 'S', 'S', 'S', 'S', 'S', 'S'];3,0->2) passes white iX via V2 conjugates 1 part1: 500 steps
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1 : ⟪ (ℓ "乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丞乏丷乏丧丞丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ ≈ ⟪ (ℓ "丞举丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丞乏乆中乏丞丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") ⟫ʷ
lem-Bar⟨'K'-'i'-'K'-'i'-'S'-'S'-'S'-'K'-'i'-'S'-'S'-'S'-'S'-'S'-'S'30-⟶2⟩-passes-white-iX-via-V2-conjugates-1-part1 = derive (ℓ "乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丞乏丷乏丧丞丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丧丫丈丧丧丧丧丧丧丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞") (ℓ "丞举丞丷主丷丷乗业乗业义义义乗业义义义义义义乐丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丈丈丈丫丈丧丧丧丧丧丧丧丧丧丈丈丈丫丈丈丈丈丫丈乐丫丈丫丈丧丧丞乏乆中乏丞丫丈丧丧丧丧丧丧丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞义义义丞丷主丷丷丞乓丞丷丷丷丷丷丷丏主丷丷丷丞乓丞丞乊乘乊乊丞丞乊乊乊丞")
  (re 33 3 (ℓ "举") ∷
   rw 34 q1 ∷
   rw 31 q1 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 32 q2 ∷
   re 33 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "举") ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   re 34 1 (ℓ "乏丷乏") ∷
   rw 33 q6 ∷
   re 34 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q6 ∷
   re 32 3 (ℓ "举") ∷
   rw 33 q1 ∷
   rw 30 q1 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q2 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "举") ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   re 33 1 (ℓ "乏丷乏") ∷
   rw 32 q6 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q6 ∷
   re 31 3 (ℓ "举") ∷
   rw 32 q1 ∷
   rw 29 q1 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q2 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "举") ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q6 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q6 ∷
   re 30 3 (ℓ "举") ∷
   rw 31 q1 ∷
   rw 28 q1 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q6 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q6 ∷
   re 29 3 (ℓ "举") ∷
   rw 30 q1 ∷
   rw 27 q1 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q6 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q6 ∷
   re 28 3 (ℓ "举") ∷
   rw 29 q1 ∷
   rw 26 q1 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q6 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 27 3 (ℓ "举") ∷
   rw 28 q1 ∷
   rw 25 q1 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q6 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q6 ∷
   re 26 3 (ℓ "举") ∷
   rw 27 q1 ∷
   rw 24 q1 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q6 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 25 3 (ℓ "举") ∷
   rw 26 q1 ∷
   rw 23 q1 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q6 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 24 3 (ℓ "举") ∷
   rw 25 q1 ∷
   rw 22 q1 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q6 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q6 ∷
   re 23 3 (ℓ "举") ∷
   rw 24 q1 ∷
   rw 21 q1 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q6 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q6 ∷
   re 22 3 (ℓ "举") ∷
   rw 23 q1 ∷
   rw 20 q1 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q6 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 21 3 (ℓ "举") ∷
   rw 22 q1 ∷
   rw 19 q1 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 20 3 (ℓ "举") ∷
   rw 21 q1 ∷
   rw 18 q1 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 19 3 (ℓ "举") ∷
   rw 20 q1 ∷
   rw 17 q1 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 18 3 (ℓ "举") ∷
   rw 19 q1 ∷
   rw 16 q1 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 17 3 (ℓ "举") ∷
   rw 18 q1 ∷
   rw 19 q2 ∷
   rw 18 q7 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 19 q6 ∷
   rw 16 q7 ∷
   re 15 1 (ℓ "乏乃乏") ∷
   rw 17 q6 ∷
   rw 16 q8 ∷
   rw 15 q9 ∷
   rw 18 q2 ∷
   re 16 3 (ℓ "举") ∷
   rw 17 q9 ∷
   rw 20 q2 ∷
   re 18 3 (ℓ "乐") ∷
   rw 19 q6 ∷
   rw 0 q10 ∷
   rw 62 q11 ∷
   re 61 1 (ℓ "乏丼丳丼乏") ∷
   rw 67 q2 ∷
   re 65 3 (ℓ "举") ∷
   rw 64 q3 ∷
   rw 63 q12 ∷
   rw 62 q5 ∷
   re 62 1 (ℓ "乏丷乏") ∷
   rw 61 q6 ∷
   re 62 5 (ℓ "乐") ∷
   re 62 1 (ℓ "乏丼丳丼乏") ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "乂") ∷
   rw 65 q13 ∷
   rw 64 q14 ∷
   rw 63 q15 ∷
   re 63 1 (ℓ "乏主乏") ∷
   rw 62 q6 ∷
   re 63 5 (ℓ "乐") ∷
   re 63 1 (ℓ "乏丼丳丼乏") ∷
   rw 69 q2 ∷
   re 67 3 (ℓ "举") ∷
   rw 66 q3 ∷
   rw 65 q12 ∷
   rw 64 q5 ∷
   re 64 1 (ℓ "乏丷乏") ∷
   rw 63 q6 ∷
   re 64 5 (ℓ "乐") ∷
   re 64 1 (ℓ "乏丼丳丼乏") ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "举") ∷
   rw 67 q3 ∷
   rw 66 q12 ∷
   rw 65 q5 ∷
   re 65 1 (ℓ "乏丷乏") ∷
   rw 64 q6 ∷
   re 65 5 (ℓ "乐") ∷
   rw 19 q16 ∷
   re 18 1 (ℓ "乏丼丳丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q3 ∷
   rw 20 q12 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q6 ∷
   re 19 5 (ℓ "乐") ∷
   re 19 1 (ℓ "乏丼丳丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "乂") ∷
   rw 22 q13 ∷
   rw 21 q14 ∷
   rw 20 q15 ∷
   re 20 1 (ℓ "乏主乏") ∷
   rw 19 q6 ∷
   re 20 5 (ℓ "乐") ∷
   re 20 1 (ℓ "乏丼丳丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q3 ∷
   rw 22 q12 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q6 ∷
   re 21 5 (ℓ "乐") ∷
   re 21 1 (ℓ "乏丼丳丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q3 ∷
   rw 23 q12 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q6 ∷
   re 22 5 (ℓ "乐") ∷
   rw 3 q17 ∷
   rw 80 q1 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q2 ∷
   re 82 3 (ℓ "中") ∷
   re 82 1 (ℓ "乏丼丠丼乏") ∷
   rw 88 q2 ∷
   re 86 3 (ℓ "乓") ∷
   rw 85 q18 ∷
   rw 84 q19 ∷
   rw 83 q20 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 82 q6 ∷
   re 83 5 (ℓ "中") ∷
   re 83 1 (ℓ "乏丧乏") ∷
   rw 85 q6 ∷
   re 81 3 (ℓ "乓") ∷
   rw 82 q1 ∷
   rw 79 q1 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q2 ∷
   re 81 3 (ℓ "中") ∷
   re 81 1 (ℓ "乏丼丠丼乏") ∷
   rw 87 q2 ∷
   re 85 3 (ℓ "乓") ∷
   rw 84 q18 ∷
   rw 83 q19 ∷
   rw 82 q20 ∷
   re 82 1 (ℓ "乏乆乏") ∷
   rw 81 q6 ∷
   re 82 5 (ℓ "中") ∷
   re 82 1 (ℓ "乏丧乏") ∷
   rw 84 q6 ∷
   re 80 3 (ℓ "乓") ∷
   rw 81 q1 ∷
   rw 78 q1 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q2 ∷
   re 80 3 (ℓ "中") ∷
   re 80 1 (ℓ "乏丼丠丼乏") ∷
   rw 86 q2 ∷
   re 84 3 (ℓ "乓") ∷
   rw 83 q18 ∷
   rw 82 q19 ∷
   rw 81 q20 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 80 q6 ∷
   re 81 5 (ℓ "中") ∷
   re 81 1 (ℓ "乏丧乏") ∷
   rw 83 q6 ∷
   re 79 3 (ℓ "乓") ∷
   rw 80 q1 ∷
   rw 77 q1 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q2 ∷
   re 79 3 (ℓ "中") ∷
   re 79 1 (ℓ "乏丼丠丼乏") ∷
   rw 85 q2 ∷
   re 83 3 (ℓ "乓") ∷
   rw 82 q18 ∷
   rw 81 q19 ∷
   rw 80 q20 ∷
   re 80 1 (ℓ "乏乆乏") ∷
   rw 79 q6 ∷
   re 80 5 (ℓ "中") ∷
   re 80 1 (ℓ "乏丧乏") ∷
   rw 82 q6 ∷
   re 78 3 (ℓ "乓") ∷
   rw 79 q1 ∷
   rw 76 q1 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q2 ∷
   re 78 3 (ℓ "中") ∷
   re 78 1 (ℓ "乏丼丠丼乏") ∷
   rw 84 q2 ∷
   re 82 3 (ℓ "乓") ∷
   rw 81 q18 ∷
   rw 80 q19 ∷
   rw 79 q20 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 78 q6 ∷
   re 79 5 (ℓ "中") ∷
   re 79 1 (ℓ "乏丧乏") ∷
   rw 81 q6 ∷
   re 77 3 (ℓ "乓") ∷
   rw 78 q1 ∷
   rw 75 q1 ∷
   re 77 1 (ℓ "乏乆乏") ∷
   rw 76 q2 ∷
   re 77 3 (ℓ "中") ∷
   re 77 1 (ℓ "乏丼丠丼乏") ∷
   rw 83 q2 ∷
   re 81 3 (ℓ "乓") ∷
   rw 80 q18 ∷
   rw 79 q19 ∷
   rw 78 q20 ∷
   re 78 1 (ℓ "乏乆乏") ∷
   rw 77 q6 ∷
   re 78 5 (ℓ "中") ∷
   re 78 1 (ℓ "乏丧乏") ∷
   rw 80 q6 ∷
   re 76 3 (ℓ "乓") ∷
   rw 77 q1 ∷
   rw 74 q21 ∷
   rw 75 q22 ∷
   rw 76 q21 ∷
   rw 73 q23 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q2 ∷
   re 75 3 (ℓ "丱") ∷
   re 75 1 (ℓ "乏丼两丼乏") ∷
   rw 81 q2 ∷
   re 79 3 (ℓ "乓") ∷
   rw 78 q18 ∷
   rw 77 q24 ∷
   rw 76 q20 ∷
   re 76 1 (ℓ "乏乆乏") ∷
   rw 75 q6 ∷
   re 76 5 (ℓ "丱") ∷
   re 76 1 (ℓ "乏丫乏") ∷
   rw 78 q6 ∷
   re 74 3 (ℓ "乓") ∷
   rw 75 q23 ∷
   rw 72 q1 ∷
   re 74 1 (ℓ "乏乆乏") ∷
   rw 73 q2 ∷
   re 74 3 (ℓ "中") ∷
   re 74 1 (ℓ "乏丼丠丼乏") ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "乓") ∷
   rw 77 q18 ∷
   rw 76 q19 ∷
   rw 75 q20 ∷
   re 75 1 (ℓ "乏乆乏") ∷
   rw 74 q6 ∷
   re 75 5 (ℓ "中") ∷ []) Eq.refl
