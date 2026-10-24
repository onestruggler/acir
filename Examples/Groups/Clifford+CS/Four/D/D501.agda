{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D501 (W : Ws) where

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
  q2 = wE 20 W
  q3 : Eqn
  q3 = eqn (ℓ "丣义") (ℓ "义丣") (low-comm (CX₀₁) (CS))
  q4 : Eqn
  q4 = wE 49 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 352 W
  q7 : Eqn
  q7 = eqn (ℓ "丣乍") (ℓ "乍丣") (low-comm (CX₀₁) (CK₀₁))
  q8 : Eqn
  q8 = wE 357 W
  q9 : Eqn
  q9 = wE 1247 W
  q10 : Eqn
  q10 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = wE 1279 W
  q12 : Eqn
  q12 = eqn (ℓ "丌义") (ℓ "义丌") (low₁-comm (X) ((CS ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "丌乍") (ℓ "乍丌") (low₁-comm (X) ((CK₀₁ ↑)))
  q14 : Eqn
  q14 = wE 1244 W
  q15 : Eqn
  q15 = eqn (ℓ "丌且") (ℓ "且丌") (low₁-comm (X) ((S ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "丣且") (ℓ "且丣") (low-comm (CX₀₁) (S))
  q17 : Eqn
  q17 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q19 : Eqn
  q19 = wE 1276 W
  q20 : Eqn
  q20 = wE 1319 W
  q21 : Eqn
  q21 = wE 1320 W

-- Bar(SSSKSS;0,2->3) passes groups of WBar(SSKSKK;~0,1->3) part1: 500 steps
lem-Bar⟨SSSKSS02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part1 : ⟪ (ℓ "丌中中丱中丱丱丌丌丣丌中中中丱中中乁与乁与乏乏个乏丶乏丽丽乁与丽丽丽丽丽丽义义义义义义乍且义义义义义义义义义个义义义乍义义丌丣丌丽丽乁丽乁乁") ⟫ʷ ≈ ⟪ (ℓ "丌中中丱中丱丱丌丌丣丌乁与乁与丽丽丽乁与丽丽丽丽丽丽丌丣丌中中中丱中中丽丽乁丽乏为乏个乁义义义义义义乍且义义义义义义义义义个义义义乍义义") ⟫ʷ
lem-Bar⟨SSSKSS02-⟶3⟩-passes-groups-of-WBar⟨SSKSKK~01-⟶3⟩-part1 = derive (ℓ "丌中中丱中丱丱丌丌丣丌中中中丱中中乁与乁与乏乏个乏丶乏丽丽乁与丽丽丽丽丽丽义义义义义义乍且义义义义义义义义义个义义义乍义义丌丣丌丽丽乁丽乁乁") (ℓ "丌中中丱中丱丱丌丌丣丌乁与乁与丽丽丽乁与丽丽丽丽丽丽丌丣丌中中中丱中中丽丽乁丽乏为乏个乁义义义义义义乍且义义义义义义义义义个义义义乍义义")
  (re 22 3 (ℓ "丰") ∷
   re 22 1 (ℓ "乏丼丣丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "丽") ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q5 ∷
   re 23 5 (ℓ "丰") ∷
   re 23 1 (ℓ "乏个乏") ∷
   rw 25 q5 ∷
   re 21 3 (ℓ "丽") ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 22 q1 ∷
   re 23 3 (ℓ "丰") ∷
   re 23 1 (ℓ "乏丼丣丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "丽") ∷
   rw 26 q2 ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q5 ∷
   re 24 5 (ℓ "丰") ∷
   re 24 1 (ℓ "乏个乏") ∷
   rw 26 q5 ∷
   re 22 3 (ℓ "丽") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "丰") ∷
   re 24 1 (ℓ "乏丼丣丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "丽") ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   re 25 1 (ℓ "乏丶乏") ∷
   rw 24 q5 ∷
   re 25 5 (ℓ "丰") ∷
   re 25 1 (ℓ "乏个乏") ∷
   rw 27 q5 ∷
   re 23 3 (ℓ "丽") ∷
   re 25 1 (ℓ "乏为乏") ∷
   rw 24 q1 ∷
   re 25 3 (ℓ "丰") ∷
   re 25 1 (ℓ "乏丼丣丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "乁") ∷
   rw 28 q6 ∷
   rw 27 q7 ∷
   rw 26 q8 ∷
   re 26 1 (ℓ "乏为乏") ∷
   rw 25 q5 ∷
   re 26 5 (ℓ "丰") ∷
   re 26 1 (ℓ "乏个乏") ∷
   rw 28 q5 ∷
   re 24 3 (ℓ "乁") ∷
   rw 25 q9 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "丰") ∷
   re 27 1 (ℓ "乏丼丣丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "丽") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q5 ∷
   re 28 5 (ℓ "丰") ∷
   re 28 1 (ℓ "乏个乏") ∷
   rw 30 q5 ∷
   re 26 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "丰") ∷
   re 28 1 (ℓ "乏丼丣丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丽") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q5 ∷
   re 29 5 (ℓ "丰") ∷
   re 29 1 (ℓ "乏个乏") ∷
   rw 31 q5 ∷
   re 27 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 28 q1 ∷
   re 29 3 (ℓ "丰") ∷
   re 29 1 (ℓ "乏丼丣丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "丽") ∷
   rw 32 q2 ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q5 ∷
   re 30 5 (ℓ "丰") ∷
   re 30 1 (ℓ "乏个乏") ∷
   rw 32 q5 ∷
   re 28 3 (ℓ "丽") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "丰") ∷
   re 30 1 (ℓ "乏丼丣丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "丽") ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q5 ∷
   re 31 5 (ℓ "丰") ∷
   re 31 1 (ℓ "乏个乏") ∷
   rw 33 q5 ∷
   re 29 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q1 ∷
   re 31 3 (ℓ "丰") ∷
   re 31 1 (ℓ "乏丼丣丼乏") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "丽") ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q5 ∷
   re 32 5 (ℓ "丰") ∷
   re 32 1 (ℓ "乏个乏") ∷
   rw 34 q5 ∷
   re 30 3 (ℓ "丽") ∷
   re 32 1 (ℓ "乏丶乏") ∷
   rw 31 q1 ∷
   re 32 3 (ℓ "丰") ∷
   re 32 1 (ℓ "乏丼丣丼乏") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "丽") ∷
   rw 35 q2 ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q5 ∷
   re 33 5 (ℓ "丰") ∷
   re 33 1 (ℓ "乏个乏") ∷
   rw 35 q5 ∷
   re 31 3 (ℓ "丽") ∷
   rw 32 q1 ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 33 q5 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 32 q5 ∷
   re 29 1 (ℓ "乏丶乏") ∷
   rw 31 q5 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 30 q5 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 29 q5 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q5 ∷
   rw 25 q10 ∷
   re 24 1 (ℓ "乏为乏") ∷
   rw 26 q5 ∷
   re 23 1 (ℓ "乏丶乏") ∷
   rw 25 q5 ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 24 q5 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 23 q5 ∷
   rw 20 q10 ∷
   re 19 1 (ℓ "乏为乏") ∷
   rw 21 q5 ∷
   rw 18 q10 ∷
   re 17 1 (ℓ "乏为乏") ∷
   rw 19 q5 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q5 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q5 ∷
   re 14 1 (ℓ "乏丫乏") ∷
   rw 16 q5 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q5 ∷
   rw 12 q11 ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "乁") ∷
   rw⁻ 12 q10 ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乁") ∷
   rw⁻ 14 q10 ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "丽") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "丽") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "丽") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "乁") ∷
   rw⁻ 19 q10 ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "丽") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "丽") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "丽") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "丽") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "丽") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "丽") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "丱") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 32 q5 ∷
   rw⁻ 56 q12 ∷
   rw⁻ 57 q3 ∷
   rw⁻ 58 q12 ∷
   rw⁻ 55 q12 ∷
   rw⁻ 56 q3 ∷
   rw⁻ 57 q12 ∷
   rw⁻ 54 q13 ∷
   rw⁻ 55 q7 ∷
   rw⁻ 56 q13 ∷
   rw⁻ 53 q12 ∷
   rw⁻ 54 q3 ∷
   rw⁻ 55 q12 ∷
   rw⁻ 52 q12 ∷
   rw⁻ 53 q3 ∷
   rw⁻ 54 q12 ∷
   rw⁻ 51 q12 ∷
   rw⁻ 52 q3 ∷
   rw⁻ 53 q12 ∷
   rw 50 q14 ∷
   rw⁻ 49 q12 ∷
   rw⁻ 50 q3 ∷
   rw⁻ 51 q12 ∷
   rw⁻ 48 q12 ∷
   rw⁻ 49 q3 ∷
   rw⁻ 50 q12 ∷
   rw⁻ 47 q12 ∷
   rw⁻ 48 q3 ∷
   rw⁻ 49 q12 ∷
   rw⁻ 46 q12 ∷
   rw⁻ 47 q3 ∷
   rw⁻ 48 q12 ∷
   rw⁻ 45 q12 ∷
   rw⁻ 46 q3 ∷
   rw⁻ 47 q12 ∷
   rw⁻ 44 q12 ∷
   rw⁻ 45 q3 ∷
   rw⁻ 46 q12 ∷
   rw⁻ 43 q12 ∷
   rw⁻ 44 q3 ∷
   rw⁻ 45 q12 ∷
   rw⁻ 42 q12 ∷
   rw⁻ 43 q3 ∷
   rw⁻ 44 q12 ∷
   rw⁻ 41 q12 ∷
   rw⁻ 42 q3 ∷
   rw⁻ 43 q12 ∷
   rw⁻ 40 q15 ∷
   rw⁻ 41 q16 ∷
   rw⁻ 42 q15 ∷
   rw⁻ 39 q13 ∷
   rw⁻ 40 q7 ∷
   rw⁻ 41 q13 ∷
   rw⁻ 38 q12 ∷
   rw⁻ 39 q3 ∷
   rw⁻ 40 q12 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 38 q3 ∷
   rw⁻ 39 q12 ∷
   rw⁻ 36 q12 ∷
   rw⁻ 37 q3 ∷
   rw⁻ 38 q12 ∷
   rw⁻ 35 q12 ∷
   rw⁻ 36 q3 ∷
   rw⁻ 37 q12 ∷
   rw⁻ 34 q12 ∷
   rw⁻ 35 q3 ∷
   rw⁻ 36 q12 ∷
   rw⁻ 33 q12 ∷
   rw⁻ 34 q3 ∷
   rw⁻ 35 q12 ∷
   rw 32 q14 ∷
   rw 35 q1 ∷
   rw 34 q17 ∷
   rw 33 q18 ∷
   rw 32 q17 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q5 ∷
   re 29 1 (ℓ "乏丫乏") ∷
   rw 31 q5 ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q5 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q5 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q5 ∷
   rw 27 q19 ∷
   rw⁻ 26 q17 ∷
   rw⁻ 27 q18 ∷
   rw⁻ 28 q17 ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "丱") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 35 q5 ∷
   rw 54 q20 ∷
   re 54 1 (ℓ "乏丶乏") ∷
   rw 53 q1 ∷
   re 54 3 (ℓ "丰") ∷
   re 54 1 (ℓ "乏丼丣丼乏") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "丽") ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 55 q4 ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q5 ∷
   re 55 5 (ℓ "丰") ∷
   re 55 1 (ℓ "乏个乏") ∷
   rw 57 q5 ∷
   re 53 3 (ℓ "丽") ∷
   re 55 1 (ℓ "乏丶乏") ∷
   rw 54 q1 ∷
   re 55 3 (ℓ "丰") ∷
   re 55 1 (ℓ "乏丼丣丼乏") ∷
   rw 61 q1 ∷
   re 59 3 (ℓ "丽") ∷
   rw 58 q2 ∷
   rw 57 q3 ∷
   rw 56 q4 ∷
   re 56 1 (ℓ "乏丶乏") ∷
   rw 55 q5 ∷
   re 56 5 (ℓ "丰") ∷
   re 56 1 (ℓ "乏个乏") ∷
   rw 58 q5 ∷
   re 54 3 (ℓ "丽") ∷
   re 56 1 (ℓ "乏为乏") ∷
   rw 55 q1 ∷
   re 56 3 (ℓ "丰") ∷
   re 56 1 (ℓ "乏丼丣丼乏") ∷
   rw 62 q1 ∷
   re 60 3 (ℓ "乁") ∷
   rw 59 q6 ∷
   rw 58 q7 ∷
   rw 57 q8 ∷
   re 57 1 (ℓ "乏为乏") ∷
   rw 56 q5 ∷
   re 57 5 (ℓ "丰") ∷
   re 57 1 (ℓ "乏个乏") ∷
   rw 59 q5 ∷
   re 55 3 (ℓ "乁") ∷
   re 57 1 (ℓ "乏丶乏") ∷
   rw 56 q1 ∷
   re 57 3 (ℓ "丰") ∷
   re 57 1 (ℓ "乏丼丣丼乏") ∷
   rw 63 q1 ∷
   re 61 3 (ℓ "丽") ∷
   rw 60 q2 ∷
   rw 59 q3 ∷
   rw 58 q4 ∷
   re 58 1 (ℓ "乏丶乏") ∷
   rw 57 q5 ∷
   re 58 5 (ℓ "丰") ∷
   re 58 1 (ℓ "乏个乏") ∷
   rw 60 q5 ∷
   re 56 3 (ℓ "丽") ∷
   re 58 1 (ℓ "乏为乏") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "丰") ∷
   re 58 1 (ℓ "乏丼丣丼乏") ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乁") ∷
   rw 61 q6 ∷
   rw 60 q7 ∷
   rw 59 q8 ∷
   re 59 1 (ℓ "乏为乏") ∷
   rw 58 q5 ∷
   re 59 5 (ℓ "丰") ∷
   re 59 1 (ℓ "乏个乏") ∷
   rw 61 q5 ∷
   re 57 3 (ℓ "乁") ∷
   re 59 1 (ℓ "乏为乏") ∷
   rw 58 q1 ∷
   re 59 3 (ℓ "丰") ∷
   re 59 1 (ℓ "乏丼丣丼乏") ∷
   rw 65 q1 ∷
   re 63 3 (ℓ "乁") ∷
   rw 62 q6 ∷
   rw 61 q7 ∷
   rw 60 q8 ∷
   re 60 1 (ℓ "乏为乏") ∷
   rw 59 q5 ∷
   re 60 5 (ℓ "丰") ∷
   re 60 1 (ℓ "乏个乏") ∷
   rw 62 q5 ∷
   re 58 3 (ℓ "乁") ∷
   rw 36 q21 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q1 ∷
   re 36 3 (ℓ "丰") ∷
   re 36 1 (ℓ "乏丼丣丼乏") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "丽") ∷
   rw 39 q2 ∷
   rw 38 q3 ∷
   rw 37 q4 ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q5 ∷
   re 37 5 (ℓ "丰") ∷
   re 37 1 (ℓ "乏个乏") ∷
   rw 39 q5 ∷
   re 35 3 (ℓ "丽") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q1 ∷
   re 37 3 (ℓ "丰") ∷
   re 37 1 (ℓ "乏丼丣丼乏") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "丽") ∷
   rw 40 q2 ∷
   rw 39 q3 ∷
   rw 38 q4 ∷
   re 38 1 (ℓ "乏丶乏") ∷
   rw 37 q5 ∷
   re 38 5 (ℓ "丰") ∷
   re 38 1 (ℓ "乏个乏") ∷
   rw 40 q5 ∷
   re 36 3 (ℓ "丽") ∷
   re 38 1 (ℓ "乏为乏") ∷
   rw 37 q1 ∷
   re 38 3 (ℓ "丰") ∷
   re 38 1 (ℓ "乏丼丣丼乏") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "乁") ∷
   rw 41 q6 ∷
   rw 40 q7 ∷
   rw 39 q8 ∷
   re 39 1 (ℓ "乏为乏") ∷
   rw 38 q5 ∷
   re 39 5 (ℓ "丰") ∷
   re 39 1 (ℓ "乏个乏") ∷
   rw 41 q5 ∷
   re 37 3 (ℓ "乁") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q1 ∷
   re 39 3 (ℓ "丰") ∷
   re 39 1 (ℓ "乏丼丣丼乏") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "丽") ∷
   rw 42 q2 ∷
   rw 41 q3 ∷
   rw 40 q4 ∷
   re 40 1 (ℓ "乏丶乏") ∷
   rw 39 q5 ∷
   re 40 5 (ℓ "丰") ∷
   re 40 1 (ℓ "乏个乏") ∷
   rw 42 q5 ∷
   re 38 3 (ℓ "丽") ∷
   re 40 1 (ℓ "乏为乏") ∷
   rw 39 q1 ∷
   re 40 3 (ℓ "丰") ∷
   re 40 1 (ℓ "乏丼丣丼乏") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "乁") ∷
   rw 43 q6 ∷
   rw 42 q7 ∷
   rw 41 q8 ∷
   re 41 1 (ℓ "乏为乏") ∷
   rw 40 q5 ∷
   re 41 5 (ℓ "丰") ∷
   re 41 1 (ℓ "乏个乏") ∷
   rw 43 q5 ∷ []) Eq.refl
