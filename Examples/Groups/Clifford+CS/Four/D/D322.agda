{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D322 (W : Ws) where

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
  q2 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 464 W
  q8 : Eqn
  q8 = wE 945 W
  q9 : Eqn
  q9 = wE 151 W
  q10 : Eqn
  q10 = wE 880 W
  q11 : Eqn
  q11 = wE 157 W
  q12 : Eqn
  q12 = eqn (ℓ "丠乌") (ℓ "乌丠") (low-comm (CS) (CX₀₁))
  q13 : Eqn
  q13 = wE 158 W
  q14 : Eqn
  q14 = wE 879 W
  q15 : Eqn
  q15 = eqn (ℓ "临乌") (ℓ "乌临") (low-comm (CK₁₀) (CX₀₁))
  q16 : Eqn
  q16 = wE 881 W

-- Bar(SSSKSS;1,3->0) passes groups of WBar(KiKiSSSKiSSSSSS;~1,2->0) part0: 500 steps
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part0 : ⟪ (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丠丠丠临丠丠乀中中中中中中乑业中中丒乏乏丹丒中中中中中中中乀中中中乑中中丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ
lem-Bar⟨SSSKSS13-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~12-⟶0⟩-part0 = derive (ℓ "丠丠丠临丠丠乀中中中中中中乑业中中中中中中中中中乀中中中乑中中丒临与临与丠丠丠临与丠丠丠丠丠丠丒丒丹丒丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "丒临与临与丠丠丠临与丠丠丠丠丠丠丒丠丠丠临丠丠乀中中中中中中乑业中中丒乏乏丹丒中中中中中中中乀中中中乑中中丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丒丹丒乄且乄且丧丧丧乄且丧丧丧丧丧丧")
  (rw 48 q1 ∷
   rw 47 q2 ∷
   rw 46 q3 ∷
   rw 45 q3 ∷
   rw 44 q3 ∷
   rw 43 q3 ∷
   rw 42 q3 ∷
   rw 41 q3 ∷
   rw 40 q4 ∷
   rw 39 q5 ∷
   rw 38 q3 ∷
   rw 37 q3 ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   rw 31 q2 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q6 ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q6 ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw 30 q6 ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q6 ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q6 ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q6 ∷
   re 24 1 (ℓ "乏丹乏") ∷
   rw 26 q6 ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q6 ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q6 ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q6 ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q6 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q6 ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q6 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q6 ∷
   re 16 1 (ℓ "乏丧乏") ∷
   rw 18 q6 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q6 ∷
   rw 14 q7 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw 15 q6 ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q6 ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q6 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q6 ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   re 6 1 (ℓ "乏丹乏") ∷
   rw 8 q6 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw 3 q5 ∷
   rw 2 q3 ∷
   rw 1 q3 ∷
   rw 0 q3 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q5 ∷
   rw⁻ 2 q4 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q4 ∷
   rw⁻ 5 q3 ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q3 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q4 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q3 ∷
   rw⁻ 12 q3 ∷
   rw⁻ 13 q3 ∷
   rw⁻ 14 q3 ∷
   rw⁻ 15 q3 ∷
   rw⁻ 16 q2 ∷
   rw⁻ 17 q3 ∷
   rw⁻ 18 q3 ∷
   rw⁻ 19 q3 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q3 ∷
   rw⁻ 22 q3 ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乀") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "中") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "中") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "中") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乑") ∷
   rw 31 q9 ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "乀") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "乑") ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q6 ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q6 ∷
   rw 48 q10 ∷
   rw⁻ 47 q2 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "中") ∷
   rw 49 q6 ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "乀") ∷
   rw 51 q11 ∷
   rw 50 q12 ∷
   rw 49 q13 ∷
   re 49 1 (ℓ "乏丹乏") ∷
   rw 48 q6 ∷
   re 49 5 (ℓ "中") ∷
   rw 51 q1 ∷
   rw 50 q2 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q6 ∷
   rw 50 q10 ∷
   rw⁻ 49 q2 ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "中") ∷
   rw 51 q6 ∷
   rw 48 q1 ∷
   rw 47 q2 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q6 ∷
   rw 47 q10 ∷
   rw⁻ 46 q2 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q6 ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "乀") ∷
   rw 50 q11 ∷
   rw 49 q12 ∷
   rw 48 q13 ∷
   re 48 1 (ℓ "乏丹乏") ∷
   rw 47 q6 ∷
   re 48 5 (ℓ "中") ∷
   rw 50 q1 ∷
   rw 49 q2 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q6 ∷
   rw 49 q10 ∷
   rw⁻ 48 q2 ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "中") ∷
   rw 50 q6 ∷
   rw 47 q1 ∷
   rw 46 q2 ∷
   re 45 1 (ℓ "乏乄乏") ∷
   rw 47 q6 ∷
   rw 46 q14 ∷
   rw⁻ 45 q2 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "乑") ∷
   rw 47 q6 ∷
   re 46 1 (ℓ "乏丼临丼乏") ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "乀") ∷
   rw 49 q11 ∷
   rw 48 q15 ∷
   rw 47 q13 ∷
   re 47 1 (ℓ "乏丹乏") ∷
   rw 46 q6 ∷
   re 47 5 (ℓ "乑") ∷
   rw 49 q1 ∷
   rw 48 q2 ∷
   re 47 1 (ℓ "乏乄乏") ∷
   rw 49 q6 ∷
   rw 48 q14 ∷
   rw⁻ 47 q2 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乑") ∷
   rw 49 q6 ∷
   rw 46 q1 ∷
   rw 45 q2 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q6 ∷
   rw 45 q10 ∷
   rw⁻ 44 q2 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q6 ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q1 ∷
   re 49 3 (ℓ "乀") ∷
   rw 48 q11 ∷
   rw 47 q12 ∷
   rw 46 q13 ∷
   re 46 1 (ℓ "乏丹乏") ∷
   rw 45 q6 ∷
   re 46 5 (ℓ "中") ∷
   rw 48 q1 ∷
   rw 47 q2 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q6 ∷
   rw 47 q10 ∷
   rw⁻ 46 q2 ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "中") ∷
   rw 48 q6 ∷
   rw 45 q1 ∷
   rw 44 q2 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q6 ∷
   rw 44 q10 ∷
   rw⁻ 43 q2 ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q6 ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乀") ∷
   rw 47 q11 ∷
   rw 46 q12 ∷
   rw 45 q13 ∷
   re 45 1 (ℓ "乏丹乏") ∷
   rw 44 q6 ∷
   re 45 5 (ℓ "中") ∷
   rw 47 q1 ∷
   rw 46 q2 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q6 ∷
   rw 46 q10 ∷
   rw⁻ 45 q2 ∷
   rw 48 q1 ∷
   re 46 3 (ℓ "中") ∷
   rw 47 q6 ∷
   rw 44 q1 ∷
   rw 43 q2 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q6 ∷
   rw 43 q10 ∷
   rw⁻ 42 q2 ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q6 ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q1 ∷
   re 47 3 (ℓ "乀") ∷
   rw 46 q11 ∷
   rw 45 q12 ∷
   rw 44 q13 ∷
   re 44 1 (ℓ "乏丹乏") ∷
   rw 43 q6 ∷
   re 44 5 (ℓ "中") ∷
   rw 46 q1 ∷
   rw 45 q2 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q6 ∷
   rw 45 q10 ∷
   rw⁻ 44 q2 ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "中") ∷
   rw 46 q6 ∷
   rw 41 q16 ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q6 ∷
   rw 41 q10 ∷
   rw⁻ 40 q2 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q6 ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q1 ∷
   re 45 3 (ℓ "乀") ∷
   rw 44 q11 ∷
   rw 43 q12 ∷
   rw 42 q13 ∷
   re 42 1 (ℓ "乏丹乏") ∷
   rw 41 q6 ∷
   re 42 5 (ℓ "中") ∷
   rw 44 q1 ∷
   rw 43 q2 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q6 ∷
   rw 43 q10 ∷
   rw⁻ 42 q2 ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 44 q6 ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q6 ∷
   rw 40 q10 ∷
   rw⁻ 39 q2 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q6 ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "乀") ∷
   rw 43 q11 ∷
   rw 42 q12 ∷
   rw 41 q13 ∷
   re 41 1 (ℓ "乏丹乏") ∷
   rw 40 q6 ∷
   re 41 5 (ℓ "中") ∷
   rw 43 q1 ∷
   rw 42 q2 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q6 ∷
   rw 42 q10 ∷
   rw⁻ 41 q2 ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 43 q6 ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q6 ∷
   rw 39 q10 ∷
   rw⁻ 38 q2 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q6 ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "乀") ∷
   rw 42 q11 ∷
   rw 41 q12 ∷
   rw 40 q13 ∷
   re 40 1 (ℓ "乏丹乏") ∷
   rw 39 q6 ∷
   re 40 5 (ℓ "中") ∷
   rw 42 q1 ∷
   rw 41 q2 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q6 ∷
   rw 41 q10 ∷
   rw⁻ 40 q2 ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "中") ∷
   rw 42 q6 ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q6 ∷
   rw 38 q10 ∷
   rw⁻ 37 q2 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q6 ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "乀") ∷
   rw 41 q11 ∷
   rw 40 q12 ∷
   rw 39 q13 ∷
   re 39 1 (ℓ "乏丹乏") ∷
   rw 38 q6 ∷
   re 39 5 (ℓ "中") ∷
   rw 41 q1 ∷
   rw 40 q2 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q6 ∷
   rw 40 q10 ∷
   rw⁻ 39 q2 ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "中") ∷
   rw 41 q6 ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q6 ∷
   rw 37 q10 ∷
   rw⁻ 36 q2 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q6 ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q1 ∷
   re 41 3 (ℓ "乀") ∷
   rw 40 q11 ∷
   rw 39 q12 ∷
   rw 38 q13 ∷
   re 38 1 (ℓ "乏丹乏") ∷
   rw 37 q6 ∷
   re 38 5 (ℓ "中") ∷
   rw 40 q1 ∷
   rw 39 q2 ∷
   re 38 1 (ℓ "乏丧乏") ∷
   rw 40 q6 ∷
   rw 39 q10 ∷
   rw⁻ 38 q2 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "中") ∷
   rw 40 q6 ∷
   rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q6 ∷
   rw 36 q10 ∷
   rw⁻ 35 q2 ∷
   rw 38 q1 ∷
   re 36 3 (ℓ "中") ∷
   rw 37 q6 ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q1 ∷
   re 40 3 (ℓ "乀") ∷
   rw 39 q11 ∷
   rw 38 q12 ∷
   rw 37 q13 ∷
   re 37 1 (ℓ "乏丹乏") ∷
   rw 36 q6 ∷
   re 37 5 (ℓ "中") ∷
   rw 39 q1 ∷
   rw 38 q2 ∷
   re 37 1 (ℓ "乏丧乏") ∷
   rw 39 q6 ∷
   rw 38 q10 ∷
   rw⁻ 37 q2 ∷
   rw 40 q1 ∷
   re 38 3 (ℓ "中") ∷
   rw 39 q6 ∷
   rw 36 q1 ∷
   rw 35 q2 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q6 ∷
   rw 35 q10 ∷
   rw⁻ 34 q2 ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "中") ∷
   rw 36 q6 ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "乀") ∷
   rw 38 q11 ∷
   rw 37 q12 ∷
   rw 36 q13 ∷
   re 36 1 (ℓ "乏丹乏") ∷
   rw 35 q6 ∷
   re 36 5 (ℓ "中") ∷
   rw 38 q1 ∷
   rw 37 q2 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q6 ∷
   rw 37 q10 ∷
   rw⁻ 36 q2 ∷
   rw 39 q1 ∷
   re 37 3 (ℓ "中") ∷
   rw 38 q6 ∷
   rw 35 q1 ∷ []) Eq.refl
