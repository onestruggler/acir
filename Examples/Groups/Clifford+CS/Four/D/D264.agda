{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D264 (W : Ws) where

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
  q1 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q2 : Eqn
  q2 = wE 78 W
  q3 : Eqn
  q3 = wE 13 W
  q4 : Eqn
  q4 = wE 762 W
  q5 : Eqn
  q5 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q6 : Eqn
  q6 = wE 5 W
  q7 : Eqn
  q7 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 140 W
  q9 : Eqn
  q9 = wE 7 W
  q10 : Eqn
  q10 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q11 : Eqn
  q11 = wE 852 W
  q12 : Eqn
  q12 = wE 27 W
  q13 : Eqn
  q13 = wE 142 W
  q14 : Eqn
  q14 = wE 31 W
  q15 : Eqn
  q15 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q17 : Eqn
  q17 = wE 537 W
  q18 : Eqn
  q18 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q19 : Eqn
  q19 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q20 : Eqn
  q20 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q21 : Eqn
  q21 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q22 : Eqn
  q22 = wE 538 W
  q23 : Eqn
  q23 = wE 617 W
  q24 : Eqn
  q24 = wE 618 W

-- Bar(SSKSKK;3,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~3,2->0) part1: 500 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part1 : ⟪ (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞中中乑中乑乑丧丧丧丧丧丧丧丧丧丧丧丧丧丼乖丠丼丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丞乖丞中中乑中乑乑乄且乄且丧丧丧乄且丧丧丧丧丧乓丼丠丼临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part1 = derive (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞中中乑中乑乑丧丧丧丧丧丧丧丧丧丧丧丧丧丼乖丠丼丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丞乖丞中中乑中乑乑乄且乄且丧丧丧乄且丧丧丧丧丧乓丼丠丼临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw⁻ 40 q1 ∷
   rw 41 q2 ∷
   re 39 3 (ℓ "丧") ∷
   re 41 1 (ℓ "丼丠丼") ∷
   rw 40 q3 ∷
   rw⁻ 41 q1 ∷
   rw 42 q2 ∷
   re 40 3 (ℓ "丧") ∷
   re 42 1 (ℓ "丼丠丼") ∷
   rw 41 q3 ∷
   rw⁻ 42 q1 ∷
   rw 43 q2 ∷
   re 41 3 (ℓ "丧") ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q3 ∷
   rw⁻ 43 q1 ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "丧") ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 43 q3 ∷
   rw⁻ 44 q1 ∷
   rw 45 q2 ∷
   re 43 3 (ℓ "丧") ∷
   rw 44 q4 ∷
   rw 45 q4 ∷
   rw 46 q4 ∷
   re 48 1 (ℓ "丼临丼") ∷
   rw 47 q3 ∷
   rw⁻ 48 q5 ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "乄") ∷
   rw 48 q4 ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 49 q3 ∷
   rw⁻ 50 q1 ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "丧") ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 50 q3 ∷
   rw⁻ 51 q1 ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "丧") ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q3 ∷
   rw⁻ 52 q1 ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "丧") ∷
   re 53 1 (ℓ "丼丠丼") ∷
   rw 52 q3 ∷
   rw⁻ 53 q1 ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "丧") ∷
   re 54 1 (ℓ "丼丠丼") ∷
   rw 53 q3 ∷
   rw⁻ 54 q1 ∷
   rw 55 q2 ∷
   re 53 3 (ℓ "丧") ∷
   re 55 1 (ℓ "丼丠丼") ∷
   rw 54 q3 ∷
   rw⁻ 55 q1 ∷
   rw 56 q2 ∷
   re 54 3 (ℓ "丧") ∷
   re 56 1 (ℓ "丼丠丼") ∷
   rw 55 q3 ∷
   rw⁻ 56 q1 ∷
   rw 57 q2 ∷
   re 55 3 (ℓ "丧") ∷
   re 57 1 (ℓ "丼丠丼") ∷
   rw 56 q3 ∷
   rw⁻ 57 q1 ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "丧") ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 57 q3 ∷
   rw⁻ 58 q1 ∷
   rw 59 q2 ∷
   re 57 3 (ℓ "丧") ∷
   rw 58 q4 ∷
   rw 59 q4 ∷
   rw 60 q4 ∷
   re 62 1 (ℓ "丼临丼") ∷
   rw 61 q3 ∷
   rw⁻ 62 q5 ∷
   rw 63 q2 ∷
   re 61 3 (ℓ "乄") ∷
   rw 62 q4 ∷
   rw 63 q4 ∷
   rw 64 q4 ∷
   rw 65 q4 ∷
   re 67 1 (ℓ "丼临丼") ∷
   rw 66 q3 ∷
   rw⁻ 67 q5 ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "乄") ∷
   rw 67 q4 ∷
   rw 68 q6 ∷
   rw⁻ 67 q7 ∷
   rw 66 q8 ∷
   rw⁻ 65 q7 ∷
   rw⁻ 64 q7 ∷
   rw⁻ 63 q7 ∷
   rw⁻ 62 q7 ∷
   rw 61 q8 ∷
   rw⁻ 60 q7 ∷
   rw⁻ 59 q7 ∷
   rw⁻ 58 q7 ∷
   rw 57 q9 ∷
   rw 56 q9 ∷
   rw 55 q9 ∷
   rw 54 q9 ∷
   rw 53 q9 ∷
   rw 52 q9 ∷
   rw 51 q9 ∷
   rw 50 q9 ∷
   rw 49 q9 ∷
   rw⁻ 48 q7 ∷
   rw 47 q8 ∷
   rw⁻ 46 q7 ∷
   rw⁻ 45 q7 ∷
   rw⁻ 44 q7 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q9 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   rw 35 q9 ∷
   rw 34 q9 ∷
   rw 33 q9 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 26 q9 ∷
   re 25 1 (ℓ "乏乄乏") ∷
   rw⁻ 27 q10 ∷
   rw 26 q8 ∷
   rw⁻ 25 q10 ∷
   re 26 3 (ℓ "乔") ∷
   re 24 1 (ℓ "乏乄乏") ∷
   rw⁻ 26 q10 ∷
   rw 25 q8 ∷
   rw⁻ 24 q10 ∷
   re 25 3 (ℓ "乔") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw⁻ 25 q10 ∷
   rw 24 q9 ∷
   rw⁻ 23 q10 ∷
   re 24 3 (ℓ "丽") ∷
   re 22 1 (ℓ "乏乄乏") ∷
   rw⁻ 24 q10 ∷
   rw 23 q8 ∷
   rw⁻ 22 q10 ∷
   re 23 3 (ℓ "乔") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw⁻ 23 q10 ∷
   rw 22 q9 ∷
   rw⁻ 21 q10 ∷
   re 22 3 (ℓ "丽") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q10 ∷
   rw 21 q9 ∷
   rw⁻ 20 q10 ∷
   re 21 3 (ℓ "丽") ∷
   rw 21 q11 ∷
   rw 20 q12 ∷
   rw 21 q12 ∷
   rw 22 q12 ∷
   rw 23 q12 ∷
   rw 24 q12 ∷
   rw 25 q12 ∷
   rw 26 q12 ∷
   rw 27 q12 ∷
   rw 28 q12 ∷
   rw 29 q12 ∷
   rw 30 q12 ∷
   rw 31 q12 ∷
   rw 32 q12 ∷
   rw 33 q12 ∷
   rw 34 q12 ∷
   rw 35 q12 ∷
   rw 36 q12 ∷
   rw 37 q12 ∷
   rw 38 q7 ∷
   rw 39 q7 ∷
   rw 40 q7 ∷
   rw 41 q13 ∷
   rw 42 q7 ∷
   rw 43 q12 ∷
   rw 44 q12 ∷
   rw 45 q12 ∷
   rw 46 q12 ∷
   rw 47 q12 ∷
   rw 48 q12 ∷
   rw 49 q12 ∷
   rw 50 q12 ∷
   rw 51 q12 ∷
   rw 52 q7 ∷
   rw 53 q7 ∷
   rw 54 q7 ∷
   rw 55 q13 ∷
   rw 56 q7 ∷
   rw 57 q7 ∷
   rw 58 q7 ∷
   rw 59 q7 ∷
   rw 60 q13 ∷
   rw 61 q7 ∷
   re 63 1 (ℓ "乏丶乏") ∷
   rw 62 q10 ∷
   rw 63 q12 ∷
   rw 64 q10 ∷
   re 62 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丶乏") ∷
   rw 63 q10 ∷
   rw 64 q12 ∷
   rw 65 q10 ∷
   re 63 3 (ℓ "中") ∷
   re 65 1 (ℓ "乏乇乏") ∷
   rw 64 q10 ∷
   rw 65 q13 ∷
   rw 66 q10 ∷
   re 64 3 (ℓ "乑") ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q10 ∷
   rw 66 q12 ∷
   rw 67 q10 ∷
   re 65 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏乇乏") ∷
   rw 66 q10 ∷
   rw 67 q13 ∷
   rw 68 q10 ∷
   re 66 3 (ℓ "乑") ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q10 ∷
   rw 68 q13 ∷
   rw 69 q10 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q14 ∷
   rw 90 q15 ∷
   rw 91 q5 ∷
   rw 92 q15 ∷
   rw 89 q15 ∷
   rw 90 q5 ∷
   rw 91 q15 ∷
   rw 88 q16 ∷
   rw 89 q1 ∷
   rw 90 q16 ∷
   rw 87 q15 ∷
   rw 88 q5 ∷
   rw 89 q15 ∷
   rw 86 q16 ∷
   rw 87 q1 ∷
   rw 88 q16 ∷
   rw 85 q16 ∷
   rw 86 q1 ∷
   rw 87 q16 ∷
   rw 84 q17 ∷
   rw 83 q16 ∷
   rw 84 q1 ∷
   rw 85 q16 ∷
   rw 82 q16 ∷
   rw 83 q1 ∷
   rw 84 q16 ∷
   rw 81 q16 ∷
   rw 82 q1 ∷
   rw 83 q16 ∷
   rw 80 q16 ∷
   rw 81 q1 ∷
   rw 82 q16 ∷
   rw 79 q16 ∷
   rw 80 q1 ∷
   rw 81 q16 ∷
   rw 78 q16 ∷
   rw 79 q1 ∷
   rw 80 q16 ∷
   rw 77 q18 ∷
   rw 78 q19 ∷
   rw 79 q18 ∷
   rw 76 q15 ∷
   rw 77 q5 ∷
   rw 78 q15 ∷
   rw 75 q16 ∷
   rw 76 q1 ∷
   rw 77 q16 ∷
   rw 74 q16 ∷
   rw 75 q1 ∷
   rw 76 q16 ∷
   rw 73 q16 ∷
   rw 74 q1 ∷
   rw 75 q16 ∷
   rw 72 q18 ∷
   rw 73 q19 ∷
   rw 74 q18 ∷
   rw 71 q15 ∷
   rw 72 q5 ∷
   rw 73 q15 ∷
   rw 70 q18 ∷
   rw 71 q19 ∷
   rw 72 q18 ∷
   rw 69 q15 ∷
   rw 70 q5 ∷
   rw 71 q15 ∷
   rw 68 q17 ∷
   rw 71 q6 ∷
   rw⁻ 70 q20 ∷
   rw⁻ 69 q21 ∷
   rw⁻ 68 q20 ∷
   re 67 1 (ℓ "乏乄乏") ∷
   rw⁻ 69 q10 ∷
   rw 68 q8 ∷
   rw⁻ 67 q10 ∷
   re 68 3 (ℓ "乔") ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw⁻ 68 q10 ∷
   rw 67 q8 ∷
   rw⁻ 66 q10 ∷
   re 67 3 (ℓ "乔") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw⁻ 67 q10 ∷
   rw 66 q9 ∷
   rw⁻ 65 q10 ∷
   re 66 3 (ℓ "丽") ∷
   re 64 1 (ℓ "乏乄乏") ∷
   rw⁻ 66 q10 ∷
   rw 65 q8 ∷
   rw⁻ 64 q10 ∷
   re 65 3 (ℓ "乔") ∷
   re 63 1 (ℓ "乏丧乏") ∷
   rw⁻ 65 q10 ∷
   rw 64 q9 ∷
   rw⁻ 63 q10 ∷
   re 64 3 (ℓ "丽") ∷
   re 62 1 (ℓ "乏丧乏") ∷
   rw⁻ 64 q10 ∷
   rw 63 q9 ∷
   rw⁻ 62 q10 ∷
   re 63 3 (ℓ "丽") ∷
   rw 63 q22 ∷
   rw 62 q20 ∷
   rw 63 q21 ∷
   rw 64 q20 ∷
   re 66 1 (ℓ "乏丶乏") ∷
   rw 65 q10 ∷
   rw 66 q12 ∷
   rw 67 q10 ∷
   re 65 3 (ℓ "中") ∷
   re 67 1 (ℓ "乏丶乏") ∷
   rw 66 q10 ∷
   rw 67 q12 ∷
   rw 68 q10 ∷
   re 66 3 (ℓ "中") ∷
   re 68 1 (ℓ "乏乇乏") ∷
   rw 67 q10 ∷
   rw 68 q13 ∷
   rw 69 q10 ∷
   re 67 3 (ℓ "乑") ∷
   re 69 1 (ℓ "乏丶乏") ∷
   rw 68 q10 ∷
   rw 69 q12 ∷
   rw 70 q10 ∷
   re 68 3 (ℓ "中") ∷
   re 70 1 (ℓ "乏乇乏") ∷
   rw 69 q10 ∷
   rw 70 q13 ∷
   rw 71 q10 ∷
   re 69 3 (ℓ "乑") ∷
   re 71 1 (ℓ "乏乇乏") ∷
   rw 70 q10 ∷
   rw 71 q13 ∷
   rw 72 q10 ∷
   re 70 3 (ℓ "乑") ∷
   rw 71 q14 ∷
   rw 88 q23 ∷
   re 88 1 (ℓ "丼临丼") ∷
   rw 87 q3 ∷
   rw⁻ 88 q5 ∷
   rw 89 q2 ∷
   re 87 3 (ℓ "乄") ∷
   rw 88 q4 ∷
   re 90 1 (ℓ "丼临丼") ∷
   rw 89 q3 ∷
   rw⁻ 90 q5 ∷
   rw 91 q2 ∷
   re 89 3 (ℓ "乄") ∷
   rw 90 q4 ∷
   re 92 1 (ℓ "丼丠丼") ∷
   rw 91 q3 ∷
   rw⁻ 92 q1 ∷
   rw 93 q2 ∷
   re 91 3 (ℓ "丧") ∷
   re 93 1 (ℓ "丼丠丼") ∷
   rw 92 q3 ∷
   rw⁻ 93 q1 ∷
   rw 94 q2 ∷
   re 92 3 (ℓ "丧") ∷
   re 94 1 (ℓ "丼丠丼") ∷
   rw 93 q3 ∷
   rw⁻ 94 q1 ∷
   rw 95 q2 ∷
   re 93 3 (ℓ "丧") ∷
   re 95 1 (ℓ "丼临丼") ∷
   rw 94 q3 ∷
   rw⁻ 95 q5 ∷
   rw 96 q2 ∷
   re 94 3 (ℓ "乄") ∷
   rw 95 q4 ∷
   re 97 1 (ℓ "丼丠丼") ∷
   rw 96 q3 ∷
   rw⁻ 97 q1 ∷
   rw 98 q2 ∷
   re 96 3 (ℓ "丧") ∷
   re 98 1 (ℓ "丼丠丼") ∷
   rw 97 q3 ∷
   rw⁻ 98 q1 ∷
   rw 99 q2 ∷
   re 97 3 (ℓ "丧") ∷
   re 99 1 (ℓ "丼丠丼") ∷
   rw 98 q3 ∷
   rw⁻ 99 q1 ∷
   rw 100 q2 ∷
   re 98 3 (ℓ "丧") ∷
   re 100 1 (ℓ "丼丠丼") ∷
   rw 99 q3 ∷
   rw⁻ 100 q1 ∷
   rw 101 q2 ∷
   re 99 3 (ℓ "丧") ∷
   re 101 1 (ℓ "丼丠丼") ∷
   rw 100 q3 ∷
   rw⁻ 101 q1 ∷
   rw 102 q2 ∷
   re 100 3 (ℓ "丧") ∷
   re 102 1 (ℓ "丼丠丼") ∷
   rw 101 q3 ∷
   rw⁻ 102 q1 ∷
   rw 103 q2 ∷
   re 101 3 (ℓ "丧") ∷
   rw 72 q24 ∷
   re 72 1 (ℓ "丼临丼") ∷
   rw 71 q3 ∷
   rw⁻ 72 q5 ∷
   rw 73 q2 ∷
   re 71 3 (ℓ "乄") ∷
   rw 72 q4 ∷
   re 74 1 (ℓ "丼临丼") ∷
   rw 73 q3 ∷
   rw⁻ 74 q5 ∷
   rw 75 q2 ∷
   re 73 3 (ℓ "乄") ∷
   rw 74 q4 ∷
   re 76 1 (ℓ "丼丠丼") ∷
   rw 75 q3 ∷
   rw⁻ 76 q1 ∷
   rw 77 q2 ∷
   re 75 3 (ℓ "丧") ∷
   re 77 1 (ℓ "丼丠丼") ∷
   rw 76 q3 ∷
   rw⁻ 77 q1 ∷
   rw 78 q2 ∷
   re 76 3 (ℓ "丧") ∷
   re 78 1 (ℓ "丼丠丼") ∷
   rw 77 q3 ∷
   rw⁻ 78 q1 ∷
   rw 79 q2 ∷
   re 77 3 (ℓ "丧") ∷
   re 79 1 (ℓ "丼临丼") ∷
   rw 78 q3 ∷
   rw⁻ 79 q5 ∷
   rw 80 q2 ∷
   re 78 3 (ℓ "乄") ∷
   rw 79 q4 ∷
   re 81 1 (ℓ "丼丠丼") ∷
   rw 80 q3 ∷
   rw⁻ 81 q1 ∷
   rw 82 q2 ∷
   re 80 3 (ℓ "丧") ∷
   re 82 1 (ℓ "丼丠丼") ∷
   rw 81 q3 ∷
   rw⁻ 82 q1 ∷
   rw 83 q2 ∷
   re 81 3 (ℓ "丧") ∷
   re 83 1 (ℓ "丼丠丼") ∷
   rw 82 q3 ∷
   rw⁻ 83 q1 ∷
   rw 84 q2 ∷
   re 82 3 (ℓ "丧") ∷
   re 84 1 (ℓ "丼丠丼") ∷
   rw 83 q3 ∷
   rw⁻ 84 q1 ∷
   rw 85 q2 ∷
   re 83 3 (ℓ "丧") ∷
   re 85 1 (ℓ "丼丠丼") ∷
   rw 84 q3 ∷
   rw⁻ 85 q1 ∷
   rw 86 q2 ∷
   re 84 3 (ℓ "丧") ∷
   re 86 1 (ℓ "丼丠丼") ∷ []) Eq.refl
