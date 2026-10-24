{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D185 (W : Ws) where

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
  q2 = wE 173 W
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = wE 761 W
  q8 : Eqn
  q8 = wE 175 W
  q9 : Eqn
  q9 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q10 : Eqn
  q10 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q11 : Eqn
  q11 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q12 : Eqn
  q12 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q13 : Eqn
  q13 = wE 537 W
  q14 : Eqn
  q14 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q15 : Eqn
  q15 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q16 : Eqn
  q16 = wE 5 W
  q17 : Eqn
  q17 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q18 : Eqn
  q18 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q19 : Eqn
  q19 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q20 : Eqn
  q20 = wE 140 W
  q21 : Eqn
  q21 = wE 7 W
  q22 : Eqn
  q22 = wE 538 W
  q23 : Eqn
  q23 = wE 27 W
  q24 : Eqn
  q24 = wE 142 W
  q25 : Eqn
  q25 = wE 31 W
  q26 : Eqn
  q26 = wE 617 W
  q27 : Eqn
  q27 = wE 13 W
  q28 : Eqn
  q28 = wE 78 W
  q29 : Eqn
  q29 = wE 762 W
  q30 : Eqn
  q30 = wE 618 W
  q31 : Eqn
  q31 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q32 : Eqn
  q32 = wE 763 W
  q33 : Eqn
  q33 = wE 764 W
  q34 : Eqn
  q34 = wE 765 W
  q35 : Eqn
  q35 = wE 766 W

-- Bar(SSKSKK;3,1->0) passes groups of WBar(SSKSKK;~3,2->0): 731 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~32-⟶0⟩ : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中中乑中乑乑丞丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧丞乖丞丧丧乄丧乄乄") ⟫ʷ ≈ ⟪ (ℓ "丞中中乑中乑乑丞丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧丞乖丞丧丧乄丧乄乄中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨SSKSKK~32-⟶0⟩ = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞中中乑中乑乑丞丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧丞乖丞丧丧乄丧乄乄") (ℓ "丞中中乑中乑乑丞丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧丞乖丞丧丧乄丧乄乄中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临")
  (rw 37 q1 ∷
   rw 36 q2 ∷
   re 35 1 (ℓ "乏乄乏") ∷
   rw 37 q3 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw 36 q3 ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q3 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw 34 q3 ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q3 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   rw 28 q4 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   rw 23 q5 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q3 ∷
   rw 21 q5 ∷
   rw 20 q5 ∷
   rw 19 q5 ∷
   rw 18 q5 ∷
   rw 17 q5 ∷
   rw 16 q5 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q6 ∷
   rw 9 q4 ∷
   rw 8 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏乆乏") ∷
   rw 8 q3 ∷
   re 5 1 (ℓ "乏乄乏") ∷
   rw 7 q3 ∷
   re 4 1 (ℓ "乏乄乏") ∷
   rw 6 q3 ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q3 ∷
   re 2 1 (ℓ "乏乄乏") ∷
   rw 4 q3 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q3 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q3 ∷
   rw 1 q7 ∷
   rw 0 q8 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乑") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "中") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "乑") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "乑") ∷
   rw 7 q8 ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "中") ∷
   rw 11 q1 ∷
   re 9 3 (ℓ "中") ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "乑") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "乑") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "乑") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "乓") ∷
   rw⁻ 15 q4 ∷
   rw⁻ 16 q6 ∷
   rw⁻ 17 q4 ∷
   rw⁻ 18 q6 ∷
   rw⁻ 19 q5 ∷
   rw⁻ 20 q5 ∷
   rw⁻ 21 q5 ∷
   rw⁻ 22 q4 ∷
   rw⁻ 23 q6 ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q5 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q5 ∷
   rw⁻ 28 q5 ∷
   rw⁻ 29 q5 ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "乓") ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q5 ∷
   rw⁻ 33 q4 ∷
   rw⁻ 34 q5 ∷
   rw⁻ 35 q4 ∷
   rw⁻ 36 q4 ∷
   rw 37 q3 ∷
   rw 36 q9 ∷
   rw 37 q10 ∷
   rw 38 q9 ∷
   rw 35 q9 ∷
   rw 36 q10 ∷
   rw 37 q9 ∷
   rw 34 q11 ∷
   rw 35 q12 ∷
   rw 36 q11 ∷
   rw 33 q9 ∷
   rw 34 q10 ∷
   rw 35 q9 ∷
   rw 32 q11 ∷
   rw 33 q12 ∷
   rw 34 q11 ∷
   rw 31 q11 ∷
   rw 32 q12 ∷
   rw 33 q11 ∷
   rw 30 q13 ∷
   rw 29 q11 ∷
   rw 30 q12 ∷
   rw 31 q11 ∷
   rw 28 q11 ∷
   rw 29 q12 ∷
   rw 30 q11 ∷
   rw 27 q11 ∷
   rw 28 q12 ∷
   rw 29 q11 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 25 q11 ∷
   rw 26 q12 ∷
   rw 27 q11 ∷
   rw 24 q11 ∷
   rw 25 q12 ∷
   rw 26 q11 ∷
   rw 23 q14 ∷
   rw 24 q15 ∷
   rw 25 q14 ∷
   rw 22 q9 ∷
   rw 23 q10 ∷
   rw 24 q9 ∷
   rw 21 q11 ∷
   rw 22 q12 ∷
   rw 23 q11 ∷
   rw 20 q11 ∷
   rw 21 q12 ∷
   rw 22 q11 ∷
   rw 19 q11 ∷
   rw 20 q12 ∷
   rw 21 q11 ∷
   rw 18 q14 ∷
   rw 19 q15 ∷
   rw 20 q14 ∷
   rw 17 q9 ∷
   rw 18 q10 ∷
   rw 19 q9 ∷
   rw 16 q14 ∷
   rw 17 q15 ∷
   rw 18 q14 ∷
   rw 15 q9 ∷
   rw 16 q10 ∷
   rw 17 q9 ∷
   rw 14 q13 ∷
   rw 17 q16 ∷
   rw⁻ 16 q17 ∷
   rw⁻ 15 q18 ∷
   rw⁻ 14 q17 ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q19 ∷
   rw 14 q20 ∷
   rw⁻ 13 q19 ∷
   re 14 3 (ℓ "乔") ∷
   re 12 1 (ℓ "乏乄乏") ∷
   rw⁻ 14 q19 ∷
   rw 13 q20 ∷
   rw⁻ 12 q19 ∷
   re 13 3 (ℓ "乔") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q19 ∷
   rw 12 q21 ∷
   rw⁻ 11 q19 ∷
   re 12 3 (ℓ "丽") ∷
   re 10 1 (ℓ "乏乄乏") ∷
   rw⁻ 12 q19 ∷
   rw 11 q20 ∷
   rw⁻ 10 q19 ∷
   re 11 3 (ℓ "乔") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw⁻ 11 q19 ∷
   rw 10 q21 ∷
   rw⁻ 9 q19 ∷
   re 10 3 (ℓ "丽") ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw⁻ 10 q19 ∷
   rw 9 q21 ∷
   rw⁻ 8 q19 ∷
   re 9 3 (ℓ "丽") ∷
   rw 9 q22 ∷
   rw 8 q17 ∷
   rw 9 q18 ∷
   rw 10 q17 ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 11 q19 ∷
   rw 12 q23 ∷
   rw 13 q19 ∷
   re 11 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 12 q19 ∷
   rw 13 q23 ∷
   rw 14 q19 ∷
   re 12 3 (ℓ "中") ∷
   re 14 1 (ℓ "乏乇乏") ∷
   rw 13 q19 ∷
   rw 14 q24 ∷
   rw 15 q19 ∷
   re 13 3 (ℓ "乑") ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 14 q19 ∷
   rw 15 q23 ∷
   rw 16 q19 ∷
   re 14 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏乇乏") ∷
   rw 15 q19 ∷
   rw 16 q24 ∷
   rw 17 q19 ∷
   re 15 3 (ℓ "乑") ∷
   re 17 1 (ℓ "乏乇乏") ∷
   rw 16 q19 ∷
   rw 17 q24 ∷
   rw 18 q19 ∷
   re 16 3 (ℓ "乑") ∷
   rw 17 q25 ∷
   rw 34 q26 ∷
   re 34 1 (ℓ "丼临丼") ∷
   rw 33 q27 ∷
   rw⁻ 34 q10 ∷
   rw 35 q28 ∷
   re 33 3 (ℓ "乄") ∷
   rw 34 q29 ∷
   re 36 1 (ℓ "丼临丼") ∷
   rw 35 q27 ∷
   rw⁻ 36 q10 ∷
   rw 37 q28 ∷
   re 35 3 (ℓ "乄") ∷
   rw 36 q29 ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 37 q27 ∷
   rw⁻ 38 q12 ∷
   rw 39 q28 ∷
   re 37 3 (ℓ "丧") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q27 ∷
   rw⁻ 39 q12 ∷
   rw 40 q28 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q27 ∷
   rw⁻ 40 q12 ∷
   rw 41 q28 ∷
   re 39 3 (ℓ "丧") ∷
   re 41 1 (ℓ "丼临丼") ∷
   rw 40 q27 ∷
   rw⁻ 41 q10 ∷
   rw 42 q28 ∷
   re 40 3 (ℓ "乄") ∷
   rw 41 q29 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q27 ∷
   rw⁻ 43 q12 ∷
   rw 44 q28 ∷
   re 42 3 (ℓ "丧") ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 43 q27 ∷
   rw⁻ 44 q12 ∷
   rw 45 q28 ∷
   re 43 3 (ℓ "丧") ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 44 q27 ∷
   rw⁻ 45 q12 ∷
   rw 46 q28 ∷
   re 44 3 (ℓ "丧") ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 45 q27 ∷
   rw⁻ 46 q12 ∷
   rw 47 q28 ∷
   re 45 3 (ℓ "丧") ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 46 q27 ∷
   rw⁻ 47 q12 ∷
   rw 48 q28 ∷
   re 46 3 (ℓ "丧") ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 47 q27 ∷
   rw⁻ 48 q12 ∷
   rw 49 q28 ∷
   re 47 3 (ℓ "丧") ∷
   rw 18 q30 ∷
   re 18 1 (ℓ "丼临丼") ∷
   rw 17 q27 ∷
   rw⁻ 18 q10 ∷
   rw 19 q28 ∷
   re 17 3 (ℓ "乄") ∷
   rw 18 q29 ∷
   re 20 1 (ℓ "丼临丼") ∷
   rw 19 q27 ∷
   rw⁻ 20 q10 ∷
   rw 21 q28 ∷
   re 19 3 (ℓ "乄") ∷
   rw 20 q29 ∷
   re 22 1 (ℓ "丼丠丼") ∷
   rw 21 q27 ∷
   rw⁻ 22 q12 ∷
   rw 23 q28 ∷
   re 21 3 (ℓ "丧") ∷
   re 23 1 (ℓ "丼丠丼") ∷
   rw 22 q27 ∷
   rw⁻ 23 q12 ∷
   rw 24 q28 ∷
   re 22 3 (ℓ "丧") ∷
   re 24 1 (ℓ "丼丠丼") ∷
   rw 23 q27 ∷
   rw⁻ 24 q12 ∷
   rw 25 q28 ∷
   re 23 3 (ℓ "丧") ∷
   re 25 1 (ℓ "丼临丼") ∷
   rw 24 q27 ∷
   rw⁻ 25 q10 ∷
   rw 26 q28 ∷
   re 24 3 (ℓ "乄") ∷
   rw 25 q29 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q27 ∷
   rw⁻ 27 q12 ∷
   rw 28 q28 ∷
   re 26 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q27 ∷
   rw⁻ 28 q12 ∷
   rw 29 q28 ∷
   re 27 3 (ℓ "丧") ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q27 ∷
   rw⁻ 29 q12 ∷
   rw 30 q28 ∷
   re 28 3 (ℓ "丧") ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q27 ∷
   rw⁻ 30 q12 ∷
   rw 31 q28 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q27 ∷
   rw⁻ 31 q12 ∷
   rw 32 q28 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 31 q27 ∷
   rw⁻ 32 q12 ∷
   rw 33 q28 ∷
   re 31 3 (ℓ "丧") ∷
   rw 32 q16 ∷
   rw 31 q21 ∷
   rw 30 q21 ∷
   rw 29 q21 ∷
   rw 28 q21 ∷
   rw 27 q21 ∷
   rw 26 q21 ∷
   rw⁻ 25 q31 ∷
   rw 24 q20 ∷
   rw 23 q21 ∷
   rw 22 q21 ∷
   rw 21 q21 ∷
   rw⁻ 20 q31 ∷
   rw 19 q20 ∷
   rw⁻ 18 q31 ∷
   rw 17 q20 ∷
   re 16 1 (ℓ "乏乄乏") ∷
   rw⁻ 18 q19 ∷
   rw 17 q20 ∷
   rw⁻ 16 q19 ∷
   re 17 3 (ℓ "乔") ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw⁻ 17 q19 ∷
   rw 16 q20 ∷
   rw⁻ 15 q19 ∷
   re 16 3 (ℓ "乔") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw⁻ 16 q19 ∷
   rw 15 q21 ∷
   rw⁻ 14 q19 ∷
   re 15 3 (ℓ "丽") ∷
   re 13 1 (ℓ "乏乄乏") ∷
   rw⁻ 15 q19 ∷
   rw 14 q20 ∷
   rw⁻ 13 q19 ∷
   re 14 3 (ℓ "乔") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw⁻ 14 q19 ∷
   rw 13 q21 ∷
   rw⁻ 12 q19 ∷
   re 13 3 (ℓ "丽") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw⁻ 13 q19 ∷
   rw 12 q21 ∷
   rw⁻ 11 q19 ∷
   re 12 3 (ℓ "丽") ∷
   rw 12 q32 ∷
   rw 11 q24 ∷
   rw 12 q31 ∷
   rw 13 q24 ∷
   rw 14 q31 ∷
   rw 15 q23 ∷
   rw 16 q23 ∷
   rw 17 q23 ∷
   rw 18 q24 ∷
   rw 19 q31 ∷
   rw 20 q23 ∷
   rw 21 q23 ∷
   rw 22 q23 ∷
   rw 23 q23 ∷
   rw 24 q23 ∷
   rw 25 q23 ∷
   re 27 1 (ℓ "乏丶乏") ∷
   rw 26 q19 ∷
   rw 27 q23 ∷
   rw 28 q19 ∷
   re 26 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 27 q19 ∷
   rw 28 q23 ∷
   rw 29 q19 ∷
   re 27 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏乇乏") ∷
   rw 28 q19 ∷
   rw 29 q24 ∷
   rw 30 q19 ∷
   re 28 3 (ℓ "乑") ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q19 ∷
   rw 30 q23 ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏乇乏") ∷
   rw 30 q19 ∷
   rw 31 q24 ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "乑") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q19 ∷
   rw 32 q24 ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "乑") ∷
   rw 32 q25 ∷
   rw 54 q9 ∷
   rw 55 q10 ∷
   rw 56 q9 ∷
   rw 53 q9 ∷
   rw 54 q10 ∷
   rw 55 q9 ∷
   rw 52 q11 ∷
   rw 53 q12 ∷
   rw 54 q11 ∷
   rw 51 q9 ∷
   rw 52 q10 ∷
   rw 53 q9 ∷
   rw 50 q11 ∷
   rw 51 q12 ∷
   rw 52 q11 ∷
   rw 49 q11 ∷
   rw 50 q12 ∷
   rw 51 q11 ∷
   rw 48 q13 ∷
   rw 47 q11 ∷
   rw 48 q12 ∷
   rw 49 q11 ∷
   rw 46 q11 ∷
   rw 47 q12 ∷
   rw 48 q11 ∷
   rw 45 q11 ∷
   rw 46 q12 ∷
   rw 47 q11 ∷
   rw 44 q11 ∷
   rw 45 q12 ∷
   rw 46 q11 ∷
   rw 43 q11 ∷
   rw 44 q12 ∷
   rw 45 q11 ∷
   rw 42 q11 ∷
   rw 43 q12 ∷
   rw 44 q11 ∷
   rw 41 q14 ∷
   rw 42 q15 ∷
   rw 43 q14 ∷
   rw 40 q9 ∷
   rw 41 q10 ∷
   rw 42 q9 ∷
   rw 39 q11 ∷
   rw 40 q12 ∷
   rw 41 q11 ∷
   rw 38 q11 ∷
   rw 39 q12 ∷
   rw 40 q11 ∷
   rw 37 q11 ∷
   rw 38 q12 ∷
   rw 39 q11 ∷
   rw 36 q14 ∷
   rw 37 q15 ∷
   rw 38 q14 ∷
   rw 35 q9 ∷
   rw 36 q10 ∷
   rw 37 q9 ∷
   rw 34 q14 ∷
   rw 35 q15 ∷
   rw 36 q14 ∷
   rw 33 q9 ∷
   rw 34 q10 ∷
   rw 35 q9 ∷
   rw 32 q13 ∷
   rw 35 q16 ∷
   rw⁻ 34 q17 ∷
   rw⁻ 33 q18 ∷
   rw⁻ 32 q17 ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw⁻ 33 q19 ∷
   rw 32 q20 ∷
   rw⁻ 31 q19 ∷
   re 32 3 (ℓ "乔") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw⁻ 32 q19 ∷
   rw 31 q20 ∷
   rw⁻ 30 q19 ∷
   re 31 3 (ℓ "乔") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q19 ∷
   rw 30 q21 ∷
   rw⁻ 29 q19 ∷
   re 30 3 (ℓ "丽") ∷
   re 28 1 (ℓ "乏乄乏") ∷
   rw⁻ 30 q19 ∷
   rw 29 q20 ∷
   rw⁻ 28 q19 ∷
   re 29 3 (ℓ "乔") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw⁻ 29 q19 ∷
   rw 28 q21 ∷
   rw⁻ 27 q19 ∷
   re 28 3 (ℓ "丽") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw⁻ 28 q19 ∷
   rw 27 q21 ∷
   rw⁻ 26 q19 ∷
   re 27 3 (ℓ "丽") ∷
   rw 27 q22 ∷
   rw 26 q17 ∷
   rw 27 q18 ∷
   rw 28 q17 ∷
   re 30 1 (ℓ "乏丶乏") ∷
   rw 29 q19 ∷
   rw 30 q23 ∷
   rw 31 q19 ∷
   re 29 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丶乏") ∷
   rw 30 q19 ∷
   rw 31 q23 ∷
   rw 32 q19 ∷
   re 30 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏乇乏") ∷
   rw 31 q19 ∷
   rw 32 q24 ∷
   rw 33 q19 ∷
   re 31 3 (ℓ "乑") ∷
   re 33 1 (ℓ "乏丶乏") ∷
   rw 32 q19 ∷
   rw 33 q23 ∷
   rw 34 q19 ∷
   re 32 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏乇乏") ∷
   rw 33 q19 ∷
   rw 34 q24 ∷
   rw 35 q19 ∷
   re 33 3 (ℓ "乑") ∷
   re 35 1 (ℓ "乏乇乏") ∷
   rw 34 q19 ∷
   rw 35 q24 ∷
   rw 36 q19 ∷
   re 34 3 (ℓ "乑") ∷
   rw 35 q25 ∷
   rw 52 q33 ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q27 ∷
   rw⁻ 52 q12 ∷
   rw 53 q28 ∷
   re 51 3 (ℓ "丧") ∷
   re 53 1 (ℓ "丼丠丼") ∷
   rw 52 q27 ∷
   rw⁻ 53 q12 ∷
   rw 54 q28 ∷
   re 52 3 (ℓ "丧") ∷
   re 54 1 (ℓ "丼临丼") ∷
   rw 53 q27 ∷
   rw⁻ 54 q10 ∷
   rw 55 q28 ∷
   re 53 3 (ℓ "乄") ∷
   re 55 1 (ℓ "丼丠丼") ∷
   rw 54 q27 ∷
   rw⁻ 55 q12 ∷
   rw 56 q28 ∷
   re 54 3 (ℓ "丧") ∷
   re 56 1 (ℓ "丼临丼") ∷
   rw 55 q27 ∷
   rw⁻ 56 q10 ∷
   rw 57 q28 ∷
   re 55 3 (ℓ "乄") ∷
   re 57 1 (ℓ "丼临丼") ∷
   rw 56 q27 ∷
   rw⁻ 57 q10 ∷
   rw 58 q28 ∷
   re 56 3 (ℓ "乄") ∷
   rw 36 q34 ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q27 ∷
   rw⁻ 36 q12 ∷
   rw 37 q28 ∷
   re 35 3 (ℓ "丧") ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 36 q27 ∷
   rw⁻ 37 q12 ∷
   rw 38 q28 ∷
   re 36 3 (ℓ "丧") ∷
   re 38 1 (ℓ "丼临丼") ∷
   rw 37 q27 ∷
   rw⁻ 38 q10 ∷
   rw 39 q28 ∷
   re 37 3 (ℓ "乄") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q27 ∷
   rw⁻ 39 q12 ∷
   rw 40 q28 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼临丼") ∷
   rw 39 q27 ∷
   rw⁻ 40 q10 ∷
   rw 41 q28 ∷
   re 39 3 (ℓ "乄") ∷
   re 41 1 (ℓ "丼临丼") ∷
   rw 40 q27 ∷
   rw⁻ 41 q10 ∷
   rw 42 q28 ∷
   re 40 3 (ℓ "乄") ∷
   rw 41 q16 ∷
   rw 40 q20 ∷
   rw 39 q20 ∷
   rw 38 q21 ∷
   rw 37 q20 ∷
   rw 36 q21 ∷
   rw 35 q21 ∷
   re 34 1 (ℓ "乏乄乏") ∷
   rw⁻ 36 q19 ∷
   rw 35 q20 ∷
   rw⁻ 34 q19 ∷
   re 35 3 (ℓ "乔") ∷
   re 33 1 (ℓ "乏乄乏") ∷
   rw⁻ 35 q19 ∷
   rw 34 q20 ∷
   rw⁻ 33 q19 ∷
   re 34 3 (ℓ "乔") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw⁻ 34 q19 ∷
   rw 33 q21 ∷
   rw⁻ 32 q19 ∷
   re 33 3 (ℓ "丽") ∷
   re 31 1 (ℓ "乏乄乏") ∷
   rw⁻ 33 q19 ∷
   rw 32 q20 ∷
   rw⁻ 31 q19 ∷
   re 32 3 (ℓ "乔") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw⁻ 32 q19 ∷
   rw 31 q21 ∷
   rw⁻ 30 q19 ∷
   re 31 3 (ℓ "丽") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw⁻ 31 q19 ∷
   rw 30 q21 ∷
   rw⁻ 29 q19 ∷
   re 30 3 (ℓ "丽") ∷
   rw 30 q35 ∷
   rw 29 q23 ∷
   rw 30 q23 ∷
   rw 31 q24 ∷
   rw 32 q23 ∷
   rw 33 q24 ∷
   rw 34 q24 ∷
   re 36 1 (ℓ "乏丶乏") ∷
   rw 35 q19 ∷
   rw 36 q23 ∷
   rw 37 q19 ∷
   re 35 3 (ℓ "中") ∷
   re 37 1 (ℓ "乏丶乏") ∷
   rw 36 q19 ∷
   rw 37 q23 ∷
   rw 38 q19 ∷
   re 36 3 (ℓ "中") ∷
   re 38 1 (ℓ "乏乇乏") ∷
   rw 37 q19 ∷
   rw 38 q24 ∷
   rw 39 q19 ∷
   re 37 3 (ℓ "乑") ∷
   re 39 1 (ℓ "乏丶乏") ∷
   rw 38 q19 ∷
   rw 39 q23 ∷
   rw 40 q19 ∷
   re 38 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏乇乏") ∷
   rw 39 q19 ∷
   rw 40 q24 ∷
   rw 41 q19 ∷
   re 39 3 (ℓ "乑") ∷
   re 41 1 (ℓ "乏乇乏") ∷
   rw 40 q19 ∷
   rw 41 q24 ∷
   rw 42 q19 ∷
   re 40 3 (ℓ "乑") ∷
   rw 41 q25 ∷ []) Eq.refl
