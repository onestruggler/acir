{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D263 (W : Ws) where

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
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q7 : Eqn
  q7 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q8 : Eqn
  q8 = wE 611 W
  q9 : Eqn
  q9 = wE 175 W
  q10 : Eqn
  q10 = wE 151 W
  q11 : Eqn
  q11 = eqn (ℓ "临丞") (ℓ "丞临") (low-comm (CK₁₀) ((X ↑)))
  q12 : Eqn
  q12 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q13 : Eqn
  q13 = eqn (ℓ "丠丞") (ℓ "丞丠") (low-comm (CS) ((X ↑)))
  q14 : Eqn
  q14 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q15 : Eqn
  q15 = wE 537 W
  q16 : Eqn
  q16 = eqn (ℓ "与丞") (ℓ "丞与") (low-comm ((S ↑)) ((X ↑)))
  q17 : Eqn
  q17 = eqn (ℓ "与乖") (ℓ "乖与") (low-comm ((S ↑)) (CX₁₀))
  q18 : Eqn
  q18 = wE 5 W
  q19 : Eqn
  q19 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q20 : Eqn
  q20 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q21 : Eqn
  q21 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q22 : Eqn
  q22 = wE 140 W
  q23 : Eqn
  q23 = wE 7 W
  q24 : Eqn
  q24 = wE 538 W
  q25 : Eqn
  q25 = wE 27 W
  q26 : Eqn
  q26 = wE 142 W
  q27 : Eqn
  q27 = wE 31 W
  q28 : Eqn
  q28 = wE 614 W
  q29 : Eqn
  q29 = wE 13 W
  q30 : Eqn
  q30 = wE 78 W
  q31 : Eqn
  q31 = wE 762 W
  q32 : Eqn
  q32 = wE 615 W

-- Bar(SSKSKK;3,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~3,2->0) part0: 500 steps
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part0 : ⟪ (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乑业乑业中中中乑业中中中中中中丞丞乖丞丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞中中乑中乑乑丧丧丧丧丧丧丧丧丧丧丧丧丧丼乖丠丼丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ
lem-Bar⟨SSKSKK31-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~32-⟶0⟩-part0 = derive (ℓ "中中乑中乑乑乓临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乑业乑业中中中乑业中中中中中中丞丞乖丞丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧") (ℓ "丞乑业乑业中中中乑业中中中中中中丞丞乖丞中中乑中乑乑丧丧丧丧丧丧丧丧丧丧丧丧丧丼乖丠丼丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且临与临与丠丠丠临与丠丠丠丠丠丠乓丠丠临丠临临丞乖丞乄且乄且丧丧丧乄且丧丧丧丧丧丧")
  (rw 46 q1 ∷
   rw 45 q2 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q3 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q3 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q3 ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q3 ∷
   re 40 1 (ℓ "乏丧乏") ∷
   rw 42 q3 ∷
   re 39 1 (ℓ "乏丧乏") ∷
   rw 41 q3 ∷
   rw 38 q4 ∷
   re 37 1 (ℓ "乏乄乏") ∷
   rw 39 q3 ∷
   re 36 1 (ℓ "乏丧乏") ∷
   rw 38 q3 ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q3 ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q3 ∷
   rw 33 q4 ∷
   re 32 1 (ℓ "乏乄乏") ∷
   rw 34 q3 ∷
   rw 31 q4 ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q3 ∷
   rw 29 q2 ∷
   rw 28 q5 ∷
   rw 27 q5 ∷
   rw 26 q6 ∷
   rw 25 q5 ∷
   rw 24 q6 ∷
   rw 23 q6 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 24 q3 ∷
   rw 21 q6 ∷
   rw 20 q6 ∷
   rw 19 q6 ∷
   rw 18 q6 ∷
   rw 17 q6 ∷
   rw 16 q6 ∷
   rw 15 q7 ∷
   rw 14 q5 ∷
   rw 13 q6 ∷
   rw 12 q6 ∷
   rw 11 q6 ∷
   rw 10 q7 ∷
   rw 9 q5 ∷
   rw 8 q7 ∷
   rw 7 q5 ∷
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
   rw 1 q8 ∷
   rw 0 q9 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "乑") ∷
   rw 2 q10 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "乑") ∷
   rw 4 q10 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 9 q1 ∷
   re 7 3 (ℓ "中") ∷
   rw 10 q1 ∷
   re 8 3 (ℓ "乑") ∷
   rw 9 q10 ∷
   rw 12 q1 ∷
   re 10 3 (ℓ "中") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "中") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "中") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "中") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "中") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q9 ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "中") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "中") ∷
   rw 21 q1 ∷
   re 19 3 (ℓ "乑") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "中") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "乑") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "乑") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "乓") ∷
   rw⁻ 24 q5 ∷
   rw⁻ 25 q7 ∷
   rw⁻ 26 q5 ∷
   rw⁻ 27 q7 ∷
   rw⁻ 28 q6 ∷
   rw⁻ 29 q6 ∷
   rw⁻ 30 q6 ∷
   rw⁻ 31 q5 ∷
   rw⁻ 32 q7 ∷
   rw⁻ 33 q6 ∷
   rw⁻ 34 q6 ∷
   rw⁻ 35 q6 ∷
   rw⁻ 36 q6 ∷
   rw⁻ 37 q6 ∷
   rw⁻ 38 q6 ∷
   rw 41 q1 ∷
   re 39 3 (ℓ "乓") ∷
   rw⁻ 40 q6 ∷
   rw⁻ 41 q6 ∷
   rw⁻ 42 q5 ∷
   rw⁻ 43 q6 ∷
   rw⁻ 44 q5 ∷
   rw⁻ 45 q5 ∷
   rw 46 q3 ∷
   rw 45 q11 ∷
   rw 46 q12 ∷
   rw 47 q11 ∷
   rw 44 q11 ∷
   rw 45 q12 ∷
   rw 46 q11 ∷
   rw 43 q13 ∷
   rw 44 q14 ∷
   rw 45 q13 ∷
   rw 42 q11 ∷
   rw 43 q12 ∷
   rw 44 q11 ∷
   rw 41 q13 ∷
   rw 42 q14 ∷
   rw 43 q13 ∷
   rw 40 q13 ∷
   rw 41 q14 ∷
   rw 42 q13 ∷
   rw 39 q15 ∷
   rw 38 q13 ∷
   rw 39 q14 ∷
   rw 40 q13 ∷
   rw 37 q13 ∷
   rw 38 q14 ∷
   rw 39 q13 ∷
   rw 36 q13 ∷
   rw 37 q14 ∷
   rw 38 q13 ∷
   rw 35 q13 ∷
   rw 36 q14 ∷
   rw 37 q13 ∷
   rw 34 q13 ∷
   rw 35 q14 ∷
   rw 36 q13 ∷
   rw 33 q13 ∷
   rw 34 q14 ∷
   rw 35 q13 ∷
   rw 32 q16 ∷
   rw 33 q17 ∷
   rw 34 q16 ∷
   rw 31 q11 ∷
   rw 32 q12 ∷
   rw 33 q11 ∷
   rw 30 q13 ∷
   rw 31 q14 ∷
   rw 32 q13 ∷
   rw 29 q13 ∷
   rw 30 q14 ∷
   rw 31 q13 ∷
   rw 28 q13 ∷
   rw 29 q14 ∷
   rw 30 q13 ∷
   rw 27 q16 ∷
   rw 28 q17 ∷
   rw 29 q16 ∷
   rw 26 q11 ∷
   rw 27 q12 ∷
   rw 28 q11 ∷
   rw 25 q16 ∷
   rw 26 q17 ∷
   rw 27 q16 ∷
   rw 24 q11 ∷
   rw 25 q12 ∷
   rw 26 q11 ∷
   rw 23 q15 ∷
   rw 26 q18 ∷
   rw⁻ 25 q19 ∷
   rw⁻ 24 q20 ∷
   rw⁻ 23 q19 ∷
   re 22 1 (ℓ "乏乄乏") ∷
   rw⁻ 24 q21 ∷
   rw 23 q22 ∷
   rw⁻ 22 q21 ∷
   re 23 3 (ℓ "乔") ∷
   re 21 1 (ℓ "乏乄乏") ∷
   rw⁻ 23 q21 ∷
   rw 22 q22 ∷
   rw⁻ 21 q21 ∷
   re 22 3 (ℓ "乔") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw⁻ 22 q21 ∷
   rw 21 q23 ∷
   rw⁻ 20 q21 ∷
   re 21 3 (ℓ "丽") ∷
   re 19 1 (ℓ "乏乄乏") ∷
   rw⁻ 21 q21 ∷
   rw 20 q22 ∷
   rw⁻ 19 q21 ∷
   re 20 3 (ℓ "乔") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw⁻ 20 q21 ∷
   rw 19 q23 ∷
   rw⁻ 18 q21 ∷
   re 19 3 (ℓ "丽") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw⁻ 19 q21 ∷
   rw 18 q23 ∷
   rw⁻ 17 q21 ∷
   re 18 3 (ℓ "丽") ∷
   rw 18 q24 ∷
   rw 17 q19 ∷
   rw 18 q20 ∷
   rw 19 q19 ∷
   re 21 1 (ℓ "乏丶乏") ∷
   rw 20 q21 ∷
   rw 21 q25 ∷
   rw 22 q21 ∷
   re 20 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丶乏") ∷
   rw 21 q21 ∷
   rw 22 q25 ∷
   rw 23 q21 ∷
   re 21 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏乇乏") ∷
   rw 22 q21 ∷
   rw 23 q26 ∷
   rw 24 q21 ∷
   re 22 3 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丶乏") ∷
   rw 23 q21 ∷
   rw 24 q25 ∷
   rw 25 q21 ∷
   re 23 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏乇乏") ∷
   rw 24 q21 ∷
   rw 25 q26 ∷
   rw 26 q21 ∷
   re 24 3 (ℓ "乑") ∷
   re 26 1 (ℓ "乏乇乏") ∷
   rw 25 q21 ∷
   rw 26 q26 ∷
   rw 27 q21 ∷
   re 25 3 (ℓ "乑") ∷
   rw 26 q27 ∷
   rw 43 q28 ∷
   re 43 1 (ℓ "丼丠丼") ∷
   rw 42 q29 ∷
   rw⁻ 43 q14 ∷
   rw 44 q30 ∷
   re 42 3 (ℓ "丧") ∷
   re 44 1 (ℓ "丼丠丼") ∷
   rw 43 q29 ∷
   rw⁻ 44 q14 ∷
   rw 45 q30 ∷
   re 43 3 (ℓ "丧") ∷
   re 45 1 (ℓ "丼丠丼") ∷
   rw 44 q29 ∷
   rw⁻ 45 q14 ∷
   rw 46 q30 ∷
   re 44 3 (ℓ "丧") ∷
   re 46 1 (ℓ "丼丠丼") ∷
   rw 45 q29 ∷
   rw⁻ 46 q14 ∷
   rw 47 q30 ∷
   re 45 3 (ℓ "丧") ∷
   re 47 1 (ℓ "丼丠丼") ∷
   rw 46 q29 ∷
   rw⁻ 47 q14 ∷
   rw 48 q30 ∷
   re 46 3 (ℓ "丧") ∷
   re 48 1 (ℓ "丼丠丼") ∷
   rw 47 q29 ∷
   rw⁻ 48 q14 ∷
   rw 49 q30 ∷
   re 47 3 (ℓ "丧") ∷
   re 49 1 (ℓ "丼丠丼") ∷
   rw 48 q29 ∷
   rw⁻ 49 q14 ∷
   rw 50 q30 ∷
   re 48 3 (ℓ "丧") ∷
   re 50 1 (ℓ "丼丠丼") ∷
   rw 49 q29 ∷
   rw⁻ 50 q14 ∷
   rw 51 q30 ∷
   re 49 3 (ℓ "丧") ∷
   re 51 1 (ℓ "丼丠丼") ∷
   rw 50 q29 ∷
   rw⁻ 51 q14 ∷
   rw 52 q30 ∷
   re 50 3 (ℓ "丧") ∷
   re 52 1 (ℓ "丼丠丼") ∷
   rw 51 q29 ∷
   rw⁻ 52 q14 ∷
   rw 53 q30 ∷
   re 51 3 (ℓ "丧") ∷
   re 53 1 (ℓ "丼丠丼") ∷
   rw 52 q29 ∷
   rw⁻ 53 q14 ∷
   rw 54 q30 ∷
   re 52 3 (ℓ "丧") ∷
   re 54 1 (ℓ "丼丠丼") ∷
   rw 53 q29 ∷
   rw⁻ 54 q14 ∷
   rw 55 q30 ∷
   re 53 3 (ℓ "丧") ∷
   re 55 1 (ℓ "丼丠丼") ∷
   rw 54 q29 ∷
   rw⁻ 55 q14 ∷
   rw 56 q30 ∷
   re 54 3 (ℓ "丧") ∷
   re 56 1 (ℓ "丼丠丼") ∷
   rw 55 q29 ∷
   rw⁻ 56 q14 ∷
   rw 57 q30 ∷
   re 55 3 (ℓ "丧") ∷
   re 57 1 (ℓ "丼丠丼") ∷
   rw 56 q29 ∷
   rw⁻ 57 q14 ∷
   rw 58 q30 ∷
   re 56 3 (ℓ "丧") ∷
   re 58 1 (ℓ "丼丠丼") ∷
   rw 57 q29 ∷
   rw⁻ 58 q14 ∷
   rw 59 q30 ∷
   re 57 3 (ℓ "丧") ∷
   re 59 1 (ℓ "丼丠丼") ∷
   rw 58 q29 ∷
   rw⁻ 59 q14 ∷
   rw 60 q30 ∷
   re 58 3 (ℓ "丧") ∷
   re 60 1 (ℓ "丼丠丼") ∷
   rw 59 q29 ∷
   rw⁻ 60 q14 ∷
   rw 61 q30 ∷
   re 59 3 (ℓ "丧") ∷
   rw 60 q31 ∷
   rw 61 q31 ∷
   rw 62 q31 ∷
   re 64 1 (ℓ "丼临丼") ∷
   rw 63 q29 ∷
   rw⁻ 64 q12 ∷
   rw 65 q30 ∷
   re 63 3 (ℓ "乄") ∷
   rw 64 q31 ∷
   re 66 1 (ℓ "丼丠丼") ∷
   rw 65 q29 ∷
   rw⁻ 66 q14 ∷
   rw 67 q30 ∷
   re 65 3 (ℓ "丧") ∷
   re 67 1 (ℓ "丼丠丼") ∷
   rw 66 q29 ∷
   rw⁻ 67 q14 ∷
   rw 68 q30 ∷
   re 66 3 (ℓ "丧") ∷
   re 68 1 (ℓ "丼丠丼") ∷
   rw 67 q29 ∷
   rw⁻ 68 q14 ∷
   rw 69 q30 ∷
   re 67 3 (ℓ "丧") ∷
   re 69 1 (ℓ "丼丠丼") ∷
   rw 68 q29 ∷
   rw⁻ 69 q14 ∷
   rw 70 q30 ∷
   re 68 3 (ℓ "丧") ∷
   re 70 1 (ℓ "丼丠丼") ∷
   rw 69 q29 ∷
   rw⁻ 70 q14 ∷
   rw 71 q30 ∷
   re 69 3 (ℓ "丧") ∷
   re 71 1 (ℓ "丼丠丼") ∷
   rw 70 q29 ∷
   rw⁻ 71 q14 ∷
   rw 72 q30 ∷
   re 70 3 (ℓ "丧") ∷
   re 72 1 (ℓ "丼丠丼") ∷
   rw 71 q29 ∷
   rw⁻ 72 q14 ∷
   rw 73 q30 ∷
   re 71 3 (ℓ "丧") ∷
   re 73 1 (ℓ "丼丠丼") ∷
   rw 72 q29 ∷
   rw⁻ 73 q14 ∷
   rw 74 q30 ∷
   re 72 3 (ℓ "丧") ∷
   re 74 1 (ℓ "丼丠丼") ∷
   rw 73 q29 ∷
   rw⁻ 74 q14 ∷
   rw 75 q30 ∷
   re 73 3 (ℓ "丧") ∷
   rw 74 q31 ∷
   rw 75 q31 ∷
   rw 76 q31 ∷
   re 78 1 (ℓ "丼临丼") ∷
   rw 77 q29 ∷
   rw⁻ 78 q12 ∷
   rw 79 q30 ∷
   re 77 3 (ℓ "乄") ∷
   rw 78 q31 ∷
   rw 79 q31 ∷
   rw 80 q31 ∷
   rw 81 q31 ∷
   re 83 1 (ℓ "丼临丼") ∷
   rw 82 q29 ∷
   rw⁻ 83 q12 ∷
   rw 84 q30 ∷
   re 82 3 (ℓ "乄") ∷
   rw 83 q31 ∷
   rw 27 q32 ∷
   re 27 1 (ℓ "丼丠丼") ∷
   rw 26 q29 ∷
   rw⁻ 27 q14 ∷
   rw 28 q30 ∷
   re 26 3 (ℓ "丧") ∷
   re 28 1 (ℓ "丼丠丼") ∷
   rw 27 q29 ∷
   rw⁻ 28 q14 ∷
   rw 29 q30 ∷
   re 27 3 (ℓ "丧") ∷
   re 29 1 (ℓ "丼丠丼") ∷
   rw 28 q29 ∷
   rw⁻ 29 q14 ∷
   rw 30 q30 ∷
   re 28 3 (ℓ "丧") ∷
   re 30 1 (ℓ "丼丠丼") ∷
   rw 29 q29 ∷
   rw⁻ 30 q14 ∷
   rw 31 q30 ∷
   re 29 3 (ℓ "丧") ∷
   re 31 1 (ℓ "丼丠丼") ∷
   rw 30 q29 ∷
   rw⁻ 31 q14 ∷
   rw 32 q30 ∷
   re 30 3 (ℓ "丧") ∷
   re 32 1 (ℓ "丼丠丼") ∷
   rw 31 q29 ∷
   rw⁻ 32 q14 ∷
   rw 33 q30 ∷
   re 31 3 (ℓ "丧") ∷
   re 33 1 (ℓ "丼丠丼") ∷
   rw 32 q29 ∷
   rw⁻ 33 q14 ∷
   rw 34 q30 ∷
   re 32 3 (ℓ "丧") ∷
   re 34 1 (ℓ "丼丠丼") ∷
   rw 33 q29 ∷
   rw⁻ 34 q14 ∷
   rw 35 q30 ∷
   re 33 3 (ℓ "丧") ∷
   re 35 1 (ℓ "丼丠丼") ∷
   rw 34 q29 ∷
   rw⁻ 35 q14 ∷
   rw 36 q30 ∷
   re 34 3 (ℓ "丧") ∷
   re 36 1 (ℓ "丼丠丼") ∷
   rw 35 q29 ∷
   rw⁻ 36 q14 ∷
   rw 37 q30 ∷
   re 35 3 (ℓ "丧") ∷
   re 37 1 (ℓ "丼丠丼") ∷
   rw 36 q29 ∷
   rw⁻ 37 q14 ∷
   rw 38 q30 ∷
   re 36 3 (ℓ "丧") ∷
   re 38 1 (ℓ "丼丠丼") ∷
   rw 37 q29 ∷
   rw⁻ 38 q14 ∷
   rw 39 q30 ∷
   re 37 3 (ℓ "丧") ∷
   re 39 1 (ℓ "丼丠丼") ∷
   rw 38 q29 ∷
   rw⁻ 39 q14 ∷
   rw 40 q30 ∷
   re 38 3 (ℓ "丧") ∷
   re 40 1 (ℓ "丼丠丼") ∷
   rw 39 q29 ∷ []) Eq.refl
