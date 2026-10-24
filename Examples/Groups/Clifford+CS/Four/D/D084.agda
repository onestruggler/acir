{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D084 (W : Ws) where

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
  q2 = eqn (ℓ "乆业") (ℓ "业乆") (low₃-comm ((CX₁₀ ↑)) (S))
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = wE 13 W
  q5 : Eqn
  q5 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q6 : Eqn
  q6 = wE 78 W
  q7 : Eqn
  q7 = wE 464 W
  q8 : Eqn
  q8 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q9 : Eqn
  q9 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q11 : Eqn
  q11 = wE 615 W
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q16 : Eqn
  q16 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q17 : Eqn
  q17 = wE 140 W

-- Bar(SSKSKK;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part1: 500 steps
lem-Bar⟨SSKSKK21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part1 : ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中乏丼丠丼乏乆乏乏业业业乑业业业业乑业丠丠临丠临临丘乌丘乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧乄丧乄乄中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乏乄並乏业业业业乔业並乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乌丘乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-Bar⟨SSKSKK21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part1 = derive (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧乄丧乄乄乆临与临与丠丠丠临与丠丠丠丠丠丠中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中乏丼丠丼乏乆乏乏业业业乑业业业业乑业丠丠临丠临临丘乌丘乑业乑业中中中乑业中中中中中中") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧乄丧乄乄中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乏乄並乏业业业业乔业並乆临与临与丠丠丠临与丠丠丠丠丠丠乆丠丠临丠临临丘乌丘乑业乑业中中中乑业中中中中中中")
  (rw 79 q1 ∷
   re 73 5 (ℓ "中") ∷
   rw 74 q2 ∷
   rw 75 q2 ∷
   rw 76 q2 ∷
   re 78 1 (ℓ "乏丼临丼乏") ∷
   rw 77 q3 ∷
   re 78 3 (ℓ "乓") ∷
   rw 78 q4 ∷
   rw⁻ 79 q5 ∷
   rw 80 q6 ∷
   re 81 1 (ℓ "乏乆乏") ∷
   rw 83 q1 ∷
   re 77 5 (ℓ "乑") ∷
   rw 78 q2 ∷
   rw 79 q2 ∷
   rw 80 q2 ∷
   rw 81 q2 ∷
   re 83 1 (ℓ "乏丼临丼乏") ∷
   rw 82 q3 ∷
   re 83 3 (ℓ "乓") ∷
   rw 83 q4 ∷
   rw⁻ 84 q5 ∷
   rw 85 q6 ∷
   re 86 1 (ℓ "乏乆乏") ∷
   rw 88 q1 ∷
   re 82 5 (ℓ "乑") ∷
   rw 83 q2 ∷
   rw 84 q3 ∷
   rw 83 q7 ∷
   re 82 1 (ℓ "乏乄乏") ∷
   rw 84 q1 ∷
   rw 81 q7 ∷
   rw 80 q7 ∷
   rw 79 q7 ∷
   rw 78 q7 ∷
   re 77 1 (ℓ "乏乄乏") ∷
   rw 79 q1 ∷
   rw 76 q7 ∷
   rw 75 q7 ∷
   rw 74 q7 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q1 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q1 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q1 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q1 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q1 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q1 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q1 ∷
   re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q1 ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q1 ∷
   rw 64 q7 ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw 65 q1 ∷
   rw 62 q7 ∷
   rw 61 q7 ∷
   rw 60 q7 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q1 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q1 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q1 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q1 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q1 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q1 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q1 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q1 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q1 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q1 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q1 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q1 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q1 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q1 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q1 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q1 ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q1 ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q1 ∷
   rw 41 q8 ∷
   rw 40 q8 ∷
   rw 39 q8 ∷
   rw 38 q8 ∷
   rw 37 q8 ∷
   rw 36 q8 ∷
   rw 35 q9 ∷
   rw 34 q10 ∷
   rw 33 q8 ∷
   rw 32 q8 ∷
   rw 31 q8 ∷
   rw 30 q9 ∷
   rw 29 q10 ∷
   rw 28 q9 ∷
   rw 27 q10 ∷
   rw 28 q11 ∷
   rw 29 q3 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q3 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q3 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q3 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q3 ∷
   re 31 3 (ℓ "中") ∷
   rw 34 q3 ∷
   re 32 3 (ℓ "中") ∷
   rw 35 q3 ∷
   re 33 3 (ℓ "中") ∷
   rw 36 q3 ∷
   re 34 3 (ℓ "中") ∷
   rw 37 q3 ∷
   re 35 3 (ℓ "中") ∷
   rw 38 q3 ∷
   re 36 3 (ℓ "中") ∷
   rw 39 q3 ∷
   re 37 3 (ℓ "中") ∷
   rw 40 q3 ∷
   re 38 3 (ℓ "中") ∷
   rw 41 q3 ∷
   re 39 3 (ℓ "中") ∷
   rw 42 q3 ∷
   re 40 3 (ℓ "中") ∷
   rw 43 q3 ∷
   re 41 3 (ℓ "中") ∷
   rw 44 q3 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q3 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q3 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q12 ∷
   rw 46 q12 ∷
   rw 47 q12 ∷
   rw 50 q3 ∷
   re 48 3 (ℓ "乑") ∷
   rw 49 q12 ∷
   rw 52 q3 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q3 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q3 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q3 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q3 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q3 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q3 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q3 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q3 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q12 ∷
   rw 60 q12 ∷
   rw 61 q12 ∷
   rw 64 q3 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q12 ∷
   rw 64 q12 ∷
   rw 65 q12 ∷
   rw 66 q12 ∷
   rw 69 q3 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q12 ∷
   rw⁻ 69 q10 ∷
   rw⁻ 70 q9 ∷
   rw⁻ 71 q10 ∷
   rw⁻ 72 q9 ∷
   rw⁻ 73 q8 ∷
   rw⁻ 74 q8 ∷
   rw⁻ 75 q8 ∷
   rw⁻ 76 q10 ∷
   rw⁻ 77 q9 ∷
   rw⁻ 78 q8 ∷
   rw⁻ 79 q8 ∷
   rw⁻ 80 q8 ∷
   rw⁻ 81 q8 ∷
   rw⁻ 82 q8 ∷
   rw⁻ 83 q8 ∷
   rw 84 q1 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q3 ∷
   re 27 3 (ℓ "乓") ∷
   rw 27 q4 ∷
   rw⁻ 28 q13 ∷
   rw 29 q6 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 32 q1 ∷
   re 26 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q3 ∷
   re 28 3 (ℓ "乓") ∷
   rw 28 q4 ∷
   rw⁻ 29 q13 ∷
   rw 30 q6 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 33 q1 ∷
   re 27 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q3 ∷
   re 29 3 (ℓ "乓") ∷
   rw 29 q4 ∷
   rw⁻ 30 q13 ∷
   rw 31 q6 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 34 q1 ∷
   re 28 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q3 ∷
   re 30 3 (ℓ "乓") ∷
   rw 30 q4 ∷
   rw⁻ 31 q13 ∷
   rw 32 q6 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 35 q1 ∷
   re 29 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q3 ∷
   re 31 3 (ℓ "乓") ∷
   rw 31 q4 ∷
   rw⁻ 32 q13 ∷
   rw 33 q6 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 36 q1 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q3 ∷
   re 32 3 (ℓ "乓") ∷
   rw 32 q4 ∷
   rw⁻ 33 q13 ∷
   rw 34 q6 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 37 q1 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q3 ∷
   re 33 3 (ℓ "乓") ∷
   rw 33 q4 ∷
   rw⁻ 34 q13 ∷
   rw 35 q6 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 38 q1 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q3 ∷
   re 34 3 (ℓ "乓") ∷
   rw 34 q4 ∷
   rw⁻ 35 q13 ∷
   rw 36 q6 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 39 q1 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q3 ∷
   re 35 3 (ℓ "乓") ∷
   rw 35 q4 ∷
   rw⁻ 36 q13 ∷
   rw 37 q6 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 40 q1 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q3 ∷
   re 36 3 (ℓ "乓") ∷
   rw 36 q4 ∷
   rw⁻ 37 q13 ∷
   rw 38 q6 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 41 q1 ∷
   re 35 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q3 ∷
   re 37 3 (ℓ "乓") ∷
   rw 37 q4 ∷
   rw⁻ 38 q13 ∷
   rw 39 q6 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 42 q1 ∷
   re 36 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q3 ∷
   re 38 3 (ℓ "乓") ∷
   rw 38 q4 ∷
   rw⁻ 39 q13 ∷
   rw 40 q6 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 43 q1 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q3 ∷
   re 39 3 (ℓ "乓") ∷
   rw 39 q4 ∷
   rw⁻ 40 q13 ∷
   rw 41 q6 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 44 q1 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q3 ∷
   re 40 3 (ℓ "乓") ∷
   rw 40 q4 ∷
   rw⁻ 41 q13 ∷
   rw 42 q6 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 45 q1 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q3 ∷
   re 41 3 (ℓ "乓") ∷
   rw 41 q4 ∷
   rw⁻ 42 q13 ∷
   rw 43 q6 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 46 q1 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q3 ∷
   re 42 3 (ℓ "乓") ∷
   rw 42 q4 ∷
   rw⁻ 43 q13 ∷
   rw 44 q6 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 47 q1 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q3 ∷
   re 43 3 (ℓ "乓") ∷
   rw 43 q4 ∷
   rw⁻ 44 q13 ∷
   rw 45 q6 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q1 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q3 ∷
   re 44 3 (ℓ "乓") ∷
   rw 44 q4 ∷
   rw⁻ 45 q13 ∷
   rw 46 q6 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 49 q1 ∷
   re 43 5 (ℓ "中") ∷
   rw 44 q2 ∷
   rw 45 q2 ∷
   rw 46 q2 ∷
   re 48 1 (ℓ "乏丼临丼乏") ∷
   rw 47 q3 ∷
   re 48 3 (ℓ "乓") ∷
   rw 48 q4 ∷
   rw⁻ 49 q5 ∷
   rw 50 q6 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 53 q1 ∷
   re 47 5 (ℓ "乑") ∷
   rw 48 q2 ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q3 ∷
   re 50 3 (ℓ "乓") ∷
   rw 50 q4 ∷
   rw⁻ 51 q13 ∷
   rw 52 q6 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 55 q1 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q3 ∷
   re 51 3 (ℓ "乓") ∷
   rw 51 q4 ∷
   rw⁻ 52 q13 ∷
   rw 53 q6 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 56 q1 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q3 ∷
   re 52 3 (ℓ "乓") ∷
   rw 52 q4 ∷
   rw⁻ 53 q13 ∷
   rw 54 q6 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 57 q1 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q3 ∷
   re 53 3 (ℓ "乓") ∷
   rw 53 q4 ∷
   rw⁻ 54 q13 ∷
   rw 55 q6 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 58 q1 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q3 ∷
   re 54 3 (ℓ "乓") ∷
   rw 54 q4 ∷
   rw⁻ 55 q13 ∷
   rw 56 q6 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 59 q1 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q3 ∷
   re 55 3 (ℓ "乓") ∷
   rw 55 q4 ∷
   rw⁻ 56 q13 ∷
   rw 57 q6 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 60 q1 ∷
   re 54 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q3 ∷
   re 56 3 (ℓ "乓") ∷
   rw 56 q4 ∷
   rw⁻ 57 q13 ∷
   rw 58 q6 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 61 q1 ∷
   re 55 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q3 ∷
   re 57 3 (ℓ "乓") ∷
   rw 57 q4 ∷
   rw⁻ 58 q13 ∷
   rw 59 q6 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 62 q1 ∷
   re 56 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q3 ∷
   re 58 3 (ℓ "乓") ∷
   rw 58 q4 ∷
   rw⁻ 59 q13 ∷
   rw 60 q6 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 63 q1 ∷
   re 57 5 (ℓ "中") ∷
   rw 58 q2 ∷
   rw 59 q2 ∷
   rw 60 q2 ∷
   re 62 1 (ℓ "乏丼临丼乏") ∷
   rw 61 q3 ∷
   re 62 3 (ℓ "乓") ∷
   rw 62 q4 ∷
   rw⁻ 63 q5 ∷
   rw 64 q6 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 67 q1 ∷
   re 61 5 (ℓ "乑") ∷
   rw 62 q2 ∷
   rw 63 q2 ∷
   rw 64 q2 ∷
   rw 65 q2 ∷
   re 67 1 (ℓ "乏丼临丼乏") ∷
   rw 66 q3 ∷
   re 67 3 (ℓ "乓") ∷
   rw 67 q4 ∷
   rw⁻ 68 q5 ∷
   rw 69 q6 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 72 q1 ∷
   re 66 5 (ℓ "乑") ∷
   rw 67 q2 ∷
   rw 68 q14 ∷
   rw⁻ 67 q15 ∷
   re 66 1 (ℓ "乏乄乏") ∷
   rw⁻ 68 q16 ∷
   rw 67 q17 ∷
   rw⁻ 66 q16 ∷
   re 67 3 (ℓ "乔") ∷
   rw⁻ 65 q15 ∷
   rw⁻ 64 q15 ∷
   rw⁻ 63 q15 ∷
   rw⁻ 62 q15 ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw⁻ 63 q16 ∷ []) Eq.refl
