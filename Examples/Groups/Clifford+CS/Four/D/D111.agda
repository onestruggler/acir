{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D111 (W : Ws) where

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
  q2 = wE 13 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q4 : Eqn
  q4 = wE 78 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "乆业") (ℓ "业乆") (low₃-comm ((CX₁₀ ↑)) (S))
  q7 : Eqn
  q7 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q8 : Eqn
  q8 = wE 464 W
  q9 : Eqn
  q9 = eqn (ℓ "丠乏") (ℓ "乏丠") (low-comm (CS) (Swap))
  q10 : Eqn
  q10 = eqn (ℓ "与乏") (ℓ "乏与") (low-comm ((S ↑)) (Swap))
  q11 : Eqn
  q11 = eqn (ℓ "临乏") (ℓ "乏临") (low-comm (CK₁₀) (Swap))
  q12 : Eqn
  q12 = wE 663 W
  q13 : Eqn
  q13 = wE 151 W
  q14 : Eqn
  q14 = wE 5 W
  q15 : Eqn
  q15 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))

-- Bar(SSSKSS;2,1->0) passes groups of WBar(KiKiSSSKiSSSSSS;~2,3->0) part1: 500 steps
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part1 : ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中乆乏丼丠丼乏业业业乑业业业业乑业丠丠丠临丠丠丘乌丘乑业乑业中中中乑业中中中中中中") ⟫ʷ ≈ ⟪ (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧丧乄丧丧中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乏乄乏並业並乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乌丘乑业乑业中中中乑业中中中中中中") ⟫ʷ
lem-Bar⟨SSSKSS21-⟶0⟩-passes-groups-of-WBar⟨KiKiSSSKiSSSSSS~23-⟶0⟩-part1 = derive (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧丧乄丧丧乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中乆乏丼丠丼乏业业业乑业业业业乑业丠丠丠临丠丠丘乌丘乑业乑业中中中乑业中中中中中中") (ℓ "丘乄且乄且丧丧丧乄且丧丧丧丧丧丧丘丘乌丘丧丧丧乄丧丧中中中中中中中中中中中中中中中中中中业业业乑业中中中中中中中中中业业业乑业业业业乏乄乏並业並乆丠丠丠丠丠丠临与丠丠丠丠丠丠丠丠丠乆丠丠丠临丠丠丘乌丘乑业乑业中中中乑业中中中中中中")
  (rw 75 q1 ∷
   re 76 3 (ℓ "乓") ∷
   rw 76 q2 ∷
   rw⁻ 77 q3 ∷
   rw 78 q4 ∷
   re 79 1 (ℓ "乏乆乏") ∷
   rw 81 q5 ∷
   re 75 5 (ℓ "中") ∷
   rw 76 q6 ∷
   rw 77 q6 ∷
   rw 78 q6 ∷
   re 80 1 (ℓ "乏丼临丼乏") ∷
   rw 79 q1 ∷
   re 80 3 (ℓ "乓") ∷
   rw 80 q2 ∷
   rw⁻ 81 q7 ∷
   rw 82 q4 ∷
   re 83 1 (ℓ "乏乆乏") ∷
   rw 85 q5 ∷
   re 79 5 (ℓ "乑") ∷
   rw 80 q6 ∷
   rw 81 q6 ∷
   rw 82 q6 ∷
   rw 83 q6 ∷
   re 85 1 (ℓ "乏丼临丼乏") ∷
   rw 84 q1 ∷
   re 85 3 (ℓ "乓") ∷
   rw 85 q2 ∷
   rw⁻ 86 q7 ∷
   rw 87 q4 ∷
   re 88 1 (ℓ "乏乆乏") ∷
   rw 90 q5 ∷
   re 84 5 (ℓ "乑") ∷
   rw 85 q6 ∷
   rw 86 q1 ∷
   rw 85 q8 ∷
   re 84 1 (ℓ "乏乄乏") ∷
   rw 86 q5 ∷
   rw 83 q8 ∷
   rw 82 q8 ∷
   rw 81 q8 ∷
   rw 80 q8 ∷
   re 79 1 (ℓ "乏乄乏") ∷
   rw 81 q5 ∷
   rw 78 q8 ∷
   rw 77 q8 ∷
   rw 76 q8 ∷
   re 75 1 (ℓ "乏丧乏") ∷
   rw 77 q5 ∷
   re 74 1 (ℓ "乏丧乏") ∷
   rw 76 q5 ∷
   re 73 1 (ℓ "乏丧乏") ∷
   rw 75 q5 ∷
   re 72 1 (ℓ "乏丧乏") ∷
   rw 74 q5 ∷
   re 71 1 (ℓ "乏丧乏") ∷
   rw 73 q5 ∷
   re 70 1 (ℓ "乏丧乏") ∷
   rw 72 q5 ∷
   re 69 1 (ℓ "乏丧乏") ∷
   rw 71 q5 ∷
   re 68 1 (ℓ "乏丧乏") ∷
   rw 70 q5 ∷
   re 67 1 (ℓ "乏丧乏") ∷
   rw 69 q5 ∷
   rw 66 q8 ∷
   re 65 1 (ℓ "乏乄乏") ∷
   rw 67 q5 ∷
   rw 64 q8 ∷
   rw 63 q8 ∷
   rw 62 q8 ∷
   re 61 1 (ℓ "乏丧乏") ∷
   rw 63 q5 ∷
   re 60 1 (ℓ "乏丧乏") ∷
   rw 62 q5 ∷
   re 59 1 (ℓ "乏丧乏") ∷
   rw 61 q5 ∷
   re 58 1 (ℓ "乏丧乏") ∷
   rw 60 q5 ∷
   re 57 1 (ℓ "乏丧乏") ∷
   rw 59 q5 ∷
   re 56 1 (ℓ "乏丧乏") ∷
   rw 58 q5 ∷
   re 55 1 (ℓ "乏丧乏") ∷
   rw 57 q5 ∷
   re 54 1 (ℓ "乏丧乏") ∷
   rw 56 q5 ∷
   re 53 1 (ℓ "乏丧乏") ∷
   rw 55 q5 ∷
   re 52 1 (ℓ "乏丧乏") ∷
   rw 54 q5 ∷
   re 51 1 (ℓ "乏丧乏") ∷
   rw 53 q5 ∷
   re 50 1 (ℓ "乏丧乏") ∷
   rw 52 q5 ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q5 ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q5 ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q5 ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q5 ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q5 ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q5 ∷
   rw 43 q9 ∷
   rw 42 q9 ∷
   rw 41 q9 ∷
   rw 40 q9 ∷
   rw 39 q9 ∷
   rw 38 q9 ∷
   rw 37 q9 ∷
   rw 36 q9 ∷
   rw 35 q9 ∷
   rw 34 q10 ∷
   rw 33 q11 ∷
   rw 32 q9 ∷
   rw 31 q9 ∷
   rw 30 q9 ∷
   rw 29 q9 ∷
   rw 28 q9 ∷
   rw 27 q9 ∷
   rw 28 q12 ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "中") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "中") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "中") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "中") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "中") ∷
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
   re 41 3 (ℓ "中") ∷
   rw 44 q1 ∷
   re 42 3 (ℓ "中") ∷
   rw 45 q1 ∷
   re 43 3 (ℓ "中") ∷
   rw 46 q1 ∷
   re 44 3 (ℓ "中") ∷
   rw 45 q13 ∷
   rw 46 q13 ∷
   rw 47 q13 ∷
   rw 50 q1 ∷
   re 48 3 (ℓ "乑") ∷
   rw 49 q13 ∷
   rw 52 q1 ∷
   re 50 3 (ℓ "中") ∷
   rw 53 q1 ∷
   re 51 3 (ℓ "中") ∷
   rw 54 q1 ∷
   re 52 3 (ℓ "中") ∷
   rw 55 q1 ∷
   re 53 3 (ℓ "中") ∷
   rw 56 q1 ∷
   re 54 3 (ℓ "中") ∷
   rw 57 q1 ∷
   re 55 3 (ℓ "中") ∷
   rw 58 q1 ∷
   re 56 3 (ℓ "中") ∷
   rw 59 q1 ∷
   re 57 3 (ℓ "中") ∷
   rw 60 q1 ∷
   re 58 3 (ℓ "中") ∷
   rw 59 q13 ∷
   rw 60 q13 ∷
   rw 61 q13 ∷
   rw 64 q1 ∷
   re 62 3 (ℓ "乑") ∷
   rw 63 q13 ∷
   rw 64 q13 ∷
   rw 65 q13 ∷
   rw 66 q13 ∷
   rw 69 q1 ∷
   re 67 3 (ℓ "乑") ∷
   rw 68 q13 ∷
   rw⁻ 69 q9 ∷
   rw⁻ 70 q9 ∷
   rw⁻ 71 q9 ∷
   rw⁻ 72 q9 ∷
   rw⁻ 73 q9 ∷
   rw⁻ 74 q9 ∷
   rw⁻ 75 q11 ∷
   rw⁻ 76 q10 ∷
   rw⁻ 77 q9 ∷
   rw⁻ 78 q9 ∷
   rw⁻ 79 q9 ∷
   rw⁻ 80 q9 ∷
   rw⁻ 81 q9 ∷
   rw⁻ 82 q9 ∷
   rw⁻ 83 q9 ∷
   rw⁻ 84 q9 ∷
   rw⁻ 85 q9 ∷
   rw 86 q5 ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "乓") ∷
   rw 27 q2 ∷
   rw⁻ 28 q3 ∷
   rw 29 q4 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 32 q5 ∷
   re 26 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "乓") ∷
   rw 28 q2 ∷
   rw⁻ 29 q3 ∷
   rw 30 q4 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 33 q5 ∷
   re 27 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 29 3 (ℓ "乓") ∷
   rw 29 q2 ∷
   rw⁻ 30 q3 ∷
   rw 31 q4 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 34 q5 ∷
   re 28 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "乓") ∷
   rw 30 q2 ∷
   rw⁻ 31 q3 ∷
   rw 32 q4 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 35 q5 ∷
   re 29 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 31 3 (ℓ "乓") ∷
   rw 31 q2 ∷
   rw⁻ 32 q3 ∷
   rw 33 q4 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 36 q5 ∷
   re 30 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q1 ∷
   re 32 3 (ℓ "乓") ∷
   rw 32 q2 ∷
   rw⁻ 33 q3 ∷
   rw 34 q4 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 37 q5 ∷
   re 31 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 33 3 (ℓ "乓") ∷
   rw 33 q2 ∷
   rw⁻ 34 q3 ∷
   rw 35 q4 ∷
   re 36 1 (ℓ "乏乆乏") ∷
   rw 38 q5 ∷
   re 32 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 34 3 (ℓ "乓") ∷
   rw 34 q2 ∷
   rw⁻ 35 q3 ∷
   rw 36 q4 ∷
   re 37 1 (ℓ "乏乆乏") ∷
   rw 39 q5 ∷
   re 33 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q1 ∷
   re 35 3 (ℓ "乓") ∷
   rw 35 q2 ∷
   rw⁻ 36 q3 ∷
   rw 37 q4 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 40 q5 ∷
   re 34 5 (ℓ "中") ∷
   re 36 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q1 ∷
   re 36 3 (ℓ "乓") ∷
   rw 36 q2 ∷
   rw⁻ 37 q3 ∷
   rw 38 q4 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 41 q5 ∷
   re 35 5 (ℓ "中") ∷
   re 37 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 37 3 (ℓ "乓") ∷
   rw 37 q2 ∷
   rw⁻ 38 q3 ∷
   rw 39 q4 ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 42 q5 ∷
   re 36 5 (ℓ "中") ∷
   re 38 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q1 ∷
   re 38 3 (ℓ "乓") ∷
   rw 38 q2 ∷
   rw⁻ 39 q3 ∷
   rw 40 q4 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 43 q5 ∷
   re 37 5 (ℓ "中") ∷
   re 39 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q1 ∷
   re 39 3 (ℓ "乓") ∷
   rw 39 q2 ∷
   rw⁻ 40 q3 ∷
   rw 41 q4 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 44 q5 ∷
   re 38 5 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q1 ∷
   re 40 3 (ℓ "乓") ∷
   rw 40 q2 ∷
   rw⁻ 41 q3 ∷
   rw 42 q4 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 45 q5 ∷
   re 39 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q1 ∷
   re 41 3 (ℓ "乓") ∷
   rw 41 q2 ∷
   rw⁻ 42 q3 ∷
   rw 43 q4 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 46 q5 ∷
   re 40 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 41 q1 ∷
   re 42 3 (ℓ "乓") ∷
   rw 42 q2 ∷
   rw⁻ 43 q3 ∷
   rw 44 q4 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 47 q5 ∷
   re 41 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 42 q1 ∷
   re 43 3 (ℓ "乓") ∷
   rw 43 q2 ∷
   rw⁻ 44 q3 ∷
   rw 45 q4 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 48 q5 ∷
   re 42 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 43 q1 ∷
   re 44 3 (ℓ "乓") ∷
   rw 44 q2 ∷
   rw⁻ 45 q3 ∷
   rw 46 q4 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 49 q5 ∷
   re 43 5 (ℓ "中") ∷
   rw 44 q6 ∷
   rw 45 q6 ∷
   rw 46 q6 ∷
   re 48 1 (ℓ "乏丼临丼乏") ∷
   rw 47 q1 ∷
   re 48 3 (ℓ "乓") ∷
   rw 48 q2 ∷
   rw⁻ 49 q7 ∷
   rw 50 q4 ∷
   re 51 1 (ℓ "乏乆乏") ∷
   rw 53 q5 ∷
   re 47 5 (ℓ "乑") ∷
   rw 48 q6 ∷
   re 50 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q1 ∷
   re 50 3 (ℓ "乓") ∷
   rw 50 q2 ∷
   rw⁻ 51 q3 ∷
   rw 52 q4 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 55 q5 ∷
   re 49 5 (ℓ "中") ∷
   re 51 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q1 ∷
   re 51 3 (ℓ "乓") ∷
   rw 51 q2 ∷
   rw⁻ 52 q3 ∷
   rw 53 q4 ∷
   re 54 1 (ℓ "乏乆乏") ∷
   rw 56 q5 ∷
   re 50 5 (ℓ "中") ∷
   re 52 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q1 ∷
   re 52 3 (ℓ "乓") ∷
   rw 52 q2 ∷
   rw⁻ 53 q3 ∷
   rw 54 q4 ∷
   re 55 1 (ℓ "乏乆乏") ∷
   rw 57 q5 ∷
   re 51 5 (ℓ "中") ∷
   re 53 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q1 ∷
   re 53 3 (ℓ "乓") ∷
   rw 53 q2 ∷
   rw⁻ 54 q3 ∷
   rw 55 q4 ∷
   re 56 1 (ℓ "乏乆乏") ∷
   rw 58 q5 ∷
   re 52 5 (ℓ "中") ∷
   re 54 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q1 ∷
   re 54 3 (ℓ "乓") ∷
   rw 54 q2 ∷
   rw⁻ 55 q3 ∷
   rw 56 q4 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 59 q5 ∷
   re 53 5 (ℓ "中") ∷
   re 55 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q1 ∷
   re 55 3 (ℓ "乓") ∷
   rw 55 q2 ∷
   rw⁻ 56 q3 ∷
   rw 57 q4 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 60 q5 ∷
   re 54 5 (ℓ "中") ∷
   re 56 1 (ℓ "乏丼丠丼乏") ∷
   rw 55 q1 ∷
   re 56 3 (ℓ "乓") ∷
   rw 56 q2 ∷
   rw⁻ 57 q3 ∷
   rw 58 q4 ∷
   re 59 1 (ℓ "乏乆乏") ∷
   rw 61 q5 ∷
   re 55 5 (ℓ "中") ∷
   re 57 1 (ℓ "乏丼丠丼乏") ∷
   rw 56 q1 ∷
   re 57 3 (ℓ "乓") ∷
   rw 57 q2 ∷
   rw⁻ 58 q3 ∷
   rw 59 q4 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 62 q5 ∷
   re 56 5 (ℓ "中") ∷
   re 58 1 (ℓ "乏丼丠丼乏") ∷
   rw 57 q1 ∷
   re 58 3 (ℓ "乓") ∷
   rw 58 q2 ∷
   rw⁻ 59 q3 ∷
   rw 60 q4 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 63 q5 ∷
   re 57 5 (ℓ "中") ∷
   rw 58 q6 ∷
   rw 59 q6 ∷
   rw 60 q6 ∷
   re 62 1 (ℓ "乏丼临丼乏") ∷
   rw 61 q1 ∷
   re 62 3 (ℓ "乓") ∷
   rw 62 q2 ∷
   rw⁻ 63 q7 ∷
   rw 64 q4 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 67 q5 ∷
   re 61 5 (ℓ "乑") ∷
   rw 62 q6 ∷
   rw 63 q6 ∷
   rw 64 q6 ∷
   rw 65 q6 ∷
   re 67 1 (ℓ "乏丼临丼乏") ∷
   rw 66 q1 ∷
   re 67 3 (ℓ "乓") ∷
   rw 67 q2 ∷
   rw⁻ 68 q7 ∷
   rw 69 q4 ∷
   re 70 1 (ℓ "乏乆乏") ∷
   rw 72 q5 ∷
   re 66 5 (ℓ "乑") ∷
   rw 67 q6 ∷
   rw 68 q14 ∷
   rw⁻ 67 q15 ∷
   re 66 1 (ℓ "乏乄乏") ∷ []) Eq.refl
