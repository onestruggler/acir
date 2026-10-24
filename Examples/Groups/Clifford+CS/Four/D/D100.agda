{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D100 (W : Ws) where

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
  q3 = wE 113 W
  q4 : Eqn
  q4 = eqn (ℓ "丠乖") (ℓ "乖丠") (low-comm (CS) (CX₁₀))
  q5 : Eqn
  q5 = wE 114 W
  q6 : Eqn
  q6 = wE 487 W
  q7 : Eqn
  q7 = eqn (ℓ "临乖") (ℓ "乖临") (low-comm (CK₁₀) (CX₁₀))
  q8 : Eqn
  q8 = wE 640 W

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [CX31] part1: 500 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CX31-part1 : ⟪ (ℓ "乑业乑业中中中乑业中中中中中中乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧乏乆中乏丧乄且丧丧丧丧丧丧") ⟫ʷ ≈ ⟪ (ℓ "乑业乑业中中中乑业中中中中中中乖乏乏丧乏乆乏丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧丧丧乄且丧丧丧丧丧丧") ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CX31-part1 = derive (ℓ "乑业乑业中中中乑业中中中中中中乖丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧乏乆中乏丧乄且丧丧丧丧丧丧") (ℓ "乑业乑业中中中乑业中中中中中中乖乏乏丧乏乆乏丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧丧且且且乄且丧丧丧丧丧丧丧丧丧且且且乄且且且且乄且乖乄且乄且丧丧丧乄且丧丧丧丧丧丧")
  (re 66 1 (ℓ "乏丧乏") ∷
   rw 68 q1 ∷
   re 64 3 (ℓ "乓") ∷
   re 64 1 (ℓ "乏乆乏") ∷
   rw 63 q2 ∷
   re 64 3 (ℓ "中") ∷
   re 64 1 (ℓ "乏丼丠丼乏") ∷
   rw 70 q2 ∷
   re 68 3 (ℓ "乓") ∷
   rw 67 q3 ∷
   rw 66 q4 ∷
   rw 65 q5 ∷
   re 65 1 (ℓ "乏乆乏") ∷
   rw 64 q1 ∷
   re 65 5 (ℓ "中") ∷
   re 65 1 (ℓ "乏丧乏") ∷
   rw 67 q1 ∷
   re 63 3 (ℓ "乓") ∷
   rw 62 q6 ∷
   re 62 1 (ℓ "乏乆乏") ∷
   rw 61 q2 ∷
   re 62 3 (ℓ "乑") ∷
   re 62 1 (ℓ "乏丼临丼乏") ∷
   rw 68 q2 ∷
   re 66 3 (ℓ "乓") ∷
   rw 65 q3 ∷
   rw 64 q7 ∷
   rw 63 q5 ∷
   re 63 1 (ℓ "乏乆乏") ∷
   rw 62 q1 ∷
   re 63 5 (ℓ "乑") ∷
   re 63 1 (ℓ "乏乄乏") ∷
   rw 65 q1 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q6 ∷
   re 60 1 (ℓ "乏乆乏") ∷
   rw 59 q2 ∷
   re 60 3 (ℓ "乑") ∷
   re 60 1 (ℓ "乏丼临丼乏") ∷
   rw 66 q2 ∷
   re 64 3 (ℓ "乓") ∷
   rw 63 q3 ∷
   rw 62 q7 ∷
   rw 61 q5 ∷
   re 61 1 (ℓ "乏乆乏") ∷
   rw 60 q1 ∷
   re 61 5 (ℓ "乑") ∷
   re 61 1 (ℓ "乏乄乏") ∷
   rw 63 q1 ∷
   re 59 3 (ℓ "乓") ∷
   rw 58 q8 ∷
   rw 57 q6 ∷
   re 57 1 (ℓ "乏乆乏") ∷
   rw 56 q2 ∷
   re 57 3 (ℓ "乑") ∷
   re 57 1 (ℓ "乏丼临丼乏") ∷
   rw 63 q2 ∷
   re 61 3 (ℓ "乓") ∷
   rw 60 q3 ∷
   rw 59 q7 ∷
   rw 58 q5 ∷
   re 58 1 (ℓ "乏乆乏") ∷
   rw 57 q1 ∷
   re 58 5 (ℓ "乑") ∷
   re 58 1 (ℓ "乏乄乏") ∷
   rw 60 q1 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q6 ∷
   rw 54 q6 ∷
   rw 53 q6 ∷
   rw 52 q6 ∷
   re 52 1 (ℓ "乏乆乏") ∷
   rw 51 q2 ∷
   re 52 3 (ℓ "乑") ∷
   re 52 1 (ℓ "乏丼临丼乏") ∷
   rw 58 q2 ∷
   re 56 3 (ℓ "乓") ∷
   rw 55 q3 ∷
   rw 54 q7 ∷
   rw 53 q5 ∷
   re 53 1 (ℓ "乏乆乏") ∷
   rw 52 q1 ∷
   re 53 5 (ℓ "乑") ∷
   re 53 1 (ℓ "乏乄乏") ∷
   rw 55 q1 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q6 ∷
   rw 49 q6 ∷
   rw 48 q6 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q2 ∷
   re 48 3 (ℓ "中") ∷
   re 48 1 (ℓ "乏丼丠丼乏") ∷
   rw 54 q2 ∷
   re 52 3 (ℓ "乓") ∷
   rw 51 q3 ∷
   rw 50 q4 ∷
   rw 49 q5 ∷
   re 49 1 (ℓ "乏乆乏") ∷
   rw 48 q1 ∷
   re 49 5 (ℓ "中") ∷
   re 49 1 (ℓ "乏丧乏") ∷
   rw 51 q1 ∷
   re 47 3 (ℓ "乓") ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q2 ∷
   re 47 3 (ℓ "中") ∷
   re 47 1 (ℓ "乏丼丠丼乏") ∷
   rw 53 q2 ∷
   re 51 3 (ℓ "乓") ∷
   rw 50 q3 ∷
   rw 49 q4 ∷
   rw 48 q5 ∷
   re 48 1 (ℓ "乏乆乏") ∷
   rw 47 q1 ∷
   re 48 5 (ℓ "中") ∷
   re 48 1 (ℓ "乏丧乏") ∷
   rw 50 q1 ∷
   re 46 3 (ℓ "乓") ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q2 ∷
   re 46 3 (ℓ "中") ∷
   re 46 1 (ℓ "乏丼丠丼乏") ∷
   rw 52 q2 ∷
   re 50 3 (ℓ "乓") ∷
   rw 49 q3 ∷
   rw 48 q4 ∷
   rw 47 q5 ∷
   re 47 1 (ℓ "乏乆乏") ∷
   rw 46 q1 ∷
   re 47 5 (ℓ "中") ∷
   re 47 1 (ℓ "乏丧乏") ∷
   rw 49 q1 ∷
   re 45 3 (ℓ "乓") ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q2 ∷
   re 45 3 (ℓ "中") ∷
   re 45 1 (ℓ "乏丼丠丼乏") ∷
   rw 51 q2 ∷
   re 49 3 (ℓ "乓") ∷
   rw 48 q3 ∷
   rw 47 q4 ∷
   rw 46 q5 ∷
   re 46 1 (ℓ "乏乆乏") ∷
   rw 45 q1 ∷
   re 46 5 (ℓ "中") ∷
   re 46 1 (ℓ "乏丧乏") ∷
   rw 48 q1 ∷
   re 44 3 (ℓ "乓") ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q2 ∷
   re 44 3 (ℓ "中") ∷
   re 44 1 (ℓ "乏丼丠丼乏") ∷
   rw 50 q2 ∷
   re 48 3 (ℓ "乓") ∷
   rw 47 q3 ∷
   rw 46 q4 ∷
   rw 45 q5 ∷
   re 45 1 (ℓ "乏乆乏") ∷
   rw 44 q1 ∷
   re 45 5 (ℓ "中") ∷
   re 45 1 (ℓ "乏丧乏") ∷
   rw 47 q1 ∷
   re 43 3 (ℓ "乓") ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q2 ∷
   re 43 3 (ℓ "中") ∷
   re 43 1 (ℓ "乏丼丠丼乏") ∷
   rw 49 q2 ∷
   re 47 3 (ℓ "乓") ∷
   rw 46 q3 ∷
   rw 45 q4 ∷
   rw 44 q5 ∷
   re 44 1 (ℓ "乏乆乏") ∷
   rw 43 q1 ∷
   re 44 5 (ℓ "中") ∷
   re 44 1 (ℓ "乏丧乏") ∷
   rw 46 q1 ∷
   re 42 3 (ℓ "乓") ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q2 ∷
   re 42 3 (ℓ "中") ∷
   re 42 1 (ℓ "乏丼丠丼乏") ∷
   rw 48 q2 ∷
   re 46 3 (ℓ "乓") ∷
   rw 45 q3 ∷
   rw 44 q4 ∷
   rw 43 q5 ∷
   re 43 1 (ℓ "乏乆乏") ∷
   rw 42 q1 ∷
   re 43 5 (ℓ "中") ∷
   re 43 1 (ℓ "乏丧乏") ∷
   rw 45 q1 ∷
   re 41 3 (ℓ "乓") ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q2 ∷
   re 41 3 (ℓ "中") ∷
   re 41 1 (ℓ "乏丼丠丼乏") ∷
   rw 47 q2 ∷
   re 45 3 (ℓ "乓") ∷
   rw 44 q3 ∷
   rw 43 q4 ∷
   rw 42 q5 ∷
   re 42 1 (ℓ "乏乆乏") ∷
   rw 41 q1 ∷
   re 42 5 (ℓ "中") ∷
   re 42 1 (ℓ "乏丧乏") ∷
   rw 44 q1 ∷
   re 40 3 (ℓ "乓") ∷
   re 40 1 (ℓ "乏乆乏") ∷
   rw 39 q2 ∷
   re 40 3 (ℓ "中") ∷
   re 40 1 (ℓ "乏丼丠丼乏") ∷
   rw 46 q2 ∷
   re 44 3 (ℓ "乓") ∷
   rw 43 q3 ∷
   rw 42 q4 ∷
   rw 41 q5 ∷
   re 41 1 (ℓ "乏乆乏") ∷
   rw 40 q1 ∷
   re 41 5 (ℓ "中") ∷
   re 41 1 (ℓ "乏丧乏") ∷
   rw 43 q1 ∷
   re 39 3 (ℓ "乓") ∷
   rw 38 q6 ∷
   re 38 1 (ℓ "乏乆乏") ∷
   rw 37 q2 ∷
   re 38 3 (ℓ "乑") ∷
   re 38 1 (ℓ "乏丼临丼乏") ∷
   rw 44 q2 ∷
   re 42 3 (ℓ "乓") ∷
   rw 41 q3 ∷
   rw 40 q7 ∷
   rw 39 q5 ∷
   re 39 1 (ℓ "乏乆乏") ∷
   rw 38 q1 ∷
   re 39 5 (ℓ "乑") ∷
   re 39 1 (ℓ "乏乄乏") ∷
   rw 41 q1 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q6 ∷
   rw 35 q6 ∷
   rw 34 q6 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q2 ∷
   re 34 3 (ℓ "中") ∷
   re 34 1 (ℓ "乏丼丠丼乏") ∷
   rw 40 q2 ∷
   re 38 3 (ℓ "乓") ∷
   rw 37 q3 ∷
   rw 36 q4 ∷
   rw 35 q5 ∷
   re 35 1 (ℓ "乏乆乏") ∷
   rw 34 q1 ∷
   re 35 5 (ℓ "中") ∷
   re 35 1 (ℓ "乏丧乏") ∷
   rw 37 q1 ∷
   re 33 3 (ℓ "乓") ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q2 ∷
   re 33 3 (ℓ "中") ∷
   re 33 1 (ℓ "乏丼丠丼乏") ∷
   rw 39 q2 ∷
   re 37 3 (ℓ "乓") ∷
   rw 36 q3 ∷
   rw 35 q4 ∷
   rw 34 q5 ∷
   re 34 1 (ℓ "乏乆乏") ∷
   rw 33 q1 ∷
   re 34 5 (ℓ "中") ∷
   re 34 1 (ℓ "乏丧乏") ∷
   rw 36 q1 ∷
   re 32 3 (ℓ "乓") ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q2 ∷
   re 32 3 (ℓ "中") ∷
   re 32 1 (ℓ "乏丼丠丼乏") ∷
   rw 38 q2 ∷
   re 36 3 (ℓ "乓") ∷
   rw 35 q3 ∷
   rw 34 q4 ∷
   rw 33 q5 ∷
   re 33 1 (ℓ "乏乆乏") ∷
   rw 32 q1 ∷
   re 33 5 (ℓ "中") ∷
   re 33 1 (ℓ "乏丧乏") ∷
   rw 35 q1 ∷
   re 31 3 (ℓ "乓") ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q2 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q2 ∷
   re 35 3 (ℓ "乓") ∷
   rw 34 q3 ∷
   rw 33 q4 ∷
   rw 32 q5 ∷
   re 32 1 (ℓ "乏乆乏") ∷
   rw 31 q1 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q1 ∷
   re 30 3 (ℓ "乓") ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q2 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q2 ∷
   re 34 3 (ℓ "乓") ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   rw 31 q5 ∷
   re 31 1 (ℓ "乏乆乏") ∷
   rw 30 q1 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q1 ∷
   re 29 3 (ℓ "乓") ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q2 ∷
   re 29 3 (ℓ "中") ∷
   re 29 1 (ℓ "乏丼丠丼乏") ∷
   rw 35 q2 ∷
   re 33 3 (ℓ "乓") ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 30 q5 ∷
   re 30 1 (ℓ "乏乆乏") ∷
   rw 29 q1 ∷
   re 30 5 (ℓ "中") ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q1 ∷
   re 28 3 (ℓ "乓") ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q2 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q2 ∷
   re 32 3 (ℓ "乓") ∷
   rw 31 q3 ∷
   rw 30 q4 ∷
   rw 29 q5 ∷
   re 29 1 (ℓ "乏乆乏") ∷
   rw 28 q1 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q1 ∷
   re 27 3 (ℓ "乓") ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q2 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q2 ∷
   re 31 3 (ℓ "乓") ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   rw 28 q5 ∷
   re 28 1 (ℓ "乏乆乏") ∷
   rw 27 q1 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q1 ∷
   re 26 3 (ℓ "乓") ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q2 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q2 ∷
   re 30 3 (ℓ "乓") ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   rw 27 q5 ∷
   re 27 1 (ℓ "乏乆乏") ∷
   rw 26 q1 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q1 ∷
   re 25 3 (ℓ "乓") ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q2 ∷
   re 25 3 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼丠丼乏") ∷
   rw 31 q2 ∷
   re 29 3 (ℓ "乓") ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   rw 26 q5 ∷
   re 26 1 (ℓ "乏乆乏") ∷
   rw 25 q1 ∷
   re 26 5 (ℓ "中") ∷
   re 26 1 (ℓ "乏丧乏") ∷
   rw 28 q1 ∷
   re 24 3 (ℓ "乓") ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q2 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q2 ∷
   re 28 3 (ℓ "乓") ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   rw 25 q5 ∷
   re 25 1 (ℓ "乏乆乏") ∷
   rw 24 q1 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q1 ∷
   re 23 3 (ℓ "乓") ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q2 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q2 ∷
   re 27 3 (ℓ "乓") ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   rw 24 q5 ∷
   re 24 1 (ℓ "乏乆乏") ∷
   rw 23 q1 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q1 ∷
   re 22 3 (ℓ "乓") ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q2 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q2 ∷
   re 26 3 (ℓ "乓") ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   rw 23 q5 ∷
   re 23 1 (ℓ "乏乆乏") ∷
   rw 22 q1 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q1 ∷
   re 21 3 (ℓ "乓") ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q2 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q2 ∷
   re 25 3 (ℓ "乓") ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   rw 22 q5 ∷
   re 22 1 (ℓ "乏乆乏") ∷
   rw 21 q1 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q1 ∷
   re 20 3 (ℓ "乓") ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q2 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q2 ∷
   re 24 3 (ℓ "乓") ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   rw 21 q5 ∷
   re 21 1 (ℓ "乏乆乏") ∷
   rw 20 q1 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q1 ∷
   re 19 3 (ℓ "乓") ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q2 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q2 ∷
   re 23 3 (ℓ "乓") ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   rw 20 q5 ∷
   re 20 1 (ℓ "乏乆乏") ∷
   rw 19 q1 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q1 ∷
   re 18 3 (ℓ "乓") ∷
   re 18 1 (ℓ "乏乆乏") ∷
   rw 17 q2 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q2 ∷
   re 22 3 (ℓ "乓") ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   rw 19 q5 ∷
   re 19 1 (ℓ "乏乆乏") ∷
   rw 18 q1 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q1 ∷
   re 17 3 (ℓ "乓") ∷
   re 17 1 (ℓ "乏乆乏") ∷
   rw 16 q2 ∷ []) Eq.refl
