{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D257 (W : Ws) where

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
  q2 = wE 21 W
  q3 : Eqn
  q3 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q4 : Eqn
  q4 = wE 51 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q7 : Eqn
  q7 = wE 750 W
  q8 : Eqn
  q8 = wE 211 W
  q9 : Eqn
  q9 = wE 527 W
  q10 : Eqn
  q10 = wE 526 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [CSd13]: 399 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd13 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧举") ⟫ʷ ≈ ⟪ (ℓ "举中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-CSd13 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧举") (ℓ "举中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q1 ∷
   re 31 3 (ℓ "中") ∷
   re 31 1 (ℓ "乏丼丠丼乏") ∷
   rw 37 q1 ∷
   re 35 3 (ℓ "举") ∷
   rw 34 q2 ∷
   rw 33 q3 ∷
   rw 32 q4 ∷
   re 32 1 (ℓ "乏丷乏") ∷
   rw 31 q5 ∷
   re 32 5 (ℓ "中") ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q5 ∷
   re 30 3 (ℓ "举") ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q1 ∷
   re 30 3 (ℓ "中") ∷
   re 30 1 (ℓ "乏丼丠丼乏") ∷
   rw 36 q1 ∷
   re 34 3 (ℓ "举") ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   re 31 1 (ℓ "乏丷乏") ∷
   rw 30 q5 ∷
   re 31 5 (ℓ "中") ∷
   re 31 1 (ℓ "乏丧乏") ∷
   rw 33 q5 ∷
   re 29 3 (ℓ "举") ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q1 ∷
   re 29 3 (ℓ "乑") ∷
   re 29 1 (ℓ "乏丼临丼乏") ∷
   rw 35 q1 ∷
   re 33 3 (ℓ "举") ∷
   rw 32 q2 ∷
   rw 31 q6 ∷
   rw 30 q4 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 29 q5 ∷
   re 30 5 (ℓ "乑") ∷
   re 30 1 (ℓ "乏乄乏") ∷
   rw 32 q5 ∷
   re 28 3 (ℓ "举") ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q1 ∷
   re 28 3 (ℓ "中") ∷
   re 28 1 (ℓ "乏丼丠丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q5 ∷
   re 29 5 (ℓ "中") ∷
   re 29 1 (ℓ "乏丧乏") ∷
   rw 31 q5 ∷
   re 27 3 (ℓ "举") ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q1 ∷
   re 27 3 (ℓ "中") ∷
   re 27 1 (ℓ "乏丼丠丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q5 ∷
   re 28 5 (ℓ "中") ∷
   re 28 1 (ℓ "乏丧乏") ∷
   rw 30 q5 ∷
   re 26 3 (ℓ "举") ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q1 ∷
   re 26 3 (ℓ "中") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q2 ∷
   rw 28 q3 ∷
   rw 27 q4 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q5 ∷
   re 27 5 (ℓ "中") ∷
   re 27 1 (ℓ "乏丧乏") ∷
   rw 29 q5 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q7 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q1 ∷
   re 24 3 (ℓ "中") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q4 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q5 ∷
   re 25 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丧乏") ∷
   rw 27 q5 ∷
   re 23 3 (ℓ "举") ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q1 ∷
   re 23 3 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q2 ∷
   rw 25 q3 ∷
   rw 24 q4 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q5 ∷
   re 24 5 (ℓ "中") ∷
   re 24 1 (ℓ "乏丧乏") ∷
   rw 26 q5 ∷
   re 22 3 (ℓ "举") ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q1 ∷
   re 22 3 (ℓ "中") ∷
   re 22 1 (ℓ "乏丼丠丼乏") ∷
   rw 28 q1 ∷
   re 26 3 (ℓ "举") ∷
   rw 25 q2 ∷
   rw 24 q3 ∷
   rw 23 q4 ∷
   re 23 1 (ℓ "乏丷乏") ∷
   rw 22 q5 ∷
   re 23 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丧乏") ∷
   rw 25 q5 ∷
   re 21 3 (ℓ "举") ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q1 ∷
   re 21 3 (ℓ "中") ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q2 ∷
   rw 23 q3 ∷
   rw 22 q4 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q5 ∷
   re 22 5 (ℓ "中") ∷
   re 22 1 (ℓ "乏丧乏") ∷
   rw 24 q5 ∷
   re 20 3 (ℓ "举") ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q1 ∷
   re 20 3 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q2 ∷
   rw 22 q3 ∷
   rw 21 q4 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q5 ∷
   re 21 5 (ℓ "中") ∷
   re 21 1 (ℓ "乏丧乏") ∷
   rw 23 q5 ∷
   re 19 3 (ℓ "举") ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q1 ∷
   re 19 3 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q2 ∷
   rw 21 q3 ∷
   rw 20 q4 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q5 ∷
   re 20 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丧乏") ∷
   rw 22 q5 ∷
   re 18 3 (ℓ "举") ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q1 ∷
   re 18 3 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q2 ∷
   rw 20 q3 ∷
   rw 19 q4 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q5 ∷
   re 19 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q5 ∷
   re 17 3 (ℓ "举") ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q1 ∷
   re 17 3 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   rw 18 q4 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q5 ∷
   re 18 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丧乏") ∷
   rw 20 q5 ∷
   re 16 3 (ℓ "举") ∷
   re 16 1 (ℓ "乏丷乏") ∷
   rw 15 q1 ∷
   re 16 3 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q2 ∷
   rw 18 q3 ∷
   rw 17 q4 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q5 ∷
   re 17 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q5 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q8 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q1 ∷
   re 14 3 (ℓ "乑") ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q2 ∷
   rw 16 q6 ∷
   rw 15 q4 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q5 ∷
   re 15 5 (ℓ "乑") ∷
   re 15 1 (ℓ "乏乄乏") ∷
   rw 17 q5 ∷
   re 13 3 (ℓ "举") ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q1 ∷
   re 13 3 (ℓ "中") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q2 ∷
   rw 15 q3 ∷
   rw 14 q4 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q5 ∷
   re 14 5 (ℓ "中") ∷
   re 14 1 (ℓ "乏丧乏") ∷
   rw 16 q5 ∷
   re 12 3 (ℓ "举") ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q1 ∷
   re 12 3 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q2 ∷
   rw 14 q3 ∷
   rw 13 q4 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q5 ∷
   re 13 5 (ℓ "中") ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q5 ∷
   re 11 3 (ℓ "举") ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q1 ∷
   re 11 3 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q2 ∷
   rw 13 q3 ∷
   rw 12 q4 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q5 ∷
   re 12 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丧乏") ∷
   rw 14 q5 ∷
   re 10 3 (ℓ "举") ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q1 ∷
   re 10 3 (ℓ "中") ∷
   re 10 1 (ℓ "乏丼丠丼乏") ∷
   rw 16 q1 ∷
   re 14 3 (ℓ "举") ∷
   rw 13 q2 ∷
   rw 12 q3 ∷
   rw 11 q4 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 10 q5 ∷
   re 11 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丧乏") ∷
   rw 13 q5 ∷
   re 9 3 (ℓ "举") ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q1 ∷
   re 9 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丼丠丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q2 ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   re 10 5 (ℓ "中") ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q5 ∷
   re 8 3 (ℓ "举") ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q1 ∷
   re 8 3 (ℓ "中") ∷
   re 8 1 (ℓ "乏丼丠丼乏") ∷
   rw 14 q1 ∷
   re 12 3 (ℓ "举") ∷
   rw 11 q2 ∷
   rw 10 q3 ∷
   rw 9 q4 ∷
   re 9 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   re 9 5 (ℓ "中") ∷
   re 9 1 (ℓ "乏丧乏") ∷
   rw 11 q5 ∷
   re 7 3 (ℓ "举") ∷
   rw 6 q7 ∷
   rw 7 q1 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q5 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q5 ∷
   rw 6 q9 ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "举") ∷
   rw 8 q1 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q5 ∷
   rw 6 q1 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw 6 q5 ∷
   rw 5 q9 ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "举") ∷
   rw 7 q1 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q5 ∷
   rw 5 q1 ∷
   re 4 1 (ℓ "乏丷乏") ∷
   rw 6 q5 ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw 5 q5 ∷
   rw 4 q10 ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "举") ∷
   rw 6 q1 ∷
   re 4 3 (ℓ "乑") ∷
   rw 5 q5 ∷
   rw 4 q1 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q5 ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw 4 q5 ∷
   rw 3 q9 ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "举") ∷
   rw 5 q1 ∷
   re 3 3 (ℓ "中") ∷
   rw 4 q5 ∷
   rw 3 q1 ∷
   re 2 1 (ℓ "乏丷乏") ∷
   rw 4 q5 ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw 3 q5 ∷
   rw 2 q9 ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "举") ∷
   rw 4 q1 ∷
   re 2 3 (ℓ "中") ∷
   rw 3 q5 ∷
   rw 2 q1 ∷
   re 1 1 (ℓ "乏丷乏") ∷
   rw 3 q5 ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw 2 q5 ∷
   rw 1 q9 ∷
   rw 2 q1 ∷
   re 0 3 (ℓ "举") ∷
   rw 3 q1 ∷
   re 1 3 (ℓ "中") ∷
   rw 2 q5 ∷ []) Eq.refl

private
  q11 : Eqn
  q11 = wE 5 W
  q12 : Eqn
  q12 = eqn (ℓ "並丞") (ℓ "丞並") (low-comm (Swap) ((X ↑)))
  q13 : Eqn
  q13 = eqn (ℓ "並乘") (ℓ "乘並") (low-comm (Swap) ((S ↑ • CK₁₀)))
  q14 : Eqn
  q14 = wE 7 W
  q15 : Eqn
  q15 = wE 140 W
  q16 : Eqn
  q16 = eqn (ℓ "並乖") (ℓ "乖並") (low-comm (Swap) (CX₁₀))
  q17 : Eqn
  q17 = eqn (ℓ "並且") (ℓ "且並") (low-comm (Swap) (S))
  q18 : Eqn
  q18 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q19 : Eqn
  q19 = wE 837 W
  q20 : Eqn
  q20 = wE 27 W
  q21 : Eqn
  q21 = wE 142 W
  q22 : Eqn
  q22 = wE 31 W

-- pass [CS03 CS03 CS03 CK30 CS03 CS03 CX32 CS02 CS02 CS02 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CS02 CX32 CS02 CS02 CS02 CK20 CS02 CS02] [X3 CKd32 X3]: 119 steps
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd32-X3 : ⟪ (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乘丞") ⟫ʷ ≈ ⟪ (ℓ "丞乘丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧") ⟫ʷ
lem-pass-CS03-CS03-CS03-CK30-CS03-CS03-CX32-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX32-CS02-CS02-CS02-CK20-CS02-CS02-vs-X3-CKd32-X3 = derive (ℓ "中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧丞乘丞") (ℓ "丞乘丞中中中乑中中乖丧丧丧丧丧丧乄且丧丧丧丧丧丧丧丧丧乖丧丧丧乄丧丧")
  (rw 34 q11 ∷
   rw⁻ 33 q12 ∷
   rw⁻ 32 q13 ∷
   rw⁻ 31 q12 ∷
   rw 30 q14 ∷
   rw 29 q14 ∷
   rw 28 q15 ∷
   rw 27 q14 ∷
   rw 26 q14 ∷
   rw 25 q14 ∷
   rw⁻ 24 q16 ∷
   rw 23 q14 ∷
   rw 22 q14 ∷
   rw 21 q14 ∷
   rw 20 q14 ∷
   rw 19 q14 ∷
   rw 18 q14 ∷
   rw 17 q14 ∷
   rw 16 q14 ∷
   rw 15 q14 ∷
   rw⁻ 14 q17 ∷
   rw 13 q15 ∷
   rw 12 q14 ∷
   rw 11 q14 ∷
   rw 10 q14 ∷
   rw 9 q14 ∷
   rw 8 q14 ∷
   rw 7 q14 ∷
   rw⁻ 6 q16 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q18 ∷
   rw 6 q14 ∷
   rw⁻ 5 q18 ∷
   re 6 3 (ℓ "丽") ∷
   re 4 1 (ℓ "乏丧乏") ∷
   rw⁻ 6 q18 ∷
   rw 5 q14 ∷
   rw⁻ 4 q18 ∷
   re 5 3 (ℓ "丽") ∷
   re 3 1 (ℓ "乏乄乏") ∷
   rw⁻ 5 q18 ∷
   rw 4 q15 ∷
   rw⁻ 3 q18 ∷
   re 4 3 (ℓ "乔") ∷
   re 2 1 (ℓ "乏丧乏") ∷
   rw⁻ 4 q18 ∷
   rw 3 q14 ∷
   rw⁻ 2 q18 ∷
   re 3 3 (ℓ "丽") ∷
   re 1 1 (ℓ "乏丧乏") ∷
   rw⁻ 3 q18 ∷
   rw 2 q14 ∷
   rw⁻ 1 q18 ∷
   re 2 3 (ℓ "丽") ∷
   re 0 1 (ℓ "乏丧乏") ∷
   rw⁻ 2 q18 ∷
   rw 1 q14 ∷
   rw⁻ 0 q18 ∷
   re 1 3 (ℓ "丽") ∷
   rw 1 q19 ∷
   rw 0 q12 ∷
   rw 1 q13 ∷
   rw 2 q12 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 3 q18 ∷
   rw 4 q20 ∷
   rw 5 q18 ∷
   re 3 3 (ℓ "中") ∷
   re 5 1 (ℓ "乏丶乏") ∷
   rw 4 q18 ∷
   rw 5 q20 ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "中") ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q18 ∷
   rw 6 q20 ∷
   rw 7 q18 ∷
   re 5 3 (ℓ "中") ∷
   re 7 1 (ℓ "乏乇乏") ∷
   rw 6 q18 ∷
   rw 7 q21 ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "乑") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 7 q18 ∷
   rw 8 q20 ∷
   rw 9 q18 ∷
   re 7 3 (ℓ "中") ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 8 q18 ∷
   rw 9 q20 ∷
   rw 10 q18 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q16 ∷
   rw 10 q20 ∷
   rw 11 q20 ∷
   rw 12 q20 ∷
   rw 13 q20 ∷
   rw 14 q20 ∷
   rw 15 q20 ∷
   rw 16 q21 ∷
   rw 17 q17 ∷
   rw 18 q20 ∷
   rw 19 q20 ∷
   rw 20 q20 ∷
   rw 21 q20 ∷
   rw 22 q20 ∷
   rw 23 q20 ∷
   rw 24 q20 ∷
   rw 25 q20 ∷
   rw 26 q20 ∷
   rw 27 q16 ∷
   rw 28 q20 ∷
   rw 29 q20 ∷
   rw 30 q20 ∷
   rw 31 q21 ∷
   rw 32 q20 ∷
   rw 33 q20 ∷
   rw 34 q22 ∷ []) Eq.refl
