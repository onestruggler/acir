{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D121 (W : Ws) where

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
  q3 = eqn (ℓ "临乊") (ℓ "乊临") (low-comm (CK₁₀) ((CS • CS • CS)))
  q4 : Eqn
  q4 = wE 51 W
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = eqn (ℓ "丠乊") (ℓ "乊丠") (low-comm (CS) ((CS • CS • CS)))
  q7 : Eqn
  q7 = wE 525 W
  q8 : Eqn
  q8 = eqn (ℓ "丷业") (ℓ "业丷") (low₃-comm (((CS • CS • CS) ↑)) (S))
  q9 : Eqn
  q9 = wE 526 W
  q10 : Eqn
  q10 = wE 527 W

-- pass [CS02 CS02 CK20 CS02 CK20 CK20 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX23 CS03 CS03 CK30 CS03 CK30 CK30] [CSd12]: 173 steps
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CSd12 : ⟪ (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丷") ⟫ʷ ≈ ⟪ (ℓ "丷丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑") ⟫ʷ
lem-pass-CS02-CS02-CK20-CS02-CK20-CK20-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX23-CS03-CS03-CK30-CS03-CK30-CK30-vs-CSd12 = derive (ℓ "丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑丷") (ℓ "丷丧丧乄丧乄乄乌乑业乑业中中中乑业中中中中中中乌中中乑中乑乑")
  (re 28 1 (ℓ "乏丼临丼乏") ∷
   rw 34 q1 ∷
   re 32 3 (ℓ "举") ∷
   rw 31 q2 ∷
   rw 30 q3 ∷
   rw 29 q4 ∷
   re 29 1 (ℓ "乏丷乏") ∷
   rw 28 q5 ∷
   re 29 5 (ℓ "乑") ∷
   re 27 1 (ℓ "乏丼临丼乏") ∷
   rw 33 q1 ∷
   re 31 3 (ℓ "举") ∷
   rw 30 q2 ∷
   rw 29 q3 ∷
   rw 28 q4 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 27 q5 ∷
   re 28 5 (ℓ "乑") ∷
   re 26 1 (ℓ "乏丼丠丼乏") ∷
   rw 32 q1 ∷
   re 30 3 (ℓ "举") ∷
   rw 29 q2 ∷
   rw 28 q6 ∷
   rw 27 q4 ∷
   re 27 1 (ℓ "乏丷乏") ∷
   rw 26 q5 ∷
   re 27 5 (ℓ "中") ∷
   re 25 1 (ℓ "乏丼临丼乏") ∷
   rw 31 q1 ∷
   re 29 3 (ℓ "举") ∷
   rw 28 q2 ∷
   rw 27 q3 ∷
   rw 26 q4 ∷
   re 26 1 (ℓ "乏丷乏") ∷
   rw 25 q5 ∷
   re 26 5 (ℓ "乑") ∷
   re 24 1 (ℓ "乏丼丠丼乏") ∷
   rw 30 q1 ∷
   re 28 3 (ℓ "举") ∷
   rw 27 q2 ∷
   rw 26 q6 ∷
   rw 25 q4 ∷
   re 25 1 (ℓ "乏丷乏") ∷
   rw 24 q5 ∷
   re 25 5 (ℓ "中") ∷
   re 23 1 (ℓ "乏丼丠丼乏") ∷
   rw 29 q1 ∷
   re 27 3 (ℓ "举") ∷
   rw 26 q2 ∷
   rw 25 q6 ∷
   rw 24 q4 ∷
   re 24 1 (ℓ "乏丷乏") ∷
   rw 23 q5 ∷
   re 24 5 (ℓ "中") ∷
   rw 22 q7 ∷
   re 21 1 (ℓ "乏丼丠丼乏") ∷
   rw 27 q1 ∷
   re 25 3 (ℓ "举") ∷
   rw 24 q2 ∷
   rw 23 q6 ∷
   rw 22 q4 ∷
   re 22 1 (ℓ "乏丷乏") ∷
   rw 21 q5 ∷
   re 22 5 (ℓ "中") ∷
   re 20 1 (ℓ "乏丼丠丼乏") ∷
   rw 26 q1 ∷
   re 24 3 (ℓ "举") ∷
   rw 23 q2 ∷
   rw 22 q6 ∷
   rw 21 q4 ∷
   re 21 1 (ℓ "乏丷乏") ∷
   rw 20 q5 ∷
   re 21 5 (ℓ "中") ∷
   re 19 1 (ℓ "乏丼丠丼乏") ∷
   rw 25 q1 ∷
   re 23 3 (ℓ "举") ∷
   rw 22 q2 ∷
   rw 21 q6 ∷
   rw 20 q4 ∷
   re 20 1 (ℓ "乏丷乏") ∷
   rw 19 q5 ∷
   re 20 5 (ℓ "中") ∷
   re 18 1 (ℓ "乏丼丠丼乏") ∷
   rw 24 q1 ∷
   re 22 3 (ℓ "举") ∷
   rw 21 q2 ∷
   rw 20 q6 ∷
   rw 19 q4 ∷
   re 19 1 (ℓ "乏丷乏") ∷
   rw 18 q5 ∷
   re 19 5 (ℓ "中") ∷
   re 17 1 (ℓ "乏丼丠丼乏") ∷
   rw 23 q1 ∷
   re 21 3 (ℓ "举") ∷
   rw 20 q2 ∷
   rw 19 q6 ∷
   rw 18 q4 ∷
   re 18 1 (ℓ "乏丷乏") ∷
   rw 17 q5 ∷
   re 18 5 (ℓ "中") ∷
   re 16 1 (ℓ "乏丼丠丼乏") ∷
   rw 22 q1 ∷
   re 20 3 (ℓ "举") ∷
   rw 19 q2 ∷
   rw 18 q6 ∷
   rw 17 q4 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 16 q5 ∷
   re 17 5 (ℓ "中") ∷
   rw⁻ 15 q8 ∷
   re 14 1 (ℓ "乏丼临丼乏") ∷
   rw 20 q1 ∷
   re 18 3 (ℓ "举") ∷
   rw 17 q2 ∷
   rw 16 q3 ∷
   rw 15 q4 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 14 q5 ∷
   re 15 5 (ℓ "乑") ∷
   re 13 1 (ℓ "乏丼丠丼乏") ∷
   rw 19 q1 ∷
   re 17 3 (ℓ "举") ∷
   rw 16 q2 ∷
   rw 15 q6 ∷
   rw 14 q4 ∷
   re 14 1 (ℓ "乏丷乏") ∷
   rw 13 q5 ∷
   re 14 5 (ℓ "中") ∷
   re 12 1 (ℓ "乏丼丠丼乏") ∷
   rw 18 q1 ∷
   re 16 3 (ℓ "举") ∷
   rw 15 q2 ∷
   rw 14 q6 ∷
   rw 13 q4 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 12 q5 ∷
   re 13 5 (ℓ "中") ∷
   re 11 1 (ℓ "乏丼丠丼乏") ∷
   rw 17 q1 ∷
   re 15 3 (ℓ "举") ∷
   rw 14 q2 ∷
   rw 13 q6 ∷
   rw 12 q4 ∷
   re 12 1 (ℓ "乏丷乏") ∷
   rw 11 q5 ∷
   re 12 5 (ℓ "中") ∷
   rw⁻ 10 q8 ∷
   re 9 1 (ℓ "乏丼临丼乏") ∷
   rw 15 q1 ∷
   re 13 3 (ℓ "举") ∷
   rw 12 q2 ∷
   rw 11 q3 ∷
   rw 10 q4 ∷
   re 10 1 (ℓ "乏丷乏") ∷
   rw 9 q5 ∷
   re 10 5 (ℓ "乑") ∷
   rw⁻ 8 q8 ∷
   re 7 1 (ℓ "乏丼临丼乏") ∷
   rw 13 q1 ∷
   re 11 3 (ℓ "举") ∷
   rw 10 q2 ∷
   rw 9 q3 ∷
   rw 8 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q5 ∷
   re 8 5 (ℓ "乑") ∷
   rw 6 q7 ∷
   rw 5 q9 ∷
   rw 4 q9 ∷
   rw 3 q10 ∷
   rw 2 q9 ∷
   rw 1 q10 ∷
   rw 0 q10 ∷ []) Eq.refl
