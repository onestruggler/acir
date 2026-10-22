{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D097 (W : Ws) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)
open import Examples.Groups.Clifford+CS.Syntactics
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Tools using (ax)
open import Examples.Groups.Clifford+CS.LowComm using (low-comm ; low₁-comm)
open import Examples.Groups.Clifford+CS.Four.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Four.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

private
  q1 : Eqn
  q1 = wE 5 W
  q2 : Eqn
  q2 = eqn (Sw01 ∷ CS23 ∷ []) (CS23 ∷ Sw01 ∷ []) (low-comm (Swap) (CS))
  q3 : Eqn
  q3 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q4 : Eqn
  q4 = wE 7 W
  q5 : Eqn
  q5 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q6 : Eqn
  q6 = wE 140 W
  q7 : Eqn
  q7 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q8 : Eqn
  q8 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q9 : Eqn
  q9 = wE 638 W
  q10 : Eqn
  q10 = wE 142 W
  q11 : Eqn
  q11 = wE 27 W
  q12 : Eqn
  q12 = wE 31 W

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [CS23]: 489 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CS23 : ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (CS23 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CS23 = derive (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS23 ∷ []) (CS23 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 75 q1 ∷
   rw⁻ 74 q2 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q3 ∷
   rw 74 q4 ∷
   rw⁻ 73 q3 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q3 ∷
   rw 73 q4 ∷
   rw⁻ 72 q3 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q3 ∷
   rw 72 q4 ∷
   rw⁻ 71 q3 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q3 ∷
   rw 71 q4 ∷
   rw⁻ 70 q3 ∷
   re 71 3 (CS13 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q3 ∷
   rw 70 q4 ∷
   rw⁻ 69 q3 ∷
   re 70 3 (CS13 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q3 ∷
   rw 69 q4 ∷
   rw⁻ 68 q3 ∷
   re 69 3 (CS13 ∷ []) ∷
   rw⁻ 67 q5 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q3 ∷
   rw 67 q6 ∷
   rw⁻ 66 q3 ∷
   re 67 3 (CK31 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q3 ∷
   rw 66 q4 ∷
   rw⁻ 65 q3 ∷
   re 66 3 (CS13 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q3 ∷
   rw 65 q4 ∷
   rw⁻ 64 q3 ∷
   re 65 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q3 ∷
   rw 64 q4 ∷
   rw⁻ 63 q3 ∷
   re 64 3 (CS13 ∷ []) ∷
   rw⁻ 62 q5 ∷
   re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q3 ∷
   rw 62 q6 ∷
   rw⁻ 61 q3 ∷
   re 62 3 (CK31 ∷ []) ∷
   rw⁻ 60 q5 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q3 ∷
   rw 60 q6 ∷
   rw⁻ 59 q3 ∷
   re 60 3 (CK31 ∷ []) ∷
   rw⁻ 58 q7 ∷
   rw⁻ 57 q5 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q3 ∷
   rw 57 q6 ∷
   rw⁻ 56 q3 ∷
   re 57 3 (CK31 ∷ []) ∷
   rw⁻ 55 q5 ∷
   rw⁻ 54 q5 ∷
   rw⁻ 53 q5 ∷
   rw⁻ 52 q5 ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q3 ∷
   rw 52 q6 ∷
   rw⁻ 51 q3 ∷
   re 52 3 (CK31 ∷ []) ∷
   rw⁻ 50 q5 ∷
   rw⁻ 49 q5 ∷
   rw⁻ 48 q5 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q3 ∷
   rw 48 q4 ∷
   rw⁻ 47 q3 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q3 ∷
   rw 47 q4 ∷
   rw⁻ 46 q3 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q3 ∷
   rw 46 q4 ∷
   rw⁻ 45 q3 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q3 ∷
   rw 45 q4 ∷
   rw⁻ 44 q3 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q3 ∷
   rw 44 q4 ∷
   rw⁻ 43 q3 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q3 ∷
   rw 43 q4 ∷
   rw⁻ 42 q3 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q3 ∷
   rw 42 q4 ∷
   rw⁻ 41 q3 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q3 ∷
   rw 41 q4 ∷
   rw⁻ 40 q3 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q3 ∷
   rw 40 q4 ∷
   rw⁻ 39 q3 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw⁻ 38 q5 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q3 ∷
   rw 38 q6 ∷
   rw⁻ 37 q3 ∷
   re 38 3 (CK31 ∷ []) ∷
   rw⁻ 36 q5 ∷
   rw⁻ 35 q5 ∷
   rw⁻ 34 q5 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q3 ∷
   rw 34 q4 ∷
   rw⁻ 33 q3 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q3 ∷
   rw 33 q4 ∷
   rw⁻ 32 q3 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q3 ∷
   rw 32 q4 ∷
   rw⁻ 31 q3 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q3 ∷
   rw 31 q4 ∷
   rw⁻ 30 q3 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q3 ∷
   rw 30 q4 ∷
   rw⁻ 29 q3 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q3 ∷
   rw 29 q4 ∷
   rw⁻ 28 q3 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q3 ∷
   rw 28 q4 ∷
   rw⁻ 27 q3 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q3 ∷
   rw 27 q4 ∷
   rw⁻ 26 q3 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q3 ∷
   rw 26 q4 ∷
   rw⁻ 25 q3 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q3 ∷
   rw 25 q4 ∷
   rw⁻ 24 q3 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q3 ∷
   rw 24 q4 ∷
   rw⁻ 23 q3 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q3 ∷
   rw 23 q4 ∷
   rw⁻ 22 q3 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q3 ∷
   rw 22 q4 ∷
   rw⁻ 21 q3 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q3 ∷
   rw 21 q4 ∷
   rw⁻ 20 q3 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q3 ∷
   rw 20 q4 ∷
   rw⁻ 19 q3 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q3 ∷
   rw 19 q4 ∷
   rw⁻ 18 q3 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q3 ∷
   rw 18 q4 ∷
   rw⁻ 17 q3 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q3 ∷
   rw 17 q4 ∷
   rw⁻ 16 q3 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q7 ∷
   rw 14 q4 ∷
   rw 13 q4 ∷
   rw 12 q4 ∷
   rw 11 q4 ∷
   rw 10 q4 ∷
   rw 9 q4 ∷
   rw⁻ 8 q8 ∷
   rw 7 q6 ∷
   rw 6 q4 ∷
   rw 5 q4 ∷
   rw 4 q4 ∷
   rw⁻ 3 q8 ∷
   rw 2 q6 ∷
   rw⁻ 1 q8 ∷
   rw 0 q6 ∷
   rw 1 q9 ∷
   rw 0 q2 ∷
   rw 1 q10 ∷
   rw 2 q8 ∷
   rw 3 q10 ∷
   rw 4 q8 ∷
   rw 5 q11 ∷
   rw 6 q11 ∷
   rw 7 q11 ∷
   rw 8 q10 ∷
   rw 9 q8 ∷
   rw 10 q11 ∷
   rw 11 q11 ∷
   rw 12 q11 ∷
   rw 13 q11 ∷
   rw 14 q11 ∷
   rw 15 q11 ∷
   rw 16 q7 ∷
   re 18 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 18 q11 ∷
   rw 19 q3 ∷
   re 17 3 (CS03 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   rw 19 q11 ∷
   rw 20 q3 ∷
   re 18 3 (CS03 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 20 q11 ∷
   rw 21 q3 ∷
   re 19 3 (CS03 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   rw 21 q11 ∷
   rw 22 q3 ∷
   re 20 3 (CS03 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   rw 22 q11 ∷
   rw 23 q3 ∷
   re 21 3 (CS03 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   rw 23 q11 ∷
   rw 24 q3 ∷
   re 22 3 (CS03 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   rw 24 q11 ∷
   rw 25 q3 ∷
   re 23 3 (CS03 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   rw 25 q11 ∷
   rw 26 q3 ∷
   re 24 3 (CS03 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   rw 26 q11 ∷
   rw 27 q3 ∷
   re 25 3 (CS03 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   rw 27 q11 ∷
   rw 28 q3 ∷
   re 26 3 (CS03 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   rw 28 q11 ∷
   rw 29 q3 ∷
   re 27 3 (CS03 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   rw 29 q11 ∷
   rw 30 q3 ∷
   re 28 3 (CS03 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   rw 30 q11 ∷
   rw 31 q3 ∷
   re 29 3 (CS03 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   rw 31 q11 ∷
   rw 32 q3 ∷
   re 30 3 (CS03 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   rw 32 q11 ∷
   rw 33 q3 ∷
   re 31 3 (CS03 ∷ []) ∷
   re 33 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   rw 33 q11 ∷
   rw 34 q3 ∷
   re 32 3 (CS03 ∷ []) ∷
   re 34 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   rw 34 q11 ∷
   rw 35 q3 ∷
   re 33 3 (CS03 ∷ []) ∷
   re 35 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   rw 35 q11 ∷
   rw 36 q3 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q5 ∷
   rw 36 q5 ∷
   rw 37 q5 ∷
   re 39 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   rw 39 q10 ∷
   rw 40 q3 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q5 ∷
   re 41 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   rw 41 q11 ∷
   rw 42 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   rw 42 q11 ∷
   rw 43 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   rw 43 q11 ∷
   rw 44 q3 ∷
   re 42 3 (CS03 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   rw 44 q11 ∷
   rw 45 q3 ∷
   re 43 3 (CS03 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   rw 45 q11 ∷
   rw 46 q3 ∷
   re 44 3 (CS03 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   rw 46 q11 ∷
   rw 47 q3 ∷
   re 45 3 (CS03 ∷ []) ∷
   re 47 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   rw 47 q11 ∷
   rw 48 q3 ∷
   re 46 3 (CS03 ∷ []) ∷
   re 48 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 47 q3 ∷
   rw 48 q11 ∷
   rw 49 q3 ∷
   re 47 3 (CS03 ∷ []) ∷
   re 49 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 48 q3 ∷
   rw 49 q11 ∷
   rw 50 q3 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 49 q5 ∷
   rw 50 q5 ∷
   rw 51 q5 ∷
   re 53 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   rw 53 q10 ∷
   rw 54 q3 ∷
   re 52 3 (CK30 ∷ []) ∷
   rw 53 q5 ∷
   rw 54 q5 ∷
   rw 55 q5 ∷
   rw 56 q5 ∷
   re 58 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   rw 58 q10 ∷
   rw 59 q3 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 58 q5 ∷
   rw 59 q7 ∷
   re 61 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 60 q3 ∷
   rw 61 q10 ∷
   rw 62 q3 ∷
   re 60 3 (CK30 ∷ []) ∷
   rw 61 q5 ∷
   re 63 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 62 q3 ∷
   rw 63 q10 ∷
   rw 64 q3 ∷
   re 62 3 (CK30 ∷ []) ∷
   rw 63 q5 ∷
   re 65 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 64 q3 ∷
   rw 65 q11 ∷
   rw 66 q3 ∷
   re 64 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 65 q3 ∷
   rw 66 q11 ∷
   rw 67 q3 ∷
   re 65 3 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 66 q3 ∷
   rw 67 q11 ∷
   rw 68 q3 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 68 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 67 q3 ∷
   rw 68 q10 ∷
   rw 69 q3 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q5 ∷
   re 70 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 69 q3 ∷
   rw 70 q11 ∷
   rw 71 q3 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 70 q3 ∷
   rw 71 q11 ∷
   rw 72 q3 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   rw 72 q11 ∷
   rw 73 q3 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 72 q3 ∷
   rw 73 q11 ∷
   rw 74 q3 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   rw 74 q11 ∷
   rw 75 q3 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   rw 75 q11 ∷
   rw 76 q3 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 75 q12 ∷ []) Eq.refl
