{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D093 (W : Ws) where

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
  q2 = eqn (Sw01 ∷ Sw23 ∷ []) (Sw23 ∷ Sw01 ∷ []) (low-comm (Swap) (Swap))
  q3 : Eqn
  q3 = wE 7 W
  q4 : Eqn
  q4 = eqn (Sw01 ∷ S3 ∷ []) (S3 ∷ Sw01 ∷ []) (low-comm (Swap) ((S ↑)))
  q5 : Eqn
  q5 = wE 140 W
  q6 : Eqn
  q6 = eqn (Sw01 ∷ CX23 ∷ []) (CX23 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₀₁))
  q7 : Eqn
  q7 = eqn (Sw01 ∷ S2 ∷ []) (S2 ∷ Sw01 ∷ []) (low-comm (Swap) (S))
  q8 : Eqn
  q8 = wE 633 W
  q9 : Eqn
  q9 = wE 142 W
  q10 : Eqn
  q10 = wE 27 W
  q11 : Eqn
  q11 = eqn (Sw01 ∷ CX32 ∷ []) (CX32 ∷ Sw01 ∷ []) (low-comm (Swap) (CX₁₀))
  q12 : Eqn
  q12 = wE 31 W
  q13 : Eqn
  q13 = wE 1 W
  q14 : Eqn
  q14 = wE 107 W
  q15 : Eqn
  q15 = eqn (CS01 ∷ CZ23 ∷ []) (CZ23 ∷ CS01 ∷ []) (low-comm (CS) (CZ))
  q16 : Eqn
  q16 = wE 108 W
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = wE 622 W
  q19 : Eqn
  q19 = eqn (CK10 ∷ CZ23 ∷ []) (CZ23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (CZ))

-- pass [CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX23 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX23 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03] [CZ13] part0: 500 steps
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CZ13-part0 : ⟪ (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CZ13 ∷ []) ⟫ʷ ≈ ⟪ (CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw23 ∷ CZ12 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ []) ⟫ʷ
lem-pass-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX23-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX23-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-vs-CZ13-part0 = derive (CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX23 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX23 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CZ13 ∷ []) (CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX32 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ S2 ∷ S2 ∷ S2 ∷ CK20 ∷ S2 ∷ CX32 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ Sw23 ∷ CZ12 ∷ CS03 ∷ Sw23 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ [])
  (rw 74 q1 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 75 q2 ∷
   rw 74 q3 ∷
   rw⁻ 73 q2 ∷
   re 74 3 (CS13 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 74 q2 ∷
   rw 73 q3 ∷
   rw⁻ 72 q2 ∷
   re 73 3 (CS13 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 73 q2 ∷
   rw 72 q3 ∷
   rw⁻ 71 q2 ∷
   re 72 3 (CS13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 72 q2 ∷
   rw 71 q3 ∷
   rw⁻ 70 q2 ∷
   re 71 3 (CS13 ∷ []) ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 71 q2 ∷
   rw 70 q3 ∷
   rw⁻ 69 q2 ∷
   re 70 3 (CS13 ∷ []) ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 70 q2 ∷
   rw 69 q3 ∷
   rw⁻ 68 q2 ∷
   re 69 3 (CS13 ∷ []) ∷
   rw⁻ 67 q4 ∷
   re 66 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 68 q2 ∷
   rw 67 q5 ∷
   rw⁻ 66 q2 ∷
   re 67 3 (CK31 ∷ []) ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 67 q2 ∷
   rw 66 q3 ∷
   rw⁻ 65 q2 ∷
   re 66 3 (CS13 ∷ []) ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 66 q2 ∷
   rw 65 q3 ∷
   rw⁻ 64 q2 ∷
   re 65 3 (CS13 ∷ []) ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 65 q2 ∷
   rw 64 q3 ∷
   rw⁻ 63 q2 ∷
   re 64 3 (CS13 ∷ []) ∷
   rw⁻ 62 q4 ∷
   re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 63 q2 ∷
   rw 62 q5 ∷
   rw⁻ 61 q2 ∷
   re 62 3 (CK31 ∷ []) ∷
   rw⁻ 60 q4 ∷
   re 59 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 61 q2 ∷
   rw 60 q5 ∷
   rw⁻ 59 q2 ∷
   re 60 3 (CK31 ∷ []) ∷
   rw⁻ 58 q6 ∷
   rw⁻ 57 q4 ∷
   re 56 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 58 q2 ∷
   rw 57 q5 ∷
   rw⁻ 56 q2 ∷
   re 57 3 (CK31 ∷ []) ∷
   rw⁻ 55 q4 ∷
   rw⁻ 54 q4 ∷
   rw⁻ 53 q4 ∷
   rw⁻ 52 q4 ∷
   re 51 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 53 q2 ∷
   rw 52 q5 ∷
   rw⁻ 51 q2 ∷
   re 52 3 (CK31 ∷ []) ∷
   rw⁻ 50 q4 ∷
   rw⁻ 49 q4 ∷
   rw⁻ 48 q4 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 49 q2 ∷
   rw 48 q3 ∷
   rw⁻ 47 q2 ∷
   re 48 3 (CS13 ∷ []) ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 48 q2 ∷
   rw 47 q3 ∷
   rw⁻ 46 q2 ∷
   re 47 3 (CS13 ∷ []) ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 47 q2 ∷
   rw 46 q3 ∷
   rw⁻ 45 q2 ∷
   re 46 3 (CS13 ∷ []) ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 46 q2 ∷
   rw 45 q3 ∷
   rw⁻ 44 q2 ∷
   re 45 3 (CS13 ∷ []) ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 45 q2 ∷
   rw 44 q3 ∷
   rw⁻ 43 q2 ∷
   re 44 3 (CS13 ∷ []) ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 44 q2 ∷
   rw 43 q3 ∷
   rw⁻ 42 q2 ∷
   re 43 3 (CS13 ∷ []) ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 43 q2 ∷
   rw 42 q3 ∷
   rw⁻ 41 q2 ∷
   re 42 3 (CS13 ∷ []) ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 42 q2 ∷
   rw 41 q3 ∷
   rw⁻ 40 q2 ∷
   re 41 3 (CS13 ∷ []) ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 41 q2 ∷
   rw 40 q3 ∷
   rw⁻ 39 q2 ∷
   re 40 3 (CS13 ∷ []) ∷
   rw⁻ 38 q4 ∷
   re 37 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw⁻ 39 q2 ∷
   rw 38 q5 ∷
   rw⁻ 37 q2 ∷
   re 38 3 (CK31 ∷ []) ∷
   rw⁻ 36 q4 ∷
   rw⁻ 35 q4 ∷
   rw⁻ 34 q4 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 35 q2 ∷
   rw 34 q3 ∷
   rw⁻ 33 q2 ∷
   re 34 3 (CS13 ∷ []) ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 34 q2 ∷
   rw 33 q3 ∷
   rw⁻ 32 q2 ∷
   re 33 3 (CS13 ∷ []) ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 33 q2 ∷
   rw 32 q3 ∷
   rw⁻ 31 q2 ∷
   re 32 3 (CS13 ∷ []) ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 32 q2 ∷
   rw 31 q3 ∷
   rw⁻ 30 q2 ∷
   re 31 3 (CS13 ∷ []) ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 31 q2 ∷
   rw 30 q3 ∷
   rw⁻ 29 q2 ∷
   re 30 3 (CS13 ∷ []) ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 30 q2 ∷
   rw 29 q3 ∷
   rw⁻ 28 q2 ∷
   re 29 3 (CS13 ∷ []) ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 29 q2 ∷
   rw 28 q3 ∷
   rw⁻ 27 q2 ∷
   re 28 3 (CS13 ∷ []) ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 28 q2 ∷
   rw 27 q3 ∷
   rw⁻ 26 q2 ∷
   re 27 3 (CS13 ∷ []) ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 27 q2 ∷
   rw 26 q3 ∷
   rw⁻ 25 q2 ∷
   re 26 3 (CS13 ∷ []) ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 26 q2 ∷
   rw 25 q3 ∷
   rw⁻ 24 q2 ∷
   re 25 3 (CS13 ∷ []) ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 25 q2 ∷
   rw 24 q3 ∷
   rw⁻ 23 q2 ∷
   re 24 3 (CS13 ∷ []) ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 24 q2 ∷
   rw 23 q3 ∷
   rw⁻ 22 q2 ∷
   re 23 3 (CS13 ∷ []) ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 23 q2 ∷
   rw 22 q3 ∷
   rw⁻ 21 q2 ∷
   re 22 3 (CS13 ∷ []) ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 22 q2 ∷
   rw 21 q3 ∷
   rw⁻ 20 q2 ∷
   re 21 3 (CS13 ∷ []) ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 21 q2 ∷
   rw 20 q3 ∷
   rw⁻ 19 q2 ∷
   re 20 3 (CS13 ∷ []) ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 20 q2 ∷
   rw 19 q3 ∷
   rw⁻ 18 q2 ∷
   re 19 3 (CS13 ∷ []) ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 19 q2 ∷
   rw 18 q3 ∷
   rw⁻ 17 q2 ∷
   re 18 3 (CS13 ∷ []) ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw⁻ 18 q2 ∷
   rw 17 q3 ∷
   rw⁻ 16 q2 ∷
   re 17 3 (CS13 ∷ []) ∷
   rw⁻ 15 q6 ∷
   rw 14 q3 ∷
   rw 13 q3 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q3 ∷
   rw 9 q3 ∷
   rw⁻ 8 q7 ∷
   rw 7 q5 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   rw 4 q3 ∷
   rw⁻ 3 q7 ∷
   rw 2 q5 ∷
   rw⁻ 1 q7 ∷
   rw 0 q5 ∷
   rw 1 q8 ∷
   re 1 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 0 q2 ∷
   rw 1 q9 ∷
   rw 2 q2 ∷
   re 0 3 (CK30 ∷ []) ∷
   rw 1 q4 ∷
   re 3 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 2 q2 ∷
   rw 3 q9 ∷
   rw 4 q2 ∷
   re 2 3 (CK30 ∷ []) ∷
   rw 3 q4 ∷
   re 5 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 4 q2 ∷
   rw 5 q10 ∷
   rw 6 q2 ∷
   re 4 3 (CS03 ∷ []) ∷
   re 6 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 5 q2 ∷
   rw 6 q10 ∷
   rw 7 q2 ∷
   re 5 3 (CS03 ∷ []) ∷
   re 7 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 6 q2 ∷
   rw 7 q10 ∷
   rw 8 q2 ∷
   re 6 3 (CS03 ∷ []) ∷
   re 8 1 (Sw23 ∷ CK21 ∷ Sw23 ∷ []) ∷
   rw 7 q2 ∷
   rw 8 q9 ∷
   rw 9 q2 ∷
   re 7 3 (CK30 ∷ []) ∷
   rw 8 q4 ∷
   re 10 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 9 q2 ∷
   rw 10 q10 ∷
   rw 11 q2 ∷
   re 9 3 (CS03 ∷ []) ∷
   re 11 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 10 q2 ∷
   rw 11 q10 ∷
   rw 12 q2 ∷
   re 10 3 (CS03 ∷ []) ∷
   re 12 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 11 q2 ∷
   rw 12 q10 ∷
   rw 13 q2 ∷
   re 11 3 (CS03 ∷ []) ∷
   re 13 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 12 q2 ∷
   rw 13 q10 ∷
   rw 14 q2 ∷
   re 12 3 (CS03 ∷ []) ∷
   re 14 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 13 q2 ∷
   rw 14 q10 ∷
   rw 15 q2 ∷
   re 13 3 (CS03 ∷ []) ∷
   re 15 1 (Sw23 ∷ CS12 ∷ Sw23 ∷ []) ∷
   rw 14 q2 ∷
   rw 15 q10 ∷
   rw 16 q2 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 15 q11 ∷
   rw 16 q10 ∷
   rw 17 q10 ∷
   rw 18 q10 ∷
   rw 19 q10 ∷
   rw 20 q10 ∷
   rw 21 q10 ∷
   rw 22 q10 ∷
   rw 23 q10 ∷
   rw 24 q10 ∷
   rw 25 q10 ∷
   rw 26 q10 ∷
   rw 27 q10 ∷
   rw 28 q10 ∷
   rw 29 q10 ∷
   rw 30 q10 ∷
   rw 31 q10 ∷
   rw 32 q10 ∷
   rw 33 q10 ∷
   rw 34 q7 ∷
   rw 35 q7 ∷
   rw 36 q7 ∷
   rw 37 q9 ∷
   rw 38 q7 ∷
   rw 39 q10 ∷
   rw 40 q10 ∷
   rw 41 q10 ∷
   rw 42 q10 ∷
   rw 43 q10 ∷
   rw 44 q10 ∷
   rw 45 q10 ∷
   rw 46 q10 ∷
   rw 47 q10 ∷
   rw 48 q7 ∷
   rw 49 q7 ∷
   rw 50 q7 ∷
   rw 51 q9 ∷
   rw 52 q7 ∷
   rw 53 q7 ∷
   rw 54 q7 ∷
   rw 55 q7 ∷
   rw 56 q9 ∷
   rw 57 q7 ∷
   rw 58 q11 ∷
   rw 59 q9 ∷
   rw 60 q7 ∷
   rw 61 q9 ∷
   rw 62 q7 ∷
   rw 63 q10 ∷
   rw 64 q10 ∷
   rw 65 q10 ∷
   rw 66 q9 ∷
   rw 67 q7 ∷
   rw 68 q10 ∷
   rw 69 q10 ∷
   rw 70 q10 ∷
   rw 71 q10 ∷
   rw 72 q10 ∷
   rw 73 q10 ∷
   rw 74 q12 ∷
   re 74 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 73 q13 ∷
   re 74 3 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 80 q13 ∷
   re 78 3 (CZ13 ∷ []) ∷
   rw 77 q14 ∷
   rw 76 q15 ∷
   rw 75 q16 ∷
   re 75 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 74 q17 ∷
   re 75 5 (CS03 ∷ []) ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q17 ∷
   re 73 3 (CZ13 ∷ []) ∷
   re 73 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 72 q13 ∷
   re 73 3 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 79 q13 ∷
   re 77 3 (CZ13 ∷ []) ∷
   rw 76 q14 ∷
   rw 75 q15 ∷
   rw 74 q16 ∷
   re 74 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 73 q17 ∷
   re 74 5 (CS03 ∷ []) ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q17 ∷
   re 72 3 (CZ13 ∷ []) ∷
   re 72 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 71 q13 ∷
   re 72 3 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 78 q13 ∷
   re 76 3 (CZ13 ∷ []) ∷
   rw 75 q14 ∷
   rw 74 q15 ∷
   rw 73 q16 ∷
   re 73 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 72 q17 ∷
   re 73 5 (CS03 ∷ []) ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q17 ∷
   re 71 3 (CZ13 ∷ []) ∷
   re 71 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 70 q13 ∷
   re 71 3 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 77 q13 ∷
   re 75 3 (CZ13 ∷ []) ∷
   rw 74 q14 ∷
   rw 73 q15 ∷
   rw 72 q16 ∷
   re 72 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 71 q17 ∷
   re 72 5 (CS03 ∷ []) ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q17 ∷
   re 70 3 (CZ13 ∷ []) ∷
   re 70 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 69 q13 ∷
   re 70 3 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 76 q13 ∷
   re 74 3 (CZ13 ∷ []) ∷
   rw 73 q14 ∷
   rw 72 q15 ∷
   rw 71 q16 ∷
   re 71 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 70 q17 ∷
   re 71 5 (CS03 ∷ []) ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q17 ∷
   re 69 3 (CZ13 ∷ []) ∷
   re 69 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 68 q13 ∷
   re 69 3 (CS03 ∷ []) ∷
   re 69 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 75 q13 ∷
   re 73 3 (CZ13 ∷ []) ∷
   rw 72 q14 ∷
   rw 71 q15 ∷
   rw 70 q16 ∷
   re 70 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 69 q17 ∷
   re 70 5 (CS03 ∷ []) ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q17 ∷
   re 68 3 (CZ13 ∷ []) ∷
   rw 67 q18 ∷
   re 67 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 66 q13 ∷
   re 67 3 (CK30 ∷ []) ∷
   re 67 1 (Sw23 ∷ Sw12 ∷ CK10 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 73 q13 ∷
   re 71 3 (CZ13 ∷ []) ∷
   rw 70 q14 ∷
   rw 69 q19 ∷
   rw 68 q16 ∷
   re 68 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 67 q17 ∷
   re 68 5 (CK30 ∷ []) ∷
   re 68 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 70 q17 ∷
   re 66 3 (CZ13 ∷ []) ∷
   re 66 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 65 q13 ∷
   re 66 3 (CS03 ∷ []) ∷
   re 66 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 72 q13 ∷
   re 70 3 (CZ13 ∷ []) ∷
   rw 69 q14 ∷
   rw 68 q15 ∷
   rw 67 q16 ∷
   re 67 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 66 q17 ∷
   re 67 5 (CS03 ∷ []) ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q17 ∷
   re 65 3 (CZ13 ∷ []) ∷
   re 65 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 64 q13 ∷
   re 65 3 (CS03 ∷ []) ∷
   re 65 1 (Sw23 ∷ Sw12 ∷ CS01 ∷ Sw12 ∷ Sw23 ∷ []) ∷
   rw 71 q13 ∷
   re 69 3 (CZ13 ∷ []) ∷
   rw 68 q14 ∷
   rw 67 q15 ∷
   rw 66 q16 ∷
   re 66 1 (Sw23 ∷ CZ12 ∷ Sw23 ∷ []) ∷
   rw 65 q17 ∷
   re 66 5 (CS03 ∷ []) ∷ []) Eq.refl
