{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D453 (W : Ws) where

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
  q1 = wE 1 W
  q2 : Eqn
  q2 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q3 : Eqn
  q3 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q4 : Eqn
  q4 = wE 3 W
  q5 : Eqn
  q5 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q6 : Eqn
  q6 = wE 1199 W
  q7 : Eqn
  q7 = wE 151 W
  q8 : Eqn
  q8 = wE 464 W
  q9 : Eqn
  q9 = wE 1200 W

-- respell hyb CS03 CS03 CK30 CS03 CX31 CS01 CS01 CS01  -> CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 : 234 steps
lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- : ⟪ (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ
lem-respell-hyb-CS03-CS03-CK30-CS03-CX31-CS01-CS01-CS01---⟶-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03- = derive (CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ S1 ∷ S1 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX31 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S2 ∷ CK20 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ [])
  (rw 21 q1 ∷
   rw 20 q2 ∷
   rw 19 q3 ∷
   rw 18 q2 ∷
   rw 17 q2 ∷
   re 16 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 18 q4 ∷
   rw 15 q2 ∷
   rw 14 q2 ∷
   rw 13 q2 ∷
   rw 12 q2 ∷
   rw 11 q2 ∷
   rw 10 q2 ∷
   rw 9 q5 ∷
   rw 8 q3 ∷
   rw 7 q2 ∷
   rw 6 q2 ∷
   rw 5 q2 ∷
   re 4 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 6 q4 ∷
   re 3 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 5 q4 ∷
   re 2 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 4 q4 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q4 ∷
   re 0 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 2 q4 ∷
   rw 1 q6 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q2 ∷
   rw⁻ 2 q3 ∷
   rw⁻ 3 q2 ∷
   rw 6 q1 ∷
   re 4 3 (CX13 ∷ []) ∷
   rw 7 q1 ∷
   re 5 3 (CS03 ∷ []) ∷
   rw 8 q1 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 9 q1 ∷
   re 7 3 (CS03 ∷ []) ∷
   rw 10 q1 ∷
   re 8 3 (CK30 ∷ []) ∷
   rw 9 q7 ∷
   rw 12 q1 ∷
   re 10 3 (CS03 ∷ []) ∷
   rw 13 q1 ∷
   re 11 3 (CS03 ∷ []) ∷
   rw 14 q1 ∷
   re 12 3 (CS03 ∷ []) ∷
   rw 15 q1 ∷
   re 13 3 (CS03 ∷ []) ∷
   rw 16 q1 ∷
   re 14 3 (CS03 ∷ []) ∷
   rw 17 q1 ∷
   re 15 3 (CS03 ∷ []) ∷
   rw 18 q1 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CK30 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 21 q4 ∷
   rw 78 q1 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q4 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q4 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q4 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q4 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q4 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q4 ∷
   re 71 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 73 q4 ∷
   rw 70 q8 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q4 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q4 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q4 ∷
   re 66 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 68 q4 ∷
   rw 65 q2 ∷
   rw 64 q2 ∷
   rw 63 q2 ∷
   rw 62 q2 ∷
   rw 61 q2 ∷
   rw 60 q2 ∷
   rw 59 q2 ∷
   rw 58 q2 ∷
   rw 57 q2 ∷
   rw 56 q3 ∷
   rw 55 q5 ∷
   rw 54 q5 ∷
   rw 53 q5 ∷
   rw 52 q5 ∷
   rw 51 q2 ∷
   rw 50 q2 ∷
   rw 49 q2 ∷
   rw 48 q2 ∷
   rw 47 q2 ∷
   rw 46 q2 ∷
   rw 45 q2 ∷
   rw 44 q2 ∷
   rw 43 q2 ∷
   rw 42 q2 ∷
   rw 41 q2 ∷
   rw 40 q2 ∷
   rw 39 q2 ∷
   rw 38 q2 ∷
   rw 37 q2 ∷
   rw 36 q2 ∷
   rw 35 q2 ∷
   rw 34 q2 ∷
   re 33 1 (Sw23 ∷ CX21 ∷ Sw23 ∷ []) ∷
   rw 35 q4 ∷
   rw 32 q2 ∷
   rw 31 q2 ∷
   rw 30 q2 ∷
   rw 29 q2 ∷
   rw 28 q2 ∷
   rw 27 q2 ∷
   rw 26 q3 ∷
   rw 25 q5 ∷
   rw 24 q2 ∷
   rw 23 q2 ∷
   rw 22 q2 ∷
   rw 23 q9 ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q7 ∷
   rw 28 q1 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 29 q1 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q1 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q1 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q1 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q1 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q1 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q1 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q1 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q1 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q1 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q1 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q1 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q1 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q1 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q1 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q1 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 52 q1 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q1 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q7 ∷
   rw 53 q7 ∷
   rw 54 q7 ∷
   rw 55 q7 ∷
   rw 58 q1 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 59 q1 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 60 q1 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 61 q1 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 62 q1 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q1 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q1 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q1 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q1 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CX13 ∷ []) ∷
   rw⁻ 67 q2 ∷
   rw⁻ 68 q2 ∷
   rw⁻ 69 q2 ∷
   rw⁻ 70 q5 ∷
   rw⁻ 71 q3 ∷
   rw⁻ 72 q2 ∷
   rw⁻ 73 q2 ∷
   rw⁻ 74 q2 ∷
   rw⁻ 75 q2 ∷
   rw⁻ 76 q2 ∷
   rw⁻ 77 q2 ∷
   rw 78 q4 ∷ []) Eq.refl
