{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D332 (W : Ws) where

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
  q2 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q3 : Eqn
  q3 = wE 3 W
  q4 : Eqn
  q4 = wE 464 W
  q5 : Eqn
  q5 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q6 : Eqn
  q6 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q8 : Eqn
  q8 = wE 955 W
  q9 : Eqn
  q9 = wE 151 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X1 CK10 S1 CK10 S1 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 S3 S3 S3 CK30 S3 CX13 CK30 S3 CK30 S3 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 X1]: 353 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-X1 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X1-CK10-S1-CK10-S1-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-S3-S3-S3-CK30-S3-CX13-CK30-S3-CK30-S3-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-X1 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ []) (X1 ∷ CK10 ∷ S1 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CX13 ∷ CK30 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 107 q1 ∷
   rw 106 q2 ∷
   re 105 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 107 q3 ∷
   re 104 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 106 q3 ∷
   re 103 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 105 q3 ∷
   re 102 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 104 q3 ∷
   re 101 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 103 q3 ∷
   re 100 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 102 q3 ∷
   rw 99 q4 ∷
   re 98 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 100 q3 ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 99 q3 ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 98 q3 ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q3 ∷
   rw 94 q4 ∷
   re 93 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 95 q3 ∷
   rw 92 q4 ∷
   re 91 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 93 q3 ∷
   re 90 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 92 q3 ∷
   rw 89 q4 ∷
   re 88 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 90 q3 ∷
   rw 87 q4 ∷
   rw 86 q4 ∷
   rw 85 q4 ∷
   rw 84 q4 ∷
   re 83 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   rw 82 q4 ∷
   rw 81 q4 ∷
   rw 80 q4 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q3 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   rw 70 q4 ∷
   re 69 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   rw 68 q4 ∷
   rw 67 q4 ∷
   rw 66 q4 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q3 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q3 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q3 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q3 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q3 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q3 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q3 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q3 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q3 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q3 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q3 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q3 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q3 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q3 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q3 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q3 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q3 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   re 47 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 49 q3 ∷
   rw 46 q5 ∷
   rw 45 q5 ∷
   rw 44 q5 ∷
   rw 43 q5 ∷
   rw 42 q5 ∷
   rw 41 q5 ∷
   rw 40 q6 ∷
   rw 39 q7 ∷
   rw 38 q5 ∷
   rw 37 q5 ∷
   rw 36 q5 ∷
   rw 35 q6 ∷
   rw 34 q7 ∷
   rw 33 q6 ∷
   rw 32 q7 ∷
   rw 31 q2 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 28 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 24 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 26 q3 ∷
   re 23 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 25 q3 ∷
   re 22 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 24 q3 ∷
   re 21 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 23 q3 ∷
   re 20 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 22 q3 ∷
   re 19 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 21 q3 ∷
   re 18 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 20 q3 ∷
   re 17 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   re 16 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 18 q3 ∷
   re 15 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 17 q3 ∷
   rw 14 q4 ∷
   re 13 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 15 q3 ∷
   re 12 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 14 q3 ∷
   re 11 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 13 q3 ∷
   re 10 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 12 q3 ∷
   re 9 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 11 q3 ∷
   re 8 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 10 q3 ∷
   re 7 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 9 q3 ∷
   re 6 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 8 q3 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q7 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw⁻ 1 q7 ∷
   rw⁻ 2 q6 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 4 q6 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q7 ∷
   rw⁻ 9 q6 ∷
   rw⁻ 10 q5 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q5 ∷
   rw 18 q1 ∷
   re 16 3 (CX13 ∷ []) ∷
   rw 19 q1 ∷
   re 17 3 (CS03 ∷ []) ∷
   rw 20 q1 ∷
   re 18 3 (CS03 ∷ []) ∷
   rw 21 q1 ∷
   re 19 3 (CS03 ∷ []) ∷
   rw 22 q1 ∷
   re 20 3 (CS03 ∷ []) ∷
   rw 23 q1 ∷
   re 21 3 (CS03 ∷ []) ∷
   rw 24 q1 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q1 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q1 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 27 q1 ∷
   re 25 3 (CS03 ∷ []) ∷
   rw 28 q1 ∷
   re 26 3 (CS03 ∷ []) ∷
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
   re 33 3 (CS03 ∷ []) ∷
   rw 36 q1 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 35 q9 ∷
   rw 36 q9 ∷
   rw 37 q9 ∷
   rw 40 q1 ∷
   re 38 3 (CK30 ∷ []) ∷
   rw 39 q9 ∷
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
   rw 49 q9 ∷
   rw 50 q9 ∷
   rw 51 q9 ∷
   rw 54 q1 ∷
   re 52 3 (CK30 ∷ []) ∷
   rw 53 q9 ∷
   rw 54 q9 ∷
   rw 55 q9 ∷
   rw 56 q9 ∷
   rw 59 q1 ∷
   re 57 3 (CK30 ∷ []) ∷
   rw 58 q9 ∷
   rw 61 q1 ∷
   re 59 3 (CX13 ∷ []) ∷
   rw 62 q1 ∷
   re 60 3 (CK30 ∷ []) ∷
   rw 61 q9 ∷
   rw 64 q1 ∷
   re 62 3 (CK30 ∷ []) ∷
   rw 63 q9 ∷
   rw 66 q1 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q1 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q1 ∷
   re 66 3 (CS03 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CK30 ∷ []) ∷
   rw 68 q9 ∷
   rw 71 q1 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 72 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CS03 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw⁻ 75 q2 ∷
   rw⁻ 76 q5 ∷
   rw⁻ 77 q5 ∷
   rw⁻ 78 q5 ∷
   rw⁻ 79 q7 ∷
   rw⁻ 80 q5 ∷
   rw⁻ 81 q5 ∷
   rw 84 q1 ∷
   re 82 3 (CX13 ∷ []) ∷
   rw 85 q1 ∷
   re 83 3 (CS03 ∷ []) ∷
   rw 86 q1 ∷
   re 84 3 (CS03 ∷ []) ∷
   rw 87 q1 ∷
   re 85 3 (CS03 ∷ []) ∷
   rw 88 q1 ∷
   re 86 3 (CS03 ∷ []) ∷
   rw 89 q1 ∷
   re 87 3 (CS03 ∷ []) ∷
   rw 90 q1 ∷
   re 88 3 (CS03 ∷ []) ∷
   rw 91 q1 ∷
   re 89 3 (CK30 ∷ []) ∷
   rw 90 q9 ∷
   rw 93 q1 ∷
   re 91 3 (CS03 ∷ []) ∷
   rw 94 q1 ∷
   re 92 3 (CS03 ∷ []) ∷
   rw 95 q1 ∷
   re 93 3 (CS03 ∷ []) ∷
   rw 96 q1 ∷
   re 94 3 (CS03 ∷ []) ∷
   rw 97 q1 ∷
   re 95 3 (CS03 ∷ []) ∷
   rw 98 q1 ∷
   re 96 3 (CS03 ∷ []) ∷
   rw 99 q1 ∷
   re 97 3 (CS03 ∷ []) ∷
   rw 100 q1 ∷
   re 98 3 (CS03 ∷ []) ∷
   rw 101 q1 ∷
   re 99 3 (CS03 ∷ []) ∷
   rw 102 q1 ∷
   re 100 3 (CX13 ∷ []) ∷
   rw 103 q1 ∷
   re 101 3 (CS03 ∷ []) ∷
   rw 104 q1 ∷
   re 102 3 (CS03 ∷ []) ∷
   rw 105 q1 ∷
   re 103 3 (CS03 ∷ []) ∷
   rw 106 q1 ∷
   re 104 3 (CK30 ∷ []) ∷
   rw 107 q1 ∷
   re 105 3 (CS03 ∷ []) ∷
   rw 108 q1 ∷
   re 106 3 (CS03 ∷ []) ∷
   rw 107 q3 ∷ []) Eq.refl
