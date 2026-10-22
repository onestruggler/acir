{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)

module Examples.Groups.Clifford+CS.Four.D.D313 (W : Ws) where

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
  q8 = wE 936 W
  q9 : Eqn
  q9 = wE 151 W

-- pass [CS01 CS01 CS01 CS01 CS01 CS01 CK10 S1 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03] [X1 CKd13 X1]: 311 steps
lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-CKd13-X1 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) ⟫ʷ ≈ ⟪ (X1 ∷ CK13⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CS01-CS01-CS01-CK10-S1-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-vs-X1-CKd13-X1 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ X1 ∷ CK13⁻ ∷ X1 ∷ []) (X1 ∷ CK13⁻ ∷ X1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ S1 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ [])
  (rw 89 q1 ∷
   rw 88 q2 ∷
   re 87 1 (Sw23 ∷ CK12⁻ ∷ Sw23 ∷ []) ∷
   rw 89 q3 ∷
   rw 86 q2 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q3 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q3 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q3 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q3 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q3 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q3 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q3 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q3 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q3 ∷
   rw 76 q4 ∷
   re 75 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 77 q3 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q3 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q3 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q3 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q3 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q3 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q3 ∷
   re 68 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 70 q3 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q3 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q3 ∷
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
   rw 49 q4 ∷
   re 48 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 50 q3 ∷
   rw 47 q4 ∷
   rw 46 q4 ∷
   rw 45 q4 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q3 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q3 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q3 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q3 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q3 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q3 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q3 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q3 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q3 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q3 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q3 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q3 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q3 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q3 ∷
   re 30 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 32 q3 ∷
   re 29 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 31 q3 ∷
   re 28 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 30 q3 ∷
   re 27 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 29 q3 ∷
   re 26 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 28 q3 ∷
   re 25 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 27 q3 ∷
   re 24 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
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
   re 17 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 19 q3 ∷
   rw 16 q5 ∷
   rw 15 q5 ∷
   rw 14 q5 ∷
   rw 13 q5 ∷
   rw 12 q5 ∷
   rw 11 q5 ∷
   rw 10 q5 ∷
   rw 9 q5 ∷
   rw 8 q5 ∷
   rw 7 q6 ∷
   rw 6 q7 ∷
   rw 5 q5 ∷
   rw 4 q5 ∷
   rw 3 q5 ∷
   rw 2 q5 ∷
   rw 1 q5 ∷
   rw 0 q5 ∷
   rw 1 q8 ∷
   rw⁻ 0 q2 ∷
   rw 3 q1 ∷
   re 1 3 (CK13⁻ ∷ []) ∷
   rw⁻ 2 q2 ∷
   rw⁻ 3 q5 ∷
   rw⁻ 4 q5 ∷
   rw⁻ 5 q5 ∷
   rw⁻ 6 q5 ∷
   rw⁻ 7 q5 ∷
   rw⁻ 8 q5 ∷
   rw⁻ 9 q7 ∷
   rw⁻ 10 q6 ∷
   rw⁻ 11 q5 ∷
   rw⁻ 12 q5 ∷
   rw⁻ 13 q5 ∷
   rw⁻ 14 q5 ∷
   rw⁻ 15 q5 ∷
   rw⁻ 16 q5 ∷
   rw⁻ 17 q5 ∷
   rw⁻ 18 q5 ∷
   rw⁻ 19 q5 ∷
   rw 22 q1 ∷
   re 20 3 (CX13 ∷ []) ∷
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
   rw 48 q9 ∷
   rw 49 q9 ∷
   rw 50 q9 ∷
   rw 53 q1 ∷
   re 51 3 (CK30 ∷ []) ∷
   rw 52 q9 ∷
   rw 55 q1 ∷
   re 53 3 (CS03 ∷ []) ∷
   rw 56 q1 ∷
   re 54 3 (CS03 ∷ []) ∷
   rw 57 q1 ∷
   re 55 3 (CS03 ∷ []) ∷
   rw 58 q1 ∷
   re 56 3 (CS03 ∷ []) ∷
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
   re 66 3 (CS03 ∷ []) ∷
   rw 69 q1 ∷
   re 67 3 (CS03 ∷ []) ∷
   rw 70 q1 ∷
   re 68 3 (CS03 ∷ []) ∷
   rw 71 q1 ∷
   re 69 3 (CS03 ∷ []) ∷
   rw 72 q1 ∷
   re 70 3 (CS03 ∷ []) ∷
   rw 73 q1 ∷
   re 71 3 (CX13 ∷ []) ∷
   rw 74 q1 ∷
   re 72 3 (CS03 ∷ []) ∷
   rw 75 q1 ∷
   re 73 3 (CS03 ∷ []) ∷
   rw 76 q1 ∷
   re 74 3 (CS03 ∷ []) ∷
   rw 77 q1 ∷
   re 75 3 (CS03 ∷ []) ∷
   rw 78 q1 ∷
   re 76 3 (CS03 ∷ []) ∷
   rw 79 q1 ∷
   re 77 3 (CS03 ∷ []) ∷
   rw 80 q1 ∷
   re 78 3 (CK30 ∷ []) ∷
   rw 79 q9 ∷
   rw 82 q1 ∷
   re 80 3 (CS03 ∷ []) ∷
   rw 83 q1 ∷
   re 81 3 (CS03 ∷ []) ∷
   rw 84 q1 ∷
   re 82 3 (CS03 ∷ []) ∷
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
   rw 89 q3 ∷ []) Eq.refl
