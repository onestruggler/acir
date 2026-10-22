{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD582 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D582 (W : Ws) (Sᴰ : SD582) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 : St 1020
  lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 = pickᴰ 0 Sᴰ

private
  q1 : Eqn
  q1 = wE 1 W
  q2 : Eqn
  q2 = wE 173 W
  q3 : Eqn
  q3 = eqn (X1 ∷ Sw23 ∷ []) (Sw23 ∷ X1 ∷ []) (low-comm ((X ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (X0 ∷ Sw23 ∷ []) (Sw23 ∷ X0 ∷ []) (low₁-comm (X) ((Swap ↑)))
  q5 : Eqn
  q5 = wE 3 W
  q6 : Eqn
  q6 = wE 464 W
  q7 : Eqn
  q7 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q8 : Eqn
  q8 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q9 : Eqn
  q9 = wE 1648 W
  q10 : Eqn
  q10 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q11 : Eqn
  q11 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q12 : Eqn
  q12 = wE 151 W
  q13 : Eqn
  q13 = sE 1020 lem-Bar⟨SSSKSS13-⟶0⟩-passes-factors-of-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3
  q14 : Eqn
  q14 = wE 1649 W
  q15 : Eqn
  q15 = wE 175 W

-- pass [CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03] [X0 X1 X3 CS01 CS01 CS01 CK10 CS01 CS01 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CK30 CS03 CS03 X0 X1 X3]: 469 steps
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 : ⟪ (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-vs-X0-X1-X3-CS01-CS01-CS01-CK10-CS01-CS01-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CK30-CS03-CS03-X0-X1-X3 = derive (CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ []) (X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ X0 ∷ X1 ∷ X3 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CS03 ∷ [])
  (rw 68 q1 ∷
   rw 67 q2 ∷
   rw 66 q3 ∷
   rw 65 q4 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   re 62 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 64 q5 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q5 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q5 ∷
   re 58 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 60 q5 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q5 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q5 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   rw 48 q6 ∷
   re 47 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q5 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 40 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   rw 39 q7 ∷
   rw 38 q7 ∷
   rw 37 q8 ∷
   rw 36 q7 ∷
   rw 35 q7 ∷
   rw 34 q7 ∷
   rw 33 q2 ∷
   rw 32 q3 ∷
   rw 31 q4 ∷
   rw 32 q9 ∷
   rw⁻ 31 q3 ∷
   rw⁻ 32 q8 ∷
   rw⁻ 33 q7 ∷
   rw⁻ 34 q7 ∷
   rw⁻ 35 q10 ∷
   rw⁻ 36 q3 ∷
   rw⁻ 37 q3 ∷
   rw⁻ 38 q7 ∷
   rw⁻ 39 q7 ∷
   rw⁻ 40 q8 ∷
   rw⁻ 41 q7 ∷
   rw⁻ 42 q3 ∷
   rw⁻ 43 q3 ∷
   rw⁻ 44 q7 ∷
   rw⁻ 45 q7 ∷
   rw⁻ 46 q7 ∷
   rw⁻ 47 q7 ∷
   rw⁻ 48 q7 ∷
   rw⁻ 49 q7 ∷
   rw⁻ 50 q8 ∷
   rw⁻ 51 q11 ∷
   rw⁻ 52 q7 ∷
   rw⁻ 53 q7 ∷
   rw⁻ 54 q7 ∷
   rw⁻ 55 q7 ∷
   rw⁻ 56 q7 ∷
   rw⁻ 57 q7 ∷
   rw⁻ 58 q7 ∷
   rw⁻ 59 q7 ∷
   rw⁻ 60 q7 ∷
   rw 63 q1 ∷
   re 61 3 (CX13 ∷ []) ∷
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
   re 71 3 (CS03 ∷ []) ∷
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
   re 78 3 (CS03 ∷ []) ∷
   rw 81 q1 ∷
   re 79 3 (CS03 ∷ []) ∷
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
   rw 89 q12 ∷
   rw 90 q12 ∷
   rw 91 q12 ∷
   rw 94 q1 ∷
   re 92 3 (CK30 ∷ []) ∷
   rw 93 q12 ∷
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
   re 100 3 (CS03 ∷ []) ∷
   rw 103 q1 ∷
   re 101 3 (CS03 ∷ []) ∷
   rw 104 q1 ∷
   re 102 3 (CS03 ∷ []) ∷
   rw 105 q1 ∷
   re 103 3 (CS03 ∷ []) ∷
   rw 106 q1 ∷
   re 104 3 (CS03 ∷ []) ∷
   rw 107 q1 ∷
   re 105 3 (CS03 ∷ []) ∷
   rw 108 q1 ∷
   re 106 3 (CS03 ∷ []) ∷
   rw 109 q1 ∷
   re 107 3 (CS03 ∷ []) ∷
   rw 110 q1 ∷
   re 108 3 (CS03 ∷ []) ∷
   rw 111 q1 ∷
   re 109 3 (CS03 ∷ []) ∷
   rw 112 q1 ∷
   re 110 3 (CS03 ∷ []) ∷
   rw 113 q1 ∷
   re 111 3 (CS03 ∷ []) ∷
   rw 114 q1 ∷
   re 112 3 (CX13 ∷ []) ∷
   rw 115 q1 ∷
   re 113 3 (CS03 ∷ []) ∷
   rw 116 q1 ∷
   re 114 3 (CS03 ∷ []) ∷
   rw 117 q1 ∷
   re 115 3 (CS03 ∷ []) ∷
   rw 118 q1 ∷
   re 116 3 (CS03 ∷ []) ∷
   rw 119 q1 ∷
   re 117 3 (CS03 ∷ []) ∷
   rw 120 q1 ∷
   re 118 3 (CS03 ∷ []) ∷
   rw 121 q1 ∷
   re 119 3 (CK30 ∷ []) ∷
   rw 120 q12 ∷
   rw 123 q1 ∷
   re 121 3 (CS03 ∷ []) ∷
   rw 124 q1 ∷
   re 122 3 (CS03 ∷ []) ∷
   rw 125 q1 ∷
   re 123 3 (CS03 ∷ []) ∷
   rw 126 q1 ∷
   re 124 3 (CS03 ∷ []) ∷
   rw 127 q1 ∷
   re 125 3 (CS03 ∷ []) ∷
   rw 128 q1 ∷
   re 126 3 (CS03 ∷ []) ∷
   rw 129 q1 ∷
   re 127 3 (CS03 ∷ []) ∷
   rw 130 q1 ∷
   re 128 3 (CS03 ∷ []) ∷
   rw 131 q1 ∷
   re 129 3 (CS03 ∷ []) ∷
   rw⁻ 130 q3 ∷
   rw⁻ 131 q3 ∷
   rw⁻ 132 q8 ∷
   rw⁻ 133 q7 ∷
   rw⁻ 134 q7 ∷
   rw⁻ 135 q10 ∷
   rw⁻ 136 q3 ∷
   rw 137 q5 ∷
   rw 0 q13 ∷
   rw 106 q1 ∷
   rw 105 q3 ∷
   rw 104 q10 ∷
   rw 103 q7 ∷
   rw 102 q7 ∷
   rw 101 q8 ∷
   rw 100 q3 ∷
   rw 99 q3 ∷
   re 98 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 100 q5 ∷
   re 97 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 99 q5 ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 98 q5 ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q5 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q5 ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q5 ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q5 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q5 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 92 q5 ∷
   rw 89 q6 ∷
   re 88 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 90 q5 ∷
   re 87 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 89 q5 ∷
   re 86 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 88 q5 ∷
   re 85 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 87 q5 ∷
   re 84 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 86 q5 ∷
   re 83 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 85 q5 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q5 ∷
   re 81 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 83 q5 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q5 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q5 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q5 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q5 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q5 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q5 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q5 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q5 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q5 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q5 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q5 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q5 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q5 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q5 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q5 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q5 ∷
   re 64 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 66 q5 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q5 ∷
   rw 62 q6 ∷
   re 61 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 63 q5 ∷
   rw 60 q6 ∷
   rw 59 q6 ∷
   rw 58 q6 ∷
   re 57 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 59 q5 ∷
   re 56 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 58 q5 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q5 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q5 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q5 ∷
   re 52 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 54 q5 ∷
   re 51 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 53 q5 ∷
   re 50 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 52 q5 ∷
   re 49 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 51 q5 ∷
   re 48 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 50 q5 ∷
   re 47 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 49 q5 ∷
   re 46 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 48 q5 ∷
   re 45 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 47 q5 ∷
   re 44 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 46 q5 ∷
   re 43 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 45 q5 ∷
   re 42 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 44 q5 ∷
   re 41 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 43 q5 ∷
   re 40 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 42 q5 ∷
   re 39 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 41 q5 ∷
   re 38 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 40 q5 ∷
   re 37 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 39 q5 ∷
   re 36 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 38 q5 ∷
   re 35 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 37 q5 ∷
   re 34 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 36 q5 ∷
   re 33 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 35 q5 ∷
   re 32 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 34 q5 ∷
   re 31 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 33 q5 ∷
   re 30 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 32 q5 ∷
   rw 29 q7 ∷
   rw 28 q7 ∷
   rw 27 q7 ∷
   rw 26 q7 ∷
   rw 25 q7 ∷
   rw 24 q7 ∷
   rw 23 q7 ∷
   rw 22 q7 ∷
   rw 21 q7 ∷
   rw 20 q11 ∷
   rw 19 q8 ∷
   rw 18 q7 ∷
   rw 17 q7 ∷
   rw 16 q7 ∷
   rw 15 q7 ∷
   rw 14 q7 ∷
   rw 13 q7 ∷
   rw 12 q3 ∷
   rw 11 q3 ∷
   rw 10 q7 ∷
   rw 9 q8 ∷
   rw 8 q7 ∷
   rw 7 q7 ∷
   rw 6 q3 ∷
   rw 5 q3 ∷
   rw 4 q10 ∷
   rw 3 q7 ∷
   rw 2 q7 ∷
   rw 1 q8 ∷
   rw 0 q3 ∷
   rw 1 q14 ∷
   rw⁻ 0 q4 ∷
   rw⁻ 1 q3 ∷
   rw 2 q15 ∷
   rw⁻ 3 q7 ∷
   rw⁻ 4 q7 ∷
   rw⁻ 5 q7 ∷
   rw⁻ 6 q8 ∷
   rw⁻ 7 q7 ∷
   rw⁻ 8 q7 ∷
   rw 11 q1 ∷
   re 9 3 (CX13 ∷ []) ∷
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
   re 16 3 (CK30 ∷ []) ∷
   rw 17 q12 ∷
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
   re 27 3 (CX13 ∷ []) ∷
   rw 30 q1 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q1 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q1 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q1 ∷
   re 31 3 (CK30 ∷ []) ∷
   rw 34 q1 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q1 ∷
   re 33 3 (CS03 ∷ []) ∷
   rw⁻ 34 q4 ∷
   rw⁻ 35 q3 ∷
   rw 36 q15 ∷
   rw 37 q5 ∷ []) Eq.refl
