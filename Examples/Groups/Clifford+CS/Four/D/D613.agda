{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD613 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D613 (W : Ws) (Sᴰ : SD613) where

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
  lem-pass-CS13-vs-CS03 : St 1092
  lem-pass-CS13-vs-CS03 = pickᴰ 0 Sᴰ
  lem-pass-CSd13-vs-CS03 : St 1095
  lem-pass-CSd13-vs-CS03 = pickᴰ 1 Sᴰ
  lem-pass-CS03-vs-S1 : St 663
  lem-pass-CS03-vs-S1 = pickᴰ 2 Sᴰ
  lem-pass-CS03-vs-Sd1 : St 1100
  lem-pass-CS03-vs-Sd1 = pickᴰ 3 Sᴰ
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03 : St 1383
  lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03 = pickᴰ 4 Sᴰ
  lem-pass-TOFF102-vs-CS03 : St 1124
  lem-pass-TOFF102-vs-CS03 = pickᴰ 5 Sᴰ
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-ᵖinv : St 1384
  lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-ᵖinv = pickᴰ 6 Sᴰ

private
  q1 : Eqn
  q1 = sE 1383 lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03
  q2 : Eqn
  q2 = wE 1829 W
  q3 : Eqn
  q3 = wE 1 W
  q4 : Eqn
  q4 = eqn (CS01 ∷ Sw23 ∷ []) (Sw23 ∷ CS01 ∷ []) (low-comm (CS) (Swap))
  q5 : Eqn
  q5 = eqn (CK10 ∷ Sw23 ∷ []) (Sw23 ∷ CK10 ∷ []) (low-comm (CK₁₀) (Swap))
  q6 : Eqn
  q6 = eqn (S1 ∷ Sw23 ∷ []) (Sw23 ∷ S1 ∷ []) (low-comm ((S ↑)) (Swap))
  q7 : Eqn
  q7 = wE 3 W
  q8 : Eqn
  q8 = wE 464 W
  q9 : Eqn
  q9 = wE 1830 W
  q10 : Eqn
  q10 = wE 153 W
  q11 : Eqn
  q11 = eqn (CS01⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CS01⁻ ∷ []) (low-comm ((CS • CS • CS)) (Swap))
  q12 : Eqn
  q12 = eqn (CK10⁻ ∷ Sw23 ∷ []) (Sw23 ∷ CK10⁻ ∷ []) (low-comm ((S ↑ • CK₁₀)) (Swap))
  q13 : Eqn
  q13 = sE 1384 lem-pass-CS01-CS01-CS01-CK10-CS01-CS01-CX12-CS02-CS02-CS02-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CS02-CK20-CS02-CS02-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-ᵖinv
  q14 : Eqn
  q14 = wE 689 W
  q15 : Eqn
  q15 = wE 1831 W
  q16 : Eqn
  q16 = wE 151 W
  q17 : Eqn
  q17 = wE 1832 W

-- pass [CS01 CS01 CK10 CS01 CK10 CK10 CX12 CK20 S2 CK20 S2 CS02 CS02 CS02 CK20 S2 CS02 CS02 CS02 CS02 CS02 CS02 CX12 CS02 CS02 CK20 CS02 CK20 CK20] [CS01 CS01 CK10 CS01 CX13 CS03 CS03 CS03 CK30 S3 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CK30 CS03 CK20 CS03 CS03 CS03 S3 CK30 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 S3 S3 S3 S3 CK30 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CS03 CX13 CS01 CS01 CS01 S1 CK10 CS01 CS01 CS01 CS01 CS01 CS01 S2 CK20]: 276 steps
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20 : ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) ⟫ʷ ≈ ⟪ (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ []) ⟫ʷ
lem-pass-CS01-CS01-CK10-CS01-CK10-CK10-CX12-CK20-S2-CK20-S2-CS02-CS02-CS02-CK20-S2-CS02-CS02-CS02-CS02-CS02-CS02-CX12-CS02-CS02-CK20-CS02-CK20-CK20-vs-CS01-CS01-CK10-CS01-CX13-CS03-CS03-CS03-CK30-S3-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CK30-CS03-CK20-CS03-CS03-CS03-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-S3-S3-S3-S3-CK30-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CS03-CX13-CS01-CS01-CS01-S1-CK10-CS01-CS01-CS01-CS01-CS01-CS01-S2-CK20 = derive (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ []) (CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CK30 ∷ S3 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CK30 ∷ CS03 ∷ CK20 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ S3 ∷ S3 ∷ S3 ∷ S3 ∷ CK30 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CS03 ∷ CX13 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S1 ∷ CK10 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ CS01 ∷ S2 ∷ CK20 ∷ CS01 ∷ CS01 ∷ CK10 ∷ CS01 ∷ CK10 ∷ CK10 ∷ CX12 ∷ CK20 ∷ S2 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CK20 ∷ S2 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CS02 ∷ CX12 ∷ CS02 ∷ CS02 ∷ CK20 ∷ CS02 ∷ CK20 ∷ CK20 ∷ [])
  (rw 0 q1 ∷
   rw 21 q2 ∷
   rw 109 q3 ∷
   rw 108 q4 ∷
   rw 107 q4 ∷
   rw 106 q4 ∷
   rw 105 q4 ∷
   rw 104 q4 ∷
   rw 103 q4 ∷
   rw 102 q5 ∷
   rw 101 q6 ∷
   rw 100 q4 ∷
   rw 99 q4 ∷
   rw 98 q4 ∷
   re 97 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 99 q7 ∷
   re 96 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 98 q7 ∷
   re 95 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 97 q7 ∷
   re 94 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 96 q7 ∷
   re 93 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 95 q7 ∷
   re 92 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 94 q7 ∷
   re 91 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 93 q7 ∷
   re 90 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 92 q7 ∷
   re 89 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 91 q7 ∷
   re 88 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 90 q7 ∷
   re 87 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 89 q7 ∷
   rw 86 q8 ∷
   rw 85 q8 ∷
   rw 84 q8 ∷
   rw 83 q8 ∷
   re 82 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 84 q7 ∷
   re 81 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 83 q7 ∷
   re 80 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 82 q7 ∷
   re 79 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 81 q7 ∷
   re 78 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 80 q7 ∷
   re 77 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 79 q7 ∷
   re 76 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 78 q7 ∷
   re 75 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 77 q7 ∷
   re 74 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 76 q7 ∷
   re 73 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 75 q7 ∷
   re 72 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 74 q7 ∷
   re 71 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 73 q7 ∷
   re 70 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 72 q7 ∷
   re 69 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 71 q7 ∷
   re 68 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 70 q7 ∷
   re 67 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 69 q7 ∷
   re 66 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 68 q7 ∷
   re 65 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 67 q7 ∷
   re 64 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 66 q7 ∷
   re 63 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 65 q7 ∷
   re 62 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 64 q7 ∷
   re 61 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 63 q7 ∷
   re 60 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 62 q7 ∷
   re 59 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 61 q7 ∷
   re 58 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 60 q7 ∷
   re 57 1 (Sw23 ∷ CK20 ∷ Sw23 ∷ []) ∷
   rw 59 q7 ∷
   rw 56 q8 ∷
   re 55 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 57 q7 ∷
   re 54 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 56 q7 ∷
   re 53 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 55 q7 ∷
   rw 54 q9 ∷
   rw 55 q3 ∷
   re 53 3 (CS03⁻ ∷ []) ∷
   rw 56 q3 ∷
   re 54 3 (CK30⁻ ∷ []) ∷
   rw 57 q3 ∷
   re 55 3 (CS03⁻ ∷ []) ∷
   rw 58 q3 ∷
   re 56 3 (CS03⁻ ∷ []) ∷
   rw 59 q3 ∷
   re 57 3 (CX13 ∷ []) ∷
   rw 60 q3 ∷
   re 58 3 (CS03⁻ ∷ []) ∷
   rw 61 q3 ∷
   re 59 3 (CS03⁻ ∷ []) ∷
   rw 62 q3 ∷
   re 60 3 (CS03⁻ ∷ []) ∷
   rw 63 q3 ∷
   re 61 3 (CS03⁻ ∷ []) ∷
   rw 64 q3 ∷
   re 62 3 (CS03⁻ ∷ []) ∷
   rw 65 q3 ∷
   re 63 3 (CS03⁻ ∷ []) ∷
   rw 64 q10 ∷
   rw 67 q3 ∷
   re 65 3 (CK30⁻ ∷ []) ∷
   rw 68 q3 ∷
   re 66 3 (CS03⁻ ∷ []) ∷
   rw 69 q3 ∷
   re 67 3 (CS03⁻ ∷ []) ∷
   rw 70 q3 ∷
   re 68 3 (CS03⁻ ∷ []) ∷
   rw 71 q3 ∷
   re 69 3 (CX13 ∷ []) ∷
   rw⁻ 70 q11 ∷
   rw⁻ 71 q12 ∷
   rw⁻ 72 q11 ∷
   rw⁻ 73 q11 ∷
   rw 74 q7 ∷
   rw 22 q13 ∷
   rw 43 q3 ∷
   rw 42 q11 ∷
   rw 41 q11 ∷
   rw 40 q12 ∷
   rw 39 q11 ∷
   re 38 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 40 q7 ∷
   re 37 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 39 q7 ∷
   re 36 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 38 q7 ∷
   re 35 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 37 q7 ∷
   re 34 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 36 q7 ∷
   rw 33 q14 ∷
   re 32 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 34 q7 ∷
   re 31 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 33 q7 ∷
   re 30 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 32 q7 ∷
   re 29 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 31 q7 ∷
   re 28 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 30 q7 ∷
   re 27 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 29 q7 ∷
   re 26 1 (Sw23 ∷ CX12 ∷ Sw23 ∷ []) ∷
   rw 28 q7 ∷
   re 25 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 27 q7 ∷
   re 24 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 26 q7 ∷
   re 23 1 (Sw23 ∷ CK20⁻ ∷ Sw23 ∷ []) ∷
   rw 25 q7 ∷
   re 22 1 (Sw23 ∷ CS02⁻ ∷ Sw23 ∷ []) ∷
   rw 24 q7 ∷
   rw 23 q15 ∷
   rw 24 q3 ∷
   re 22 3 (CS03 ∷ []) ∷
   rw 25 q3 ∷
   re 23 3 (CS03 ∷ []) ∷
   rw 26 q3 ∷
   re 24 3 (CS03 ∷ []) ∷
   rw 25 q16 ∷
   rw 28 q3 ∷
   re 26 3 (CK30 ∷ []) ∷
   rw 29 q3 ∷
   re 27 3 (CS03 ∷ []) ∷
   rw 30 q3 ∷
   re 28 3 (CS03 ∷ []) ∷
   rw 31 q3 ∷
   re 29 3 (CS03 ∷ []) ∷
   rw 32 q3 ∷
   re 30 3 (CS03 ∷ []) ∷
   rw 33 q3 ∷
   re 31 3 (CS03 ∷ []) ∷
   rw 34 q3 ∷
   re 32 3 (CS03 ∷ []) ∷
   rw 35 q3 ∷
   re 33 3 (CX13 ∷ []) ∷
   rw 36 q3 ∷
   re 34 3 (CS03 ∷ []) ∷
   rw 37 q3 ∷
   re 35 3 (CS03 ∷ []) ∷
   rw 38 q3 ∷
   re 36 3 (CS03 ∷ []) ∷
   rw 39 q3 ∷
   re 37 3 (CS03 ∷ []) ∷
   rw 40 q3 ∷
   re 38 3 (CS03 ∷ []) ∷
   rw 41 q3 ∷
   re 39 3 (CS03 ∷ []) ∷
   rw 42 q3 ∷
   re 40 3 (CS03 ∷ []) ∷
   rw 43 q3 ∷
   re 41 3 (CS03 ∷ []) ∷
   rw 44 q3 ∷
   re 42 3 (CS03 ∷ []) ∷
   rw 45 q3 ∷
   re 43 3 (CS03 ∷ []) ∷
   rw 46 q3 ∷
   re 44 3 (CS03 ∷ []) ∷
   rw 47 q3 ∷
   re 45 3 (CS03 ∷ []) ∷
   rw 48 q3 ∷
   re 46 3 (CS03 ∷ []) ∷
   rw 49 q3 ∷
   re 47 3 (CS03 ∷ []) ∷
   rw 50 q3 ∷
   re 48 3 (CS03 ∷ []) ∷
   rw 51 q3 ∷
   re 49 3 (CS03 ∷ []) ∷
   rw 52 q3 ∷
   re 50 3 (CS03 ∷ []) ∷
   rw 53 q3 ∷
   re 51 3 (CS03 ∷ []) ∷
   rw 52 q16 ∷
   rw 53 q16 ∷
   rw 54 q16 ∷
   rw 55 q16 ∷
   rw 58 q3 ∷
   re 56 3 (CK30 ∷ []) ∷
   rw 59 q3 ∷
   re 57 3 (CS03 ∷ []) ∷
   rw 60 q3 ∷
   re 58 3 (CS03 ∷ []) ∷
   rw 61 q3 ∷
   re 59 3 (CS03 ∷ []) ∷
   rw 62 q3 ∷
   re 60 3 (CS03 ∷ []) ∷
   rw 63 q3 ∷
   re 61 3 (CS03 ∷ []) ∷
   rw 64 q3 ∷
   re 62 3 (CS03 ∷ []) ∷
   rw 65 q3 ∷
   re 63 3 (CS03 ∷ []) ∷
   rw 66 q3 ∷
   re 64 3 (CS03 ∷ []) ∷
   rw 67 q3 ∷
   re 65 3 (CS03 ∷ []) ∷
   rw 68 q3 ∷
   re 66 3 (CX13 ∷ []) ∷
   rw⁻ 67 q4 ∷
   rw⁻ 68 q4 ∷
   rw⁻ 69 q4 ∷
   rw⁻ 70 q6 ∷
   rw⁻ 71 q5 ∷
   rw⁻ 72 q4 ∷
   rw⁻ 73 q4 ∷
   rw⁻ 74 q4 ∷
   rw⁻ 75 q4 ∷
   rw⁻ 76 q4 ∷
   rw⁻ 77 q4 ∷
   rw 78 q7 ∷
   rw 78 q17 ∷ []) Eq.refl

private
  q18 : Eqn
  q18 = sE 663 lem-pass-CS03-vs-S1
  q19 : Eqn
  q19 = sE 1095 lem-pass-CSd13-vs-CS03
  q20 : Eqn
  q20 = sE 1124 lem-pass-TOFF102-vs-CS03
  q21 : Eqn
  q21 = sE 1100 lem-pass-CS03-vs-Sd1
  q22 : Eqn
  q22 = sE 1092 lem-pass-CS13-vs-CS03

-- pass [CS03] [S1 CSd13 TOFF102 Sd1 CS13 TOFF102]: 6 steps
lem-pass-CS03-vs-S1-CSd13-TOFF102-Sd1-CS13-TOFF102 : ⟪ (CS03 ∷ S1 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ []) ⟫ʷ ≈ ⟪ (S1 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-S1-CSd13-TOFF102-Sd1-CS13-TOFF102 = derive (CS03 ∷ S1 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ []) (S1 ∷ CS13⁻ ∷ Toff102 ∷ S1⁻ ∷ CS13 ∷ Toff102 ∷ CS03 ∷ [])
  (rw 0 q18 ∷
   rw⁻ 1 q19 ∷
   rw⁻ 2 q20 ∷
   rw 3 q21 ∷
   rw⁻ 4 q22 ∷
   rw⁻ 5 q20 ∷ []) Eq.refl

private
  q23 : Eqn
  q23 = wE 1359 W
  q24 : Eqn
  q24 = eqn (CX01 ∷ Sw23 ∷ []) (Sw23 ∷ CX01 ∷ []) (low-comm (CX₀₁) (Swap))
  q25 : Eqn
  q25 = wE 1360 W
  q26 : Eqn
  q26 = wE 1361 W

-- pass [CS03] [CS13 X2 TOFF102 X2 CSd13 X2 TOFF102 X2]: 26 steps
lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 : ⟪ (CS03 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) ⟫ʷ ≈ ⟪ (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ []) ⟫ʷ
lem-pass-CS03-vs-CS13-X2-TOFF102-X2-CSd13-X2-TOFF102-X2 = derive (CS03 ∷ CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ []) (CS13 ∷ X2 ∷ Toff102 ∷ X2 ∷ CS13⁻ ∷ X2 ∷ Toff102 ∷ X2 ∷ CS03 ∷ [])
  (rw⁻ 0 q22 ∷
   rw 2 q23 ∷
   rw 3 q3 ∷
   rw 2 q24 ∷
   re 1 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 3 q7 ∷
   rw 2 q25 ∷
   rw⁻ 1 q24 ∷
   rw 4 q3 ∷
   re 2 3 (CS03 ∷ []) ∷
   rw 3 q7 ∷
   rw⁻ 2 q20 ∷
   rw 1 q26 ∷
   rw⁻ 4 q19 ∷
   rw 6 q23 ∷
   rw 7 q3 ∷
   rw 6 q24 ∷
   re 5 1 (Sw23 ∷ CS02 ∷ Sw23 ∷ []) ∷
   rw 7 q7 ∷
   rw 6 q25 ∷
   rw⁻ 5 q24 ∷
   rw 8 q3 ∷
   re 6 3 (CS03 ∷ []) ∷
   rw 7 q7 ∷
   rw⁻ 6 q20 ∷
   rw 5 q26 ∷ []) Eq.refl
