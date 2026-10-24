{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD649 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D649 (W : Ws) (Sᴰ : SD649) where

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

-- The lemmas of other derivation modules (DSig).
private
  lem-AXIOM-LF-at2013 : St 1600
  lem-AXIOM-LF-at2013 = pickᴰ 0 Sᴰ
  lem-pass-TOFF301-vs-X0-TOFF301-X0 : St 1601
  lem-pass-TOFF301-vs-X0-TOFF301-X0 = pickᴰ 1 Sᴰ
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 : St 776
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 = pickᴰ 2 Sᴰ
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : St 1080
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = pickᴰ 3 Sᴰ
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : St 1081
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = pickᴰ 4 Sᴰ
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0 : St 1404
  lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0 = pickᴰ 5 Sᴰ
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 : St 1405
  lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0 = pickᴰ 6 Sᴰ
  lem-pass-TOFF301-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 : St 1602
  lem-pass-TOFF301-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0 = pickᴰ 7 Sᴰ
  lem-pass-TOFF301-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 : St 1603
  lem-pass-TOFF301-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = sE 1600 lem-AXIOM-LF-at2013
  q2 : Eqn
  q2 = wE 873 W
  q3 : Eqn
  q3 = sE 1080 lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0
  q4 : Eqn
  q4 = sE 1602 lem-pass-TOFF301-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0
  q5 : Eqn
  q5 = sE 1081 lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-CS02-CS02-CK02-CS02-CK02-CK02-CX01-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX01-CS12-CS12-CK12-CS12-CK12-CK12-X0
  q6 : Eqn
  q6 = sE 1404 lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-TOFF301-X0
  q7 : Eqn
  q7 = sE 1601 lem-pass-TOFF301-vs-X0-TOFF301-X0
  q8 : Eqn
  q8 = sE 1405 lem-pass-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-vs-X0-TOFF301-X0
  q9 : Eqn
  q9 = sE 776 lem-pass-CS02-CS02-CK02-CS02-CK02-CK02-CX03-CK32-S3-CK32-S3-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CK32-CS23-CK32-CK32-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0
  q10 : Eqn
  q10 = sE 1603 lem-pass-TOFF301-vs-X0-CS02-CS02-CS02-CK02-CS02-CS02-CX03-CS23-CS23-CS23-CS23-CS23-CS23-CK32-S3-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CS23-CX03-CS23-CS23-CS23-CK32-CS23-CS23-X0
  q11 : Eqn
  q11 = wE 1951 W
  q12 : Eqn
  q12 = wE 1 W
  q13 : Eqn
  q13 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q14 : Eqn
  q14 = wE 335 W
  q15 : Eqn
  q15 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q16 : Eqn
  q16 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q17 : Eqn
  q17 = wE 3 W
  q18 : Eqn
  q18 = wE 1294 W
  q19 : Eqn
  q19 = wE 368 W
  q20 : Eqn
  q20 = wE 1952 W
  q21 : Eqn
  q21 = wE 5 W
  q22 : Eqn
  q22 = wE 1106 W
  q23 : Eqn
  q23 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q24 : Eqn
  q24 = eqn (ℓ "並乗") (ℓ "乗並") (low-comm (Swap) (CK₁₀))
  q25 : Eqn
  q25 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q26 : Eqn
  q26 = wE 74 W
  q27 : Eqn
  q27 = eqn (ℓ "並业") (ℓ "业並") (low-comm (Swap) ((S ↑)))
  q28 : Eqn
  q28 = wE 7 W
  q29 : Eqn
  q29 = wE 772 W
  q30 : Eqn
  q30 = wE 1953 W
  q31 : Eqn
  q31 = wE 31 W
  q32 : Eqn
  q32 = wE 1954 W

-- L87 merge-k CS02 CS02 CK02 CS02 CX01 CS12 CS12 CS12  0: 325 steps
lem-L87-merge-k-CS02-CS02-CK02-CS02-CX01-CS12-CS12-CS12--0 : ⟪ (ℓ "丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌") ⟫ʷ ≈ ⟪ (ℓ "丶丶为丶为为丶丶为丶为为乀义义义乗义义义义义乗义义乀义义乗义乗乗义义乗义乗乗") ⟫ʷ
lem-L87-merge-k-CS02-CS02-CK02-CS02-CX01-CS12-CS12-CS12--0 = derive (ℓ "丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌丧丧丫丧丣丶丶丶为与丶丶丶丶丶丶丣丶丶为丶乗丶丶丶与为丶丶丶丶丶丶丣丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶丶与与与与为丶丶丶丶丶丶丶丶丶丣丧丧丧丈丫丧丧丧丧丧丧业乗丌") (ℓ "丶丶为丶为为丶丶为丶为为乀义义义乗义义义义义乗义义乀义义乗义乗乗义义乗义乗乗")
  (rw 0 q1 ∷
   rw 92 q1 ∷
   rw 121 q2 ∷
   rw 124 q2 ∷
   rw 157 q2 ∷
   rw 160 q2 ∷
   rw 62 q3 ∷
   rw 61 q4 ∷
   rw 30 q5 ∷
   rw 29 q4 ∷
   rw 93 q6 ∷
   rw 92 q7 ∷
   rw 61 q8 ∷
   rw 96 q9 ∷
   rw 95 q10 ∷
   rw 129 q6 ∷
   rw 0 q11 ∷
   rw 16 q12 ∷
   rw 15 q13 ∷
   re 14 1 (ℓ "乏乣乏") ∷
   re 15 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 14 q14 ∷
   rw 17 q12 ∷
   re 15 3 (ℓ "丽") ∷
   rw⁻ 16 q15 ∷
   rw 19 q12 ∷
   re 17 3 (ℓ "举") ∷
   rw⁻ 18 q15 ∷
   rw 21 q12 ∷
   re 19 3 (ℓ "中") ∷
   rw 20 q14 ∷
   rw⁻ 21 q16 ∷
   rw 22 q17 ∷
   rw 21 q16 ∷
   rw 20 q18 ∷
   re 19 1 (ℓ "乏丧乏") ∷
   rw 21 q17 ∷
   rw 18 q15 ∷
   re 17 1 (ℓ "乏丷乏") ∷
   rw 19 q17 ∷
   rw 16 q15 ∷
   re 15 1 (ℓ "乏丶乏") ∷
   rw 17 q17 ∷
   rw 14 q18 ∷
   rw 15 q19 ∷
   re 15 8 (ℓ "乣") ∷
   rw 13 q13 ∷
   re 12 1 (ℓ "乏乣乏") ∷
   re 13 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 12 q14 ∷
   rw 15 q12 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 14 q15 ∷
   rw 17 q12 ∷
   re 15 3 (ℓ "举") ∷
   rw⁻ 16 q15 ∷
   rw 19 q12 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q14 ∷
   rw⁻ 19 q16 ∷
   rw 20 q17 ∷
   rw 19 q16 ∷
   rw 18 q18 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q17 ∷
   rw 16 q15 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 17 q17 ∷
   rw 14 q15 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q17 ∷
   rw 12 q18 ∷
   rw 13 q19 ∷
   re 13 8 (ℓ "乣") ∷
   rw 13 q20 ∷
   rw 14 q12 ∷
   re 12 3 (ℓ "乀") ∷
   rw 13 q17 ∷
   rw 77 q21 ∷
   rw 76 q22 ∷
   rw⁻ 75 q23 ∷
   rw⁻ 74 q23 ∷
   rw⁻ 73 q24 ∷
   rw⁻ 72 q23 ∷
   rw⁻ 71 q23 ∷
   rw⁻ 70 q23 ∷
   re 69 1 (ℓ "乏个乏") ∷
   rw⁻ 71 q25 ∷
   rw 70 q26 ∷
   rw⁻ 69 q25 ∷
   re 70 3 (ℓ "乀") ∷
   rw⁻ 68 q23 ∷
   rw⁻ 67 q23 ∷
   rw⁻ 66 q23 ∷
   rw⁻ 65 q23 ∷
   rw⁻ 64 q23 ∷
   rw⁻ 63 q23 ∷
   rw⁻ 62 q23 ∷
   rw⁻ 61 q23 ∷
   rw⁻ 60 q23 ∷
   rw⁻ 59 q27 ∷
   rw⁻ 58 q24 ∷
   rw⁻ 57 q23 ∷
   rw⁻ 56 q23 ∷
   rw⁻ 55 q23 ∷
   rw⁻ 54 q23 ∷
   rw⁻ 53 q23 ∷
   rw⁻ 52 q23 ∷
   re 51 1 (ℓ "乏个乏") ∷
   rw⁻ 53 q25 ∷
   rw 52 q26 ∷
   rw⁻ 51 q25 ∷
   re 52 3 (ℓ "乀") ∷
   rw 50 q28 ∷
   rw 49 q28 ∷
   rw 48 q29 ∷
   rw 47 q28 ∷
   rw 46 q28 ∷
   rw 45 q28 ∷
   rw 44 q22 ∷
   rw⁻ 43 q23 ∷
   rw⁻ 42 q23 ∷
   rw⁻ 41 q24 ∷
   rw⁻ 40 q23 ∷
   rw⁻ 39 q23 ∷
   rw⁻ 38 q23 ∷
   re 37 1 (ℓ "乏个乏") ∷
   rw⁻ 39 q25 ∷
   rw 38 q26 ∷
   rw⁻ 37 q25 ∷
   re 38 3 (ℓ "乀") ∷
   rw⁻ 36 q23 ∷
   rw⁻ 35 q23 ∷
   rw⁻ 34 q23 ∷
   rw⁻ 33 q23 ∷
   rw⁻ 32 q23 ∷
   rw⁻ 31 q23 ∷
   rw⁻ 30 q23 ∷
   rw⁻ 29 q23 ∷
   rw⁻ 28 q23 ∷
   rw⁻ 27 q27 ∷
   rw⁻ 26 q24 ∷
   rw⁻ 25 q23 ∷
   rw⁻ 24 q23 ∷
   rw⁻ 23 q23 ∷
   rw⁻ 22 q23 ∷
   rw⁻ 21 q23 ∷
   rw⁻ 20 q23 ∷
   re 19 1 (ℓ "乏个乏") ∷
   rw⁻ 21 q25 ∷
   rw 20 q26 ∷
   rw⁻ 19 q25 ∷
   re 20 3 (ℓ "乀") ∷
   rw 18 q28 ∷
   rw 17 q28 ∷
   rw 16 q29 ∷
   rw 15 q28 ∷
   rw 14 q28 ∷
   rw 13 q28 ∷
   rw 14 q30 ∷
   rw 13 q23 ∷
   rw 14 q23 ∷
   rw 15 q23 ∷
   rw 16 q24 ∷
   rw 17 q23 ∷
   rw 18 q23 ∷
   rw 19 q23 ∷
   rw 20 q23 ∷
   rw 21 q23 ∷
   rw 22 q24 ∷
   rw 23 q23 ∷
   rw 24 q23 ∷
   rw 25 q31 ∷
   rw 29 q12 ∷
   rw 28 q13 ∷
   re 27 1 (ℓ "乏乣乏") ∷
   re 28 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 27 q14 ∷
   rw 30 q12 ∷
   re 28 3 (ℓ "丽") ∷
   rw⁻ 29 q15 ∷
   rw 32 q12 ∷
   re 30 3 (ℓ "举") ∷
   rw⁻ 31 q15 ∷
   rw 34 q12 ∷
   re 32 3 (ℓ "中") ∷
   rw 33 q14 ∷
   rw⁻ 34 q16 ∷
   rw 35 q17 ∷
   rw 34 q16 ∷
   rw 33 q18 ∷
   re 32 1 (ℓ "乏丧乏") ∷
   rw 34 q17 ∷
   rw 31 q15 ∷
   re 30 1 (ℓ "乏丷乏") ∷
   rw 32 q17 ∷
   rw 29 q15 ∷
   re 28 1 (ℓ "乏丶乏") ∷
   rw 30 q17 ∷
   rw 27 q18 ∷
   rw 28 q19 ∷
   re 28 8 (ℓ "乣") ∷
   rw 26 q13 ∷
   re 25 1 (ℓ "乏乣乏") ∷
   re 26 1 (ℓ "世丶丣丷丣丧世一") ∷
   rw 25 q14 ∷
   rw 28 q12 ∷
   re 26 3 (ℓ "丽") ∷
   rw⁻ 27 q15 ∷
   rw 30 q12 ∷
   re 28 3 (ℓ "举") ∷
   rw⁻ 29 q15 ∷
   rw 32 q12 ∷
   re 30 3 (ℓ "中") ∷
   rw 31 q14 ∷
   rw⁻ 32 q16 ∷
   rw 33 q17 ∷
   rw 32 q16 ∷
   rw 31 q18 ∷
   re 30 1 (ℓ "乏丧乏") ∷
   rw 32 q17 ∷
   rw 29 q15 ∷
   re 28 1 (ℓ "乏丷乏") ∷
   rw 30 q17 ∷
   rw 27 q15 ∷
   re 26 1 (ℓ "乏丶乏") ∷
   rw 28 q17 ∷
   rw 25 q18 ∷
   rw 26 q19 ∷
   re 26 8 (ℓ "乣") ∷
   rw 26 q20 ∷
   rw 27 q12 ∷
   re 25 3 (ℓ "乀") ∷
   rw 26 q17 ∷
   rw 86 q21 ∷
   rw 85 q22 ∷
   rw⁻ 84 q24 ∷
   rw⁻ 83 q24 ∷
   rw⁻ 82 q23 ∷
   rw⁻ 81 q24 ∷
   rw⁻ 80 q23 ∷
   rw⁻ 79 q23 ∷
   re 78 1 (ℓ "乏个乏") ∷
   rw⁻ 80 q25 ∷
   rw 79 q26 ∷
   rw⁻ 78 q25 ∷
   re 79 3 (ℓ "乀") ∷
   rw⁻ 77 q23 ∷
   rw⁻ 76 q23 ∷
   rw⁻ 75 q23 ∷
   rw⁻ 74 q23 ∷
   rw⁻ 73 q23 ∷
   rw⁻ 72 q23 ∷
   rw⁻ 71 q27 ∷
   rw⁻ 70 q24 ∷
   rw⁻ 69 q23 ∷
   rw⁻ 68 q23 ∷
   rw⁻ 67 q23 ∷
   rw⁻ 66 q27 ∷
   rw⁻ 65 q24 ∷
   rw⁻ 64 q27 ∷
   rw⁻ 63 q24 ∷
   re 62 1 (ℓ "乏个乏") ∷
   rw⁻ 64 q25 ∷
   rw 63 q26 ∷
   rw⁻ 62 q25 ∷
   re 63 3 (ℓ "乀") ∷
   rw 61 q29 ∷
   rw 60 q29 ∷
   rw 59 q28 ∷
   rw 58 q29 ∷
   rw 57 q28 ∷
   rw 56 q28 ∷
   rw 55 q22 ∷
   rw⁻ 54 q24 ∷
   rw⁻ 53 q24 ∷
   rw⁻ 52 q23 ∷
   rw⁻ 51 q24 ∷
   rw⁻ 50 q23 ∷
   rw⁻ 49 q23 ∷
   re 48 1 (ℓ "乏个乏") ∷
   rw⁻ 50 q25 ∷
   rw 49 q26 ∷
   rw⁻ 48 q25 ∷
   re 49 3 (ℓ "乀") ∷
   rw⁻ 47 q23 ∷
   rw⁻ 46 q23 ∷
   rw⁻ 45 q23 ∷
   rw⁻ 44 q23 ∷
   rw⁻ 43 q23 ∷
   rw⁻ 42 q23 ∷
   rw⁻ 41 q27 ∷
   rw⁻ 40 q24 ∷
   rw⁻ 39 q23 ∷
   rw⁻ 38 q23 ∷
   rw⁻ 37 q23 ∷
   rw⁻ 36 q27 ∷
   rw⁻ 35 q24 ∷
   rw⁻ 34 q27 ∷
   rw⁻ 33 q24 ∷
   re 32 1 (ℓ "乏个乏") ∷
   rw⁻ 34 q25 ∷
   rw 33 q26 ∷
   rw⁻ 32 q25 ∷
   re 33 3 (ℓ "乀") ∷
   rw 31 q29 ∷
   rw 30 q29 ∷
   rw 29 q28 ∷
   rw 28 q29 ∷
   rw 27 q28 ∷
   rw 26 q28 ∷
   rw 27 q32 ∷
   rw 26 q23 ∷
   rw 27 q23 ∷
   rw 28 q24 ∷
   rw 29 q23 ∷
   rw 30 q24 ∷
   rw 31 q24 ∷
   rw 32 q23 ∷
   rw 33 q23 ∷
   rw 34 q24 ∷
   rw 35 q23 ∷
   rw 36 q24 ∷
   rw 37 q24 ∷
   rw 38 q31 ∷ []) Eq.refl
