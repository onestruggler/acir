{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD768 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D768 (W : Ws) (Sᴰ : SD768) where

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
  lem-PP2≡E-at1023 : St 2862
  lem-PP2≡E-at1023 = pickᴰ 0 Sᴰ
  lem-PP2≡E-at3012 : St 3207
  lem-PP2≡E-at3012 = pickᴰ 1 Sᴰ
  lem-L87-merge-p-0123-3 : St 3208
  lem-L87-merge-p-0123-3 = pickᴰ 2 Sᴰ
  lem-merge-R0 : St 3093
  lem-merge-R0 = pickᴰ 3 Sᴰ
  lem-L87-merge-p-0123-1 : St 3209
  lem-L87-merge-p-0123-1 = pickᴰ 4 Sᴰ
  lem-L87-merge-p-0123-2 : St 3210
  lem-L87-merge-p-0123-2 = pickᴰ 5 Sᴰ
  lem-L87-merge-p-1023-2 : St 3211
  lem-L87-merge-p-1023-2 = pickᴰ 6 Sᴰ
  lem-L87-merge-p-1023-3 : St 3212
  lem-L87-merge-p-1023-3 = pickᴰ 7 Sᴰ
  lem-L87-merge-p-2013-3 : St 3213
  lem-L87-merge-p-2013-3 = pickᴰ 8 Sᴰ

private
  q1 : Eqn
  q1 = wE 389 W
  q2 : Eqn
  q2 = eqn (ℓ "丘丞") (ℓ "丞丘") (low₃-comm ((X ↑ ↑)) (X))
  q3 : Eqn
  q3 = eqn (ℓ "丌丘") (ℓ "丘丌") (low₁-comm (X) ((X ↑)))
  q4 : Eqn
  q4 = wE 387 W
  q5 : Eqn
  q5 = eqn (ℓ "丌丞") (ℓ "丞丌") (low₁-comm (X) ((X ↑ ↑)))
  q6 : Eqn
  q6 = wE 388 W
  q7 : Eqn
  q7 = eqn (ℓ "丒丞") (ℓ "丞丒") (low-comm ((X ↑)) ((X ↑)))
  q8 : Eqn
  q8 = sE 3212 lem-L87-merge-p-1023-3
  q9 : Eqn
  q9 = sE 3208 lem-L87-merge-p-0123-3
  q10 : Eqn
  q10 = sE 3213 lem-L87-merge-p-2013-3
  q11 : Eqn
  q11 = wE 2566 W

-- L87 S0: 43 steps
lem-L87-S0 : ⟪ (ℓ "丘习丽习举丘丘丞习丽习举丘丞丌丘九中九丮丌丘丌丘丞九中九丮丌丘丞丌丘九中九丮丌丘丌丘丞九中九丮丌丘丞丌乣义乣乊丌丌丞乣义乣乊丌丞丌乣义乣乊丌丌丞乣义乣乊丌丞九中九丮丞九中九丮丞九中九丮丞九中九丮丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞") ⟫ʷ ≈ ⟪ (ℓ "丈") ⟫ʷ
lem-L87-S0 = derive (ℓ "丘习丽习举丘丘丞习丽习举丘丞丌丘九中九丮丌丘丌丘丞九中九丮丌丘丞丌丘九中九丮丌丘丌丘丞九中九丮丌丘丞丌乣义乣乊丌丌丞乣义乣乊丌丞丌乣义乣乊丌丌丞乣义乣乊丌丞九中九丮丞九中九丮丞九中九丮丞九中九丮丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞") (ℓ "丈")
  (rw 5 q1 ∷
   rw 10 q2 ∷
   rw⁻ 11 q3 ∷
   rw 12 q1 ∷
   rw⁻ 17 q3 ∷
   rw 18 q1 ∷
   rw 16 q4 ∷
   rw 22 q2 ∷
   rw⁻ 23 q3 ∷
   rw 24 q1 ∷
   rw 21 q5 ∷
   rw 22 q4 ∷
   rw⁻ 27 q3 ∷
   rw 28 q1 ∷
   rw 26 q4 ∷
   rw 32 q2 ∷
   rw⁻ 33 q3 ∷
   rw 31 q5 ∷
   rw 32 q4 ∷
   rw 37 q4 ∷
   rw 42 q5 ∷
   rw 43 q4 ∷
   rw 47 q4 ∷
   rw 52 q5 ∷
   rw 79 q6 ∷
   rw 84 q7 ∷
   rw 85 q6 ∷
   rw 89 q6 ∷
   rw 94 q7 ∷
   rw 95 q6 ∷
   rw 99 q6 ∷
   rw 104 q7 ∷
   rw 1 q8 ∷
   rw 67 q8 ∷
   rw 69 q8 ∷
   rw 71 q8 ∷
   rw 4 q9 ∷
   rw 6 q9 ∷
   rw 30 q9 ∷
   rw 32 q9 ∷
   rw 9 q10 ∷
   rw 11 q10 ∷
   rw 0 q11 ∷ []) Eq.refl

private
  q12 : Eqn
  q12 = wE 2567 W

-- L87 S1: 19 steps
lem-L87-S1 : ⟪ (ℓ "丌丘九中九丮丌丘丌丘丞九中九丮丌丘丞丌乣义乣乊丌丌丞乣义乣乊丌丞丌乣义乣乊丌丌丞乣义乣乊丌丞九中九丮丞九中九丮丞九中九丮丞九中九丮丞九中九丮丞九中九丮丞") ⟫ʷ ≈ ⟪ (ℓ "与") ⟫ʷ
lem-L87-S1 = derive (ℓ "丌丘九中九丮丌丘丌丘丞九中九丮丌丘丞丌乣义乣乊丌丌丞乣义乣乊丌丞丌乣义乣乊丌丌丞乣义乣乊丌丞九中九丮丞九中九丮丞九中九丮丞九中九丮丞九中九丮丞九中九丮丞") (ℓ "与")
  (rw⁻ 7 q3 ∷
   rw 8 q1 ∷
   rw 6 q4 ∷
   rw 12 q2 ∷
   rw⁻ 13 q3 ∷
   rw 11 q5 ∷
   rw 12 q4 ∷
   rw 17 q4 ∷
   rw 22 q5 ∷
   rw 23 q4 ∷
   rw 27 q4 ∷
   rw 32 q5 ∷
   rw 2 q9 ∷
   rw 26 q9 ∷
   rw 28 q9 ∷
   rw 30 q9 ∷
   rw 5 q10 ∷
   rw 7 q10 ∷
   rw 0 q12 ∷ []) Eq.refl

private
  q13 : Eqn
  q13 = eqn (ℓ "丌丒") (ℓ "丒丌") (low₁-comm (X) (X))
  q14 : Eqn
  q14 = wE 2568 W

-- L87 S2: 35 steps
lem-L87-S2 : ⟪ (ℓ "九中九丮丞九中九丮丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "且") ⟫ʷ
lem-L87-S2 = derive (ℓ "九中九丮丞九中九丮丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞") (ℓ "且")
  (rw 15 q6 ∷
   rw 20 q7 ∷
   rw 21 q6 ∷
   rw 25 q6 ∷
   rw 30 q7 ∷
   rw⁻ 31 q13 ∷
   rw 32 q6 ∷
   rw⁻ 37 q13 ∷
   rw 38 q6 ∷
   rw 36 q4 ∷
   rw 42 q7 ∷
   rw⁻ 43 q13 ∷
   rw 44 q6 ∷
   rw 41 q5 ∷
   rw 42 q4 ∷
   rw⁻ 47 q13 ∷
   rw 48 q6 ∷
   rw 46 q4 ∷
   rw 52 q7 ∷
   rw⁻ 53 q13 ∷
   rw 54 q6 ∷
   rw 51 q5 ∷
   rw 52 q4 ∷
   rw⁻ 57 q13 ∷
   rw 58 q6 ∷
   rw 56 q4 ∷
   rw 62 q7 ∷
   rw 61 q5 ∷
   rw 0 q9 ∷
   rw 24 q9 ∷
   rw 26 q9 ∷
   rw 28 q9 ∷
   rw 3 q8 ∷
   rw 5 q8 ∷
   rw 0 q14 ∷ []) Eq.refl

private
  q15 : Eqn
  q15 = eqn (ℓ "丒丘") (ℓ "丘丒") (low-comm ((X ↑)) (X))
  q16 : Eqn
  q16 = sE 3210 lem-L87-merge-p-0123-2
  q17 : Eqn
  q17 = sE 3211 lem-L87-merge-p-1023-2
  q18 : Eqn
  q18 = wE 1 W
  q19 : Eqn
  q19 = eqn (ℓ "丒乏") (ℓ "乏丒") (low-comm ((X ↑)) (Swap))
  q20 : Eqn
  q20 = eqn (ℓ "丌乏") (ℓ "乏丌") (low₁-comm (X) ((Swap ↑)))
  q21 : Eqn
  q21 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q22 : Eqn
  q22 = wE 3 W
  q23 : Eqn
  q23 = wE 43 W
  q24 : Eqn
  q24 = wE 151 W

-- L87 S3: 180 steps
lem-L87-S3 : ⟪ (ℓ "九中九丮丘九中九丮丘丒习丽习举丒丒丘习丽习举丒丘丒习丽习举丒丒丘习丽习举丒丘丌丒九中九丮丌丒丌丒丘九中九丮丌丒丘丌丒九中九丮丌丒丌丒丘九中九丮丌丒丘丌丒九中九丮丌丒丌丒丘九中九丮丌丒丘") ⟫ʷ ≈ ⟪ (ℓ "业") ⟫ʷ
lem-L87-S3 = derive (ℓ "九中九丮丘九中九丮丘丒习丽习举丒丒丘习丽习举丒丘丒习丽习举丒丒丘习丽习举丒丘丌丒九中九丮丌丒丌丒丘九中九丮丌丒丘丌丒九中九丮丌丒丌丒丘九中九丮丌丒丘丌丒九中九丮丌丒丌丒丘九中九丮丌丒丘") (ℓ "业")
  (rw 15 q6 ∷
   rw 20 q15 ∷
   rw 21 q6 ∷
   rw 25 q6 ∷
   rw 30 q15 ∷
   rw⁻ 31 q13 ∷
   rw 32 q6 ∷
   rw⁻ 37 q13 ∷
   rw 38 q6 ∷
   rw 36 q4 ∷
   rw 42 q15 ∷
   rw⁻ 43 q13 ∷
   rw 44 q6 ∷
   rw 41 q3 ∷
   rw 42 q4 ∷
   rw⁻ 47 q13 ∷
   rw 48 q6 ∷
   rw 46 q4 ∷
   rw 52 q15 ∷
   rw⁻ 53 q13 ∷
   rw 54 q6 ∷
   rw 51 q3 ∷
   rw 52 q4 ∷
   rw⁻ 57 q13 ∷
   rw 58 q6 ∷
   rw 56 q4 ∷
   rw 62 q15 ∷
   rw 61 q3 ∷
   rw 0 q16 ∷
   rw 24 q16 ∷
   rw 26 q16 ∷
   rw 28 q16 ∷
   rw 3 q17 ∷
   rw 5 q17 ∷
   rw 16 q18 ∷
   rw 15 q19 ∷
   rw 14 q20 ∷
   re 13 1 (ℓ "乏乙乏") ∷
   re 14 1 (ℓ "丶丣丷丣丧") ∷
   rw 15 q18 ∷
   re 13 3 (ℓ "丽") ∷
   rw⁻ 14 q21 ∷
   rw 17 q18 ∷
   re 15 3 (ℓ "举") ∷
   rw⁻ 16 q21 ∷
   rw 19 q18 ∷
   re 17 3 (ℓ "中") ∷
   rw 18 q22 ∷
   re 17 1 (ℓ "乏丧乏") ∷
   rw 19 q22 ∷
   rw 16 q21 ∷
   re 15 1 (ℓ "乏丷乏") ∷
   rw 17 q22 ∷
   rw 14 q21 ∷
   re 13 1 (ℓ "乏丶乏") ∷
   rw 15 q22 ∷
   rw 14 q23 ∷
   re 14 5 (ℓ "乙") ∷
   re 12 1 (ℓ "乏丶乏") ∷
   rw 14 q22 ∷
   re 11 1 (ℓ "乏乙乏") ∷
   re 12 1 (ℓ "丶丣丷丣丧") ∷
   rw 13 q18 ∷
   re 11 3 (ℓ "丽") ∷
   rw⁻ 12 q21 ∷
   rw 15 q18 ∷
   re 13 3 (ℓ "举") ∷
   rw⁻ 14 q21 ∷
   rw 17 q18 ∷
   re 15 3 (ℓ "中") ∷
   rw 16 q22 ∷
   re 15 1 (ℓ "乏丧乏") ∷
   rw 17 q22 ∷
   rw 14 q21 ∷
   re 13 1 (ℓ "乏丷乏") ∷
   rw 15 q22 ∷
   rw 12 q21 ∷
   re 11 1 (ℓ "乏丶乏") ∷
   rw 13 q22 ∷
   rw 12 q23 ∷
   re 12 5 (ℓ "乙") ∷
   re 10 1 (ℓ "乏丶乏") ∷
   rw 12 q22 ∷
   re 9 1 (ℓ "乏乙乏") ∷
   re 10 1 (ℓ "丶丣丷丣丧") ∷
   rw 11 q18 ∷
   re 9 3 (ℓ "丽") ∷
   rw⁻ 10 q21 ∷
   rw 13 q18 ∷
   re 11 3 (ℓ "举") ∷
   rw⁻ 12 q21 ∷
   rw 15 q18 ∷
   re 13 3 (ℓ "中") ∷
   rw 14 q22 ∷
   re 13 1 (ℓ "乏丧乏") ∷
   rw 15 q22 ∷
   rw 12 q21 ∷
   re 11 1 (ℓ "乏丷乏") ∷
   rw 13 q22 ∷
   rw 10 q21 ∷
   re 9 1 (ℓ "乏丶乏") ∷
   rw 11 q22 ∷
   rw 10 q23 ∷
   re 10 5 (ℓ "乙") ∷
   re 8 1 (ℓ "乏丶乏") ∷
   rw 10 q22 ∷
   rw 7 q20 ∷
   re 6 1 (ℓ "乏乙乏") ∷
   re 7 1 (ℓ "丶丣丷丣丧") ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "丽") ∷
   rw⁻ 7 q21 ∷
   rw 10 q18 ∷
   re 8 3 (ℓ "举") ∷
   rw⁻ 9 q21 ∷
   rw 12 q18 ∷
   re 10 3 (ℓ "中") ∷
   rw 11 q22 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 12 q22 ∷
   rw 9 q21 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 10 q22 ∷
   rw 7 q21 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 8 q22 ∷
   rw 7 q23 ∷
   re 7 5 (ℓ "乙") ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q22 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q18 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q21 ∷
   rw 8 q18 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q21 ∷
   rw 10 q18 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q22 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q22 ∷
   rw 7 q21 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q22 ∷
   rw 5 q21 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q22 ∷
   rw 5 q23 ∷
   re 5 5 (ℓ "乙") ∷
   re 3 1 (ℓ "乏丧乏") ∷
   rw 5 q22 ∷
   rw 2 q19 ∷
   re 1 1 (ℓ "乏乙乏") ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q18 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q21 ∷
   rw 5 q18 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q21 ∷
   rw 7 q18 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q22 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q22 ∷
   rw 4 q21 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q22 ∷
   rw 2 q21 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q22 ∷
   rw 2 q23 ∷
   re 2 5 (ℓ "乙") ∷
   re 0 1 (ℓ "乏丶乏") ∷
   rw 2 q22 ∷
   rw 1 q14 ∷
   rw 0 q24 ∷
   rw 1 q22 ∷ []) Eq.refl

private
  q25 : Eqn
  q25 = sE 3207 lem-PP2≡E-at3012
  q26 : Eqn
  q26 = wE 2569 W

-- L87 CS0: 44 steps
lem-L87-CS0 : ⟪ (ℓ "丌丘九中九丮丌丘丌丘丞九中九丮丌丘丞丌乣义乣乊丌丌丞乣义乣乊丌丞九中九丮丞九中九丮丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒书义书乊丌丒丌丒书义书乊丌丒") ⟫ʷ ≈ ⟪ (ℓ "丠") ⟫ʷ
lem-L87-CS0 = derive (ℓ "丌丘九中九丮丌丘丌丘丞九中九丮丌丘丞丌乣义乣乊丌丌丞乣义乣乊丌丞九中九丮丞九中九丮丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒书义书乊丌丒丌丒书义书乊丌丒") (ℓ "丠")
  (rw⁻ 7 q3 ∷
   rw 8 q1 ∷
   rw 6 q4 ∷
   rw 12 q2 ∷
   rw⁻ 13 q3 ∷
   rw 11 q5 ∷
   rw 12 q4 ∷
   rw 17 q4 ∷
   rw 22 q5 ∷
   rw 39 q6 ∷
   rw 44 q7 ∷
   rw 45 q6 ∷
   rw 49 q6 ∷
   rw 54 q7 ∷
   rw⁻ 55 q13 ∷
   rw 56 q6 ∷
   rw⁻ 61 q13 ∷
   rw 62 q6 ∷
   rw 60 q4 ∷
   rw 66 q7 ∷
   rw⁻ 67 q13 ∷
   rw 68 q6 ∷
   rw 65 q5 ∷
   rw 66 q4 ∷
   rw⁻ 71 q13 ∷
   rw 72 q6 ∷
   rw 70 q4 ∷
   rw 76 q7 ∷
   rw⁻ 77 q13 ∷
   rw 78 q6 ∷
   rw 75 q5 ∷
   rw 76 q4 ∷
   rw⁻ 81 q13 ∷
   rw 82 q6 ∷
   rw 80 q4 ∷
   rw 76 q25 ∷
   rw 2 q9 ∷
   rw 16 q9 ∷
   rw 40 q9 ∷
   rw 42 q9 ∷
   rw 5 q10 ∷
   rw 11 q8 ∷
   rw 13 q8 ∷
   rw 0 q26 ∷ []) Eq.refl

private
  q27 : Eqn
  q27 = wE 2570 W

-- L87 CS1: 33 steps
lem-L87-CS1 : ⟪ (ℓ "九中九丮丞九中九丮丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒书义书乊丌丒丌丒书义书乊丌丒") ⟫ʷ ≈ ⟪ (ℓ "丶") ⟫ʷ
lem-L87-CS1 = derive (ℓ "九中九丮丞九中九丮丞丒习丽习举丒丒丞习丽习举丒丞丒习丽习举丒丒丞习丽习举丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒九中九丮丌丒丌丒丞九中九丮丌丒丞丌丒书义书乊丌丒丌丒书义书乊丌丒") (ℓ "丶")
  (rw 15 q6 ∷
   rw 20 q7 ∷
   rw 21 q6 ∷
   rw 25 q6 ∷
   rw 30 q7 ∷
   rw⁻ 31 q13 ∷
   rw 32 q6 ∷
   rw⁻ 37 q13 ∷
   rw 38 q6 ∷
   rw 36 q4 ∷
   rw 42 q7 ∷
   rw⁻ 43 q13 ∷
   rw 44 q6 ∷
   rw 41 q5 ∷
   rw 42 q4 ∷
   rw⁻ 47 q13 ∷
   rw 48 q6 ∷
   rw 46 q4 ∷
   rw 52 q7 ∷
   rw⁻ 53 q13 ∷
   rw 54 q6 ∷
   rw 51 q5 ∷
   rw 52 q4 ∷
   rw⁻ 57 q13 ∷
   rw 58 q6 ∷
   rw 56 q4 ∷
   rw 52 q25 ∷
   rw 0 q9 ∷
   rw 24 q9 ∷
   rw 26 q9 ∷
   rw 3 q8 ∷
   rw 5 q8 ∷
   rw 0 q27 ∷ []) Eq.refl

private
  q28 : Eqn
  q28 = sE 2862 lem-PP2≡E-at1023
  q29 : Eqn
  q29 = sE 3209 lem-L87-merge-p-0123-1
  q30 : Eqn
  q30 = wE 5 W
  q31 : Eqn
  q31 = eqn (ℓ "並义") (ℓ "义並") (low-comm (Swap) (CS))
  q32 : Eqn
  q32 = wE 30 W
  q33 : Eqn
  q33 = eqn (ℓ "並乊") (ℓ "乊並") (low-comm (Swap) ((CS • CS • CS)))
  q34 : Eqn
  q34 = eqn (ℓ "並乏") (ℓ "乏並") (low-comm (Swap) (Swap))
  q35 : Eqn
  q35 = wE 27 W
  q36 : Eqn
  q36 = wE 31 W
  q37 : Eqn
  q37 = wE 7 W
  q38 : Eqn
  q38 = wE 74 W
  q39 : Eqn
  q39 = wE 26 W
  q40 : Eqn
  q40 = wE 2571 W

-- L87 CS2: 53 steps
lem-L87-CS2 : ⟪ (ℓ "九中九丮丒九中九丮丒习丽习举习丽习举") ⟫ʷ ≈ ⟪ (ℓ "义") ⟫ʷ
lem-L87-CS2 = derive (ℓ "九中九丮丒九中九丮丒习丽习举习丽习举") (ℓ "义")
  (rw 10 q28 ∷
   rw 0 q29 ∷
   rw 3 q30 ∷
   re 2 1 (ℓ "並乜並") ∷
   re 3 1 (ℓ "义丹乊丹丽") ∷
   rw 2 q31 ∷
   rw 3 q32 ∷
   rw 4 q33 ∷
   rw 5 q32 ∷
   re 7 1 (ℓ "乏丶乏") ∷
   rw 6 q34 ∷
   rw 7 q35 ∷
   rw 8 q34 ∷
   re 6 3 (ℓ "中") ∷
   rw 7 q36 ∷
   re 6 1 (ℓ "乏丧乏") ∷
   rw⁻ 8 q34 ∷
   rw 7 q37 ∷
   rw⁻ 6 q34 ∷
   re 7 3 (ℓ "丽") ∷
   rw 5 q38 ∷
   rw⁻ 4 q33 ∷
   rw 3 q38 ∷
   rw⁻ 2 q31 ∷
   rw 3 q39 ∷
   re 3 5 (ℓ "乜") ∷
   re 1 1 (ℓ "並乜並") ∷
   re 2 1 (ℓ "义丹乊丹丽") ∷
   rw 1 q31 ∷
   rw 2 q32 ∷
   rw 3 q33 ∷
   rw 4 q32 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q34 ∷
   rw 6 q35 ∷
   rw 7 q34 ∷
   re 5 3 (ℓ "中") ∷
   rw 6 q36 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw⁻ 7 q34 ∷
   rw 6 q37 ∷
   rw⁻ 5 q34 ∷
   re 6 3 (ℓ "丽") ∷
   rw 4 q38 ∷
   rw⁻ 3 q33 ∷
   rw 2 q38 ∷
   rw⁻ 1 q31 ∷
   rw 2 q39 ∷
   re 2 5 (ℓ "乜") ∷
   rw⁻ 0 q31 ∷
   rw 1 q40 ∷
   rw 0 q31 ∷
   rw 1 q36 ∷ []) Eq.refl

private
  q41 : Eqn
  q41 = sE 3093 lem-merge-R0
  q42 : Eqn
  q42 = wE 2572 W

-- L87 X0: 33 steps
lem-L87-X0 : ⟪ (ℓ "丈丈丌丒丘丈上中九丮九下三丌丒丘丌丒丘丞丈上中九丮九下三丌丒丘丞丌丘丈上中九丮九下三丌丘丌丘丞丈上中九丮九下三丌丘丞丌丈上中九丮九下三丌丌丞丈上中九丮九下三丌丞丌丒丈上中九丮九下三丌丒丌丒丞丈上中九丮九下三丌丒丞") ⟫ʷ ≈ ⟪ (ℓ "丌") ⟫ʷ
lem-L87-X0 = derive (ℓ "丈丈丌丒丘丈上中九丮九下三丌丒丘丌丒丘丞丈上中九丮九下三丌丒丘丞丌丘丈上中九丮九下三丌丘丌丘丞丈上中九丮九下三丌丘丞丌丈上中九丮九下三丌丌丞丈上中九丮九下三丌丞丌丒丈上中九丮九下三丌丒丌丒丞丈上中九丮九下三丌丒丞") (ℓ "丌")
  (rw⁻ 15 q3 ∷
   rw⁻ 16 q15 ∷
   rw 17 q1 ∷
   rw⁻ 14 q13 ∷
   rw 15 q6 ∷
   rw 13 q4 ∷
   rw 24 q2 ∷
   rw⁻ 25 q3 ∷
   rw 26 q1 ∷
   rw 23 q7 ∷
   rw⁻ 24 q13 ∷
   rw 22 q5 ∷
   rw 23 q4 ∷
   rw⁻ 33 q3 ∷
   rw 34 q1 ∷
   rw 32 q4 ∷
   rw 42 q2 ∷
   rw⁻ 43 q3 ∷
   rw 41 q5 ∷
   rw 42 q4 ∷
   rw 51 q4 ∷
   rw 60 q5 ∷
   rw 61 q4 ∷
   rw⁻ 71 q13 ∷
   rw 72 q6 ∷
   rw 70 q4 ∷
   rw 80 q7 ∷
   rw 79 q5 ∷
   rw 5 q41 ∷
   rw 10 q41 ∷
   rw 15 q41 ∷
   rw 20 q41 ∷
   rw 0 q42 ∷ []) Eq.refl
