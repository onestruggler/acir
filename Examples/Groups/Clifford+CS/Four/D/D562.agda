{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Four.WinSig using (Ws ; wn)
open import Examples.Groups.Clifford+CS.Four.DEqn using (wE)
open import Examples.Groups.Clifford+CS.Four.DStmt using (St)
open import Examples.Groups.Clifford+CS.Four.DSig using (SD562 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Four.D.D562 (W : Ws) (Sᴰ : SD562) where

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
  lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-vs-X3-TOFF123-X3 : St 972
  lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-vs-X3-TOFF123-X3 = pickᴰ 0 Sᴰ
  lem-pass-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-vs-X3-TOFF123-X3 : St 973
  lem-pass-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-vs-X3-TOFF123-X3 = pickᴰ 1 Sᴰ
  lem-pass-CCZ013-vs-CCZ123 : St 906
  lem-pass-CCZ013-vs-CCZ123 = pickᴰ 2 Sᴰ
  lem-pass-CCZ013-vs-CZ12 : St 974
  lem-pass-CCZ013-vs-CZ12 = pickᴰ 3 Sᴰ
  lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 : St 975
  lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3 = pickᴰ 4 Sᴰ

private
  q1 : Eqn
  q1 = wE 1612 W
  q2 : Eqn
  q2 = wE 1 W
  q3 : Eqn
  q3 = eqn (ℓ "丐乏") (ℓ "乏丐") (low-comm ((K ↑)) (Swap))
  q4 : Eqn
  q4 = eqn (ℓ "丣乏") (ℓ "乏丣") (low-comm (CX₀₁) (Swap))
  q5 : Eqn
  q5 = eqn (ℓ "一乏") (ℓ "乏一") (low₁-comm (iI) ((Swap ↑)))
  q6 : Eqn
  q6 = wE 3 W
  q7 : Eqn
  q7 = wE 196 W
  q8 : Eqn
  q8 = wE 1347 W
  q9 : Eqn
  q9 = wE 43 W
  q10 : Eqn
  q10 = eqn (ℓ "丑乏") (ℓ "乏丑") (low-comm (((K • iI) ↑)) (Swap))
  q11 : Eqn
  q11 = wE 1509 W
  q12 : Eqn
  q12 = sE 974 lem-pass-CCZ013-vs-CZ12
  q13 : Eqn
  q13 = sE 906 lem-pass-CCZ013-vs-CCZ123
  q14 : Eqn
  q14 = wE 1510 W
  q15 : Eqn
  q15 = wE 1613 W
  q16 : Eqn
  q16 = wE 1450 W

-- pass [TOFF103] [X3 TOFF123 X3]: 112 steps
lem-pass-TOFF103-vs-X3-TOFF123-X3 : ⟪ (ℓ "乡丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞乡") ⟫ʷ
lem-pass-TOFF103-vs-X3-TOFF123-X3 = derive (ℓ "乡丞乢丞") (ℓ "丞乢丞乡")
  (rw 1 q1 ∷
   rw 1 q2 ∷
   re 0 1 (ℓ "乏习乏") ∷
   re 1 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 0 q3 ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw⁻ 6 q3 ∷
   rw⁻ 7 q5 ∷
   rw 8 q6 ∷
   rw 7 q5 ∷
   rw 6 q3 ∷
   re 5 1 (ℓ "乏丧乏") ∷
   rw 7 q6 ∷
   rw 4 q4 ∷
   re 3 1 (ℓ "乏丷乏") ∷
   rw 5 q6 ∷
   rw 2 q4 ∷
   re 1 1 (ℓ "乏丶乏") ∷
   rw 3 q6 ∷
   rw 0 q3 ∷
   rw 1 q7 ∷
   re 1 8 (ℓ "习") ∷
   rw 1 q8 ∷
   rw⁻ 0 q3 ∷
   re 2 1 (ℓ "丶丣丷丣丧") ∷
   rw 3 q2 ∷
   re 1 3 (ℓ "丽") ∷
   rw⁻ 2 q4 ∷
   rw 5 q2 ∷
   re 3 3 (ℓ "举") ∷
   rw⁻ 4 q4 ∷
   rw 7 q2 ∷
   re 5 3 (ℓ "中") ∷
   rw 1 q2 ∷
   re 3 1 (ℓ "乏丶乏") ∷
   rw 2 q6 ∷
   rw⁻ 3 q4 ∷
   re 5 1 (ℓ "乏丷乏") ∷
   rw 4 q6 ∷
   rw⁻ 5 q4 ∷
   re 7 1 (ℓ "乏丧乏") ∷
   rw 6 q6 ∷
   rw 2 q9 ∷
   re 2 5 (ℓ "乙") ∷
   re 1 3 (ℓ "乚") ∷
   rw⁻ 2 q10 ∷
   rw 3 q6 ∷
   rw 2 q11 ∷
   rw 1 q12 ∷
   rw 2 q13 ∷
   rw 3 q14 ∷
   rw 0 q15 ∷
   rw 6 q2 ∷
   rw 5 q10 ∷
   re 4 1 (ℓ "乏乙乏") ∷
   re 5 1 (ℓ "丶丣丷丣丧") ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw 9 q6 ∷
   re 8 1 (ℓ "乏丧乏") ∷
   rw 10 q6 ∷
   rw 7 q4 ∷
   re 6 1 (ℓ "乏丷乏") ∷
   rw 8 q6 ∷
   rw 5 q4 ∷
   re 4 1 (ℓ "乏丶乏") ∷
   rw 6 q6 ∷
   rw 5 q9 ∷
   re 5 5 (ℓ "乙") ∷
   rw 3 q3 ∷
   rw 4 q16 ∷
   re 4 1 (ℓ "丐丶丣丷丣丧丐一") ∷
   rw⁻ 3 q3 ∷
   rw 6 q2 ∷
   re 4 3 (ℓ "丽") ∷
   rw⁻ 5 q4 ∷
   rw 8 q2 ∷
   re 6 3 (ℓ "举") ∷
   rw⁻ 7 q4 ∷
   rw 10 q2 ∷
   re 8 3 (ℓ "中") ∷
   rw⁻ 9 q3 ∷
   rw⁻ 10 q5 ∷
   rw 3 q2 ∷
   rw⁻ 4 q3 ∷
   re 6 1 (ℓ "乏丶乏") ∷
   rw 5 q6 ∷
   rw⁻ 6 q4 ∷
   re 8 1 (ℓ "乏丷乏") ∷
   rw 7 q6 ∷
   rw⁻ 8 q4 ∷
   re 10 1 (ℓ "乏丧乏") ∷
   rw 9 q6 ∷
   rw⁻ 10 q3 ∷
   rw⁻ 11 q5 ∷
   rw 4 q7 ∷
   re 4 8 (ℓ "习") ∷
   re 3 3 (ℓ "乡") ∷
   rw 4 q6 ∷ []) Eq.refl

private
  q17 : Eqn
  q17 = wE 1614 W
  q18 : Eqn
  q18 = sE 975 lem-pass-CK32-CS23-CS23-CKd32-vs-X3-TOFF123-X3
  q19 : Eqn
  q19 = sE 973 lem-pass-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-vs-X3-TOFF123-X3
  q20 : Eqn
  q20 = wE 1615 W

-- pass [X2 CS23 CS23 CS23 CK32 CS23 CS23 CX31 CS12 CS12 CS12 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CS12 CK12 CS12 CS12 X2] [X3 TOFF123 X3]: 5 steps
lem-pass-X2-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-vs-X3-TOFF123-X3 : ⟪ (ℓ "丘义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞丘义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘") ⟫ʷ
lem-pass-X2-CS23-CS23-CS23-CK32-CS23-CS23-CX31-CS12-CS12-CS12-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CS12-CK12-CS12-CS12-X2-vs-X3-TOFF123-X3 = derive (ℓ "丘义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘丞乢丞") (ℓ "丞乢丞丘义义义乗义义乓丶丶丶丶丶丶为与丶丶丶丶丶丶丶丶丶乓丶丶丶为丶丶丘")
  (rw 0 q17 ∷
   rw 35 q18 ∷
   rw 4 q19 ∷
   rw 0 q18 ∷
   rw 3 q20 ∷ []) Eq.refl

private
  q21 : Eqn
  q21 = wE 1616 W
  q22 : Eqn
  q22 = sE 972 lem-pass-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-vs-X3-TOFF123-X3
  q23 : Eqn
  q23 = wE 1617 W

-- pass [X2 CS23 CS23 CK32 CS23 CK32 CK32 CX31 CK12 S1 CK12 S1 CS12 CS12 CS12 CK12 S1 CS12 CS12 CS12 CS12 CS12 CS12 CX31 CS12 CS12 CK12 CS12 CK12 CK12 X2] [X3 TOFF123 X3]: 5 steps
lem-pass-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-vs-X3-TOFF123-X3 : ⟪ (ℓ "丘义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞乢丞") ⟫ʷ ≈ ⟪ (ℓ "丞乢丞丘义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘") ⟫ʷ
lem-pass-X2-CS23-CS23-CK32-CS23-CK32-CK32-CX31-CK12-S1-CK12-S1-CS12-CS12-CS12-CK12-S1-CS12-CS12-CS12-CS12-CS12-CS12-CX31-CS12-CS12-CK12-CS12-CK12-CK12-X2-vs-X3-TOFF123-X3 = derive (ℓ "丘义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘丞乢丞") (ℓ "丞乢丞丘义义乗义乗乗乓为与为与丶丶丶为与丶丶丶丶丶丶乓丶丶为丶为为丘")
  (rw 0 q21 ∷
   rw 33 q18 ∷
   rw 4 q22 ∷
   rw 0 q18 ∷
   rw 3 q23 ∷ []) Eq.refl
