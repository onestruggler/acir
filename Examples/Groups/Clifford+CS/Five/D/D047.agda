{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD047 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D047 (Sᴰ : SD047) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-comm-CCZ013-CK42 : Ws → St 1465
  lem-comm-CCZ013-CK42 = pickᴰ 0 Sᴰ
  lem-comm-CK41-CCZ023 : Ws → St 1221
  lem-comm-CK41-CCZ023 = pickᴰ 1 Sᴰ
  lem-comm-CK42-CCZ013 : Ws → St 1466
  lem-comm-CK42-CCZ013 = pickᴰ 2 Sᴰ
  lem-comm-CCZ023-CK41 : Ws → St 1224
  lem-comm-CCZ023-CK41 = pickᴰ 3 Sᴰ
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 4 Sᴰ
  lem-F4-I-S2 : Ws → St 1595
  lem-F4-I-S2 = pickᴰ 5 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 6 Sᴰ
  lem-F4-S2-I : Ws → St 1597
  lem-F4-S2-I = pickᴰ 7 Sᴰ
  lem-F4-S2-K3 : Ws → St 1598
  lem-F4-S2-K3 = pickᴰ 8 Sᴰ
  lem-F4-S2-S2 : Ws → St 1599
  lem-F4-S2-S2 = pickᴰ 9 Sᴰ
  lem-F4-I-K2-at132132 : Ws → St 1600
  lem-F4-I-K2-at132132 = pickᴰ 10 Sᴰ
  lem-F4-I-S3-at132132 : Ws → St 1601
  lem-F4-I-S3-at132132 = pickᴰ 11 Sᴰ
  lem-F4-K2-K2-at132132 : Ws → St 1602
  lem-F4-K2-K2-at132132 = pickᴰ 12 Sᴰ
  lem-F4-S3-I-at132132 : Ws → St 1603
  lem-F4-S3-I-at132132 = pickᴰ 13 Sᴰ
  lem-F4-S3-K2-at132132 : Ws → St 1604
  lem-F4-S3-K2-at132132 = pickᴰ 14 Sᴰ
  lem-F4-S3-S3-at132132 : Ws → St 1605
  lem-F4-S3-S3-at132132 = pickᴰ 15 Sᴰ
  lem-box-cP-at0210233441 : Ws → St 1042
  lem-box-cP-at0210233441 = pickᴰ 16 Sᴰ
  lem-box-cP-at233442 : Ws → St 1129
  lem-box-cP-at233442 = pickᴰ 17 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 18 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1606
  lem-F4-CS2-S2 = pickᴰ 19 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 20 Sᴰ
  lem-F4-S2-CS2 : Ws → St 1607
  lem-F4-S2-CS2 = pickᴰ 21 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 22 Sᴰ
  lem-F4-CS2-CS2-at132132 : Ws → St 1608
  lem-F4-CS2-CS2-at132132 = pickᴰ 23 Sᴰ
  lem-F4-CS2-I-at132132 : Ws → St 1609
  lem-F4-CS2-I-at132132 = pickᴰ 24 Sᴰ
  lem-F4-CS2-K2-at132132 : Ws → St 1610
  lem-F4-CS2-K2-at132132 = pickᴰ 25 Sᴰ
  lem-F4-CS2-S3-at132132 : Ws → St 1611
  lem-F4-CS2-S3-at132132 = pickᴰ 26 Sᴰ
  lem-F4-I-CS2-at132132 : Ws → St 1612
  lem-F4-I-CS2-at132132 = pickᴰ 27 Sᴰ
  lem-F4-K2-CS2-at132132 : Ws → St 1613
  lem-F4-K2-CS2-at132132 = pickᴰ 28 Sᴰ
  lem-F4-S3-CS2-at132132 : Ws → St 1614
  lem-F4-S3-CS2-at132132 = pickᴰ 29 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 30 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 31 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 32 Sᴰ
  lem-box-perm-1423-at0210243143 : Ws → St 1496
  lem-box-perm-1423-at0210243143 = pickᴰ 33 Sᴰ
  lem-box-perm-1423-at243243 : Ws → St 1497
  lem-box-perm-1423-at243243 = pickᴰ 34 Sᴰ
  lem-F5-23-at132132 : Ws → St 1617
  lem-F5-23-at132132 = pickᴰ 35 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1617 (lem-F5-23-at132132 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1608 (lem-F4-CS2-CS2-at132132 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 1417 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1613 (lem-F4-K2-CS2-at132132 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1610 (lem-F4-CS2-K2-at132132 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1602 (lem-F4-K2-K2-at132132 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1418 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1614 (lem-F4-S3-CS2-at132132 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1604 (lem-F4-S3-K2-at132132 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1605 (lem-F4-S3-S3-at132132 c4)
  q11 : Ws → Eqn
  q11 c4 = wlE 1411 (lit c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1601 (lem-F4-I-S3-at132132 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1612 (lem-F4-I-CS2-at132132 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1600 (lem-F4-I-K2-at132132 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1603 (lem-F4-S3-I-at132132 c4)

-- deb-P-hi-split-a @132132: 136 steps
lem-deb-P-hi-split-a-at132132 : Ws → ⟪ (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-P-hi-split-a-at132132 c4 = derive (CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw⁻ 4 (q1 c4) ∷
   rw⁻ 3 (q2 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q2 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw⁻ 12 (q1 c4) ∷
   rw⁻ 11 (q2 c4) ∷
   rw⁻ 10 (q2 c4) ∷
   rw⁻ 9 (q2 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 13 (q2 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw⁻ 20 (q1 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw⁻ 17 (q2 c4) ∷
   rw⁻ 16 (q2 c4) ∷
   rw⁻ 15 (q2 c4) ∷
   rw⁻ 24 (q1 c4) ∷
   rw⁻ 23 (q2 c4) ∷
   rw⁻ 22 (q2 c4) ∷
   rw⁻ 21 (q2 c4) ∷
   rw⁻ 20 (q2 c4) ∷
   rw⁻ 19 (q2 c4) ∷
   rw⁻ 18 (q2 c4) ∷
   rw 28 (q3 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 25 (q4 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw⁻ 32 (q1 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 28 (q2 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 26 (q2 c4) ∷
   rw⁻ 25 (q2 c4) ∷
   rw⁻ 24 (q2 c4) ∷
   rw 36 (q3 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 34 (q6 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 39 (q5 c4) ∷
   rw⁻ 38 (q2 c4) ∷
   rw⁻ 37 (q5 c4) ∷
   rw⁻ 36 (q2 c4) ∷
   rw⁻ 35 (q2 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 33 (q2 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 30 (q2 c4) ∷
   rw 44 (q7 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 42 (q9 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q9 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw⁻ 35 (q8 c4) ∷
   rw⁻ 34 (q8 c4) ∷
   rw⁻ 33 (q8 c4) ∷
   rw 48 (q7 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 45 (q9 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 43 (q9 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q8 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 38 (q8 c4) ∷
   rw⁻ 37 (q8 c4) ∷
   rw⁻ 36 (q8 c4) ∷
   rw 52 (q7 c4) ∷
   rw⁻ 51 (q10 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 48 (q9 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   rw⁻ 46 (q9 c4) ∷
   rw⁻ 45 (q8 c4) ∷
   rw⁻ 44 (q8 c4) ∷
   rw⁻ 43 (q8 c4) ∷
   rw⁻ 42 (q8 c4) ∷
   rw⁻ 41 (q8 c4) ∷
   rw⁻ 40 (q8 c4) ∷
   rw⁻ 39 (q8 c4) ∷
   rw⁻ 56 (q11 c4) ∷
   rw⁻ 55 (q12 c4) ∷
   rw⁻ 54 (q12 c4) ∷
   rw⁻ 53 (q12 c4) ∷
   rw⁻ 52 (q13 c4) ∷
   rw⁻ 51 (q14 c4) ∷
   rw⁻ 50 (q13 c4) ∷
   rw⁻ 49 (q14 c4) ∷
   rw⁻ 48 (q13 c4) ∷
   rw⁻ 47 (q13 c4) ∷
   rw⁻ 46 (q13 c4) ∷
   rw⁻ 45 (q13 c4) ∷
   rw⁻ 44 (q13 c4) ∷
   rw⁻ 43 (q13 c4) ∷
   rw⁻ 42 (q13 c4) ∷
   rw 60 (q7 c4) ∷
   rw⁻ 59 (q15 c4) ∷
   rw⁻ 58 (q10 c4) ∷
   rw⁻ 57 (q10 c4) ∷
   rw⁻ 56 (q10 c4) ∷
   rw⁻ 55 (q8 c4) ∷
   rw⁻ 54 (q9 c4) ∷
   rw⁻ 53 (q8 c4) ∷
   rw⁻ 52 (q9 c4) ∷
   rw⁻ 51 (q8 c4) ∷
   rw⁻ 50 (q8 c4) ∷
   rw⁻ 49 (q8 c4) ∷
   rw⁻ 48 (q8 c4) ∷
   rw⁻ 47 (q8 c4) ∷
   rw⁻ 46 (q8 c4) ∷
   rw⁻ 45 (q8 c4) ∷ []) Eq.refl

private
  q16 : Ws → Eqn
  q16 c4 = sE 1609 (lem-F4-CS2-I-at132132 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1611 (lem-F4-CS2-S3-at132132 c4)

-- deb-P-hi-split-b @132132: 66 steps
lem-deb-P-hi-split-b-at132132 : Ws → ⟪ (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-deb-P-hi-split-b-at132132 c4 = derive (CS12 ∷ K1 ∷ CS12 ∷ K1 ∷ CS12 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS12 ∷ CS12 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  (rw⁻ 0 (q1 c4) ∷
   rw 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 8 (q1 c4) ∷
   rw⁻ 7 (q5 c4) ∷
   rw⁻ 6 (q2 c4) ∷
   rw 12 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 10 (q6 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 16 (q1 c4) ∷
   rw⁻ 15 (q5 c4) ∷
   rw⁻ 14 (q2 c4) ∷
   rw⁻ 13 (q5 c4) ∷
   rw⁻ 12 (q2 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q8 c4) ∷
   rw⁻ 18 (q9 c4) ∷
   rw⁻ 17 (q8 c4) ∷
   rw⁻ 16 (q9 c4) ∷
   rw⁻ 15 (q8 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q8 c4) ∷
   rw⁻ 21 (q9 c4) ∷
   rw⁻ 20 (q8 c4) ∷
   rw⁻ 19 (q9 c4) ∷
   rw⁻ 18 (q8 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q10 c4) ∷
   rw⁻ 26 (q10 c4) ∷
   rw⁻ 25 (q8 c4) ∷
   rw⁻ 24 (q9 c4) ∷
   rw⁻ 23 (q8 c4) ∷
   rw⁻ 22 (q9 c4) ∷
   rw⁻ 21 (q8 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q12 c4) ∷
   rw⁻ 30 (q12 c4) ∷
   rw⁻ 29 (q12 c4) ∷
   rw⁻ 28 (q13 c4) ∷
   rw⁻ 27 (q14 c4) ∷
   rw⁻ 26 (q13 c4) ∷
   rw⁻ 25 (q14 c4) ∷
   rw⁻ 24 (q13 c4) ∷
   rw⁻ 36 (q1 c4) ∷
   rw⁻ 35 (q16 c4) ∷
   rw⁻ 34 (q17 c4) ∷
   rw⁻ 33 (q17 c4) ∷
   rw⁻ 32 (q17 c4) ∷
   rw⁻ 31 (q2 c4) ∷
   rw⁻ 30 (q5 c4) ∷
   rw⁻ 29 (q2 c4) ∷
   rw⁻ 28 (q5 c4) ∷
   rw⁻ 27 (q2 c4) ∷
   rw⁻ 40 (q1 c4) ∷
   rw⁻ 39 (q2 c4) ∷
   rw⁻ 38 (q16 c4) ∷
   rw⁻ 37 (q17 c4) ∷
   rw⁻ 36 (q17 c4) ∷
   rw⁻ 35 (q17 c4) ∷
   rw⁻ 34 (q2 c4) ∷
   rw⁻ 33 (q5 c4) ∷
   rw⁻ 32 (q2 c4) ∷
   rw⁻ 31 (q5 c4) ∷
   rw⁻ 30 (q2 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = sE 1590 (lem-F5-23 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 1419 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1607 (lem-F4-S2-CS2 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1598 (lem-F4-S2-K3 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1599 (lem-F4-S2-S2 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1595 (lem-F4-I-S2 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1411 (lem-F4-I-K3 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1597 (lem-F4-S2-I c4)

-- deb-P-lo-split-a: 136 steps
lem-deb-P-lo-split-a : Ws → ⟪ (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-P-lo-split-a c4 = derive (CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw⁻ 4 (q18 c4) ∷
   rw⁻ 3 (q19 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q19 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw⁻ 12 (q18 c4) ∷
   rw⁻ 11 (q19 c4) ∷
   rw⁻ 10 (q19 c4) ∷
   rw⁻ 9 (q19 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 13 (q19 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw⁻ 20 (q18 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw⁻ 17 (q19 c4) ∷
   rw⁻ 16 (q19 c4) ∷
   rw⁻ 15 (q19 c4) ∷
   rw⁻ 24 (q18 c4) ∷
   rw⁻ 23 (q19 c4) ∷
   rw⁻ 22 (q19 c4) ∷
   rw⁻ 21 (q19 c4) ∷
   rw⁻ 20 (q19 c4) ∷
   rw⁻ 19 (q19 c4) ∷
   rw⁻ 18 (q19 c4) ∷
   rw 28 (q20 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 26 (q21 c4) ∷
   rw⁻ 25 (q21 c4) ∷
   rw⁻ 24 (q21 c4) ∷
   rw⁻ 23 (q21 c4) ∷
   rw⁻ 22 (q21 c4) ∷
   rw⁻ 21 (q21 c4) ∷
   rw⁻ 32 (q18 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw⁻ 29 (q19 c4) ∷
   rw⁻ 28 (q19 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 26 (q19 c4) ∷
   rw⁻ 25 (q19 c4) ∷
   rw⁻ 24 (q19 c4) ∷
   rw 36 (q20 c4) ∷
   rw⁻ 35 (q21 c4) ∷
   rw⁻ 34 (q23 c4) ∷
   rw⁻ 33 (q21 c4) ∷
   rw⁻ 32 (q21 c4) ∷
   rw⁻ 31 (q21 c4) ∷
   rw⁻ 30 (q21 c4) ∷
   rw⁻ 29 (q21 c4) ∷
   rw⁻ 28 (q21 c4) ∷
   rw⁻ 27 (q21 c4) ∷
   rw⁻ 40 (q18 c4) ∷
   rw⁻ 39 (q22 c4) ∷
   rw⁻ 38 (q19 c4) ∷
   rw⁻ 37 (q22 c4) ∷
   rw⁻ 36 (q19 c4) ∷
   rw⁻ 35 (q19 c4) ∷
   rw⁻ 34 (q19 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw⁻ 30 (q19 c4) ∷
   rw 44 (q7 c4) ∷
   rw⁻ 43 (q24 c4) ∷
   rw⁻ 42 (q25 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw⁻ 40 (q25 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw⁻ 38 (q24 c4) ∷
   rw⁻ 37 (q24 c4) ∷
   rw⁻ 36 (q24 c4) ∷
   rw⁻ 35 (q24 c4) ∷
   rw⁻ 34 (q24 c4) ∷
   rw⁻ 33 (q24 c4) ∷
   rw 48 (q7 c4) ∷
   rw⁻ 47 (q26 c4) ∷
   rw⁻ 46 (q24 c4) ∷
   rw⁻ 45 (q25 c4) ∷
   rw⁻ 44 (q24 c4) ∷
   rw⁻ 43 (q25 c4) ∷
   rw⁻ 42 (q24 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw⁻ 40 (q24 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw⁻ 38 (q24 c4) ∷
   rw⁻ 37 (q24 c4) ∷
   rw⁻ 36 (q24 c4) ∷
   rw 52 (q7 c4) ∷
   rw⁻ 51 (q26 c4) ∷
   rw⁻ 50 (q26 c4) ∷
   rw⁻ 49 (q24 c4) ∷
   rw⁻ 48 (q25 c4) ∷
   rw⁻ 47 (q24 c4) ∷
   rw⁻ 46 (q25 c4) ∷
   rw⁻ 45 (q24 c4) ∷
   rw⁻ 44 (q24 c4) ∷
   rw⁻ 43 (q24 c4) ∷
   rw⁻ 42 (q24 c4) ∷
   rw⁻ 41 (q24 c4) ∷
   rw⁻ 40 (q24 c4) ∷
   rw⁻ 39 (q24 c4) ∷
   rw⁻ 56 (q11 c4) ∷
   rw⁻ 55 (q27 c4) ∷
   rw⁻ 54 (q27 c4) ∷
   rw⁻ 53 (q27 c4) ∷
   rw⁻ 52 (q28 c4) ∷
   rw⁻ 51 (q29 c4) ∷
   rw⁻ 50 (q28 c4) ∷
   rw⁻ 49 (q29 c4) ∷
   rw⁻ 48 (q28 c4) ∷
   rw⁻ 47 (q28 c4) ∷
   rw⁻ 46 (q28 c4) ∷
   rw⁻ 45 (q28 c4) ∷
   rw⁻ 44 (q28 c4) ∷
   rw⁻ 43 (q28 c4) ∷
   rw⁻ 42 (q28 c4) ∷
   rw 60 (q7 c4) ∷
   rw⁻ 59 (q30 c4) ∷
   rw⁻ 58 (q26 c4) ∷
   rw⁻ 57 (q26 c4) ∷
   rw⁻ 56 (q26 c4) ∷
   rw⁻ 55 (q24 c4) ∷
   rw⁻ 54 (q25 c4) ∷
   rw⁻ 53 (q24 c4) ∷
   rw⁻ 52 (q25 c4) ∷
   rw⁻ 51 (q24 c4) ∷
   rw⁻ 50 (q24 c4) ∷
   rw⁻ 49 (q24 c4) ∷
   rw⁻ 48 (q24 c4) ∷
   rw⁻ 47 (q24 c4) ∷
   rw⁻ 46 (q24 c4) ∷
   rw⁻ 45 (q24 c4) ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = sE 1576 (lem-F4-CS2-I c4)
  q32 : Ws → Eqn
  q32 c4 = sE 1606 (lem-F4-CS2-S2 c4)

-- deb-P-lo-split-b: 66 steps
lem-deb-P-lo-split-b : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ
lem-deb-P-lo-split-b c4 = derive (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ CS23 ∷ CS23 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q22 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 13 (q22 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q24 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q26 c4) ∷
   rw⁻ 22 (q24 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 20 (q24 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw⁻ 18 (q24 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q26 c4) ∷
   rw⁻ 26 (q26 c4) ∷
   rw⁻ 25 (q24 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw⁻ 21 (q24 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q27 c4) ∷
   rw⁻ 30 (q27 c4) ∷
   rw⁻ 29 (q27 c4) ∷
   rw⁻ 28 (q28 c4) ∷
   rw⁻ 27 (q29 c4) ∷
   rw⁻ 26 (q28 c4) ∷
   rw⁻ 25 (q29 c4) ∷
   rw⁻ 24 (q28 c4) ∷
   rw⁻ 36 (q18 c4) ∷
   rw⁻ 35 (q31 c4) ∷
   rw⁻ 34 (q32 c4) ∷
   rw⁻ 33 (q32 c4) ∷
   rw⁻ 32 (q32 c4) ∷
   rw⁻ 31 (q19 c4) ∷
   rw⁻ 30 (q22 c4) ∷
   rw⁻ 29 (q19 c4) ∷
   rw⁻ 28 (q22 c4) ∷
   rw⁻ 27 (q19 c4) ∷
   rw⁻ 40 (q18 c4) ∷
   rw⁻ 39 (q19 c4) ∷
   rw⁻ 38 (q31 c4) ∷
   rw⁻ 37 (q32 c4) ∷
   rw⁻ 36 (q32 c4) ∷
   rw⁻ 35 (q32 c4) ∷
   rw⁻ 34 (q19 c4) ∷
   rw⁻ 33 (q22 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw⁻ 31 (q22 c4) ∷
   rw⁻ 30 (q19 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = sE 1496 (lem-box-perm-1423-at0210243143 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1042 (lem-box-cP-at0210233441 c4)
  q35 : Ws → Eqn
  q35 c4 = eqn (CCZ023 ∷ X4 ∷ []) (X4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (X))
  q36 : Ws → Eqn
  q36 c4 = sE 1221 (lem-comm-CK41-CCZ023 c4)
  q37 : Ws → Eqn
  q37 c4 = wlE 642 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wpE 517 c4

-- F4-K3-CS2 @02132031: 19 steps
lem-F4-K3-CS2-at02132031 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at02132031 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ [])
  (re 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 5 1 (CS03 ∷ []) ∷
   re 7 1 (CS03⁻ ∷ []) ∷
   rw 3 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw 1 (q36 c4) ∷
   rw⁻ 0 (q35 c4) ∷
   rw⁻ 1 (q37 c4) ∷
   rw⁻ 4 (q35 c4) ∷
   rw 3 (q36 c4) ∷
   rw⁻ 2 (q35 c4) ∷
   rw⁻ 3 (q37 c4) ∷
   rw⁻ 0 (q34 c4) ∷
   rw⁻ 0 (q33 c4) ∷
   rw⁻ 1 (q38 c4) ∷
   re 2 1 (Sb2-0-3-1 ∷ []) ∷
   re 4 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 0 5 (Sb2-0-41-3 ∷ []) ∷ []) Eq.refl

private
  q39 : Ws → Eqn
  q39 c4 = wlE 720 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 614 c4
  q41 : Ws → Eqn
  q41 c4 = wlE 721 (lit c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 722 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = sE 1224 (lem-comm-CCZ023-CK41 c4)
  q44 : Ws → Eqn
  q44 c4 = eqn (CCZ023 ∷ S4 ∷ []) (S4 ∷ CCZ023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑) (S))
  q45 : Ws → Eqn
  q45 c4 = wlE 723 (lit c4)

-- F4-CS2-K3 @02132031: 21 steps
lem-F4-CS2-K3-at02132031 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at02132031 c4 = derive (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ []) (CK41 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q39 c4) ∷
   re 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) ∷
   re 3 1 (CS03 ∷ []) ∷
   re 5 1 (CS03⁻ ∷ []) ∷
   rw⁻ 2 (q40 c4) ∷
   rw 1 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw⁻ 4 (q41 c4) ∷
   rw 3 (q42 c4) ∷
   rw 4 (q43 c4) ∷
   rw 5 (q44 c4) ∷
   rw⁻ 2 (q41 c4) ∷
   rw 1 (q42 c4) ∷
   rw 2 (q43 c4) ∷
   rw 3 (q44 c4) ∷
   rw⁻ 4 (q34 c4) ∷
   rw⁻ 4 (q33 c4) ∷
   re 6 1 (Sb2-0-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-0-3-1 ∷ []) ∷
   re 4 5 (Sb2-0-41-3 ∷ []) ∷
   rw⁻ 0 (q45 c4) ∷ []) Eq.refl

private
  q46 : Ws → Eqn
  q46 c4 = sE 1497 (lem-box-perm-1423-at243243 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 1129 (lem-box-cP-at233442 c4)
  q48 : Ws → Eqn
  q48 c4 = eqn (CCZ013 ∷ X4 ∷ []) (X4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (X))
  q49 : Ws → Eqn
  q49 c4 = sE 1466 (lem-comm-CK42-CCZ013 c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 555 c4
  q51 : Ws → Eqn
  q51 c4 = wlE 685 (lit c4)

-- F4-K3-CS2 @132132: 19 steps
lem-F4-K3-CS2-at132132 : Ws → ⟪ (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ []) ⟫ʷ
lem-F4-K3-CS2-at132132 c4 = derive (X4 ∷ CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ X4 ∷ [])
  (re 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q46 c4) ∷
   rw 3 (q47 c4) ∷
   rw⁻ 2 (q48 c4) ∷
   rw 1 (q49 c4) ∷
   rw⁻ 0 (q48 c4) ∷
   rw⁻ 1 (q50 c4) ∷
   rw⁻ 4 (q48 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 2 (q48 c4) ∷
   rw⁻ 3 (q50 c4) ∷
   rw⁻ 0 (q47 c4) ∷
   rw⁻ 0 (q46 c4) ∷
   rw⁻ 1 (q51 c4) ∷
   re 2 1 (Sb0-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 0 5 (Sb0-1-42-3 ∷ []) ∷ []) Eq.refl

private
  q52 : Ws → Eqn
  q52 c4 = wlE 725 (lit c4)
  q53 : Ws → Eqn
  q53 c4 = wlE 736 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 635 c4
  q55 : Ws → Eqn
  q55 c4 = wlE 737 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = sE 1465 (lem-comm-CCZ013-CK42 c4)
  q57 : Ws → Eqn
  q57 c4 = eqn (CCZ013 ∷ S4 ∷ []) (S4 ∷ CCZ013 ∷ []) (c₄ (Swap ↑ ↑ • CCZ • Swap ↑ ↑) (S))
  q58 : Ws → Eqn
  q58 c4 = wlE 728 (lit c4)

-- F4-CS2-K3 @132132: 21 steps
lem-F4-CS2-K3-at132132 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-K3-at132132 c4 = derive (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ CK42 ∷ []) (CK42 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  (rw⁻ 2 (q52 c4) ∷
   re 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 1 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   rw 3 (q55 c4) ∷
   rw 4 (q56 c4) ∷
   rw 5 (q57 c4) ∷
   rw⁻ 2 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q56 c4) ∷
   rw 3 (q57 c4) ∷
   rw⁻ 4 (q47 c4) ∷
   rw⁻ 4 (q46 c4) ∷
   re 6 1 (Sb0-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻0-1-3-2 ∷ []) ∷
   re 4 5 (Sb0-1-42-3 ∷ []) ∷
   rw⁻ 0 (q58 c4) ∷ []) Eq.refl

-- deb-Q-lo-split-a: 55 steps
lem-deb-Q-lo-split-a : Ws → ⟪ (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-deb-Q-lo-split-a c4 = derive (CS23 ∷ K3 ∷ CS23 ∷ K3 ∷ CS23 ∷ S2 ∷ S2 ∷ S2 ∷ ι ∷ S2 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ [])
  (rw⁻ 0 (q18 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 3 (q21 c4) ∷
   rw⁻ 8 (q18 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw⁻ 6 (q19 c4) ∷
   rw 12 (q20 c4) ∷
   rw⁻ 11 (q21 c4) ∷
   rw⁻ 10 (q23 c4) ∷
   rw⁻ 9 (q21 c4) ∷
   rw⁻ 16 (q18 c4) ∷
   rw⁻ 15 (q22 c4) ∷
   rw⁻ 14 (q19 c4) ∷
   rw⁻ 13 (q22 c4) ∷
   rw⁻ 12 (q19 c4) ∷
   rw 20 (q7 c4) ∷
   rw⁻ 19 (q24 c4) ∷
   rw⁻ 18 (q25 c4) ∷
   rw⁻ 17 (q24 c4) ∷
   rw⁻ 16 (q25 c4) ∷
   rw⁻ 15 (q24 c4) ∷
   rw 24 (q7 c4) ∷
   rw⁻ 23 (q26 c4) ∷
   rw⁻ 22 (q24 c4) ∷
   rw⁻ 21 (q25 c4) ∷
   rw⁻ 20 (q24 c4) ∷
   rw⁻ 19 (q25 c4) ∷
   rw⁻ 18 (q24 c4) ∷
   rw 28 (q7 c4) ∷
   rw⁻ 27 (q26 c4) ∷
   rw⁻ 26 (q26 c4) ∷
   rw⁻ 25 (q24 c4) ∷
   rw⁻ 24 (q25 c4) ∷
   rw⁻ 23 (q24 c4) ∷
   rw⁻ 22 (q25 c4) ∷
   rw⁻ 21 (q24 c4) ∷
   rw⁻ 32 (q11 c4) ∷
   rw⁻ 31 (q27 c4) ∷
   rw⁻ 30 (q27 c4) ∷
   rw⁻ 29 (q27 c4) ∷
   rw⁻ 28 (q28 c4) ∷
   rw⁻ 27 (q29 c4) ∷
   rw⁻ 26 (q28 c4) ∷
   rw⁻ 25 (q29 c4) ∷
   rw⁻ 24 (q28 c4) ∷
   rw 36 (q7 c4) ∷
   rw⁻ 35 (q30 c4) ∷
   rw⁻ 34 (q26 c4) ∷
   rw⁻ 33 (q26 c4) ∷
   rw⁻ 32 (q26 c4) ∷
   rw⁻ 31 (q24 c4) ∷
   rw⁻ 30 (q25 c4) ∷
   rw⁻ 29 (q24 c4) ∷
   rw⁻ 28 (q25 c4) ∷
   rw⁻ 27 (q24 c4) ∷ []) Eq.refl
