{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD066 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D066 (Sᴰ : SD066) where

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
  lem-comm-CS03-CCZ124 : Ws → St 957
  lem-comm-CS03-CCZ124 = pickᴰ 0 Sᴰ
  lem-comm-CSd03-CCZ124 : Ws → St 959
  lem-comm-CSd03-CCZ124 = pickᴰ 1 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 2 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 3 Sᴰ
  lem-comm-CS02-CCZ134 : Ws → St 431
  lem-comm-CS02-CCZ134 = pickᴰ 4 Sᴰ
  lem-comm-CSd02-CCZ134 : Ws → St 432
  lem-comm-CSd02-CCZ134 = pickᴰ 5 Sᴰ
  lem-comm-CX21-TOFF403 : Ws → St 1696
  lem-comm-CX21-TOFF403 = pickᴰ 6 Sᴰ
  lem-comm-CX31-TOFF402 : Ws → St 1697
  lem-comm-CX31-TOFF402 = pickᴰ 7 Sᴰ
  lem-F4-I-I-at0440 : Ws → St 1683
  lem-F4-I-I-at0440 = pickᴰ 8 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1684
  lem-F4-I-K1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1685
  lem-F4-I-K2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-I-K3-at0440 : Ws → St 1686
  lem-F4-I-K3-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K1-I-at0440 : Ws → St 1687
  lem-F4-K1-I-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K1-K1-at0440 : Ws → St 1688
  lem-F4-K1-K1-at0440 = pickᴰ 13 Sᴰ
  lem-F4-K1-K2-at0440 : Ws → St 1689
  lem-F4-K1-K2-at0440 = pickᴰ 14 Sᴰ
  lem-F4-K1-K3-at0440 : Ws → St 1690
  lem-F4-K1-K3-at0440 = pickᴰ 15 Sᴰ
  lem-box-tQ-at022330 : Ws → St 307
  lem-box-tQ-at022330 = pickᴰ 16 Sᴰ
  lem-box-tQ-at0330 : Ws → St 252
  lem-box-tQ-at0330 = pickᴰ 17 Sᴰ
  lem-box-cP-at0214203143 : Ws → St 1112
  lem-box-cP-at0214203143 = pickᴰ 18 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 19 Sᴰ
  lem-F4-K1-CS1-at0440 : Ws → St 1692
  lem-F4-K1-CS1-at0440 = pickᴰ 20 Sᴰ
  lem-box-cP-at04122140 : Ws → St 1698
  lem-box-cP-at04122140 = pickᴰ 21 Sᴰ
  lem-box-cP-at0413213240 : Ws → St 1195
  lem-box-cP-at0413213240 = pickᴰ 22 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 23 Sᴰ
  lem-Ku-box-at0214203143 : Ws → St 1436
  lem-Ku-box-at0214203143 = pickᴰ 24 Sᴰ
  lem-F4-I-CS0-at0440 : Ws → St 1699
  lem-F4-I-CS0-at0440 = pickᴰ 25 Sᴰ
  lem-F4-K1-CS2-at0440 : Ws → St 1694
  lem-F4-K1-CS2-at0440 = pickᴰ 26 Sᴰ
  lem-CKu-box-2-at0214203143 : Ws → St 1700
  lem-CKu-box-2-at0214203143 = pickᴰ 27 Sᴰ
  lem-box-perm-2341-at02142140 : Ws → St 1701
  lem-box-perm-2341-at02142140 = pickᴰ 28 Sᴰ
  lem-box-perm-2341-at0314213240 : Ws → St 1702
  lem-box-perm-2341-at0314213240 = pickᴰ 29 Sᴰ
  lem-box-perm-4123-at022330 : Ws → St 1703
  lem-box-perm-4123-at022330 = pickᴰ 30 Sᴰ
  lem-box-perm-4123-at0330 : Ws → St 1704
  lem-box-perm-4123-at0330 = pickᴰ 31 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1694 (lem-F4-K1-CS2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1690 (lem-F4-K1-K3-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1687 (lem-F4-K1-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1689 (lem-F4-K1-K2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1692 (lem-F4-K1-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1688 (lem-F4-K1-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1699 (lem-F4-I-CS0-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1423 (lit c4)

-- ckt-TST @0440 part68: 78 steps
lem-ckt-TST-at0440-part68 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part68 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ X0 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) (X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ [])
  (rw⁻ 298 (q1 c4) ∷
   rw⁻ 297 (q2 c4) ∷
   rw⁻ 296 (q3 c4) ∷
   rw⁻ 295 (q4 c4) ∷
   rw⁻ 294 (q5 c4) ∷
   rw⁻ 293 (q5 c4) ∷
   rw⁻ 292 (q4 c4) ∷
   rw⁻ 291 (q1 c4) ∷
   rw⁻ 290 (q1 c4) ∷
   rw⁻ 289 (q1 c4) ∷
   rw⁻ 288 (q3 c4) ∷
   rw⁻ 287 (q4 c4) ∷
   rw⁻ 286 (q5 c4) ∷
   rw⁻ 285 (q5 c4) ∷
   rw⁻ 284 (q4 c4) ∷
   rw⁻ 283 (q1 c4) ∷
   rw⁻ 282 (q6 c4) ∷
   rw⁻ 333 (q7 c4) ∷
   rw⁻ 332 (q8 c4) ∷
   rw⁻ 331 (q9 c4) ∷
   rw⁻ 330 (q8 c4) ∷
   rw⁻ 329 (q10 c4) ∷
   rw⁻ 328 (q11 c4) ∷
   rw⁻ 327 (q11 c4) ∷
   rw⁻ 326 (q10 c4) ∷
   rw⁻ 325 (q8 c4) ∷
   rw⁻ 324 (q12 c4) ∷
   rw⁻ 323 (q11 c4) ∷
   rw⁻ 322 (q11 c4) ∷
   rw⁻ 321 (q12 c4) ∷
   rw⁻ 320 (q8 c4) ∷
   rw⁻ 319 (q10 c4) ∷
   rw⁻ 318 (q11 c4) ∷
   rw⁻ 317 (q11 c4) ∷
   rw⁻ 316 (q10 c4) ∷
   rw⁻ 315 (q13 c4) ∷
   rw⁻ 314 (q8 c4) ∷
   rw⁻ 313 (q10 c4) ∷
   rw⁻ 312 (q11 c4) ∷
   rw⁻ 311 (q11 c4) ∷
   rw⁻ 310 (q10 c4) ∷
   rw⁻ 309 (q8 c4) ∷
   rw⁻ 308 (q12 c4) ∷
   rw⁻ 307 (q11 c4) ∷
   rw⁻ 306 (q11 c4) ∷
   rw⁻ 305 (q12 c4) ∷
   rw⁻ 304 (q8 c4) ∷
   rw⁻ 303 (q10 c4) ∷
   rw⁻ 302 (q11 c4) ∷
   rw⁻ 301 (q11 c4) ∷
   rw⁻ 300 (q10 c4) ∷
   rw⁻ 299 (q8 c4) ∷
   rw⁻ 298 (q12 c4) ∷
   rw⁻ 297 (q13 c4) ∷
   rw⁻ 296 (q13 c4) ∷
   rw⁻ 295 (q12 c4) ∷
   rw⁻ 294 (q11 c4) ∷
   rw⁻ 293 (q11 c4) ∷
   rw⁻ 292 (q11 c4) ∷
   rw⁻ 291 (q8 c4) ∷
   rw⁻ 290 (q12 c4) ∷
   rw⁻ 289 (q13 c4) ∷
   rw⁻ 288 (q13 c4) ∷
   rw⁻ 287 (q12 c4) ∷
   rw⁻ 286 (q11 c4) ∷
   rw⁻ 285 (q9 c4) ∷
   rw 2 (q14 c4) ∷
   rw 3 (q14 c4) ∷
   rw 4 (q14 c4) ∷
   rw 5 (q14 c4) ∷
   rw 6 (q14 c4) ∷
   rw 7 (q14 c4) ∷
   rw 8 (q14 c4) ∷
   rw 9 (q14 c4) ∷
   rw 10 (q14 c4) ∷
   rw 11 (q14 c4) ∷
   rw 12 (q14 c4) ∷
   rw 13 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = sE 1701 (lem-box-perm-2341-at02142140 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 307 (lem-box-tQ-at022330 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1698 (lem-box-cP-at04122140 c4)
  q18 : Ws → Eqn
  q18 c4 = wpE 827 c4
  q19 : Ws → Eqn
  q19 c4 = wpE 1402 c4
  q20 : Ws → Eqn
  q20 c4 = wlE 307 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wpE 515 c4
  q22 : Ws → Eqn
  q22 c4 = wlE 260 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 959 (lem-comm-CSd03-CCZ124 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 957 (lem-comm-CS03-CCZ124 c4)
  q25 : Ws → Eqn
  q25 c4 = wpE 1479 c4
  q26 : Ws → Eqn
  q26 c4 = wlE 1350 (lit c4)
  q27 : Ws → Eqn
  q27 c4 = wpE 1480 c4
  q28 : Ws → Eqn
  q28 c4 = wlE 952 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wpE 1449 c4
  q30 : Ws → Eqn
  q30 c4 = wpE 1404 c4
  q31 : Ws → Eqn
  q31 c4 = sE 1696 (lem-comm-CX21-TOFF403 c4)
  q32 : Ws → Eqn
  q32 c4 = wpE 1481 c4
  q33 : Ws → Eqn
  q33 c4 = wpE 1482 c4
  q34 : Ws → Eqn
  q34 c4 = wpE 1445 c4
  q35 : Ws → Eqn
  q35 c4 = wlE 289 (lit c4)
  q36 : Ws → Eqn
  q36 c4 = wpE 919 c4
  q37 : Ws → Eqn
  q37 c4 = wlE 280 (lit c4)
  q38 : Ws → Eqn
  q38 c4 = wlE 1222 (lit c4)
  q39 : Ws → Eqn
  q39 c4 = wlE 1717 (lit c4)
  q40 : Ws → Eqn
  q40 c4 = wpE 1483 c4
  q41 : Ws → Eqn
  q41 c4 = wpE 39 c4
  q42 : Ws → Eqn
  q42 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q43 : Ws → Eqn
  q43 c4 = wpE 32 c4
  q44 : Ws → Eqn
  q44 c4 = wpE 21 c4
  q45 : Ws → Eqn
  q45 c4 = wlE 186 (lit c4)
  q46 : Ws → Eqn
  q46 c4 = wlE 230 (lit c4)
  q47 : Ws → Eqn
  q47 c4 = sE 1703 (lem-box-perm-4123-at022330 c4)

-- box-box-1 @02142140: 105 steps
lem-box-box-1-at02142140 : Ws → ⟪ (Bx2-4130 ∷ Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ Bx2-4130 ∷ []) ⟫ʷ
lem-box-box-1-at02142140 c4 = derive (Bx2-4130 ∷ Bx4-2130 ∷ []) (Bx4-2130 ∷ Bx2-4130 ∷ [])
  (rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷
   rw 4 (q17 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q19 c4) ∷
   rw 6 (q20 c4) ∷
   rw⁻ 10 (q21 c4) ∷
   rw⁻ 9 (q22 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 7 (q20 c4) ∷
   rw 5 (q18 c4) ∷
   rw 6 (q25 c4) ∷
   rw⁻ 3 (q17 c4) ∷
   rw 3 (q17 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 4 (q27 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 8 (q30 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q32 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw 4 (q28 c4) ∷
   rw 6 (q35 c4) ∷
   rw⁻ 10 (q36 c4) ∷
   rw⁻ 9 (q37 c4) ∷
   rw 8 (q23 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 6 (q24 c4) ∷
   rw⁻ 7 (q35 c4) ∷
   rw⁻ 5 (q38 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   rw 5 (q39 c4) ∷
   rw 6 (q40 c4) ∷
   rw⁻ 5 (q28 c4) ∷
   rw 11 (q29 c4) ∷
   rw 10 (q30 c4) ∷
   rw 9 (q31 c4) ∷
   rw 8 (q32 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q33 c4) ∷
   rw 5 (q34 c4) ∷
   rw 6 (q28 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw 2 (q17 c4) ∷
   rw 1 (q18 c4) ∷
   rw 2 (q19 c4) ∷
   rw 4 (q20 c4) ∷
   rw⁻ 8 (q21 c4) ∷
   rw⁻ 7 (q22 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 5 (q22 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 5 (q20 c4) ∷
   rw 3 (q18 c4) ∷
   rw 4 (q25 c4) ∷
   rw⁻ 1 (q17 c4) ∷
   rw 1 (q17 c4) ∷
   rw⁻ 0 (q26 c4) ∷
   rw 2 (q27 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw 7 (q29 c4) ∷
   rw 6 (q30 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q32 c4) ∷
   rw 3 (q31 c4) ∷
   rw 2 (q33 c4) ∷
   rw 1 (q34 c4) ∷
   rw 2 (q28 c4) ∷
   rw 4 (q35 c4) ∷
   rw⁻ 8 (q36 c4) ∷
   rw⁻ 7 (q37 c4) ∷
   rw 6 (q23 c4) ∷
   rw⁻ 5 (q37 c4) ∷
   rw 4 (q24 c4) ∷
   rw⁻ 5 (q35 c4) ∷
   rw⁻ 3 (q38 c4) ∷
   rw⁻ 2 (q26 c4) ∷
   rw 3 (q39 c4) ∷
   rw 4 (q40 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw 9 (q29 c4) ∷
   rw 8 (q30 c4) ∷
   rw 7 (q31 c4) ∷
   rw 6 (q32 c4) ∷
   rw 5 (q31 c4) ∷
   rw 4 (q33 c4) ∷
   rw 3 (q34 c4) ∷
   rw 4 (q28 c4) ∷
   rw⁻ 0 (q17 c4) ∷
   rw 2 (q35 c4) ∷
   rw⁻ 6 (q41 c4) ∷
   rw 5 (q42 c4) ∷
   rw⁻ 4 (q43 c4) ∷
   rw 3 (q42 c4) ∷
   rw⁻ 2 (q44 c4) ∷
   rw⁻ 3 (q35 c4) ∷
   rw 3 (q45 c4) ∷
   rw 4 (q46 c4) ∷
   rw⁻ 1 (q16 c4) ∷
   rw 1 (q47 c4) ∷ []) Eq.refl

private
  q48 : Ws → Eqn
  q48 c4 = wlE 1487 (lit c4)
  q49 : Ws → Eqn
  q49 c4 = wpE 1491 c4
  q50 : Ws → Eqn
  q50 c4 = wlE 1724 (lit c4)
  q51 : Ws → Eqn
  q51 c4 = wpE 1492 c4
  q52 : Ws → Eqn
  q52 c4 = sE 1436 (lem-Ku-box-at0214203143 c4)
  q53 : Ws → Eqn
  q53 c4 = sE 1700 (lem-CKu-box-2-at0214203143 c4)
  q54 : Ws → Eqn
  q54 c4 = sE 1112 (lem-box-cP-at0214203143 c4)
  q55 : Ws → Eqn
  q55 c4 = wlE 1725 (lit c4)
  q56 : Ws → Eqn
  q56 c4 = wpE 1493 c4
  q57 : Ws → Eqn
  q57 c4 = wlE 1490 (lit c4)

-- F4-CS0-K2 @0440: 20 steps
lem-F4-CS0-K2-at0440 : Ws → ⟪ (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ []) ⟫ʷ ≈ ⟪ (CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS0-K2-at0440 c4 = derive (X0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ []) (CK02 ∷ X0 ∷ Sb2-4-01-3 ∷ X0 ∷ [])
  (rw⁻ 2 (q48 c4) ∷
   re 1 1 (Bx2-4013 ∷ Toff301 ∷ Sb2-4-3-1 ∷ Toff301 ∷ Sb⁻2-4-3-1 ∷ []) ∷
   re 3 1 (CS34 ∷ []) ∷
   re 5 1 (CS34⁻ ∷ []) ∷
   rw 5 (q49 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 3 (q51 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   rw⁻ 2 (q53 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw 5 (q56 c4) ∷
   rw⁻ 4 (q55 c4) ∷
   rw 3 (q56 c4) ∷
   rw⁻ 4 (q54 c4) ∷
   re 6 1 (Sb2-4-3-1 ∷ []) ∷
   re 8 1 (Sb⁻2-4-3-1 ∷ []) ∷
   re 4 5 (Sb2-4-01-3 ∷ []) ∷
   rw⁻ 0 (q57 c4) ∷ []) Eq.refl

private
  q58 : Ws → Eqn
  q58 c4 = sE 1702 (lem-box-perm-2341-at0314213240 c4)
  q59 : Ws → Eqn
  q59 c4 = sE 252 (lem-box-tQ-at0330 c4)
  q60 : Ws → Eqn
  q60 c4 = sE 1195 (lem-box-cP-at0413213240 c4)
  q61 : Ws → Eqn
  q61 c4 = wpE 103 c4
  q62 : Ws → Eqn
  q62 c4 = wpE 1506 c4
  q63 : Ws → Eqn
  q63 c4 = wlE 343 (lit c4)
  q64 : Ws → Eqn
  q64 c4 = wpE 706 c4
  q65 : Ws → Eqn
  q65 c4 = wlE 1021 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = sE 432 (lem-comm-CSd02-CCZ134 c4)
  q67 : Ws → Eqn
  q67 c4 = sE 431 (lem-comm-CS02-CCZ134 c4)
  q68 : Ws → Eqn
  q68 c4 = wpE 1507 c4
  q69 : Ws → Eqn
  q69 c4 = wlE 1368 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wpE 1385 c4
  q71 : Ws → Eqn
  q71 c4 = wlE 869 (lit c4)
  q72 : Ws → Eqn
  q72 c4 = wpE 1508 c4
  q73 : Ws → Eqn
  q73 c4 = wpE 1509 c4
  q74 : Ws → Eqn
  q74 c4 = sE 1697 (lem-comm-CX31-TOFF402 c4)
  q75 : Ws → Eqn
  q75 c4 = wpE 1510 c4
  q76 : Ws → Eqn
  q76 c4 = wpE 1316 c4
  q77 : Ws → Eqn
  q77 c4 = wpE 1511 c4
  q78 : Ws → Eqn
  q78 c4 = wlE 155 (lit c4)
  q79 : Ws → Eqn
  q79 c4 = wpE 261 c4
  q80 : Ws → Eqn
  q80 c4 = wlE 679 (lit c4)
  q81 : Ws → Eqn
  q81 c4 = wlE 1730 (lit c4)
  q82 : Ws → Eqn
  q82 c4 = wpE 1512 c4
  q83 : Ws → Eqn
  q83 c4 = wpE 1 c4
  q84 : Ws → Eqn
  q84 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q85 : Ws → Eqn
  q85 c4 = wpE 2 c4
  q86 : Ws → Eqn
  q86 c4 = wpE 3 c4
  q87 : Ws → Eqn
  q87 c4 = wlE 503 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = wlE 341 (lit c4)
  q89 : Ws → Eqn
  q89 c4 = sE 1704 (lem-box-perm-4123-at0330 c4)

-- box-box-1 @0314213240: 105 steps
lem-box-box-1-at0314213240 : Ws → ⟪ (Bx3-4120 ∷ Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ Bx3-4120 ∷ []) ⟫ʷ
lem-box-box-1-at0314213240 c4 = derive (Bx3-4120 ∷ Bx4-3120 ∷ []) (Bx4-3120 ∷ Bx3-4120 ∷ [])
  (rw 0 (q58 c4) ∷
   rw 0 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw 3 (q61 c4) ∷
   rw 4 (q62 c4) ∷
   rw 6 (q63 c4) ∷
   rw⁻ 10 (q64 c4) ∷
   rw⁻ 9 (q65 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 7 (q65 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 7 (q63 c4) ∷
   rw 5 (q61 c4) ∷
   rw 6 (q68 c4) ∷
   rw⁻ 3 (q60 c4) ∷
   rw 3 (q60 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw 4 (q70 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 9 (q72 c4) ∷
   rw 8 (q73 c4) ∷
   rw 7 (q74 c4) ∷
   rw 6 (q75 c4) ∷
   rw 5 (q74 c4) ∷
   rw 4 (q76 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q71 c4) ∷
   rw 6 (q78 c4) ∷
   rw⁻ 10 (q79 c4) ∷
   rw⁻ 9 (q80 c4) ∷
   rw 8 (q66 c4) ∷
   rw⁻ 7 (q80 c4) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw 5 (q38 c4) ∷
   rw⁻ 4 (q69 c4) ∷
   rw 5 (q81 c4) ∷
   rw 6 (q82 c4) ∷
   rw⁻ 5 (q71 c4) ∷
   rw 11 (q72 c4) ∷
   rw 10 (q73 c4) ∷
   rw 9 (q74 c4) ∷
   rw 8 (q75 c4) ∷
   rw 7 (q74 c4) ∷
   rw 6 (q76 c4) ∷
   rw 5 (q77 c4) ∷
   rw 6 (q71 c4) ∷
   rw⁻ 2 (q60 c4) ∷
   rw 2 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 2 (q62 c4) ∷
   rw 4 (q63 c4) ∷
   rw⁻ 8 (q64 c4) ∷
   rw⁻ 7 (q65 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 5 (q65 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 5 (q63 c4) ∷
   rw 3 (q61 c4) ∷
   rw 4 (q68 c4) ∷
   rw⁻ 1 (q60 c4) ∷
   rw 1 (q60 c4) ∷
   rw⁻ 0 (q69 c4) ∷
   rw 2 (q70 c4) ∷
   rw⁻ 1 (q71 c4) ∷
   rw 7 (q72 c4) ∷
   rw 6 (q73 c4) ∷
   rw 5 (q74 c4) ∷
   rw 4 (q75 c4) ∷
   rw 3 (q74 c4) ∷
   rw 2 (q76 c4) ∷
   rw 1 (q77 c4) ∷
   rw 2 (q71 c4) ∷
   rw 4 (q78 c4) ∷
   rw⁻ 8 (q79 c4) ∷
   rw⁻ 7 (q80 c4) ∷
   rw 6 (q66 c4) ∷
   rw⁻ 5 (q80 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw 3 (q38 c4) ∷
   rw⁻ 2 (q69 c4) ∷
   rw 3 (q81 c4) ∷
   rw 4 (q82 c4) ∷
   rw⁻ 3 (q71 c4) ∷
   rw 9 (q72 c4) ∷
   rw 8 (q73 c4) ∷
   rw 7 (q74 c4) ∷
   rw 6 (q75 c4) ∷
   rw 5 (q74 c4) ∷
   rw 4 (q76 c4) ∷
   rw 3 (q77 c4) ∷
   rw 4 (q71 c4) ∷
   rw⁻ 0 (q60 c4) ∷
   rw 2 (q78 c4) ∷
   rw⁻ 6 (q83 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 4 (q85 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   rw 3 (q87 c4) ∷
   rw 4 (q88 c4) ∷
   rw⁻ 1 (q59 c4) ∷
   rw 1 (q89 c4) ∷ []) Eq.refl
