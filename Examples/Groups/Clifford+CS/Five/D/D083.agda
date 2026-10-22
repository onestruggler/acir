{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD083 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D083 (Sᴰ : SD083) where

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
  lem-F4-I-I : Ws → St 1386
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K1 : Ws → St 1409
  lem-F4-I-K1 = pickᴰ 1 Sᴰ
  lem-F4-I-K2 : Ws → St 1410
  lem-F4-I-K2 = pickᴰ 2 Sᴰ
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 3 Sᴰ
  lem-F4-K1-I : Ws → St 1646
  lem-F4-K1-I = pickᴰ 4 Sᴰ
  lem-F4-K1-K1 : Ws → St 1822
  lem-F4-K1-K1 = pickᴰ 5 Sᴰ
  lem-F4-K1-K2 : Ws → St 1647
  lem-F4-K1-K2 = pickᴰ 6 Sᴰ
  lem-F4-K1-K3 : Ws → St 1648
  lem-F4-K1-K3 = pickᴰ 7 Sᴰ
  lem-F4-K2-K1 : Ws → St 1810
  lem-F4-K2-K1 = pickᴰ 8 Sᴰ
  lem-F4-K2-K2 : Ws → St 1565
  lem-F4-K2-K2 = pickᴰ 9 Sᴰ
  lem-F4-CS1-K1 : Ws → St 1813
  lem-F4-CS1-K1 = pickᴰ 10 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 11 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 12 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 13 Sᴰ
  lem-F4-K1-CS1 : Ws → St 1651
  lem-F4-K1-CS1 = pickᴰ 14 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1578
  lem-F4-K2-CS2 = pickᴰ 15 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 16 Sᴰ
  lem-F4-CS1-CS1 : Ws → St 1814
  lem-F4-CS1-CS1 = pickᴰ 17 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 18 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 19 Sᴰ
  lem-F4-K1-CS2 : Ws → St 1652
  lem-F4-K1-CS2 = pickᴰ 20 Sᴰ
  lem-F5-12 : Ws → St 1816
  lem-F5-12 = pickᴰ 21 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 22 Sᴰ
  lem-F4-CS1-K2 : Ws → St 1817
  lem-F4-CS1-K2 = pickᴰ 23 Sᴰ
  lem-F4-K2-CS1 : Ws → St 1818
  lem-F4-K2-CS1 = pickᴰ 24 Sᴰ
  lem-F4-CS1-CS2 : Ws → St 1819
  lem-F4-CS1-CS2 = pickᴰ 25 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 26 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1648 (lem-F4-K1-K3 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1651 (lem-F4-K1-CS1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1646 (lem-F4-K1-I c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1652 (lem-F4-K1-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1647 (lem-F4-K1-K2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1822 (lem-F4-K1-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1411 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1409 (lem-F4-I-K1 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1386 (lem-F4-I-I c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1411 (lem-F4-I-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1410 (lem-F4-I-K2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1417 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1590 (lem-F5-23 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 1409 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1578 (lem-F4-K2-CS2 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1810 (lem-F4-K2-K1 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1816 (lem-F5-12 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1817 (lem-F4-CS1-K2 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1819 (lem-F4-CS1-CS2 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1813 (lem-F4-CS1-K1 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1814 (lem-F4-CS1-CS1 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1818 (lem-F4-K2-CS1 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1565 (lem-F4-K2-K2 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1576 (lem-F4-CS2-I c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q29 : Ws → Eqn
  q29 c4 = sE 1820 (lem-F4-CS2-CS1 c4)
  q30 : Ws → Eqn
  q30 c4 = sE 1581 (lem-F4-CS2-CS2 c4)

-- ckt-TST part7: 121 steps
lem-ckt-TST-part7 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-part7 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ X4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 169 (q1 c4) ∷
   rw⁻ 168 (q2 c4) ∷
   rw⁻ 167 (q3 c4) ∷
   rw⁻ 166 (q1 c4) ∷
   rw⁻ 165 (q4 c4) ∷
   rw⁻ 164 (q4 c4) ∷
   rw⁻ 163 (q1 c4) ∷
   rw⁻ 162 (q3 c4) ∷
   rw⁻ 161 (q5 c4) ∷
   rw⁻ 160 (q4 c4) ∷
   rw⁻ 159 (q4 c4) ∷
   rw⁻ 158 (q5 c4) ∷
   rw⁻ 157 (q3 c4) ∷
   rw⁻ 156 (q1 c4) ∷
   rw⁻ 155 (q4 c4) ∷
   rw⁻ 154 (q4 c4) ∷
   rw⁻ 153 (q1 c4) ∷
   rw⁻ 152 (q3 c4) ∷
   rw⁻ 151 (q5 c4) ∷
   rw⁻ 150 (q2 c4) ∷
   rw⁻ 149 (q2 c4) ∷
   rw⁻ 148 (q5 c4) ∷
   rw⁻ 147 (q4 c4) ∷
   rw⁻ 146 (q4 c4) ∷
   rw⁻ 145 (q4 c4) ∷
   rw⁻ 144 (q3 c4) ∷
   rw⁻ 143 (q5 c4) ∷
   rw⁻ 142 (q2 c4) ∷
   rw⁻ 141 (q2 c4) ∷
   rw⁻ 140 (q5 c4) ∷
   rw⁻ 139 (q4 c4) ∷
   rw⁻ 138 (q6 c4) ∷
   rw⁻ 188 (q7 c4) ∷
   rw⁻ 187 (q8 c4) ∷
   rw⁻ 186 (q9 c4) ∷
   rw⁻ 185 (q10 c4) ∷
   rw⁻ 184 (q11 c4) ∷
   rw⁻ 183 (q11 c4) ∷
   rw⁻ 182 (q10 c4) ∷
   rw⁻ 181 (q9 c4) ∷
   rw⁻ 180 (q12 c4) ∷
   rw⁻ 179 (q11 c4) ∷
   rw⁻ 178 (q11 c4) ∷
   rw⁻ 177 (q12 c4) ∷
   rw⁻ 176 (q9 c4) ∷
   rw⁻ 175 (q10 c4) ∷
   rw⁻ 174 (q11 c4) ∷
   rw⁻ 173 (q11 c4) ∷
   rw⁻ 172 (q10 c4) ∷
   rw⁻ 171 (q13 c4) ∷
   rw⁻ 170 (q9 c4) ∷
   rw⁻ 169 (q10 c4) ∷
   rw⁻ 168 (q11 c4) ∷
   rw⁻ 167 (q11 c4) ∷
   rw⁻ 166 (q10 c4) ∷
   rw⁻ 165 (q9 c4) ∷
   rw⁻ 164 (q12 c4) ∷
   rw⁻ 163 (q11 c4) ∷
   rw⁻ 162 (q11 c4) ∷
   rw⁻ 161 (q12 c4) ∷
   rw⁻ 160 (q9 c4) ∷
   rw⁻ 159 (q10 c4) ∷
   rw⁻ 158 (q11 c4) ∷
   rw⁻ 157 (q11 c4) ∷
   rw⁻ 156 (q10 c4) ∷
   rw⁻ 155 (q9 c4) ∷
   rw⁻ 154 (q12 c4) ∷
   rw⁻ 153 (q13 c4) ∷
   rw⁻ 152 (q13 c4) ∷
   rw⁻ 151 (q12 c4) ∷
   rw⁻ 150 (q11 c4) ∷
   rw⁻ 149 (q11 c4) ∷
   rw⁻ 148 (q11 c4) ∷
   rw⁻ 147 (q9 c4) ∷
   rw⁻ 146 (q12 c4) ∷
   rw⁻ 145 (q13 c4) ∷
   rw⁻ 144 (q13 c4) ∷
   rw⁻ 143 (q12 c4) ∷
   rw⁻ 142 (q11 c4) ∷
   rw⁻ 141 (q8 c4) ∷
   rw 193 (q14 c4) ∷
   rw⁻ 197 (q15 c4) ∷
   rw⁻ 196 (q16 c4) ∷
   rw 201 (q17 c4) ∷
   rw⁻ 200 (q18 c4) ∷
   rw⁻ 199 (q19 c4) ∷
   rw⁻ 205 (q20 c4) ∷
   rw⁻ 204 (q21 c4) ∷
   rw⁻ 203 (q22 c4) ∷
   rw⁻ 202 (q23 c4) ∷
   rw⁻ 209 (q20 c4) ∷
   rw⁻ 208 (q24 c4) ∷
   rw⁻ 207 (q21 c4) ∷
   rw⁻ 206 (q22 c4) ∷
   rw⁻ 205 (q23 c4) ∷
   rw 213 (q17 c4) ∷
   rw⁻ 212 (q25 c4) ∷
   rw⁻ 211 (q25 c4) ∷
   rw⁻ 210 (q26 c4) ∷
   rw⁻ 209 (q18 c4) ∷
   rw⁻ 208 (q19 c4) ∷
   rw⁻ 217 (q7 c4) ∷
   rw⁻ 216 (q12 c4) ∷
   rw⁻ 215 (q13 c4) ∷
   rw⁻ 214 (q13 c4) ∷
   rw⁻ 213 (q12 c4) ∷
   rw⁻ 212 (q11 c4) ∷
   rw⁻ 211 (q8 c4) ∷
   rw⁻ 221 (q15 c4) ∷
   rw⁻ 220 (q27 c4) ∷
   rw⁻ 219 (q28 c4) ∷
   rw⁻ 218 (q29 c4) ∷
   rw⁻ 217 (q29 c4) ∷
   rw⁻ 216 (q28 c4) ∷
   rw⁻ 215 (q30 c4) ∷
   rw⁻ 214 (q16 c4) ∷
   rw⁻ 225 (q15 c4) ∷
   rw⁻ 224 (q30 c4) ∷
   rw⁻ 223 (q27 c4) ∷
   rw⁻ 222 (q28 c4) ∷
   rw⁻ 221 (q29 c4) ∷ []) Eq.refl
