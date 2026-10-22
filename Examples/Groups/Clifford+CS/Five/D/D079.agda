{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD079 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D079 (Sᴰ : SD079) where

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
  lem-F4-K2-I : Ws → St 1809
  lem-F4-K2-I = pickᴰ 4 Sᴰ
  lem-F4-K2-K2 : Ws → St 1565
  lem-F4-K2-K2 = pickᴰ 5 Sᴰ
  lem-F4-K2-K3 : Ws → St 1811
  lem-F4-K2-K3 = pickᴰ 6 Sᴰ
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 7 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 8 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 9 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 10 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 11 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 12 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 13 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1578
  lem-F4-K2-CS2 = pickᴰ 14 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 15 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 16 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 17 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 18 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 19 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 20 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 21 Sᴰ
  lem-F4-K2-CS1 : Ws → St 1818
  lem-F4-K2-CS1 = pickᴰ 22 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 23 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1820 (lem-F4-CS2-CS1 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1576 (lem-F4-CS2-I c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1590 (lem-F5-23 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 1419 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1618 (lem-F4-K3-I c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 1411 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1411 (lem-F4-I-K3 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1386 (lem-F4-I-I c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1410 (lem-F4-I-K2 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1409 (lem-F4-I-K1 c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 1409 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1809 (lem-F4-K2-I c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1811 (lem-F4-K2-K3 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1578 (lem-F4-K2-CS2 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1818 (lem-F4-K2-CS1 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1565 (lem-F4-K2-K2 c4)

-- ckt-TST part3: 147 steps
lem-ckt-TST-part3 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-part3 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 107 (q1 c4) ∷
   rw⁻ 106 (q2 c4) ∷
   rw⁻ 105 (q3 c4) ∷
   rw⁻ 104 (q3 c4) ∷
   rw⁻ 103 (q3 c4) ∷
   rw⁻ 102 (q4 c4) ∷
   rw⁻ 101 (q2 c4) ∷
   rw⁻ 100 (q1 c4) ∷
   rw⁻ 99 (q1 c4) ∷
   rw⁻ 98 (q2 c4) ∷
   rw⁻ 97 (q3 c4) ∷
   rw⁻ 96 (q5 c4) ∷
   rw⁻ 132 (q6 c4) ∷
   rw⁻ 131 (q3 c4) ∷
   rw⁻ 130 (q7 c4) ∷
   rw⁻ 129 (q1 c4) ∷
   rw⁻ 128 (q4 c4) ∷
   rw⁻ 127 (q7 c4) ∷
   rw⁻ 126 (q3 c4) ∷
   rw⁻ 125 (q3 c4) ∷
   rw⁻ 124 (q7 c4) ∷
   rw⁻ 123 (q4 c4) ∷
   rw⁻ 122 (q2 c4) ∷
   rw⁻ 121 (q3 c4) ∷
   rw⁻ 120 (q3 c4) ∷
   rw⁻ 119 (q2 c4) ∷
   rw⁻ 118 (q4 c4) ∷
   rw⁻ 117 (q7 c4) ∷
   rw⁻ 116 (q3 c4) ∷
   rw⁻ 115 (q3 c4) ∷
   rw⁻ 114 (q7 c4) ∷
   rw⁻ 113 (q4 c4) ∷
   rw⁻ 112 (q2 c4) ∷
   rw⁻ 111 (q1 c4) ∷
   rw⁻ 110 (q1 c4) ∷
   rw⁻ 109 (q2 c4) ∷
   rw⁻ 108 (q3 c4) ∷
   rw⁻ 107 (q3 c4) ∷
   rw⁻ 106 (q3 c4) ∷
   rw⁻ 105 (q4 c4) ∷
   rw⁻ 104 (q2 c4) ∷
   rw⁻ 103 (q1 c4) ∷
   rw⁻ 102 (q1 c4) ∷
   rw⁻ 101 (q2 c4) ∷
   rw⁻ 100 (q3 c4) ∷
   rw⁻ 99 (q5 c4) ∷
   rw 136 (q8 c4) ∷
   rw⁻ 135 (q9 c4) ∷
   rw⁻ 134 (q9 c4) ∷
   rw⁻ 133 (q10 c4) ∷
   rw⁻ 132 (q11 c4) ∷
   rw⁻ 131 (q12 c4) ∷
   rw⁻ 130 (q10 c4) ∷
   rw⁻ 129 (q9 c4) ∷
   rw⁻ 128 (q9 c4) ∷
   rw⁻ 127 (q10 c4) ∷
   rw⁻ 126 (q12 c4) ∷
   rw⁻ 125 (q13 c4) ∷
   rw⁻ 124 (q9 c4) ∷
   rw⁻ 123 (q9 c4) ∷
   rw⁻ 122 (q13 c4) ∷
   rw⁻ 121 (q12 c4) ∷
   rw⁻ 120 (q10 c4) ∷
   rw⁻ 119 (q9 c4) ∷
   rw⁻ 118 (q9 c4) ∷
   rw⁻ 117 (q10 c4) ∷
   rw⁻ 116 (q12 c4) ∷
   rw⁻ 115 (q13 c4) ∷
   rw⁻ 114 (q11 c4) ∷
   rw⁻ 113 (q11 c4) ∷
   rw⁻ 112 (q13 c4) ∷
   rw⁻ 111 (q9 c4) ∷
   rw⁻ 110 (q9 c4) ∷
   rw⁻ 109 (q9 c4) ∷
   rw⁻ 108 (q12 c4) ∷
   rw⁻ 107 (q13 c4) ∷
   rw⁻ 106 (q11 c4) ∷
   rw⁻ 105 (q11 c4) ∷
   rw⁻ 104 (q13 c4) ∷
   rw⁻ 103 (q9 c4) ∷
   rw⁻ 102 (q14 c4) ∷
   rw⁻ 140 (q15 c4) ∷
   rw⁻ 139 (q16 c4) ∷
   rw⁻ 138 (q17 c4) ∷
   rw⁻ 137 (q17 c4) ∷
   rw⁻ 136 (q16 c4) ∷
   rw⁻ 135 (q18 c4) ∷
   rw⁻ 134 (q19 c4) ∷
   rw⁻ 133 (q16 c4) ∷
   rw⁻ 132 (q17 c4) ∷
   rw⁻ 131 (q17 c4) ∷
   rw⁻ 130 (q16 c4) ∷
   rw⁻ 129 (q19 c4) ∷
   rw⁻ 128 (q20 c4) ∷
   rw⁻ 127 (q17 c4) ∷
   rw⁻ 126 (q17 c4) ∷
   rw⁻ 125 (q20 c4) ∷
   rw⁻ 124 (q19 c4) ∷
   rw⁻ 123 (q16 c4) ∷
   rw⁻ 122 (q17 c4) ∷
   rw⁻ 121 (q17 c4) ∷
   rw⁻ 120 (q16 c4) ∷
   rw⁻ 119 (q19 c4) ∷
   rw⁻ 118 (q20 c4) ∷
   rw⁻ 117 (q18 c4) ∷
   rw⁻ 116 (q18 c4) ∷
   rw⁻ 115 (q20 c4) ∷
   rw⁻ 114 (q17 c4) ∷
   rw⁻ 113 (q17 c4) ∷
   rw⁻ 112 (q17 c4) ∷
   rw⁻ 111 (q19 c4) ∷
   rw⁻ 110 (q20 c4) ∷
   rw⁻ 109 (q18 c4) ∷
   rw⁻ 108 (q18 c4) ∷
   rw⁻ 107 (q20 c4) ∷
   rw⁻ 106 (q17 c4) ∷
   rw⁻ 105 (q21 c4) ∷
   rw 144 (q22 c4) ∷
   rw⁻ 143 (q23 c4) ∷
   rw⁻ 142 (q24 c4) ∷
   rw⁻ 141 (q25 c4) ∷
   rw⁻ 140 (q25 c4) ∷
   rw⁻ 139 (q24 c4) ∷
   rw⁻ 138 (q26 c4) ∷
   rw⁻ 137 (q23 c4) ∷
   rw⁻ 136 (q24 c4) ∷
   rw⁻ 135 (q25 c4) ∷
   rw⁻ 134 (q25 c4) ∷
   rw⁻ 133 (q24 c4) ∷
   rw⁻ 132 (q23 c4) ∷
   rw⁻ 131 (q27 c4) ∷
   rw⁻ 130 (q25 c4) ∷
   rw⁻ 129 (q25 c4) ∷
   rw⁻ 128 (q27 c4) ∷
   rw⁻ 127 (q23 c4) ∷
   rw⁻ 126 (q24 c4) ∷
   rw⁻ 125 (q25 c4) ∷
   rw⁻ 124 (q25 c4) ∷
   rw⁻ 123 (q24 c4) ∷
   rw⁻ 122 (q23 c4) ∷
   rw⁻ 121 (q27 c4) ∷
   rw⁻ 120 (q26 c4) ∷
   rw⁻ 119 (q26 c4) ∷
   rw⁻ 118 (q27 c4) ∷
   rw⁻ 117 (q25 c4) ∷
   rw⁻ 116 (q25 c4) ∷
   rw⁻ 115 (q25 c4) ∷ []) Eq.refl
