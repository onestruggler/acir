{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD081 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D081 (Sᴰ : SD081) where

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
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 4 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 5 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 6 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 7 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 8 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 9 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 10 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 12 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 13 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 15 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 16 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 17 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 18 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1411 (lem-F4-I-K3 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1386 (lem-F4-I-I c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1410 (lem-F4-I-K2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1409 (lem-F4-I-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1419 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1618 (lem-F4-K3-I c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1590 (lem-F5-23 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1576 (lem-F4-CS2-I c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1820 (lem-F4-CS2-CS1 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1815 (lem-F4-CS2-K1 c4)

-- ckt-TST part5: 133 steps
lem-ckt-TST-part5 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-part5 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 145 (q1 c4) ∷
   rw⁻ 144 (q2 c4) ∷
   rw⁻ 143 (q3 c4) ∷
   rw⁻ 142 (q4 c4) ∷
   rw⁻ 141 (q4 c4) ∷
   rw⁻ 140 (q3 c4) ∷
   rw⁻ 139 (q2 c4) ∷
   rw⁻ 138 (q1 c4) ∷
   rw⁻ 137 (q4 c4) ∷
   rw⁻ 136 (q4 c4) ∷
   rw⁻ 135 (q1 c4) ∷
   rw⁻ 134 (q2 c4) ∷
   rw⁻ 133 (q3 c4) ∷
   rw⁻ 132 (q5 c4) ∷
   rw⁻ 131 (q5 c4) ∷
   rw⁻ 130 (q3 c4) ∷
   rw⁻ 129 (q4 c4) ∷
   rw⁻ 128 (q4 c4) ∷
   rw⁻ 127 (q4 c4) ∷
   rw⁻ 126 (q2 c4) ∷
   rw⁻ 125 (q3 c4) ∷
   rw⁻ 124 (q5 c4) ∷
   rw⁻ 123 (q5 c4) ∷
   rw⁻ 122 (q3 c4) ∷
   rw⁻ 121 (q4 c4) ∷
   rw⁻ 120 (q6 c4) ∷
   rw 164 (q7 c4) ∷
   rw⁻ 163 (q8 c4) ∷
   rw⁻ 162 (q9 c4) ∷
   rw⁻ 161 (q10 c4) ∷
   rw⁻ 160 (q10 c4) ∷
   rw⁻ 159 (q9 c4) ∷
   rw⁻ 158 (q8 c4) ∷
   rw⁻ 157 (q11 c4) ∷
   rw⁻ 156 (q10 c4) ∷
   rw⁻ 155 (q10 c4) ∷
   rw⁻ 154 (q11 c4) ∷
   rw⁻ 153 (q12 c4) ∷
   rw⁻ 152 (q8 c4) ∷
   rw⁻ 151 (q11 c4) ∷
   rw⁻ 150 (q10 c4) ∷
   rw⁻ 149 (q10 c4) ∷
   rw⁻ 148 (q11 c4) ∷
   rw⁻ 147 (q8 c4) ∷
   rw⁻ 146 (q9 c4) ∷
   rw⁻ 145 (q10 c4) ∷
   rw⁻ 144 (q10 c4) ∷
   rw⁻ 143 (q9 c4) ∷
   rw⁻ 142 (q8 c4) ∷
   rw⁻ 141 (q11 c4) ∷
   rw⁻ 140 (q10 c4) ∷
   rw⁻ 139 (q10 c4) ∷
   rw⁻ 138 (q11 c4) ∷
   rw⁻ 137 (q8 c4) ∷
   rw⁻ 136 (q9 c4) ∷
   rw⁻ 135 (q12 c4) ∷
   rw⁻ 134 (q12 c4) ∷
   rw⁻ 133 (q9 c4) ∷
   rw⁻ 132 (q10 c4) ∷
   rw⁻ 131 (q10 c4) ∷
   rw⁻ 130 (q10 c4) ∷
   rw⁻ 129 (q8 c4) ∷
   rw⁻ 128 (q9 c4) ∷
   rw⁻ 127 (q12 c4) ∷
   rw⁻ 126 (q12 c4) ∷
   rw⁻ 125 (q9 c4) ∷
   rw⁻ 124 (q10 c4) ∷
   rw⁻ 123 (q13 c4) ∷
   rw⁻ 168 (q14 c4) ∷
   rw⁻ 167 (q15 c4) ∷
   rw⁻ 166 (q16 c4) ∷
   rw⁻ 165 (q17 c4) ∷
   rw⁻ 164 (q18 c4) ∷
   rw⁻ 163 (q18 c4) ∷
   rw⁻ 162 (q17 c4) ∷
   rw⁻ 161 (q16 c4) ∷
   rw⁻ 160 (q15 c4) ∷
   rw⁻ 159 (q18 c4) ∷
   rw⁻ 158 (q18 c4) ∷
   rw⁻ 157 (q15 c4) ∷
   rw⁻ 156 (q19 c4) ∷
   rw⁻ 155 (q16 c4) ∷
   rw⁻ 154 (q15 c4) ∷
   rw⁻ 153 (q18 c4) ∷
   rw⁻ 152 (q18 c4) ∷
   rw⁻ 151 (q15 c4) ∷
   rw⁻ 150 (q16 c4) ∷
   rw⁻ 149 (q17 c4) ∷
   rw⁻ 148 (q18 c4) ∷
   rw⁻ 147 (q18 c4) ∷
   rw⁻ 146 (q17 c4) ∷
   rw⁻ 145 (q16 c4) ∷
   rw⁻ 144 (q15 c4) ∷
   rw⁻ 143 (q18 c4) ∷
   rw⁻ 142 (q18 c4) ∷
   rw⁻ 141 (q15 c4) ∷
   rw⁻ 140 (q16 c4) ∷
   rw⁻ 139 (q17 c4) ∷
   rw⁻ 138 (q19 c4) ∷
   rw⁻ 137 (q19 c4) ∷
   rw⁻ 136 (q17 c4) ∷
   rw⁻ 135 (q18 c4) ∷
   rw⁻ 134 (q18 c4) ∷
   rw⁻ 133 (q18 c4) ∷
   rw⁻ 132 (q16 c4) ∷
   rw⁻ 131 (q17 c4) ∷
   rw⁻ 130 (q19 c4) ∷
   rw⁻ 129 (q19 c4) ∷
   rw⁻ 128 (q17 c4) ∷
   rw⁻ 127 (q18 c4) ∷
   rw⁻ 126 (q20 c4) ∷
   rw⁻ 172 (q14 c4) ∷
   rw⁻ 171 (q18 c4) ∷
   rw⁻ 170 (q15 c4) ∷
   rw⁻ 169 (q16 c4) ∷
   rw⁻ 168 (q17 c4) ∷
   rw⁻ 167 (q18 c4) ∷
   rw⁻ 166 (q18 c4) ∷
   rw⁻ 165 (q17 c4) ∷
   rw⁻ 164 (q16 c4) ∷
   rw⁻ 163 (q15 c4) ∷
   rw⁻ 162 (q18 c4) ∷
   rw⁻ 161 (q18 c4) ∷
   rw⁻ 160 (q15 c4) ∷
   rw⁻ 159 (q19 c4) ∷
   rw⁻ 158 (q16 c4) ∷
   rw⁻ 157 (q15 c4) ∷
   rw⁻ 156 (q18 c4) ∷
   rw⁻ 155 (q18 c4) ∷
   rw⁻ 154 (q15 c4) ∷
   rw⁻ 153 (q16 c4) ∷
   rw⁻ 152 (q17 c4) ∷
   rw⁻ 151 (q18 c4) ∷ []) Eq.refl
