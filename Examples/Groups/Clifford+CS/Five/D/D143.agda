{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD143 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D143 (Sᴰ : SD143) where

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
  lem-F4-I-I-at0440 : Ws → St 1452
  lem-F4-I-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1453
  lem-F4-I-K1-at0440 = pickᴰ 1 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1454
  lem-F4-I-K2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-I-K3-at0440 : Ws → St 1455
  lem-F4-I-K3-at0440 = pickᴰ 3 Sᴰ
  lem-F4-K3-I-at0440 : Ws → St 1617
  lem-F4-K3-I-at0440 = pickᴰ 4 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1618
  lem-F4-K3-K1-at0440 = pickᴰ 5 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1619
  lem-F4-K3-K2-at0440 = pickᴰ 6 Sᴰ
  lem-F4-K3-K3-at0440 : Ws → St 1624
  lem-F4-K3-K3-at0440 = pickᴰ 7 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1460
  lem-F4-I-CS1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1462
  lem-F4-I-CS2-at0440 = pickᴰ 9 Sᴰ
  lem-F4-K3-CS1-at0440 : Ws → St 1620
  lem-F4-K3-CS1-at0440 = pickᴰ 10 Sᴰ
  lem-F4-I-CS0-at0440 : Ws → St 1466
  lem-F4-I-CS0-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1622
  lem-F4-K3-CS2-at0440 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1624 (lem-F4-K3-K3-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1622 (lem-F4-K3-CS2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1617 (lem-F4-K3-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1619 (lem-F4-K3-K2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1620 (lem-F4-K3-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1618 (lem-F4-K3-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1466 (lem-F4-I-CS0-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1452 (lem-F4-I-I-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1453 (lem-F4-I-K1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1455 (lem-F4-I-K3-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1462 (lem-F4-I-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1454 (lem-F4-I-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1460 (lem-F4-I-CS1-at0440 c4)

-- ckt-TST @0440 part60: 77 steps
lem-ckt-TST-at0440-part60 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) ⟫ʷ
lem-ckt-TST-at0440-part60 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ X0 ∷ CK03 ∷ X0 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ []) (X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ X0 ∷ S0 ∷ X0 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ Sb2-4-01-3 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK02 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ Sb4-2-03-1 ∷ X0 ∷ X0 ∷ CK03 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ X0 ∷ CK01 ∷ X0 ∷ X0 ∷ S0 ∷ X0 ∷ CK01 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ Sb4-1-02-3 ∷ Sb4-1-02-3 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ Sb4-1-02-3 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK02 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK02 ∷ S0 ∷ CK03 ∷ Sb4-2-03-1 ∷ Sb4-2-03-1 ∷ CK03 ∷ S0 ∷ CK01 ∷ S0 ∷ [])
  (rw⁻ 290 (q1 c4) ∷
   rw⁻ 289 (q2 c4) ∷
   rw⁻ 288 (q2 c4) ∷
   rw⁻ 287 (q1 c4) ∷
   rw⁻ 286 (q3 c4) ∷
   rw⁻ 285 (q4 c4) ∷
   rw⁻ 284 (q2 c4) ∷
   rw⁻ 283 (q2 c4) ∷
   rw⁻ 282 (q4 c4) ∷
   rw⁻ 281 (q3 c4) ∷
   rw⁻ 280 (q1 c4) ∷
   rw⁻ 279 (q2 c4) ∷
   rw⁻ 278 (q2 c4) ∷
   rw⁻ 277 (q1 c4) ∷
   rw⁻ 276 (q5 c4) ∷
   rw⁻ 275 (q3 c4) ∷
   rw⁻ 274 (q1 c4) ∷
   rw⁻ 273 (q2 c4) ∷
   rw⁻ 272 (q2 c4) ∷
   rw⁻ 271 (q1 c4) ∷
   rw⁻ 270 (q3 c4) ∷
   rw⁻ 269 (q4 c4) ∷
   rw⁻ 268 (q2 c4) ∷
   rw⁻ 267 (q2 c4) ∷
   rw⁻ 266 (q4 c4) ∷
   rw⁻ 265 (q3 c4) ∷
   rw⁻ 264 (q1 c4) ∷
   rw⁻ 263 (q2 c4) ∷
   rw⁻ 262 (q2 c4) ∷
   rw⁻ 261 (q1 c4) ∷
   rw⁻ 260 (q3 c4) ∷
   rw⁻ 259 (q4 c4) ∷
   rw⁻ 258 (q5 c4) ∷
   rw⁻ 257 (q5 c4) ∷
   rw⁻ 256 (q4 c4) ∷
   rw⁻ 255 (q2 c4) ∷
   rw⁻ 254 (q2 c4) ∷
   rw⁻ 253 (q2 c4) ∷
   rw⁻ 252 (q3 c4) ∷
   rw⁻ 251 (q4 c4) ∷
   rw⁻ 250 (q5 c4) ∷
   rw⁻ 249 (q5 c4) ∷
   rw⁻ 248 (q4 c4) ∷
   rw⁻ 247 (q2 c4) ∷
   rw⁻ 246 (q6 c4) ∷
   rw⁻ 297 (q7 c4) ∷
   rw⁻ 296 (q8 c4) ∷
   rw⁻ 295 (q9 c4) ∷
   rw⁻ 294 (q8 c4) ∷
   rw⁻ 293 (q10 c4) ∷
   rw⁻ 292 (q11 c4) ∷
   rw⁻ 291 (q11 c4) ∷
   rw⁻ 290 (q10 c4) ∷
   rw⁻ 289 (q8 c4) ∷
   rw⁻ 288 (q12 c4) ∷
   rw⁻ 287 (q11 c4) ∷
   rw⁻ 286 (q11 c4) ∷
   rw⁻ 285 (q12 c4) ∷
   rw⁻ 284 (q8 c4) ∷
   rw⁻ 283 (q10 c4) ∷
   rw⁻ 282 (q11 c4) ∷
   rw⁻ 281 (q11 c4) ∷
   rw⁻ 280 (q10 c4) ∷
   rw⁻ 279 (q13 c4) ∷
   rw⁻ 278 (q8 c4) ∷
   rw⁻ 277 (q10 c4) ∷
   rw⁻ 276 (q11 c4) ∷
   rw⁻ 275 (q11 c4) ∷
   rw⁻ 274 (q10 c4) ∷
   rw⁻ 273 (q8 c4) ∷
   rw⁻ 272 (q12 c4) ∷
   rw⁻ 271 (q11 c4) ∷
   rw⁻ 270 (q11 c4) ∷
   rw⁻ 269 (q12 c4) ∷
   rw⁻ 268 (q8 c4) ∷
   rw⁻ 267 (q10 c4) ∷
   rw⁻ 266 (q11 c4) ∷ []) Eq.refl
