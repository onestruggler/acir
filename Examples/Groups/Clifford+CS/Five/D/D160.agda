{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD160 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D160 (Sᴰ : SD160) where

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
  lem-F4-K2-I : Ws → St 1573
  lem-F4-K2-I = pickᴰ 0 Sᴰ
  lem-F4-K2-K1 : Ws → St 1574
  lem-F4-K2-K1 = pickᴰ 1 Sᴰ
  lem-F4-K2-K2 : Ws → St 1352
  lem-F4-K2-K2 = pickᴰ 2 Sᴰ
  lem-F4-K2-K3 : Ws → St 1575
  lem-F4-K2-K3 = pickᴰ 3 Sᴰ
  lem-F4-CS2-I : Ws → St 1363
  lem-F4-CS2-I = pickᴰ 4 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1365
  lem-F4-K2-CS2 = pickᴰ 5 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1367
  lem-F4-CS2-K2 = pickᴰ 6 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1368
  lem-F4-CS2-CS2 = pickᴰ 7 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1579
  lem-F4-CS2-K1 = pickᴰ 8 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1402
  lem-F4-CS2-K3 = pickᴰ 9 Sᴰ
  lem-F4-K2-CS1 : Ws → St 1582
  lem-F4-K2-CS1 = pickᴰ 10 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1584
  lem-F4-CS2-CS1 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS0 : Ws → St 1721
  lem-F4-CS2-CS0 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1575 (lem-F4-K2-K3 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1573 (lem-F4-K2-I c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1352 (lem-F4-K2-K2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1365 (lem-F4-K2-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1582 (lem-F4-K2-CS1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1574 (lem-F4-K2-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1721 (lem-F4-CS2-CS0 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1363 (lem-F4-CS2-I c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1579 (lem-F4-CS2-K1 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1402 (lem-F4-CS2-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1368 (lem-F4-CS2-CS2 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1367 (lem-F4-CS2-K2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1584 (lem-F4-CS2-CS1 c4)

-- ckt-TST part34: 77 steps
lem-ckt-TST-part34 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) ⟫ʷ
lem-ckt-TST-part34 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ []) (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ S4 ∷ Sb2-0-41-3 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK41 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK41 ∷ S4 ∷ [])
  (rw⁻ 229 (q1 c4) ∷
   rw⁻ 228 (q2 c4) ∷
   rw⁻ 227 (q3 c4) ∷
   rw⁻ 226 (q4 c4) ∷
   rw⁻ 225 (q4 c4) ∷
   rw⁻ 224 (q3 c4) ∷
   rw⁻ 223 (q2 c4) ∷
   rw⁻ 222 (q1 c4) ∷
   rw⁻ 221 (q4 c4) ∷
   rw⁻ 220 (q4 c4) ∷
   rw⁻ 219 (q1 c4) ∷
   rw⁻ 218 (q2 c4) ∷
   rw⁻ 217 (q3 c4) ∷
   rw⁻ 216 (q5 c4) ∷
   rw⁻ 215 (q5 c4) ∷
   rw⁻ 214 (q3 c4) ∷
   rw⁻ 213 (q4 c4) ∷
   rw⁻ 212 (q4 c4) ∷
   rw⁻ 211 (q4 c4) ∷
   rw⁻ 210 (q2 c4) ∷
   rw⁻ 209 (q3 c4) ∷
   rw⁻ 208 (q5 c4) ∷
   rw⁻ 207 (q5 c4) ∷
   rw⁻ 206 (q3 c4) ∷
   rw⁻ 205 (q4 c4) ∷
   rw⁻ 204 (q6 c4) ∷
   rw⁻ 255 (q7 c4) ∷
   rw⁻ 254 (q8 c4) ∷
   rw⁻ 253 (q9 c4) ∷
   rw⁻ 252 (q8 c4) ∷
   rw⁻ 251 (q10 c4) ∷
   rw⁻ 250 (q11 c4) ∷
   rw⁻ 249 (q11 c4) ∷
   rw⁻ 248 (q10 c4) ∷
   rw⁻ 247 (q8 c4) ∷
   rw⁻ 246 (q12 c4) ∷
   rw⁻ 245 (q11 c4) ∷
   rw⁻ 244 (q11 c4) ∷
   rw⁻ 243 (q12 c4) ∷
   rw⁻ 242 (q8 c4) ∷
   rw⁻ 241 (q10 c4) ∷
   rw⁻ 240 (q11 c4) ∷
   rw⁻ 239 (q11 c4) ∷
   rw⁻ 238 (q10 c4) ∷
   rw⁻ 237 (q13 c4) ∷
   rw⁻ 236 (q8 c4) ∷
   rw⁻ 235 (q10 c4) ∷
   rw⁻ 234 (q11 c4) ∷
   rw⁻ 233 (q11 c4) ∷
   rw⁻ 232 (q10 c4) ∷
   rw⁻ 231 (q8 c4) ∷
   rw⁻ 230 (q12 c4) ∷
   rw⁻ 229 (q11 c4) ∷
   rw⁻ 228 (q11 c4) ∷
   rw⁻ 227 (q12 c4) ∷
   rw⁻ 226 (q8 c4) ∷
   rw⁻ 225 (q10 c4) ∷
   rw⁻ 224 (q11 c4) ∷
   rw⁻ 223 (q11 c4) ∷
   rw⁻ 222 (q10 c4) ∷
   rw⁻ 221 (q8 c4) ∷
   rw⁻ 220 (q12 c4) ∷
   rw⁻ 219 (q13 c4) ∷
   rw⁻ 218 (q13 c4) ∷
   rw⁻ 217 (q12 c4) ∷
   rw⁻ 216 (q11 c4) ∷
   rw⁻ 215 (q11 c4) ∷
   rw⁻ 214 (q11 c4) ∷
   rw⁻ 213 (q8 c4) ∷
   rw⁻ 212 (q12 c4) ∷
   rw⁻ 211 (q13 c4) ∷
   rw⁻ 210 (q13 c4) ∷
   rw⁻ 209 (q12 c4) ∷
   rw⁻ 208 (q11 c4) ∷
   rw⁻ 207 (q9 c4) ∷
   rw⁻ 258 (q7 c4) ∷
   rw⁻ 257 (q8 c4) ∷ []) Eq.refl
