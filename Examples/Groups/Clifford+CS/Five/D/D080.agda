{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD080 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D080 (Sᴰ : SD080) where

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
  lem-F4-I-I : Ws → St 1183
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K2 : Ws → St 1207
  lem-F4-I-K2 = pickᴰ 1 Sᴰ
  lem-F4-I-K3 : Ws → St 1208
  lem-F4-I-K3 = pickᴰ 2 Sᴰ
  lem-F4-K2-I : Ws → St 1573
  lem-F4-K2-I = pickᴰ 3 Sᴰ
  lem-F4-K2-K1 : Ws → St 1574
  lem-F4-K2-K1 = pickᴰ 4 Sᴰ
  lem-F4-K2-K2 : Ws → St 1352
  lem-F4-K2-K2 = pickᴰ 5 Sᴰ
  lem-F4-K2-K3 : Ws → St 1575
  lem-F4-K2-K3 = pickᴰ 6 Sᴰ
  lem-F4-CS2-I : Ws → St 1363
  lem-F4-CS2-I = pickᴰ 7 Sᴰ
  lem-F4-I-CS1 : Ws → St 1229
  lem-F4-I-CS1 = pickᴰ 8 Sᴰ
  lem-F4-I-CS2 : Ws → St 1230
  lem-F4-I-CS2 = pickᴰ 9 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1365
  lem-F4-K2-CS2 = pickᴰ 10 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1367
  lem-F4-CS2-K2 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1368
  lem-F4-CS2-CS2 = pickᴰ 12 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1579
  lem-F4-CS2-K1 = pickᴰ 13 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1402
  lem-F4-CS2-K3 = pickᴰ 14 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 15 Sᴰ
  lem-F4-K2-CS1 : Ws → St 1582
  lem-F4-K2-CS1 = pickᴰ 16 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1584
  lem-F4-CS2-CS1 = pickᴰ 17 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1573 (lem-F4-K2-I c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1352 (lem-F4-K2-K2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1582 (lem-F4-K2-CS1 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1365 (lem-F4-K2-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1574 (lem-F4-K2-K1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1377 (lem-F5-23 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1367 (lem-F4-CS2-K2 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1363 (lem-F4-CS2-I c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1402 (lem-F4-CS2-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1368 (lem-F4-CS2-CS2 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1584 (lem-F4-CS2-CS1 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1579 (lem-F4-CS2-K1 c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 1409 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1575 (lem-F4-K2-K3 c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 1411 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1207 (lem-F4-I-K2 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1230 (lem-F4-I-CS2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1183 (lem-F4-I-I c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1208 (lem-F4-I-K3 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1229 (lem-F4-I-CS1 c4)

-- ckt-TST part4: 139 steps
lem-ckt-TST-part4 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-part4 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ Sb0-1-42-3 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 114 (q1 c4) ∷
   rw⁻ 113 (q2 c4) ∷
   rw⁻ 112 (q3 c4) ∷
   rw⁻ 111 (q3 c4) ∷
   rw⁻ 110 (q2 c4) ∷
   rw⁻ 109 (q4 c4) ∷
   rw⁻ 108 (q5 c4) ∷
   rw⁻ 148 (q6 c4) ∷
   rw⁻ 147 (q7 c4) ∷
   rw⁻ 146 (q8 c4) ∷
   rw⁻ 145 (q9 c4) ∷
   rw⁻ 144 (q10 c4) ∷
   rw⁻ 143 (q10 c4) ∷
   rw⁻ 142 (q9 c4) ∷
   rw⁻ 141 (q11 c4) ∷
   rw⁻ 140 (q8 c4) ∷
   rw⁻ 139 (q9 c4) ∷
   rw⁻ 138 (q10 c4) ∷
   rw⁻ 137 (q10 c4) ∷
   rw⁻ 136 (q9 c4) ∷
   rw⁻ 135 (q8 c4) ∷
   rw⁻ 134 (q7 c4) ∷
   rw⁻ 133 (q10 c4) ∷
   rw⁻ 132 (q10 c4) ∷
   rw⁻ 131 (q7 c4) ∷
   rw⁻ 130 (q8 c4) ∷
   rw⁻ 129 (q9 c4) ∷
   rw⁻ 128 (q10 c4) ∷
   rw⁻ 127 (q10 c4) ∷
   rw⁻ 126 (q9 c4) ∷
   rw⁻ 125 (q8 c4) ∷
   rw⁻ 124 (q7 c4) ∷
   rw⁻ 123 (q11 c4) ∷
   rw⁻ 122 (q11 c4) ∷
   rw⁻ 121 (q7 c4) ∷
   rw⁻ 120 (q10 c4) ∷
   rw⁻ 119 (q10 c4) ∷
   rw⁻ 118 (q10 c4) ∷
   rw⁻ 117 (q8 c4) ∷
   rw⁻ 116 (q7 c4) ∷
   rw⁻ 115 (q11 c4) ∷
   rw⁻ 114 (q11 c4) ∷
   rw⁻ 113 (q7 c4) ∷
   rw⁻ 112 (q10 c4) ∷
   rw⁻ 111 (q12 c4) ∷
   rw⁻ 152 (q6 c4) ∷
   rw⁻ 151 (q10 c4) ∷
   rw⁻ 150 (q7 c4) ∷
   rw⁻ 149 (q8 c4) ∷
   rw⁻ 148 (q9 c4) ∷
   rw⁻ 147 (q10 c4) ∷
   rw⁻ 146 (q10 c4) ∷
   rw⁻ 145 (q9 c4) ∷
   rw⁻ 144 (q11 c4) ∷
   rw⁻ 143 (q8 c4) ∷
   rw⁻ 142 (q9 c4) ∷
   rw⁻ 141 (q10 c4) ∷
   rw⁻ 140 (q10 c4) ∷
   rw⁻ 139 (q9 c4) ∷
   rw⁻ 138 (q8 c4) ∷
   rw⁻ 137 (q7 c4) ∷
   rw⁻ 136 (q10 c4) ∷
   rw⁻ 135 (q10 c4) ∷
   rw⁻ 134 (q7 c4) ∷
   rw⁻ 133 (q8 c4) ∷
   rw⁻ 132 (q9 c4) ∷
   rw⁻ 131 (q10 c4) ∷
   rw⁻ 130 (q10 c4) ∷
   rw⁻ 129 (q9 c4) ∷
   rw⁻ 128 (q8 c4) ∷
   rw⁻ 127 (q7 c4) ∷
   rw⁻ 126 (q11 c4) ∷
   rw⁻ 125 (q11 c4) ∷
   rw⁻ 124 (q7 c4) ∷
   rw⁻ 123 (q10 c4) ∷
   rw⁻ 122 (q10 c4) ∷
   rw⁻ 121 (q10 c4) ∷
   rw⁻ 120 (q8 c4) ∷
   rw⁻ 119 (q7 c4) ∷
   rw⁻ 118 (q11 c4) ∷
   rw⁻ 117 (q11 c4) ∷
   rw⁻ 116 (q7 c4) ∷
   rw⁻ 115 (q10 c4) ∷
   rw⁻ 114 (q12 c4) ∷
   rw 156 (q13 c4) ∷
   rw⁻ 155 (q4 c4) ∷
   rw⁻ 154 (q4 c4) ∷
   rw⁻ 153 (q2 c4) ∷
   rw⁻ 152 (q1 c4) ∷
   rw⁻ 151 (q14 c4) ∷
   rw⁻ 150 (q4 c4) ∷
   rw⁻ 149 (q4 c4) ∷
   rw⁻ 148 (q14 c4) ∷
   rw⁻ 147 (q3 c4) ∷
   rw⁻ 146 (q1 c4) ∷
   rw⁻ 145 (q14 c4) ∷
   rw⁻ 144 (q4 c4) ∷
   rw⁻ 143 (q4 c4) ∷
   rw⁻ 142 (q14 c4) ∷
   rw⁻ 141 (q1 c4) ∷
   rw⁻ 140 (q2 c4) ∷
   rw⁻ 139 (q4 c4) ∷
   rw⁻ 138 (q4 c4) ∷
   rw⁻ 137 (q2 c4) ∷
   rw⁻ 136 (q1 c4) ∷
   rw⁻ 135 (q14 c4) ∷
   rw⁻ 134 (q4 c4) ∷
   rw⁻ 133 (q4 c4) ∷
   rw⁻ 132 (q14 c4) ∷
   rw⁻ 131 (q1 c4) ∷
   rw⁻ 130 (q2 c4) ∷
   rw⁻ 129 (q3 c4) ∷
   rw⁻ 128 (q3 c4) ∷
   rw⁻ 127 (q2 c4) ∷
   rw⁻ 126 (q4 c4) ∷
   rw⁻ 125 (q4 c4) ∷
   rw⁻ 124 (q4 c4) ∷
   rw⁻ 123 (q1 c4) ∷
   rw⁻ 122 (q2 c4) ∷
   rw⁻ 121 (q3 c4) ∷
   rw⁻ 120 (q3 c4) ∷
   rw⁻ 119 (q2 c4) ∷
   rw⁻ 118 (q4 c4) ∷
   rw⁻ 117 (q5 c4) ∷
   rw⁻ 160 (q15 c4) ∷
   rw⁻ 159 (q16 c4) ∷
   rw⁻ 158 (q17 c4) ∷
   rw⁻ 157 (q17 c4) ∷
   rw⁻ 156 (q16 c4) ∷
   rw⁻ 155 (q18 c4) ∷
   rw⁻ 154 (q19 c4) ∷
   rw⁻ 153 (q17 c4) ∷
   rw⁻ 152 (q17 c4) ∷
   rw⁻ 151 (q19 c4) ∷
   rw⁻ 150 (q20 c4) ∷
   rw⁻ 149 (q18 c4) ∷
   rw⁻ 148 (q19 c4) ∷
   rw⁻ 147 (q17 c4) ∷
   rw⁻ 146 (q17 c4) ∷ []) Eq.refl
