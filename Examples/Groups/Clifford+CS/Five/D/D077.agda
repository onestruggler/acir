{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD077 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D077 (Sᴰ : SD077) where

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
  lem-F4-I-K1 : Ws → St 1206
  lem-F4-I-K1 = pickᴰ 1 Sᴰ
  lem-F4-I-K2 : Ws → St 1207
  lem-F4-I-K2 = pickᴰ 2 Sᴰ
  lem-F4-I-K3 : Ws → St 1208
  lem-F4-I-K3 = pickᴰ 3 Sᴰ
  lem-F4-K2-I : Ws → St 1573
  lem-F4-K2-I = pickᴰ 4 Sᴰ
  lem-F4-K2-K1 : Ws → St 1574
  lem-F4-K2-K1 = pickᴰ 5 Sᴰ
  lem-F4-K2-K2 : Ws → St 1352
  lem-F4-K2-K2 = pickᴰ 6 Sᴰ
  lem-F4-K2-K3 : Ws → St 1575
  lem-F4-K2-K3 = pickᴰ 7 Sᴰ
  lem-F4-K3-I : Ws → St 1405
  lem-F4-K3-I = pickᴰ 8 Sᴰ
  lem-F4-K3-K1 : Ws → St 1426
  lem-F4-K3-K1 = pickᴰ 9 Sᴰ
  lem-F4-K3-K2 : Ws → St 1427
  lem-F4-K3-K2 = pickᴰ 10 Sᴰ
  lem-F4-K3-K3 : Ws → St 1383
  lem-F4-K3-K3 = pickᴰ 11 Sᴰ
  lem-F4-CS2-I : Ws → St 1363
  lem-F4-CS2-I = pickᴰ 12 Sᴰ
  lem-F4-I-CS1 : Ws → St 1229
  lem-F4-I-CS1 = pickᴰ 13 Sᴰ
  lem-F4-I-CS2 : Ws → St 1230
  lem-F4-I-CS2 = pickᴰ 14 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1365
  lem-F4-K2-CS2 = pickᴰ 15 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1367
  lem-F4-CS2-K2 = pickᴰ 16 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1368
  lem-F4-CS2-CS2 = pickᴰ 17 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1579
  lem-F4-CS2-K1 = pickᴰ 18 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1402
  lem-F4-CS2-K3 = pickᴰ 19 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1430
  lem-F4-K3-CS1 = pickᴰ 20 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1403
  lem-F4-K3-CS2 = pickᴰ 21 Sᴰ
  lem-F5-23 : Ws → St 1377
  lem-F5-23 = pickᴰ 22 Sᴰ
  lem-F4-K2-CS1 : Ws → St 1582
  lem-F4-K2-CS1 = pickᴰ 23 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1584
  lem-F4-CS2-CS1 = pickᴰ 24 Sᴰ

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
  q21 : Ws → Eqn
  q21 c4 = sE 1206 (lem-F4-I-K1 c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 1419 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1405 (lem-F4-K3-I c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1427 (lem-F4-K3-K2 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1403 (lem-F4-K3-CS2 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1383 (lem-F4-K3-K3 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1430 (lem-F4-K3-CS1 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1426 (lem-F4-K3-K1 c4)

-- ckt-TST part1: 175 steps
lem-ckt-TST-part1 : Ws → ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ ≈ ⟪ (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) ⟫ʷ
lem-ckt-TST-part1 c4 = derive (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ CK42 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ []) (X4 ∷ CK41 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK42 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK41 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ S4 ∷ CK42 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ S4 ∷ CK43 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ Sb2-0-41-3 ∷ K1 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ CS23 ∷ CS23 ∷ CS23 ∷ K2 ∷ CS12 ∷ CS12 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ CS12 ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K2 ∷ CS23 ∷ CS23 ∷ K2 ∷ ι ∷ K3 ∷ CS23 ∷ CS23 ∷ K3 ∷ ι ∷ K1 ∷ ι ∷ [])
  (rw⁻ 74 (q1 c4) ∷
   rw⁻ 73 (q2 c4) ∷
   rw⁻ 72 (q3 c4) ∷
   rw⁻ 71 (q3 c4) ∷
   rw⁻ 70 (q2 c4) ∷
   rw⁻ 69 (q4 c4) ∷
   rw⁻ 68 (q4 c4) ∷
   rw⁻ 67 (q4 c4) ∷
   rw⁻ 66 (q1 c4) ∷
   rw⁻ 65 (q2 c4) ∷
   rw⁻ 64 (q3 c4) ∷
   rw⁻ 63 (q3 c4) ∷
   rw⁻ 62 (q2 c4) ∷
   rw⁻ 61 (q4 c4) ∷
   rw⁻ 60 (q5 c4) ∷
   rw⁻ 84 (q6 c4) ∷
   rw⁻ 83 (q7 c4) ∷
   rw⁻ 82 (q8 c4) ∷
   rw⁻ 81 (q9 c4) ∷
   rw⁻ 80 (q10 c4) ∷
   rw⁻ 79 (q10 c4) ∷
   rw⁻ 78 (q9 c4) ∷
   rw⁻ 77 (q8 c4) ∷
   rw⁻ 76 (q7 c4) ∷
   rw⁻ 75 (q11 c4) ∷
   rw⁻ 74 (q11 c4) ∷
   rw⁻ 73 (q7 c4) ∷
   rw⁻ 72 (q10 c4) ∷
   rw⁻ 71 (q10 c4) ∷
   rw⁻ 70 (q10 c4) ∷
   rw⁻ 69 (q8 c4) ∷
   rw⁻ 68 (q7 c4) ∷
   rw⁻ 67 (q11 c4) ∷
   rw⁻ 66 (q11 c4) ∷
   rw⁻ 65 (q7 c4) ∷
   rw⁻ 64 (q10 c4) ∷
   rw⁻ 63 (q12 c4) ∷
   rw⁻ 88 (q6 c4) ∷
   rw⁻ 87 (q10 c4) ∷
   rw⁻ 86 (q7 c4) ∷
   rw⁻ 85 (q8 c4) ∷
   rw⁻ 84 (q9 c4) ∷
   rw⁻ 83 (q10 c4) ∷
   rw⁻ 82 (q10 c4) ∷
   rw⁻ 81 (q9 c4) ∷
   rw⁻ 80 (q8 c4) ∷
   rw⁻ 79 (q7 c4) ∷
   rw⁻ 78 (q11 c4) ∷
   rw⁻ 77 (q11 c4) ∷
   rw⁻ 76 (q7 c4) ∷
   rw⁻ 75 (q10 c4) ∷
   rw⁻ 74 (q10 c4) ∷
   rw⁻ 73 (q10 c4) ∷
   rw⁻ 72 (q8 c4) ∷
   rw⁻ 71 (q7 c4) ∷
   rw⁻ 70 (q11 c4) ∷
   rw⁻ 69 (q11 c4) ∷
   rw⁻ 68 (q7 c4) ∷
   rw⁻ 67 (q10 c4) ∷
   rw⁻ 66 (q12 c4) ∷
   rw 92 (q13 c4) ∷
   rw⁻ 91 (q4 c4) ∷
   rw⁻ 90 (q4 c4) ∷
   rw⁻ 89 (q2 c4) ∷
   rw⁻ 88 (q1 c4) ∷
   rw⁻ 87 (q14 c4) ∷
   rw⁻ 86 (q4 c4) ∷
   rw⁻ 85 (q4 c4) ∷
   rw⁻ 84 (q14 c4) ∷
   rw⁻ 83 (q1 c4) ∷
   rw⁻ 82 (q2 c4) ∷
   rw⁻ 81 (q3 c4) ∷
   rw⁻ 80 (q3 c4) ∷
   rw⁻ 79 (q2 c4) ∷
   rw⁻ 78 (q4 c4) ∷
   rw⁻ 77 (q4 c4) ∷
   rw⁻ 76 (q4 c4) ∷
   rw⁻ 75 (q1 c4) ∷
   rw⁻ 74 (q2 c4) ∷
   rw⁻ 73 (q3 c4) ∷
   rw⁻ 72 (q3 c4) ∷
   rw⁻ 71 (q2 c4) ∷
   rw⁻ 70 (q4 c4) ∷
   rw⁻ 69 (q5 c4) ∷
   rw⁻ 96 (q15 c4) ∷
   rw⁻ 95 (q16 c4) ∷
   rw⁻ 94 (q17 c4) ∷
   rw⁻ 93 (q17 c4) ∷
   rw⁻ 92 (q16 c4) ∷
   rw⁻ 91 (q18 c4) ∷
   rw⁻ 90 (q19 c4) ∷
   rw⁻ 89 (q17 c4) ∷
   rw⁻ 88 (q17 c4) ∷
   rw⁻ 87 (q19 c4) ∷
   rw⁻ 86 (q18 c4) ∷
   rw⁻ 85 (q16 c4) ∷
   rw⁻ 84 (q20 c4) ∷
   rw⁻ 83 (q20 c4) ∷
   rw⁻ 82 (q16 c4) ∷
   rw⁻ 81 (q17 c4) ∷
   rw⁻ 80 (q17 c4) ∷
   rw⁻ 79 (q17 c4) ∷
   rw⁻ 78 (q18 c4) ∷
   rw⁻ 77 (q16 c4) ∷
   rw⁻ 76 (q20 c4) ∷
   rw⁻ 75 (q20 c4) ∷
   rw⁻ 74 (q16 c4) ∷
   rw⁻ 73 (q17 c4) ∷
   rw⁻ 72 (q21 c4) ∷
   rw 100 (q22 c4) ∷
   rw⁻ 99 (q23 c4) ∷
   rw⁻ 98 (q24 c4) ∷
   rw⁻ 97 (q25 c4) ∷
   rw⁻ 96 (q25 c4) ∷
   rw⁻ 95 (q24 c4) ∷
   rw⁻ 94 (q23 c4) ∷
   rw⁻ 93 (q26 c4) ∷
   rw⁻ 92 (q25 c4) ∷
   rw⁻ 91 (q25 c4) ∷
   rw⁻ 90 (q26 c4) ∷
   rw⁻ 89 (q23 c4) ∷
   rw⁻ 88 (q24 c4) ∷
   rw⁻ 87 (q27 c4) ∷
   rw⁻ 86 (q27 c4) ∷
   rw⁻ 85 (q24 c4) ∷
   rw⁻ 84 (q25 c4) ∷
   rw⁻ 83 (q25 c4) ∷
   rw⁻ 82 (q25 c4) ∷
   rw⁻ 81 (q23 c4) ∷
   rw⁻ 80 (q24 c4) ∷
   rw⁻ 79 (q27 c4) ∷
   rw⁻ 78 (q27 c4) ∷
   rw⁻ 77 (q24 c4) ∷
   rw⁻ 76 (q25 c4) ∷
   rw⁻ 75 (q28 c4) ∷
   rw⁻ 104 (q6 c4) ∷
   rw⁻ 103 (q9 c4) ∷
   rw⁻ 102 (q8 c4) ∷
   rw⁻ 101 (q7 c4) ∷
   rw⁻ 100 (q10 c4) ∷
   rw⁻ 99 (q10 c4) ∷
   rw⁻ 98 (q7 c4) ∷
   rw⁻ 97 (q8 c4) ∷
   rw⁻ 96 (q9 c4) ∷
   rw⁻ 95 (q10 c4) ∷
   rw⁻ 94 (q10 c4) ∷
   rw⁻ 93 (q9 c4) ∷
   rw⁻ 92 (q8 c4) ∷
   rw⁻ 91 (q7 c4) ∷
   rw⁻ 90 (q11 c4) ∷
   rw⁻ 89 (q11 c4) ∷
   rw⁻ 88 (q7 c4) ∷
   rw⁻ 87 (q10 c4) ∷
   rw⁻ 86 (q10 c4) ∷
   rw⁻ 85 (q10 c4) ∷
   rw⁻ 84 (q8 c4) ∷
   rw⁻ 83 (q7 c4) ∷
   rw⁻ 82 (q11 c4) ∷
   rw⁻ 81 (q11 c4) ∷
   rw⁻ 80 (q7 c4) ∷
   rw⁻ 79 (q10 c4) ∷
   rw⁻ 78 (q12 c4) ∷
   rw⁻ 108 (q6 c4) ∷
   rw⁻ 107 (q10 c4) ∷
   rw⁻ 106 (q9 c4) ∷
   rw⁻ 105 (q8 c4) ∷
   rw⁻ 104 (q7 c4) ∷
   rw⁻ 103 (q10 c4) ∷
   rw⁻ 102 (q10 c4) ∷
   rw⁻ 101 (q7 c4) ∷
   rw⁻ 100 (q8 c4) ∷
   rw⁻ 99 (q9 c4) ∷
   rw⁻ 98 (q10 c4) ∷
   rw⁻ 97 (q10 c4) ∷
   rw⁻ 96 (q9 c4) ∷ []) Eq.refl
