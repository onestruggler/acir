{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD057 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D057 (Sᴰ : SD057) where

open import Data.List.Base using (List ; [] ; _∷_)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.Str using (ℓ)

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
  lem-F4-K1-K2 : Ws → St 1647
  lem-F4-K1-K2 = pickᴰ 5 Sᴰ
  lem-F4-K1-K3 : Ws → St 1648
  lem-F4-K1-K3 = pickᴰ 6 Sᴰ
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 7 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 8 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 9 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 10 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 11 Sᴰ
  lem-F4-K1-CS1 : Ws → St 1651
  lem-F4-K1-CS1 = pickᴰ 12 Sᴰ
  lem-F4-K1-CS2 : Ws → St 1652
  lem-F4-K1-CS2 = pickᴰ 13 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1618 (lem-F4-K3-I c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 1411 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1411 (lem-F4-I-K3 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1386 (lem-F4-I-I c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1410 (lem-F4-I-K2 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1409 (lem-F4-I-K1 c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 1417 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1646 (lem-F4-K1-I c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1648 (lem-F4-K1-K3 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1652 (lem-F4-K1-CS2 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1647 (lem-F4-K1-K2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1651 (lem-F4-K1-CS1 c4)

-- ckt-TST part19: 79 steps
lem-ckt-TST-part19 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇並亊並丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊一丒一") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬並亄並亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄一") ⟫ʷ
lem-ckt-TST-part19 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇並亊並丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊一丒一") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬並亄並亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄一")
  (rw⁻ 338 (q1 c4) ∷
   rw⁻ 337 (q2 c4) ∷
   rw⁻ 336 (q2 c4) ∷
   rw⁻ 335 (q1 c4) ∷
   rw⁻ 334 (q3 c4) ∷
   rw⁻ 333 (q3 c4) ∷
   rw⁻ 332 (q3 c4) ∷
   rw⁻ 331 (q4 c4) ∷
   rw⁻ 330 (q1 c4) ∷
   rw⁻ 329 (q2 c4) ∷
   rw⁻ 328 (q2 c4) ∷
   rw⁻ 327 (q1 c4) ∷
   rw⁻ 326 (q3 c4) ∷
   rw⁻ 325 (q5 c4) ∷
   rw⁻ 373 (q6 c4) ∷
   rw⁻ 372 (q7 c4) ∷
   rw⁻ 371 (q8 c4) ∷
   rw⁻ 370 (q8 c4) ∷
   rw⁻ 369 (q7 c4) ∷
   rw⁻ 368 (q9 c4) ∷
   rw⁻ 367 (q10 c4) ∷
   rw⁻ 366 (q8 c4) ∷
   rw⁻ 365 (q8 c4) ∷
   rw⁻ 364 (q10 c4) ∷
   rw⁻ 363 (q9 c4) ∷
   rw⁻ 362 (q7 c4) ∷
   rw⁻ 361 (q8 c4) ∷
   rw⁻ 360 (q8 c4) ∷
   rw⁻ 359 (q7 c4) ∷
   rw⁻ 358 (q11 c4) ∷
   rw⁻ 357 (q9 c4) ∷
   rw⁻ 356 (q7 c4) ∷
   rw⁻ 355 (q8 c4) ∷
   rw⁻ 354 (q8 c4) ∷
   rw⁻ 353 (q7 c4) ∷
   rw⁻ 352 (q9 c4) ∷
   rw⁻ 351 (q10 c4) ∷
   rw⁻ 350 (q8 c4) ∷
   rw⁻ 349 (q8 c4) ∷
   rw⁻ 348 (q10 c4) ∷
   rw⁻ 347 (q9 c4) ∷
   rw⁻ 346 (q7 c4) ∷
   rw⁻ 345 (q8 c4) ∷
   rw⁻ 344 (q8 c4) ∷
   rw⁻ 343 (q7 c4) ∷
   rw⁻ 342 (q9 c4) ∷
   rw⁻ 341 (q10 c4) ∷
   rw⁻ 340 (q11 c4) ∷
   rw⁻ 339 (q11 c4) ∷
   rw⁻ 338 (q10 c4) ∷
   rw⁻ 337 (q8 c4) ∷
   rw⁻ 336 (q8 c4) ∷
   rw⁻ 335 (q8 c4) ∷
   rw⁻ 334 (q9 c4) ∷
   rw⁻ 333 (q10 c4) ∷
   rw⁻ 332 (q11 c4) ∷
   rw⁻ 331 (q11 c4) ∷
   rw⁻ 330 (q10 c4) ∷
   rw⁻ 329 (q8 c4) ∷
   rw⁻ 328 (q12 c4) ∷
   rw 377 (q13 c4) ∷
   rw⁻ 376 (q14 c4) ∷
   rw⁻ 375 (q15 c4) ∷
   rw⁻ 374 (q16 c4) ∷
   rw⁻ 373 (q16 c4) ∷
   rw⁻ 372 (q15 c4) ∷
   rw⁻ 371 (q14 c4) ∷
   rw⁻ 370 (q17 c4) ∷
   rw⁻ 369 (q16 c4) ∷
   rw⁻ 368 (q16 c4) ∷
   rw⁻ 367 (q17 c4) ∷
   rw⁻ 366 (q14 c4) ∷
   rw⁻ 365 (q15 c4) ∷
   rw⁻ 364 (q16 c4) ∷
   rw⁻ 363 (q16 c4) ∷
   rw⁻ 362 (q15 c4) ∷
   rw⁻ 361 (q18 c4) ∷
   rw⁻ 360 (q14 c4) ∷
   rw⁻ 359 (q15 c4) ∷ []) Eq.refl
