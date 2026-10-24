{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD093 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D093 (Sᴰ : SD093) where

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
  lem-F4-I-K1 : Ws → St 1409
  lem-F4-I-K1 = pickᴰ 0 Sᴰ
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 1 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 2 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 3 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 4 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 5 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 6 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 7 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 8 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 9 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 10 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1409 (lem-F4-I-K1 c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 1419 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1618 (lem-F4-K3-I c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1590 (lem-F5-23 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1576 (lem-F4-CS2-I c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1820 (lem-F4-CS2-CS1 c4)

-- ckt-TST part17: 81 steps
lem-ckt-TST-part17 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並亄並丢並侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並亄侬亇侧侧並侬並亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬乢丞一丒一") ⟫ʷ
lem-ckt-TST-part17 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並亄並丢並侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢丞乢乢丞一丒一") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並亄侬亇侧侧並侬並亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬乢丞一丒一")
  (rw⁻ 313 (q1 c4) ∷
   rw 357 (q2 c4) ∷
   rw⁻ 356 (q3 c4) ∷
   rw⁻ 355 (q4 c4) ∷
   rw⁻ 354 (q5 c4) ∷
   rw⁻ 353 (q5 c4) ∷
   rw⁻ 352 (q4 c4) ∷
   rw⁻ 351 (q3 c4) ∷
   rw⁻ 350 (q6 c4) ∷
   rw⁻ 349 (q5 c4) ∷
   rw⁻ 348 (q5 c4) ∷
   rw⁻ 347 (q6 c4) ∷
   rw⁻ 346 (q7 c4) ∷
   rw⁻ 345 (q3 c4) ∷
   rw⁻ 344 (q6 c4) ∷
   rw⁻ 343 (q5 c4) ∷
   rw⁻ 342 (q5 c4) ∷
   rw⁻ 341 (q6 c4) ∷
   rw⁻ 340 (q3 c4) ∷
   rw⁻ 339 (q4 c4) ∷
   rw⁻ 338 (q5 c4) ∷
   rw⁻ 337 (q5 c4) ∷
   rw⁻ 336 (q4 c4) ∷
   rw⁻ 335 (q3 c4) ∷
   rw⁻ 334 (q6 c4) ∷
   rw⁻ 333 (q5 c4) ∷
   rw⁻ 332 (q5 c4) ∷
   rw⁻ 331 (q6 c4) ∷
   rw⁻ 330 (q3 c4) ∷
   rw⁻ 329 (q4 c4) ∷
   rw⁻ 328 (q7 c4) ∷
   rw⁻ 327 (q7 c4) ∷
   rw⁻ 326 (q4 c4) ∷
   rw⁻ 325 (q5 c4) ∷
   rw⁻ 324 (q5 c4) ∷
   rw⁻ 323 (q5 c4) ∷
   rw⁻ 322 (q3 c4) ∷
   rw⁻ 321 (q4 c4) ∷
   rw⁻ 320 (q7 c4) ∷
   rw⁻ 319 (q7 c4) ∷
   rw⁻ 318 (q4 c4) ∷
   rw⁻ 317 (q5 c4) ∷
   rw⁻ 316 (q8 c4) ∷
   rw⁻ 361 (q9 c4) ∷
   rw⁻ 360 (q10 c4) ∷
   rw⁻ 359 (q11 c4) ∷
   rw⁻ 358 (q12 c4) ∷
   rw⁻ 357 (q13 c4) ∷
   rw⁻ 356 (q13 c4) ∷
   rw⁻ 355 (q12 c4) ∷
   rw⁻ 354 (q11 c4) ∷
   rw⁻ 353 (q10 c4) ∷
   rw⁻ 352 (q13 c4) ∷
   rw⁻ 351 (q13 c4) ∷
   rw⁻ 350 (q10 c4) ∷
   rw⁻ 349 (q14 c4) ∷
   rw⁻ 348 (q11 c4) ∷
   rw⁻ 347 (q10 c4) ∷
   rw⁻ 346 (q13 c4) ∷
   rw⁻ 345 (q13 c4) ∷
   rw⁻ 344 (q10 c4) ∷
   rw⁻ 343 (q11 c4) ∷
   rw⁻ 342 (q12 c4) ∷
   rw⁻ 341 (q13 c4) ∷
   rw⁻ 340 (q13 c4) ∷
   rw⁻ 339 (q12 c4) ∷
   rw⁻ 338 (q11 c4) ∷
   rw⁻ 337 (q10 c4) ∷
   rw⁻ 336 (q13 c4) ∷
   rw⁻ 335 (q13 c4) ∷
   rw⁻ 334 (q10 c4) ∷
   rw⁻ 333 (q11 c4) ∷
   rw⁻ 332 (q12 c4) ∷
   rw⁻ 331 (q14 c4) ∷
   rw⁻ 330 (q14 c4) ∷
   rw⁻ 329 (q12 c4) ∷
   rw⁻ 328 (q13 c4) ∷
   rw⁻ 327 (q13 c4) ∷
   rw⁻ 326 (q13 c4) ∷
   rw⁻ 325 (q11 c4) ∷
   rw⁻ 324 (q12 c4) ∷ []) Eq.refl
