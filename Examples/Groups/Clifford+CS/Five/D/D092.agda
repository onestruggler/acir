{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD092 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D092 (Sᴰ : SD092) where

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
  lem-F4-I-K2 : Ws → St 1410
  lem-F4-I-K2 = pickᴰ 1 Sᴰ
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 2 Sᴰ
  lem-F4-K2-I : Ws → St 1809
  lem-F4-K2-I = pickᴰ 3 Sᴰ
  lem-F4-K2-K1 : Ws → St 1810
  lem-F4-K2-K1 = pickᴰ 4 Sᴰ
  lem-F4-K2-K2 : Ws → St 1565
  lem-F4-K2-K2 = pickᴰ 5 Sᴰ
  lem-F4-K2-K3 : Ws → St 1811
  lem-F4-K2-K3 = pickᴰ 6 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 7 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 8 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1578
  lem-F4-K2-CS2 = pickᴰ 9 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 10 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 11 Sᴰ
  lem-F4-K2-CS1 : Ws → St 1818
  lem-F4-K2-CS1 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 1409 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1578 (lem-F4-K2-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1565 (lem-F4-K2-K2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1809 (lem-F4-K2-I c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1811 (lem-F4-K2-K3 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1818 (lem-F4-K2-CS1 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1810 (lem-F4-K2-K1 c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 1411 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1410 (lem-F4-I-K2 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1386 (lem-F4-I-I c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1411 (lem-F4-I-K3 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1432 (lem-F4-I-CS1 c4)

-- ckt-TST part16: 82 steps
lem-ckt-TST-part16 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並亄侬並侬並亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並亄並丢並侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-part16 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並亄侬並侬並亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬丘一丞乢乢丞一丒一") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並亄並丢並侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢丞乢乢丞一丒一")
  (rw⁻ 308 (q1 c4) ∷
   rw⁻ 307 (q2 c4) ∷
   rw 349 (q3 c4) ∷
   rw⁻ 348 (q4 c4) ∷
   rw⁻ 347 (q4 c4) ∷
   rw⁻ 346 (q5 c4) ∷
   rw⁻ 345 (q6 c4) ∷
   rw⁻ 344 (q7 c4) ∷
   rw⁻ 343 (q4 c4) ∷
   rw⁻ 342 (q4 c4) ∷
   rw⁻ 341 (q7 c4) ∷
   rw⁻ 340 (q8 c4) ∷
   rw⁻ 339 (q6 c4) ∷
   rw⁻ 338 (q7 c4) ∷
   rw⁻ 337 (q4 c4) ∷
   rw⁻ 336 (q4 c4) ∷
   rw⁻ 335 (q7 c4) ∷
   rw⁻ 334 (q6 c4) ∷
   rw⁻ 333 (q5 c4) ∷
   rw⁻ 332 (q4 c4) ∷
   rw⁻ 331 (q4 c4) ∷
   rw⁻ 330 (q5 c4) ∷
   rw⁻ 329 (q6 c4) ∷
   rw⁻ 328 (q7 c4) ∷
   rw⁻ 327 (q4 c4) ∷
   rw⁻ 326 (q4 c4) ∷
   rw⁻ 325 (q7 c4) ∷
   rw⁻ 324 (q6 c4) ∷
   rw⁻ 323 (q5 c4) ∷
   rw⁻ 322 (q8 c4) ∷
   rw⁻ 321 (q8 c4) ∷
   rw⁻ 320 (q5 c4) ∷
   rw⁻ 319 (q4 c4) ∷
   rw⁻ 318 (q4 c4) ∷
   rw⁻ 317 (q4 c4) ∷
   rw⁻ 316 (q6 c4) ∷
   rw⁻ 315 (q5 c4) ∷
   rw⁻ 314 (q8 c4) ∷
   rw⁻ 313 (q8 c4) ∷
   rw⁻ 312 (q5 c4) ∷
   rw⁻ 311 (q4 c4) ∷
   rw⁻ 310 (q9 c4) ∷
   rw⁻ 353 (q10 c4) ∷
   rw⁻ 352 (q11 c4) ∷
   rw⁻ 351 (q12 c4) ∷
   rw⁻ 350 (q12 c4) ∷
   rw⁻ 349 (q11 c4) ∷
   rw⁻ 348 (q13 c4) ∷
   rw⁻ 347 (q14 c4) ∷
   rw⁻ 346 (q12 c4) ∷
   rw⁻ 345 (q12 c4) ∷
   rw⁻ 344 (q14 c4) ∷
   rw⁻ 343 (q15 c4) ∷
   rw⁻ 342 (q13 c4) ∷
   rw⁻ 341 (q14 c4) ∷
   rw⁻ 340 (q12 c4) ∷
   rw⁻ 339 (q12 c4) ∷
   rw⁻ 338 (q14 c4) ∷
   rw⁻ 337 (q13 c4) ∷
   rw⁻ 336 (q11 c4) ∷
   rw⁻ 335 (q12 c4) ∷
   rw⁻ 334 (q12 c4) ∷
   rw⁻ 333 (q11 c4) ∷
   rw⁻ 332 (q13 c4) ∷
   rw⁻ 331 (q14 c4) ∷
   rw⁻ 330 (q12 c4) ∷
   rw⁻ 329 (q12 c4) ∷
   rw⁻ 328 (q14 c4) ∷
   rw⁻ 327 (q13 c4) ∷
   rw⁻ 326 (q11 c4) ∷
   rw⁻ 325 (q15 c4) ∷
   rw⁻ 324 (q15 c4) ∷
   rw⁻ 323 (q11 c4) ∷
   rw⁻ 322 (q12 c4) ∷
   rw⁻ 321 (q12 c4) ∷
   rw⁻ 320 (q12 c4) ∷
   rw⁻ 319 (q13 c4) ∷
   rw⁻ 318 (q11 c4) ∷
   rw⁻ 317 (q15 c4) ∷
   rw⁻ 316 (q15 c4) ∷
   rw⁻ 315 (q11 c4) ∷
   rw⁻ 314 (q12 c4) ∷ []) Eq.refl
