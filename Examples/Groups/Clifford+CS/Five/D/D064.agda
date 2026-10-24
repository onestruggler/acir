{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD064 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D064 (Sᴰ : SD064) where

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
  lem-F4-I-I-at0440 : Ws → St 1683
  lem-F4-I-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-I-K1-at0440 : Ws → St 1684
  lem-F4-I-K1-at0440 = pickᴰ 1 Sᴰ
  lem-F4-I-K2-at0440 : Ws → St 1685
  lem-F4-I-K2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-I-K3-at0440 : Ws → St 1686
  lem-F4-I-K3-at0440 = pickᴰ 3 Sᴰ
  lem-F4-K1-I-at0440 : Ws → St 1687
  lem-F4-K1-I-at0440 = pickᴰ 4 Sᴰ
  lem-F4-K1-K1-at0440 : Ws → St 1688
  lem-F4-K1-K1-at0440 = pickᴰ 5 Sᴰ
  lem-F4-K1-K2-at0440 : Ws → St 1689
  lem-F4-K1-K2-at0440 = pickᴰ 6 Sᴰ
  lem-F4-K1-K3-at0440 : Ws → St 1690
  lem-F4-K1-K3-at0440 = pickᴰ 7 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-K1-CS1-at0440 : Ws → St 1692
  lem-F4-K1-CS1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K1-CS2-at0440 : Ws → St 1694
  lem-F4-K1-CS2-at0440 = pickᴰ 11 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = wlE 1460 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1687 (lem-F4-K1-I-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1690 (lem-F4-K1-K3-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1694 (lem-F4-K1-CS2-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1689 (lem-F4-K1-K2-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1692 (lem-F4-K1-CS1-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1688 (lem-F4-K1-K1-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 1461 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)

-- ckt-TST @0440 part37: 78 steps
lem-ckt-TST-at0440-part37 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与中俵临俭俭临上与上与俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临与上与上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part37 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与中俵临俭俭临上与上与俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临与上与上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 334 (q1 c4) ∷
   rw⁻ 333 (q2 c4) ∷
   rw⁻ 332 (q3 c4) ∷
   rw⁻ 331 (q3 c4) ∷
   rw⁻ 330 (q2 c4) ∷
   rw⁻ 329 (q4 c4) ∷
   rw⁻ 328 (q5 c4) ∷
   rw 377 (q6 c4) ∷
   rw⁻ 376 (q7 c4) ∷
   rw⁻ 375 (q8 c4) ∷
   rw⁻ 374 (q9 c4) ∷
   rw⁻ 373 (q9 c4) ∷
   rw⁻ 372 (q8 c4) ∷
   rw⁻ 371 (q7 c4) ∷
   rw⁻ 370 (q10 c4) ∷
   rw⁻ 369 (q9 c4) ∷
   rw⁻ 368 (q9 c4) ∷
   rw⁻ 367 (q10 c4) ∷
   rw⁻ 366 (q7 c4) ∷
   rw⁻ 365 (q8 c4) ∷
   rw⁻ 364 (q9 c4) ∷
   rw⁻ 363 (q9 c4) ∷
   rw⁻ 362 (q8 c4) ∷
   rw⁻ 361 (q11 c4) ∷
   rw⁻ 360 (q7 c4) ∷
   rw⁻ 359 (q8 c4) ∷
   rw⁻ 358 (q9 c4) ∷
   rw⁻ 357 (q9 c4) ∷
   rw⁻ 356 (q8 c4) ∷
   rw⁻ 355 (q7 c4) ∷
   rw⁻ 354 (q10 c4) ∷
   rw⁻ 353 (q9 c4) ∷
   rw⁻ 352 (q9 c4) ∷
   rw⁻ 351 (q10 c4) ∷
   rw⁻ 350 (q7 c4) ∷
   rw⁻ 349 (q8 c4) ∷
   rw⁻ 348 (q9 c4) ∷
   rw⁻ 347 (q9 c4) ∷
   rw⁻ 346 (q8 c4) ∷
   rw⁻ 345 (q7 c4) ∷
   rw⁻ 344 (q10 c4) ∷
   rw⁻ 343 (q11 c4) ∷
   rw⁻ 342 (q11 c4) ∷
   rw⁻ 341 (q10 c4) ∷
   rw⁻ 340 (q9 c4) ∷
   rw⁻ 339 (q9 c4) ∷
   rw⁻ 338 (q9 c4) ∷
   rw⁻ 337 (q7 c4) ∷
   rw⁻ 336 (q10 c4) ∷
   rw⁻ 335 (q11 c4) ∷
   rw⁻ 334 (q11 c4) ∷
   rw⁻ 333 (q10 c4) ∷
   rw⁻ 332 (q9 c4) ∷
   rw⁻ 331 (q12 c4) ∷
   rw⁻ 381 (q13 c4) ∷
   rw⁻ 380 (q5 c4) ∷
   rw⁻ 379 (q1 c4) ∷
   rw⁻ 378 (q14 c4) ∷
   rw⁻ 377 (q4 c4) ∷
   rw⁻ 376 (q4 c4) ∷
   rw⁻ 375 (q14 c4) ∷
   rw⁻ 374 (q1 c4) ∷
   rw⁻ 373 (q2 c4) ∷
   rw⁻ 372 (q4 c4) ∷
   rw⁻ 371 (q4 c4) ∷
   rw⁻ 370 (q2 c4) ∷
   rw⁻ 369 (q1 c4) ∷
   rw⁻ 368 (q14 c4) ∷
   rw⁻ 367 (q4 c4) ∷
   rw⁻ 366 (q4 c4) ∷
   rw⁻ 365 (q14 c4) ∷
   rw⁻ 364 (q3 c4) ∷
   rw⁻ 363 (q1 c4) ∷
   rw⁻ 362 (q14 c4) ∷
   rw⁻ 361 (q4 c4) ∷
   rw⁻ 360 (q4 c4) ∷
   rw⁻ 359 (q14 c4) ∷
   rw⁻ 358 (q1 c4) ∷ []) Eq.refl
