{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD131 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D131 (Sᴰ : SD131) where

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
  lem-F4-K2-I-at0440 : Ws → St 1862
  lem-F4-K2-I-at0440 = pickᴰ 4 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1849
  lem-F4-K2-K1-at0440 = pickᴰ 5 Sᴰ
  lem-F4-K2-K2-at0440 : Ws → St 1850
  lem-F4-K2-K2-at0440 = pickᴰ 6 Sᴰ
  lem-F4-K2-K3-at0440 : Ws → St 1870
  lem-F4-K2-K3-at0440 = pickᴰ 7 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1865
  lem-F4-K3-K1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1861
  lem-F4-K2-CS1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 13 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1865 (lem-F4-K3-K1-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 1461 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = wlE 1715 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1862 (lem-F4-K2-I-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1870 (lem-F4-K2-K3-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1856 (lem-F4-K2-CS2-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1861 (lem-F4-K2-CS1-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1850 (lem-F4-K2-K2-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 18 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = eqn (ℓ "丫乢") (ℓ "乢丫") (c₂ (Swap) (CS))
  q19 : Ws → Eqn
  q19 c4 = wlE 6 (lit c4)
  q20 : Ws → Eqn
  q20 c4 = wlE 47 (lit c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 3 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 4 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = eqn (ℓ "乇乼") (ℓ "乼乇") (c₃ (CS ↑) (Swap))

-- ckt-TST @0440 part29: 85 steps
lem-ckt-TST-at0440-part29 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与中俵与主与临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临丫乊乥乼乇乥乥乼乥乊丫乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-at0440-part29 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与中俵与主与临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主一丘乢乢丘一丞乢乢丞一丒一") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临丫乊乥乼乇乥乥乼乥乊丫乢丘一丞乢乢丞一丒一")
  (rw⁻ 296 (q1 c4) ∷
   rw⁻ 295 (q2 c4) ∷
   rw⁻ 333 (q3 c4) ∷
   rw⁻ 332 (q4 c4) ∷
   rw⁻ 331 (q5 c4) ∷
   rw⁻ 330 (q5 c4) ∷
   rw⁻ 329 (q4 c4) ∷
   rw⁻ 328 (q6 c4) ∷
   rw⁻ 327 (q7 c4) ∷
   rw⁻ 326 (q4 c4) ∷
   rw⁻ 325 (q5 c4) ∷
   rw⁻ 324 (q5 c4) ∷
   rw⁻ 323 (q4 c4) ∷
   rw⁻ 322 (q7 c4) ∷
   rw⁻ 321 (q8 c4) ∷
   rw⁻ 320 (q5 c4) ∷
   rw⁻ 319 (q5 c4) ∷
   rw⁻ 318 (q8 c4) ∷
   rw⁻ 317 (q7 c4) ∷
   rw⁻ 316 (q4 c4) ∷
   rw⁻ 315 (q5 c4) ∷
   rw⁻ 314 (q5 c4) ∷
   rw⁻ 313 (q4 c4) ∷
   rw⁻ 312 (q7 c4) ∷
   rw⁻ 311 (q8 c4) ∷
   rw⁻ 310 (q6 c4) ∷
   rw⁻ 309 (q6 c4) ∷
   rw⁻ 308 (q8 c4) ∷
   rw⁻ 307 (q5 c4) ∷
   rw⁻ 306 (q5 c4) ∷
   rw⁻ 305 (q5 c4) ∷
   rw⁻ 304 (q7 c4) ∷
   rw⁻ 303 (q8 c4) ∷
   rw⁻ 302 (q6 c4) ∷
   rw⁻ 301 (q6 c4) ∷
   rw⁻ 300 (q8 c4) ∷
   rw⁻ 299 (q5 c4) ∷
   rw⁻ 298 (q9 c4) ∷
   rw 337 (q10 c4) ∷
   rw⁻ 336 (q11 c4) ∷
   rw⁻ 335 (q12 c4) ∷
   rw⁻ 334 (q13 c4) ∷
   rw⁻ 333 (q13 c4) ∷
   rw⁻ 332 (q12 c4) ∷
   rw⁻ 331 (q14 c4) ∷
   rw⁻ 330 (q11 c4) ∷
   rw⁻ 329 (q12 c4) ∷
   rw⁻ 328 (q13 c4) ∷
   rw⁻ 327 (q13 c4) ∷
   rw⁻ 326 (q12 c4) ∷
   rw⁻ 325 (q11 c4) ∷
   rw⁻ 324 (q15 c4) ∷
   rw⁻ 323 (q13 c4) ∷
   rw⁻ 322 (q13 c4) ∷
   rw⁻ 321 (q15 c4) ∷
   rw⁻ 320 (q11 c4) ∷
   rw⁻ 319 (q12 c4) ∷
   rw⁻ 318 (q13 c4) ∷
   rw⁻ 317 (q13 c4) ∷
   rw⁻ 316 (q12 c4) ∷
   rw⁻ 315 (q11 c4) ∷
   rw⁻ 314 (q15 c4) ∷
   rw⁻ 313 (q14 c4) ∷
   rw⁻ 312 (q14 c4) ∷
   rw⁻ 311 (q15 c4) ∷
   rw⁻ 310 (q13 c4) ∷
   rw⁻ 309 (q13 c4) ∷
   rw⁻ 308 (q13 c4) ∷
   rw⁻ 307 (q11 c4) ∷
   rw⁻ 306 (q15 c4) ∷
   rw⁻ 305 (q14 c4) ∷
   rw⁻ 304 (q14 c4) ∷
   rw⁻ 303 (q15 c4) ∷
   rw⁻ 302 (q13 c4) ∷
   rw⁻ 301 (q16 c4) ∷
   rw⁻ 342 (q17 c4) ∷
   rw⁻ 341 (q18 c4) ∷
   rw⁻ 343 (q19 c4) ∷
   rw 342 (q20 c4) ∷
   rw⁻ 344 (q21 c4) ∷
   re 343 1 (ℓ "乥乇乥") ∷
   rw 345 (q21 c4) ∷
   rw⁻ 345 (q22 c4) ∷
   rw 344 (q23 c4) ∷
   rw⁻ 346 (q21 c4) ∷ []) Eq.refl
