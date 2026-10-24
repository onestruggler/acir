{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD065 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D065 (Sᴰ : SD065) where

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
  lem-F4-K1-CS0-at0440 : Ws → St 1695
  lem-F4-K1-CS0-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K1-CS2-at0440 : Ws → St 1694
  lem-F4-K1-CS2-at0440 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1695 (lem-F4-K1-CS0-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1687 (lem-F4-K1-I-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1688 (lem-F4-K1-K1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1690 (lem-F4-K1-K3-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1694 (lem-F4-K1-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1689 (lem-F4-K1-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1692 (lem-F4-K1-CS1-at0440 c4)

-- ckt-TST @0440 part67: 77 steps
lem-ckt-TST-at0440-part67 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主与上与上中上俊与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵与中与俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part67 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主与上与上中上俊与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵与中与俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 323 (q1 c4) ∷
   rw⁻ 322 (q2 c4) ∷
   rw⁻ 321 (q2 c4) ∷
   rw⁻ 320 (q1 c4) ∷
   rw⁻ 319 (q3 c4) ∷
   rw⁻ 318 (q4 c4) ∷
   rw⁻ 317 (q2 c4) ∷
   rw⁻ 316 (q2 c4) ∷
   rw⁻ 315 (q4 c4) ∷
   rw⁻ 314 (q3 c4) ∷
   rw⁻ 313 (q1 c4) ∷
   rw⁻ 312 (q2 c4) ∷
   rw⁻ 311 (q2 c4) ∷
   rw⁻ 310 (q1 c4) ∷
   rw⁻ 309 (q5 c4) ∷
   rw⁻ 308 (q3 c4) ∷
   rw⁻ 307 (q1 c4) ∷
   rw⁻ 306 (q2 c4) ∷
   rw⁻ 305 (q2 c4) ∷
   rw⁻ 304 (q1 c4) ∷
   rw⁻ 303 (q3 c4) ∷
   rw⁻ 302 (q4 c4) ∷
   rw⁻ 301 (q2 c4) ∷
   rw⁻ 300 (q2 c4) ∷
   rw⁻ 299 (q4 c4) ∷
   rw⁻ 298 (q3 c4) ∷
   rw⁻ 297 (q1 c4) ∷
   rw⁻ 296 (q2 c4) ∷
   rw⁻ 295 (q2 c4) ∷
   rw⁻ 294 (q1 c4) ∷
   rw⁻ 293 (q3 c4) ∷
   rw⁻ 292 (q4 c4) ∷
   rw⁻ 291 (q5 c4) ∷
   rw⁻ 290 (q5 c4) ∷
   rw⁻ 289 (q4 c4) ∷
   rw⁻ 288 (q2 c4) ∷
   rw⁻ 287 (q2 c4) ∷
   rw⁻ 286 (q2 c4) ∷
   rw⁻ 285 (q3 c4) ∷
   rw⁻ 284 (q4 c4) ∷
   rw⁻ 283 (q5 c4) ∷
   rw⁻ 282 (q5 c4) ∷
   rw⁻ 281 (q4 c4) ∷
   rw⁻ 280 (q2 c4) ∷
   rw⁻ 279 (q6 c4) ∷
   rw⁻ 330 (q7 c4) ∷
   rw⁻ 329 (q8 c4) ∷
   rw⁻ 328 (q9 c4) ∷
   rw⁻ 327 (q8 c4) ∷
   rw⁻ 326 (q10 c4) ∷
   rw⁻ 325 (q11 c4) ∷
   rw⁻ 324 (q11 c4) ∷
   rw⁻ 323 (q10 c4) ∷
   rw⁻ 322 (q8 c4) ∷
   rw⁻ 321 (q12 c4) ∷
   rw⁻ 320 (q11 c4) ∷
   rw⁻ 319 (q11 c4) ∷
   rw⁻ 318 (q12 c4) ∷
   rw⁻ 317 (q8 c4) ∷
   rw⁻ 316 (q10 c4) ∷
   rw⁻ 315 (q11 c4) ∷
   rw⁻ 314 (q11 c4) ∷
   rw⁻ 313 (q10 c4) ∷
   rw⁻ 312 (q13 c4) ∷
   rw⁻ 311 (q8 c4) ∷
   rw⁻ 310 (q10 c4) ∷
   rw⁻ 309 (q11 c4) ∷
   rw⁻ 308 (q11 c4) ∷
   rw⁻ 307 (q10 c4) ∷
   rw⁻ 306 (q8 c4) ∷
   rw⁻ 305 (q12 c4) ∷
   rw⁻ 304 (q11 c4) ∷
   rw⁻ 303 (q11 c4) ∷
   rw⁻ 302 (q12 c4) ∷
   rw⁻ 301 (q8 c4) ∷
   rw⁻ 300 (q10 c4) ∷
   rw⁻ 299 (q11 c4) ∷ []) Eq.refl
