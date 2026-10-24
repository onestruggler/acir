{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD187 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D187 (Sᴰ : SD187) where

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
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 8 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 9 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 12 Sᴰ
  lem-F4-I-CS0-at0440 : Ws → St 1699
  lem-F4-I-CS0-at0440 = pickᴰ 13 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 14 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 15 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1861
  lem-F4-K2-CS1-at0440 = pickᴰ 16 Sᴰ
  lem-F4-K2-CS0-at0440 : Ws → St 1995
  lem-F4-K2-CS0-at0440 = pickᴰ 17 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1995 (lem-F4-K2-CS0-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1862 (lem-F4-K2-I-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1870 (lem-F4-K2-K3-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1856 (lem-F4-K2-CS2-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1850 (lem-F4-K2-K2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1861 (lem-F4-K2-CS1-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1699 (lem-F4-I-CS0-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)

-- ckt-TST @0440 part63: 77 steps
lem-ckt-TST-at0440-part63 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与中俵临俭俭临上俵俵俵与俵与临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭与上与主俵俵主上临俵俵临上主俵俵主上中上俊与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part63 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与中俵临俭俭临上俵俵俵与俵与临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭与上与主俵俵主上临俵俵临上主俵俵主上中上俊与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 267 (q1 c4) ∷
   rw⁻ 266 (q1 c4) ∷
   rw⁻ 265 (q1 c4) ∷
   rw⁻ 264 (q2 c4) ∷
   rw⁻ 263 (q3 c4) ∷
   rw⁻ 262 (q4 c4) ∷
   rw⁻ 261 (q4 c4) ∷
   rw⁻ 260 (q3 c4) ∷
   rw⁻ 259 (q1 c4) ∷
   rw⁻ 258 (q5 c4) ∷
   rw⁻ 309 (q6 c4) ∷
   rw⁻ 308 (q7 c4) ∷
   rw⁻ 307 (q8 c4) ∷
   rw⁻ 306 (q7 c4) ∷
   rw⁻ 305 (q9 c4) ∷
   rw⁻ 304 (q10 c4) ∷
   rw⁻ 303 (q10 c4) ∷
   rw⁻ 302 (q9 c4) ∷
   rw⁻ 301 (q7 c4) ∷
   rw⁻ 300 (q11 c4) ∷
   rw⁻ 299 (q10 c4) ∷
   rw⁻ 298 (q10 c4) ∷
   rw⁻ 297 (q11 c4) ∷
   rw⁻ 296 (q7 c4) ∷
   rw⁻ 295 (q9 c4) ∷
   rw⁻ 294 (q10 c4) ∷
   rw⁻ 293 (q10 c4) ∷
   rw⁻ 292 (q9 c4) ∷
   rw⁻ 291 (q12 c4) ∷
   rw⁻ 290 (q7 c4) ∷
   rw⁻ 289 (q9 c4) ∷
   rw⁻ 288 (q10 c4) ∷
   rw⁻ 287 (q10 c4) ∷
   rw⁻ 286 (q9 c4) ∷
   rw⁻ 285 (q7 c4) ∷
   rw⁻ 284 (q11 c4) ∷
   rw⁻ 283 (q10 c4) ∷
   rw⁻ 282 (q10 c4) ∷
   rw⁻ 281 (q11 c4) ∷
   rw⁻ 280 (q7 c4) ∷
   rw⁻ 279 (q9 c4) ∷
   rw⁻ 278 (q10 c4) ∷
   rw⁻ 277 (q10 c4) ∷
   rw⁻ 276 (q9 c4) ∷
   rw⁻ 275 (q7 c4) ∷
   rw⁻ 274 (q11 c4) ∷
   rw⁻ 273 (q12 c4) ∷
   rw⁻ 272 (q12 c4) ∷
   rw⁻ 271 (q11 c4) ∷
   rw⁻ 270 (q10 c4) ∷
   rw⁻ 269 (q10 c4) ∷
   rw⁻ 268 (q10 c4) ∷
   rw⁻ 267 (q7 c4) ∷
   rw⁻ 266 (q11 c4) ∷
   rw⁻ 265 (q12 c4) ∷
   rw⁻ 264 (q12 c4) ∷
   rw⁻ 263 (q11 c4) ∷
   rw⁻ 262 (q10 c4) ∷
   rw⁻ 261 (q8 c4) ∷
   rw⁻ 312 (q13 c4) ∷
   rw⁻ 311 (q14 c4) ∷
   rw⁻ 310 (q15 c4) ∷
   rw⁻ 309 (q14 c4) ∷
   rw⁻ 308 (q16 c4) ∷
   rw⁻ 307 (q17 c4) ∷
   rw⁻ 306 (q17 c4) ∷
   rw⁻ 305 (q16 c4) ∷
   rw⁻ 304 (q14 c4) ∷
   rw⁻ 303 (q18 c4) ∷
   rw⁻ 302 (q17 c4) ∷
   rw⁻ 301 (q17 c4) ∷
   rw⁻ 300 (q18 c4) ∷
   rw⁻ 299 (q14 c4) ∷
   rw⁻ 298 (q16 c4) ∷
   rw⁻ 297 (q17 c4) ∷
   rw⁻ 296 (q17 c4) ∷
   rw⁻ 295 (q16 c4) ∷ []) Eq.refl
