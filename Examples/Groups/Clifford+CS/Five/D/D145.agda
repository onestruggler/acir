{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD145 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D145 (Sᴰ : SD145) where

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
  lem-F4-K3-I-at0440 : Ws → St 1864
  lem-F4-K3-I-at0440 = pickᴰ 2 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1865
  lem-F4-K3-K1-at0440 = pickᴰ 3 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1866
  lem-F4-K3-K2-at0440 = pickᴰ 4 Sᴰ
  lem-F4-K3-K3-at0440 : Ws → St 1871
  lem-F4-K3-K3-at0440 = pickᴰ 5 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 6 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 7 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 8 Sᴰ
  lem-F4-K3-CS1-at0440 : Ws → St 1867
  lem-F4-K3-CS1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-I-CS0-at0440 : Ws → St 1699
  lem-F4-I-CS0-at0440 = pickᴰ 10 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-K3-CS0-at0440 : Ws → St 1873
  lem-F4-K3-CS0-at0440 = pickᴰ 12 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 13 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1868
  lem-F4-CS2-K3-at0440 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1868 (lem-F4-CS2-K3-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1873 (lem-F4-K3-CS0-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1864 (lem-F4-K3-I-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1865 (lem-F4-K3-K1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1871 (lem-F4-K3-K3-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1866 (lem-F4-K3-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1867 (lem-F4-K3-CS1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1699 (lem-F4-I-CS0-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)

-- ckt-TST @0440 part66: 77 steps
lem-ckt-TST-at0440-part66 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临与俵与上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主与上与上中上俊与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part66 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临与俵与上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主与上与上中上俊与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 296 (q1 c4) ∷
   rw⁻ 295 (q2 c4) ∷
   rw⁻ 294 (q2 c4) ∷
   rw⁻ 293 (q1 c4) ∷
   rw⁻ 292 (q3 c4) ∷
   rw⁻ 291 (q4 c4) ∷
   rw⁻ 290 (q2 c4) ∷
   rw⁻ 289 (q2 c4) ∷
   rw⁻ 288 (q4 c4) ∷
   rw⁻ 287 (q3 c4) ∷
   rw⁻ 286 (q1 c4) ∷
   rw⁻ 285 (q5 c4) ∷
   rw⁻ 284 (q5 c4) ∷
   rw⁻ 283 (q1 c4) ∷
   rw⁻ 282 (q2 c4) ∷
   rw⁻ 281 (q2 c4) ∷
   rw⁻ 280 (q2 c4) ∷
   rw⁻ 279 (q3 c4) ∷
   rw⁻ 278 (q1 c4) ∷
   rw⁻ 277 (q5 c4) ∷
   rw⁻ 276 (q5 c4) ∷
   rw⁻ 275 (q1 c4) ∷
   rw⁻ 274 (q2 c4) ∷
   rw⁻ 273 (q6 c4) ∷
   rw⁻ 324 (q7 c4) ∷
   rw⁻ 323 (q8 c4) ∷
   rw⁻ 322 (q9 c4) ∷
   rw⁻ 321 (q8 c4) ∷
   rw⁻ 320 (q10 c4) ∷
   rw⁻ 319 (q11 c4) ∷
   rw⁻ 318 (q11 c4) ∷
   rw⁻ 317 (q10 c4) ∷
   rw⁻ 316 (q8 c4) ∷
   rw⁻ 315 (q12 c4) ∷
   rw⁻ 314 (q11 c4) ∷
   rw⁻ 313 (q11 c4) ∷
   rw⁻ 312 (q12 c4) ∷
   rw⁻ 311 (q8 c4) ∷
   rw⁻ 310 (q10 c4) ∷
   rw⁻ 309 (q11 c4) ∷
   rw⁻ 308 (q11 c4) ∷
   rw⁻ 307 (q10 c4) ∷
   rw⁻ 306 (q13 c4) ∷
   rw⁻ 305 (q8 c4) ∷
   rw⁻ 304 (q10 c4) ∷
   rw⁻ 303 (q11 c4) ∷
   rw⁻ 302 (q11 c4) ∷
   rw⁻ 301 (q10 c4) ∷
   rw⁻ 300 (q8 c4) ∷
   rw⁻ 299 (q12 c4) ∷
   rw⁻ 298 (q11 c4) ∷
   rw⁻ 297 (q11 c4) ∷
   rw⁻ 296 (q12 c4) ∷
   rw⁻ 295 (q8 c4) ∷
   rw⁻ 294 (q10 c4) ∷
   rw⁻ 293 (q11 c4) ∷
   rw⁻ 292 (q11 c4) ∷
   rw⁻ 291 (q10 c4) ∷
   rw⁻ 290 (q8 c4) ∷
   rw⁻ 289 (q12 c4) ∷
   rw⁻ 288 (q13 c4) ∷
   rw⁻ 287 (q13 c4) ∷
   rw⁻ 286 (q12 c4) ∷
   rw⁻ 285 (q11 c4) ∷
   rw⁻ 284 (q11 c4) ∷
   rw⁻ 283 (q11 c4) ∷
   rw⁻ 282 (q8 c4) ∷
   rw⁻ 281 (q12 c4) ∷
   rw⁻ 280 (q13 c4) ∷
   rw⁻ 279 (q13 c4) ∷
   rw⁻ 278 (q12 c4) ∷
   rw⁻ 277 (q11 c4) ∷
   rw⁻ 276 (q9 c4) ∷
   rw⁻ 327 (q14 c4) ∷
   rw⁻ 326 (q15 c4) ∷
   rw⁻ 325 (q16 c4) ∷
   rw⁻ 324 (q15 c4) ∷ []) Eq.refl
