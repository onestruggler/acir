{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD210 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D210 (Sᴰ : SD210) where

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
  lem-F4-CS1-CS1-at0440 : Ws → St 1851
  lem-F4-CS1-CS1-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS1-I-at0440 : Ws → St 1863
  lem-F4-CS1-I-at0440 = pickᴰ 5 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1852
  lem-F4-CS1-K1-at0440 = pickᴰ 6 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 7 Sᴰ
  lem-F4-CS1-K3-at0440 : Ws → St 1872
  lem-F4-CS1-K3-at0440 = pickᴰ 8 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 9 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1858
  lem-F4-CS1-K2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1859
  lem-F4-CS1-CS2-at0440 = pickᴰ 11 Sᴰ
  lem-F4-CS1-CS0-at0440 : Ws → St 2126
  lem-F4-CS1-CS0-at0440 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 2126 (lem-F4-CS1-CS0-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1863 (lem-F4-CS1-I-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1852 (lem-F4-CS1-K1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1872 (lem-F4-CS1-K3-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1859 (lem-F4-CS1-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1858 (lem-F4-CS1-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1851 (lem-F4-CS1-CS1-at0440 c4)

-- ckt-TST @0440 part57: 77 steps
lem-ckt-TST-at0440-part57 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭与上与主俵俵主上临俵俵临上主俵俵主上中上俊与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临与俭与俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part57 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭与上与主俵俵主上临俵俵临上主俵俵主上中上俊与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与中俵临与俭与俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 261 (q1 c4) ∷
   rw⁻ 260 (q2 c4) ∷
   rw⁻ 259 (q3 c4) ∷
   rw⁻ 258 (q4 c4) ∷
   rw⁻ 257 (q4 c4) ∷
   rw⁻ 256 (q3 c4) ∷
   rw⁻ 255 (q2 c4) ∷
   rw⁻ 254 (q5 c4) ∷
   rw⁻ 253 (q4 c4) ∷
   rw⁻ 252 (q4 c4) ∷
   rw⁻ 251 (q5 c4) ∷
   rw⁻ 250 (q2 c4) ∷
   rw⁻ 249 (q3 c4) ∷
   rw⁻ 248 (q4 c4) ∷
   rw⁻ 247 (q4 c4) ∷
   rw⁻ 246 (q3 c4) ∷
   rw⁻ 245 (q2 c4) ∷
   rw⁻ 244 (q5 c4) ∷
   rw⁻ 243 (q1 c4) ∷
   rw⁻ 242 (q1 c4) ∷
   rw⁻ 241 (q5 c4) ∷
   rw⁻ 240 (q4 c4) ∷
   rw⁻ 239 (q4 c4) ∷
   rw⁻ 238 (q4 c4) ∷
   rw⁻ 237 (q2 c4) ∷
   rw⁻ 236 (q5 c4) ∷
   rw⁻ 235 (q1 c4) ∷
   rw⁻ 234 (q1 c4) ∷
   rw⁻ 233 (q5 c4) ∷
   rw⁻ 232 (q4 c4) ∷
   rw⁻ 231 (q6 c4) ∷
   rw⁻ 282 (q7 c4) ∷
   rw⁻ 281 (q8 c4) ∷
   rw⁻ 280 (q9 c4) ∷
   rw⁻ 279 (q8 c4) ∷
   rw⁻ 278 (q10 c4) ∷
   rw⁻ 277 (q11 c4) ∷
   rw⁻ 276 (q11 c4) ∷
   rw⁻ 275 (q10 c4) ∷
   rw⁻ 274 (q8 c4) ∷
   rw⁻ 273 (q12 c4) ∷
   rw⁻ 272 (q11 c4) ∷
   rw⁻ 271 (q11 c4) ∷
   rw⁻ 270 (q12 c4) ∷
   rw⁻ 269 (q8 c4) ∷
   rw⁻ 268 (q10 c4) ∷
   rw⁻ 267 (q11 c4) ∷
   rw⁻ 266 (q11 c4) ∷
   rw⁻ 265 (q10 c4) ∷
   rw⁻ 264 (q13 c4) ∷
   rw⁻ 263 (q8 c4) ∷
   rw⁻ 262 (q10 c4) ∷
   rw⁻ 261 (q11 c4) ∷
   rw⁻ 260 (q11 c4) ∷
   rw⁻ 259 (q10 c4) ∷
   rw⁻ 258 (q8 c4) ∷
   rw⁻ 257 (q12 c4) ∷
   rw⁻ 256 (q11 c4) ∷
   rw⁻ 255 (q11 c4) ∷
   rw⁻ 254 (q12 c4) ∷
   rw⁻ 253 (q8 c4) ∷
   rw⁻ 252 (q10 c4) ∷
   rw⁻ 251 (q11 c4) ∷
   rw⁻ 250 (q11 c4) ∷
   rw⁻ 249 (q10 c4) ∷
   rw⁻ 248 (q8 c4) ∷
   rw⁻ 247 (q12 c4) ∷
   rw⁻ 246 (q13 c4) ∷
   rw⁻ 245 (q13 c4) ∷
   rw⁻ 244 (q12 c4) ∷
   rw⁻ 243 (q11 c4) ∷
   rw⁻ 242 (q11 c4) ∷
   rw⁻ 241 (q11 c4) ∷
   rw⁻ 240 (q8 c4) ∷
   rw⁻ 239 (q12 c4) ∷
   rw⁻ 238 (q13 c4) ∷
   rw⁻ 237 (q13 c4) ∷ []) Eq.refl
