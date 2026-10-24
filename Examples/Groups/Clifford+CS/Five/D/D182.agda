{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD182 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D182 (Sᴰ : SD182) where

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
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 0 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 1 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 3 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1868
  lem-F4-CS2-K3-at0440 = pickᴰ 5 Sᴰ
  lem-F4-CS2-CS0-at0440 : Ws → St 1994
  lem-F4-CS2-CS0-at0440 = pickᴰ 6 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1868 (lem-F4-CS2-K3-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1994 (lem-F4-CS2-CS0-at0440 c4)

-- ckt-TST @0440 part55: 77 steps
lem-ckt-TST-at0440-part55 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵与俵与俵临上主俵俵主上中上俊与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与中俵临俭俭临上俵俵俵与俵与临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part55 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵与俵与俵临上主俵俵主上中上俊与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与中俵临俭俭临上俵俵俵与俵与临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 259 (q1 c4) ∷
   rw⁻ 258 (q2 c4) ∷
   rw⁻ 257 (q3 c4) ∷
   rw⁻ 256 (q4 c4) ∷
   rw⁻ 255 (q1 c4) ∷
   rw⁻ 254 (q1 c4) ∷
   rw⁻ 253 (q4 c4) ∷
   rw⁻ 252 (q5 c4) ∷
   rw⁻ 251 (q3 c4) ∷
   rw⁻ 250 (q4 c4) ∷
   rw⁻ 249 (q1 c4) ∷
   rw⁻ 248 (q1 c4) ∷
   rw⁻ 247 (q4 c4) ∷
   rw⁻ 246 (q3 c4) ∷
   rw⁻ 245 (q2 c4) ∷
   rw⁻ 244 (q1 c4) ∷
   rw⁻ 243 (q1 c4) ∷
   rw⁻ 242 (q2 c4) ∷
   rw⁻ 241 (q3 c4) ∷
   rw⁻ 240 (q4 c4) ∷
   rw⁻ 239 (q1 c4) ∷
   rw⁻ 238 (q1 c4) ∷
   rw⁻ 237 (q4 c4) ∷
   rw⁻ 236 (q3 c4) ∷
   rw⁻ 235 (q2 c4) ∷
   rw⁻ 234 (q5 c4) ∷
   rw⁻ 233 (q5 c4) ∷
   rw⁻ 232 (q2 c4) ∷
   rw⁻ 231 (q1 c4) ∷
   rw⁻ 230 (q1 c4) ∷
   rw⁻ 229 (q1 c4) ∷
   rw⁻ 228 (q3 c4) ∷
   rw⁻ 227 (q2 c4) ∷
   rw⁻ 226 (q5 c4) ∷
   rw⁻ 225 (q5 c4) ∷
   rw⁻ 224 (q2 c4) ∷
   rw⁻ 223 (q1 c4) ∷
   rw⁻ 222 (q6 c4) ∷
   rw⁻ 273 (q7 c4) ∷
   rw⁻ 272 (q3 c4) ∷
   rw⁻ 271 (q6 c4) ∷
   rw⁻ 270 (q3 c4) ∷
   rw⁻ 269 (q4 c4) ∷
   rw⁻ 268 (q1 c4) ∷
   rw⁻ 267 (q1 c4) ∷
   rw⁻ 266 (q4 c4) ∷
   rw⁻ 265 (q3 c4) ∷
   rw⁻ 264 (q2 c4) ∷
   rw⁻ 263 (q1 c4) ∷
   rw⁻ 262 (q1 c4) ∷
   rw⁻ 261 (q2 c4) ∷
   rw⁻ 260 (q3 c4) ∷
   rw⁻ 259 (q4 c4) ∷
   rw⁻ 258 (q1 c4) ∷
   rw⁻ 257 (q1 c4) ∷
   rw⁻ 256 (q4 c4) ∷
   rw⁻ 255 (q5 c4) ∷
   rw⁻ 254 (q3 c4) ∷
   rw⁻ 253 (q4 c4) ∷
   rw⁻ 252 (q1 c4) ∷
   rw⁻ 251 (q1 c4) ∷
   rw⁻ 250 (q4 c4) ∷
   rw⁻ 249 (q3 c4) ∷
   rw⁻ 248 (q2 c4) ∷
   rw⁻ 247 (q1 c4) ∷
   rw⁻ 246 (q1 c4) ∷
   rw⁻ 245 (q2 c4) ∷
   rw⁻ 244 (q3 c4) ∷
   rw⁻ 243 (q4 c4) ∷
   rw⁻ 242 (q1 c4) ∷
   rw⁻ 241 (q1 c4) ∷
   rw⁻ 240 (q4 c4) ∷
   rw⁻ 239 (q3 c4) ∷
   rw⁻ 238 (q2 c4) ∷
   rw⁻ 237 (q5 c4) ∷
   rw⁻ 236 (q5 c4) ∷
   rw⁻ 235 (q2 c4) ∷ []) Eq.refl
