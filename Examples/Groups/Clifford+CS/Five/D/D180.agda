{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD180 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D180 (Sᴰ : SD180) where

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
  lem-F4-K2-I-at0440 : Ws → St 1862
  lem-F4-K2-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-K2-K1-at0440 : Ws → St 1849
  lem-F4-K2-K1-at0440 = pickᴰ 1 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 3 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 5 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 6 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1868
  lem-F4-CS2-K3-at0440 = pickᴰ 7 Sᴰ
  lem-F4-CS2-CS0-at0440 : Ws → St 1994
  lem-F4-CS2-CS0-at0440 = pickᴰ 8 Sᴰ
  lem-F4-K2-CS0-at0440 : Ws → St 1995
  lem-F4-K2-CS0-at0440 = pickᴰ 9 Sᴰ

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
  q7 c4 = sE 1994 (lem-F4-CS2-CS0-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1995 (lem-F4-K2-CS0-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1862 (lem-F4-K2-I-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)

-- ckt-TST @0440 part52: 77 steps
lem-ckt-TST-at0440-part52 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临与俵与上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主与临与上中上俊与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part52 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临与俵与上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主与临与上中上俊与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 230 (q1 c4) ∷
   rw⁻ 229 (q2 c4) ∷
   rw⁻ 228 (q2 c4) ∷
   rw⁻ 227 (q1 c4) ∷
   rw⁻ 226 (q3 c4) ∷
   rw⁻ 225 (q4 c4) ∷
   rw⁻ 224 (q2 c4) ∷
   rw⁻ 223 (q2 c4) ∷
   rw⁻ 222 (q4 c4) ∷
   rw⁻ 221 (q3 c4) ∷
   rw⁻ 220 (q1 c4) ∷
   rw⁻ 219 (q5 c4) ∷
   rw⁻ 218 (q5 c4) ∷
   rw⁻ 217 (q1 c4) ∷
   rw⁻ 216 (q2 c4) ∷
   rw⁻ 215 (q2 c4) ∷
   rw⁻ 214 (q2 c4) ∷
   rw⁻ 213 (q3 c4) ∷
   rw⁻ 212 (q1 c4) ∷
   rw⁻ 211 (q5 c4) ∷
   rw⁻ 210 (q5 c4) ∷
   rw⁻ 209 (q1 c4) ∷
   rw⁻ 208 (q2 c4) ∷
   rw⁻ 207 (q6 c4) ∷
   rw⁻ 258 (q7 c4) ∷
   rw⁻ 257 (q3 c4) ∷
   rw⁻ 256 (q6 c4) ∷
   rw⁻ 255 (q3 c4) ∷
   rw⁻ 254 (q4 c4) ∷
   rw⁻ 253 (q2 c4) ∷
   rw⁻ 252 (q2 c4) ∷
   rw⁻ 251 (q4 c4) ∷
   rw⁻ 250 (q3 c4) ∷
   rw⁻ 249 (q1 c4) ∷
   rw⁻ 248 (q2 c4) ∷
   rw⁻ 247 (q2 c4) ∷
   rw⁻ 246 (q1 c4) ∷
   rw⁻ 245 (q3 c4) ∷
   rw⁻ 244 (q4 c4) ∷
   rw⁻ 243 (q2 c4) ∷
   rw⁻ 242 (q2 c4) ∷
   rw⁻ 241 (q4 c4) ∷
   rw⁻ 240 (q5 c4) ∷
   rw⁻ 239 (q3 c4) ∷
   rw⁻ 238 (q4 c4) ∷
   rw⁻ 237 (q2 c4) ∷
   rw⁻ 236 (q2 c4) ∷
   rw⁻ 235 (q4 c4) ∷
   rw⁻ 234 (q3 c4) ∷
   rw⁻ 233 (q1 c4) ∷
   rw⁻ 232 (q2 c4) ∷
   rw⁻ 231 (q2 c4) ∷
   rw⁻ 230 (q1 c4) ∷
   rw⁻ 229 (q3 c4) ∷
   rw⁻ 228 (q4 c4) ∷
   rw⁻ 227 (q2 c4) ∷
   rw⁻ 226 (q2 c4) ∷
   rw⁻ 225 (q4 c4) ∷
   rw⁻ 224 (q3 c4) ∷
   rw⁻ 223 (q1 c4) ∷
   rw⁻ 222 (q5 c4) ∷
   rw⁻ 221 (q5 c4) ∷
   rw⁻ 220 (q1 c4) ∷
   rw⁻ 219 (q2 c4) ∷
   rw⁻ 218 (q2 c4) ∷
   rw⁻ 217 (q2 c4) ∷
   rw⁻ 216 (q3 c4) ∷
   rw⁻ 215 (q1 c4) ∷
   rw⁻ 214 (q5 c4) ∷
   rw⁻ 213 (q5 c4) ∷
   rw⁻ 212 (q1 c4) ∷
   rw⁻ 211 (q2 c4) ∷
   rw⁻ 210 (q6 c4) ∷
   rw⁻ 261 (q8 c4) ∷
   rw⁻ 260 (q9 c4) ∷
   rw⁻ 259 (q10 c4) ∷
   rw⁻ 258 (q9 c4) ∷ []) Eq.refl
