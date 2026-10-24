{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD177 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D177 (Sᴰ : SD177) where

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
  lem-F4-K3-I-at0440 : Ws → St 1864
  lem-F4-K3-I-at0440 = pickᴰ 0 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1865
  lem-F4-K3-K1-at0440 = pickᴰ 1 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1866
  lem-F4-K3-K2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-K3-K3-at0440 : Ws → St 1871
  lem-F4-K3-K3-at0440 = pickᴰ 3 Sᴰ
  lem-F4-CS2-CS2-at0440 : Ws → St 1853
  lem-F4-CS2-CS2-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 5 Sᴰ
  lem-F4-CS2-K2-at0440 : Ws → St 1855
  lem-F4-CS2-K2-at0440 = pickᴰ 6 Sᴰ
  lem-F4-K3-CS1-at0440 : Ws → St 1867
  lem-F4-K3-CS1-at0440 = pickᴰ 7 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 8 Sᴰ
  lem-F4-CS2-CS1-at0440 : Ws → St 1860
  lem-F4-CS2-CS1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-CS2-K3-at0440 : Ws → St 1868
  lem-F4-CS2-K3-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS0-at0440 : Ws → St 1994
  lem-F4-CS2-CS0-at0440 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1866 (lem-F4-K3-K2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1864 (lem-F4-K3-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1871 (lem-F4-K3-K3-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1867 (lem-F4-K3-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1865 (lem-F4-K3-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1994 (lem-F4-CS2-CS0-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1868 (lem-F4-CS2-K3-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)

-- ckt-TST @0440 part48: 77 steps
lem-ckt-TST-at0440-part48 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵与主与俵临上主俵俵主上中上俊与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与中俵临俭俭临上俵俵俵与俵与临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part48 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵与主与俵临上主俵俵主上中上俊与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与中俵临俭俭临上俵俵俵与俵与临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 226 (q1 c4) ∷
   rw⁻ 225 (q2 c4) ∷
   rw⁻ 224 (q3 c4) ∷
   rw⁻ 223 (q4 c4) ∷
   rw⁻ 222 (q1 c4) ∷
   rw⁻ 221 (q1 c4) ∷
   rw⁻ 220 (q4 c4) ∷
   rw⁻ 219 (q5 c4) ∷
   rw⁻ 218 (q3 c4) ∷
   rw⁻ 217 (q4 c4) ∷
   rw⁻ 216 (q1 c4) ∷
   rw⁻ 215 (q1 c4) ∷
   rw⁻ 214 (q4 c4) ∷
   rw⁻ 213 (q3 c4) ∷
   rw⁻ 212 (q2 c4) ∷
   rw⁻ 211 (q1 c4) ∷
   rw⁻ 210 (q1 c4) ∷
   rw⁻ 209 (q2 c4) ∷
   rw⁻ 208 (q3 c4) ∷
   rw⁻ 207 (q4 c4) ∷
   rw⁻ 206 (q1 c4) ∷
   rw⁻ 205 (q1 c4) ∷
   rw⁻ 204 (q4 c4) ∷
   rw⁻ 203 (q3 c4) ∷
   rw⁻ 202 (q2 c4) ∷
   rw⁻ 201 (q5 c4) ∷
   rw⁻ 200 (q5 c4) ∷
   rw⁻ 199 (q2 c4) ∷
   rw⁻ 198 (q1 c4) ∷
   rw⁻ 197 (q1 c4) ∷
   rw⁻ 196 (q1 c4) ∷
   rw⁻ 195 (q3 c4) ∷
   rw⁻ 194 (q2 c4) ∷
   rw⁻ 193 (q5 c4) ∷
   rw⁻ 192 (q5 c4) ∷
   rw⁻ 191 (q2 c4) ∷
   rw⁻ 190 (q1 c4) ∷
   rw⁻ 189 (q6 c4) ∷
   rw⁻ 240 (q7 c4) ∷
   rw⁻ 239 (q8 c4) ∷
   rw⁻ 238 (q9 c4) ∷
   rw⁻ 237 (q8 c4) ∷
   rw⁻ 236 (q10 c4) ∷
   rw⁻ 235 (q11 c4) ∷
   rw⁻ 234 (q11 c4) ∷
   rw⁻ 233 (q10 c4) ∷
   rw⁻ 232 (q8 c4) ∷
   rw⁻ 231 (q12 c4) ∷
   rw⁻ 230 (q11 c4) ∷
   rw⁻ 229 (q11 c4) ∷
   rw⁻ 228 (q12 c4) ∷
   rw⁻ 227 (q8 c4) ∷
   rw⁻ 226 (q10 c4) ∷
   rw⁻ 225 (q11 c4) ∷
   rw⁻ 224 (q11 c4) ∷
   rw⁻ 223 (q10 c4) ∷
   rw⁻ 222 (q13 c4) ∷
   rw⁻ 221 (q8 c4) ∷
   rw⁻ 220 (q10 c4) ∷
   rw⁻ 219 (q11 c4) ∷
   rw⁻ 218 (q11 c4) ∷
   rw⁻ 217 (q10 c4) ∷
   rw⁻ 216 (q8 c4) ∷
   rw⁻ 215 (q12 c4) ∷
   rw⁻ 214 (q11 c4) ∷
   rw⁻ 213 (q11 c4) ∷
   rw⁻ 212 (q12 c4) ∷
   rw⁻ 211 (q8 c4) ∷
   rw⁻ 210 (q10 c4) ∷
   rw⁻ 209 (q11 c4) ∷
   rw⁻ 208 (q11 c4) ∷
   rw⁻ 207 (q10 c4) ∷
   rw⁻ 206 (q8 c4) ∷
   rw⁻ 205 (q12 c4) ∷
   rw⁻ 204 (q13 c4) ∷
   rw⁻ 203 (q13 c4) ∷
   rw⁻ 202 (q12 c4) ∷ []) Eq.refl
