{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD139 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D139 (Sᴰ : SD139) where

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
  lem-F4-K3-I-at0440 : Ws → St 1864
  lem-F4-K3-I-at0440 = pickᴰ 8 Sᴰ
  lem-F4-K3-K1-at0440 : Ws → St 1865
  lem-F4-K3-K1-at0440 = pickᴰ 9 Sᴰ
  lem-F4-K3-K2-at0440 : Ws → St 1866
  lem-F4-K3-K2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K3-K3-at0440 : Ws → St 1871
  lem-F4-K3-K3-at0440 = pickᴰ 11 Sᴰ
  lem-F4-I-CS1-at0440 : Ws → St 1691
  lem-F4-I-CS1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 13 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 14 Sᴰ
  lem-F4-I-CS0-at0440 : Ws → St 1699
  lem-F4-I-CS0-at0440 = pickᴰ 15 Sᴰ
  lem-F4-K3-CS0-at0440 : Ws → St 1873
  lem-F4-K3-CS0-at0440 = pickᴰ 16 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1861
  lem-F4-K2-CS1-at0440 = pickᴰ 17 Sᴰ
  lem-F4-K3-CS2-at0440 : Ws → St 1869
  lem-F4-K3-CS2-at0440 = pickᴰ 18 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1856 (lem-F4-K2-CS2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1870 (lem-F4-K2-K3-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1862 (lem-F4-K2-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1850 (lem-F4-K2-K2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1861 (lem-F4-K2-CS1-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1849 (lem-F4-K2-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1699 (lem-F4-I-CS0-at0440 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1684 (lem-F4-I-K1-at0440 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1691 (lem-F4-I-CS1-at0440 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1873 (lem-F4-K3-CS0-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1864 (lem-F4-K3-I-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1865 (lem-F4-K3-K1-at0440 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1871 (lem-F4-K3-K3-at0440 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1869 (lem-F4-K3-CS2-at0440 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1866 (lem-F4-K3-K2-at0440 c4)

-- ckt-TST @0440 part47: 77 steps
lem-ckt-TST-at0440-part47 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与中俵临俭俭临上俵俵俵临俭俭临上主俵与临与俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵与主与俵临上主俵俵主上中上俊与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part47 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与中俵临俭俭临上俵俵俵临俭俭临上主俵与临与俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵与主与俵临上主俵俵主上中上俊与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 199 (q1 c4) ∷
   rw⁻ 198 (q2 c4) ∷
   rw⁻ 197 (q3 c4) ∷
   rw⁻ 196 (q4 c4) ∷
   rw⁻ 195 (q5 c4) ∷
   rw⁻ 194 (q5 c4) ∷
   rw⁻ 193 (q4 c4) ∷
   rw⁻ 192 (q1 c4) ∷
   rw⁻ 191 (q1 c4) ∷
   rw⁻ 190 (q1 c4) ∷
   rw⁻ 189 (q3 c4) ∷
   rw⁻ 188 (q4 c4) ∷
   rw⁻ 187 (q5 c4) ∷
   rw⁻ 186 (q5 c4) ∷
   rw⁻ 185 (q4 c4) ∷
   rw⁻ 184 (q1 c4) ∷
   rw⁻ 183 (q6 c4) ∷
   rw⁻ 234 (q7 c4) ∷
   rw⁻ 233 (q8 c4) ∷
   rw⁻ 232 (q9 c4) ∷
   rw⁻ 231 (q8 c4) ∷
   rw⁻ 230 (q10 c4) ∷
   rw⁻ 229 (q11 c4) ∷
   rw⁻ 228 (q11 c4) ∷
   rw⁻ 227 (q10 c4) ∷
   rw⁻ 226 (q8 c4) ∷
   rw⁻ 225 (q12 c4) ∷
   rw⁻ 224 (q11 c4) ∷
   rw⁻ 223 (q11 c4) ∷
   rw⁻ 222 (q12 c4) ∷
   rw⁻ 221 (q8 c4) ∷
   rw⁻ 220 (q10 c4) ∷
   rw⁻ 219 (q11 c4) ∷
   rw⁻ 218 (q11 c4) ∷
   rw⁻ 217 (q10 c4) ∷
   rw⁻ 216 (q13 c4) ∷
   rw⁻ 215 (q8 c4) ∷
   rw⁻ 214 (q10 c4) ∷
   rw⁻ 213 (q11 c4) ∷
   rw⁻ 212 (q11 c4) ∷
   rw⁻ 211 (q10 c4) ∷
   rw⁻ 210 (q8 c4) ∷
   rw⁻ 209 (q12 c4) ∷
   rw⁻ 208 (q11 c4) ∷
   rw⁻ 207 (q11 c4) ∷
   rw⁻ 206 (q12 c4) ∷
   rw⁻ 205 (q8 c4) ∷
   rw⁻ 204 (q10 c4) ∷
   rw⁻ 203 (q11 c4) ∷
   rw⁻ 202 (q11 c4) ∷
   rw⁻ 201 (q10 c4) ∷
   rw⁻ 200 (q8 c4) ∷
   rw⁻ 199 (q12 c4) ∷
   rw⁻ 198 (q13 c4) ∷
   rw⁻ 197 (q13 c4) ∷
   rw⁻ 196 (q12 c4) ∷
   rw⁻ 195 (q11 c4) ∷
   rw⁻ 194 (q11 c4) ∷
   rw⁻ 193 (q11 c4) ∷
   rw⁻ 192 (q8 c4) ∷
   rw⁻ 191 (q12 c4) ∷
   rw⁻ 190 (q13 c4) ∷
   rw⁻ 189 (q13 c4) ∷
   rw⁻ 188 (q12 c4) ∷
   rw⁻ 187 (q11 c4) ∷
   rw⁻ 186 (q9 c4) ∷
   rw⁻ 237 (q14 c4) ∷
   rw⁻ 236 (q15 c4) ∷
   rw⁻ 235 (q16 c4) ∷
   rw⁻ 234 (q15 c4) ∷
   rw⁻ 233 (q17 c4) ∷
   rw⁻ 232 (q18 c4) ∷
   rw⁻ 231 (q18 c4) ∷
   rw⁻ 230 (q17 c4) ∷
   rw⁻ 229 (q15 c4) ∷
   rw⁻ 228 (q19 c4) ∷
   rw⁻ 227 (q18 c4) ∷ []) Eq.refl
