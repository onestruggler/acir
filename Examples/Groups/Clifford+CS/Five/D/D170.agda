{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD170 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D170 (Sᴰ : SD170) where

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
  lem-F4-CS2-I-at0440 : Ws → St 1854
  lem-F4-CS2-I-at0440 = pickᴰ 10 Sᴰ
  lem-F4-I-CS2-at0440 : Ws → St 1693
  lem-F4-I-CS2-at0440 = pickᴰ 11 Sᴰ
  lem-F4-CS2-K1-at0440 : Ws → St 1857
  lem-F4-CS2-K1-at0440 = pickᴰ 12 Sᴰ
  lem-F4-K1-CS0-at0440 : Ws → St 1695
  lem-F4-K1-CS0-at0440 = pickᴰ 13 Sᴰ
  lem-F4-K1-CS2-at0440 : Ws → St 1694
  lem-F4-K1-CS2-at0440 = pickᴰ 14 Sᴰ
  lem-F4-CS2-CS0-at0440 : Ws → St 1994
  lem-F4-CS2-CS0-at0440 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1685 (lem-F4-I-K2-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1693 (lem-F4-I-CS2-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1683 (lem-F4-I-I-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1686 (lem-F4-I-K3-at0440 c4)
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
  q14 : Ws → Eqn
  q14 c4 = sE 1994 (lem-F4-CS2-CS0-at0440 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)

-- ckt-TST @0440 part38: 77 steps
lem-ckt-TST-at0440-part38 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临与上与上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主与俵与上中上俊与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part38 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临与上与上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主与俵与上中上俊与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 357 (q1 c4) ∷
   rw⁻ 356 (q2 c4) ∷
   rw⁻ 355 (q2 c4) ∷
   rw⁻ 354 (q1 c4) ∷
   rw⁻ 353 (q3 c4) ∷
   rw⁻ 352 (q4 c4) ∷
   rw⁻ 351 (q2 c4) ∷
   rw⁻ 350 (q2 c4) ∷
   rw⁻ 349 (q4 c4) ∷
   rw⁻ 348 (q3 c4) ∷
   rw⁻ 347 (q1 c4) ∷
   rw⁻ 346 (q5 c4) ∷
   rw⁻ 345 (q5 c4) ∷
   rw⁻ 344 (q1 c4) ∷
   rw⁻ 343 (q2 c4) ∷
   rw⁻ 342 (q2 c4) ∷
   rw⁻ 341 (q2 c4) ∷
   rw⁻ 340 (q3 c4) ∷
   rw⁻ 339 (q1 c4) ∷
   rw⁻ 338 (q5 c4) ∷
   rw⁻ 337 (q5 c4) ∷
   rw⁻ 336 (q1 c4) ∷
   rw⁻ 335 (q2 c4) ∷
   rw⁻ 334 (q6 c4) ∷
   rw⁻ 192 (q7 c4) ∷
   rw⁻ 191 (q8 c4) ∷
   rw⁻ 190 (q9 c4) ∷
   rw⁻ 189 (q8 c4) ∷
   rw⁻ 188 (q10 c4) ∷
   rw⁻ 187 (q11 c4) ∷
   rw⁻ 186 (q11 c4) ∷
   rw⁻ 185 (q10 c4) ∷
   rw⁻ 184 (q8 c4) ∷
   rw⁻ 183 (q12 c4) ∷
   rw⁻ 182 (q11 c4) ∷
   rw⁻ 181 (q11 c4) ∷
   rw⁻ 180 (q12 c4) ∷
   rw⁻ 179 (q8 c4) ∷
   rw⁻ 178 (q10 c4) ∷
   rw⁻ 177 (q11 c4) ∷
   rw⁻ 176 (q11 c4) ∷
   rw⁻ 175 (q10 c4) ∷
   rw⁻ 174 (q13 c4) ∷
   rw⁻ 173 (q8 c4) ∷
   rw⁻ 172 (q10 c4) ∷
   rw⁻ 171 (q11 c4) ∷
   rw⁻ 170 (q11 c4) ∷
   rw⁻ 169 (q10 c4) ∷
   rw⁻ 168 (q8 c4) ∷
   rw⁻ 167 (q12 c4) ∷
   rw⁻ 166 (q11 c4) ∷
   rw⁻ 165 (q11 c4) ∷
   rw⁻ 164 (q12 c4) ∷
   rw⁻ 163 (q8 c4) ∷
   rw⁻ 162 (q10 c4) ∷
   rw⁻ 161 (q11 c4) ∷
   rw⁻ 160 (q11 c4) ∷
   rw⁻ 159 (q10 c4) ∷
   rw⁻ 158 (q8 c4) ∷
   rw⁻ 157 (q12 c4) ∷
   rw⁻ 156 (q13 c4) ∷
   rw⁻ 155 (q13 c4) ∷
   rw⁻ 154 (q12 c4) ∷
   rw⁻ 153 (q11 c4) ∷
   rw⁻ 152 (q11 c4) ∷
   rw⁻ 151 (q11 c4) ∷
   rw⁻ 150 (q8 c4) ∷
   rw⁻ 149 (q12 c4) ∷
   rw⁻ 148 (q13 c4) ∷
   rw⁻ 147 (q13 c4) ∷
   rw⁻ 146 (q12 c4) ∷
   rw⁻ 145 (q11 c4) ∷
   rw⁻ 144 (q9 c4) ∷
   rw⁻ 195 (q14 c4) ∷
   rw⁻ 194 (q15 c4) ∷
   rw⁻ 193 (q16 c4) ∷
   rw⁻ 192 (q15 c4) ∷ []) Eq.refl
