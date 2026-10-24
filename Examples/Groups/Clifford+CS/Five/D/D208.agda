{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD208 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D208 (Sᴰ : SD208) where

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
  lem-F4-K2-K2-at0440 : Ws → St 1850
  lem-F4-K2-K2-at0440 = pickᴰ 2 Sᴰ
  lem-F4-K2-K3-at0440 : Ws → St 1870
  lem-F4-K2-K3-at0440 = pickᴰ 3 Sᴰ
  lem-F4-CS1-CS1-at0440 : Ws → St 1851
  lem-F4-CS1-CS1-at0440 = pickᴰ 4 Sᴰ
  lem-F4-CS1-I-at0440 : Ws → St 1863
  lem-F4-CS1-I-at0440 = pickᴰ 5 Sᴰ
  lem-F4-CS1-K1-at0440 : Ws → St 1852
  lem-F4-CS1-K1-at0440 = pickᴰ 6 Sᴰ
  lem-F4-CS1-K3-at0440 : Ws → St 1872
  lem-F4-CS1-K3-at0440 = pickᴰ 7 Sᴰ
  lem-F4-K2-CS2-at0440 : Ws → St 1856
  lem-F4-K2-CS2-at0440 = pickᴰ 8 Sᴰ
  lem-F4-CS1-K2-at0440 : Ws → St 1858
  lem-F4-CS1-K2-at0440 = pickᴰ 9 Sᴰ
  lem-F4-CS1-CS2-at0440 : Ws → St 1859
  lem-F4-CS1-CS2-at0440 = pickᴰ 10 Sᴰ
  lem-F4-K2-CS1-at0440 : Ws → St 1861
  lem-F4-K2-CS1-at0440 = pickᴰ 11 Sᴰ
  lem-F4-CS1-CS0-at0440 : Ws → St 2126
  lem-F4-CS1-CS0-at0440 = pickᴰ 12 Sᴰ

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

-- ckt-TST @0440 part40: 77 steps
lem-ckt-TST-at0440-part40 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵与临与俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵与俭与俵临上主俵俵主上中上俊与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part40 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与中俵临俭俭临上俵俵俵临俭俭临上主俵与临与俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵与俭与俵临上主俵俵主上中上俊与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 166 (q1 c4) ∷
   rw⁻ 165 (q2 c4) ∷
   rw⁻ 164 (q3 c4) ∷
   rw⁻ 163 (q4 c4) ∷
   rw⁻ 162 (q5 c4) ∷
   rw⁻ 161 (q5 c4) ∷
   rw⁻ 160 (q4 c4) ∷
   rw⁻ 159 (q1 c4) ∷
   rw⁻ 158 (q1 c4) ∷
   rw⁻ 157 (q1 c4) ∷
   rw⁻ 156 (q3 c4) ∷
   rw⁻ 155 (q4 c4) ∷
   rw⁻ 154 (q5 c4) ∷
   rw⁻ 153 (q5 c4) ∷
   rw⁻ 152 (q4 c4) ∷
   rw⁻ 151 (q1 c4) ∷
   rw⁻ 150 (q6 c4) ∷
   rw⁻ 201 (q7 c4) ∷
   rw⁻ 200 (q8 c4) ∷
   rw⁻ 199 (q9 c4) ∷
   rw⁻ 198 (q8 c4) ∷
   rw⁻ 197 (q10 c4) ∷
   rw⁻ 196 (q11 c4) ∷
   rw⁻ 195 (q11 c4) ∷
   rw⁻ 194 (q10 c4) ∷
   rw⁻ 193 (q8 c4) ∷
   rw⁻ 192 (q12 c4) ∷
   rw⁻ 191 (q11 c4) ∷
   rw⁻ 190 (q11 c4) ∷
   rw⁻ 189 (q12 c4) ∷
   rw⁻ 188 (q8 c4) ∷
   rw⁻ 187 (q10 c4) ∷
   rw⁻ 186 (q11 c4) ∷
   rw⁻ 185 (q11 c4) ∷
   rw⁻ 184 (q10 c4) ∷
   rw⁻ 183 (q13 c4) ∷
   rw⁻ 182 (q8 c4) ∷
   rw⁻ 181 (q10 c4) ∷
   rw⁻ 180 (q11 c4) ∷
   rw⁻ 179 (q11 c4) ∷
   rw⁻ 178 (q10 c4) ∷
   rw⁻ 177 (q8 c4) ∷
   rw⁻ 176 (q12 c4) ∷
   rw⁻ 175 (q11 c4) ∷
   rw⁻ 174 (q11 c4) ∷
   rw⁻ 173 (q12 c4) ∷
   rw⁻ 172 (q8 c4) ∷
   rw⁻ 171 (q10 c4) ∷
   rw⁻ 170 (q11 c4) ∷
   rw⁻ 169 (q11 c4) ∷
   rw⁻ 168 (q10 c4) ∷
   rw⁻ 167 (q8 c4) ∷
   rw⁻ 166 (q12 c4) ∷
   rw⁻ 165 (q13 c4) ∷
   rw⁻ 164 (q13 c4) ∷
   rw⁻ 163 (q12 c4) ∷
   rw⁻ 162 (q11 c4) ∷
   rw⁻ 161 (q11 c4) ∷
   rw⁻ 160 (q11 c4) ∷
   rw⁻ 159 (q8 c4) ∷
   rw⁻ 158 (q12 c4) ∷
   rw⁻ 157 (q13 c4) ∷
   rw⁻ 156 (q13 c4) ∷
   rw⁻ 155 (q12 c4) ∷
   rw⁻ 154 (q11 c4) ∷
   rw⁻ 153 (q9 c4) ∷
   rw⁻ 204 (q7 c4) ∷
   rw⁻ 203 (q8 c4) ∷
   rw⁻ 202 (q9 c4) ∷
   rw⁻ 201 (q8 c4) ∷
   rw⁻ 200 (q10 c4) ∷
   rw⁻ 199 (q11 c4) ∷
   rw⁻ 198 (q11 c4) ∷
   rw⁻ 197 (q10 c4) ∷
   rw⁻ 196 (q8 c4) ∷
   rw⁻ 195 (q12 c4) ∷
   rw⁻ 194 (q11 c4) ∷ []) Eq.refl
