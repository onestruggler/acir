{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD174 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D174 (Sᴰ : SD174) where

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
  q1 c4 = sE 1860 (lem-F4-CS2-CS1-at0440 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1854 (lem-F4-CS2-I-at0440 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1868 (lem-F4-CS2-K3-at0440 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1853 (lem-F4-CS2-CS2-at0440 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1855 (lem-F4-CS2-K2-at0440 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1857 (lem-F4-CS2-K1-at0440 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1994 (lem-F4-CS2-CS0-at0440 c4)

-- ckt-TST @0440 part43: 77 steps
lem-ckt-TST-at0440-part43 : Ws → ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭与俵与主俵俵主上临俵俵临上主俵俵主上中上俊与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ ≈ ⟪ (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与中俵临与俵与俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") ⟫ʷ
lem-ckt-TST-at0440-part43 c4 = derive (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭与俵与主俵俵主上临俵俵临上主俵俵主上中上俊与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上") (ℓ "与中与与俵与与临与与俭与与俭与与临与与上与与俵与与俵与与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与与中与与俵与与临与与俭与与俭与与临与与上与与俵与中俵临与俵与俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上俊与俵与与临与与俭与与俭与与临与与上与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与俭与与主与与俵与与俵与与主与与上与与临与与俵与与俵与与临与与上与与主与与俵与与俵与与主与与上与与中与与上与中俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上中上")
  (rw⁻ 195 (q1 c4) ∷
   rw⁻ 194 (q2 c4) ∷
   rw⁻ 193 (q3 c4) ∷
   rw⁻ 192 (q4 c4) ∷
   rw⁻ 191 (q4 c4) ∷
   rw⁻ 190 (q3 c4) ∷
   rw⁻ 189 (q2 c4) ∷
   rw⁻ 188 (q5 c4) ∷
   rw⁻ 187 (q4 c4) ∷
   rw⁻ 186 (q4 c4) ∷
   rw⁻ 185 (q5 c4) ∷
   rw⁻ 184 (q2 c4) ∷
   rw⁻ 183 (q3 c4) ∷
   rw⁻ 182 (q4 c4) ∷
   rw⁻ 181 (q4 c4) ∷
   rw⁻ 180 (q3 c4) ∷
   rw⁻ 179 (q2 c4) ∷
   rw⁻ 178 (q5 c4) ∷
   rw⁻ 177 (q1 c4) ∷
   rw⁻ 176 (q1 c4) ∷
   rw⁻ 175 (q5 c4) ∷
   rw⁻ 174 (q4 c4) ∷
   rw⁻ 173 (q4 c4) ∷
   rw⁻ 172 (q4 c4) ∷
   rw⁻ 171 (q2 c4) ∷
   rw⁻ 170 (q5 c4) ∷
   rw⁻ 169 (q1 c4) ∷
   rw⁻ 168 (q1 c4) ∷
   rw⁻ 167 (q5 c4) ∷
   rw⁻ 166 (q4 c4) ∷
   rw⁻ 165 (q6 c4) ∷
   rw⁻ 216 (q7 c4) ∷
   rw⁻ 215 (q2 c4) ∷
   rw⁻ 214 (q6 c4) ∷
   rw⁻ 213 (q2 c4) ∷
   rw⁻ 212 (q3 c4) ∷
   rw⁻ 211 (q4 c4) ∷
   rw⁻ 210 (q4 c4) ∷
   rw⁻ 209 (q3 c4) ∷
   rw⁻ 208 (q2 c4) ∷
   rw⁻ 207 (q5 c4) ∷
   rw⁻ 206 (q4 c4) ∷
   rw⁻ 205 (q4 c4) ∷
   rw⁻ 204 (q5 c4) ∷
   rw⁻ 203 (q2 c4) ∷
   rw⁻ 202 (q3 c4) ∷
   rw⁻ 201 (q4 c4) ∷
   rw⁻ 200 (q4 c4) ∷
   rw⁻ 199 (q3 c4) ∷
   rw⁻ 198 (q1 c4) ∷
   rw⁻ 197 (q2 c4) ∷
   rw⁻ 196 (q3 c4) ∷
   rw⁻ 195 (q4 c4) ∷
   rw⁻ 194 (q4 c4) ∷
   rw⁻ 193 (q3 c4) ∷
   rw⁻ 192 (q2 c4) ∷
   rw⁻ 191 (q5 c4) ∷
   rw⁻ 190 (q4 c4) ∷
   rw⁻ 189 (q4 c4) ∷
   rw⁻ 188 (q5 c4) ∷
   rw⁻ 187 (q2 c4) ∷
   rw⁻ 186 (q3 c4) ∷
   rw⁻ 185 (q4 c4) ∷
   rw⁻ 184 (q4 c4) ∷
   rw⁻ 183 (q3 c4) ∷
   rw⁻ 182 (q2 c4) ∷
   rw⁻ 181 (q5 c4) ∷
   rw⁻ 180 (q1 c4) ∷
   rw⁻ 179 (q1 c4) ∷
   rw⁻ 178 (q5 c4) ∷
   rw⁻ 177 (q4 c4) ∷
   rw⁻ 176 (q4 c4) ∷
   rw⁻ 175 (q4 c4) ∷
   rw⁻ 174 (q2 c4) ∷
   rw⁻ 173 (q5 c4) ∷
   rw⁻ 172 (q1 c4) ∷
   rw⁻ 171 (q1 c4) ∷ []) Eq.refl
