{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD159 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D159 (Sᴰ : SD159) where

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
  lem-F4-I-I : Ws → St 1386
  lem-F4-I-I = pickᴰ 0 Sᴰ
  lem-F4-I-K1 : Ws → St 1409
  lem-F4-I-K1 = pickᴰ 1 Sᴰ
  lem-F4-I-K2 : Ws → St 1410
  lem-F4-I-K2 = pickᴰ 2 Sᴰ
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 3 Sᴰ
  lem-F4-K2-I : Ws → St 1809
  lem-F4-K2-I = pickᴰ 4 Sᴰ
  lem-F4-K2-K1 : Ws → St 1810
  lem-F4-K2-K1 = pickᴰ 5 Sᴰ
  lem-F4-K2-K2 : Ws → St 1565
  lem-F4-K2-K2 = pickᴰ 6 Sᴰ
  lem-F4-K2-K3 : Ws → St 1811
  lem-F4-K2-K3 = pickᴰ 7 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 8 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 9 Sᴰ
  lem-F4-I-CS0 : Ws → St 1401
  lem-F4-I-CS0 = pickᴰ 10 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 11 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 12 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1578
  lem-F4-K2-CS2 = pickᴰ 13 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 15 Sᴰ
  lem-F4-K2-CS1 : Ws → St 1818
  lem-F4-K2-CS1 = pickᴰ 16 Sᴰ
  lem-F4-K2-CS0 : Ws → St 1987
  lem-F4-K2-CS0 = pickᴰ 17 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1401 (lem-F4-I-CS0 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1386 (lem-F4-I-I c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1409 (lem-F4-I-K1 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1411 (lem-F4-I-K3 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1410 (lem-F4-I-K2 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1987 (lem-F4-K2-CS0 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1809 (lem-F4-K2-I c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1810 (lem-F4-K2-K1 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1811 (lem-F4-K2-K3 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1578 (lem-F4-K2-CS2 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1565 (lem-F4-K2-K2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1818 (lem-F4-K2-CS1 c4)

-- ckt-TST part33: 77 steps
lem-ckt-TST-part33 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧並亊並亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊並亇並侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part33 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧並亊並亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊並亇並侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw⁻ 202 (q1 c4) ∷
   rw⁻ 201 (q1 c4) ∷
   rw⁻ 200 (q2 c4) ∷
   rw⁻ 199 (q3 c4) ∷
   rw⁻ 198 (q4 c4) ∷
   rw⁻ 249 (q5 c4) ∷
   rw⁻ 248 (q6 c4) ∷
   rw⁻ 247 (q7 c4) ∷
   rw⁻ 246 (q6 c4) ∷
   rw⁻ 245 (q8 c4) ∷
   rw⁻ 244 (q9 c4) ∷
   rw⁻ 243 (q9 c4) ∷
   rw⁻ 242 (q8 c4) ∷
   rw⁻ 241 (q6 c4) ∷
   rw⁻ 240 (q10 c4) ∷
   rw⁻ 239 (q9 c4) ∷
   rw⁻ 238 (q9 c4) ∷
   rw⁻ 237 (q10 c4) ∷
   rw⁻ 236 (q6 c4) ∷
   rw⁻ 235 (q8 c4) ∷
   rw⁻ 234 (q9 c4) ∷
   rw⁻ 233 (q9 c4) ∷
   rw⁻ 232 (q8 c4) ∷
   rw⁻ 231 (q11 c4) ∷
   rw⁻ 230 (q6 c4) ∷
   rw⁻ 229 (q8 c4) ∷
   rw⁻ 228 (q9 c4) ∷
   rw⁻ 227 (q9 c4) ∷
   rw⁻ 226 (q8 c4) ∷
   rw⁻ 225 (q6 c4) ∷
   rw⁻ 224 (q10 c4) ∷
   rw⁻ 223 (q9 c4) ∷
   rw⁻ 222 (q9 c4) ∷
   rw⁻ 221 (q10 c4) ∷
   rw⁻ 220 (q6 c4) ∷
   rw⁻ 219 (q8 c4) ∷
   rw⁻ 218 (q9 c4) ∷
   rw⁻ 217 (q9 c4) ∷
   rw⁻ 216 (q8 c4) ∷
   rw⁻ 215 (q6 c4) ∷
   rw⁻ 214 (q10 c4) ∷
   rw⁻ 213 (q11 c4) ∷
   rw⁻ 212 (q11 c4) ∷
   rw⁻ 211 (q10 c4) ∷
   rw⁻ 210 (q9 c4) ∷
   rw⁻ 209 (q9 c4) ∷
   rw⁻ 208 (q9 c4) ∷
   rw⁻ 207 (q6 c4) ∷
   rw⁻ 206 (q10 c4) ∷
   rw⁻ 205 (q11 c4) ∷
   rw⁻ 204 (q11 c4) ∷
   rw⁻ 203 (q10 c4) ∷
   rw⁻ 202 (q9 c4) ∷
   rw⁻ 201 (q7 c4) ∷
   rw⁻ 252 (q12 c4) ∷
   rw⁻ 251 (q13 c4) ∷
   rw⁻ 250 (q14 c4) ∷
   rw⁻ 249 (q13 c4) ∷
   rw⁻ 248 (q15 c4) ∷
   rw⁻ 247 (q16 c4) ∷
   rw⁻ 246 (q16 c4) ∷
   rw⁻ 245 (q15 c4) ∷
   rw⁻ 244 (q13 c4) ∷
   rw⁻ 243 (q17 c4) ∷
   rw⁻ 242 (q16 c4) ∷
   rw⁻ 241 (q16 c4) ∷
   rw⁻ 240 (q17 c4) ∷
   rw⁻ 239 (q13 c4) ∷
   rw⁻ 238 (q15 c4) ∷
   rw⁻ 237 (q16 c4) ∷
   rw⁻ 236 (q16 c4) ∷
   rw⁻ 235 (q15 c4) ∷
   rw⁻ 234 (q18 c4) ∷
   rw⁻ 233 (q13 c4) ∷
   rw⁻ 232 (q15 c4) ∷
   rw⁻ 231 (q16 c4) ∷
   rw⁻ 230 (q16 c4) ∷ []) Eq.refl
