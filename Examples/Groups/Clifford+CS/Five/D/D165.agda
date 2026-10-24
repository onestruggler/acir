{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD165 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D165 (Sᴰ : SD165) where

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
  lem-F4-K2-K3 : Ws → St 1811
  lem-F4-K2-K3 = pickᴰ 6 Sᴰ
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 7 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 8 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 9 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 10 Sᴰ
  lem-F4-I-CS0 : Ws → St 1401
  lem-F4-I-CS0 = pickᴰ 11 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 12 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 13 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1578
  lem-F4-K2-CS2 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 15 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 16 Sᴰ
  lem-F4-K2-CS0 : Ws → St 1987
  lem-F4-K2-CS0 = pickᴰ 17 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1618 (lem-F4-K3-I c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1401 (lem-F4-I-CS0 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1386 (lem-F4-I-I c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1409 (lem-F4-I-K1 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1411 (lem-F4-I-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1410 (lem-F4-I-K2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1987 (lem-F4-K2-CS0 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1809 (lem-F4-K2-I c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1810 (lem-F4-K2-K1 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1811 (lem-F4-K2-K3 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1578 (lem-F4-K2-CS2 c4)

-- ckt-TST part43: 77 steps
lem-ckt-TST-part43 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊並亊並丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇並亇並丢亊侬侬亊丢亄丢俄並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part43 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊並亊並丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇並亇並丢亊侬侬亊丢亄丢俄並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw⁻ 264 (q1 c4) ∷
   rw⁻ 263 (q2 c4) ∷
   rw⁻ 262 (q2 c4) ∷
   rw⁻ 261 (q1 c4) ∷
   rw⁻ 260 (q3 c4) ∷
   rw⁻ 259 (q4 c4) ∷
   rw⁻ 258 (q5 c4) ∷
   rw⁻ 257 (q5 c4) ∷
   rw⁻ 256 (q4 c4) ∷
   rw⁻ 255 (q2 c4) ∷
   rw⁻ 254 (q2 c4) ∷
   rw⁻ 253 (q2 c4) ∷
   rw⁻ 252 (q3 c4) ∷
   rw⁻ 251 (q4 c4) ∷
   rw⁻ 250 (q5 c4) ∷
   rw⁻ 249 (q5 c4) ∷
   rw⁻ 248 (q4 c4) ∷
   rw⁻ 247 (q2 c4) ∷
   rw⁻ 246 (q6 c4) ∷
   rw⁻ 297 (q7 c4) ∷
   rw⁻ 296 (q8 c4) ∷
   rw⁻ 295 (q9 c4) ∷
   rw⁻ 294 (q8 c4) ∷
   rw⁻ 293 (q10 c4) ∷
   rw⁻ 292 (q11 c4) ∷
   rw⁻ 291 (q11 c4) ∷
   rw⁻ 290 (q10 c4) ∷
   rw⁻ 289 (q8 c4) ∷
   rw⁻ 288 (q12 c4) ∷
   rw⁻ 287 (q11 c4) ∷
   rw⁻ 286 (q11 c4) ∷
   rw⁻ 285 (q12 c4) ∷
   rw⁻ 284 (q8 c4) ∷
   rw⁻ 283 (q10 c4) ∷
   rw⁻ 282 (q11 c4) ∷
   rw⁻ 281 (q11 c4) ∷
   rw⁻ 280 (q10 c4) ∷
   rw⁻ 279 (q13 c4) ∷
   rw⁻ 278 (q8 c4) ∷
   rw⁻ 277 (q10 c4) ∷
   rw⁻ 276 (q11 c4) ∷
   rw⁻ 275 (q11 c4) ∷
   rw⁻ 274 (q10 c4) ∷
   rw⁻ 273 (q8 c4) ∷
   rw⁻ 272 (q12 c4) ∷
   rw⁻ 271 (q11 c4) ∷
   rw⁻ 270 (q11 c4) ∷
   rw⁻ 269 (q12 c4) ∷
   rw⁻ 268 (q8 c4) ∷
   rw⁻ 267 (q10 c4) ∷
   rw⁻ 266 (q11 c4) ∷
   rw⁻ 265 (q11 c4) ∷
   rw⁻ 264 (q10 c4) ∷
   rw⁻ 263 (q8 c4) ∷
   rw⁻ 262 (q12 c4) ∷
   rw⁻ 261 (q13 c4) ∷
   rw⁻ 260 (q13 c4) ∷
   rw⁻ 259 (q12 c4) ∷
   rw⁻ 258 (q11 c4) ∷
   rw⁻ 257 (q11 c4) ∷
   rw⁻ 256 (q11 c4) ∷
   rw⁻ 255 (q8 c4) ∷
   rw⁻ 254 (q12 c4) ∷
   rw⁻ 253 (q13 c4) ∷
   rw⁻ 252 (q13 c4) ∷
   rw⁻ 251 (q12 c4) ∷
   rw⁻ 250 (q11 c4) ∷
   rw⁻ 249 (q9 c4) ∷
   rw⁻ 300 (q14 c4) ∷
   rw⁻ 299 (q15 c4) ∷
   rw⁻ 298 (q16 c4) ∷
   rw⁻ 297 (q15 c4) ∷
   rw⁻ 296 (q17 c4) ∷
   rw⁻ 295 (q18 c4) ∷
   rw⁻ 294 (q18 c4) ∷
   rw⁻ 293 (q17 c4) ∷
   rw⁻ 292 (q15 c4) ∷ []) Eq.refl
