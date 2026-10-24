{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD089 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D089 (Sᴰ : SD089) where

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
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 0 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 1 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 2 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 3 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 4 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 5 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 6 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 7 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 8 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 9 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 10 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1590 (lem-F5-23 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1820 (lem-F4-CS2-CS1 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1576 (lem-F4-CS2-I c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q12 : Ws → Eqn
  q12 c4 = wlE 1419 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1618 (lem-F4-K3-I c4)

-- ckt-TST part13: 87 steps
lem-ckt-TST-part13 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並亄侬亇侧侧亇並亊並丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇並亊並侬侬亇丢亊侬侬亊丢侧亊侬侬亊一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-part13 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並亄侬亇侧侧亇並亊並丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇並亊並侬侬亇丢亊侬侬亊丢侧亊侬侬亊一丘乢乢丘一丞乢乢丞一丒一")
  (rw⁻ 291 (q1 c4) ∷
   rw⁻ 290 (q2 c4) ∷
   rw⁻ 289 (q2 c4) ∷
   rw⁻ 288 (q1 c4) ∷
   rw⁻ 287 (q3 c4) ∷
   rw⁻ 286 (q4 c4) ∷
   rw⁻ 321 (q5 c4) ∷
   rw⁻ 320 (q6 c4) ∷
   rw⁻ 319 (q7 c4) ∷
   rw⁻ 318 (q8 c4) ∷
   rw⁻ 317 (q6 c4) ∷
   rw⁻ 316 (q9 c4) ∷
   rw⁻ 315 (q9 c4) ∷
   rw⁻ 314 (q6 c4) ∷
   rw⁻ 313 (q8 c4) ∷
   rw⁻ 312 (q10 c4) ∷
   rw⁻ 311 (q9 c4) ∷
   rw⁻ 310 (q9 c4) ∷
   rw⁻ 309 (q10 c4) ∷
   rw⁻ 308 (q8 c4) ∷
   rw⁻ 307 (q6 c4) ∷
   rw⁻ 306 (q9 c4) ∷
   rw⁻ 305 (q9 c4) ∷
   rw⁻ 304 (q6 c4) ∷
   rw⁻ 303 (q8 c4) ∷
   rw⁻ 302 (q10 c4) ∷
   rw⁻ 301 (q7 c4) ∷
   rw⁻ 300 (q7 c4) ∷
   rw⁻ 299 (q10 c4) ∷
   rw⁻ 298 (q9 c4) ∷
   rw⁻ 297 (q9 c4) ∷
   rw⁻ 296 (q9 c4) ∷
   rw⁻ 295 (q8 c4) ∷
   rw⁻ 294 (q10 c4) ∷
   rw⁻ 293 (q7 c4) ∷
   rw⁻ 292 (q7 c4) ∷
   rw⁻ 291 (q10 c4) ∷
   rw⁻ 290 (q9 c4) ∷
   rw⁻ 289 (q11 c4) ∷
   rw⁻ 325 (q5 c4) ∷
   rw⁻ 324 (q9 c4) ∷
   rw⁻ 323 (q6 c4) ∷
   rw⁻ 322 (q7 c4) ∷
   rw⁻ 321 (q8 c4) ∷
   rw⁻ 320 (q6 c4) ∷
   rw⁻ 319 (q9 c4) ∷
   rw⁻ 318 (q9 c4) ∷
   rw⁻ 317 (q6 c4) ∷
   rw⁻ 316 (q8 c4) ∷
   rw⁻ 315 (q10 c4) ∷
   rw⁻ 314 (q9 c4) ∷
   rw⁻ 313 (q9 c4) ∷
   rw⁻ 312 (q10 c4) ∷
   rw⁻ 311 (q8 c4) ∷
   rw⁻ 310 (q6 c4) ∷
   rw⁻ 309 (q9 c4) ∷
   rw⁻ 308 (q9 c4) ∷
   rw⁻ 307 (q6 c4) ∷
   rw⁻ 306 (q8 c4) ∷
   rw⁻ 305 (q10 c4) ∷
   rw⁻ 304 (q7 c4) ∷
   rw⁻ 303 (q7 c4) ∷
   rw⁻ 302 (q10 c4) ∷
   rw⁻ 301 (q9 c4) ∷
   rw⁻ 300 (q9 c4) ∷
   rw⁻ 299 (q9 c4) ∷
   rw⁻ 298 (q8 c4) ∷
   rw⁻ 297 (q10 c4) ∷
   rw⁻ 296 (q7 c4) ∷
   rw⁻ 295 (q7 c4) ∷
   rw⁻ 294 (q10 c4) ∷
   rw⁻ 293 (q9 c4) ∷
   rw⁻ 292 (q11 c4) ∷
   rw 329 (q12 c4) ∷
   rw⁻ 328 (q3 c4) ∷
   rw⁻ 327 (q3 c4) ∷
   rw⁻ 326 (q13 c4) ∷
   rw⁻ 325 (q2 c4) ∷
   rw⁻ 324 (q14 c4) ∷
   rw⁻ 323 (q13 c4) ∷
   rw⁻ 322 (q3 c4) ∷
   rw⁻ 321 (q3 c4) ∷
   rw⁻ 320 (q13 c4) ∷
   rw⁻ 319 (q14 c4) ∷
   rw⁻ 318 (q1 c4) ∷
   rw⁻ 317 (q3 c4) ∷
   rw⁻ 316 (q3 c4) ∷ []) Eq.refl
