{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD088 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D088 (Sᴰ : SD088) where

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
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 4 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 5 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 6 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 7 Sᴰ
  lem-F4-CS1-I : Ws → St 1812
  lem-F4-CS1-I = pickᴰ 8 Sᴰ
  lem-F4-CS1-K1 : Ws → St 1813
  lem-F4-CS1-K1 = pickᴰ 9 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 10 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 11 Sᴰ
  lem-F4-CS1-CS1 : Ws → St 1814
  lem-F4-CS1-CS1 = pickᴰ 12 Sᴰ
  lem-F4-CS1-K3 : Ws → St 1821
  lem-F4-CS1-K3 = pickᴰ 13 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 15 Sᴰ
  lem-F5-12 : Ws → St 1816
  lem-F5-12 = pickᴰ 16 Sᴰ
  lem-F4-CS1-K2 : Ws → St 1817
  lem-F4-CS1-K2 = pickᴰ 17 Sᴰ
  lem-F4-CS1-CS2 : Ws → St 1819
  lem-F4-CS1-CS2 = pickᴰ 18 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 1411 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1411 (lem-F4-I-K3 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1386 (lem-F4-I-I c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1410 (lem-F4-I-K2 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1409 (lem-F4-I-K1 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1816 (lem-F5-12 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1812 (lem-F4-CS1-I c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1821 (lem-F4-CS1-K3 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1819 (lem-F4-CS1-CS2 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1817 (lem-F4-CS1-K2 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1814 (lem-F4-CS1-CS1 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1813 (lem-F4-CS1-K1 c4)
  q17 : Ws → Eqn
  q17 c4 = wlE 1419 (lit c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1618 (lem-F4-K3-I c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1650 (lem-F4-K3-K2 c4)

-- ckt-TST part12: 89 steps
lem-ckt-TST-part12 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬並亊並亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並亄侬亇侧侧亇並亊並丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-part12 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬並亊並亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並亄侬亇侧侧亇並亊並丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw⁻ 278 (q1 c4) ∷
   rw⁻ 277 (q2 c4) ∷
   rw⁻ 309 (q3 c4) ∷
   rw⁻ 308 (q4 c4) ∷
   rw⁻ 307 (q5 c4) ∷
   rw⁻ 306 (q5 c4) ∷
   rw⁻ 305 (q4 c4) ∷
   rw⁻ 304 (q6 c4) ∷
   rw⁻ 303 (q7 c4) ∷
   rw⁻ 302 (q5 c4) ∷
   rw⁻ 301 (q5 c4) ∷
   rw⁻ 300 (q7 c4) ∷
   rw⁻ 299 (q6 c4) ∷
   rw⁻ 298 (q4 c4) ∷
   rw⁻ 297 (q5 c4) ∷
   rw⁻ 296 (q5 c4) ∷
   rw⁻ 295 (q4 c4) ∷
   rw⁻ 294 (q6 c4) ∷
   rw⁻ 293 (q7 c4) ∷
   rw⁻ 292 (q8 c4) ∷
   rw⁻ 291 (q8 c4) ∷
   rw⁻ 290 (q7 c4) ∷
   rw⁻ 289 (q5 c4) ∷
   rw⁻ 288 (q5 c4) ∷
   rw⁻ 287 (q5 c4) ∷
   rw⁻ 286 (q6 c4) ∷
   rw⁻ 285 (q7 c4) ∷
   rw⁻ 284 (q8 c4) ∷
   rw⁻ 283 (q8 c4) ∷
   rw⁻ 282 (q7 c4) ∷
   rw⁻ 281 (q5 c4) ∷
   rw⁻ 280 (q9 c4) ∷
   rw⁻ 313 (q10 c4) ∷
   rw⁻ 312 (q11 c4) ∷
   rw⁻ 311 (q12 c4) ∷
   rw⁻ 310 (q13 c4) ∷
   rw⁻ 309 (q13 c4) ∷
   rw⁻ 308 (q12 c4) ∷
   rw⁻ 307 (q11 c4) ∷
   rw⁻ 306 (q14 c4) ∷
   rw⁻ 305 (q13 c4) ∷
   rw⁻ 304 (q13 c4) ∷
   rw⁻ 303 (q14 c4) ∷
   rw⁻ 302 (q11 c4) ∷
   rw⁻ 301 (q12 c4) ∷
   rw⁻ 300 (q13 c4) ∷
   rw⁻ 299 (q13 c4) ∷
   rw⁻ 298 (q12 c4) ∷
   rw⁻ 297 (q11 c4) ∷
   rw⁻ 296 (q14 c4) ∷
   rw⁻ 295 (q15 c4) ∷
   rw⁻ 294 (q15 c4) ∷
   rw⁻ 293 (q14 c4) ∷
   rw⁻ 292 (q13 c4) ∷
   rw⁻ 291 (q13 c4) ∷
   rw⁻ 290 (q13 c4) ∷
   rw⁻ 289 (q11 c4) ∷
   rw⁻ 288 (q14 c4) ∷
   rw⁻ 287 (q15 c4) ∷
   rw⁻ 286 (q15 c4) ∷
   rw⁻ 285 (q14 c4) ∷
   rw⁻ 284 (q13 c4) ∷
   rw⁻ 283 (q16 c4) ∷
   rw 317 (q17 c4) ∷
   rw⁻ 316 (q18 c4) ∷
   rw⁻ 315 (q19 c4) ∷
   rw⁻ 314 (q20 c4) ∷
   rw⁻ 313 (q1 c4) ∷
   rw⁻ 312 (q1 c4) ∷
   rw⁻ 311 (q20 c4) ∷
   rw⁻ 310 (q19 c4) ∷
   rw⁻ 309 (q21 c4) ∷
   rw⁻ 308 (q1 c4) ∷
   rw⁻ 307 (q1 c4) ∷
   rw⁻ 306 (q21 c4) ∷
   rw⁻ 305 (q19 c4) ∷
   rw⁻ 304 (q20 c4) ∷
   rw⁻ 303 (q1 c4) ∷
   rw⁻ 302 (q1 c4) ∷
   rw⁻ 301 (q20 c4) ∷
   rw⁻ 300 (q19 c4) ∷
   rw⁻ 299 (q21 c4) ∷
   rw⁻ 298 (q18 c4) ∷
   rw⁻ 297 (q18 c4) ∷
   rw⁻ 296 (q21 c4) ∷
   rw⁻ 295 (q1 c4) ∷
   rw⁻ 294 (q1 c4) ∷
   rw⁻ 293 (q1 c4) ∷
   rw⁻ 292 (q19 c4) ∷ []) Eq.refl
