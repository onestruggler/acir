{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD085 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D085 (Sᴰ : SD085) where

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
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 8 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 9 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 10 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 11 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 12 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 13 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 14 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1578
  lem-F4-K2-CS2 = pickᴰ 15 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 16 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 17 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 18 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 19 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 20 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 21 Sᴰ
  lem-F5-23 : Ws → St 1590
  lem-F5-23 = pickᴰ 22 Sᴰ
  lem-F4-K2-CS1 : Ws → St 1818
  lem-F4-K2-CS1 = pickᴰ 23 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 24 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1820 (lem-F4-CS2-CS1 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1590 (lem-F5-23 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1576 (lem-F4-CS2-I c4)
  q8 : Ws → Eqn
  q8 c4 = wlE 1419 (lit c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1618 (lem-F4-K3-I c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q15 : Ws → Eqn
  q15 c4 = wlE 1411 (lit c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1411 (lem-F4-I-K3 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1386 (lem-F4-I-I c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1410 (lem-F4-I-K2 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1409 (lem-F4-I-K1 c4)
  q22 : Ws → Eqn
  q22 c4 = wlE 1409 (lit c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1809 (lem-F4-K2-I c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1811 (lem-F4-K2-K3 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1578 (lem-F4-K2-CS2 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 1565 (lem-F4-K2-K2 c4)
  q27 : Ws → Eqn
  q27 c4 = sE 1818 (lem-F4-K2-CS1 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 1810 (lem-F4-K2-K1 c4)

-- ckt-TST part9: 99 steps
lem-ckt-TST-part9 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並亄侬亇侧侧亇並侬並丢侬侬侬亇侧侧亇丢亊侬乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並亄侬亇侧侧亇丢並侬並侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-part9 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並亄侬亇侧侧亇並侬並丢侬侬侬亇侧侧亇丢亊侬乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並亄侬亇侧侧亇丢並侬並侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw⁻ 246 (q1 c4) ∷
   rw⁻ 245 (q2 c4) ∷
   rw⁻ 244 (q2 c4) ∷
   rw⁻ 243 (q1 c4) ∷
   rw⁻ 242 (q3 c4) ∷
   rw⁻ 241 (q4 c4) ∷
   rw⁻ 261 (q5 c4) ∷
   rw⁻ 260 (q3 c4) ∷
   rw⁻ 259 (q6 c4) ∷
   rw⁻ 258 (q7 c4) ∷
   rw⁻ 257 (q1 c4) ∷
   rw⁻ 256 (q2 c4) ∷
   rw⁻ 255 (q2 c4) ∷
   rw⁻ 254 (q1 c4) ∷
   rw⁻ 253 (q3 c4) ∷
   rw⁻ 252 (q3 c4) ∷
   rw⁻ 251 (q3 c4) ∷
   rw⁻ 250 (q7 c4) ∷
   rw⁻ 249 (q1 c4) ∷
   rw⁻ 248 (q2 c4) ∷
   rw⁻ 247 (q2 c4) ∷
   rw⁻ 246 (q1 c4) ∷
   rw⁻ 245 (q3 c4) ∷
   rw⁻ 244 (q4 c4) ∷
   rw 265 (q8 c4) ∷
   rw⁻ 264 (q9 c4) ∷
   rw⁻ 263 (q9 c4) ∷
   rw⁻ 262 (q10 c4) ∷
   rw⁻ 261 (q11 c4) ∷
   rw⁻ 260 (q12 c4) ∷
   rw⁻ 259 (q13 c4) ∷
   rw⁻ 258 (q13 c4) ∷
   rw⁻ 257 (q12 c4) ∷
   rw⁻ 256 (q9 c4) ∷
   rw⁻ 255 (q9 c4) ∷
   rw⁻ 254 (q9 c4) ∷
   rw⁻ 253 (q11 c4) ∷
   rw⁻ 252 (q12 c4) ∷
   rw⁻ 251 (q13 c4) ∷
   rw⁻ 250 (q13 c4) ∷
   rw⁻ 249 (q12 c4) ∷
   rw⁻ 248 (q9 c4) ∷
   rw⁻ 247 (q14 c4) ∷
   rw⁻ 269 (q15 c4) ∷
   rw⁻ 268 (q16 c4) ∷
   rw⁻ 267 (q17 c4) ∷
   rw⁻ 266 (q17 c4) ∷
   rw⁻ 265 (q16 c4) ∷
   rw⁻ 264 (q18 c4) ∷
   rw⁻ 263 (q19 c4) ∷
   rw⁻ 262 (q20 c4) ∷
   rw⁻ 261 (q20 c4) ∷
   rw⁻ 260 (q19 c4) ∷
   rw⁻ 259 (q17 c4) ∷
   rw⁻ 258 (q17 c4) ∷
   rw⁻ 257 (q17 c4) ∷
   rw⁻ 256 (q18 c4) ∷
   rw⁻ 255 (q19 c4) ∷
   rw⁻ 254 (q20 c4) ∷
   rw⁻ 253 (q20 c4) ∷
   rw⁻ 252 (q19 c4) ∷
   rw⁻ 251 (q17 c4) ∷
   rw⁻ 250 (q21 c4) ∷
   rw 273 (q22 c4) ∷
   rw⁻ 272 (q23 c4) ∷
   rw⁻ 271 (q24 c4) ∷
   rw⁻ 270 (q25 c4) ∷
   rw⁻ 269 (q25 c4) ∷
   rw⁻ 268 (q24 c4) ∷
   rw⁻ 267 (q23 c4) ∷
   rw⁻ 266 (q26 c4) ∷
   rw⁻ 265 (q27 c4) ∷
   rw⁻ 264 (q27 c4) ∷
   rw⁻ 263 (q26 c4) ∷
   rw⁻ 262 (q25 c4) ∷
   rw⁻ 261 (q25 c4) ∷
   rw⁻ 260 (q25 c4) ∷
   rw⁻ 259 (q23 c4) ∷
   rw⁻ 258 (q26 c4) ∷
   rw⁻ 257 (q27 c4) ∷
   rw⁻ 256 (q27 c4) ∷
   rw⁻ 255 (q26 c4) ∷
   rw⁻ 254 (q25 c4) ∷
   rw⁻ 253 (q28 c4) ∷
   rw⁻ 277 (q5 c4) ∷
   rw⁻ 276 (q1 c4) ∷
   rw⁻ 275 (q7 c4) ∷
   rw⁻ 274 (q6 c4) ∷
   rw⁻ 273 (q3 c4) ∷
   rw⁻ 272 (q3 c4) ∷
   rw⁻ 271 (q6 c4) ∷
   rw⁻ 270 (q7 c4) ∷
   rw⁻ 269 (q1 c4) ∷
   rw⁻ 268 (q2 c4) ∷
   rw⁻ 267 (q2 c4) ∷
   rw⁻ 266 (q1 c4) ∷
   rw⁻ 265 (q3 c4) ∷
   rw⁻ 264 (q3 c4) ∷
   rw⁻ 263 (q3 c4) ∷ []) Eq.refl
