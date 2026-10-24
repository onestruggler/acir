{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD169 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D169 (Sᴰ : SD169) where

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
  lem-nat-S-at0410213243 : Ws → St 1988
  lem-nat-S-at0410213243 = pickᴰ 1 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 2 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 3 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 4 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 5 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 6 Sᴰ
  lem-F4-K3-CS0 : Ws → St 1654
  lem-F4-K3-CS0 = pickᴰ 7 Sᴰ
  lem-L-CCZ-1-at0440-part2 : Ws → St 1989
  lem-L-CCZ-1-at0440-part2 = pickᴰ 8 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 9 Sᴰ
  lem-L-CCZ-1-at0440-part1 : Ws → St 1990
  lem-L-CCZ-1-at0440-part1 = pickᴰ 10 Sᴰ
  lem-L-CCZ-1-at0440-part3 : Ws → St 1991
  lem-L-CCZ-1-at0440-part3 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS0 : Ws → St 1986
  lem-F4-CS2-CS0 = pickᴰ 12 Sᴰ
  lem-SW-S-at0410213243 : Ws → St 1992
  lem-SW-S-at0410213243 = pickᴰ 13 Sᴰ
  lem-L-CCZ-1-at0440-part0 : Ws → St 1993
  lem-L-CCZ-1-at0440-part0 = pickᴰ 14 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1576 (lem-F4-CS2-I c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1820 (lem-F4-CS2-CS1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1986 (lem-F4-CS2-CS0 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1654 (lem-F4-K3-CS0 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1618 (lem-F4-K3-I c4)

-- ckt-TST part48: 77 steps
lem-ckt-TST-part48 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊並侬並侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄並亊並丢俄並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part48 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊並侬並侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄並亊並丢俄並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw⁻ 295 (q1 c4) ∷
   rw⁻ 294 (q2 c4) ∷
   rw⁻ 293 (q3 c4) ∷
   rw⁻ 292 (q4 c4) ∷
   rw⁻ 291 (q4 c4) ∷
   rw⁻ 290 (q3 c4) ∷
   rw⁻ 289 (q2 c4) ∷
   rw⁻ 288 (q1 c4) ∷
   rw⁻ 287 (q4 c4) ∷
   rw⁻ 286 (q4 c4) ∷
   rw⁻ 285 (q1 c4) ∷
   rw⁻ 284 (q2 c4) ∷
   rw⁻ 283 (q3 c4) ∷
   rw⁻ 282 (q5 c4) ∷
   rw⁻ 281 (q5 c4) ∷
   rw⁻ 280 (q3 c4) ∷
   rw⁻ 279 (q4 c4) ∷
   rw⁻ 278 (q4 c4) ∷
   rw⁻ 277 (q4 c4) ∷
   rw⁻ 276 (q2 c4) ∷
   rw⁻ 275 (q3 c4) ∷
   rw⁻ 274 (q5 c4) ∷
   rw⁻ 273 (q5 c4) ∷
   rw⁻ 272 (q3 c4) ∷
   rw⁻ 271 (q4 c4) ∷
   rw⁻ 270 (q6 c4) ∷
   rw⁻ 321 (q7 c4) ∷
   rw⁻ 320 (q2 c4) ∷
   rw⁻ 319 (q6 c4) ∷
   rw⁻ 318 (q2 c4) ∷
   rw⁻ 317 (q1 c4) ∷
   rw⁻ 316 (q4 c4) ∷
   rw⁻ 315 (q4 c4) ∷
   rw⁻ 314 (q1 c4) ∷
   rw⁻ 313 (q2 c4) ∷
   rw⁻ 312 (q3 c4) ∷
   rw⁻ 311 (q4 c4) ∷
   rw⁻ 310 (q4 c4) ∷
   rw⁻ 309 (q3 c4) ∷
   rw⁻ 308 (q2 c4) ∷
   rw⁻ 307 (q1 c4) ∷
   rw⁻ 306 (q4 c4) ∷
   rw⁻ 305 (q4 c4) ∷
   rw⁻ 304 (q1 c4) ∷
   rw⁻ 303 (q5 c4) ∷
   rw⁻ 302 (q2 c4) ∷
   rw⁻ 301 (q1 c4) ∷
   rw⁻ 300 (q4 c4) ∷
   rw⁻ 299 (q4 c4) ∷
   rw⁻ 298 (q1 c4) ∷
   rw⁻ 297 (q2 c4) ∷
   rw⁻ 296 (q3 c4) ∷
   rw⁻ 295 (q4 c4) ∷
   rw⁻ 294 (q4 c4) ∷
   rw⁻ 293 (q3 c4) ∷
   rw⁻ 292 (q2 c4) ∷
   rw⁻ 291 (q1 c4) ∷
   rw⁻ 290 (q4 c4) ∷
   rw⁻ 289 (q4 c4) ∷
   rw⁻ 288 (q1 c4) ∷
   rw⁻ 287 (q2 c4) ∷
   rw⁻ 286 (q3 c4) ∷
   rw⁻ 285 (q5 c4) ∷
   rw⁻ 284 (q5 c4) ∷
   rw⁻ 283 (q3 c4) ∷
   rw⁻ 282 (q4 c4) ∷
   rw⁻ 281 (q4 c4) ∷
   rw⁻ 280 (q4 c4) ∷
   rw⁻ 279 (q2 c4) ∷
   rw⁻ 278 (q3 c4) ∷
   rw⁻ 277 (q5 c4) ∷
   rw⁻ 276 (q5 c4) ∷
   rw⁻ 275 (q3 c4) ∷
   rw⁻ 274 (q4 c4) ∷
   rw⁻ 273 (q6 c4) ∷
   rw⁻ 324 (q8 c4) ∷
   rw⁻ 323 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = wlE 3 (lit c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1992 (lem-SW-S-at0410213243 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1988 (lem-nat-S-at0410213243 c4)

-- F0 @0410213243: 3 steps
lem-F0-at0410213243 : Ws → ⟪ (ℓ "俊") ⟫ʷ ≈ ⟪ (ℓ "俟") ⟫ʷ
lem-F0-at0410213243 c4 = derive (ℓ "俊") (ℓ "俟")
  (rw⁻ 0 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 0 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = sE 1993 (lem-L-CCZ-1-at0440-part0 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1990 (lem-L-CCZ-1-at0440-part1 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1989 (lem-L-CCZ-1-at0440-part2 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1991 (lem-L-CCZ-1-at0440-part3 c4)

-- L-CCZ-1 @0440: 4 steps
lem-L-CCZ-1-at0440 : Ws → ⟪ (ℓ "俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-L-CCZ-1-at0440 c4 = derive (ℓ "俵临俭俭临上俵俵俵临俭俭临上主俵俵主上临俵俵临上主俵俵主上俭主俵俵主上临俵俵临上主俵俵主上") (ℓ "侔")
  (rw 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷
   rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl
