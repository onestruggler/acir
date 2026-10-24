{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD167 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D167 (Sᴰ : SD167) where

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
  lem-F4-K2-I : Ws → St 1809
  lem-F4-K2-I = pickᴰ 0 Sᴰ
  lem-F4-K2-K1 : Ws → St 1810
  lem-F4-K2-K1 = pickᴰ 1 Sᴰ
  lem-F4-K2-K2 : Ws → St 1565
  lem-F4-K2-K2 = pickᴰ 2 Sᴰ
  lem-F4-K2-K3 : Ws → St 1811
  lem-F4-K2-K3 = pickᴰ 3 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 4 Sᴰ
  lem-F4-K2-CS2 : Ws → St 1578
  lem-F4-K2-CS2 = pickᴰ 5 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 6 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 7 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 8 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 9 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 10 Sᴰ
  lem-F4-CS2-CS0 : Ws → St 1986
  lem-F4-CS2-CS0 = pickᴰ 11 Sᴰ
  lem-F4-K2-CS0 : Ws → St 1987
  lem-F4-K2-CS0 = pickᴰ 12 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1820 (lem-F4-CS2-CS1 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1576 (lem-F4-CS2-I c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1986 (lem-F4-CS2-CS0 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1987 (lem-F4-K2-CS0 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1809 (lem-F4-K2-I c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1810 (lem-F4-K2-K1 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1811 (lem-F4-K2-K3 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1578 (lem-F4-K2-CS2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1565 (lem-F4-K2-K2 c4)

-- ckt-TST part45: 77 steps
lem-ckt-TST-part45 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並亄侬亇侧侧亇丢侬侬侬亇侧並侬並侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬並亇並侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part45 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並亄侬亇侧侧亇丢侬侬侬亇侧並侬並侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬並亇並侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw⁻ 266 (q1 c4) ∷
   rw⁻ 265 (q2 c4) ∷
   rw⁻ 264 (q3 c4) ∷
   rw⁻ 263 (q3 c4) ∷
   rw⁻ 262 (q3 c4) ∷
   rw⁻ 261 (q4 c4) ∷
   rw⁻ 260 (q2 c4) ∷
   rw⁻ 259 (q1 c4) ∷
   rw⁻ 258 (q1 c4) ∷
   rw⁻ 257 (q2 c4) ∷
   rw⁻ 256 (q3 c4) ∷
   rw⁻ 255 (q5 c4) ∷
   rw⁻ 306 (q6 c4) ∷
   rw⁻ 305 (q4 c4) ∷
   rw⁻ 304 (q5 c4) ∷
   rw⁻ 303 (q4 c4) ∷
   rw⁻ 302 (q7 c4) ∷
   rw⁻ 301 (q3 c4) ∷
   rw⁻ 300 (q3 c4) ∷
   rw⁻ 299 (q7 c4) ∷
   rw⁻ 298 (q4 c4) ∷
   rw⁻ 297 (q2 c4) ∷
   rw⁻ 296 (q3 c4) ∷
   rw⁻ 295 (q3 c4) ∷
   rw⁻ 294 (q2 c4) ∷
   rw⁻ 293 (q4 c4) ∷
   rw⁻ 292 (q7 c4) ∷
   rw⁻ 291 (q3 c4) ∷
   rw⁻ 290 (q3 c4) ∷
   rw⁻ 289 (q7 c4) ∷
   rw⁻ 288 (q1 c4) ∷
   rw⁻ 287 (q4 c4) ∷
   rw⁻ 286 (q7 c4) ∷
   rw⁻ 285 (q3 c4) ∷
   rw⁻ 284 (q3 c4) ∷
   rw⁻ 283 (q7 c4) ∷
   rw⁻ 282 (q4 c4) ∷
   rw⁻ 281 (q2 c4) ∷
   rw⁻ 280 (q3 c4) ∷
   rw⁻ 279 (q3 c4) ∷
   rw⁻ 278 (q2 c4) ∷
   rw⁻ 277 (q4 c4) ∷
   rw⁻ 276 (q7 c4) ∷
   rw⁻ 275 (q3 c4) ∷
   rw⁻ 274 (q3 c4) ∷
   rw⁻ 273 (q7 c4) ∷
   rw⁻ 272 (q4 c4) ∷
   rw⁻ 271 (q2 c4) ∷
   rw⁻ 270 (q1 c4) ∷
   rw⁻ 269 (q1 c4) ∷
   rw⁻ 268 (q2 c4) ∷
   rw⁻ 267 (q3 c4) ∷
   rw⁻ 266 (q3 c4) ∷
   rw⁻ 265 (q3 c4) ∷
   rw⁻ 264 (q4 c4) ∷
   rw⁻ 263 (q2 c4) ∷
   rw⁻ 262 (q1 c4) ∷
   rw⁻ 261 (q1 c4) ∷
   rw⁻ 260 (q2 c4) ∷
   rw⁻ 259 (q3 c4) ∷
   rw⁻ 258 (q5 c4) ∷
   rw⁻ 309 (q8 c4) ∷
   rw⁻ 308 (q9 c4) ∷
   rw⁻ 307 (q10 c4) ∷
   rw⁻ 306 (q9 c4) ∷
   rw⁻ 305 (q11 c4) ∷
   rw⁻ 304 (q12 c4) ∷
   rw⁻ 303 (q12 c4) ∷
   rw⁻ 302 (q11 c4) ∷
   rw⁻ 301 (q9 c4) ∷
   rw⁻ 300 (q13 c4) ∷
   rw⁻ 299 (q12 c4) ∷
   rw⁻ 298 (q12 c4) ∷
   rw⁻ 297 (q13 c4) ∷
   rw⁻ 296 (q9 c4) ∷
   rw⁻ 295 (q11 c4) ∷
   rw⁻ 294 (q12 c4) ∷ []) Eq.refl
