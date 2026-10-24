{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD163 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D163 (Sᴰ : SD163) where

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
  lem-F4-K3-CS0 : Ws → St 1654
  lem-F4-K3-CS0 = pickᴰ 9 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 10 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 11 Sᴰ
  lem-F4-CS2-CS0 : Ws → St 1986
  lem-F4-CS2-CS0 = pickᴰ 12 Sᴰ

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
  q8 c4 = sE 1654 (lem-F4-K3-CS0 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1618 (lem-F4-K3-I c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1650 (lem-F4-K3-K2 c4)

-- ckt-TST part38: 77 steps
lem-ckt-TST-part38 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並亄侬亇侧侧亇丢侬侬侬亇侧並侬並侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬並亊並侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part38 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並亄侬亇侧侧亇丢侬侬侬亇侧並侬並侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬並亊並侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw⁻ 233 (q1 c4) ∷
   rw⁻ 232 (q2 c4) ∷
   rw⁻ 231 (q3 c4) ∷
   rw⁻ 230 (q3 c4) ∷
   rw⁻ 229 (q3 c4) ∷
   rw⁻ 228 (q4 c4) ∷
   rw⁻ 227 (q2 c4) ∷
   rw⁻ 226 (q1 c4) ∷
   rw⁻ 225 (q1 c4) ∷
   rw⁻ 224 (q2 c4) ∷
   rw⁻ 223 (q3 c4) ∷
   rw⁻ 222 (q5 c4) ∷
   rw⁻ 273 (q6 c4) ∷
   rw⁻ 272 (q4 c4) ∷
   rw⁻ 271 (q5 c4) ∷
   rw⁻ 270 (q4 c4) ∷
   rw⁻ 269 (q7 c4) ∷
   rw⁻ 268 (q3 c4) ∷
   rw⁻ 267 (q3 c4) ∷
   rw⁻ 266 (q7 c4) ∷
   rw⁻ 265 (q4 c4) ∷
   rw⁻ 264 (q2 c4) ∷
   rw⁻ 263 (q3 c4) ∷
   rw⁻ 262 (q3 c4) ∷
   rw⁻ 261 (q2 c4) ∷
   rw⁻ 260 (q4 c4) ∷
   rw⁻ 259 (q7 c4) ∷
   rw⁻ 258 (q3 c4) ∷
   rw⁻ 257 (q3 c4) ∷
   rw⁻ 256 (q7 c4) ∷
   rw⁻ 255 (q1 c4) ∷
   rw⁻ 254 (q4 c4) ∷
   rw⁻ 253 (q7 c4) ∷
   rw⁻ 252 (q3 c4) ∷
   rw⁻ 251 (q3 c4) ∷
   rw⁻ 250 (q7 c4) ∷
   rw⁻ 249 (q4 c4) ∷
   rw⁻ 248 (q2 c4) ∷
   rw⁻ 247 (q3 c4) ∷
   rw⁻ 246 (q3 c4) ∷
   rw⁻ 245 (q2 c4) ∷
   rw⁻ 244 (q4 c4) ∷
   rw⁻ 243 (q7 c4) ∷
   rw⁻ 242 (q3 c4) ∷
   rw⁻ 241 (q3 c4) ∷
   rw⁻ 240 (q7 c4) ∷
   rw⁻ 239 (q4 c4) ∷
   rw⁻ 238 (q2 c4) ∷
   rw⁻ 237 (q1 c4) ∷
   rw⁻ 236 (q1 c4) ∷
   rw⁻ 235 (q2 c4) ∷
   rw⁻ 234 (q3 c4) ∷
   rw⁻ 233 (q3 c4) ∷
   rw⁻ 232 (q3 c4) ∷
   rw⁻ 231 (q4 c4) ∷
   rw⁻ 230 (q2 c4) ∷
   rw⁻ 229 (q1 c4) ∷
   rw⁻ 228 (q1 c4) ∷
   rw⁻ 227 (q2 c4) ∷
   rw⁻ 226 (q3 c4) ∷
   rw⁻ 225 (q5 c4) ∷
   rw⁻ 276 (q8 c4) ∷
   rw⁻ 275 (q9 c4) ∷
   rw⁻ 274 (q10 c4) ∷
   rw⁻ 273 (q9 c4) ∷
   rw⁻ 272 (q11 c4) ∷
   rw⁻ 271 (q12 c4) ∷
   rw⁻ 270 (q12 c4) ∷
   rw⁻ 269 (q11 c4) ∷
   rw⁻ 268 (q9 c4) ∷
   rw⁻ 267 (q13 c4) ∷
   rw⁻ 266 (q12 c4) ∷
   rw⁻ 265 (q12 c4) ∷
   rw⁻ 264 (q13 c4) ∷
   rw⁻ 263 (q9 c4) ∷
   rw⁻ 262 (q11 c4) ∷
   rw⁻ 261 (q12 c4) ∷ []) Eq.refl
