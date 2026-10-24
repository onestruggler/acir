{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD158 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D158 (Sᴰ : SD158) where

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
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 3 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 4 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 5 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 6 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 7 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 8 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 9 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 10 Sᴰ
  lem-F4-CS2-CS0 : Ws → St 1986
  lem-F4-CS2-CS0 = pickᴰ 11 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1618 (lem-F4-K3-I c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1986 (lem-F4-CS2-CS0 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1576 (lem-F4-CS2-I c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1820 (lem-F4-CS2-CS1 c4)

-- ckt-TST part31: 77 steps
lem-ckt-TST-part31 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並亄侬亇侧侧亇丢侬侬侬亇侧並亊並侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬並侬並侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") ⟫ʷ
lem-ckt-TST-part31 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並亄侬亇侧侧亇丢侬侬侬亇侧並亊並侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬並侬並侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢俄並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亄並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄丢")
  (rw⁻ 200 (q1 c4) ∷
   rw⁻ 199 (q2 c4) ∷
   rw⁻ 198 (q3 c4) ∷
   rw⁻ 197 (q3 c4) ∷
   rw⁻ 196 (q3 c4) ∷
   rw⁻ 195 (q4 c4) ∷
   rw⁻ 194 (q2 c4) ∷
   rw⁻ 193 (q1 c4) ∷
   rw⁻ 192 (q1 c4) ∷
   rw⁻ 191 (q2 c4) ∷
   rw⁻ 190 (q3 c4) ∷
   rw⁻ 189 (q5 c4) ∷
   rw⁻ 240 (q6 c4) ∷
   rw⁻ 239 (q7 c4) ∷
   rw⁻ 238 (q8 c4) ∷
   rw⁻ 237 (q7 c4) ∷
   rw⁻ 236 (q9 c4) ∷
   rw⁻ 235 (q10 c4) ∷
   rw⁻ 234 (q10 c4) ∷
   rw⁻ 233 (q9 c4) ∷
   rw⁻ 232 (q7 c4) ∷
   rw⁻ 231 (q11 c4) ∷
   rw⁻ 230 (q10 c4) ∷
   rw⁻ 229 (q10 c4) ∷
   rw⁻ 228 (q11 c4) ∷
   rw⁻ 227 (q7 c4) ∷
   rw⁻ 226 (q9 c4) ∷
   rw⁻ 225 (q10 c4) ∷
   rw⁻ 224 (q10 c4) ∷
   rw⁻ 223 (q9 c4) ∷
   rw⁻ 222 (q12 c4) ∷
   rw⁻ 221 (q7 c4) ∷
   rw⁻ 220 (q9 c4) ∷
   rw⁻ 219 (q10 c4) ∷
   rw⁻ 218 (q10 c4) ∷
   rw⁻ 217 (q9 c4) ∷
   rw⁻ 216 (q7 c4) ∷
   rw⁻ 215 (q11 c4) ∷
   rw⁻ 214 (q10 c4) ∷
   rw⁻ 213 (q10 c4) ∷
   rw⁻ 212 (q11 c4) ∷
   rw⁻ 211 (q7 c4) ∷
   rw⁻ 210 (q9 c4) ∷
   rw⁻ 209 (q10 c4) ∷
   rw⁻ 208 (q10 c4) ∷
   rw⁻ 207 (q9 c4) ∷
   rw⁻ 206 (q7 c4) ∷
   rw⁻ 205 (q11 c4) ∷
   rw⁻ 204 (q12 c4) ∷
   rw⁻ 203 (q12 c4) ∷
   rw⁻ 202 (q11 c4) ∷
   rw⁻ 201 (q10 c4) ∷
   rw⁻ 200 (q10 c4) ∷
   rw⁻ 199 (q10 c4) ∷
   rw⁻ 198 (q7 c4) ∷
   rw⁻ 197 (q11 c4) ∷
   rw⁻ 196 (q12 c4) ∷
   rw⁻ 195 (q12 c4) ∷
   rw⁻ 194 (q11 c4) ∷
   rw⁻ 193 (q10 c4) ∷
   rw⁻ 192 (q8 c4) ∷
   rw⁻ 243 (q6 c4) ∷
   rw⁻ 242 (q7 c4) ∷
   rw⁻ 241 (q8 c4) ∷
   rw⁻ 240 (q7 c4) ∷
   rw⁻ 239 (q9 c4) ∷
   rw⁻ 238 (q10 c4) ∷
   rw⁻ 237 (q10 c4) ∷
   rw⁻ 236 (q9 c4) ∷
   rw⁻ 235 (q7 c4) ∷
   rw⁻ 234 (q11 c4) ∷
   rw⁻ 233 (q10 c4) ∷
   rw⁻ 232 (q10 c4) ∷
   rw⁻ 231 (q11 c4) ∷
   rw⁻ 230 (q7 c4) ∷
   rw⁻ 229 (q9 c4) ∷
   rw⁻ 228 (q10 c4) ∷ []) Eq.refl
