{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD082 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D082 (Sᴰ : SD082) where

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
  lem-F4-K1-I : Ws → St 1646
  lem-F4-K1-I = pickᴰ 4 Sᴰ
  lem-F4-K1-K2 : Ws → St 1647
  lem-F4-K1-K2 = pickᴰ 5 Sᴰ
  lem-F4-K1-K3 : Ws → St 1648
  lem-F4-K1-K3 = pickᴰ 6 Sᴰ
  lem-F4-K3-I : Ws → St 1618
  lem-F4-K3-I = pickᴰ 7 Sᴰ
  lem-F4-K3-K1 : Ws → St 1649
  lem-F4-K3-K1 = pickᴰ 8 Sᴰ
  lem-F4-K3-K2 : Ws → St 1650
  lem-F4-K3-K2 = pickᴰ 9 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 10 Sᴰ
  lem-F4-CS2-I : Ws → St 1576
  lem-F4-CS2-I = pickᴰ 11 Sᴰ
  lem-F4-I-CS1 : Ws → St 1432
  lem-F4-I-CS1 = pickᴰ 12 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 13 Sᴰ
  lem-F4-CS2-K2 : Ws → St 1580
  lem-F4-CS2-K2 = pickᴰ 14 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 15 Sᴰ
  lem-F4-CS2-K1 : Ws → St 1815
  lem-F4-CS2-K1 = pickᴰ 16 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 17 Sᴰ
  lem-F4-K1-CS2 : Ws → St 1652
  lem-F4-K1-CS2 = pickᴰ 18 Sᴰ
  lem-F4-K3-CS1 : Ws → St 1653
  lem-F4-K3-CS1 = pickᴰ 19 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 20 Sᴰ
  lem-F4-CS2-CS1 : Ws → St 1820
  lem-F4-CS2-CS1 = pickᴰ 21 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1580 (lem-F4-CS2-K2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1576 (lem-F4-CS2-I c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1820 (lem-F4-CS2-CS1 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1815 (lem-F4-CS2-K1 c4)
  q7 : Ws → Eqn
  q7 c4 = wlE 1419 (lit c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1596 (lem-F4-K3-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1618 (lem-F4-K3-I c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1650 (lem-F4-K3-K2 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1653 (lem-F4-K3-CS1 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1649 (lem-F4-K3-K1 c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 1411 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1411 (lem-F4-I-K3 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1386 (lem-F4-I-I c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1410 (lem-F4-I-K2 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1432 (lem-F4-I-CS1 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1409 (lem-F4-I-K1 c4)
  q21 : Ws → Eqn
  q21 c4 = wlE 1417 (lit c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1646 (lem-F4-K1-I c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1648 (lem-F4-K1-K3 c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1652 (lem-F4-K1-CS2 c4)
  q25 : Ws → Eqn
  q25 c4 = sE 1647 (lem-F4-K1-K2 c4)

-- ckt-TST part6: 128 steps
lem-ckt-TST-part6 : Ws → ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬並侬並侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬丞一丒一俄丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ ≈ ⟪ (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊並亄並侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄一俄丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") ⟫ʷ
lem-ckt-TST-part6 c4 = derive (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬並侬並侬亇丢亊侬侬亊丢侧亊侬侬亊丢亇侬侬亇丢亊侬侬丞一丒一俄丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一") (ℓ "並亄並並侬並並亇並並侧並並侧並並亇並並丢並並侬並並侬並並侬並並亇並並侧並並侧並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並並侧並並亊並並侬並並侬並並亊並並丢並並亇並並侬並並侬並並亇並並丢並並亊並並侬並並侬並並亊並並丢並亄侬亇侧侧亇丢侬侬侬亇侧侧亇丢亊侬侬亊丢亇侬侬亇丢亊侬侬亊丢侧亊並亄並侬侬亊丢亇侬侬亇丢亊侬侬亊丢亄一俄丒乢丘乇乇丘一乢乢乢丘乇乇丘一丞乢乢丞一丘乢乢丘一丞乢乢丞一乇丞乢乢丞一丘乢乢丘一丞乢乢丞一丒一")
  (rw⁻ 150 (q1 c4) ∷
   rw⁻ 149 (q2 c4) ∷
   rw⁻ 148 (q3 c4) ∷
   rw⁻ 147 (q4 c4) ∷
   rw⁻ 146 (q1 c4) ∷
   rw⁻ 145 (q1 c4) ∷
   rw⁻ 144 (q4 c4) ∷
   rw⁻ 143 (q3 c4) ∷
   rw⁻ 142 (q2 c4) ∷
   rw⁻ 141 (q5 c4) ∷
   rw⁻ 140 (q5 c4) ∷
   rw⁻ 139 (q2 c4) ∷
   rw⁻ 138 (q1 c4) ∷
   rw⁻ 137 (q1 c4) ∷
   rw⁻ 136 (q1 c4) ∷
   rw⁻ 135 (q3 c4) ∷
   rw⁻ 134 (q2 c4) ∷
   rw⁻ 133 (q5 c4) ∷
   rw⁻ 132 (q5 c4) ∷
   rw⁻ 131 (q2 c4) ∷
   rw⁻ 130 (q1 c4) ∷
   rw⁻ 129 (q6 c4) ∷
   rw 176 (q7 c4) ∷
   rw⁻ 175 (q8 c4) ∷
   rw⁻ 174 (q8 c4) ∷
   rw⁻ 173 (q9 c4) ∷
   rw⁻ 172 (q10 c4) ∷
   rw⁻ 171 (q11 c4) ∷
   rw⁻ 170 (q8 c4) ∷
   rw⁻ 169 (q8 c4) ∷
   rw⁻ 168 (q11 c4) ∷
   rw⁻ 167 (q10 c4) ∷
   rw⁻ 166 (q9 c4) ∷
   rw⁻ 165 (q8 c4) ∷
   rw⁻ 164 (q8 c4) ∷
   rw⁻ 163 (q9 c4) ∷
   rw⁻ 162 (q12 c4) ∷
   rw⁻ 161 (q10 c4) ∷
   rw⁻ 160 (q9 c4) ∷
   rw⁻ 159 (q8 c4) ∷
   rw⁻ 158 (q8 c4) ∷
   rw⁻ 157 (q9 c4) ∷
   rw⁻ 156 (q10 c4) ∷
   rw⁻ 155 (q11 c4) ∷
   rw⁻ 154 (q8 c4) ∷
   rw⁻ 153 (q8 c4) ∷
   rw⁻ 152 (q11 c4) ∷
   rw⁻ 151 (q10 c4) ∷
   rw⁻ 150 (q9 c4) ∷
   rw⁻ 149 (q8 c4) ∷
   rw⁻ 148 (q8 c4) ∷
   rw⁻ 147 (q9 c4) ∷
   rw⁻ 146 (q10 c4) ∷
   rw⁻ 145 (q11 c4) ∷
   rw⁻ 144 (q12 c4) ∷
   rw⁻ 143 (q12 c4) ∷
   rw⁻ 142 (q11 c4) ∷
   rw⁻ 141 (q8 c4) ∷
   rw⁻ 140 (q8 c4) ∷
   rw⁻ 139 (q8 c4) ∷
   rw⁻ 138 (q10 c4) ∷
   rw⁻ 137 (q11 c4) ∷
   rw⁻ 136 (q12 c4) ∷
   rw⁻ 135 (q12 c4) ∷
   rw⁻ 134 (q11 c4) ∷
   rw⁻ 133 (q8 c4) ∷
   rw⁻ 132 (q13 c4) ∷
   rw⁻ 180 (q14 c4) ∷
   rw⁻ 179 (q15 c4) ∷
   rw⁻ 178 (q16 c4) ∷
   rw⁻ 177 (q16 c4) ∷
   rw⁻ 176 (q15 c4) ∷
   rw⁻ 175 (q17 c4) ∷
   rw⁻ 174 (q18 c4) ∷
   rw⁻ 173 (q16 c4) ∷
   rw⁻ 172 (q16 c4) ∷
   rw⁻ 171 (q18 c4) ∷
   rw⁻ 170 (q17 c4) ∷
   rw⁻ 169 (q15 c4) ∷
   rw⁻ 168 (q16 c4) ∷
   rw⁻ 167 (q16 c4) ∷
   rw⁻ 166 (q15 c4) ∷
   rw⁻ 165 (q19 c4) ∷
   rw⁻ 164 (q17 c4) ∷
   rw⁻ 163 (q15 c4) ∷
   rw⁻ 162 (q16 c4) ∷
   rw⁻ 161 (q16 c4) ∷
   rw⁻ 160 (q15 c4) ∷
   rw⁻ 159 (q17 c4) ∷
   rw⁻ 158 (q18 c4) ∷
   rw⁻ 157 (q16 c4) ∷
   rw⁻ 156 (q16 c4) ∷
   rw⁻ 155 (q18 c4) ∷
   rw⁻ 154 (q17 c4) ∷
   rw⁻ 153 (q15 c4) ∷
   rw⁻ 152 (q16 c4) ∷
   rw⁻ 151 (q16 c4) ∷
   rw⁻ 150 (q15 c4) ∷
   rw⁻ 149 (q17 c4) ∷
   rw⁻ 148 (q18 c4) ∷
   rw⁻ 147 (q19 c4) ∷
   rw⁻ 146 (q19 c4) ∷
   rw⁻ 145 (q18 c4) ∷
   rw⁻ 144 (q16 c4) ∷
   rw⁻ 143 (q16 c4) ∷
   rw⁻ 142 (q16 c4) ∷
   rw⁻ 141 (q17 c4) ∷
   rw⁻ 140 (q18 c4) ∷
   rw⁻ 139 (q19 c4) ∷
   rw⁻ 138 (q19 c4) ∷
   rw⁻ 137 (q18 c4) ∷
   rw⁻ 136 (q16 c4) ∷
   rw⁻ 135 (q20 c4) ∷
   rw 184 (q21 c4) ∷
   rw⁻ 183 (q22 c4) ∷
   rw⁻ 182 (q23 c4) ∷
   rw⁻ 181 (q24 c4) ∷
   rw⁻ 180 (q24 c4) ∷
   rw⁻ 179 (q23 c4) ∷
   rw⁻ 178 (q22 c4) ∷
   rw⁻ 177 (q25 c4) ∷
   rw⁻ 176 (q24 c4) ∷
   rw⁻ 175 (q24 c4) ∷
   rw⁻ 174 (q25 c4) ∷
   rw⁻ 173 (q22 c4) ∷
   rw⁻ 172 (q23 c4) ∷
   rw⁻ 171 (q24 c4) ∷
   rw⁻ 170 (q24 c4) ∷ []) Eq.refl
