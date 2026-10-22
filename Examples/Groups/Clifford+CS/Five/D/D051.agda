{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD051 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D051 (Sᴰ : SD051) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)

-- The lemmas of other derivation modules (DSig).
private
  lem-F4-I-K3 : Ws → St 1411
  lem-F4-I-K3 = pickᴰ 0 Sᴰ
  lem-F4-I-S2 : Ws → St 1595
  lem-F4-I-S2 = pickᴰ 1 Sᴰ
  lem-F4-K3-K3 : Ws → St 1596
  lem-F4-K3-K3 = pickᴰ 2 Sᴰ
  lem-F4-K3-S2 : Ws → St 1619
  lem-F4-K3-S2 = pickᴰ 3 Sᴰ
  lem-F4-S2-K3 : Ws → St 1598
  lem-F4-S2-K3 = pickᴰ 4 Sᴰ
  lem-F4-S2-S2 : Ws → St 1599
  lem-F4-S2-S2 = pickᴰ 5 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1606
  lem-F4-CS2-S2 = pickᴰ 6 Sᴰ
  lem-F4-I-CS2 : Ws → St 1433
  lem-F4-I-CS2 = pickᴰ 7 Sᴰ
  lem-F4-S2-CS2 : Ws → St 1607
  lem-F4-S2-CS2 = pickᴰ 8 Sᴰ
  lem-F4-CS2-CS2 : Ws → St 1581
  lem-F4-CS2-CS2 = pickᴰ 9 Sᴰ
  lem-F4-CS2-K3 : Ws → St 1615
  lem-F4-CS2-K3 = pickᴰ 10 Sᴰ
  lem-F4-K3-CS2 : Ws → St 1616
  lem-F4-K3-CS2 = pickᴰ 11 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1599 (lem-F4-S2-S2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1606 (lem-F4-CS2-S2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1619 (lem-F4-K3-S2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1595 (lem-F4-I-S2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1433 (lem-F4-I-CS2 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1607 (lem-F4-S2-CS2 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1581 (lem-F4-CS2-CS2 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1616 (lem-F4-K3-CS2 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1411 (lem-F4-I-K3 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1598 (lem-F4-S2-K3 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1615 (lem-F4-CS2-K3 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1596 (lem-F4-K3-K3 c4)

-- deb-CKS part1: 173 steps
lem-deb-CKS-part1 : Ws → ⟪ (CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-deb-CKS-part1 c4 = derive (CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ S4 ∷ X4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CK43 ∷ X4 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ CS24 ∷ X4 ∷ X4 ∷ S4 ∷ X4 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS24 ∷ CS34 ∷ CS34 ∷ CS34 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CK43 ∷ Sb0-2-43-1 ∷ CS24 ∷ CS24 ∷ CS24 ∷ S4 ∷ CS34 ∷ [])
  (rw 130 (q1 c4) ∷
   rw 127 (q1 c4) ∷
   rw 124 (q1 c4) ∷
   rw 121 (q2 c4) ∷
   rw 118 (q3 c4) ∷
   rw 115 (q2 c4) ∷
   rw 112 (q3 c4) ∷
   rw 109 (q2 c4) ∷
   rw 106 (q2 c4) ∷
   rw 103 (q4 c4) ∷
   rw 100 (q1 c4) ∷
   rw 97 (q1 c4) ∷
   rw 94 (q1 c4) ∷
   rw 91 (q2 c4) ∷
   rw 88 (q3 c4) ∷
   rw 85 (q2 c4) ∷
   rw 82 (q3 c4) ∷
   rw 79 (q2 c4) ∷
   rw 134 (q5 c4) ∷
   rw 131 (q6 c4) ∷
   rw 128 (q6 c4) ∷
   rw 125 (q6 c4) ∷
   rw 122 (q7 c4) ∷
   rw 119 (q8 c4) ∷
   rw 116 (q7 c4) ∷
   rw 113 (q8 c4) ∷
   rw 110 (q7 c4) ∷
   rw 107 (q7 c4) ∷
   rw 104 (q5 c4) ∷
   rw 101 (q6 c4) ∷
   rw 98 (q6 c4) ∷
   rw 95 (q6 c4) ∷
   rw 92 (q7 c4) ∷
   rw 89 (q8 c4) ∷
   rw 86 (q7 c4) ∷
   rw 83 (q8 c4) ∷
   rw 80 (q7 c4) ∷
   rw 135 (q5 c4) ∷
   rw 132 (q6 c4) ∷
   rw 129 (q6 c4) ∷
   rw 126 (q6 c4) ∷
   rw 123 (q7 c4) ∷
   rw 120 (q8 c4) ∷
   rw 117 (q7 c4) ∷
   rw 114 (q8 c4) ∷
   rw 111 (q7 c4) ∷
   rw 108 (q7 c4) ∷
   rw 105 (q5 c4) ∷
   rw 102 (q6 c4) ∷
   rw 99 (q6 c4) ∷
   rw 96 (q6 c4) ∷
   rw 93 (q7 c4) ∷
   rw 90 (q8 c4) ∷
   rw 87 (q7 c4) ∷
   rw 84 (q8 c4) ∷
   rw 81 (q7 c4) ∷
   rw 136 (q5 c4) ∷
   rw 133 (q6 c4) ∷
   rw 130 (q6 c4) ∷
   rw 127 (q6 c4) ∷
   rw 124 (q7 c4) ∷
   rw 121 (q8 c4) ∷
   rw 118 (q7 c4) ∷
   rw 115 (q8 c4) ∷
   rw 112 (q7 c4) ∷
   rw 109 (q7 c4) ∷
   rw 106 (q5 c4) ∷
   rw 103 (q6 c4) ∷
   rw 100 (q6 c4) ∷
   rw 97 (q6 c4) ∷
   rw 94 (q7 c4) ∷
   rw 91 (q8 c4) ∷
   rw 88 (q7 c4) ∷
   rw 85 (q8 c4) ∷
   rw 82 (q7 c4) ∷
   rw 137 (q5 c4) ∷
   rw 134 (q6 c4) ∷
   rw 131 (q6 c4) ∷
   rw 128 (q6 c4) ∷
   rw 125 (q7 c4) ∷
   rw 122 (q8 c4) ∷
   rw 119 (q7 c4) ∷
   rw 116 (q8 c4) ∷
   rw 113 (q7 c4) ∷
   rw 110 (q7 c4) ∷
   rw 107 (q5 c4) ∷
   rw 104 (q6 c4) ∷
   rw 101 (q6 c4) ∷
   rw 98 (q6 c4) ∷
   rw 95 (q7 c4) ∷
   rw 92 (q8 c4) ∷
   rw 89 (q7 c4) ∷
   rw 86 (q8 c4) ∷
   rw 83 (q7 c4) ∷
   rw 138 (q9 c4) ∷
   rw 135 (q10 c4) ∷
   rw 132 (q10 c4) ∷
   rw 129 (q10 c4) ∷
   rw 126 (q11 c4) ∷
   rw 123 (q12 c4) ∷
   rw 120 (q11 c4) ∷
   rw 117 (q12 c4) ∷
   rw 114 (q11 c4) ∷
   rw 111 (q11 c4) ∷
   rw 108 (q9 c4) ∷
   rw 105 (q10 c4) ∷
   rw 102 (q10 c4) ∷
   rw 99 (q10 c4) ∷
   rw 96 (q11 c4) ∷
   rw 93 (q12 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q12 c4) ∷
   rw 84 (q11 c4) ∷
   rw 139 (q5 c4) ∷
   rw 136 (q6 c4) ∷
   rw 133 (q6 c4) ∷
   rw 130 (q6 c4) ∷
   rw 127 (q7 c4) ∷
   rw 124 (q8 c4) ∷
   rw 121 (q7 c4) ∷
   rw 118 (q8 c4) ∷
   rw 115 (q7 c4) ∷
   rw 112 (q7 c4) ∷
   rw 109 (q5 c4) ∷
   rw 106 (q6 c4) ∷
   rw 103 (q6 c4) ∷
   rw 100 (q6 c4) ∷
   rw 97 (q7 c4) ∷
   rw 94 (q8 c4) ∷
   rw 91 (q7 c4) ∷
   rw 88 (q8 c4) ∷
   rw 85 (q7 c4) ∷
   rw 140 (q9 c4) ∷
   rw 137 (q10 c4) ∷
   rw 134 (q10 c4) ∷
   rw 131 (q10 c4) ∷
   rw 128 (q11 c4) ∷
   rw 125 (q12 c4) ∷
   rw 122 (q11 c4) ∷
   rw 119 (q12 c4) ∷
   rw 116 (q11 c4) ∷
   rw 113 (q11 c4) ∷
   rw 110 (q9 c4) ∷
   rw 107 (q10 c4) ∷
   rw 104 (q10 c4) ∷
   rw 101 (q10 c4) ∷
   rw 98 (q11 c4) ∷
   rw 95 (q12 c4) ∷
   rw 92 (q11 c4) ∷
   rw 89 (q12 c4) ∷
   rw 86 (q11 c4) ∷
   rw 141 (q5 c4) ∷
   rw 138 (q6 c4) ∷
   rw 135 (q6 c4) ∷
   rw 132 (q6 c4) ∷
   rw 129 (q7 c4) ∷
   rw 126 (q8 c4) ∷
   rw 123 (q7 c4) ∷
   rw 120 (q8 c4) ∷
   rw 117 (q7 c4) ∷
   rw 114 (q7 c4) ∷
   rw 111 (q5 c4) ∷
   rw 108 (q6 c4) ∷
   rw 105 (q6 c4) ∷
   rw 102 (q6 c4) ∷
   rw 99 (q7 c4) ∷
   rw 96 (q8 c4) ∷
   rw 93 (q7 c4) ∷
   rw 90 (q8 c4) ∷
   rw 87 (q7 c4) ∷
   rw 142 (q4 c4) ∷
   rw 139 (q1 c4) ∷
   rw 136 (q1 c4) ∷ []) Eq.refl
