{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD055 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D055 (Sᴰ : SD055) where

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
  lem-F4-I-I-at0213243140 : Ws → St 1645
  lem-F4-I-I-at0213243140 = pickᴰ 0 Sᴰ
  lem-F4-I-K3-at0213243140 : Ws → St 1630
  lem-F4-I-K3-at0213243140 = pickᴰ 1 Sᴰ
  lem-F4-I-S2-at0213243140 : Ws → St 1631
  lem-F4-I-S2-at0213243140 = pickᴰ 2 Sᴰ
  lem-F4-K3-I-at0213243140 : Ws → St 1632
  lem-F4-K3-I-at0213243140 = pickᴰ 3 Sᴰ
  lem-F4-K3-K3-at0213243140 : Ws → St 1633
  lem-F4-K3-K3-at0213243140 = pickᴰ 4 Sᴰ
  lem-F4-K3-S2-at0213243140 : Ws → St 1634
  lem-F4-K3-S2-at0213243140 = pickᴰ 5 Sᴰ
  lem-F4-S2-I-at0213243140 : Ws → St 1635
  lem-F4-S2-I-at0213243140 = pickᴰ 6 Sᴰ
  lem-F4-S2-K3-at0213243140 : Ws → St 1636
  lem-F4-S2-K3-at0213243140 = pickᴰ 7 Sᴰ
  lem-F4-S2-S2-at0213243140 : Ws → St 1637
  lem-F4-S2-S2-at0213243140 = pickᴰ 8 Sᴰ
  lem-F4-I-CS2-at0213243140 : Ws → St 1638
  lem-F4-I-CS2-at0213243140 = pickᴰ 9 Sᴰ
  lem-F4-S2-CS2-at0213243140 : Ws → St 1639
  lem-F4-S2-CS2-at0213243140 = pickᴰ 10 Sᴰ
  lem-F4-CS2-CS2-at0213243140 : Ws → St 1640
  lem-F4-CS2-CS2-at0213243140 = pickᴰ 11 Sᴰ
  lem-F4-CS2-I-at0213243140 : Ws → St 1641
  lem-F4-CS2-I-at0213243140 = pickᴰ 12 Sᴰ
  lem-F4-CS2-S2-at0213243140 : Ws → St 1642
  lem-F4-CS2-S2-at0213243140 = pickᴰ 13 Sᴰ
  lem-F4-CS2-K3-at0213243140 : Ws → St 1643
  lem-F4-CS2-K3-at0213243140 = pickᴰ 14 Sᴰ
  lem-F4-K3-CS2-at0213243140 : Ws → St 1644
  lem-F4-K3-CS2-at0213243140 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1643 (lem-F4-CS2-K3-at0213243140 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1633 (lem-F4-K3-K3-at0213243140 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1638 (lem-F4-I-CS2-at0213243140 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1639 (lem-F4-S2-CS2-at0213243140 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1640 (lem-F4-CS2-CS2-at0213243140 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1644 (lem-F4-K3-CS2-at0213243140 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1630 (lem-F4-I-K3-at0213243140 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1636 (lem-F4-S2-K3-at0213243140 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1631 (lem-F4-I-S2-at0213243140 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1637 (lem-F4-S2-S2-at0213243140 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1642 (lem-F4-CS2-S2-at0213243140 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1634 (lem-F4-K3-S2-at0213243140 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1645 (lem-F4-I-I-at0213243140 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1635 (lem-F4-S2-I-at0213243140 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1641 (lem-F4-CS2-I-at0213243140 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1632 (lem-F4-K3-I-at0213243140 c4)

-- deb-CKS @0213243140 part1: 173 steps
lem-deb-CKS-at0213243140-part1 : Ws → ⟪ (ℓ "五与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与与俊与与俊与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与俊与俊与与中与与俊与中与中与与俊与与丽与与丽与与丽与与上与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与俊中俊丽丽丽上丽俊俊俊俊中俊中俊丽丽丽上丽丨丨丨俊中俊中俊丽丽丽上俊俊中俊中俊丽丽丽上丨") ⟫ʷ ≈ ⟪ (ℓ "五与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与与俊与与俊与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与俊中俊中俊丽丽丽上丽与俊与俊与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与俊俊俊中俊中俊丽丽丽上丽丨丨丨俊中俊中俊丽丽丽上俊俊中俊中俊丽丽丽上丨") ⟫ʷ
lem-deb-CKS-at0213243140-part1 c4 = derive (ℓ "五与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与与俊与与俊与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与俊与俊与与中与与俊与中与中与与俊与与丽与与丽与与丽与与上与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与俊中俊丽丽丽上丽俊俊俊俊中俊中俊丽丽丽上丽丨丨丨俊中俊中俊丽丽丽上俊俊中俊中俊丽丽丽上丨") (ℓ "五与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与与俊与与俊与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与俊中俊中俊丽丽丽上丽与俊与俊与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与俊俊俊中俊中俊丽丽丽上丽丨丨丨俊中俊中俊丽丽丽上俊俊中俊中俊丽丽丽上丨")
  (rw 77 (q1 c4) ∷
   rw 74 (q2 c4) ∷
   rw 71 (q1 c4) ∷
   rw 126 (q3 c4) ∷
   rw 123 (q4 c4) ∷
   rw 120 (q4 c4) ∷
   rw 117 (q4 c4) ∷
   rw 114 (q5 c4) ∷
   rw 111 (q6 c4) ∷
   rw 108 (q5 c4) ∷
   rw 105 (q6 c4) ∷
   rw 102 (q5 c4) ∷
   rw 99 (q5 c4) ∷
   rw 96 (q3 c4) ∷
   rw 93 (q4 c4) ∷
   rw 90 (q4 c4) ∷
   rw 87 (q4 c4) ∷
   rw 84 (q5 c4) ∷
   rw 81 (q6 c4) ∷
   rw 78 (q5 c4) ∷
   rw 75 (q6 c4) ∷
   rw 72 (q5 c4) ∷
   rw 127 (q7 c4) ∷
   rw 124 (q8 c4) ∷
   rw 121 (q8 c4) ∷
   rw 118 (q8 c4) ∷
   rw 115 (q1 c4) ∷
   rw 112 (q2 c4) ∷
   rw 109 (q1 c4) ∷
   rw 106 (q2 c4) ∷
   rw 103 (q1 c4) ∷
   rw 100 (q1 c4) ∷
   rw 97 (q7 c4) ∷
   rw 94 (q8 c4) ∷
   rw 91 (q8 c4) ∷
   rw 88 (q8 c4) ∷
   rw 85 (q1 c4) ∷
   rw 82 (q2 c4) ∷
   rw 79 (q1 c4) ∷
   rw 76 (q2 c4) ∷
   rw 73 (q1 c4) ∷
   rw 128 (q3 c4) ∷
   rw 125 (q4 c4) ∷
   rw 122 (q4 c4) ∷
   rw 119 (q4 c4) ∷
   rw 116 (q5 c4) ∷
   rw 113 (q6 c4) ∷
   rw 110 (q5 c4) ∷
   rw 107 (q6 c4) ∷
   rw 104 (q5 c4) ∷
   rw 101 (q5 c4) ∷
   rw 98 (q3 c4) ∷
   rw 95 (q4 c4) ∷
   rw 92 (q4 c4) ∷
   rw 89 (q4 c4) ∷
   rw 86 (q5 c4) ∷
   rw 83 (q6 c4) ∷
   rw 80 (q5 c4) ∷
   rw 77 (q6 c4) ∷
   rw 74 (q5 c4) ∷
   rw 129 (q9 c4) ∷
   rw 126 (q10 c4) ∷
   rw 123 (q10 c4) ∷
   rw 120 (q10 c4) ∷
   rw 117 (q11 c4) ∷
   rw 114 (q12 c4) ∷
   rw 111 (q11 c4) ∷
   rw 108 (q12 c4) ∷
   rw 105 (q11 c4) ∷
   rw 102 (q11 c4) ∷
   rw 99 (q9 c4) ∷
   rw 96 (q10 c4) ∷
   rw 93 (q10 c4) ∷
   rw 90 (q10 c4) ∷
   rw 87 (q11 c4) ∷
   rw 84 (q12 c4) ∷
   rw 81 (q11 c4) ∷
   rw 78 (q12 c4) ∷
   rw 75 (q11 c4) ∷
   rw 130 (q9 c4) ∷
   rw 127 (q10 c4) ∷
   rw 124 (q10 c4) ∷
   rw 121 (q10 c4) ∷
   rw 118 (q11 c4) ∷
   rw 115 (q12 c4) ∷
   rw 112 (q11 c4) ∷
   rw 109 (q12 c4) ∷
   rw 106 (q11 c4) ∷
   rw 103 (q11 c4) ∷
   rw 100 (q9 c4) ∷
   rw 97 (q10 c4) ∷
   rw 94 (q10 c4) ∷
   rw 91 (q10 c4) ∷
   rw 88 (q11 c4) ∷
   rw 85 (q12 c4) ∷
   rw 82 (q11 c4) ∷
   rw 79 (q12 c4) ∷
   rw 76 (q11 c4) ∷
   rw 131 (q9 c4) ∷
   rw 128 (q10 c4) ∷
   rw 125 (q10 c4) ∷
   rw 122 (q10 c4) ∷
   rw 119 (q11 c4) ∷
   rw 116 (q12 c4) ∷
   rw 113 (q11 c4) ∷
   rw 110 (q12 c4) ∷
   rw 107 (q11 c4) ∷
   rw 104 (q11 c4) ∷
   rw 101 (q9 c4) ∷
   rw 98 (q10 c4) ∷
   rw 95 (q10 c4) ∷
   rw 92 (q10 c4) ∷
   rw 89 (q11 c4) ∷
   rw 86 (q12 c4) ∷
   rw 83 (q11 c4) ∷
   rw 80 (q12 c4) ∷
   rw 77 (q11 c4) ∷
   rw 132 (q13 c4) ∷
   rw 129 (q14 c4) ∷
   rw 126 (q14 c4) ∷
   rw 123 (q14 c4) ∷
   rw 120 (q15 c4) ∷
   rw 117 (q16 c4) ∷
   rw 114 (q15 c4) ∷
   rw 111 (q16 c4) ∷
   rw 108 (q15 c4) ∷
   rw 105 (q15 c4) ∷
   rw 102 (q13 c4) ∷
   rw 99 (q14 c4) ∷
   rw 96 (q14 c4) ∷
   rw 93 (q14 c4) ∷
   rw 90 (q15 c4) ∷
   rw 87 (q16 c4) ∷
   rw 84 (q15 c4) ∷
   rw 81 (q16 c4) ∷
   rw 78 (q15 c4) ∷
   rw 133 (q9 c4) ∷
   rw 130 (q10 c4) ∷
   rw 127 (q10 c4) ∷
   rw 124 (q10 c4) ∷
   rw 121 (q11 c4) ∷
   rw 118 (q12 c4) ∷
   rw 115 (q11 c4) ∷
   rw 112 (q12 c4) ∷
   rw 109 (q11 c4) ∷
   rw 106 (q11 c4) ∷
   rw 103 (q9 c4) ∷
   rw 100 (q10 c4) ∷
   rw 97 (q10 c4) ∷
   rw 94 (q10 c4) ∷
   rw 91 (q11 c4) ∷
   rw 88 (q12 c4) ∷
   rw 85 (q11 c4) ∷
   rw 82 (q12 c4) ∷
   rw 79 (q11 c4) ∷
   rw 134 (q3 c4) ∷
   rw 131 (q4 c4) ∷
   rw 128 (q4 c4) ∷
   rw 125 (q4 c4) ∷
   rw 122 (q5 c4) ∷
   rw 119 (q6 c4) ∷
   rw 116 (q5 c4) ∷
   rw 113 (q6 c4) ∷
   rw 110 (q5 c4) ∷
   rw 107 (q5 c4) ∷
   rw 104 (q3 c4) ∷
   rw 101 (q4 c4) ∷
   rw 98 (q4 c4) ∷
   rw 95 (q4 c4) ∷
   rw 92 (q5 c4) ∷
   rw 89 (q6 c4) ∷
   rw 86 (q5 c4) ∷
   rw 83 (q6 c4) ∷ []) Eq.refl
