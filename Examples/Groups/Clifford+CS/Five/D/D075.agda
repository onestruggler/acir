{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD075 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D075 (Sᴰ : SD075) where

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
  lem-F4-I-K3-at02132031 : Ws → St 1787
  lem-F4-I-K3-at02132031 = pickᴰ 0 Sᴰ
  lem-F4-I-S2-at02132031 : Ws → St 1771
  lem-F4-I-S2-at02132031 = pickᴰ 1 Sᴰ
  lem-F4-K3-K3-at02132031 : Ws → St 1789
  lem-F4-K3-K3-at02132031 = pickᴰ 2 Sᴰ
  lem-F4-S2-I-at02132031 : Ws → St 1791
  lem-F4-S2-I-at02132031 = pickᴰ 3 Sᴰ
  lem-F4-S2-K3-at02132031 : Ws → St 1793
  lem-F4-S2-K3-at02132031 = pickᴰ 4 Sᴰ
  lem-F4-S2-S2-at02132031 : Ws → St 1795
  lem-F4-S2-S2-at02132031 = pickᴰ 5 Sᴰ
  lem-F4-CS2-CS2-at02132031 : Ws → St 1583
  lem-F4-CS2-CS2-at02132031 = pickᴰ 6 Sᴰ
  lem-F4-CS2-I-at02132031 : Ws → St 1584
  lem-F4-CS2-I-at02132031 = pickᴰ 7 Sᴰ
  lem-F4-CS2-S2-at02132031 : Ws → St 1777
  lem-F4-CS2-S2-at02132031 = pickᴰ 8 Sᴰ
  lem-F4-I-CS2-at02132031 : Ws → St 1587
  lem-F4-I-CS2-at02132031 = pickᴰ 9 Sᴰ
  lem-F4-S2-CS2-at02132031 : Ws → St 1797
  lem-F4-S2-CS2-at02132031 = pickᴰ 10 Sᴰ
  lem-F5-23-at02132031 : Ws → St 1591
  lem-F5-23-at02132031 = pickᴰ 11 Sᴰ
  lem-F4-CS2-K3-at02132031 : Ws → St 1799
  lem-F4-CS2-K3-at02132031 = pickᴰ 12 Sᴰ
  lem-F4-K3-CS2-at02132031 : Ws → St 1801
  lem-F4-K3-CS2-at02132031 = pickᴰ 13 Sᴰ
  lem-deb-CKS-split-a-at0213243140-part0 : Ws → St 1807
  lem-deb-CKS-split-a-at0213243140-part0 = pickᴰ 14 Sᴰ
  lem-deb-CKS-split-a-at0213243140-part1 : Ws → St 1808
  lem-deb-CKS-split-a-at0213243140-part1 = pickᴰ 15 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1807 (lem-deb-CKS-split-a-at0213243140-part0 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1808 (lem-deb-CKS-split-a-at0213243140-part1 c4)

-- deb-CKS-split-a @0213243140: 2 steps
lem-deb-CKS-split-a-at0213243140 : Ws → ⟪ (ℓ "乕丒乕丒乕丢丢丢一丢乕乕乕乕丒乕丒乕丢丢丢一丢") ⟫ʷ ≈ ⟪ (ℓ "与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与与俊与与俊与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与俊中俊中俊丽丽丽上丽俊俊俊俊中俊中俊丽丽丽上丽") ⟫ʷ
lem-deb-CKS-split-a-at0213243140 c4 = derive (ℓ "乕丒乕丒乕丢丢丢一丢乕乕乕乕丒乕丒乕丢丢丢一丢") (ℓ "与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与与俊与与俊与与俊与与俊与与中与与俊与与中与与俊与与丽与与丽与与丽与与上与与丽与俊中俊中俊丽丽丽上丽俊俊俊俊中俊中俊丽丽丽上丽")
  (rw 0 (q1 c4) ∷
   rw 0 (q2 c4) ∷ []) Eq.refl

private
  q3 : Ws → Eqn
  q3 c4 = sE 1591 (lem-F5-23-at02132031 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1583 (lem-F4-CS2-CS2-at02132031 c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 1417 (lit c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1801 (lem-F4-K3-CS2-at02132031 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1799 (lem-F4-CS2-K3-at02132031 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1789 (lem-F4-K3-K3-at02132031 c4)
  q9 : Ws → Eqn
  q9 c4 = wpE 1267 c4
  q10 : Ws → Eqn
  q10 c4 = sE 1797 (lem-F4-S2-CS2-at02132031 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1793 (lem-F4-S2-K3-at02132031 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1795 (lem-F4-S2-S2-at02132031 c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 1411 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1771 (lem-F4-I-S2-at02132031 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1587 (lem-F4-I-CS2-at02132031 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1787 (lem-F4-I-K3-at02132031 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1791 (lem-F4-S2-I-at02132031 c4)

-- deb-AD-split-a @02132031: 136 steps
lem-deb-AD-split-a-at02132031 : Ws → ⟪ (ℓ "丨丨丨丨丨丨丨丒丨丒丨上上上一上") ⟫ʷ ≈ ⟪ (ℓ "並俄並並俄並並俄並並俄並並俄並並俄並並俄並並亄並並俄並並亄並並俄並並丽並並丽並並丽並並丢並並丽並俄俄俄俄俄俄俄亄俄亄俄丽丽丽丢丽") ⟫ʷ
lem-deb-AD-split-a-at02132031 c4 = derive (ℓ "丨丨丨丨丨丨丨丒丨丒丨上上上一上") (ℓ "並俄並並俄並並俄並並俄並並俄並並俄並並俄並並亄並並俄並並亄並並俄並並丽並並丽並並丽並並丢並並丽並俄俄俄俄俄俄俄亄俄亄俄丽丽丽丢丽")
  (rw⁻ 0 (q3 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw⁻ 3 (q4 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 7 (q4 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw⁻ 12 (q3 c4) ∷
   rw⁻ 11 (q4 c4) ∷
   rw⁻ 10 (q4 c4) ∷
   rw⁻ 9 (q4 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 13 (q4 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw⁻ 20 (q3 c4) ∷
   rw⁻ 19 (q4 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw⁻ 17 (q4 c4) ∷
   rw⁻ 16 (q4 c4) ∷
   rw⁻ 15 (q4 c4) ∷
   rw⁻ 24 (q3 c4) ∷
   rw⁻ 23 (q4 c4) ∷
   rw⁻ 22 (q4 c4) ∷
   rw⁻ 21 (q4 c4) ∷
   rw⁻ 20 (q4 c4) ∷
   rw⁻ 19 (q4 c4) ∷
   rw⁻ 18 (q4 c4) ∷
   rw 28 (q5 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 26 (q6 c4) ∷
   rw⁻ 25 (q6 c4) ∷
   rw⁻ 24 (q6 c4) ∷
   rw⁻ 23 (q6 c4) ∷
   rw⁻ 22 (q6 c4) ∷
   rw⁻ 21 (q6 c4) ∷
   rw⁻ 32 (q3 c4) ∷
   rw⁻ 31 (q7 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 28 (q4 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 26 (q4 c4) ∷
   rw⁻ 25 (q4 c4) ∷
   rw⁻ 24 (q4 c4) ∷
   rw 36 (q5 c4) ∷
   rw⁻ 35 (q6 c4) ∷
   rw⁻ 34 (q8 c4) ∷
   rw⁻ 33 (q6 c4) ∷
   rw⁻ 32 (q6 c4) ∷
   rw⁻ 31 (q6 c4) ∷
   rw⁻ 30 (q6 c4) ∷
   rw⁻ 29 (q6 c4) ∷
   rw⁻ 28 (q6 c4) ∷
   rw⁻ 27 (q6 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 39 (q7 c4) ∷
   rw⁻ 38 (q4 c4) ∷
   rw⁻ 37 (q7 c4) ∷
   rw⁻ 36 (q4 c4) ∷
   rw⁻ 35 (q4 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 33 (q4 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q4 c4) ∷
   rw 44 (q9 c4) ∷
   rw⁻ 43 (q10 c4) ∷
   rw⁻ 42 (q11 c4) ∷
   rw⁻ 41 (q10 c4) ∷
   rw⁻ 40 (q11 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 38 (q10 c4) ∷
   rw⁻ 37 (q10 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw⁻ 35 (q10 c4) ∷
   rw⁻ 34 (q10 c4) ∷
   rw⁻ 33 (q10 c4) ∷
   rw 48 (q9 c4) ∷
   rw⁻ 47 (q12 c4) ∷
   rw⁻ 46 (q10 c4) ∷
   rw⁻ 45 (q11 c4) ∷
   rw⁻ 44 (q10 c4) ∷
   rw⁻ 43 (q11 c4) ∷
   rw⁻ 42 (q10 c4) ∷
   rw⁻ 41 (q10 c4) ∷
   rw⁻ 40 (q10 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 38 (q10 c4) ∷
   rw⁻ 37 (q10 c4) ∷
   rw⁻ 36 (q10 c4) ∷
   rw 52 (q9 c4) ∷
   rw⁻ 51 (q12 c4) ∷
   rw⁻ 50 (q12 c4) ∷
   rw⁻ 49 (q10 c4) ∷
   rw⁻ 48 (q11 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 46 (q11 c4) ∷
   rw⁻ 45 (q10 c4) ∷
   rw⁻ 44 (q10 c4) ∷
   rw⁻ 43 (q10 c4) ∷
   rw⁻ 42 (q10 c4) ∷
   rw⁻ 41 (q10 c4) ∷
   rw⁻ 40 (q10 c4) ∷
   rw⁻ 39 (q10 c4) ∷
   rw⁻ 56 (q13 c4) ∷
   rw⁻ 55 (q14 c4) ∷
   rw⁻ 54 (q14 c4) ∷
   rw⁻ 53 (q14 c4) ∷
   rw⁻ 52 (q15 c4) ∷
   rw⁻ 51 (q16 c4) ∷
   rw⁻ 50 (q15 c4) ∷
   rw⁻ 49 (q16 c4) ∷
   rw⁻ 48 (q15 c4) ∷
   rw⁻ 47 (q15 c4) ∷
   rw⁻ 46 (q15 c4) ∷
   rw⁻ 45 (q15 c4) ∷
   rw⁻ 44 (q15 c4) ∷
   rw⁻ 43 (q15 c4) ∷
   rw⁻ 42 (q15 c4) ∷
   rw 60 (q9 c4) ∷
   rw⁻ 59 (q17 c4) ∷
   rw⁻ 58 (q12 c4) ∷
   rw⁻ 57 (q12 c4) ∷
   rw⁻ 56 (q12 c4) ∷
   rw⁻ 55 (q10 c4) ∷
   rw⁻ 54 (q11 c4) ∷
   rw⁻ 53 (q10 c4) ∷
   rw⁻ 52 (q11 c4) ∷
   rw⁻ 51 (q10 c4) ∷
   rw⁻ 50 (q10 c4) ∷
   rw⁻ 49 (q10 c4) ∷
   rw⁻ 48 (q10 c4) ∷
   rw⁻ 47 (q10 c4) ∷
   rw⁻ 46 (q10 c4) ∷
   rw⁻ 45 (q10 c4) ∷ []) Eq.refl

private
  q18 : Ws → Eqn
  q18 c4 = sE 1584 (lem-F4-CS2-I-at02132031 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 1777 (lem-F4-CS2-S2-at02132031 c4)

-- deb-AD-split-b @02132031: 66 steps
lem-deb-AD-split-b-at02132031 : Ws → ⟪ (ℓ "丨丒丨丒丨上上上一丨丨") ⟫ʷ ≈ ⟪ (ℓ "並俄並並亄並並俄並並亄並並俄並並丽並並丽並並丽並並丢並並俄並並俄並俄亄俄亄俄丽丽丽丢俄俄") ⟫ʷ
lem-deb-AD-split-b-at02132031 c4 = derive (ℓ "丨丒丨丒丨上上上一丨丨") (ℓ "並俄並並亄並並俄並並亄並並俄並並丽並並丽並並丽並並丢並並俄並並俄並俄亄俄亄俄丽丽丽丢俄俄")
  (rw⁻ 0 (q3 c4) ∷
   rw 4 (q5 c4) ∷
   rw⁻ 3 (q6 c4) ∷
   rw⁻ 8 (q3 c4) ∷
   rw⁻ 7 (q7 c4) ∷
   rw⁻ 6 (q4 c4) ∷
   rw 12 (q5 c4) ∷
   rw⁻ 11 (q6 c4) ∷
   rw⁻ 10 (q8 c4) ∷
   rw⁻ 9 (q6 c4) ∷
   rw⁻ 16 (q3 c4) ∷
   rw⁻ 15 (q7 c4) ∷
   rw⁻ 14 (q4 c4) ∷
   rw⁻ 13 (q7 c4) ∷
   rw⁻ 12 (q4 c4) ∷
   rw 20 (q9 c4) ∷
   rw⁻ 19 (q10 c4) ∷
   rw⁻ 18 (q11 c4) ∷
   rw⁻ 17 (q10 c4) ∷
   rw⁻ 16 (q11 c4) ∷
   rw⁻ 15 (q10 c4) ∷
   rw 24 (q9 c4) ∷
   rw⁻ 23 (q12 c4) ∷
   rw⁻ 22 (q10 c4) ∷
   rw⁻ 21 (q11 c4) ∷
   rw⁻ 20 (q10 c4) ∷
   rw⁻ 19 (q11 c4) ∷
   rw⁻ 18 (q10 c4) ∷
   rw 28 (q9 c4) ∷
   rw⁻ 27 (q12 c4) ∷
   rw⁻ 26 (q12 c4) ∷
   rw⁻ 25 (q10 c4) ∷
   rw⁻ 24 (q11 c4) ∷
   rw⁻ 23 (q10 c4) ∷
   rw⁻ 22 (q11 c4) ∷
   rw⁻ 21 (q10 c4) ∷
   rw⁻ 32 (q13 c4) ∷
   rw⁻ 31 (q14 c4) ∷
   rw⁻ 30 (q14 c4) ∷
   rw⁻ 29 (q14 c4) ∷
   rw⁻ 28 (q15 c4) ∷
   rw⁻ 27 (q16 c4) ∷
   rw⁻ 26 (q15 c4) ∷
   rw⁻ 25 (q16 c4) ∷
   rw⁻ 24 (q15 c4) ∷
   rw⁻ 36 (q3 c4) ∷
   rw⁻ 35 (q18 c4) ∷
   rw⁻ 34 (q19 c4) ∷
   rw⁻ 33 (q19 c4) ∷
   rw⁻ 32 (q19 c4) ∷
   rw⁻ 31 (q4 c4) ∷
   rw⁻ 30 (q7 c4) ∷
   rw⁻ 29 (q4 c4) ∷
   rw⁻ 28 (q7 c4) ∷
   rw⁻ 27 (q4 c4) ∷
   rw⁻ 40 (q3 c4) ∷
   rw⁻ 39 (q4 c4) ∷
   rw⁻ 38 (q18 c4) ∷
   rw⁻ 37 (q19 c4) ∷
   rw⁻ 36 (q19 c4) ∷
   rw⁻ 35 (q19 c4) ∷
   rw⁻ 34 (q4 c4) ∷
   rw⁻ 33 (q7 c4) ∷
   rw⁻ 32 (q4 c4) ∷
   rw⁻ 31 (q7 c4) ∷
   rw⁻ 30 (q4 c4) ∷ []) Eq.refl
