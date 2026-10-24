{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD152 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D152 (Sᴰ : SD152) where

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
  lem-F4-I-I-at02132031 : Ws → St 1981
  lem-F4-I-I-at02132031 = pickᴰ 0 Sᴰ
  lem-F4-I-S2-at02132031 : Ws → St 1771
  lem-F4-I-S2-at02132031 = pickᴰ 1 Sᴰ
  lem-F4-I-S3-at02132031 : Ws → St 1570
  lem-F4-I-S3-at02132031 = pickᴰ 2 Sᴰ
  lem-F4-K3-I-at02132031 : Ws → St 1982
  lem-F4-K3-I-at02132031 = pickᴰ 3 Sᴰ
  lem-F4-K3-S2-at02132031 : Ws → St 1983
  lem-F4-K3-S2-at02132031 = pickᴰ 4 Sᴰ
  lem-F4-K3-S3-at02132031 : Ws → St 1959
  lem-F4-K3-S3-at02132031 = pickᴰ 5 Sᴰ
  lem-F4-S2-I-at02132031 : Ws → St 1791
  lem-F4-S2-I-at02132031 = pickᴰ 6 Sᴰ
  lem-F4-S2-S2-at02132031 : Ws → St 1795
  lem-F4-S2-S2-at02132031 = pickᴰ 7 Sᴰ
  lem-F4-S2-S3-at02132031 : Ws → St 1961
  lem-F4-S2-S3-at02132031 = pickᴰ 8 Sᴰ
  lem-F4-CS2-I-at02132031 : Ws → St 1584
  lem-F4-CS2-I-at02132031 = pickᴰ 9 Sᴰ
  lem-F4-CS2-S2-at02132031 : Ws → St 1777
  lem-F4-CS2-S2-at02132031 = pickᴰ 10 Sᴰ
  lem-F4-CS2-S3-at02132031 : Ws → St 1586
  lem-F4-CS2-S3-at02132031 = pickᴰ 11 Sᴰ
  lem-deb-AD-split-a-at02132031 : Ws → St 1984
  lem-deb-AD-split-a-at02132031 = pickᴰ 12 Sᴰ
  lem-deb-AD-split-b-at02132031 : Ws → St 1985
  lem-deb-AD-split-b-at02132031 = pickᴰ 13 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1983 (lem-F4-K3-S2-at02132031 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1777 (lem-F4-CS2-S2-at02132031 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1771 (lem-F4-I-S2-at02132031 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1795 (lem-F4-S2-S2-at02132031 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1584 (lem-F4-CS2-I-at02132031 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1981 (lem-F4-I-I-at02132031 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 1791 (lem-F4-S2-I-at02132031 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1982 (lem-F4-K3-I-at02132031 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1586 (lem-F4-CS2-S3-at02132031 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1570 (lem-F4-I-S3-at02132031 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1961 (lem-F4-S2-S3-at02132031 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1959 (lem-F4-K3-S3-at02132031 c4)
  q13 : Ws → Eqn
  q13 c4 = sE 1984 (lem-deb-AD-split-a-at02132031 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1985 (lem-deb-AD-split-b-at02132031 c4)

-- deb-AD @02132031 part1: 138 steps
lem-deb-AD-at02132031-part1 : Ws → ⟪ (ℓ "亄乕五並俄並並俄並並俄並並俄並並俄並並俄並並俄並並亄並並俄並並亄並並俄並並丽並並丽並並丽並並丢並並丽並俄俄俄俄俄俄俄亄俄亄俄丽並俄並並亄並並俄並並亄並丽並俄並並丽並並丽並並丽並並丢並並俄並並俄並丽丢丽乕乕乕乕乕乕乕乕乕俄亄俄亄俄丽丽丽丢俄俄乕乕乕") ⟫ʷ ≈ ⟪ (ℓ "亄乕五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕") ⟫ʷ
lem-deb-AD-at02132031-part1 c4 = derive (ℓ "亄乕五並俄並並俄並並俄並並俄並並俄並並俄並並俄並並亄並並俄並並亄並並俄並並丽並並丽並並丽並並丢並並丽並俄俄俄俄俄俄俄亄俄亄俄丽並俄並並亄並並俄並並亄並丽並俄並並丽並並丽並並丽並並丢並並俄並並俄並丽丢丽乕乕乕乕乕乕乕乕乕俄亄俄亄俄丽丽丽丢俄俄乕乕乕") (ℓ "亄乕五丨丨丨丨丨丨丨丒丨丒丨上上上一上乕乕乕乕乕乕乕乕乕丨丒丨丒丨上上上一丨丨乕乕乕")
  (rw 72 (q1 c4) ∷
   rw 69 (q2 c4) ∷
   rw 66 (q1 c4) ∷
   rw 63 (q2 c4) ∷
   rw 94 (q2 c4) ∷
   rw 91 (q2 c4) ∷
   rw 88 (q3 c4) ∷
   rw 85 (q4 c4) ∷
   rw 82 (q4 c4) ∷
   rw 79 (q4 c4) ∷
   rw 76 (q2 c4) ∷
   rw 73 (q1 c4) ∷
   rw 70 (q2 c4) ∷
   rw 67 (q1 c4) ∷
   rw 64 (q2 c4) ∷
   rw 95 (q5 c4) ∷
   rw 92 (q5 c4) ∷
   rw 89 (q6 c4) ∷
   rw 86 (q7 c4) ∷
   rw 83 (q7 c4) ∷
   rw 80 (q7 c4) ∷
   rw 77 (q5 c4) ∷
   rw 74 (q8 c4) ∷
   rw 71 (q5 c4) ∷
   rw 68 (q8 c4) ∷
   rw 65 (q5 c4) ∷
   rw 96 (q2 c4) ∷
   rw 93 (q2 c4) ∷
   rw 90 (q3 c4) ∷
   rw 87 (q4 c4) ∷
   rw 84 (q4 c4) ∷
   rw 81 (q4 c4) ∷
   rw 78 (q2 c4) ∷
   rw 75 (q1 c4) ∷
   rw 72 (q2 c4) ∷
   rw 69 (q1 c4) ∷
   rw 66 (q2 c4) ∷
   rw 97 (q9 c4) ∷
   rw 94 (q9 c4) ∷
   rw 91 (q10 c4) ∷
   rw 88 (q11 c4) ∷
   rw 85 (q11 c4) ∷
   rw 82 (q11 c4) ∷
   rw 79 (q9 c4) ∷
   rw 76 (q12 c4) ∷
   rw 73 (q9 c4) ∷
   rw 70 (q12 c4) ∷
   rw 67 (q9 c4) ∷
   rw 98 (q9 c4) ∷
   rw 95 (q9 c4) ∷
   rw 92 (q10 c4) ∷
   rw 89 (q11 c4) ∷
   rw 86 (q11 c4) ∷
   rw 83 (q11 c4) ∷
   rw 80 (q9 c4) ∷
   rw 77 (q12 c4) ∷
   rw 74 (q9 c4) ∷
   rw 71 (q12 c4) ∷
   rw 68 (q9 c4) ∷
   rw 99 (q9 c4) ∷
   rw 96 (q9 c4) ∷
   rw 93 (q10 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q11 c4) ∷
   rw 84 (q11 c4) ∷
   rw 81 (q9 c4) ∷
   rw 78 (q12 c4) ∷
   rw 75 (q9 c4) ∷
   rw 72 (q12 c4) ∷
   rw 69 (q9 c4) ∷
   rw 100 (q9 c4) ∷
   rw 97 (q9 c4) ∷
   rw 94 (q10 c4) ∷
   rw 91 (q11 c4) ∷
   rw 88 (q11 c4) ∷
   rw 85 (q11 c4) ∷
   rw 82 (q9 c4) ∷
   rw 79 (q12 c4) ∷
   rw 76 (q9 c4) ∷
   rw 73 (q12 c4) ∷
   rw 70 (q9 c4) ∷
   rw 101 (q9 c4) ∷
   rw 98 (q9 c4) ∷
   rw 95 (q10 c4) ∷
   rw 92 (q11 c4) ∷
   rw 89 (q11 c4) ∷
   rw 86 (q11 c4) ∷
   rw 83 (q9 c4) ∷
   rw 80 (q12 c4) ∷
   rw 77 (q9 c4) ∷
   rw 74 (q12 c4) ∷
   rw 71 (q9 c4) ∷
   rw 102 (q9 c4) ∷
   rw 99 (q9 c4) ∷
   rw 96 (q10 c4) ∷
   rw 93 (q11 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q11 c4) ∷
   rw 84 (q9 c4) ∷
   rw 81 (q12 c4) ∷
   rw 78 (q9 c4) ∷
   rw 75 (q12 c4) ∷
   rw 72 (q9 c4) ∷
   rw 103 (q9 c4) ∷
   rw 100 (q9 c4) ∷
   rw 97 (q10 c4) ∷
   rw 94 (q11 c4) ∷
   rw 91 (q11 c4) ∷
   rw 88 (q11 c4) ∷
   rw 85 (q9 c4) ∷
   rw 82 (q12 c4) ∷
   rw 79 (q9 c4) ∷
   rw 76 (q12 c4) ∷
   rw 73 (q9 c4) ∷
   rw 104 (q9 c4) ∷
   rw 101 (q9 c4) ∷
   rw 98 (q10 c4) ∷
   rw 95 (q11 c4) ∷
   rw 92 (q11 c4) ∷
   rw 89 (q11 c4) ∷
   rw 86 (q9 c4) ∷
   rw 83 (q12 c4) ∷
   rw 80 (q9 c4) ∷
   rw 77 (q12 c4) ∷
   rw 74 (q9 c4) ∷
   rw 105 (q9 c4) ∷
   rw 102 (q9 c4) ∷
   rw 99 (q10 c4) ∷
   rw 96 (q11 c4) ∷
   rw 93 (q11 c4) ∷
   rw 90 (q11 c4) ∷
   rw 87 (q9 c4) ∷
   rw 84 (q12 c4) ∷
   rw 81 (q9 c4) ∷
   rw 78 (q12 c4) ∷
   rw 75 (q9 c4) ∷
   rw⁻ 3 (q13 c4) ∷
   rw⁻ 28 (q14 c4) ∷ []) Eq.refl
