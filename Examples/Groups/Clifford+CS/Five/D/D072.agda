{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD072 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D072 (Sᴰ : SD072) where

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
  lem-F4-I-S2 : Ws → St 1595
  lem-F4-I-S2 = pickᴰ 0 Sᴰ
  lem-F4-I-S3 : Ws → St 1564
  lem-F4-I-S3 = pickᴰ 1 Sᴰ
  lem-F4-K2-S2 : Ws → St 1767
  lem-F4-K2-S2 = pickᴰ 2 Sᴰ
  lem-F4-K3-S3 : Ws → St 1768
  lem-F4-K3-S3 = pickᴰ 3 Sᴰ
  lem-F4-S2-S3 : Ws → St 1769
  lem-F4-S2-S3 = pickᴰ 4 Sᴰ
  lem-F4-S3-S2 : Ws → St 1770
  lem-F4-S3-S2 = pickᴰ 5 Sᴰ
  lem-F4-I-S2-at02132031 : Ws → St 1771
  lem-F4-I-S2-at02132031 = pickᴰ 6 Sᴰ
  lem-F4-I-S2-at132132 : Ws → St 1772
  lem-F4-I-S2-at132132 = pickᴰ 7 Sᴰ
  lem-F4-K2-S2-at02132031 : Ws → St 1773
  lem-F4-K2-S2-at02132031 = pickᴰ 8 Sᴰ
  lem-F4-K2-S2-at132132 : Ws → St 1774
  lem-F4-K2-S2-at132132 = pickᴰ 9 Sᴰ
  lem-F4-S3-S2-at02132031 : Ws → St 1775
  lem-F4-S3-S2-at02132031 = pickᴰ 10 Sᴰ
  lem-F4-S3-S2-at132132 : Ws → St 1776
  lem-F4-S3-S2-at132132 = pickᴰ 11 Sᴰ
  lem-F4-CS2-S2 : Ws → St 1606
  lem-F4-CS2-S2 = pickᴰ 12 Sᴰ
  lem-F4-CS2-S3 : Ws → St 1577
  lem-F4-CS2-S3 = pickᴰ 13 Sᴰ
  lem-F4-CS2-S2-at02132031 : Ws → St 1777
  lem-F4-CS2-S2-at02132031 = pickᴰ 14 Sᴰ
  lem-F4-CS2-S2-at132132 : Ws → St 1778
  lem-F4-CS2-S2-at132132 = pickᴰ 15 Sᴰ
  lem-deb-P-hi-split-a : Ws → St 1779
  lem-deb-P-hi-split-a = pickᴰ 16 Sᴰ
  lem-deb-P-hi-split-a-at02132031 : Ws → St 1780
  lem-deb-P-hi-split-a-at02132031 = pickᴰ 17 Sᴰ
  lem-deb-P-hi-split-b : Ws → St 1781
  lem-deb-P-hi-split-b = pickᴰ 18 Sᴰ
  lem-deb-P-hi-split-b-at02132031 : Ws → St 1782
  lem-deb-P-hi-split-b-at02132031 = pickᴰ 19 Sᴰ
  lem-deb-P-hi-split-a-at132132 : Ws → St 1783
  lem-deb-P-hi-split-a-at132132 = pickᴰ 20 Sᴰ
  lem-deb-P-hi-split-b-at132132 : Ws → St 1784
  lem-deb-P-hi-split-b-at132132 = pickᴰ 21 Sᴰ
  lem-deb-P-lo-split-a : Ws → St 1785
  lem-deb-P-lo-split-a = pickᴰ 22 Sᴰ
  lem-deb-P-lo-split-b : Ws → St 1786
  lem-deb-P-lo-split-b = pickᴰ 23 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1770 (lem-F4-S3-S2 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 1606 (lem-F4-CS2-S2 c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1767 (lem-F4-K2-S2 c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1595 (lem-F4-I-S2 c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1779 (lem-deb-P-hi-split-a c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1781 (lem-deb-P-hi-split-b c4)

-- deb-P-hi part1: 32 steps
lem-deb-P-hi-part1 : Ws → ⟪ (ℓ "亇亰並侬並並侬並並侬並並侬並並侬並並侬並並侬並並亇並並侬並並亇並並侬並並乹並並乹並並乹並並丢並並乹並侬侬侬侬侬侬侬亇侬亇侬乹乹乹丢乹乩乩乩乩乩乩並侬並並亇並並侬並並亇並並侬並並乹並並乹並並乹並乩並丢並並侬並並侬並乩乩侬亇侬亇侬乹乹乹丢侬侬乩乩乩") ⟫ʷ ≈ ⟪ (ℓ "亇亰乢乢乢乢乢乢乢丘乢丘乢东东东一东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东一乢乢乩乩乩") ⟫ʷ
lem-deb-P-hi-part1 c4 = derive (ℓ "亇亰並侬並並侬並並侬並並侬並並侬並並侬並並侬並並亇並並侬並並亇並並侬並並乹並並乹並並乹並並丢並並乹並侬侬侬侬侬侬侬亇侬亇侬乹乹乹丢乹乩乩乩乩乩乩並侬並並亇並並侬並並亇並並侬並並乹並並乹並並乹並乩並丢並並侬並並侬並乩乩侬亇侬亇侬乹乹乹丢侬侬乩乩乩") (ℓ "亇亰乢乢乢乢乢乢乢丘乢丘乢东东东一东乩乩乩乩乩乩乩乩乩乢丘乢丘乢东东东一乢乢乩乩乩")
  (rw 93 (q1 c4) ∷
   rw 90 (q1 c4) ∷
   rw 87 (q1 c4) ∷
   rw 84 (q2 c4) ∷
   rw 81 (q3 c4) ∷
   rw 78 (q2 c4) ∷
   rw 75 (q3 c4) ∷
   rw 72 (q2 c4) ∷
   rw 103 (q2 c4) ∷
   rw 100 (q2 c4) ∷
   rw 97 (q4 c4) ∷
   rw 94 (q1 c4) ∷
   rw 91 (q1 c4) ∷
   rw 88 (q1 c4) ∷
   rw 85 (q2 c4) ∷
   rw 82 (q3 c4) ∷
   rw 79 (q2 c4) ∷
   rw 76 (q3 c4) ∷
   rw 73 (q2 c4) ∷
   rw 104 (q2 c4) ∷
   rw 101 (q2 c4) ∷
   rw 98 (q4 c4) ∷
   rw 95 (q1 c4) ∷
   rw 92 (q1 c4) ∷
   rw 89 (q1 c4) ∷
   rw 86 (q2 c4) ∷
   rw 83 (q3 c4) ∷
   rw 80 (q2 c4) ∷
   rw 77 (q3 c4) ∷
   rw 74 (q2 c4) ∷
   rw⁻ 2 (q5 c4) ∷
   rw⁻ 27 (q6 c4) ∷ []) Eq.refl

private
  q7 : Ws → Eqn
  q7 c4 = sE 1777 (lem-F4-CS2-S2-at02132031 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 1771 (lem-F4-I-S2-at02132031 c4)
  q9 : Ws → Eqn
  q9 c4 = sE 1775 (lem-F4-S3-S2-at02132031 c4)
  q10 : Ws → Eqn
  q10 c4 = sE 1773 (lem-F4-K2-S2-at02132031 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 1780 (lem-deb-P-hi-split-a-at02132031 c4)
  q12 : Ws → Eqn
  q12 c4 = sE 1782 (lem-deb-P-hi-split-b-at02132031 c4)

-- deb-P-hi @02132031 part1: 100 steps
lem-deb-P-hi-at02132031-part1 : Ws → ⟪ (ℓ "亁五並俄並並俄並並俄並並俄並並俄並並俄並並俄並並亁並並俄並並亁並並俄並並乕並並乕並並乕並並丢並並乕並俄俄俄俄俄俄俄亁俄亁俄乕乕乕丢乕並俄並並亁並並俄並並亁並並俄並並乕並並乕並並乕並並丢並並俄並丽並俄並丽丽丽丽丽丽丽丽俄亁俄亁俄乕乕乕丢俄俄丽丽丽") ⟫ʷ ≈ ⟪ (ℓ "亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽") ⟫ʷ
lem-deb-P-hi-at02132031-part1 c4 = derive (ℓ "亁五並俄並並俄並並俄並並俄並並俄並並俄並並俄並並亁並並俄並並亁並並俄並並乕並並乕並並乕並並丢並並乕並俄俄俄俄俄俄俄亁俄亁俄乕乕乕丢乕並俄並並亁並並俄並並亁並並俄並並乕並並乕並並乕並並丢並並俄並丽並俄並丽丽丽丽丽丽丽丽俄亁俄亁俄乕乕乕丢俄俄丽丽丽") (ℓ "亁五丨丨丨丨丨丨丨丌丨丌丨丐丐丐一丐丽丽丽丽丽丽丽丽丽丨丌丨丌丨丐丐丐一丨丨丽丽丽")
  (rw 93 (q7 c4) ∷
   rw 90 (q8 c4) ∷
   rw 87 (q9 c4) ∷
   rw 84 (q9 c4) ∷
   rw 81 (q9 c4) ∷
   rw 78 (q7 c4) ∷
   rw 75 (q10 c4) ∷
   rw 72 (q7 c4) ∷
   rw 69 (q10 c4) ∷
   rw 66 (q7 c4) ∷
   rw 97 (q7 c4) ∷
   rw 94 (q7 c4) ∷
   rw 91 (q8 c4) ∷
   rw 88 (q9 c4) ∷
   rw 85 (q9 c4) ∷
   rw 82 (q9 c4) ∷
   rw 79 (q7 c4) ∷
   rw 76 (q10 c4) ∷
   rw 73 (q7 c4) ∷
   rw 70 (q10 c4) ∷
   rw 67 (q7 c4) ∷
   rw 98 (q7 c4) ∷
   rw 95 (q7 c4) ∷
   rw 92 (q8 c4) ∷
   rw 89 (q9 c4) ∷
   rw 86 (q9 c4) ∷
   rw 83 (q9 c4) ∷
   rw 80 (q7 c4) ∷
   rw 77 (q10 c4) ∷
   rw 74 (q7 c4) ∷
   rw 71 (q10 c4) ∷
   rw 68 (q7 c4) ∷
   rw 99 (q7 c4) ∷
   rw 96 (q7 c4) ∷
   rw 93 (q8 c4) ∷
   rw 90 (q9 c4) ∷
   rw 87 (q9 c4) ∷
   rw 84 (q9 c4) ∷
   rw 81 (q7 c4) ∷
   rw 78 (q10 c4) ∷
   rw 75 (q7 c4) ∷
   rw 72 (q10 c4) ∷
   rw 69 (q7 c4) ∷
   rw 100 (q7 c4) ∷
   rw 97 (q7 c4) ∷
   rw 94 (q8 c4) ∷
   rw 91 (q9 c4) ∷
   rw 88 (q9 c4) ∷
   rw 85 (q9 c4) ∷
   rw 82 (q7 c4) ∷
   rw 79 (q10 c4) ∷
   rw 76 (q7 c4) ∷
   rw 73 (q10 c4) ∷
   rw 70 (q7 c4) ∷
   rw 101 (q7 c4) ∷
   rw 98 (q7 c4) ∷
   rw 95 (q8 c4) ∷
   rw 92 (q9 c4) ∷
   rw 89 (q9 c4) ∷
   rw 86 (q9 c4) ∷
   rw 83 (q7 c4) ∷
   rw 80 (q10 c4) ∷
   rw 77 (q7 c4) ∷
   rw 74 (q10 c4) ∷
   rw 71 (q7 c4) ∷
   rw 102 (q7 c4) ∷
   rw 99 (q7 c4) ∷
   rw 96 (q8 c4) ∷
   rw 93 (q9 c4) ∷
   rw 90 (q9 c4) ∷
   rw 87 (q9 c4) ∷
   rw 84 (q7 c4) ∷
   rw 81 (q10 c4) ∷
   rw 78 (q7 c4) ∷
   rw 75 (q10 c4) ∷
   rw 72 (q7 c4) ∷
   rw 103 (q7 c4) ∷
   rw 100 (q7 c4) ∷
   rw 97 (q8 c4) ∷
   rw 94 (q9 c4) ∷
   rw 91 (q9 c4) ∷
   rw 88 (q9 c4) ∷
   rw 85 (q7 c4) ∷
   rw 82 (q10 c4) ∷
   rw 79 (q7 c4) ∷
   rw 76 (q10 c4) ∷
   rw 73 (q7 c4) ∷
   rw 104 (q7 c4) ∷
   rw 101 (q7 c4) ∷
   rw 98 (q8 c4) ∷
   rw 95 (q9 c4) ∷
   rw 92 (q9 c4) ∷
   rw 89 (q9 c4) ∷
   rw 86 (q7 c4) ∷
   rw 83 (q10 c4) ∷
   rw 80 (q7 c4) ∷
   rw 77 (q10 c4) ∷
   rw 74 (q7 c4) ∷
   rw⁻ 2 (q11 c4) ∷
   rw⁻ 27 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = sE 1776 (lem-F4-S3-S2-at132132 c4)
  q14 : Ws → Eqn
  q14 c4 = sE 1778 (lem-F4-CS2-S2-at132132 c4)
  q15 : Ws → Eqn
  q15 c4 = sE 1774 (lem-F4-K2-S2-at132132 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 1772 (lem-F4-I-S2-at132132 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1783 (lem-deb-P-hi-split-a-at132132 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1784 (lem-deb-P-hi-split-b-at132132 c4)

-- deb-P-hi @132132 part1: 64 steps
lem-deb-P-hi-at132132-part1 : Ws → ⟪ (ℓ "亄亨並侧並並侧並並侧並並侧並並侧並並侧並並侧並並亄並並侧並並亄並並侧並並乩並並乩並並乩並並丢並並乩並侧侧侧侧侧侧侧亄侧亄侧乩乩乩丢乩乕乕乕並侧並並亄並並侧並並亄並並侧並並乩並並乩並乕並乩並並丢並並侧並並侧並乕乕乕乕乕侧亄侧亄侧乩乩乩丢侧侧乕乕乕") ⟫ʷ ≈ ⟪ (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕") ⟫ʷ
lem-deb-P-hi-at132132-part1 c4 = derive (ℓ "亄亨並侧並並侧並並侧並並侧並並侧並並侧並並侧並並亄並並侧並並亄並並侧並並乩並並乩並並乩並並丢並並乩並侧侧侧侧侧侧侧亄侧亄侧乩乩乩丢乩乕乕乕並侧並並亄並並侧並並亄並並侧並並乩並並乩並乕並乩並並丢並並侧並並侧並乕乕乕乕乕侧亄侧亄侧乩乩乩丢侧侧乕乕乕") (ℓ "亄亨乇乇乇乇乇乇乇丒乇丒乇世世世一世乕乕乕乕乕乕乕乕乕乇丒乇丒乇世世世一乇乇乕乕乕")
  (rw 87 (q13 c4) ∷
   rw 84 (q13 c4) ∷
   rw 81 (q14 c4) ∷
   rw 78 (q15 c4) ∷
   rw 75 (q14 c4) ∷
   rw 72 (q15 c4) ∷
   rw 69 (q14 c4) ∷
   rw 100 (q14 c4) ∷
   rw 97 (q14 c4) ∷
   rw 94 (q16 c4) ∷
   rw 91 (q13 c4) ∷
   rw 88 (q13 c4) ∷
   rw 85 (q13 c4) ∷
   rw 82 (q14 c4) ∷
   rw 79 (q15 c4) ∷
   rw 76 (q14 c4) ∷
   rw 73 (q15 c4) ∷
   rw 70 (q14 c4) ∷
   rw 101 (q14 c4) ∷
   rw 98 (q14 c4) ∷
   rw 95 (q16 c4) ∷
   rw 92 (q13 c4) ∷
   rw 89 (q13 c4) ∷
   rw 86 (q13 c4) ∷
   rw 83 (q14 c4) ∷
   rw 80 (q15 c4) ∷
   rw 77 (q14 c4) ∷
   rw 74 (q15 c4) ∷
   rw 71 (q14 c4) ∷
   rw 102 (q14 c4) ∷
   rw 99 (q14 c4) ∷
   rw 96 (q16 c4) ∷
   rw 93 (q13 c4) ∷
   rw 90 (q13 c4) ∷
   rw 87 (q13 c4) ∷
   rw 84 (q14 c4) ∷
   rw 81 (q15 c4) ∷
   rw 78 (q14 c4) ∷
   rw 75 (q15 c4) ∷
   rw 72 (q14 c4) ∷
   rw 103 (q14 c4) ∷
   rw 100 (q14 c4) ∷
   rw 97 (q16 c4) ∷
   rw 94 (q13 c4) ∷
   rw 91 (q13 c4) ∷
   rw 88 (q13 c4) ∷
   rw 85 (q14 c4) ∷
   rw 82 (q15 c4) ∷
   rw 79 (q14 c4) ∷
   rw 76 (q15 c4) ∷
   rw 73 (q14 c4) ∷
   rw 104 (q14 c4) ∷
   rw 101 (q14 c4) ∷
   rw 98 (q16 c4) ∷
   rw 95 (q13 c4) ∷
   rw 92 (q13 c4) ∷
   rw 89 (q13 c4) ∷
   rw 86 (q14 c4) ∷
   rw 83 (q15 c4) ∷
   rw 80 (q14 c4) ∷
   rw 77 (q15 c4) ∷
   rw 74 (q14 c4) ∷
   rw⁻ 2 (q17 c4) ∷
   rw⁻ 27 (q18 c4) ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = sE 1769 (lem-F4-S2-S3 c4)
  q20 : Ws → Eqn
  q20 c4 = sE 1577 (lem-F4-CS2-S3 c4)
  q21 : Ws → Eqn
  q21 c4 = sE 1768 (lem-F4-K3-S3 c4)
  q22 : Ws → Eqn
  q22 c4 = sE 1564 (lem-F4-I-S3 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 1785 (lem-deb-P-lo-split-a c4)
  q24 : Ws → Eqn
  q24 c4 = sE 1786 (lem-deb-P-lo-split-b c4)

-- deb-P-lo part1: 32 steps
lem-deb-P-lo-part1 : Ws → ⟪ (ℓ "亊亰並侬並並侬並並侬並並侬並並侬並並侬並並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並侬侬侬侬侬侬侬亊侬亊侬乩乩乩丢乩乹乹乹乹乹乹並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並乹並丢並並侬並並侬並乹乹侬亊侬亊侬乩乩乩丢侬侬乹乹乹") ⟫ʷ ≈ ⟪ (ℓ "亊亰乢乢乢乢乢乢乢丞乢丞乢世世世一世乹乹乹乹乹乹乹乹乹乢丞乢丞乢世世世一乢乢乹乹乹") ⟫ʷ
lem-deb-P-lo-part1 c4 = derive (ℓ "亊亰並侬並並侬並並侬並並侬並並侬並並侬並並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並並丢並並乩並侬侬侬侬侬侬侬亊侬亊侬乩乩乩丢乩乹乹乹乹乹乹並侬並並亊並並侬並並亊並並侬並並乩並並乩並並乩並乹並丢並並侬並並侬並乹乹侬亊侬亊侬乩乩乩丢侬侬乹乹乹") (ℓ "亊亰乢乢乢乢乢乢乢丞乢丞乢世世世一世乹乹乹乹乹乹乹乹乹乢丞乢丞乢世世世一乢乢乹乹乹")
  (rw 93 (q19 c4) ∷
   rw 90 (q19 c4) ∷
   rw 87 (q19 c4) ∷
   rw 84 (q20 c4) ∷
   rw 81 (q21 c4) ∷
   rw 78 (q20 c4) ∷
   rw 75 (q21 c4) ∷
   rw 72 (q20 c4) ∷
   rw 103 (q20 c4) ∷
   rw 100 (q20 c4) ∷
   rw 97 (q22 c4) ∷
   rw 94 (q19 c4) ∷
   rw 91 (q19 c4) ∷
   rw 88 (q19 c4) ∷
   rw 85 (q20 c4) ∷
   rw 82 (q21 c4) ∷
   rw 79 (q20 c4) ∷
   rw 76 (q21 c4) ∷
   rw 73 (q20 c4) ∷
   rw 104 (q20 c4) ∷
   rw 101 (q20 c4) ∷
   rw 98 (q22 c4) ∷
   rw 95 (q19 c4) ∷
   rw 92 (q19 c4) ∷
   rw 89 (q19 c4) ∷
   rw 86 (q20 c4) ∷
   rw 83 (q21 c4) ∷
   rw 80 (q20 c4) ∷
   rw 77 (q21 c4) ∷
   rw 74 (q20 c4) ∷
   rw⁻ 2 (q23 c4) ∷
   rw⁻ 27 (q24 c4) ∷ []) Eq.refl
