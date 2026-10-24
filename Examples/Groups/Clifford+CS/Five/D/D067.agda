{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD067 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D067 (Sᴰ : SD067) where

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
  lem-comm-CS13-CCZ024 : Ws → St 958
  lem-comm-CS13-CCZ024 = pickᴰ 0 Sᴰ
  lem-comm-CS24-CCZ013 : Ws → St 194
  lem-comm-CS24-CCZ013 = pickᴰ 1 Sᴰ
  lem-comm-CSd13-CCZ024 : Ws → St 960
  lem-comm-CSd13-CCZ024 = pickᴰ 2 Sᴰ
  lem-comm-CSd24-CCZ013 : Ws → St 204
  lem-comm-CSd24-CCZ013 = pickᴰ 3 Sᴰ
  lem-comm-CX04-TOFF213 : Ws → St 1023
  lem-comm-CX04-TOFF213 = pickᴰ 4 Sᴰ
  lem-comm-CX12-CCZ034 : Ws → St 2
  lem-comm-CX12-CCZ034 = pickᴰ 5 Sᴰ
  lem-comm-CX13-CCZ024 : Ws → St 3
  lem-comm-CX13-CCZ024 = pickᴰ 6 Sᴰ
  lem-comm-CZ13-CCZ024 : Ws → St 67
  lem-comm-CZ13-CCZ024 = pickᴰ 7 Sᴰ
  lem-comm-TOFF013-CSd24 : Ws → St 210
  lem-comm-TOFF013-CSd24 = pickᴰ 8 Sᴰ
  lem-comm-CCZ014-CX23 : Ws → St 893
  lem-comm-CCZ014-CX23 = pickᴰ 9 Sᴰ
  lem-comm-CCZ024-CX13 : Ws → St 1024
  lem-comm-CCZ024-CX13 = pickᴰ 10 Sᴰ
  lem-comm-CCZ034-CS12 : Ws → St 1705
  lem-comm-CCZ034-CS12 = pickᴰ 11 Sᴰ
  lem-comm-CX04-TOFF312 : Ws → St 1025
  lem-comm-CX04-TOFF312 = pickᴰ 12 Sᴰ
  lem-comm-TOFF013-CS24 : Ws → St 1286
  lem-comm-TOFF013-CS24 = pickᴰ 13 Sᴰ
  lem-comm-TOFF013-CX24 : Ws → St 1059
  lem-comm-TOFF013-CX24 = pickᴰ 14 Sᴰ
  lem-comm-TOFF213-CX04 : Ws → St 1028
  lem-comm-TOFF213-CX04 = pickᴰ 15 Sᴰ
  lem-comm-TOFF023-CX14 : Ws → St 1060
  lem-comm-TOFF023-CX14 = pickᴰ 16 Sᴰ
  lem-inv-SBOX⟨2·0·41·3⟩ : Ws → St 1706
  lem-inv-SBOX⟨2·0·41·3⟩ = pickᴰ 17 Sᴰ
  lem-invr-SBOX⟨2·0·41·3⟩ : Ws → St 1707
  lem-invr-SBOX⟨2·0·41·3⟩ = pickᴰ 18 Sᴰ
  lem-box-tQ : Ws → St 247
  lem-box-tQ = pickᴰ 19 Sᴰ
  lem-box-tQ-at0330 : Ws → St 252
  lem-box-tQ-at0330 = pickᴰ 20 Sᴰ
  lem-box-cP-at032032 : Ws → St 868
  lem-box-cP-at032032 = pickᴰ 21 Sᴰ
  lem-box-cP-at04203243 : Ws → St 919
  lem-box-cP-at04203243 = pickᴰ 22 Sᴰ
  lem-box-cP-at0210243143 : Ws → St 994
  lem-box-cP-at0210243143 = pickᴰ 23 Sᴰ
  lem-box-cP-at0314203142 : Ws → St 997
  lem-box-cP-at0314203142 = pickᴰ 24 Sᴰ
  lem-box-cP-at122441 : Ws → St 1002
  lem-box-cP-at122441 = pickᴰ 25 Sᴰ
  lem-box-cP-at243243 : Ws → St 1008
  lem-box-cP-at243243 = pickᴰ 26 Sᴰ
  lem-box-perm-2314-at03102132 : Ws → St 1708
  lem-box-perm-2314-at03102132 = pickᴰ 27 Sᴰ
  lem-CSdu-box-3-at043043 : Ws → St 1239
  lem-CSdu-box-3-at043043 = pickᴰ 28 Sᴰ
  lem-CSu-box-3-at043043 : Ws → St 1709
  lem-CSu-box-3-at043043 = pickᴰ 29 Sᴰ
  lem-box-perm-1324-at043043 : Ws → St 1470
  lem-box-perm-1324-at043043 = pickᴰ 30 Sᴰ
  lem-box-perm-3124 : Ws → St 1710
  lem-box-perm-3124 = pickᴰ 31 Sᴰ
  lem-box-perm-3124-at0330 : Ws → St 1711
  lem-box-perm-3124-at0330 = pickᴰ 32 Sᴰ
  lem-box2-at043043 : Ws → St 1712
  lem-box2-at043043 = pickᴰ 33 Sᴰ
  lem-CSdu-box-3-at0210243143 : Ws → St 1510
  lem-CSdu-box-3-at0210243143 = pickᴰ 34 Sᴰ
  lem-CSdu-box-3-at0314213042 : Ws → St 1273
  lem-CSdu-box-3-at0314213042 = pickᴰ 35 Sᴰ
  lem-CSdu-box-3-at122441 : Ws → St 1511
  lem-CSdu-box-3-at122441 = pickᴰ 36 Sᴰ
  lem-CSu-box-3-at0210243143 : Ws → St 1512
  lem-CSu-box-3-at0210243143 = pickᴰ 37 Sᴰ
  lem-CSu-box-3-at0314213042 : Ws → St 1713
  lem-CSu-box-3-at0314213042 = pickᴰ 38 Sᴰ
  lem-CSu-box-3-at122441 : Ws → St 1513
  lem-CSu-box-3-at122441 = pickᴰ 39 Sᴰ
  lem-box-perm-1324-at0314213042 : Ws → St 1475
  lem-box-perm-1324-at0314213042 = pickᴰ 40 Sᴰ
  lem-box-perm-2314-at0210243143 : Ws → St 1714
  lem-box-perm-2314-at0210243143 = pickᴰ 41 Sᴰ
  lem-box-perm-3124-at0214213043 : Ws → St 1715
  lem-box-perm-3124-at0214213043 = pickᴰ 42 Sᴰ
  lem-box2-at0314213042 : Ws → St 1716
  lem-box2-at0314213042 = pickᴰ 43 Sᴰ
  lem-box-perm-1324-at0330 : Ws → St 1717
  lem-box-perm-1324-at0330 = pickᴰ 44 Sᴰ
  lem-box-perm-2314-at132132 : Ws → St 1718
  lem-box-perm-2314-at132132 = pickᴰ 45 Sᴰ
  lem-F0-R : Ws → St 1719
  lem-F0-R = pickᴰ 46 Sᴰ
  lem-F0-R-at14213243 : Ws → St 1720
  lem-F0-R-at14213243 = pickᴰ 47 Sᴰ
  lem-F5-01 : Ws → St 1721
  lem-F5-01 = pickᴰ 48 Sᴰ
  lem-box-perm-1342-at0210243143 : Ws → St 1516
  lem-box-perm-1342-at0210243143 = pickᴰ 49 Sᴰ
  lem-box-perm-1423-at021021 : Ws → St 1517
  lem-box-perm-1423-at021021 = pickᴰ 50 Sᴰ
  lem-box-perm-2431 : Ws → St 1722
  lem-box-perm-2431 = pickᴰ 51 Sᴰ
  lem-box-perm-4132-at122441 : Ws → St 1563
  lem-box-perm-4132-at122441 = pickᴰ 52 Sᴰ
  lem-AX-S23 : Ws → St 1723
  lem-AX-S23 = pickᴰ 53 Sᴰ
  lem-F0-B : Ws → St 1724
  lem-F0-B = pickᴰ 54 Sᴰ
  lem-F0-B-at14213243 : Ws → St 1725
  lem-F0-B-at14213243 = pickᴰ 55 Sᴰ
  lem-XCKX-box-2-at0210243143 : Ws → St 1726
  lem-XCKX-box-2-at0210243143 = pickᴰ 56 Sᴰ
  lem-XCKX-box-2-at122441 : Ws → St 1727
  lem-XCKX-box-2-at122441 = pickᴰ 57 Sᴰ
  lem-XCKX-box-2-at243243 : Ws → St 1728
  lem-XCKX-box-2-at243243 = pickᴰ 58 Sᴰ
  lem-box-box-1-at03102132 : Ws → St 1729
  lem-box-box-1-at03102132 = pickᴰ 59 Sᴰ
  lem-box-box-2 : Ws → St 1730
  lem-box-box-2 = pickᴰ 60 Sᴰ
  lem-F4-CS0-CS2 : Ws → St 1731
  lem-F4-CS0-CS2 = pickᴰ 61 Sᴰ
  lem-nf-X-CS0at0 : Ws → St 1732
  lem-nf-X-CS0at0 = pickᴰ 62 Sᴰ
  lem-nf-X-CS0at1 : Ws → St 1733
  lem-nf-X-CS0at1 = pickᴰ 63 Sᴰ
  lem-nf-X-CS0at2 : Ws → St 1734
  lem-nf-X-CS0at2 = pickᴰ 64 Sᴰ
  lem-nf-X-CS1at0 : Ws → St 1735
  lem-nf-X-CS1at0 = pickᴰ 65 Sᴰ
  lem-nf-X-CS1at1 : Ws → St 1736
  lem-nf-X-CS1at1 = pickᴰ 66 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 1708 (lem-box-perm-2314-at03102132 c4)
  q2 : Ws → Eqn
  q2 c4 = wlE 541 (lit c4)
  q3 : Ws → Eqn
  q3 c4 = sE 1724 (lem-F0-B c4)
  q4 : Ws → Eqn
  q4 c4 = sE 1719 (lem-F0-R c4)
  q5 : Ws → Eqn
  q5 c4 = sE 1239 (lem-CSdu-box-3-at043043 c4)
  q6 : Ws → Eqn
  q6 c4 = sE 1470 (lem-box-perm-1324-at043043 c4)
  q7 : Ws → Eqn
  q7 c4 = sE 919 (lem-box-cP-at04203243 c4)
  q8 : Ws → Eqn
  q8 c4 = wpE 376 c4
  q9 : Ws → Eqn
  q9 c4 = wlE 348 (lit c4)
  q10 : Ws → Eqn
  q10 c4 = wpE 311 c4
  q11 : Ws → Eqn
  q11 c4 = eqn (ℓ "丬亳") (ℓ "亳丬") (c₂ (CX₀₁) (Toffᵗ))
  q12 : Ws → Eqn
  q12 c4 = wlE 460 (lit c4)
  q13 : Ws → Eqn
  q13 c4 = wlE 461 (lit c4)
  q14 : Ws → Eqn
  q14 c4 = wlE 516 (lit c4)
  q15 : Ws → Eqn
  q15 c4 = wpE 391 c4
  q16 : Ws → Eqn
  q16 c4 = sE 1709 (lem-CSu-box-3-at043043 c4)
  q17 : Ws → Eqn
  q17 c4 = sE 1712 (lem-box2-at043043 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 1711 (lem-box-perm-3124-at0330 c4)

-- CXuA-S: 44 steps
lem-CXuA-S : Ws → ⟪ (ℓ "乽俐") ⟫ʷ ≈ ⟪ (ℓ "俐乽") ⟫ʷ
lem-CXuA-S c4 = derive (ℓ "乽俐") (ℓ "俐乽")
  (re 1 1 (ℓ "佤享俎享俏") ∷
   re 3 1 (ℓ "丽") ∷
   re 5 1 (ℓ "举") ∷
   rw 1 (q1 c4) ∷
   rw⁻ 2 (q2 c4) ∷
   rw 0 (q3 c4) ∷
   rw 2 (q4 c4) ∷
   rw 5 (q5 c4) ∷
   rw 5 (q6 c4) ∷
   rw 5 (q7 c4) ∷
   rw⁻ 4 (q8 c4) ∷
   rw 6 (q9 c4) ∷
   rw 10 (q10 c4) ∷
   rw 9 (q11 c4) ∷
   rw 8 (q12 c4) ∷
   rw 7 (q11 c4) ∷
   rw 6 (q13 c4) ∷
   rw⁻ 7 (q9 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 6 (q15 c4) ∷
   rw 7 (q14 c4) ∷
   rw⁻ 4 (q7 c4) ∷
   rw⁻ 4 (q6 c4) ∷
   rw 3 (q16 c4) ∷
   rw 3 (q6 c4) ∷
   rw 3 (q7 c4) ∷
   rw⁻ 2 (q8 c4) ∷
   rw 4 (q9 c4) ∷
   rw 8 (q10 c4) ∷
   rw 7 (q11 c4) ∷
   rw 6 (q12 c4) ∷
   rw 5 (q11 c4) ∷
   rw 4 (q13 c4) ∷
   rw⁻ 5 (q9 c4) ∷
   rw 3 (q14 c4) ∷
   rw⁻ 4 (q15 c4) ∷
   rw 5 (q14 c4) ∷
   rw⁻ 2 (q7 c4) ∷
   rw⁻ 2 (q6 c4) ∷
   rw 1 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   re 2 1 (ℓ "俎") ∷
   re 4 1 (ℓ "俏") ∷
   re 0 5 (ℓ "俐") ∷ []) Eq.refl

private
  q19 : Ws → Eqn
  q19 c4 = sE 1728 (lem-XCKX-box-2-at243243 c4)
  q20 : Ws → Eqn
  q20 c4 = wpE 484 c4
  q21 : Ws → Eqn
  q21 c4 = wpE 485 c4
  q22 : Ws → Eqn
  q22 c4 = wpE 486 c4

-- F4-K0-CS1: 11 steps
lem-F4-K0-CS1 : Ws → ⟪ (ℓ "並亁並侧") ⟫ʷ ≈ ⟪ (ℓ "侧並亁並") ⟫ʷ
lem-F4-K0-CS1 c4 = derive (ℓ "並亁並侧") (ℓ "侧並亁並")
  (re 3 1 (ℓ "仄亲侥亲侦") ∷
   re 5 1 (ℓ "乎") ∷
   re 7 1 (ℓ "乏") ∷
   rw 0 (q19 c4) ∷
   rw⁻ 1 (q20 c4) ∷
   rw⁻ 2 (q21 c4) ∷
   rw⁻ 3 (q20 c4) ∷
   rw⁻ 4 (q22 c4) ∷
   re 2 1 (ℓ "侥") ∷
   re 4 1 (ℓ "侦") ∷
   re 0 5 (ℓ "侧") ∷ []) Eq.refl

private
  q23 : Ws → Eqn
  q23 c4 = sE 1727 (lem-XCKX-box-2-at122441 c4)
  q24 : Ws → Eqn
  q24 c4 = wpE 491 c4
  q25 : Ws → Eqn
  q25 c4 = wpE 492 c4
  q26 : Ws → Eqn
  q26 c4 = wpE 493 c4

-- F4-K0-CS2: 11 steps
lem-F4-K0-CS2 : Ws → ⟪ (ℓ "並亁並侬") ⟫ʷ ≈ ⟪ (ℓ "侬並亁並") ⟫ʷ
lem-F4-K0-CS2 c4 = derive (ℓ "並亁並侬") (ℓ "侬並亁並")
  (re 3 1 (ℓ "仞亭侪亭侫") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 0 (q23 c4) ∷
   rw⁻ 1 (q24 c4) ∷
   rw⁻ 2 (q25 c4) ∷
   rw⁻ 3 (q24 c4) ∷
   rw⁻ 4 (q26 c4) ∷
   re 2 1 (ℓ "侪") ∷
   re 4 1 (ℓ "侫") ∷
   re 0 5 (ℓ "侬") ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = sE 1726 (lem-XCKX-box-2-at0210243143 c4)
  q28 : Ws → Eqn
  q28 c4 = wlE 666 (lit c4)
  q29 : Ws → Eqn
  q29 c4 = wpE 538 c4
  q30 : Ws → Eqn
  q30 c4 = wpE 539 c4

-- F4-K2-CS0: 11 steps
lem-F4-K2-CS0 : Ws → ⟪ (ℓ "並亇並俄") ⟫ʷ ≈ ⟪ (ℓ "俄並亇並") ⟫ʷ
lem-F4-K2-CS0 c4 = derive (ℓ "並亇並俄") (ℓ "俄並亇並")
  (re 3 1 (ℓ "伱亮係亮促") ∷
   re 5 1 (ℓ "丶") ∷
   re 7 1 (ℓ "丷") ∷
   rw 0 (q27 c4) ∷
   rw⁻ 1 (q28 c4) ∷
   rw⁻ 2 (q29 c4) ∷
   rw⁻ 3 (q28 c4) ∷
   rw⁻ 4 (q30 c4) ∷
   re 2 1 (ℓ "係") ∷
   re 4 1 (ℓ "促") ∷
   re 0 5 (ℓ "俄") ∷ []) Eq.refl

private
  q31 : Ws → Eqn
  q31 c4 = sE 1714 (lem-box-perm-2314-at0210243143 c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 806 (lit c4)
  q33 : Ws → Eqn
  q33 c4 = sE 1725 (lem-F0-B-at14213243 c4)
  q34 : Ws → Eqn
  q34 c4 = sE 1720 (lem-F0-R-at14213243 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 1273 (lem-CSdu-box-3-at0314213042 c4)
  q36 : Ws → Eqn
  q36 c4 = sE 1475 (lem-box-perm-1324-at0314213042 c4)
  q37 : Ws → Eqn
  q37 c4 = sE 997 (lem-box-cP-at0314203142 c4)
  q38 : Ws → Eqn
  q38 c4 = wpE 702 c4
  q39 : Ws → Eqn
  q39 c4 = wpE 41 c4
  q40 : Ws → Eqn
  q40 c4 = wlE 501 (lit c4)
  q41 : Ws → Eqn
  q41 c4 = sE 1025 (lem-comm-CX04-TOFF312 c4)
  q42 : Ws → Eqn
  q42 c4 = wlE 778 (lit c4)
  q43 : Ws → Eqn
  q43 c4 = wlE 499 (lit c4)
  q44 : Ws → Eqn
  q44 c4 = wlE 779 (lit c4)
  q45 : Ws → Eqn
  q45 c4 = wpE 716 c4
  q46 : Ws → Eqn
  q46 c4 = sE 1713 (lem-CSu-box-3-at0314213042 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 1716 (lem-box2-at0314213042 c4)
  q48 : Ws → Eqn
  q48 c4 = sE 1715 (lem-box-perm-3124-at0214213043 c4)

-- CXuA-S @14213243: 44 steps
lem-CXuA-S-at14213243 : Ws → ⟪ (ℓ "书俄") ⟫ʷ ≈ ⟪ (ℓ "俄书") ⟫ʷ
lem-CXuA-S-at14213243 c4 = derive (ℓ "书俄") (ℓ "俄书")
  (re 1 1 (ℓ "伱亮係亮促") ∷
   re 3 1 (ℓ "丶") ∷
   re 5 1 (ℓ "丷") ∷
   rw 1 (q31 c4) ∷
   rw⁻ 2 (q32 c4) ∷
   rw 0 (q33 c4) ∷
   rw 2 (q34 c4) ∷
   rw 5 (q35 c4) ∷
   rw 5 (q36 c4) ∷
   rw 5 (q37 c4) ∷
   rw⁻ 4 (q38 c4) ∷
   rw 6 (q39 c4) ∷
   rw 10 (q40 c4) ∷
   rw 9 (q41 c4) ∷
   rw 8 (q42 c4) ∷
   rw 7 (q41 c4) ∷
   rw 6 (q43 c4) ∷
   rw⁻ 7 (q39 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 6 (q45 c4) ∷
   rw⁻ 7 (q44 c4) ∷
   rw⁻ 4 (q37 c4) ∷
   rw⁻ 4 (q36 c4) ∷
   rw 3 (q46 c4) ∷
   rw 3 (q36 c4) ∷
   rw 3 (q37 c4) ∷
   rw⁻ 2 (q38 c4) ∷
   rw 4 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 5 (q41 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw⁻ 3 (q44 c4) ∷
   rw⁻ 4 (q45 c4) ∷
   rw⁻ 5 (q44 c4) ∷
   rw⁻ 2 (q37 c4) ∷
   rw⁻ 2 (q36 c4) ∷
   rw 1 (q47 c4) ∷
   rw 0 (q48 c4) ∷
   re 2 1 (ℓ "係") ∷
   re 4 1 (ℓ "促") ∷
   re 0 5 (ℓ "俄") ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = sE 994 (lem-box-cP-at0210243143 c4)
  q50 : Ws → Eqn
  q50 c4 = wpE 20 c4
  q51 : Ws → Eqn
  q51 c4 = wlE 183 (lit c4)
  q52 : Ws → Eqn
  q52 c4 = eqn (ℓ "亦並") (ℓ "並亦") (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))
  q53 : Ws → Eqn
  q53 c4 = wlE 184 (lit c4)
  q54 : Ws → Eqn
  q54 c4 = wpE 21 c4
  q55 : Ws → Eqn
  q55 c4 = wpE 22 c4
  q56 : Ws → Eqn
  q56 c4 = sE 960 (lem-comm-CSd13-CCZ024 c4)
  q57 : Ws → Eqn
  q57 c4 = sE 958 (lem-comm-CS13-CCZ024 c4)
  q58 : Ws → Eqn
  q58 c4 = wpE 23 c4
  q59 : Ws → Eqn
  q59 c4 = wlE 185 (lit c4)
  q60 : Ws → Eqn
  q60 c4 = wlE 186 (lit c4)
  q61 : Ws → Eqn
  q61 c4 = sE 1510 (lem-CSdu-box-3-at0210243143 c4)
  q62 : Ws → Eqn
  q62 c4 = wlE 241 (lit c4)
  q63 : Ws → Eqn
  q63 c4 = wpE 88 c4
  q64 : Ws → Eqn
  q64 c4 = wpE 34 c4
  q65 : Ws → Eqn
  q65 c4 = sE 3 (lem-comm-CX13-CCZ024 c4)
  q66 : Ws → Eqn
  q66 c4 = wpE 35 c4
  q67 : Ws → Eqn
  q67 c4 = wpE 36 c4
  q68 : Ws → Eqn
  q68 c4 = wpE 89 c4
  q69 : Ws → Eqn
  q69 c4 = wlE 1025 (lit c4)
  q70 : Ws → Eqn
  q70 c4 = wpE 768 c4
  q71 : Ws → Eqn
  q71 c4 = wpE 352 c4
  q72 : Ws → Eqn
  q72 c4 = wlE 196 (lit c4)
  q73 : Ws → Eqn
  q73 c4 = sE 1023 (lem-comm-CX04-TOFF213 c4)
  q74 : Ws → Eqn
  q74 c4 = wlE 807 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = wlE 808 (lit c4)
  q76 : Ws → Eqn
  q76 c4 = wlE 942 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wlE 979 (lit c4)
  q78 : Ws → Eqn
  q78 c4 = sE 1512 (lem-CSu-box-3-at0210243143 c4)
  q79 : Ws → Eqn
  q79 c4 = sE 1563 (lem-box-perm-4132-at122441 c4)
  q80 : Ws → Eqn
  q80 c4 = sE 1516 (lem-box-perm-1342-at0210243143 c4)
  q81 : Ws → Eqn
  q81 c4 = sE 1730 (lem-box-box-2 c4)
  q82 : Ws → Eqn
  q82 c4 = sE 1517 (lem-box-perm-1423-at021021 c4)
  q83 : Ws → Eqn
  q83 c4 = sE 1722 (lem-box-perm-2431 c4)
  q84 : Ws → Eqn
  q84 c4 = sE 1002 (lem-box-cP-at122441 c4)
  q85 : Ws → Eqn
  q85 c4 = wlE 906 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = sE 67 (lem-comm-CZ13-CCZ024 c4)
  q87 : Ws → Eqn
  q87 c4 = wlE 1026 (lit c4)
  q88 : Ws → Eqn
  q88 c4 = wpE 828 c4
  q89 : Ws → Eqn
  q89 c4 = sE 1705 (lem-comm-CCZ034-CS12 c4)
  q90 : Ws → Eqn
  q90 c4 = wlE 645 (lit c4)
  q91 : Ws → Eqn
  q91 c4 = wpE 829 c4
  q92 : Ws → Eqn
  q92 c4 = wlE 703 (lit c4)
  q93 : Ws → Eqn
  q93 c4 = wpE 830 c4
  q94 : Ws → Eqn
  q94 c4 = wlE 230 (lit c4)
  q95 : Ws → Eqn
  q95 c4 = wpE 831 c4
  q96 : Ws → Eqn
  q96 c4 = wpE 7 c4
  q97 : Ws → Eqn
  q97 c4 = wlE 745 (lit c4)
  q98 : Ws → Eqn
  q98 c4 = wlE 1027 (lit c4)
  q99 : Ws → Eqn
  q99 c4 = wlE 1028 (lit c4)
  q100 : Ws → Eqn
  q100 c4 = wpE 832 c4
  q101 : Ws → Eqn
  q101 c4 = wpE 673 c4
  q102 : Ws → Eqn
  q102 c4 = sE 1024 (lem-comm-CCZ024-CX13 c4)
  q103 : Ws → Eqn
  q103 c4 = wpE 833 c4
  q104 : Ws → Eqn
  q104 c4 = wlE 190 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wpE 37 c4
  q106 : Ws → Eqn
  q106 c4 = wpE 33 c4
  q107 : Ws → Eqn
  q107 c4 = wlE 1029 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 256 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = sE 1286 (lem-comm-TOFF013-CS24 c4)
  q110 : Ws → Eqn
  q110 c4 = wlE 872 (lit c4)
  q111 : Ws → Eqn
  q111 c4 = sE 210 (lem-comm-TOFF013-CSd24 c4)
  q112 : Ws → Eqn
  q112 c4 = wpE 785 c4
  q113 : Ws → Eqn
  q113 c4 = wpE 786 c4
  q114 : Ws → Eqn
  q114 c4 = wpE 663 c4
  q115 : Ws → Eqn
  q115 c4 = wpE 787 c4
  q116 : Ws → Eqn
  q116 c4 = wlE 1030 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = wlE 187 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = wpE 657 c4
  q119 : Ws → Eqn
  q119 c4 = wlE 986 (lit c4)
  q120 : Ws → Eqn
  q120 c4 = wpE 277 c4
  q121 : Ws → Eqn
  q121 c4 = wlE 983 (lit c4)
  q122 : Ws → Eqn
  q122 c4 = sE 1513 (lem-CSu-box-3-at122441 c4)
  q123 : Ws → Eqn
  q123 c4 = wpE 659 c4
  q124 : Ws → Eqn
  q124 c4 = wlE 469 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wpE 834 c4
  q126 : Ws → Eqn
  q126 c4 = wlE 981 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = sE 1511 (lem-CSdu-box-3-at122441 c4)

-- F4-CS2-CS0: 284 steps
lem-F4-CS2-CS0 : Ws → ⟪ (ℓ "並侬並俄") ⟫ʷ ≈ ⟪ (ℓ "俄並侬並") ⟫ʷ
lem-F4-CS2-CS0 c4 = derive (ℓ "並侬並俄") (ℓ "俄並侬並")
  (re 3 1 (ℓ "伱亮係亮促") ∷
   re 5 1 (ℓ "丶") ∷
   re 7 1 (ℓ "丷") ∷
   rw 3 (q49 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 4 (q51 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   rw 6 (q53 c4) ∷
   rw⁻ 10 (q54 c4) ∷
   rw⁻ 9 (q55 c4) ∷
   rw 8 (q56 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 6 (q57 c4) ∷
   rw⁻ 7 (q53 c4) ∷
   rw⁻ 5 (q58 c4) ∷
   rw⁻ 4 (q50 c4) ∷
   rw 5 (q59 c4) ∷
   rw 6 (q60 c4) ∷
   rw⁻ 5 (q52 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   re 1 1 (ℓ "仞亭侪亭侫") ∷
   re 5 1 (ℓ "么") ∷
   rw 5 (q61 c4) ∷
   rw 5 (q49 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw⁻ 9 (q64 c4) ∷
   rw 8 (q65 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw 6 (q65 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 5 (q62 c4) ∷
   rw 5 (q69 c4) ∷
   rw⁻ 7 (q70 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw⁻ 12 (q63 c4) ∷
   rw⁻ 11 (q64 c4) ∷
   rw 10 (q65 c4) ∷
   rw⁻ 9 (q66 c4) ∷
   rw 8 (q65 c4) ∷
   rw⁻ 7 (q67 c4) ∷
   rw⁻ 6 (q68 c4) ∷
   rw 7 (q62 c4) ∷
   rw 9 (q71 c4) ∷
   rw 13 (q72 c4) ∷
   rw 12 (q73 c4) ∷
   rw 11 (q74 c4) ∷
   rw 10 (q73 c4) ∷
   rw 9 (q75 c4) ∷
   rw⁻ 10 (q71 c4) ∷
   rw⁻ 8 (q76 c4) ∷
   rw 7 (q69 c4) ∷
   rw 8 (q77 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   re 3 1 (ℓ "乇") ∷
   rw 3 (q78 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 2 (q62 c4) ∷
   rw⁻ 8 (q63 c4) ∷
   rw⁻ 7 (q64 c4) ∷
   rw 6 (q65 c4) ∷
   rw⁻ 5 (q66 c4) ∷
   rw 4 (q65 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw 3 (q62 c4) ∷
   rw 3 (q69 c4) ∷
   rw⁻ 5 (q70 c4) ∷
   rw⁻ 4 (q62 c4) ∷
   rw⁻ 10 (q63 c4) ∷
   rw⁻ 9 (q64 c4) ∷
   rw 8 (q65 c4) ∷
   rw⁻ 7 (q66 c4) ∷
   rw 6 (q65 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw 5 (q62 c4) ∷
   rw 7 (q71 c4) ∷
   rw 11 (q72 c4) ∷
   rw 10 (q73 c4) ∷
   rw 9 (q74 c4) ∷
   rw 8 (q73 c4) ∷
   rw 7 (q75 c4) ∷
   rw⁻ 8 (q71 c4) ∷
   rw⁻ 6 (q76 c4) ∷
   rw 5 (q69 c4) ∷
   rw 6 (q77 c4) ∷
   rw⁻ 2 (q49 c4) ∷
   rw 1 (q79 c4) ∷
   rw 2 (q80 c4) ∷
   rw 1 (q81 c4) ∷
   rw 1 (q82 c4) ∷
   rw 2 (q83 c4) ∷
   rw 1 (q49 c4) ∷
   rw⁻ 0 (q50 c4) ∷
   rw 2 (q51 c4) ∷
   rw⁻ 1 (q52 c4) ∷
   rw 4 (q53 c4) ∷
   rw⁻ 8 (q54 c4) ∷
   rw⁻ 7 (q55 c4) ∷
   rw 6 (q56 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 4 (q57 c4) ∷
   rw⁻ 5 (q53 c4) ∷
   rw⁻ 3 (q58 c4) ∷
   rw⁻ 2 (q50 c4) ∷
   rw 3 (q59 c4) ∷
   rw 4 (q60 c4) ∷
   rw⁻ 3 (q52 c4) ∷
   rw⁻ 0 (q49 c4) ∷
   rw 3 (q84 c4) ∷
   rw 2 (q53 c4) ∷
   rw⁻ 6 (q54 c4) ∷
   rw⁻ 5 (q55 c4) ∷
   rw 4 (q56 c4) ∷
   rw⁻ 3 (q55 c4) ∷
   rw 2 (q57 c4) ∷
   rw⁻ 3 (q53 c4) ∷
   rw 3 (q85 c4) ∷
   rw 5 (q53 c4) ∷
   rw⁻ 9 (q54 c4) ∷
   rw⁻ 8 (q55 c4) ∷
   rw 7 (q56 c4) ∷
   rw⁻ 6 (q55 c4) ∷
   rw 5 (q57 c4) ∷
   rw⁻ 6 (q53 c4) ∷
   rw 4 (q86 c4) ∷
   rw 5 (q87 c4) ∷
   rw⁻ 2 (q84 c4) ∷
   rw 3 (q88 c4) ∷
   rw 6 (q89 c4) ∷
   rw 5 (q90 c4) ∷
   rw 6 (q91 c4) ∷
   rw 8 (q92 c4) ∷
   rw 9 (q93 c4) ∷
   rw 10 (q94 c4) ∷
   rw 4 (q89 c4) ∷
   rw 5 (q95 c4) ∷
   rw 6 (q96 c4) ∷
   re 4 1 (ℓ "侪") ∷
   re 6 1 (ℓ "侫") ∷
   re 2 5 (ℓ "侬") ∷
   rw⁻ 3 (q97 c4) ∷
   re 2 1 (ℓ "仞亭侪亭侫") ∷
   re 4 1 (ℓ "乇") ∷
   re 6 1 (ℓ "么") ∷
   rw⁻ 3 (q98 c4) ∷
   rw 2 (q84 c4) ∷
   rw⁻ 5 (q99 c4) ∷
   rw 7 (q100 c4) ∷
   rw 4 (q101 c4) ∷
   rw 6 (q102 c4) ∷
   rw 7 (q103 c4) ∷
   rw⁻ 10 (q104 c4) ∷
   rw 9 (q105 c4) ∷
   rw 10 (q67 c4) ∷
   rw 11 (q102 c4) ∷
   rw 12 (q66 c4) ∷
   rw 13 (q102 c4) ∷
   rw 14 (q64 c4) ∷
   rw 15 (q106 c4) ∷
   rw 9 (q104 c4) ∷
   rw⁻ 3 (q107 c4) ∷
   rw 5 (q108 c4) ∷
   rw 4 (q109 c4) ∷
   rw⁻ 5 (q110 c4) ∷
   rw 6 (q111 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw⁻ 8 (q112 c4) ∷
   rw⁻ 4 (q108 c4) ∷
   rw⁻ 5 (q99 c4) ∷
   rw 7 (q113 c4) ∷
   rw 9 (q108 c4) ∷
   rw 8 (q109 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw 10 (q111 c4) ∷
   rw⁻ 11 (q110 c4) ∷
   rw⁻ 12 (q112 c4) ∷
   rw⁻ 8 (q108 c4) ∷
   rw 9 (q100 c4) ∷
   rw⁻ 3 (q114 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q102 c4) ∷
   rw⁻ 4 (q104 c4) ∷
   rw 3 (q105 c4) ∷
   rw 4 (q67 c4) ∷
   rw 5 (q102 c4) ∷
   rw 6 (q66 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q64 c4) ∷
   rw 9 (q106 c4) ∷
   rw 3 (q104 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   re 6 1 (ℓ "侪") ∷
   re 8 1 (ℓ "侫") ∷
   re 4 5 (ℓ "侬") ∷
   rw⁻ 1 (q117 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   re 3 1 (ℓ "仞亭侪亭侫") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw⁻ 7 (q119 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   rw⁻ 5 (q121 c4) ∷
   rw⁻ 4 (q120 c4) ∷
   rw⁻ 3 (q122 c4) ∷
   re 6 1 (ℓ "侪") ∷
   re 8 1 (ℓ "侫") ∷
   re 4 5 (ℓ "侬") ∷
   rw⁻ 2 (q118 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   re 4 1 (ℓ "仞亭侪亭侫") ∷
   re 6 1 (ℓ "乇") ∷
   re 8 1 (ℓ "么") ∷
   rw⁻ 5 (q98 c4) ∷
   rw 4 (q84 c4) ∷
   rw⁻ 7 (q99 c4) ∷
   rw 9 (q100 c4) ∷
   rw 6 (q101 c4) ∷
   rw 8 (q102 c4) ∷
   rw 9 (q103 c4) ∷
   rw⁻ 12 (q104 c4) ∷
   rw 11 (q105 c4) ∷
   rw 12 (q67 c4) ∷
   rw 13 (q102 c4) ∷
   rw 14 (q66 c4) ∷
   rw 15 (q102 c4) ∷
   rw 16 (q64 c4) ∷
   rw 17 (q106 c4) ∷
   rw 11 (q104 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   rw 7 (q108 c4) ∷
   rw 6 (q109 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw 8 (q111 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw⁻ 10 (q112 c4) ∷
   rw⁻ 6 (q108 c4) ∷
   rw⁻ 7 (q99 c4) ∷
   rw 9 (q113 c4) ∷
   rw 11 (q108 c4) ∷
   rw 10 (q109 c4) ∷
   rw⁻ 11 (q110 c4) ∷
   rw 12 (q111 c4) ∷
   rw⁻ 13 (q110 c4) ∷
   rw⁻ 14 (q112 c4) ∷
   rw⁻ 10 (q108 c4) ∷
   rw 11 (q100 c4) ∷
   rw⁻ 5 (q114 c4) ∷
   rw⁻ 7 (q115 c4) ∷
   rw 5 (q116 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   re 8 1 (ℓ "侪") ∷
   re 10 1 (ℓ "侫") ∷
   re 6 5 (ℓ "侬") ∷
   rw⁻ 3 (q117 c4) ∷
   rw⁻ 6 (q123 c4) ∷
   re 5 1 (ℓ "仞亭侪亭侫") ∷
   re 7 1 (ℓ "乇") ∷
   re 9 1 (ℓ "么") ∷
   rw⁻ 9 (q124 c4) ∷
   rw⁻ 8 (q125 c4) ∷
   rw⁻ 7 (q126 c4) ∷
   rw⁻ 6 (q125 c4) ∷
   rw⁻ 5 (q127 c4) ∷
   re 8 1 (ℓ "侪") ∷
   re 10 1 (ℓ "侫") ∷
   re 6 5 (ℓ "侬") ∷
   rw⁻ 4 (q123 c4) ∷
   re 2 1 (ℓ "係") ∷
   re 4 1 (ℓ "促") ∷
   re 0 5 (ℓ "俄") ∷ []) Eq.refl

private
  q128 : Ws → Eqn
  q128 c4 = wlE 1083 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = sE 1707 (lem-invr-SBOX⟨2·0·41·3⟩ c4)
  q130 : Ws → Eqn
  q130 c4 = sE 1721 (lem-F5-01 c4)
  q131 : Ws → Eqn
  q131 c4 = sE 1723 (lem-AX-S23 c4)
  q132 : Ws → Eqn
  q132 c4 = sE 1706 (lem-inv-SBOX⟨2·0·41·3⟩ c4)
  q133 : Ws → Eqn
  q133 c4 = sE 1731 (lem-F4-CS0-CS2 c4)

-- F2-CS0-CS2: 16 steps
lem-F2-CS0-CS2 : Ws → ⟪ (ℓ "俄侬") ⟫ʷ ≈ ⟪ (ℓ "侬俄") ⟫ʷ
lem-F2-CS0-CS2 c4 = derive (ℓ "俄侬") (ℓ "侬俄")
  (rw⁻ 0 (q128 c4) ∷
   rw⁻ 1 (q129 c4) ∷
   rw⁻ 2 (q128 c4) ∷
   rw 3 (q130 c4) ∷
   rw 3 (q131 c4) ∷
   rw⁻ 4 (q128 c4) ∷
   rw⁻ 5 (q132 c4) ∷
   rw⁻ 6 (q128 c4) ∷
   rw⁻ 3 (q133 c4) ∷
   rw 2 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw 0 (q128 c4) ∷
   rw⁻ 4 (q130 c4) ∷
   rw 3 (q128 c4) ∷
   rw 2 (q129 c4) ∷
   rw 1 (q128 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = sE 247 (lem-box-tQ c4)
  q135 : Ws → Eqn
  q135 c4 = wlE 1084 (lit c4)
  q136 : Ws → Eqn
  q136 c4 = wpE 883 c4
  q137 : Ws → Eqn
  q137 c4 = wpE 884 c4
  q138 : Ws → Eqn
  q138 c4 = wpE 122 c4
  q139 : Ws → Eqn
  q139 c4 = wlE 871 (lit c4)
  q140 : Ws → Eqn
  q140 c4 = wpE 66 c4
  q141 : Ws → Eqn
  q141 c4 = wpE 885 c4
  q142 : Ws → Eqn
  q142 c4 = wpE 106 c4
  q143 : Ws → Eqn
  q143 c4 = sE 2 (lem-comm-CX12-CCZ034 c4)
  q144 : Ws → Eqn
  q144 c4 = wpE 107 c4
  q145 : Ws → Eqn
  q145 c4 = wpE 108 c4
  q146 : Ws → Eqn
  q146 c4 = wlE 1085 (lit c4)
  q147 : Ws → Eqn
  q147 c4 = sE 252 (lem-box-tQ-at0330 c4)
  q148 : Ws → Eqn
  q148 c4 = sE 1717 (lem-box-perm-1324-at0330 c4)
  q149 : Ws → Eqn
  q149 c4 = sE 868 (lem-box-cP-at032032 c4)
  q150 : Ws → Eqn
  q150 c4 = wlE 325 (lit c4)
  q151 : Ws → Eqn
  q151 c4 = wlE 445 (lit c4)
  q152 : Ws → Eqn
  q152 c4 = wlE 446 (lit c4)
  q153 : Ws → Eqn
  q153 c4 = eqn (ℓ "不亲") (ℓ "亲不") (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑))
  q154 : Ws → Eqn
  q154 c4 = wpE 298 c4
  q155 : Ws → Eqn
  q155 c4 = eqn (ℓ "丬亲") (ℓ "亲丬") (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI))
  q156 : Ws → Eqn
  q156 c4 = wlE 447 (lit c4)
  q157 : Ws → Eqn
  q157 c4 = wlE 214 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = eqn (ℓ "丌亲") (ℓ "亲丌") (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑))
  q159 : Ws → Eqn
  q159 c4 = wpE 299 c4
  q160 : Ws → Eqn
  q160 c4 = wlE 448 (lit c4)
  q161 : Ws → Eqn
  q161 c4 = sE 204 (lem-comm-CSd24-CCZ013 c4)
  q162 : Ws → Eqn
  q162 c4 = sE 194 (lem-comm-CS24-CCZ013 c4)
  q163 : Ws → Eqn
  q163 c4 = wlE 327 (lit c4)
  q164 : Ws → Eqn
  q164 c4 = wlE 449 (lit c4)
  q165 : Ws → Eqn
  q165 c4 = wlE 450 (lit c4)
  q166 : Ws → Eqn
  q166 c4 = wpE 300 c4
  q167 : Ws → Eqn
  q167 c4 = wlE 263 (lit c4)
  q168 : Ws → Eqn
  q168 c4 = sE 1710 (lem-box-perm-3124 c4)
  q169 : Ws → Eqn
  q169 c4 = sE 1729 (lem-box-box-1-at03102132 c4)
  q170 : Ws → Eqn
  q170 c4 = sE 1718 (lem-box-perm-2314-at132132 c4)

-- Tu-box: 83 steps
lem-Tu-box : Ws → ⟪ (ℓ "亓亹亓") ⟫ʷ ≈ ⟪ (ℓ "亹佬") ⟫ʷ
lem-Tu-box c4 = derive (ℓ "亓亹亓") (ℓ "亹佬")
  (rw 1 (q134 c4) ∷
   rw⁻ 0 (q135 c4) ∷
   rw⁻ 2 (q136 c4) ∷
   rw⁻ 4 (q135 c4) ∷
   rw⁻ 6 (q137 c4) ∷
   rw 3 (q138 c4) ∷
   rw 5 (q139 c4) ∷
   rw 4 (q39 c4) ∷
   rw 8 (q40 c4) ∷
   rw 7 (q41 c4) ∷
   rw 6 (q42 c4) ∷
   rw 5 (q41 c4) ∷
   rw 4 (q43 c4) ∷
   rw⁻ 5 (q39 c4) ∷
   rw 5 (q140 c4) ∷
   rw 6 (q141 c4) ∷
   rw 5 (q108 c4) ∷
   rw⁻ 9 (q142 c4) ∷
   rw 8 (q143 c4) ∷
   rw⁻ 7 (q144 c4) ∷
   rw 6 (q143 c4) ∷
   rw⁻ 5 (q145 c4) ∷
   rw⁻ 6 (q108 c4) ∷
   rw 3 (q146 c4) ∷
   rw⁻ 4 (q96 c4) ∷
   rw⁻ 1 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 1 (q149 c4) ∷
   rw⁻ 0 (q150 c4) ∷
   rw 2 (q151 c4) ∷
   rw⁻ 1 (q152 c4) ∷
   rw 7 (q153 c4) ∷
   rw 6 (q154 c4) ∷
   rw 5 (q155 c4) ∷
   rw 4 (q156 c4) ∷
   rw 3 (q155 c4) ∷
   rw 2 (q157 c4) ∷
   rw 1 (q158 c4) ∷
   rw 2 (q152 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 8 (q159 c4) ∷
   rw⁻ 7 (q160 c4) ∷
   rw 6 (q161 c4) ∷
   rw⁻ 5 (q160 c4) ∷
   rw 4 (q162 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw⁻ 3 (q163 c4) ∷
   rw⁻ 2 (q150 c4) ∷
   rw 3 (q164 c4) ∷
   rw 4 (q165 c4) ∷
   rw⁻ 3 (q152 c4) ∷
   rw 9 (q153 c4) ∷
   rw 8 (q154 c4) ∷
   rw 7 (q155 c4) ∷
   rw 6 (q156 c4) ∷
   rw 5 (q155 c4) ∷
   rw 4 (q157 c4) ∷
   rw 3 (q158 c4) ∷
   rw 4 (q152 c4) ∷
   rw⁻ 0 (q149 c4) ∷
   rw⁻ 0 (q148 c4) ∷
   rw 2 (q108 c4) ∷
   rw⁻ 6 (q142 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 4 (q144 c4) ∷
   rw 3 (q143 c4) ∷
   rw⁻ 2 (q145 c4) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 3 (q166 c4) ∷
   rw 4 (q108 c4) ∷
   rw⁻ 8 (q142 c4) ∷
   rw 7 (q143 c4) ∷
   rw⁻ 6 (q144 c4) ∷
   rw 5 (q143 c4) ∷
   rw⁻ 4 (q145 c4) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 5 (q167 c4) ∷
   rw⁻ 1 (q134 c4) ∷
   rw 0 (q18 c4) ∷
   rw 1 (q168 c4) ∷
   rw 0 (q169 c4) ∷
   rw 0 (q170 c4) ∷
   rw 1 (q1 c4) ∷ []) Eq.refl

private
  q171 : Ws → Eqn
  q171 c4 = wpE 931 c4
  q172 : Ws → Eqn
  q172 c4 = wlE 747 (lit c4)
  q173 : Ws → Eqn
  q173 c4 = wpE 654 c4
  q174 : Ws → Eqn
  q174 c4 = wlE 197 (lit c4)
  q175 : Ws → Eqn
  q175 c4 = wlE 195 (lit c4)
  q176 : Ws → Eqn
  q176 c4 = sE 1028 (lem-comm-TOFF213-CX04 c4)
  q177 : Ws → Eqn
  q177 c4 = wlE 194 (lit c4)
  q178 : Ws → Eqn
  q178 c4 = wlE 193 (lit c4)
  q179 : Ws → Eqn
  q179 c4 = wpE 44 c4
  q180 : Ws → Eqn
  q180 c4 = wpE 38 c4
  q181 : Ws → Eqn
  q181 c4 = wlE 191 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = wpE 32 c4
  q183 : Ws → Eqn
  q183 c4 = wpE 651 c4
  q184 : Ws → Eqn
  q184 c4 = wpE 161 c4
  q185 : Ws → Eqn
  q185 c4 = wpE 932 c4
  q186 : Ws → Eqn
  q186 c4 = sE 1732 (lem-nf-X-CS0at0 c4)

-- F1-X-CS0@0: 86 steps
lem-F1-X-CS0at0 : Ws → ⟪ (ℓ "亁丽丽亁丢俄") ⟫ʷ ≈ ⟪ (ℓ "俄俄俄亁丽丽亁丢乕") ⟫ʷ
lem-F1-X-CS0at0 c4 = derive (ℓ "亁丽丽亁丢俄") (ℓ "俄俄俄亁丽丽亁丢乕")
  (re 5 1 (ℓ "伱亮係亮促") ∷
   re 7 1 (ℓ "丶") ∷
   re 9 1 (ℓ "丷") ∷
   rw 0 (q171 c4) ∷
   rw 1 (q49 c4) ∷
   rw 4 (q172 c4) ∷
   rw 3 (q173 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw 2 (q174 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 5 (q177 c4) ∷
   rw 6 (q176 c4) ∷
   rw⁻ 7 (q178 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 4 (q172 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q66 c4) ∷
   rw 6 (q102 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q106 c4) ∷
   rw 2 (q104 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 4 (q49 c4) ∷
   rw 7 (q172 c4) ∷
   rw 6 (q173 c4) ∷
   rw⁻ 9 (q104 c4) ∷
   rw 8 (q105 c4) ∷
   rw 9 (q67 c4) ∷
   rw 10 (q102 c4) ∷
   rw 11 (q66 c4) ∷
   rw 12 (q102 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q106 c4) ∷
   rw 8 (q104 c4) ∷
   rw 5 (q174 c4) ∷
   rw 7 (q39 c4) ∷
   rw⁻ 6 (q175 c4) ∷
   rw 7 (q176 c4) ∷
   rw⁻ 8 (q177 c4) ∷
   rw 9 (q176 c4) ∷
   rw⁻ 10 (q178 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 7 (q172 c4) ∷
   rw⁻ 5 (q179 c4) ∷
   rw⁻ 4 (q180 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 6 (q49 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 9 (q181 c4) ∷
   rw 8 (q182 c4) ∷
   rw⁻ 7 (q181 c4) ∷
   rw 6 (q182 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw 1 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 0 (q185 c4) ∷
   rw⁻ 0 (q186 c4) ∷ []) Eq.refl

private
  q187 : Ws → Eqn
  q187 c4 = wlE 1142 (lit c4)
  q188 : Ws → Eqn
  q188 c4 = sE 1008 (lem-box-cP-at243243 c4)
  q189 : Ws → Eqn
  q189 c4 = wpE 805 c4
  q190 : Ws → Eqn
  q190 c4 = wpE 806 c4
  q191 : Ws → Eqn
  q191 c4 = wlE 217 (lit c4)
  q192 : Ws → Eqn
  q192 c4 = wpE 65 c4
  q193 : Ws → Eqn
  q193 c4 = wpE 64 c4
  q194 : Ws → Eqn
  q194 c4 = sE 893 (lem-comm-CCZ014-CX23 c4)
  q195 : Ws → Eqn
  q195 c4 = wpE 63 c4
  q196 : Ws → Eqn
  q196 c4 = wpE 62 c4
  q197 : Ws → Eqn
  q197 c4 = wpE 61 c4
  q198 : Ws → Eqn
  q198 c4 = wpE 72 c4
  q199 : Ws → Eqn
  q199 c4 = wlE 220 (lit c4)
  q200 : Ws → Eqn
  q200 c4 = wpE 70 c4
  q201 : Ws → Eqn
  q201 c4 = sE 1060 (lem-comm-TOFF023-CX14 c4)
  q202 : Ws → Eqn
  q202 c4 = wpE 69 c4
  q203 : Ws → Eqn
  q203 c4 = wlE 221 (lit c4)
  q204 : Ws → Eqn
  q204 c4 = wpE 74 c4
  q205 : Ws → Eqn
  q205 c4 = wlE 222 (lit c4)
  q206 : Ws → Eqn
  q206 c4 = wpE 53 c4
  q207 : Ws → Eqn
  q207 c4 = wlE 219 (lit c4)
  q208 : Ws → Eqn
  q208 c4 = wpE 60 c4
  q209 : Ws → Eqn
  q209 c4 = wlE 1000 (lit c4)
  q210 : Ws → Eqn
  q210 c4 = wlE 1143 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = sE 1733 (lem-nf-X-CS0at1 c4)

-- F1-X-CS0@1: 86 steps
lem-F1-X-CS0at1 : Ws → ⟪ (ℓ "亄乕乕亄丢侧") ⟫ʷ ≈ ⟪ (ℓ "侧侧侧亄乕乕亄丢乩") ⟫ʷ
lem-F1-X-CS0at1 c4 = derive (ℓ "亄乕乕亄丢侧") (ℓ "侧侧侧亄乕乕亄丢乩")
  (re 5 1 (ℓ "仄亲侥亲侦") ∷
   re 7 1 (ℓ "乎") ∷
   re 9 1 (ℓ "乏") ∷
   rw 0 (q187 c4) ∷
   rw 1 (q188 c4) ∷
   rw 4 (q189 c4) ∷
   rw 3 (q190 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 5 (q192 c4) ∷
   rw 6 (q193 c4) ∷
   rw 7 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw 9 (q194 c4) ∷
   rw 10 (q196 c4) ∷
   rw 11 (q197 c4) ∷
   rw 5 (q191 c4) ∷
   rw 2 (q198 c4) ∷
   rw 4 (q199 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw 4 (q201 c4) ∷
   rw⁻ 5 (q202 c4) ∷
   rw 6 (q201 c4) ∷
   rw⁻ 7 (q203 c4) ∷
   rw⁻ 3 (q199 c4) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw 1 (q140 c4) ∷
   rw⁻ 3 (q191 c4) ∷
   rw 2 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw 6 (q194 c4) ∷
   rw 7 (q196 c4) ∷
   rw 8 (q197 c4) ∷
   rw 2 (q191 c4) ∷
   rw⁻ 3 (q188 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 6 (q205 c4) ∷
   rw 5 (q206 c4) ∷
   rw⁻ 4 (q205 c4) ∷
   rw 3 (q206 c4) ∷
   rw⁻ 4 (q188 c4) ∷
   rw 4 (q188 c4) ∷
   rw 7 (q189 c4) ∷
   rw 6 (q190 c4) ∷
   rw⁻ 9 (q191 c4) ∷
   rw 8 (q192 c4) ∷
   rw 9 (q193 c4) ∷
   rw 10 (q194 c4) ∷
   rw 11 (q195 c4) ∷
   rw 12 (q194 c4) ∷
   rw 13 (q196 c4) ∷
   rw 14 (q197 c4) ∷
   rw 8 (q191 c4) ∷
   rw 5 (q198 c4) ∷
   rw 7 (q199 c4) ∷
   rw⁻ 6 (q200 c4) ∷
   rw 7 (q201 c4) ∷
   rw⁻ 8 (q202 c4) ∷
   rw 9 (q201 c4) ∷
   rw⁻ 10 (q203 c4) ∷
   rw⁻ 6 (q199 c4) ∷
   rw 7 (q189 c4) ∷
   rw⁻ 5 (q204 c4) ∷
   rw 4 (q140 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 5 (q192 c4) ∷
   rw 6 (q193 c4) ∷
   rw 7 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw 9 (q194 c4) ∷
   rw 10 (q196 c4) ∷
   rw 11 (q197 c4) ∷
   rw 5 (q191 c4) ∷
   rw⁻ 6 (q188 c4) ∷
   rw 6 (q188 c4) ∷
   rw⁻ 9 (q207 c4) ∷
   rw 8 (q208 c4) ∷
   rw⁻ 7 (q207 c4) ∷
   rw 6 (q208 c4) ∷
   rw⁻ 7 (q188 c4) ∷
   rw 1 (q209 c4) ∷
   rw 3 (q167 c4) ∷
   rw 0 (q210 c4) ∷
   rw⁻ 0 (q211 c4) ∷ []) Eq.refl

private
  q212 : Ws → Eqn
  q212 c4 = wlE 1147 (lit c4)
  q213 : Ws → Eqn
  q213 c4 = wpE 843 c4
  q214 : Ws → Eqn
  q214 c4 = wpE 845 c4
  q215 : Ws → Eqn
  q215 c4 = wpE 97 c4
  q216 : Ws → Eqn
  q216 c4 = wlE 245 (lit c4)
  q217 : Ws → Eqn
  q217 c4 = wpE 95 c4
  q218 : Ws → Eqn
  q218 c4 = sE 1059 (lem-comm-TOFF013-CX24 c4)
  q219 : Ws → Eqn
  q219 c4 = wpE 94 c4
  q220 : Ws → Eqn
  q220 c4 = wlE 246 (lit c4)
  q221 : Ws → Eqn
  q221 c4 = wpE 842 c4
  q222 : Ws → Eqn
  q222 c4 = wpE 90 c4
  q223 : Ws → Eqn
  q223 c4 = wlE 247 (lit c4)
  q224 : Ws → Eqn
  q224 c4 = wpE 81 c4
  q225 : Ws → Eqn
  q225 c4 = wlE 244 (lit c4)
  q226 : Ws → Eqn
  q226 c4 = wpE 87 c4
  q227 : Ws → Eqn
  q227 c4 = wlE 1037 (lit c4)
  q228 : Ws → Eqn
  q228 c4 = wlE 305 (lit c4)
  q229 : Ws → Eqn
  q229 c4 = wlE 1148 (lit c4)
  q230 : Ws → Eqn
  q230 c4 = sE 1734 (lem-nf-X-CS0at2 c4)

-- F1-X-CS0@2: 86 steps
lem-F1-X-CS0at2 : Ws → ⟪ (ℓ "亇乩乩亇丢侬") ⟫ʷ ≈ ⟪ (ℓ "侬侬侬亇乩乩亇丢乹") ⟫ʷ
lem-F1-X-CS0at2 c4 = derive (ℓ "亇乩乩亇丢侬") (ℓ "侬侬侬亇乩乩亇丢乹")
  (re 5 1 (ℓ "仞亭侪亭侫") ∷
   re 7 1 (ℓ "乇") ∷
   re 9 1 (ℓ "么") ∷
   rw 0 (q212 c4) ∷
   rw 1 (q84 c4) ∷
   rw 4 (q213 c4) ∷
   rw 3 (q214 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw 5 (q68 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw 2 (q215 c4) ∷
   rw 4 (q216 c4) ∷
   rw⁻ 3 (q217 c4) ∷
   rw 4 (q218 c4) ∷
   rw⁻ 5 (q219 c4) ∷
   rw 6 (q218 c4) ∷
   rw⁻ 7 (q220 c4) ∷
   rw⁻ 3 (q216 c4) ∷
   rw 4 (q213 c4) ∷
   rw⁻ 2 (q221 c4) ∷
   rw 1 (q222 c4) ∷
   rw⁻ 3 (q62 c4) ∷
   rw 2 (q68 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q66 c4) ∷
   rw 6 (q102 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q63 c4) ∷
   rw 2 (q62 c4) ∷
   rw⁻ 3 (q84 c4) ∷
   rw 3 (q84 c4) ∷
   rw⁻ 6 (q223 c4) ∷
   rw 5 (q224 c4) ∷
   rw⁻ 4 (q223 c4) ∷
   rw 3 (q224 c4) ∷
   rw⁻ 4 (q84 c4) ∷
   rw 4 (q84 c4) ∷
   rw 7 (q213 c4) ∷
   rw 6 (q214 c4) ∷
   rw⁻ 9 (q62 c4) ∷
   rw 8 (q68 c4) ∷
   rw 9 (q67 c4) ∷
   rw 10 (q102 c4) ∷
   rw 11 (q66 c4) ∷
   rw 12 (q102 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q63 c4) ∷
   rw 8 (q62 c4) ∷
   rw 5 (q215 c4) ∷
   rw 7 (q216 c4) ∷
   rw⁻ 6 (q217 c4) ∷
   rw 7 (q218 c4) ∷
   rw⁻ 8 (q219 c4) ∷
   rw 9 (q218 c4) ∷
   rw⁻ 10 (q220 c4) ∷
   rw⁻ 6 (q216 c4) ∷
   rw 7 (q213 c4) ∷
   rw⁻ 5 (q221 c4) ∷
   rw 4 (q222 c4) ∷
   rw⁻ 6 (q62 c4) ∷
   rw 5 (q68 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q63 c4) ∷
   rw 5 (q62 c4) ∷
   rw⁻ 6 (q84 c4) ∷
   rw 6 (q84 c4) ∷
   rw⁻ 9 (q225 c4) ∷
   rw 8 (q226 c4) ∷
   rw⁻ 7 (q225 c4) ∷
   rw 6 (q226 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   rw 1 (q227 c4) ∷
   rw 3 (q228 c4) ∷
   rw 0 (q229 c4) ∷
   rw⁻ 0 (q230 c4) ∷ []) Eq.refl

private
  q231 : Ws → Eqn
  q231 c4 = wpE 954 c4
  q232 : Ws → Eqn
  q232 c4 = sE 1735 (lem-nf-X-CS1at0 c4)

-- F1-X-CS1@0: 86 steps
lem-F1-X-CS1at0 : Ws → ⟪ (ℓ "亄乕乕亄丢俄") ⟫ʷ ≈ ⟪ (ℓ "俄俄俄亄乕乕亄丢丽") ⟫ʷ
lem-F1-X-CS1at0 c4 = derive (ℓ "亄乕乕亄丢俄") (ℓ "俄俄俄亄乕乕亄丢丽")
  (re 5 1 (ℓ "伱亮係亮促") ∷
   re 7 1 (ℓ "丶") ∷
   re 9 1 (ℓ "丷") ∷
   rw 0 (q187 c4) ∷
   rw 1 (q49 c4) ∷
   rw 4 (q172 c4) ∷
   rw 3 (q173 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw 2 (q174 c4) ∷
   rw 4 (q39 c4) ∷
   rw⁻ 3 (q175 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 5 (q177 c4) ∷
   rw 6 (q176 c4) ∷
   rw⁻ 7 (q178 c4) ∷
   rw⁻ 3 (q39 c4) ∷
   rw 4 (q172 c4) ∷
   rw⁻ 2 (q179 c4) ∷
   rw⁻ 1 (q180 c4) ∷
   rw⁻ 3 (q104 c4) ∷
   rw 2 (q105 c4) ∷
   rw 3 (q67 c4) ∷
   rw 4 (q102 c4) ∷
   rw 5 (q66 c4) ∷
   rw 6 (q102 c4) ∷
   rw 7 (q64 c4) ∷
   rw 8 (q106 c4) ∷
   rw 2 (q104 c4) ∷
   rw⁻ 3 (q49 c4) ∷
   rw 3 (q49 c4) ∷
   rw⁻ 6 (q72 c4) ∷
   rw 5 (q54 c4) ∷
   rw⁻ 4 (q72 c4) ∷
   rw 3 (q54 c4) ∷
   rw⁻ 4 (q49 c4) ∷
   rw 4 (q49 c4) ∷
   rw 7 (q172 c4) ∷
   rw 6 (q173 c4) ∷
   rw⁻ 9 (q104 c4) ∷
   rw 8 (q105 c4) ∷
   rw 9 (q67 c4) ∷
   rw 10 (q102 c4) ∷
   rw 11 (q66 c4) ∷
   rw 12 (q102 c4) ∷
   rw 13 (q64 c4) ∷
   rw 14 (q106 c4) ∷
   rw 8 (q104 c4) ∷
   rw 5 (q174 c4) ∷
   rw 7 (q39 c4) ∷
   rw⁻ 6 (q175 c4) ∷
   rw 7 (q176 c4) ∷
   rw⁻ 8 (q177 c4) ∷
   rw 9 (q176 c4) ∷
   rw⁻ 10 (q178 c4) ∷
   rw⁻ 6 (q39 c4) ∷
   rw 7 (q172 c4) ∷
   rw⁻ 5 (q179 c4) ∷
   rw⁻ 4 (q180 c4) ∷
   rw⁻ 6 (q104 c4) ∷
   rw 5 (q105 c4) ∷
   rw 6 (q67 c4) ∷
   rw 7 (q102 c4) ∷
   rw 8 (q66 c4) ∷
   rw 9 (q102 c4) ∷
   rw 10 (q64 c4) ∷
   rw 11 (q106 c4) ∷
   rw 5 (q104 c4) ∷
   rw⁻ 6 (q49 c4) ∷
   rw 6 (q49 c4) ∷
   rw⁻ 9 (q181 c4) ∷
   rw 8 (q182 c4) ∷
   rw⁻ 7 (q181 c4) ∷
   rw 6 (q182 c4) ∷
   rw⁻ 7 (q49 c4) ∷
   rw 1 (q183 c4) ∷
   rw 3 (q184 c4) ∷
   rw 0 (q231 c4) ∷
   rw⁻ 0 (q232 c4) ∷ []) Eq.refl

private
  q233 : Ws → Eqn
  q233 c4 = wlE 1169 (lit c4)
  q234 : Ws → Eqn
  q234 c4 = sE 1736 (lem-nf-X-CS1at1 c4)

-- F1-X-CS1@1: 86 steps
lem-F1-X-CS1at1 : Ws → ⟪ (ℓ "亇乩乩亇丢侧") ⟫ʷ ≈ ⟪ (ℓ "侧侧侧亇乩乩亇丢乕") ⟫ʷ
lem-F1-X-CS1at1 c4 = derive (ℓ "亇乩乩亇丢侧") (ℓ "侧侧侧亇乩乩亇丢乕")
  (re 5 1 (ℓ "仄亲侥亲侦") ∷
   re 7 1 (ℓ "乎") ∷
   re 9 1 (ℓ "乏") ∷
   rw 0 (q212 c4) ∷
   rw 1 (q188 c4) ∷
   rw 4 (q189 c4) ∷
   rw 3 (q190 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 5 (q192 c4) ∷
   rw 6 (q193 c4) ∷
   rw 7 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw 9 (q194 c4) ∷
   rw 10 (q196 c4) ∷
   rw 11 (q197 c4) ∷
   rw 5 (q191 c4) ∷
   rw 2 (q198 c4) ∷
   rw 4 (q199 c4) ∷
   rw⁻ 3 (q200 c4) ∷
   rw 4 (q201 c4) ∷
   rw⁻ 5 (q202 c4) ∷
   rw 6 (q201 c4) ∷
   rw⁻ 7 (q203 c4) ∷
   rw⁻ 3 (q199 c4) ∷
   rw 4 (q189 c4) ∷
   rw⁻ 2 (q204 c4) ∷
   rw 1 (q140 c4) ∷
   rw⁻ 3 (q191 c4) ∷
   rw 2 (q192 c4) ∷
   rw 3 (q193 c4) ∷
   rw 4 (q194 c4) ∷
   rw 5 (q195 c4) ∷
   rw 6 (q194 c4) ∷
   rw 7 (q196 c4) ∷
   rw 8 (q197 c4) ∷
   rw 2 (q191 c4) ∷
   rw⁻ 3 (q188 c4) ∷
   rw 3 (q188 c4) ∷
   rw⁻ 6 (q205 c4) ∷
   rw 5 (q206 c4) ∷
   rw⁻ 4 (q205 c4) ∷
   rw 3 (q206 c4) ∷
   rw⁻ 4 (q188 c4) ∷
   rw 4 (q188 c4) ∷
   rw 7 (q189 c4) ∷
   rw 6 (q190 c4) ∷
   rw⁻ 9 (q191 c4) ∷
   rw 8 (q192 c4) ∷
   rw 9 (q193 c4) ∷
   rw 10 (q194 c4) ∷
   rw 11 (q195 c4) ∷
   rw 12 (q194 c4) ∷
   rw 13 (q196 c4) ∷
   rw 14 (q197 c4) ∷
   rw 8 (q191 c4) ∷
   rw 5 (q198 c4) ∷
   rw 7 (q199 c4) ∷
   rw⁻ 6 (q200 c4) ∷
   rw 7 (q201 c4) ∷
   rw⁻ 8 (q202 c4) ∷
   rw 9 (q201 c4) ∷
   rw⁻ 10 (q203 c4) ∷
   rw⁻ 6 (q199 c4) ∷
   rw 7 (q189 c4) ∷
   rw⁻ 5 (q204 c4) ∷
   rw 4 (q140 c4) ∷
   rw⁻ 6 (q191 c4) ∷
   rw 5 (q192 c4) ∷
   rw 6 (q193 c4) ∷
   rw 7 (q194 c4) ∷
   rw 8 (q195 c4) ∷
   rw 9 (q194 c4) ∷
   rw 10 (q196 c4) ∷
   rw 11 (q197 c4) ∷
   rw 5 (q191 c4) ∷
   rw⁻ 6 (q188 c4) ∷
   rw 6 (q188 c4) ∷
   rw⁻ 9 (q207 c4) ∷
   rw 8 (q208 c4) ∷
   rw⁻ 7 (q207 c4) ∷
   rw 6 (q208 c4) ∷
   rw⁻ 7 (q188 c4) ∷
   rw 1 (q209 c4) ∷
   rw 3 (q167 c4) ∷
   rw 0 (q233 c4) ∷
   rw⁻ 0 (q234 c4) ∷ []) Eq.refl
