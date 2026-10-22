{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD017 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D017 (Sᴰ : SD017) where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl ; wp)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)
open import Examples.Groups.Clifford+CS.Five.Reflect using (Eqn ; eqn ; rw ; rw⁻ ; re ; derive)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS23-CCZ014 ; lem-comm-CS24-CCZ013 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-CCZ013 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ014-CX23 ; lem-comm-CX40-CCZ123)

-- The lemmas of other derivation modules (DSig).
private
  lem-sym-ab-at0210243143 : Ws → St 14
  lem-sym-ab-at0210243143 = pickᴰ 0 Sᴰ
  lem-sym-ab-at0310243142 : Ws → St 754
  lem-sym-ab-at0310243142 = pickᴰ 1 Sᴰ
  lem-sym-ab-at032032 : Ws → St 15
  lem-sym-ab-at032032 = pickᴰ 2 Sᴰ
  lem-sym-ab-at13243142 : Ws → St 755
  lem-sym-ab-at13243142 = pickᴰ 3 Sᴰ
  lem-sym-ab-at022330 : Ws → St 756
  lem-sym-ab-at022330 = pickᴰ 4 Sᴰ
  lem-sym-ab-at0330 : Ws → St 757
  lem-sym-ab-at0330 = pickᴰ 5 Sᴰ
  lem-nat-SWbc-at041041 : Ws → St 758
  lem-nat-SWbc-at041041 = pickᴰ 6 Sᴰ
  lem-nat-SWbc-at0413203142 : Ws → St 759
  lem-nat-SWbc-at0413203142 = pickᴰ 7 Sᴰ
  lem-nat-SWbc-at0413213042 : Ws → St 760
  lem-nat-SWbc-at0413213042 = pickᴰ 8 Sᴰ
  lem-nat-SWbc-at04233240 : Ws → St 761
  lem-nat-SWbc-at04233240 = pickᴰ 9 Sᴰ
  lem-nat-SWbc-at0440 : Ws → St 762
  lem-nat-SWbc-at0440 = pickᴰ 10 Sᴰ
  lem-sym-ab-at02102331 : Ws → St 763
  lem-sym-ab-at02102331 = pickᴰ 11 Sᴰ
  lem-sym-ab-at031031 : Ws → St 764
  lem-sym-ab-at031031 = pickᴰ 12 Sᴰ
  lem-box-tQ-at03102132 : Ws → St 78
  lem-box-tQ-at03102132 = pickᴰ 13 Sᴰ
  lem-box-tQ-at032032 : Ws → St 25
  lem-box-tQ-at032032 = pickᴰ 14 Sᴰ
  lem-box-tQ-at04203243 : Ws → St 26
  lem-box-tQ-at04203243 = pickᴰ 15 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 89
  lem-box-tQ-at0310213442 = pickᴰ 16 Sᴰ
  lem-nat-SWbc-at02102331 : Ws → St 765
  lem-nat-SWbc-at02102331 = pickᴰ 17 Sᴰ
  lem-nat-SWbc-at04122041 : Ws → St 766
  lem-nat-SWbc-at04122041 = pickᴰ 18 Sᴰ
  lem-nat-SWbc-at04122140 : Ws → St 767
  lem-nat-SWbc-at04122140 = pickᴰ 19 Sᴰ
  lem-nat-SWbc-at0412233041 : Ws → St 768
  lem-nat-SWbc-at0412233041 = pickᴰ 20 Sᴰ
  lem-nat-SWbc-at0412233140 : Ws → St 769
  lem-nat-SWbc-at0412233140 = pickᴰ 21 Sᴰ
  lem-nat-SWbc-at0413213240 : Ws → St 770
  lem-nat-SWbc-at0413213240 = pickᴰ 22 Sᴰ
  lem-nat-SWbc-at04133140 : Ws → St 771
  lem-nat-SWbc-at04133140 = pickᴰ 23 Sᴰ
  lem-nat-SWbc-at142142 : Ws → St 772
  lem-nat-SWbc-at142142 = pickᴰ 24 Sᴰ
  lem-box-tQ-at0314203142 : Ws → St 191
  lem-box-tQ-at0314203142 = pickᴰ 25 Sᴰ
  lem-t-cP-at03102132 : Ws → St 773
  lem-t-cP-at03102132 = pickᴰ 26 Sᴰ
  lem-t-cP-at032032 : Ws → St 774
  lem-t-cP-at032032 = pickᴰ 27 Sᴰ
  lem-tP-at02102331 : Ws → St 271
  lem-tP-at02102331 = pickᴰ 28 Sᴰ
  lem-tP-at02142041 : Ws → St 274
  lem-tP-at02142041 = pickᴰ 29 Sᴰ
  lem-tP-at0314203241 : Ws → St 277
  lem-tP-at0314203241 = pickᴰ 30 Sᴰ
  lem-tP-at03243042 : Ws → St 279
  lem-tP-at03243042 = pickᴰ 31 Sᴰ
  lem-tP-at04103143 : Ws → St 280
  lem-tP-at04103143 = pickᴰ 32 Sᴰ
  lem-tP-at04122041 : Ws → St 281
  lem-tP-at04122041 = pickᴰ 33 Sᴰ
  lem-tP-at0412233041 : Ws → St 282
  lem-tP-at0412233041 = pickᴰ 34 Sᴰ
  lem-tP-at04233042 : Ws → St 283
  lem-tP-at04233042 = pickᴰ 35 Sᴰ
  lem-tP-at142142 : Ws → St 284
  lem-tP-at142142 = pickᴰ 36 Sᴰ
  lem-P-box-at0410213243 : Ws → St 775
  lem-P-box-at0410213243 = pickᴰ 37 Sᴰ
  lem-P-box-at04203243 : Ws → St 776
  lem-P-box-at04203243 = pickᴰ 38 Sᴰ
  lem-box-tQ-at0412233041 : Ws → St 287
  lem-box-tQ-at0412233041 = pickᴰ 39 Sᴰ
  lem-box-tQ-at0412233140 : Ws → St 301
  lem-box-tQ-at0412233140 = pickᴰ 40 Sᴰ
  lem-t-cP-at0310213442 : Ws → St 777
  lem-t-cP-at0310213442 = pickᴰ 41 Sᴰ
  lem-t-cP-at04203243 : Ws → St 778
  lem-t-cP-at04203243 = pickᴰ 42 Sᴰ
  lem-tP-at02142140 : Ws → St 292
  lem-tP-at02142140 = pickᴰ 43 Sᴰ
  lem-tP-at0410233142 : Ws → St 305
  lem-tP-at0410233142 = pickᴰ 44 Sᴰ
  lem-tP-at0410233241 : Ws → St 293
  lem-tP-at0410233241 = pickᴰ 45 Sᴰ
  lem-tP-at0412213043 : Ws → St 294
  lem-tP-at0412213043 = pickᴰ 46 Sᴰ
  lem-tP-at04122140 : Ws → St 306
  lem-tP-at04122140 = pickᴰ 47 Sᴰ
  lem-tP-at0412233140 : Ws → St 307
  lem-tP-at0412233140 = pickᴰ 48 Sᴰ
  lem-tP-at0413203142 : Ws → St 295
  lem-tP-at0413203142 = pickᴰ 49 Sᴰ
  lem-tP-at0413203241 : Ws → St 308
  lem-tP-at0413203241 = pickᴰ 50 Sᴰ
  lem-tP-at0413213240 : Ws → St 309
  lem-tP-at0413213240 = pickᴰ 51 Sᴰ
  lem-tP-at0440 : Ws → St 296
  lem-tP-at0440 = pickᴰ 52 Sᴰ
  lem-box-cP-at03102132 : Ws → St 728
  lem-box-cP-at03102132 = pickᴰ 53 Sᴰ
  lem-box-cP-at032032 : Ws → St 729
  lem-box-cP-at032032 = pickᴰ 54 Sᴰ
  lem-box-cP-at0410213243 : Ws → St 730
  lem-box-cP-at0410213243 = pickᴰ 55 Sᴰ
  lem-box-cP-at04203243 : Ws → St 779
  lem-box-cP-at04203243 = pickᴰ 56 Sᴰ
  lem-sym-bc-at0220 : Ws → St 780
  lem-sym-bc-at0220 = pickᴰ 57 Sᴰ
  lem-sym-bc-at03102132 : Ws → St 735
  lem-sym-bc-at03102132 = pickᴰ 58 Sᴰ
  lem-sym-bc-at0310213442 : Ws → St 736
  lem-sym-bc-at0310213442 = pickᴰ 59 Sᴰ
  lem-sym-bc-at032032 : Ws → St 737
  lem-sym-bc-at032032 = pickᴰ 60 Sᴰ
  lem-sym-bc-at04203243 : Ws → St 738
  lem-sym-bc-at04203243 = pickᴰ 61 Sᴰ
  lem-sym-bc-at14233142 : Ws → St 781
  lem-sym-bc-at14233142 = pickᴰ 62 Sᴰ
  lem-QVQ-at02102331 : Ws → St 782
  lem-QVQ-at02102331 = pickᴰ 63 Sᴰ
  lem-QVQ-at02142041 : Ws → St 783
  lem-QVQ-at02142041 = pickᴰ 64 Sᴰ
  lem-QVQ-at02142140 : Ws → St 784
  lem-QVQ-at02142140 = pickᴰ 65 Sᴰ
  lem-QVQ-at0314203241 : Ws → St 785
  lem-QVQ-at0314203241 = pickᴰ 66 Sᴰ
  lem-QVQ-at03243042 : Ws → St 786
  lem-QVQ-at03243042 = pickᴰ 67 Sᴰ
  lem-QVQ-at0410233142 : Ws → St 787
  lem-QVQ-at0410233142 = pickᴰ 68 Sᴰ
  lem-QVQ-at0410233241 : Ws → St 788
  lem-QVQ-at0410233241 = pickᴰ 69 Sᴰ
  lem-QVQ-at04103143 : Ws → St 789
  lem-QVQ-at04103143 = pickᴰ 70 Sᴰ
  lem-QVQ-at04122041 : Ws → St 790
  lem-QVQ-at04122041 = pickᴰ 71 Sᴰ
  lem-QVQ-at0412213043 : Ws → St 791
  lem-QVQ-at0412213043 = pickᴰ 72 Sᴰ
  lem-QVQ-at04122140 : Ws → St 792
  lem-QVQ-at04122140 = pickᴰ 73 Sᴰ
  lem-QVQ-at0412233041 : Ws → St 793
  lem-QVQ-at0412233041 = pickᴰ 74 Sᴰ
  lem-QVQ-at0412233140 : Ws → St 794
  lem-QVQ-at0412233140 = pickᴰ 75 Sᴰ
  lem-QVQ-at0413203142 : Ws → St 795
  lem-QVQ-at0413203142 = pickᴰ 76 Sᴰ
  lem-QVQ-at0413203241 : Ws → St 796
  lem-QVQ-at0413203241 = pickᴰ 77 Sᴰ
  lem-QVQ-at0413213240 : Ws → St 797
  lem-QVQ-at0413213240 = pickᴰ 78 Sᴰ
  lem-QVQ-at04233042 : Ws → St 798
  lem-QVQ-at04233042 = pickᴰ 79 Sᴰ
  lem-QVQ-at0440 : Ws → St 799
  lem-QVQ-at0440 = pickᴰ 80 Sᴰ
  lem-QVQ-at142142 : Ws → St 800
  lem-QVQ-at142142 = pickᴰ 81 Sᴰ
  lem-SWbc-box-at02102331 : Ws → St 801
  lem-SWbc-box-at02102331 = pickᴰ 82 Sᴰ
  lem-SWbc-box-at041041 : Ws → St 802
  lem-SWbc-box-at041041 = pickᴰ 83 Sᴰ
  lem-SWbc-box-at04122041 : Ws → St 803
  lem-SWbc-box-at04122041 = pickᴰ 84 Sᴰ
  lem-SWbc-box-at04122140 : Ws → St 804
  lem-SWbc-box-at04122140 = pickᴰ 85 Sᴰ
  lem-SWbc-box-at0412233041 : Ws → St 805
  lem-SWbc-box-at0412233041 = pickᴰ 86 Sᴰ
  lem-SWbc-box-at0412233140 : Ws → St 806
  lem-SWbc-box-at0412233140 = pickᴰ 87 Sᴰ
  lem-SWbc-box-at0413203142 : Ws → St 807
  lem-SWbc-box-at0413203142 = pickᴰ 88 Sᴰ
  lem-SWbc-box-at0413213042 : Ws → St 808
  lem-SWbc-box-at0413213042 = pickᴰ 89 Sᴰ
  lem-SWbc-box-at0413213240 : Ws → St 809
  lem-SWbc-box-at0413213240 = pickᴰ 90 Sᴰ
  lem-SWbc-box-at04133140 : Ws → St 810
  lem-SWbc-box-at04133140 = pickᴰ 91 Sᴰ
  lem-SWbc-box-at04233240 : Ws → St 811
  lem-SWbc-box-at04233240 = pickᴰ 92 Sᴰ
  lem-SWbc-box-at0440 : Ws → St 812
  lem-SWbc-box-at0440 = pickᴰ 93 Sᴰ
  lem-SWbc-box-at142142 : Ws → St 813
  lem-SWbc-box-at142142 = pickᴰ 94 Sᴰ
  lem-XCSX-box-2-at04122041 : Ws → St 814
  lem-XCSX-box-2-at04122041 = pickᴰ 95 Sᴰ
  lem-box-cP-at0213243041 : Ws → St 750
  lem-box-cP-at0213243041 = pickᴰ 96 Sᴰ
  lem-box-cP-at0310213442 : Ws → St 752
  lem-box-cP-at0310213442 = pickᴰ 97 Sᴰ
  lem-sym-bc-at021021 : Ws → St 815
  lem-sym-bc-at021021 = pickᴰ 98 Sᴰ
  lem-sym-bc-at0210213443 : Ws → St 816
  lem-sym-bc-at0210213443 = pickᴰ 99 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 78 (lem-box-tQ-at03102132 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 728 (lem-box-cP-at03102132 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 443 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 773 (lem-t-cP-at03102132 c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 305 (lit c4)

-- box2 @03102132: 11 steps
lem-box2-at03102132 : Ws → ⟪ (Bx3-0124 ∷ Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03102132 c4 = derive (Bx3-0124 ∷ Bx3-0124 ∷ []) []
  (rw 0 (q1 c4) ∷
   rw 4 (q2 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q4 c4) ∷
   rw⁻ 5 (q2 c4) ∷
   rw 5 (q1 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q3 c4) ∷ []) Eq.refl

private
  q6 : Ws → Eqn
  q6 c4 = wlE 1319 (lit c4)
  q7 : Ws → Eqn
  q7 c4 = sE 783 (lem-QVQ-at02142041 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 274 (lem-tP-at02142041 c4)
  q9 : Ws → Eqn
  q9 c4 = wpE 19 c4

-- box-cP @02142041: 12 steps
lem-box-cP-at02142041 : Ws → ⟪ (Bx2-4031 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at02142041 c4 = derive (Bx2-4031 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff204 ∷ Bx4-231 ∷ Toff204 ∷ CCZ024 ∷ Bx4-231 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q6 c4) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-41 ∷ Toff423 ∷ CCZ234 ∷ Bx2-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = sE 785 (lem-QVQ-at0314203241 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 277 (lem-tP-at0314203241 c4)
  q12 : Ws → Eqn
  q12 c4 = wpE 351 c4

-- box-cP @0314203241: 12 steps
lem-box-cP-at0314203241 : Ws → ⟪ (Bx3-4021 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) ⟫ʷ
lem-box-cP-at0314203241 c4 = derive (Bx3-4021 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff304 ∷ Bx4-321 ∷ Toff304 ∷ CCZ034 ∷ Bx4-321 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   re 4 1 (CZ14 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   rw⁻ 2 (q6 c4) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx3-41 ∷ Toff423 ∷ CCZ234 ∷ Bx3-41 ∷ []) ∷
   re 7 1 (CZ14 ∷ []) ∷
   re 10 1 (CZ14 ∷ []) ∷
   rw⁻ 5 (q6 c4) ∷
   rw 2 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = sE 737 (lem-sym-bc-at032032 c4)

-- box-perm-1324 @032032: 1 steps
lem-box-perm-1324-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1204 ∷ []) ⟫ʷ
lem-box-perm-1324-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-1204 ∷ [])
  (rw 0 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = sE 757 (lem-sym-ab-at0330 c4)

-- box-perm-3124 @032032: 2 steps
lem-box-perm-3124-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2104 ∷ []) ⟫ʷ
lem-box-perm-3124-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-2104 ∷ [])
  (rw 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = sE 780 (lem-sym-bc-at0220 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 756 (lem-sym-ab-at022330 c4)

-- box-perm-3124 @0220: 2 steps
lem-box-perm-3124-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3104 ∷ []) ⟫ʷ
lem-box-perm-3124-at0220 c4 = derive (Bx2-1034 ∷ []) (Bx2-3104 ∷ [])
  (rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = sE 15 (lem-sym-ab-at032032 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 735 (lem-sym-bc-at03102132 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 764 (lem-sym-ab-at031031 c4)

-- box-perm-3214 @032032: 3 steps
lem-box-perm-3214-at032032 : Ws → ⟪ (Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-2014 ∷ []) ⟫ʷ
lem-box-perm-3214-at032032 c4 = derive (Bx3-1024 ∷ []) (Bx3-2014 ∷ [])
  (rw 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 0 (q19 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = sE 815 (lem-sym-bc-at021021 c4)

-- box-perm-1324 @021021: 1 steps
lem-box-perm-1324-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0314 ∷ []) ⟫ʷ
lem-box-perm-1324-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-0314 ∷ [])
  (rw 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = wpE 1232 c4
  q22 : Ws → Eqn
  q22 c4 = sE 782 (lem-QVQ-at02102331 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 271 (lem-tP-at02102331 c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 635 (lit c4)

-- box-cP @02102331: 12 steps
lem-box-cP-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ []) ⟫ʷ
lem-box-cP-at02102331 c4 = derive (Bx2-0314 ∷ []) (CCZ023 ∷ Toff214 ∷ CCZ023 ∷ Toff214 ∷ [])
  (re 0 1 (CCZ023 ∷ Toff203 ∷ Bx0-214 ∷ Toff203 ∷ CCZ023 ∷ Bx0-214 ∷ []) ∷
   re 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw 2 (q21 c4) ∷
   re 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-04 ∷ Toff012 ∷ CCZ012 ∷ Bx2-04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw 5 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = sE 813 (lem-SWbc-box-at142142 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 772 (lem-nat-SWbc-at142142 c4)

-- sym-bc @142142: 2 steps
lem-sym-bc-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4312 ∷ []) ⟫ʷ
lem-sym-bc-at142142 c4 = derive (Bx0-4132 ∷ []) (Bx0-4312 ∷ [])
  (rw⁻ 0 (q25 c4) ∷
   rw 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = sE 755 (lem-sym-ab-at13243142 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 781 (lem-sym-bc-at14233142 c4)

-- box-perm-2314 @13243142: 2 steps
lem-box-perm-2314-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4132 ∷ []) ⟫ʷ
lem-box-perm-2314-at13243142 c4 = derive (Bx0-3412 ∷ []) (Bx0-4132 ∷ [])
  (rw 0 (q27 c4) ∷
   rw 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wlE 344 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = sE 786 (lem-QVQ-at03243042 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 279 (lem-tP-at03243042 c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 788 (lit c4)

-- box-cP @03243042: 12 steps
lem-box-cP-at03243042 : Ws → ⟪ (Bx3-1402 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) ⟫ʷ
lem-box-cP-at03243042 c4 = derive (Bx3-1402 ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff314 ∷ Bx1-302 ∷ Toff314 ∷ CCZ134 ∷ Bx1-302 ∷ []) ∷
   re 2 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q29 c4) ∷
   re 5 1 (CCZ013 ∷ Toff103 ∷ Bx3-12 ∷ Toff103 ∷ CCZ013 ∷ Bx3-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = sE 763 (lem-sym-ab-at02102331 c4)

-- box-perm-3124 @021021: 2 steps
lem-box-perm-3124-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3014 ∷ []) ⟫ʷ
lem-box-perm-3124-at021021 c4 = derive (Bx2-0134 ∷ []) (Bx2-3014 ∷ [])
  (rw 0 (q20 c4) ∷
   rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = sE 801 (lem-SWbc-box-at02102331 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 765 (lem-nat-SWbc-at02102331 c4)

-- sym-bc @02102331: 2 steps
lem-sym-bc-at02102331 : Ws → ⟪ (Bx2-0314 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym-bc-at02102331 c4 = derive (Bx2-0314 ∷ []) (Bx2-0134 ∷ [])
  (rw⁻ 0 (q34 c4) ∷
   rw 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wpE 661 c4
  q37 : Ws → Eqn
  q37 c4 = sE 800 (lem-QVQ-at142142 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 284 (lem-tP-at142142 c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 51 c4

-- box-cP @142142: 12 steps
lem-box-cP-at142142 : Ws → ⟪ (Bx0-4132 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) ⟫ʷ
lem-box-cP-at142142 c4 = derive (Bx0-4132 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  (re 0 1 (CCZ014 ∷ Toff014 ∷ Bx4-032 ∷ Toff014 ∷ CCZ014 ∷ Bx4-032 ∷ []) ∷
   re 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   re 4 1 (CZ24 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   rw⁻ 2 (q36 c4) ∷
   re 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-42 ∷ Toff403 ∷ CCZ034 ∷ Bx0-42 ∷ []) ∷
   re 7 1 (CZ24 ∷ []) ∷
   re 10 1 (CZ24 ∷ []) ∷
   rw⁻ 5 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = sE 25 (lem-box-tQ-at032032 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 729 (lem-box-cP-at032032 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 774 (lem-t-cP-at032032 c4)

-- box2 @032032: 11 steps
lem-box2-at032032 : Ws → ⟪ (Bx3-1024 ∷ Bx3-1024 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at032032 c4 = derive (Bx3-1024 ∷ Bx3-1024 ∷ []) []
  (rw 0 (q40 c4) ∷
   rw 4 (q41 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q42 c4) ∷
   rw⁻ 5 (q41 c4) ∷
   rw 5 (q40 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q3 c4) ∷ []) Eq.refl

private
  q43 : Ws → Eqn
  q43 c4 = sE 803 (lem-SWbc-box-at04122041 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 766 (lem-nat-SWbc-at04122041 c4)

-- sym-bc @04122041: 2 steps
lem-sym-bc-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-sym-bc-at04122041 c4 = derive (Bx4-2031 ∷ []) (Bx4-2301 ∷ [])
  (rw⁻ 0 (q43 c4) ∷
   rw 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = wpE 218 c4
  q46 : Ws → Eqn
  q46 c4 = sE 793 (lem-QVQ-at0412233041 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 282 (lem-tP-at0412233041 c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 457 (lit c4)

-- box-cP @0412233041: 12 steps
lem-box-cP-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-box-cP-at0412233041 c4 = derive (Bx4-2301 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-401 ∷ Toff423 ∷ CCZ234 ∷ Bx2-401 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q45 c4) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx4-21 ∷ Toff204 ∷ CCZ024 ∷ Bx4-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wlE 1271 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = sE 790 (lem-QVQ-at04122041 c4)
  q51 : Ws → Eqn
  q51 c4 = sE 281 (lem-tP-at04122041 c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1323 c4

-- box-cP @04122041: 12 steps
lem-box-cP-at04122041 : Ws → ⟪ (Bx4-2031 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-box-cP-at04122041 c4 = derive (Bx4-2031 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff402 ∷ Bx2-431 ∷ Toff402 ∷ CCZ024 ∷ Bx2-431 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw⁻ 2 (q49 c4) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-21 ∷ Toff234 ∷ CCZ234 ∷ Bx4-21 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw⁻ 5 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 2 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = wpE 1331 c4
  q54 : Ws → Eqn
  q54 c4 = sE 789 (lem-QVQ-at04103143 c4)
  q55 : Ws → Eqn
  q55 c4 = sE 280 (lem-tP-at04103143 c4)

-- box-cP @04103143: 12 steps
lem-box-cP-at04103143 : Ws → ⟪ (Bx4-0213 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ []) ⟫ʷ
lem-box-cP-at04103143 c4 = derive (Bx4-0213 ∷ []) (CCZ024 ∷ Toff413 ∷ CCZ024 ∷ Toff413 ∷ [])
  (re 0 1 (CCZ024 ∷ Toff402 ∷ Bx0-413 ∷ Toff402 ∷ CCZ024 ∷ Bx0-413 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw 2 (q53 c4) ∷
   re 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-03 ∷ Toff014 ∷ CCZ014 ∷ Bx4-03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw 5 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q52 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = wpE 212 c4
  q57 : Ws → Eqn
  q57 c4 = sE 798 (lem-QVQ-at04233042 c4)
  q58 : Ws → Eqn
  q58 c4 = sE 283 (lem-tP-at04233042 c4)
  q59 : Ws → Eqn
  q59 c4 = wlE 1474 (lit c4)

-- box-cP @04233042: 12 steps
lem-box-cP-at04233042 : Ws → ⟪ (Bx4-1302 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-box-cP-at04233042 c4 = derive (Bx4-1302 ∷ []) (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx1-402 ∷ Toff413 ∷ CCZ134 ∷ Bx1-402 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) ∷
   re 4 1 (CZ12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   rw 2 (q56 c4) ∷
   re 5 1 (CCZ014 ∷ Toff104 ∷ Bx4-12 ∷ Toff104 ∷ CCZ014 ∷ Bx4-12 ∷ []) ∷
   re 7 1 (CZ12 ∷ []) ∷
   re 10 1 (CZ12 ∷ []) ∷
   rw 5 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = sE 775 (lem-P-box-at0410213243 c4)
  q61 : Ws → Eqn
  q61 c4 = sE 730 (lem-box-cP-at0410213243 c4)
  q62 : Ws → Eqn
  q62 c4 = sE 287 (lem-box-tQ-at0412233041 c4)

-- pairs @0410213243: 4 steps
lem-pairs-at0410213243 : Ws → ⟪ (Bx4-0123 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2301 ∷ []) ⟫ʷ
lem-pairs-at0410213243 c4 = derive (Bx4-0123 ∷ []) (Bx4-2301 ∷ [])
  (rw⁻ 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = sE 805 (lem-SWbc-box-at0412233041 c4)
  q64 : Ws → Eqn
  q64 c4 = sE 768 (lem-nat-SWbc-at0412233041 c4)

-- sym-bc @0412233041: 2 steps
lem-sym-bc-at0412233041 : Ws → ⟪ (Bx4-2301 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2031 ∷ []) ⟫ʷ
lem-sym-bc-at0412233041 c4 = derive (Bx4-2301 ∷ []) (Bx4-2031 ∷ [])
  (rw⁻ 0 (q63 c4) ∷
   rw 0 (q64 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wlE 1441 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 1515 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = sE 779 (lem-box-cP-at04203243 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (K1 ∷ Toff423 ∷ []) (Toff423 ∷ K1 ∷ []) (c₂ (K ↑) (Toffᵗ))
  q69 : Ws → Eqn
  q69 c4 = eqn (CK01 ∷ Toff423 ∷ []) (Toff423 ∷ CK01 ∷ []) (c₂ (CK₀₁) (Toffᵗ))
  q70 : Ws → Eqn
  q70 c4 = eqn (S0 ∷ Toff423 ∷ []) (Toff423 ∷ S0 ∷ []) (c₁ (S) (Toffᵗ ↑))
  q71 : Ws → Eqn
  q71 c4 = wpE 1350 c4
  q72 : Ws → Eqn
  q72 c4 = wlE 1443 (lit c4)

-- F4-CS1-K1 @0440: 19 steps
lem-F4-CS1-K1-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ []) ⟫ʷ ≈ ⟪ (CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-K1-at0440 c4 = derive (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ []) (CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  (rw⁻ 2 (q65 c4) ∷
   re 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw⁻ 2 (q66 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 4 (q68 c4) ∷
   rw⁻ 5 (q69 c4) ∷
   rw⁻ 6 (q70 c4) ∷
   rw 3 (q71 c4) ∷
   rw⁻ 2 (q68 c4) ∷
   rw⁻ 3 (q69 c4) ∷
   rw⁻ 4 (q70 c4) ∷
   rw 1 (q71 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   re 6 1 (Sb4-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 4 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = wpE 1351 c4
  q74 : Ws → Eqn
  q74 c4 = wlE 1516 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (X0 ∷ Toff423 ∷ []) (Toff423 ∷ X0 ∷ []) (c₁ (X) (Toffᵗ ↑))
  q76 : Ws → Eqn
  q76 c4 = wlE 207 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wpE 53 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 54 c4
  q79 : Ws → Eqn
  q79 c4 = eqn (CS23⁻ ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4))
  q80 : Ws → Eqn
  q80 c4 = eqn (CS23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4))
  q81 : Ws → Eqn
  q81 c4 = wpE 1352 c4
  q82 : Ws → Eqn
  q82 c4 = wpE 1353 c4
  q83 : Ws → Eqn
  q83 c4 = wlE 463 (lit c4)
  q84 : Ws → Eqn
  q84 c4 = wpE 60 c4
  q85 : Ws → Eqn
  q85 c4 = wlE 1517 (lit c4)
  q86 : Ws → Eqn
  q86 c4 = wlE 1501 (lit c4)
  q87 : Ws → Eqn
  q87 c4 = wpE 61 c4
  q88 : Ws → Eqn
  q88 c4 = wpE 155 c4
  q89 : Ws → Eqn
  q89 c4 = eqn (CX23 ∷ CCZ014 ∷ []) (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4))
  q90 : Ws → Eqn
  q90 c4 = wpE 156 c4
  q91 : Ws → Eqn
  q91 c4 = wpE 157 c4
  q92 : Ws → Eqn
  q92 c4 = wpE 65 c4
  q93 : Ws → Eqn
  q93 c4 = wpE 1354 c4
  q94 : Ws → Eqn
  q94 c4 = wpE 1335 c4
  q95 : Ws → Eqn
  q95 c4 = wlE 929 (lit c4)
  q96 : Ws → Eqn
  q96 c4 = wlE 461 (lit c4)
  q97 : Ws → Eqn
  q97 c4 = eqn (CX10 ∷ Toff423 ∷ []) (Toff423 ∷ CX10 ∷ []) (c₂ (CX₁₀) (Toffᵗ))
  q98 : Ws → Eqn
  q98 c4 = wpE 1355 c4
  q99 : Ws → Eqn
  q99 c4 = wpE 311 c4
  q100 : Ws → Eqn
  q100 c4 = wpE 1318 c4
  q101 : Ws → Eqn
  q101 c4 = wpE 1356 c4
  q102 : Ws → Eqn
  q102 c4 = wlE 1509 (lit c4)
  q103 : Ws → Eqn
  q103 c4 = wlE 1518 (lit c4)
  q104 : Ws → Eqn
  q104 c4 = wlE 181 (lit c4)
  q105 : Ws → Eqn
  q105 c4 = wlE 1519 (lit c4)
  q106 : Ws → Eqn
  q106 c4 = wlE 341 (lit c4)
  q107 : Ws → Eqn
  q107 c4 = wlE 1520 (lit c4)
  q108 : Ws → Eqn
  q108 c4 = wlE 1521 (lit c4)
  q109 : Ws → Eqn
  q109 c4 = wlE 1522 (lit c4)
  q110 : Ws → Eqn
  q110 c4 = wpE 1357 c4
  q111 : Ws → Eqn
  q111 c4 = wpE 1023 c4
  q112 : Ws → Eqn
  q112 c4 = eqn (CCZ014 ∷ CX23 ∷ []) (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4))
  q113 : Ws → Eqn
  q113 c4 = wpE 1358 c4
  q114 : Ws → Eqn
  q114 c4 = wlE 1523 (lit c4)
  q115 : Ws → Eqn
  q115 c4 = wpE 1019 c4
  q116 : Ws → Eqn
  q116 c4 = wlE 1524 (lit c4)
  q117 : Ws → Eqn
  q117 c4 = wlE 1525 (lit c4)
  q118 : Ws → Eqn
  q118 c4 = wlE 1526 (lit c4)
  q119 : Ws → Eqn
  q119 c4 = wlE 1527 (lit c4)
  q120 : Ws → Eqn
  q120 c4 = wlE 1528 (lit c4)
  q121 : Ws → Eqn
  q121 c4 = wlE 1529 (lit c4)

-- F4-CS1-CS1 @0440: 286 steps
lem-F4-CS1-CS1-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-CS1-at0440 c4 = derive (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  (re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw 4 (q74 c4) ∷
   rw 3 (q75 c4) ∷
   rw 6 (q76 c4) ∷
   rw⁻ 10 (q77 c4) ∷
   rw⁻ 9 (q78 c4) ∷
   rw 8 (q79 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw 6 (q80 c4) ∷
   rw⁻ 7 (q76 c4) ∷
   rw⁻ 5 (q81 c4) ∷
   rw⁻ 4 (q73 c4) ∷
   rw 5 (q82 c4) ∷
   rw 6 (q83 c4) ∷
   rw 5 (q75 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   re 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 6 (q67 c4) ∷
   rw⁻ 5 (q84 c4) ∷
   rw 6 (q85 c4) ∷
   rw⁻ 7 (q84 c4) ∷
   rw 8 (q85 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw⁻ 10 (q87 c4) ∷
   rw⁻ 9 (q88 c4) ∷
   rw 8 (q89 c4) ∷
   rw⁻ 7 (q90 c4) ∷
   rw 6 (q89 c4) ∷
   rw⁻ 5 (q91 c4) ∷
   rw⁻ 4 (q92 c4) ∷
   rw 5 (q86 c4) ∷
   rw 5 (q93 c4) ∷
   rw⁻ 7 (q86 c4) ∷
   rw⁻ 13 (q87 c4) ∷
   rw⁻ 12 (q88 c4) ∷
   rw 11 (q89 c4) ∷
   rw⁻ 10 (q90 c4) ∷
   rw 9 (q89 c4) ∷
   rw⁻ 8 (q91 c4) ∷
   rw⁻ 7 (q92 c4) ∷
   rw 8 (q86 c4) ∷
   rw⁻ 6 (q94 c4) ∷
   rw 9 (q93 c4) ∷
   rw 8 (q95 c4) ∷
   rw 12 (q96 c4) ∷
   rw 11 (q97 c4) ∷
   rw 10 (q98 c4) ∷
   rw 9 (q97 c4) ∷
   rw 8 (q99 c4) ∷
   rw⁻ 9 (q95 c4) ∷
   rw 7 (q100 c4) ∷
   rw⁻ 8 (q101 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   re 3 1 (CS13 ∷ []) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 3 (q77 c4) ∷
   rw 4 (q102 c4) ∷
   rw⁻ 5 (q77 c4) ∷
   rw 6 (q102 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 2 (q86 c4) ∷
   rw⁻ 8 (q87 c4) ∷
   rw⁻ 7 (q88 c4) ∷
   rw 6 (q89 c4) ∷
   rw⁻ 5 (q90 c4) ∷
   rw 4 (q89 c4) ∷
   rw⁻ 3 (q91 c4) ∷
   rw⁻ 2 (q92 c4) ∷
   rw 3 (q86 c4) ∷
   rw 3 (q93 c4) ∷
   rw⁻ 5 (q86 c4) ∷
   rw⁻ 11 (q87 c4) ∷
   rw⁻ 10 (q88 c4) ∷
   rw 9 (q89 c4) ∷
   rw⁻ 8 (q90 c4) ∷
   rw 7 (q89 c4) ∷
   rw⁻ 6 (q91 c4) ∷
   rw⁻ 5 (q92 c4) ∷
   rw 6 (q86 c4) ∷
   rw⁻ 4 (q94 c4) ∷
   rw 7 (q93 c4) ∷
   rw 6 (q95 c4) ∷
   rw 10 (q96 c4) ∷
   rw 9 (q97 c4) ∷
   rw 8 (q98 c4) ∷
   rw 7 (q97 c4) ∷
   rw 6 (q99 c4) ∷
   rw⁻ 7 (q95 c4) ∷
   rw 5 (q100 c4) ∷
   rw⁻ 6 (q101 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw 1 (q67 c4) ∷
   rw⁻ 0 (q73 c4) ∷
   rw 2 (q74 c4) ∷
   rw 1 (q75 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw 6 (q79 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw 4 (q80 c4) ∷
   rw⁻ 5 (q76 c4) ∷
   rw⁻ 3 (q81 c4) ∷
   rw⁻ 2 (q73 c4) ∷
   rw 3 (q82 c4) ∷
   rw 4 (q83 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw 3 (q67 c4) ∷
   rw 2 (q76 c4) ∷
   rw⁻ 6 (q77 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw 4 (q79 c4) ∷
   rw⁻ 3 (q78 c4) ∷
   rw 2 (q80 c4) ∷
   rw⁻ 3 (q76 c4) ∷
   rw 3 (q83 c4) ∷
   rw 4 (q76 c4) ∷
   rw⁻ 8 (q77 c4) ∷
   rw⁻ 7 (q78 c4) ∷
   rw 6 (q79 c4) ∷
   rw⁻ 5 (q78 c4) ∷
   rw 4 (q80 c4) ∷
   rw⁻ 5 (q76 c4) ∷
   rw 5 (q83 c4) ∷
   rw⁻ 2 (q67 c4) ∷
   rw⁻ 3 (q103 c4) ∷
   rw 10 (q104 c4) ∷
   rw 3 (q105 c4) ∷
   rw 5 (q106 c4) ∷
   re 4 1 (Sb4-1-3-2 ∷ []) ∷
   re 6 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 2 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 3 (q107 c4) ∷
   re 2 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 4 1 (CS13 ∷ []) ∷
   re 6 1 (CS13⁻ ∷ []) ∷
   rw⁻ 3 (q108 c4) ∷
   rw 2 (q67 c4) ∷
   rw⁻ 5 (q109 c4) ∷
   rw⁻ 7 (q110 c4) ∷
   rw 4 (q111 c4) ∷
   rw 6 (q112 c4) ∷
   rw 7 (q113 c4) ∷
   rw⁻ 10 (q86 c4) ∷
   rw 9 (q92 c4) ∷
   rw 10 (q91 c4) ∷
   rw 11 (q112 c4) ∷
   rw 12 (q90 c4) ∷
   rw 13 (q112 c4) ∷
   rw 14 (q88 c4) ∷
   rw 15 (q87 c4) ∷
   rw 9 (q86 c4) ∷
   rw⁻ 3 (q114 c4) ∷
   rw 5 (q95 c4) ∷
   rw⁻ 4 (q99 c4) ∷
   rw⁻ 5 (q97 c4) ∷
   rw⁻ 6 (q98 c4) ∷
   rw⁻ 7 (q97 c4) ∷
   rw⁻ 8 (q96 c4) ∷
   rw⁻ 4 (q95 c4) ∷
   rw⁻ 5 (q109 c4) ∷
   rw⁻ 7 (q100 c4) ∷
   rw 9 (q95 c4) ∷
   rw⁻ 8 (q99 c4) ∷
   rw⁻ 9 (q97 c4) ∷
   rw⁻ 10 (q98 c4) ∷
   rw⁻ 11 (q97 c4) ∷
   rw⁻ 12 (q96 c4) ∷
   rw⁻ 8 (q95 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw⁻ 3 (q115 c4) ∷
   rw⁻ 5 (q101 c4) ∷
   rw 3 (q116 c4) ∷
   rw 2 (q112 c4) ∷
   rw⁻ 4 (q86 c4) ∷
   rw 3 (q92 c4) ∷
   rw 4 (q91 c4) ∷
   rw 5 (q112 c4) ∷
   rw 6 (q90 c4) ∷
   rw 7 (q112 c4) ∷
   rw 8 (q88 c4) ∷
   rw 9 (q87 c4) ∷
   rw 3 (q86 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   re 6 1 (Sb4-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 4 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 1 (q117 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw⁻ 4 (q119 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw 5 (q77 c4) ∷
   rw⁻ 4 (q102 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   re 6 1 (Sb4-1-3-2 ∷ []) ∷
   re 8 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 4 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 2 (q118 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   re 4 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 6 1 (CS13 ∷ []) ∷
   re 8 1 (CS13⁻ ∷ []) ∷
   rw⁻ 5 (q108 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 7 (q109 c4) ∷
   rw⁻ 9 (q110 c4) ∷
   rw 6 (q111 c4) ∷
   rw 8 (q112 c4) ∷
   rw 9 (q113 c4) ∷
   rw⁻ 12 (q86 c4) ∷
   rw 11 (q92 c4) ∷
   rw 12 (q91 c4) ∷
   rw 13 (q112 c4) ∷
   rw 14 (q90 c4) ∷
   rw 15 (q112 c4) ∷
   rw 16 (q88 c4) ∷
   rw 17 (q87 c4) ∷
   rw 11 (q86 c4) ∷
   rw⁻ 5 (q114 c4) ∷
   rw 7 (q95 c4) ∷
   rw⁻ 6 (q99 c4) ∷
   rw⁻ 7 (q97 c4) ∷
   rw⁻ 8 (q98 c4) ∷
   rw⁻ 9 (q97 c4) ∷
   rw⁻ 10 (q96 c4) ∷
   rw⁻ 6 (q95 c4) ∷
   rw⁻ 7 (q109 c4) ∷
   rw⁻ 9 (q100 c4) ∷
   rw 11 (q95 c4) ∷
   rw⁻ 10 (q99 c4) ∷
   rw⁻ 11 (q97 c4) ∷
   rw⁻ 12 (q98 c4) ∷
   rw⁻ 13 (q97 c4) ∷
   rw⁻ 14 (q96 c4) ∷
   rw⁻ 10 (q95 c4) ∷
   rw⁻ 11 (q110 c4) ∷
   rw⁻ 5 (q115 c4) ∷
   rw⁻ 7 (q101 c4) ∷
   rw 5 (q116 c4) ∷
   rw 4 (q112 c4) ∷
   rw⁻ 6 (q86 c4) ∷
   rw 5 (q92 c4) ∷
   rw 6 (q91 c4) ∷
   rw 7 (q112 c4) ∷
   rw 8 (q90 c4) ∷
   rw 9 (q112 c4) ∷
   rw 10 (q88 c4) ∷
   rw 11 (q87 c4) ∷
   rw 5 (q86 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   re 8 1 (Sb4-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 6 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 3 (q117 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   re 5 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 7 1 (CS13 ∷ []) ∷
   re 9 1 (CS13⁻ ∷ []) ∷
   rw⁻ 6 (q121 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 8 (q85 c4) ∷
   rw 7 (q84 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   re 8 1 (Sb4-1-3-2 ∷ []) ∷
   re 10 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 6 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 4 (q120 c4) ∷
   re 2 1 (Sb4-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷ []) Eq.refl

private
  q122 : Ws → Eqn
  q122 c4 = wpE 1360 c4
  q123 : Ws → Eqn
  q123 c4 = wlE 1533 (lit c4)
  q124 : Ws → Eqn
  q124 c4 = wlE 1534 (lit c4)
  q125 : Ws → Eqn
  q125 c4 = wlE 1431 (lit c4)

-- F4-I-CS1 @0440: 15 steps
lem-F4-I-CS1-at0440 : Ws → ⟪ (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ []) ⟫ʷ
lem-F4-I-CS1-at0440 c4 = derive (X0 ∷ S0 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ S0 ∷ X0 ∷ [])
  (re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 0 (q122 c4) ∷
   rw⁻ 1 (q123 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw⁻ 1 (q124 c4) ∷
   re 2 1 (Sb4-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷
   rw 1 (q125 c4) ∷
   rw⁻ 1 (q125 c4) ∷ []) Eq.refl

private
  q126 : Ws → Eqn
  q126 c4 = wlE 1446 (lit c4)
  q127 : Ws → Eqn
  q127 c4 = wlE 1557 (lit c4)
  q128 : Ws → Eqn
  q128 c4 = wlE 1558 (lit c4)
  q129 : Ws → Eqn
  q129 c4 = wpE 1383 c4
  q130 : Ws → Eqn
  q130 c4 = wlE 1448 (lit c4)

-- F4-CS1-I @0440: 15 steps
lem-F4-CS1-I-at0440 : Ws → ⟪ (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ S0 ∷ []) ⟫ʷ ≈ ⟪ (S0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ []) ⟫ʷ
lem-F4-CS1-I-at0440 c4 = derive (X0 ∷ Sb4-1-02-3 ∷ X0 ∷ S0 ∷ []) (S0 ∷ X0 ∷ Sb4-1-02-3 ∷ X0 ∷ [])
  (rw 2 (q126 c4) ∷
   re 1 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 3 1 (CS13 ∷ []) ∷
   re 5 1 (CS13⁻ ∷ []) ∷
   rw 2 (q127 c4) ∷
   rw 1 (q67 c4) ∷
   rw 4 (q128 c4) ∷
   rw 3 (q129 c4) ∷
   rw 2 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   re 5 1 (Sb4-1-3-2 ∷ []) ∷
   re 7 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 3 5 (Sb4-1-02-3 ∷ []) ∷
   rw⁻ 0 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = sE 738 (lem-sym-bc-at04203243 c4)

-- box-perm-1324 @04203243: 1 steps
lem-box-perm-1324-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1203 ∷ []) ⟫ʷ
lem-box-perm-1324-at04203243 c4 = derive (Bx4-1023 ∷ []) (Bx4-1203 ∷ [])
  (rw 0 (q131 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = sE 802 (lem-SWbc-box-at041041 c4)
  q133 : Ws → Eqn
  q133 c4 = sE 758 (lem-nat-SWbc-at041041 c4)

-- sym-bc @041041: 2 steps
lem-sym-bc-at041041 : Ws → ⟪ (Bx4-0231 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-0321 ∷ []) ⟫ʷ
lem-sym-bc-at041041 c4 = derive (Bx4-0231 ∷ []) (Bx4-0321 ∷ [])
  (rw⁻ 0 (q132 c4) ∷
   rw 0 (q133 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = wpE 516 c4
  q135 : Ws → Eqn
  q135 c4 = sE 788 (lem-QVQ-at0410233241 c4)
  q136 : Ws → Eqn
  q136 c4 = sE 293 (lem-tP-at0410233241 c4)
  q137 : Ws → Eqn
  q137 c4 = wpE 317 c4

-- box-cP @0410233241: 12 steps
lem-box-cP-at0410233241 : Ws → ⟪ (Bx4-0321 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0410233241 c4 = derive (Bx4-0321 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-421 ∷ Toff403 ∷ CCZ034 ∷ Bx0-421 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw 2 (q134 c4) ∷
   re 5 1 (CCZ024 ∷ Toff024 ∷ Bx4-01 ∷ Toff024 ∷ CCZ024 ∷ Bx4-01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw 5 (q134 c4) ∷
   rw 2 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = wpE 598 c4
  q139 : Ws → Eqn
  q139 c4 = sE 791 (lem-QVQ-at0412213043 c4)
  q140 : Ws → Eqn
  q140 c4 = sE 294 (lem-tP-at0412213043 c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 470 (lit c4)

-- box-cP @0412213043: 12 steps
lem-box-cP-at0412213043 : Ws → ⟪ (Bx4-2103 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at0412213043 c4 = derive (Bx4-2103 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-403 ∷ Toff412 ∷ CCZ124 ∷ Bx2-403 ∷ []) ∷
   re 2 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw 2 (q138 c4) ∷
   re 5 1 (CCZ024 ∷ Toff204 ∷ Bx4-23 ∷ Toff204 ∷ CCZ024 ∷ Bx4-23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw 5 (q138 c4) ∷
   rw 2 (q139 c4) ∷
   rw 1 (q140 c4) ∷
   rw 2 (q141 c4) ∷ []) Eq.refl

private
  q142 : Ws → Eqn
  q142 c4 = wpE 1395 c4
  q143 : Ws → Eqn
  q143 c4 = wlE 1585 (lit c4)

-- F4-K1-CS1 @0440: 17 steps
lem-F4-K1-CS1-at0440 : Ws → ⟪ (X0 ∷ CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ X0 ∷ []) ⟫ʷ
lem-F4-K1-CS1-at0440 c4 = derive (X0 ∷ CK01 ∷ X0 ∷ Sb4-1-02-3 ∷ []) (Sb4-1-02-3 ∷ X0 ∷ CK01 ∷ X0 ∷ [])
  (re 3 1 (Bx4-1023 ∷ Toff302 ∷ Sb4-1-3-2 ∷ Toff302 ∷ Sb⁻4-1-3-2 ∷ []) ∷
   re 5 1 (CS13 ∷ []) ∷
   re 7 1 (CS13⁻ ∷ []) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 0 (q142 c4) ∷
   rw 3 (q75 c4) ∷
   rw 2 (q69 c4) ∷
   rw 1 (q75 c4) ∷
   rw⁻ 2 (q142 c4) ∷
   rw 5 (q75 c4) ∷
   rw 4 (q69 c4) ∷
   rw 3 (q75 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw⁻ 1 (q143 c4) ∷
   re 2 1 (Sb4-1-3-2 ∷ []) ∷
   re 4 1 (Sb⁻4-1-3-2 ∷ []) ∷
   re 0 5 (Sb4-1-02-3 ∷ []) ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = sE 811 (lem-SWbc-box-at04233240 c4)
  q145 : Ws → Eqn
  q145 c4 = sE 761 (lem-nat-SWbc-at04233240 c4)

-- sym-bc @04233240: 2 steps
lem-sym-bc-at04233240 : Ws → ⟪ (Bx4-1320 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1230 ∷ []) ⟫ʷ
lem-sym-bc-at04233240 c4 = derive (Bx4-1320 ∷ []) (Bx4-1230 ∷ [])
  (rw⁻ 0 (q144 c4) ∷
   rw 0 (q145 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = wpE 733 c4
  q147 : Ws → Eqn
  q147 c4 = sE 799 (lem-QVQ-at0440 c4)
  q148 : Ws → Eqn
  q148 c4 = sE 296 (lem-tP-at0440 c4)

-- box-cP @0440: 12 steps
lem-box-cP-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at0440 c4 = derive (Bx4-1230 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx1-430 ∷ Toff412 ∷ CCZ124 ∷ Bx1-430 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   re 4 1 (CZ01 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   rw⁻ 2 (q146 c4) ∷
   re 5 1 (CCZ134 ∷ Toff134 ∷ Bx4-10 ∷ Toff134 ∷ CCZ134 ∷ Bx4-10 ∷ []) ∷
   re 7 1 (CZ01 ∷ []) ∷
   re 10 1 (CZ01 ∷ []) ∷
   rw⁻ 5 (q146 c4) ∷
   rw 2 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 2 (q141 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = sE 807 (lem-SWbc-box-at0413203142 c4)
  q150 : Ws → Eqn
  q150 c4 = sE 759 (lem-nat-SWbc-at0413203142 c4)

-- sym-bc @0413203142: 2 steps
lem-sym-bc-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3102 ∷ []) ⟫ʷ
lem-sym-bc-at0413203142 c4 = derive (Bx4-3012 ∷ []) (Bx4-3102 ∷ [])
  (rw⁻ 0 (q149 c4) ∷
   rw 0 (q150 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = wpE 992 c4
  q152 : Ws → Eqn
  q152 c4 = sE 784 (lem-QVQ-at02142140 c4)
  q153 : Ws → Eqn
  q153 c4 = sE 292 (lem-tP-at02142140 c4)
  q154 : Ws → Eqn
  q154 c4 = wlE 636 (lit c4)

-- box-cP @02142140: 12 steps
lem-box-cP-at02142140 : Ws → ⟪ (Bx2-4130 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ []) ⟫ʷ
lem-box-cP-at02142140 c4 = derive (Bx2-4130 ∷ []) (CCZ124 ∷ Toff203 ∷ CCZ124 ∷ Toff203 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff214 ∷ Bx4-230 ∷ Toff214 ∷ CCZ124 ∷ Bx4-230 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) ∷
   re 4 1 (CZ04 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   rw⁻ 2 (q151 c4) ∷
   re 5 1 (CCZ234 ∷ Toff423 ∷ Bx2-40 ∷ Toff423 ∷ CCZ234 ∷ Bx2-40 ∷ []) ∷
   re 7 1 (CZ04 ∷ []) ∷
   re 10 1 (CZ04 ∷ []) ∷
   rw⁻ 5 (q151 c4) ∷
   rw 2 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = sE 808 (lem-SWbc-box-at0413213042 c4)
  q156 : Ws → Eqn
  q156 c4 = sE 760 (lem-nat-SWbc-at0413213042 c4)

-- sym-bc @0413213042: 2 steps
lem-sym-bc-at0413213042 : Ws → ⟪ (Bx4-3102 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3012 ∷ []) ⟫ʷ
lem-sym-bc-at0413213042 c4 = derive (Bx4-3102 ∷ []) (Bx4-3012 ∷ [])
  (rw⁻ 0 (q155 c4) ∷
   rw 0 (q156 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = wlE 1596 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = sE 795 (lem-QVQ-at0413203142 c4)
  q159 : Ws → Eqn
  q159 c4 = sE 295 (lem-tP-at0413203142 c4)

-- box-cP @0413203142: 12 steps
lem-box-cP-at0413203142 : Ws → ⟪ (Bx4-3012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0413203142 c4 = derive (Bx4-3012 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-412 ∷ Toff403 ∷ CCZ034 ∷ Bx3-412 ∷ []) ∷
   re 2 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   re 4 1 (CZ23 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   rw⁻ 2 (q157 c4) ∷
   re 5 1 (CCZ134 ∷ Toff314 ∷ Bx4-32 ∷ Toff314 ∷ CCZ134 ∷ Bx4-32 ∷ []) ∷
   re 7 1 (CZ23 ∷ []) ∷
   re 10 1 (CZ23 ∷ []) ∷
   rw⁻ 5 (q157 c4) ∷
   rw 2 (q158 c4) ∷
   rw 1 (q159 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = sE 812 (lem-SWbc-box-at0440 c4)
  q161 : Ws → Eqn
  q161 c4 = sE 762 (lem-nat-SWbc-at0440 c4)

-- sym-bc @0440: 2 steps
lem-sym-bc-at0440 : Ws → ⟪ (Bx4-1230 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1320 ∷ []) ⟫ʷ
lem-sym-bc-at0440 c4 = derive (Bx4-1230 ∷ []) (Bx4-1320 ∷ [])
  (rw⁻ 0 (q160 c4) ∷
   rw 0 (q161 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = wpE 766 c4
  q163 : Ws → Eqn
  q163 c4 = sE 797 (lem-QVQ-at0413213240 c4)
  q164 : Ws → Eqn
  q164 c4 = sE 309 (lem-tP-at0413213240 c4)

-- box-cP @0413213240: 12 steps
lem-box-cP-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ []) ⟫ʷ
lem-box-cP-at0413213240 c4 = derive (Bx4-3120 ∷ []) (CCZ134 ∷ Toff402 ∷ CCZ134 ∷ Toff402 ∷ [])
  (re 0 1 (CCZ134 ∷ Toff413 ∷ Bx3-420 ∷ Toff413 ∷ CCZ134 ∷ Bx3-420 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) ∷
   re 4 1 (CZ03 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   rw⁻ 2 (q162 c4) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-30 ∷ Toff324 ∷ CCZ234 ∷ Bx4-30 ∷ []) ∷
   re 7 1 (CZ03 ∷ []) ∷
   re 10 1 (CZ03 ∷ []) ∷
   rw⁻ 5 (q162 c4) ∷
   rw 2 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = sE 736 (lem-sym-bc-at0310213442 c4)
  q166 : Ws → Eqn
  q166 c4 = sE 754 (lem-sym-ab-at0310243142 c4)

-- box-perm-3124 @0310213442: 2 steps
lem-box-perm-3124-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-4012 ∷ []) ⟫ʷ
lem-box-perm-3124-at0310213442 c4 = derive (Bx3-0142 ∷ []) (Bx3-4012 ∷ [])
  (rw 0 (q165 c4) ∷
   rw 0 (q166 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = sE 191 (lem-box-tQ-at0314203142 c4)
  q168 : Ws → Eqn
  q168 c4 = sE 750 (lem-box-cP-at0213243041 c4)
  q169 : Ws → Eqn
  q169 c4 = wlE 508 (lit c4)
  q170 : Ws → Eqn
  q170 c4 = wlE 1635 (lit c4)
  q171 : Ws → Eqn
  q171 c4 = wlE 1353 (lit c4)
  q172 : Ws → Eqn
  q172 c4 = wlE 433 (lit c4)
  q173 : Ws → Eqn
  q173 c4 = wpE 776 c4
  q174 : Ws → Eqn
  q174 c4 = eqn (CS01⁻ ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (CCZ))
  q175 : Ws → Eqn
  q175 c4 = eqn (CS01 ∷ CCZ234 ∷ []) (CCZ234 ∷ CS01 ∷ []) (c₂ (CS) (CCZ))
  q176 : Ws → Eqn
  q176 c4 = wlE 1636 (lit c4)
  q177 : Ws → Eqn
  q177 c4 = wpE 1071 c4
  q178 : Ws → Eqn
  q178 c4 = wpE 1288 c4
  q179 : Ws → Eqn
  q179 c4 = wpE 1185 c4
  q180 : Ws → Eqn
  q180 c4 = eqn (Toff201 ∷ K3⁻ ∷ []) (K3⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (K • iI))
  q181 : Ws → Eqn
  q181 c4 = wlE 1329 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (Toff201 ∷ CX34 ∷ []) (CX34 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CX₀₁))
  q183 : Ws → Eqn
  q183 c4 = wpE 1186 c4
  q184 : Ws → Eqn
  q184 c4 = wpE 1187 c4
  q185 : Ws → Eqn
  q185 c4 = eqn (Toff201 ∷ K3 ∷ []) (K3 ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (K))
  q186 : Ws → Eqn
  q186 c4 = wpE 90 c4
  q187 : Ws → Eqn
  q187 c4 = wpE 1143 c4
  q188 : Ws → Eqn
  q188 c4 = wlE 452 (lit c4)
  q189 : Ws → Eqn
  q189 c4 = wpE 1171 c4
  q190 : Ws → Eqn
  q190 c4 = wpE 685 c4
  q191 : Ws → Eqn
  q191 c4 = wpE 1189 c4
  q192 : Ws → Eqn
  q192 c4 = wlE 765 (lit c4)
  q193 : Ws → Eqn
  q193 c4 = eqn (CX40 ∷ CCZ123 ∷ []) (CCZ123 ∷ CX40 ∷ []) (lem-comm-CX40-CCZ123 (lit c4))
  q194 : Ws → Eqn
  q194 c4 = wlE 1321 (lit c4)
  q195 : Ws → Eqn
  q195 c4 = wlE 763 (lit c4)
  q196 : Ws → Eqn
  q196 c4 = wpE 687 c4
  q197 : Ws → Eqn
  q197 c4 = wpE 161 c4

-- box-box-4 @0314203142: 103 steps
lem-box-box-4-at0314203142 : Ws → ⟪ (Bx3-4012 ∷ Bx2-3401 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3401 ∷ Bx3-4012 ∷ []) ⟫ʷ
lem-box-box-4-at0314203142 c4 = derive (Bx3-4012 ∷ Bx2-3401 ∷ []) (Bx2-3401 ∷ Bx3-4012 ∷ [])
  (rw 0 (q167 c4) ∷
   rw 4 (q168 c4) ∷
   rw 3 (q169 c4) ∷
   rw 4 (q170 c4) ∷
   rw 6 (q169 c4) ∷
   rw 5 (q171 c4) ∷
   rw⁻ 9 (q172 c4) ∷
   rw⁻ 8 (q173 c4) ∷
   rw 7 (q174 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q175 c4) ∷
   rw⁻ 6 (q171 c4) ∷
   rw 6 (q176 c4) ∷
   rw⁻ 3 (q168 c4) ∷
   rw 3 (q168 c4) ∷
   rw⁻ 2 (q177 c4) ∷
   rw 4 (q178 c4) ∷
   rw⁻ 3 (q179 c4) ∷
   rw⁻ 9 (q180 c4) ∷
   rw 8 (q181 c4) ∷
   rw⁻ 7 (q182 c4) ∷
   rw 6 (q183 c4) ∷
   rw⁻ 5 (q182 c4) ∷
   rw 4 (q184 c4) ∷
   rw⁻ 3 (q185 c4) ∷
   rw 4 (q179 c4) ∷
   rw 6 (q186 c4) ∷
   rw 5 (q187 c4) ∷
   rw⁻ 9 (q188 c4) ∷
   rw⁻ 8 (q189 c4) ∷
   rw 7 (q174 c4) ∷
   rw⁻ 6 (q189 c4) ∷
   rw 5 (q175 c4) ∷
   rw⁻ 6 (q187 c4) ∷
   rw⁻ 4 (q177 c4) ∷
   rw⁻ 6 (q190 c4) ∷
   rw 6 (q191 c4) ∷
   rw⁻ 5 (q179 c4) ∷
   rw⁻ 11 (q180 c4) ∷
   rw 10 (q181 c4) ∷
   rw⁻ 9 (q182 c4) ∷
   rw 8 (q183 c4) ∷
   rw⁻ 7 (q182 c4) ∷
   rw 6 (q184 c4) ∷
   rw⁻ 5 (q185 c4) ∷
   rw 6 (q179 c4) ∷
   rw⁻ 2 (q168 c4) ∷
   rw 2 (q168 c4) ∷
   rw 1 (q169 c4) ∷
   rw 2 (q170 c4) ∷
   rw 4 (q169 c4) ∷
   rw 3 (q171 c4) ∷
   rw⁻ 7 (q172 c4) ∷
   rw⁻ 6 (q173 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q173 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q171 c4) ∷
   rw 4 (q176 c4) ∷
   rw⁻ 1 (q168 c4) ∷
   rw 1 (q168 c4) ∷
   rw⁻ 0 (q177 c4) ∷
   rw 2 (q178 c4) ∷
   rw⁻ 1 (q179 c4) ∷
   rw⁻ 7 (q180 c4) ∷
   rw 6 (q181 c4) ∷
   rw⁻ 5 (q182 c4) ∷
   rw 4 (q183 c4) ∷
   rw⁻ 3 (q182 c4) ∷
   rw 2 (q184 c4) ∷
   rw⁻ 1 (q185 c4) ∷
   rw 2 (q179 c4) ∷
   rw 4 (q186 c4) ∷
   rw 3 (q187 c4) ∷
   rw⁻ 7 (q188 c4) ∷
   rw⁻ 6 (q189 c4) ∷
   rw 5 (q174 c4) ∷
   rw⁻ 4 (q189 c4) ∷
   rw 3 (q175 c4) ∷
   rw⁻ 4 (q187 c4) ∷
   rw⁻ 2 (q177 c4) ∷
   rw⁻ 4 (q190 c4) ∷
   rw 4 (q191 c4) ∷
   rw⁻ 3 (q179 c4) ∷
   rw⁻ 9 (q180 c4) ∷
   rw 8 (q181 c4) ∷
   rw⁻ 7 (q182 c4) ∷
   rw 6 (q183 c4) ∷
   rw⁻ 5 (q182 c4) ∷
   rw 4 (q184 c4) ∷
   rw⁻ 3 (q185 c4) ∷
   rw 4 (q179 c4) ∷
   rw⁻ 0 (q168 c4) ∷
   rw 2 (q187 c4) ∷
   rw⁻ 6 (q192 c4) ∷
   rw 5 (q193 c4) ∷
   rw⁻ 4 (q194 c4) ∷
   rw 3 (q193 c4) ∷
   rw⁻ 2 (q195 c4) ∷
   rw⁻ 3 (q187 c4) ∷
   rw 3 (q196 c4) ∷
   rw 4 (q197 c4) ∷
   rw⁻ 1 (q167 c4) ∷ []) Eq.refl

private
  q198 : Ws → Eqn
  q198 c4 = sE 752 (lem-box-cP-at0310213442 c4)
  q199 : Ws → Eqn
  q199 c4 = wpE 184 c4
  q200 : Ws → Eqn
  q200 c4 = wlE 1643 (lit c4)
  q201 : Ws → Eqn
  q201 c4 = wlE 293 (lit c4)
  q202 : Ws → Eqn
  q202 c4 = wlE 324 (lit c4)
  q203 : Ws → Eqn
  q203 c4 = wpE 523 c4
  q204 : Ws → Eqn
  q204 c4 = eqn (CS24⁻ ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4))
  q205 : Ws → Eqn
  q205 c4 = eqn (CS24 ∷ CCZ013 ∷ []) (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4))
  q206 : Ws → Eqn
  q206 c4 = wlE 1204 (lit c4)
  q207 : Ws → Eqn
  q207 c4 = wlE 1644 (lit c4)
  q208 : Ws → Eqn
  q208 c4 = wlE 1645 (lit c4)

-- CSdu-box-3 @0310213442: 17 steps
lem-CSdu-box-3-at0310213442 : Ws → ⟪ (CS34⁻ ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CS34⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0310213442 c4 = derive (CS34⁻ ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CS34⁻ ∷ [])
  (rw 1 (q198 c4) ∷
   rw⁻ 0 (q199 c4) ∷
   rw 1 (q200 c4) ∷
   rw 4 (q201 c4) ∷
   rw⁻ 8 (q202 c4) ∷
   rw⁻ 7 (q203 c4) ∷
   rw 6 (q204 c4) ∷
   rw⁻ 5 (q203 c4) ∷
   rw 4 (q205 c4) ∷
   rw⁻ 5 (q201 c4) ∷
   rw 3 (q204 c4) ∷
   rw⁻ 2 (q199 c4) ∷
   rw 5 (q206 c4) ∷
   rw 4 (q207 c4) ∷
   rw 3 (q200 c4) ∷
   rw 4 (q208 c4) ∷
   rw⁻ 0 (q198 c4) ∷ []) Eq.refl

private
  q209 : Ws → Eqn
  q209 c4 = wpE 185 c4
  q210 : Ws → Eqn
  q210 c4 = wlE 1652 (lit c4)
  q211 : Ws → Eqn
  q211 c4 = wlE 1653 (lit c4)
  q212 : Ws → Eqn
  q212 c4 = wlE 1654 (lit c4)

-- CSu-box-3 @0310213442: 17 steps
lem-CSu-box-3-at0310213442 : Ws → ⟪ (CS34 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0142 ∷ CS34 ∷ []) ⟫ʷ
lem-CSu-box-3-at0310213442 c4 = derive (CS34 ∷ Bx3-0142 ∷ []) (Bx3-0142 ∷ CS34 ∷ [])
  (rw 1 (q198 c4) ∷
   rw⁻ 0 (q209 c4) ∷
   rw 1 (q210 c4) ∷
   rw 4 (q201 c4) ∷
   rw⁻ 8 (q202 c4) ∷
   rw⁻ 7 (q203 c4) ∷
   rw 6 (q204 c4) ∷
   rw⁻ 5 (q203 c4) ∷
   rw 4 (q205 c4) ∷
   rw⁻ 5 (q201 c4) ∷
   rw 3 (q205 c4) ∷
   rw⁻ 2 (q209 c4) ∷
   rw 5 (q206 c4) ∷
   rw 4 (q211 c4) ∷
   rw 3 (q210 c4) ∷
   rw 4 (q212 c4) ∷
   rw⁻ 0 (q198 c4) ∷ []) Eq.refl

private
  q213 : Ws → Eqn
  q213 c4 = sE 89 (lem-box-tQ-at0310213442 c4)
  q214 : Ws → Eqn
  q214 c4 = sE 777 (lem-t-cP-at0310213442 c4)

-- box2 @0310213442: 11 steps
lem-box2-at0310213442 : Ws → ⟪ (Bx3-0142 ∷ Bx3-0142 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0310213442 c4 = derive (Bx3-0142 ∷ Bx3-0142 ∷ []) []
  (rw 0 (q213 c4) ∷
   rw 4 (q198 c4) ∷
   rw⁻ 4 (q3 c4) ∷
   rw 5 (q214 c4) ∷
   rw⁻ 5 (q198 c4) ∷
   rw 5 (q213 c4) ∷
   rw 4 (q3 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q3 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q3 c4) ∷ []) Eq.refl

private
  q215 : Ws → Eqn
  q215 c4 = sE 816 (lem-sym-bc-at0210213443 c4)
  q216 : Ws → Eqn
  q216 c4 = sE 14 (lem-sym-ab-at0210243143 c4)

-- box-perm-3124 @0210213443: 2 steps
lem-box-perm-3124-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-4013 ∷ []) ⟫ʷ
lem-box-perm-3124-at0210213443 c4 = derive (Bx2-0143 ∷ []) (Bx2-4013 ∷ [])
  (rw 0 (q215 c4) ∷
   rw 0 (q216 c4) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = sE 776 (lem-P-box-at04203243 c4)
  q218 : Ws → Eqn
  q218 c4 = sE 301 (lem-box-tQ-at0412233140 c4)

-- pairs @04203243: 4 steps
lem-pairs-at04203243 : Ws → ⟪ (Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-pairs-at04203243 c4 = derive (Bx4-1023 ∷ []) (Bx4-2310 ∷ [])
  (rw⁻ 0 (q217 c4) ∷
   rw 1 (q67 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 0 (q218 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = sE 806 (lem-SWbc-box-at0412233140 c4)
  q220 : Ws → Eqn
  q220 c4 = sE 769 (lem-nat-SWbc-at0412233140 c4)

-- sym-bc @0412233140: 2 steps
lem-sym-bc-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2130 ∷ []) ⟫ʷ
lem-sym-bc-at0412233140 c4 = derive (Bx4-2310 ∷ []) (Bx4-2130 ∷ [])
  (rw⁻ 0 (q219 c4) ∷
   rw 0 (q220 c4) ∷ []) Eq.refl

private
  q221 : Ws → Eqn
  q221 c4 = wpE 1437 c4
  q222 : Ws → Eqn
  q222 c4 = sE 787 (lem-QVQ-at0410233142 c4)
  q223 : Ws → Eqn
  q223 c4 = sE 305 (lem-tP-at0410233142 c4)

-- box-cP @0410233142: 12 steps
lem-box-cP-at0410233142 : Ws → ⟪ (Bx4-0312 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0410233142 c4 = derive (Bx4-0312 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx0-412 ∷ Toff403 ∷ CCZ034 ∷ Bx0-412 ∷ []) ∷
   re 2 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw 2 (q221 c4) ∷
   re 5 1 (CCZ014 ∷ Toff014 ∷ Bx4-02 ∷ Toff014 ∷ CCZ014 ∷ Bx4-02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw 5 (q221 c4) ∷
   rw 2 (q222 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = sE 804 (lem-SWbc-box-at04122140 c4)
  q225 : Ws → Eqn
  q225 c4 = sE 767 (lem-nat-SWbc-at04122140 c4)

-- sym-bc @04122140: 2 steps
lem-sym-bc-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-2310 ∷ []) ⟫ʷ
lem-sym-bc-at04122140 c4 = derive (Bx4-2130 ∷ []) (Bx4-2310 ∷ [])
  (rw⁻ 0 (q224 c4) ∷
   rw 0 (q225 c4) ∷ []) Eq.refl

private
  q226 : Ws → Eqn
  q226 c4 = wpE 1436 c4
  q227 : Ws → Eqn
  q227 c4 = sE 794 (lem-QVQ-at0412233140 c4)
  q228 : Ws → Eqn
  q228 c4 = sE 307 (lem-tP-at0412233140 c4)

-- box-cP @0412233140: 12 steps
lem-box-cP-at0412233140 : Ws → ⟪ (Bx4-2310 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ []) ⟫ʷ
lem-box-cP-at0412233140 c4 = derive (Bx4-2310 ∷ []) (CCZ234 ∷ Toff401 ∷ CCZ234 ∷ Toff401 ∷ [])
  (re 0 1 (CCZ234 ∷ Toff423 ∷ Bx2-410 ∷ Toff423 ∷ CCZ234 ∷ Bx2-410 ∷ []) ∷
   re 2 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q226 c4) ∷
   re 5 1 (CCZ124 ∷ Toff214 ∷ Bx4-20 ∷ Toff214 ∷ CCZ124 ∷ Bx4-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q226 c4) ∷
   rw 2 (q227 c4) ∷
   rw 1 (q228 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q229 : Ws → Eqn
  q229 c4 = wpE 62 c4
  q230 : Ws → Eqn
  q230 c4 = wlE 1682 (lit c4)
  q231 : Ws → Eqn
  q231 c4 = wlE 675 (lit c4)
  q232 : Ws → Eqn
  q232 c4 = wpE 64 c4
  q233 : Ws → Eqn
  q233 c4 = wpE 269 c4
  q234 : Ws → Eqn
  q234 c4 = wlE 1683 (lit c4)
  q235 : Ws → Eqn
  q235 c4 = wlE 1684 (lit c4)
  q236 : Ws → Eqn
  q236 c4 = wlE 1685 (lit c4)

-- CSu-box-3 @04203243: 17 steps
lem-CSu-box-3-at04203243 : Ws → ⟪ (CS24 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS24 ∷ []) ⟫ʷ
lem-CSu-box-3-at04203243 c4 = derive (CS24 ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ CS24 ∷ [])
  (rw 1 (q67 c4) ∷
   rw⁻ 0 (q229 c4) ∷
   rw 1 (q230 c4) ∷
   rw 4 (q231 c4) ∷
   rw⁻ 8 (q232 c4) ∷
   rw⁻ 7 (q233 c4) ∷
   rw 6 (q79 c4) ∷
   rw⁻ 5 (q233 c4) ∷
   rw 4 (q80 c4) ∷
   rw⁻ 5 (q231 c4) ∷
   rw 3 (q80 c4) ∷
   rw⁻ 2 (q229 c4) ∷
   rw 5 (q234 c4) ∷
   rw 4 (q235 c4) ∷
   rw 3 (q230 c4) ∷
   rw 4 (q236 c4) ∷
   rw⁻ 0 (q67 c4) ∷ []) Eq.refl

private
  q237 : Ws → Eqn
  q237 c4 = wpE 722 c4
  q238 : Ws → Eqn
  q238 c4 = wlE 1686 (lit c4)
  q239 : Ws → Eqn
  q239 c4 = wlE 1687 (lit c4)
  q240 : Ws → Eqn
  q240 c4 = wlE 1688 (lit c4)

-- CSdu-box-3 @04203243: 17 steps
lem-CSdu-box-3-at04203243 : Ws → ⟪ (CS24⁻ ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-1023 ∷ CS24⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at04203243 c4 = derive (CS24⁻ ∷ Bx4-1023 ∷ []) (Bx4-1023 ∷ CS24⁻ ∷ [])
  (rw 1 (q67 c4) ∷
   rw⁻ 0 (q237 c4) ∷
   rw 1 (q238 c4) ∷
   rw 4 (q231 c4) ∷
   rw⁻ 8 (q232 c4) ∷
   rw⁻ 7 (q233 c4) ∷
   rw 6 (q79 c4) ∷
   rw⁻ 5 (q233 c4) ∷
   rw 4 (q80 c4) ∷
   rw⁻ 5 (q231 c4) ∷
   rw 3 (q79 c4) ∷
   rw⁻ 2 (q237 c4) ∷
   rw 5 (q234 c4) ∷
   rw 4 (q239 c4) ∷
   rw 3 (q238 c4) ∷
   rw 4 (q240 c4) ∷
   rw⁻ 0 (q67 c4) ∷ []) Eq.refl

private
  q241 : Ws → Eqn
  q241 c4 = sE 26 (lem-box-tQ-at04203243 c4)
  q242 : Ws → Eqn
  q242 c4 = wpE 306 c4
  q243 : Ws → Eqn
  q243 c4 = sE 778 (lem-t-cP-at04203243 c4)

-- box2 @04203243: 11 steps
lem-box2-at04203243 : Ws → ⟪ (Bx4-1023 ∷ Bx4-1023 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at04203243 c4 = derive (Bx4-1023 ∷ Bx4-1023 ∷ []) []
  (rw 0 (q241 c4) ∷
   rw 4 (q67 c4) ∷
   rw⁻ 4 (q242 c4) ∷
   rw 5 (q243 c4) ∷
   rw⁻ 5 (q67 c4) ∷
   rw 5 (q241 c4) ∷
   rw 4 (q242 c4) ∷
   rw 3 (q5 c4) ∷
   rw 2 (q242 c4) ∷
   rw 1 (q5 c4) ∷
   rw 0 (q242 c4) ∷ []) Eq.refl

private
  q244 : Ws → Eqn
  q244 c4 = sE 814 (lem-XCSX-box-2-at04122041 c4)
  q245 : Ws → Eqn
  q245 c4 = wpE 1476 c4
  q246 : Ws → Eqn
  q246 c4 = wpE 1477 c4
  q247 : Ws → Eqn
  q247 c4 = wpE 1478 c4
  q248 : Ws → Eqn
  q248 c4 = wpE 1281 c4

-- F4-S0-CS2 @0440: 13 steps
lem-F4-S0-CS2-at0440 : Ws → ⟪ (X0 ∷ CS04 ∷ X0 ∷ Sb4-2-03-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb4-2-03-1 ∷ X0 ∷ CS04 ∷ X0 ∷ []) ⟫ʷ
lem-F4-S0-CS2-at0440 c4 = derive (X0 ∷ CS04 ∷ X0 ∷ Sb4-2-03-1 ∷ []) (Sb4-2-03-1 ∷ X0 ∷ CS04 ∷ X0 ∷ [])
  (re 3 1 (Bx4-2031 ∷ Toff103 ∷ Sb4-2-1-3 ∷ Toff103 ∷ Sb⁻4-2-1-3 ∷ []) ∷
   re 5 1 (CS12 ∷ []) ∷
   re 7 1 (CS12⁻ ∷ []) ∷
   rw 0 (q244 c4) ∷
   rw⁻ 1 (q245 c4) ∷
   rw⁻ 2 (q246 c4) ∷
   rw⁻ 3 (q245 c4) ∷
   rw⁻ 4 (q247 c4) ∷
   re 2 1 (Sb4-2-1-3 ∷ []) ∷
   re 4 1 (Sb⁻4-2-1-3 ∷ []) ∷
   re 0 5 (Sb4-2-03-1 ∷ []) ∷
   rw⁻ 1 (q248 c4) ∷
   rw 1 (q248 c4) ∷ []) Eq.refl

private
  q249 : Ws → Eqn
  q249 c4 = wlE 756 (lit c4)
  q250 : Ws → Eqn
  q250 c4 = sE 796 (lem-QVQ-at0413203241 c4)
  q251 : Ws → Eqn
  q251 c4 = sE 308 (lem-tP-at0413203241 c4)

-- box-cP @0413203241: 12 steps
lem-box-cP-at0413203241 : Ws → ⟪ (Bx4-3021 ∷ []) ⟫ʷ ≈ ⟪ (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ []) ⟫ʷ
lem-box-cP-at0413203241 c4 = derive (Bx4-3021 ∷ []) (CCZ034 ∷ Toff412 ∷ CCZ034 ∷ Toff412 ∷ [])
  (re 0 1 (CCZ034 ∷ Toff403 ∷ Bx3-421 ∷ Toff403 ∷ CCZ034 ∷ Bx3-421 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) ∷
   re 4 1 (CZ13 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   rw⁻ 2 (q249 c4) ∷
   re 5 1 (CCZ234 ∷ Toff324 ∷ Bx4-31 ∷ Toff324 ∷ CCZ234 ∷ Bx4-31 ∷ []) ∷
   re 7 1 (CZ13 ∷ []) ∷
   re 10 1 (CZ13 ∷ []) ∷
   rw⁻ 5 (q249 c4) ∷
   rw 2 (q250 c4) ∷
   rw 1 (q251 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q252 : Ws → Eqn
  q252 c4 = wpE 732 c4
  q253 : Ws → Eqn
  q253 c4 = sE 792 (lem-QVQ-at04122140 c4)
  q254 : Ws → Eqn
  q254 c4 = sE 306 (lem-tP-at04122140 c4)

-- box-cP @04122140: 12 steps
lem-box-cP-at04122140 : Ws → ⟪ (Bx4-2130 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ []) ⟫ʷ
lem-box-cP-at04122140 c4 = derive (Bx4-2130 ∷ []) (CCZ124 ∷ Toff403 ∷ CCZ124 ∷ Toff403 ∷ [])
  (re 0 1 (CCZ124 ∷ Toff412 ∷ Bx2-430 ∷ Toff412 ∷ CCZ124 ∷ Bx2-430 ∷ []) ∷
   re 2 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   re 4 1 (CZ02 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   rw⁻ 2 (q252 c4) ∷
   re 5 1 (CCZ234 ∷ Toff234 ∷ Bx4-20 ∷ Toff234 ∷ CCZ234 ∷ Bx4-20 ∷ []) ∷
   re 7 1 (CZ02 ∷ []) ∷
   re 10 1 (CZ02 ∷ []) ∷
   rw⁻ 5 (q252 c4) ∷
   rw 2 (q253 c4) ∷
   rw 1 (q254 c4) ∷
   rw 2 (q141 c4) ∷ []) Eq.refl

private
  q255 : Ws → Eqn
  q255 c4 = sE 810 (lem-SWbc-box-at04133140 c4)
  q256 : Ws → Eqn
  q256 c4 = sE 771 (lem-nat-SWbc-at04133140 c4)

-- sym-bc @04133140: 2 steps
lem-sym-bc-at04133140 : Ws → ⟪ (Bx4-3210 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3120 ∷ []) ⟫ʷ
lem-sym-bc-at04133140 c4 = derive (Bx4-3210 ∷ []) (Bx4-3120 ∷ [])
  (rw⁻ 0 (q255 c4) ∷
   rw 0 (q256 c4) ∷ []) Eq.refl

private
  q257 : Ws → Eqn
  q257 c4 = sE 809 (lem-SWbc-box-at0413213240 c4)
  q258 : Ws → Eqn
  q258 c4 = sE 770 (lem-nat-SWbc-at0413213240 c4)

-- sym-bc @0413213240: 2 steps
lem-sym-bc-at0413213240 : Ws → ⟪ (Bx4-3120 ∷ []) ⟫ʷ ≈ ⟪ (Bx4-3210 ∷ []) ⟫ʷ
lem-sym-bc-at0413213240 c4 = derive (Bx4-3120 ∷ []) (Bx4-3210 ∷ [])
  (rw⁻ 0 (q257 c4) ∷
   rw 0 (q258 c4) ∷ []) Eq.refl
