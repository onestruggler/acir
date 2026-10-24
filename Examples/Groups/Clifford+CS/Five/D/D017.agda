{-# OPTIONS --without-K --safe #-}

open import Examples.Groups.Clifford+CS.Five.DEqn using (wpE ; wlE)
open import Examples.Groups.Clifford+CS.Five.DStmt using (St)
open import Examples.Groups.Clifford+CS.Five.DSig using (SD017 ; pickᴰ ; sE)

module Examples.Groups.Clifford+CS.Five.D.D017 (Sᴰ : SD017) where

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
  lem-comm-CS23-CCZ014 : Ws → St 703
  lem-comm-CS23-CCZ014 = pickᴰ 0 Sᴰ
  lem-comm-CS24-CCZ013 : Ws → St 194
  lem-comm-CS24-CCZ013 = pickᴰ 1 Sᴰ
  lem-comm-CSd23-CCZ014 : Ws → St 704
  lem-comm-CSd23-CCZ014 = pickᴰ 2 Sᴰ
  lem-comm-CSd24-CCZ013 : Ws → St 204
  lem-comm-CSd24-CCZ013 = pickᴰ 3 Sᴰ
  lem-comm-CX23-CCZ014 : Ws → St 6
  lem-comm-CX23-CCZ014 = pickᴰ 4 Sᴰ
  lem-comm-CCZ014-CX23 : Ws → St 893
  lem-comm-CCZ014-CX23 = pickᴰ 5 Sᴰ
  lem-comm-CX40-CCZ123 : Ws → St 20
  lem-comm-CX40-CCZ123 = pickᴰ 6 Sᴰ
  lem-sym-ab-at0210243143 : Ws → St 53
  lem-sym-ab-at0210243143 = pickᴰ 7 Sᴰ
  lem-sym-ab-at0310243142 : Ws → St 894
  lem-sym-ab-at0310243142 = pickᴰ 8 Sᴰ
  lem-sym-ab-at032032 : Ws → St 54
  lem-sym-ab-at032032 = pickᴰ 9 Sᴰ
  lem-sym-ab-at13243142 : Ws → St 895
  lem-sym-ab-at13243142 = pickᴰ 10 Sᴰ
  lem-sym-ab-at022330 : Ws → St 896
  lem-sym-ab-at022330 = pickᴰ 11 Sᴰ
  lem-sym-ab-at0330 : Ws → St 897
  lem-sym-ab-at0330 = pickᴰ 12 Sᴰ
  lem-nat-SWbc-at041041 : Ws → St 898
  lem-nat-SWbc-at041041 = pickᴰ 13 Sᴰ
  lem-nat-SWbc-at0413203142 : Ws → St 899
  lem-nat-SWbc-at0413203142 = pickᴰ 14 Sᴰ
  lem-nat-SWbc-at0413213042 : Ws → St 900
  lem-nat-SWbc-at0413213042 = pickᴰ 15 Sᴰ
  lem-nat-SWbc-at04233240 : Ws → St 901
  lem-nat-SWbc-at04233240 = pickᴰ 16 Sᴰ
  lem-nat-SWbc-at0440 : Ws → St 902
  lem-nat-SWbc-at0440 = pickᴰ 17 Sᴰ
  lem-sym-ab-at02102331 : Ws → St 903
  lem-sym-ab-at02102331 = pickᴰ 18 Sᴰ
  lem-sym-ab-at031031 : Ws → St 904
  lem-sym-ab-at031031 = pickᴰ 19 Sᴰ
  lem-box-tQ-at03102132 : Ws → St 138
  lem-box-tQ-at03102132 = pickᴰ 20 Sᴰ
  lem-box-tQ-at032032 : Ws → St 83
  lem-box-tQ-at032032 = pickᴰ 21 Sᴰ
  lem-box-tQ-at04203243 : Ws → St 84
  lem-box-tQ-at04203243 = pickᴰ 22 Sᴰ
  lem-box-tQ-at0310213442 : Ws → St 149
  lem-box-tQ-at0310213442 = pickᴰ 23 Sᴰ
  lem-nat-SWbc-at02102331 : Ws → St 905
  lem-nat-SWbc-at02102331 = pickᴰ 24 Sᴰ
  lem-nat-SWbc-at04122041 : Ws → St 906
  lem-nat-SWbc-at04122041 = pickᴰ 25 Sᴰ
  lem-nat-SWbc-at04122140 : Ws → St 907
  lem-nat-SWbc-at04122140 = pickᴰ 26 Sᴰ
  lem-nat-SWbc-at0412233041 : Ws → St 908
  lem-nat-SWbc-at0412233041 = pickᴰ 27 Sᴰ
  lem-nat-SWbc-at0412233140 : Ws → St 909
  lem-nat-SWbc-at0412233140 = pickᴰ 28 Sᴰ
  lem-nat-SWbc-at0413213240 : Ws → St 910
  lem-nat-SWbc-at0413213240 = pickᴰ 29 Sᴰ
  lem-nat-SWbc-at04133140 : Ws → St 911
  lem-nat-SWbc-at04133140 = pickᴰ 30 Sᴰ
  lem-nat-SWbc-at142142 : Ws → St 912
  lem-nat-SWbc-at142142 = pickᴰ 31 Sᴰ
  lem-box-tQ-at0314203142 : Ws → St 310
  lem-box-tQ-at0314203142 = pickᴰ 32 Sᴰ
  lem-t-cP-at03102132 : Ws → St 913
  lem-t-cP-at03102132 = pickᴰ 33 Sᴰ
  lem-t-cP-at032032 : Ws → St 914
  lem-t-cP-at032032 = pickᴰ 34 Sᴰ
  lem-tP-at02102331 : Ws → St 405
  lem-tP-at02102331 = pickᴰ 35 Sᴰ
  lem-tP-at02142041 : Ws → St 408
  lem-tP-at02142041 = pickᴰ 36 Sᴰ
  lem-tP-at0314203241 : Ws → St 411
  lem-tP-at0314203241 = pickᴰ 37 Sᴰ
  lem-tP-at03243042 : Ws → St 413
  lem-tP-at03243042 = pickᴰ 38 Sᴰ
  lem-tP-at04103143 : Ws → St 414
  lem-tP-at04103143 = pickᴰ 39 Sᴰ
  lem-tP-at04122041 : Ws → St 415
  lem-tP-at04122041 = pickᴰ 40 Sᴰ
  lem-tP-at0412233041 : Ws → St 416
  lem-tP-at0412233041 = pickᴰ 41 Sᴰ
  lem-tP-at04233042 : Ws → St 417
  lem-tP-at04233042 = pickᴰ 42 Sᴰ
  lem-tP-at142142 : Ws → St 418
  lem-tP-at142142 = pickᴰ 43 Sᴰ
  lem-P-box-at0410213243 : Ws → St 915
  lem-P-box-at0410213243 = pickᴰ 44 Sᴰ
  lem-P-box-at04203243 : Ws → St 916
  lem-P-box-at04203243 = pickᴰ 45 Sᴰ
  lem-box-tQ-at0412233041 : Ws → St 421
  lem-box-tQ-at0412233041 = pickᴰ 46 Sᴰ
  lem-box-tQ-at0412233140 : Ws → St 438
  lem-box-tQ-at0412233140 = pickᴰ 47 Sᴰ
  lem-t-cP-at0310213442 : Ws → St 917
  lem-t-cP-at0310213442 = pickᴰ 48 Sᴰ
  lem-t-cP-at04203243 : Ws → St 918
  lem-t-cP-at04203243 = pickᴰ 49 Sᴰ
  lem-tP-at02142140 : Ws → St 426
  lem-tP-at02142140 = pickᴰ 50 Sᴰ
  lem-tP-at0410233142 : Ws → St 442
  lem-tP-at0410233142 = pickᴰ 51 Sᴰ
  lem-tP-at0410233241 : Ws → St 427
  lem-tP-at0410233241 = pickᴰ 52 Sᴰ
  lem-tP-at0412213043 : Ws → St 428
  lem-tP-at0412213043 = pickᴰ 53 Sᴰ
  lem-tP-at04122140 : Ws → St 443
  lem-tP-at04122140 = pickᴰ 54 Sᴰ
  lem-tP-at0412233140 : Ws → St 444
  lem-tP-at0412233140 = pickᴰ 55 Sᴰ
  lem-tP-at0413203142 : Ws → St 429
  lem-tP-at0413203142 = pickᴰ 56 Sᴰ
  lem-tP-at0413203241 : Ws → St 445
  lem-tP-at0413203241 = pickᴰ 57 Sᴰ
  lem-tP-at0413213240 : Ws → St 446
  lem-tP-at0413213240 = pickᴰ 58 Sᴰ
  lem-tP-at0440 : Ws → St 430
  lem-tP-at0440 = pickᴰ 59 Sᴰ
  lem-box-cP-at03102132 : Ws → St 867
  lem-box-cP-at03102132 = pickᴰ 60 Sᴰ
  lem-box-cP-at032032 : Ws → St 868
  lem-box-cP-at032032 = pickᴰ 61 Sᴰ
  lem-box-cP-at0410213243 : Ws → St 869
  lem-box-cP-at0410213243 = pickᴰ 62 Sᴰ
  lem-box-cP-at04203243 : Ws → St 919
  lem-box-cP-at04203243 = pickᴰ 63 Sᴰ
  lem-sym-bc-at0220 : Ws → St 920
  lem-sym-bc-at0220 = pickᴰ 64 Sᴰ
  lem-sym-bc-at03102132 : Ws → St 874
  lem-sym-bc-at03102132 = pickᴰ 65 Sᴰ
  lem-sym-bc-at0310213442 : Ws → St 875
  lem-sym-bc-at0310213442 = pickᴰ 66 Sᴰ
  lem-sym-bc-at032032 : Ws → St 876
  lem-sym-bc-at032032 = pickᴰ 67 Sᴰ
  lem-sym-bc-at04203243 : Ws → St 877
  lem-sym-bc-at04203243 = pickᴰ 68 Sᴰ
  lem-sym-bc-at14233142 : Ws → St 921
  lem-sym-bc-at14233142 = pickᴰ 69 Sᴰ
  lem-QVQ-at02102331 : Ws → St 922
  lem-QVQ-at02102331 = pickᴰ 70 Sᴰ
  lem-QVQ-at02142041 : Ws → St 923
  lem-QVQ-at02142041 = pickᴰ 71 Sᴰ
  lem-QVQ-at02142140 : Ws → St 924
  lem-QVQ-at02142140 = pickᴰ 72 Sᴰ
  lem-QVQ-at0314203241 : Ws → St 925
  lem-QVQ-at0314203241 = pickᴰ 73 Sᴰ
  lem-QVQ-at03243042 : Ws → St 926
  lem-QVQ-at03243042 = pickᴰ 74 Sᴰ
  lem-QVQ-at0410233142 : Ws → St 927
  lem-QVQ-at0410233142 = pickᴰ 75 Sᴰ
  lem-QVQ-at0410233241 : Ws → St 928
  lem-QVQ-at0410233241 = pickᴰ 76 Sᴰ
  lem-QVQ-at04103143 : Ws → St 929
  lem-QVQ-at04103143 = pickᴰ 77 Sᴰ
  lem-QVQ-at04122041 : Ws → St 930
  lem-QVQ-at04122041 = pickᴰ 78 Sᴰ
  lem-QVQ-at0412213043 : Ws → St 931
  lem-QVQ-at0412213043 = pickᴰ 79 Sᴰ
  lem-QVQ-at04122140 : Ws → St 932
  lem-QVQ-at04122140 = pickᴰ 80 Sᴰ
  lem-QVQ-at0412233041 : Ws → St 933
  lem-QVQ-at0412233041 = pickᴰ 81 Sᴰ
  lem-QVQ-at0412233140 : Ws → St 934
  lem-QVQ-at0412233140 = pickᴰ 82 Sᴰ
  lem-QVQ-at0413203142 : Ws → St 935
  lem-QVQ-at0413203142 = pickᴰ 83 Sᴰ
  lem-QVQ-at0413203241 : Ws → St 936
  lem-QVQ-at0413203241 = pickᴰ 84 Sᴰ
  lem-QVQ-at0413213240 : Ws → St 937
  lem-QVQ-at0413213240 = pickᴰ 85 Sᴰ
  lem-QVQ-at04233042 : Ws → St 938
  lem-QVQ-at04233042 = pickᴰ 86 Sᴰ
  lem-QVQ-at0440 : Ws → St 939
  lem-QVQ-at0440 = pickᴰ 87 Sᴰ
  lem-QVQ-at142142 : Ws → St 940
  lem-QVQ-at142142 = pickᴰ 88 Sᴰ
  lem-SWbc-box-at02102331 : Ws → St 941
  lem-SWbc-box-at02102331 = pickᴰ 89 Sᴰ
  lem-SWbc-box-at041041 : Ws → St 942
  lem-SWbc-box-at041041 = pickᴰ 90 Sᴰ
  lem-SWbc-box-at04122041 : Ws → St 943
  lem-SWbc-box-at04122041 = pickᴰ 91 Sᴰ
  lem-SWbc-box-at04122140 : Ws → St 944
  lem-SWbc-box-at04122140 = pickᴰ 92 Sᴰ
  lem-SWbc-box-at0412233041 : Ws → St 945
  lem-SWbc-box-at0412233041 = pickᴰ 93 Sᴰ
  lem-SWbc-box-at0412233140 : Ws → St 946
  lem-SWbc-box-at0412233140 = pickᴰ 94 Sᴰ
  lem-SWbc-box-at0413203142 : Ws → St 947
  lem-SWbc-box-at0413203142 = pickᴰ 95 Sᴰ
  lem-SWbc-box-at0413213042 : Ws → St 948
  lem-SWbc-box-at0413213042 = pickᴰ 96 Sᴰ
  lem-SWbc-box-at0413213240 : Ws → St 949
  lem-SWbc-box-at0413213240 = pickᴰ 97 Sᴰ
  lem-SWbc-box-at04133140 : Ws → St 950
  lem-SWbc-box-at04133140 = pickᴰ 98 Sᴰ
  lem-SWbc-box-at04233240 : Ws → St 951
  lem-SWbc-box-at04233240 = pickᴰ 99 Sᴰ
  lem-SWbc-box-at0440 : Ws → St 952
  lem-SWbc-box-at0440 = pickᴰ 100 Sᴰ
  lem-SWbc-box-at142142 : Ws → St 953
  lem-SWbc-box-at142142 = pickᴰ 101 Sᴰ
  lem-XCSX-box-2-at04122041 : Ws → St 954
  lem-XCSX-box-2-at04122041 = pickᴰ 102 Sᴰ
  lem-box-cP-at0213243041 : Ws → St 889
  lem-box-cP-at0213243041 = pickᴰ 103 Sᴰ
  lem-box-cP-at0310213442 : Ws → St 891
  lem-box-cP-at0310213442 = pickᴰ 104 Sᴰ
  lem-sym-bc-at021021 : Ws → St 955
  lem-sym-bc-at021021 = pickᴰ 105 Sᴰ
  lem-sym-bc-at0210213443 : Ws → St 956
  lem-sym-bc-at0210213443 = pickᴰ 106 Sᴰ

private
  q1 : Ws → Eqn
  q1 c4 = sE 138 (lem-box-tQ-at03102132 c4)
  q2 : Ws → Eqn
  q2 c4 = sE 867 (lem-box-cP-at03102132 c4)
  q3 : Ws → Eqn
  q3 c4 = wlE 443 (lit c4)
  q4 : Ws → Eqn
  q4 c4 = sE 913 (lem-t-cP-at03102132 c4)
  q5 : Ws → Eqn
  q5 c4 = wlE 305 (lit c4)

-- box2 @03102132: 11 steps
lem-box2-at03102132 : Ws → ⟪ (ℓ "佤佤") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at03102132 c4 = derive (ℓ "佤佤") []
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
  q7 c4 = sE 923 (lem-QVQ-at02142041 c4)
  q8 : Ws → Eqn
  q8 c4 = sE 408 (lem-tP-at02142041 c4)
  q9 : Ws → Eqn
  q9 c4 = wpE 19 c4

-- box-cP @02142041: 12 steps
lem-box-cP-at02142041 : Ws → ⟪ (ℓ "余") ⟫ʷ ≈ ⟪ (ℓ "亜亦亜亦") ⟫ʷ
lem-box-cP-at02142041 c4 = derive (ℓ "余") (ℓ "亜亦亜亦")
  (re 0 1 (ℓ "亜亞佘亞亜佘") ∷
   re 2 1 (ℓ "亰亳佗亳亰佗") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q6 c4) ∷
   re 5 1 (ℓ "亰亳佗亳亰佗") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q6 c4) ∷
   rw 2 (q7 c4) ∷
   rw 1 (q8 c4) ∷
   rw 2 (q9 c4) ∷ []) Eq.refl

private
  q10 : Ws → Eqn
  q10 c4 = sE 925 (lem-QVQ-at0314203241 c4)
  q11 : Ws → Eqn
  q11 c4 = sE 411 (lem-tP-at0314203241 c4)
  q12 : Ws → Eqn
  q12 c4 = wpE 351 c4

-- box-cP @0314203241: 12 steps
lem-box-cP-at0314203241 : Ws → ⟪ (ℓ "佾") ⟫ʷ ≈ ⟪ (ℓ "亠产亠产") ⟫ʷ
lem-box-cP-at0314203241 c4 = derive (ℓ "佾") (ℓ "亠产亠产")
  (re 0 1 (ℓ "亠亢佽亢亠佽") ∷
   re 2 1 (ℓ "亰亳佼亳亰佼") ∷
   re 4 1 (ℓ "乗") ∷
   re 7 1 (ℓ "乗") ∷
   rw⁻ 2 (q6 c4) ∷
   re 5 1 (ℓ "亰亳佼亳亰佼") ∷
   re 7 1 (ℓ "乗") ∷
   re 10 1 (ℓ "乗") ∷
   rw⁻ 5 (q6 c4) ∷
   rw 2 (q10 c4) ∷
   rw 1 (q11 c4) ∷
   rw 2 (q12 c4) ∷ []) Eq.refl

private
  q13 : Ws → Eqn
  q13 c4 = sE 876 (lem-sym-bc-at032032 c4)

-- box-perm-1324 @032032: 1 steps
lem-box-perm-1324-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "佬") ⟫ʷ
lem-box-perm-1324-at032032 c4 = derive (ℓ "佪") (ℓ "佬")
  (rw 0 (q13 c4) ∷ []) Eq.refl

private
  q14 : Ws → Eqn
  q14 c4 = sE 897 (lem-sym-ab-at0330 c4)

-- box-perm-3124 @032032: 2 steps
lem-box-perm-3124-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "佲") ⟫ʷ
lem-box-perm-3124-at032032 c4 = derive (ℓ "佪") (ℓ "佲")
  (rw 0 (q13 c4) ∷
   rw 0 (q14 c4) ∷ []) Eq.refl

private
  q15 : Ws → Eqn
  q15 c4 = sE 920 (lem-sym-bc-at0220 c4)
  q16 : Ws → Eqn
  q16 c4 = sE 896 (lem-sym-ab-at022330 c4)

-- box-perm-3124 @0220: 2 steps
lem-box-perm-3124-at0220 : Ws → ⟪ (ℓ "伳") ⟫ʷ ≈ ⟪ (ℓ "佅") ⟫ʷ
lem-box-perm-3124-at0220 c4 = derive (ℓ "伳") (ℓ "佅")
  (rw 0 (q15 c4) ∷
   rw 0 (q16 c4) ∷ []) Eq.refl

private
  q17 : Ws → Eqn
  q17 c4 = sE 54 (lem-sym-ab-at032032 c4)
  q18 : Ws → Eqn
  q18 c4 = sE 874 (lem-sym-bc-at03102132 c4)
  q19 : Ws → Eqn
  q19 c4 = sE 904 (lem-sym-ab-at031031 c4)

-- box-perm-3214 @032032: 3 steps
lem-box-perm-3214-at032032 : Ws → ⟪ (ℓ "佪") ⟫ʷ ≈ ⟪ (ℓ "佰") ⟫ʷ
lem-box-perm-3214-at032032 c4 = derive (ℓ "佪") (ℓ "佰")
  (rw 0 (q17 c4) ∷
   rw 0 (q18 c4) ∷
   rw 0 (q19 c4) ∷ []) Eq.refl

private
  q20 : Ws → Eqn
  q20 c4 = sE 955 (lem-sym-bc-at021021 c4)

-- box-perm-1324 @021021: 1 steps
lem-box-perm-1324-at021021 : Ws → ⟪ (ℓ "伭") ⟫ʷ ≈ ⟪ (ℓ "伯") ⟫ʷ
lem-box-perm-1324-at021021 c4 = derive (ℓ "伭") (ℓ "伯")
  (rw 0 (q20 c4) ∷ []) Eq.refl

private
  q21 : Ws → Eqn
  q21 c4 = wpE 1232 c4
  q22 : Ws → Eqn
  q22 c4 = sE 922 (lem-QVQ-at02102331 c4)
  q23 : Ws → Eqn
  q23 c4 = sE 405 (lem-tP-at02102331 c4)
  q24 : Ws → Eqn
  q24 c4 = wlE 635 (lit c4)

-- box-cP @02102331: 12 steps
lem-box-cP-at02102331 : Ws → ⟪ (ℓ "伯") ⟫ʷ ≈ ⟪ (ℓ "亘亪亘亪") ⟫ʷ
lem-box-cP-at02102331 c4 = derive (ℓ "伯") (ℓ "亘亪亘亪")
  (re 0 1 (ℓ "亘亚从亚亘从") ∷
   re 2 1 (ℓ "二亍仍亍二仍") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw 2 (q21 c4) ∷
   re 5 1 (ℓ "二亍仍亍二仍") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw 5 (q21 c4) ∷
   rw 2 (q22 c4) ∷
   rw 1 (q23 c4) ∷
   rw 2 (q24 c4) ∷ []) Eq.refl

private
  q25 : Ws → Eqn
  q25 c4 = sE 953 (lem-SWbc-box-at142142 c4)
  q26 : Ws → Eqn
  q26 c4 = sE 912 (lem-nat-SWbc-at142142 c4)

-- sym-bc @142142: 2 steps
lem-sym-bc-at142142 : Ws → ⟪ (ℓ "企") ⟫ʷ ≈ ⟪ (ℓ "伋") ⟫ʷ
lem-sym-bc-at142142 c4 = derive (ℓ "企") (ℓ "伋")
  (rw⁻ 0 (q25 c4) ∷
   rw 0 (q26 c4) ∷ []) Eq.refl

private
  q27 : Ws → Eqn
  q27 c4 = sE 895 (lem-sym-ab-at13243142 c4)
  q28 : Ws → Eqn
  q28 c4 = sE 921 (lem-sym-bc-at14233142 c4)

-- box-perm-2314 @13243142: 2 steps
lem-box-perm-2314-at13243142 : Ws → ⟪ (ℓ "仳") ⟫ʷ ≈ ⟪ (ℓ "企") ⟫ʷ
lem-box-perm-2314-at13243142 c4 = derive (ℓ "仳") (ℓ "企")
  (rw 0 (q27 c4) ∷
   rw 0 (q28 c4) ∷ []) Eq.refl

private
  q29 : Ws → Eqn
  q29 c4 = wlE 344 (lit c4)
  q30 : Ws → Eqn
  q30 c4 = sE 926 (lem-QVQ-at03243042 c4)
  q31 : Ws → Eqn
  q31 c4 = sE 413 (lem-tP-at03243042 c4)
  q32 : Ws → Eqn
  q32 c4 = wlE 788 (lit c4)

-- box-cP @03243042: 12 steps
lem-box-cP-at03243042 : Ws → ⟪ (ℓ "佮") ⟫ʷ ≈ ⟪ (ℓ "京些京些") ⟫ʷ
lem-box-cP-at03243042 c4 = derive (ℓ "佮") (ℓ "京些京些")
  (re 0 1 (ℓ "京亮会亮京会") ∷
   re 2 1 (ℓ "亐互伙互亐伙") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw 2 (q29 c4) ∷
   re 5 1 (ℓ "亐互伙互亐伙") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw 5 (q29 c4) ∷
   rw 2 (q30 c4) ∷
   rw 1 (q31 c4) ∷
   rw 2 (q32 c4) ∷ []) Eq.refl

private
  q33 : Ws → Eqn
  q33 c4 = sE 903 (lem-sym-ab-at02102331 c4)

-- box-perm-3124 @021021: 2 steps
lem-box-perm-3124-at021021 : Ws → ⟪ (ℓ "伭") ⟫ʷ ≈ ⟪ (ℓ "似") ⟫ʷ
lem-box-perm-3124-at021021 c4 = derive (ℓ "伭") (ℓ "似")
  (rw 0 (q20 c4) ∷
   rw 0 (q33 c4) ∷ []) Eq.refl

private
  q34 : Ws → Eqn
  q34 c4 = sE 941 (lem-SWbc-box-at02102331 c4)
  q35 : Ws → Eqn
  q35 c4 = sE 905 (lem-nat-SWbc-at02102331 c4)

-- sym-bc @02102331: 2 steps
lem-sym-bc-at02102331 : Ws → ⟪ (ℓ "伯") ⟫ʷ ≈ ⟪ (ℓ "伭") ⟫ʷ
lem-sym-bc-at02102331 c4 = derive (ℓ "伯") (ℓ "伭")
  (rw⁻ 0 (q34 c4) ∷
   rw 0 (q35 c4) ∷ []) Eq.refl

private
  q36 : Ws → Eqn
  q36 c4 = wpE 661 c4
  q37 : Ws → Eqn
  q37 c4 = sE 940 (lem-QVQ-at142142 c4)
  q38 : Ws → Eqn
  q38 c4 = sE 418 (lem-tP-at142142 c4)
  q39 : Ws → Eqn
  q39 c4 = wpE 51 c4

-- box-cP @142142: 12 steps
lem-box-cP-at142142 : Ws → ⟪ (ℓ "企") ⟫ʷ ≈ ⟪ (ℓ "五亙五亙") ⟫ʷ
lem-box-cP-at142142 c4 = derive (ℓ "企") (ℓ "五亙五亙")
  (re 0 1 (ℓ "五井伀井五伀") ∷
   re 2 1 (ℓ "亠亣仿亣亠仿") ∷
   re 4 1 (ℓ "乫") ∷
   re 7 1 (ℓ "乫") ∷
   rw⁻ 2 (q36 c4) ∷
   re 5 1 (ℓ "亠亣仿亣亠仿") ∷
   re 7 1 (ℓ "乫") ∷
   re 10 1 (ℓ "乫") ∷
   rw⁻ 5 (q36 c4) ∷
   rw 2 (q37 c4) ∷
   rw 1 (q38 c4) ∷
   rw 2 (q39 c4) ∷ []) Eq.refl

private
  q40 : Ws → Eqn
  q40 c4 = sE 83 (lem-box-tQ-at032032 c4)
  q41 : Ws → Eqn
  q41 c4 = sE 868 (lem-box-cP-at032032 c4)
  q42 : Ws → Eqn
  q42 c4 = sE 914 (lem-t-cP-at032032 c4)

-- box2 @032032: 11 steps
lem-box2-at032032 : Ws → ⟪ (ℓ "佪佪") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at032032 c4 = derive (ℓ "佪佪") []
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
  q43 c4 = sE 943 (lem-SWbc-box-at04122041 c4)
  q44 : Ws → Eqn
  q44 c4 = sE 906 (lem-nat-SWbc-at04122041 c4)

-- sym-bc @04122041: 2 steps
lem-sym-bc-at04122041 : Ws → ⟪ (ℓ "侗") ⟫ʷ ≈ ⟪ (ℓ "侚") ⟫ʷ
lem-sym-bc-at04122041 c4 = derive (ℓ "侗") (ℓ "侚")
  (rw⁻ 0 (q43 c4) ∷
   rw 0 (q44 c4) ∷ []) Eq.refl

private
  q45 : Ws → Eqn
  q45 c4 = wpE 218 c4
  q46 : Ws → Eqn
  q46 c4 = sE 933 (lem-QVQ-at0412233041 c4)
  q47 : Ws → Eqn
  q47 c4 = sE 416 (lem-tP-at0412233041 c4)
  q48 : Ws → Eqn
  q48 c4 = wlE 457 (lit c4)

-- box-cP @0412233041: 12 steps
lem-box-cP-at0412233041 : Ws → ⟪ (ℓ "侚") ⟫ʷ ≈ ⟪ (ℓ "亰亗亰亗") ⟫ʷ
lem-box-cP-at0412233041 c4 = derive (ℓ "侚") (ℓ "亰亗亰亗")
  (re 0 1 (ℓ "亰亳佑亳亰佑") ∷
   re 2 1 (ℓ "亜亞佐亞亜佐") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw⁻ 2 (q45 c4) ∷
   re 5 1 (ℓ "亜亞佐亞亜佐") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw⁻ 5 (q45 c4) ∷
   rw 2 (q46 c4) ∷
   rw 1 (q47 c4) ∷
   rw 2 (q48 c4) ∷ []) Eq.refl

private
  q49 : Ws → Eqn
  q49 c4 = wlE 1271 (lit c4)
  q50 : Ws → Eqn
  q50 c4 = sE 930 (lem-QVQ-at04122041 c4)
  q51 : Ws → Eqn
  q51 c4 = sE 415 (lem-tP-at04122041 c4)
  q52 : Ws → Eqn
  q52 c4 = wpE 1323 c4

-- box-cP @04122041: 12 steps
lem-box-cP-at04122041 : Ws → ⟪ (ℓ "侗") ⟫ʷ ≈ ⟪ (ℓ "亜亯亜亯") ⟫ʷ
lem-box-cP-at04122041 c4 = derive (ℓ "侗") (ℓ "亜亯亜亯")
  (re 0 1 (ℓ "亜亟佣亟亜佣") ∷
   re 2 1 (ℓ "亰亱佐亱亰佐") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw⁻ 2 (q49 c4) ∷
   re 5 1 (ℓ "亰亱佐亱亰佐") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw⁻ 5 (q49 c4) ∷
   rw 2 (q50 c4) ∷
   rw 1 (q51 c4) ∷
   rw 2 (q52 c4) ∷ []) Eq.refl

private
  q53 : Ws → Eqn
  q53 c4 = wpE 1331 c4
  q54 : Ws → Eqn
  q54 c4 = sE 929 (lem-QVQ-at04103143 c4)
  q55 : Ws → Eqn
  q55 c4 = sE 414 (lem-tP-at04103143 c4)

-- box-cP @04103143: 12 steps
lem-box-cP-at04103143 : Ws → ⟪ (ℓ "侎") ⟫ʷ ≈ ⟪ (ℓ "亜亯亜亯") ⟫ʷ
lem-box-cP-at04103143 c4 = derive (ℓ "侎") (ℓ "亜亯亜亯")
  (re 0 1 (ℓ "亜亟仾亟亜仾") ∷
   re 2 1 (ℓ "五井份井五份") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw 2 (q53 c4) ∷
   re 5 1 (ℓ "五井份井五份") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw 5 (q53 c4) ∷
   rw 2 (q54 c4) ∷
   rw 1 (q55 c4) ∷
   rw 2 (q52 c4) ∷ []) Eq.refl

private
  q56 : Ws → Eqn
  q56 c4 = wpE 212 c4
  q57 : Ws → Eqn
  q57 c4 = sE 938 (lem-QVQ-at04233042 c4)
  q58 : Ws → Eqn
  q58 c4 = sE 417 (lem-tP-at04233042 c4)
  q59 : Ws → Eqn
  q59 c4 = wlE 1474 (lit c4)

-- box-cP @04233042: 12 steps
lem-box-cP-at04233042 : Ws → ⟪ (ℓ "侕") ⟫ʷ ≈ ⟪ (ℓ "京亟京亟") ⟫ʷ
lem-box-cP-at04233042 c4 = derive (ℓ "侕") (ℓ "京亟京亟")
  (re 0 1 (ℓ "京亯伣亯京伣") ∷
   re 2 1 (ℓ "五亖伢亖五伢") ∷
   re 4 1 (ℓ "义") ∷
   re 7 1 (ℓ "义") ∷
   rw 2 (q56 c4) ∷
   re 5 1 (ℓ "五亖伢亖五伢") ∷
   re 7 1 (ℓ "义") ∷
   re 10 1 (ℓ "义") ∷
   rw 5 (q56 c4) ∷
   rw 2 (q57 c4) ∷
   rw 1 (q58 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q60 : Ws → Eqn
  q60 c4 = sE 915 (lem-P-box-at0410213243 c4)
  q61 : Ws → Eqn
  q61 c4 = sE 869 (lem-box-cP-at0410213243 c4)
  q62 : Ws → Eqn
  q62 c4 = sE 421 (lem-box-tQ-at0412233041 c4)

-- pairs @0410213243: 4 steps
lem-pairs-at0410213243 : Ws → ⟪ (ℓ "侍") ⟫ʷ ≈ ⟪ (ℓ "侚") ⟫ʷ
lem-pairs-at0410213243 c4 = derive (ℓ "侍") (ℓ "侚")
  (rw⁻ 0 (q60 c4) ∷
   rw 1 (q61 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 0 (q62 c4) ∷ []) Eq.refl

private
  q63 : Ws → Eqn
  q63 c4 = sE 945 (lem-SWbc-box-at0412233041 c4)
  q64 : Ws → Eqn
  q64 c4 = sE 908 (lem-nat-SWbc-at0412233041 c4)

-- sym-bc @0412233041: 2 steps
lem-sym-bc-at0412233041 : Ws → ⟪ (ℓ "侚") ⟫ʷ ≈ ⟪ (ℓ "侗") ⟫ʷ
lem-sym-bc-at0412233041 c4 = derive (ℓ "侚") (ℓ "侗")
  (rw⁻ 0 (q63 c4) ∷
   rw 0 (q64 c4) ∷ []) Eq.refl

private
  q65 : Ws → Eqn
  q65 c4 = wlE 1441 (lit c4)
  q66 : Ws → Eqn
  q66 c4 = wlE 1515 (lit c4)
  q67 : Ws → Eqn
  q67 c4 = sE 919 (lem-box-cP-at04203243 c4)
  q68 : Ws → Eqn
  q68 c4 = eqn (ℓ "丒亳") (ℓ "亳丒") (c₂ (K ↑) (Toffᵗ))
  q69 : Ws → Eqn
  q69 c4 = eqn (ℓ "中亳") (ℓ "亳中") (c₂ (CK₀₁) (Toffᵗ))
  q70 : Ws → Eqn
  q70 c4 = eqn (ℓ "上亳") (ℓ "亳上") (c₁ (S) (Toffᵗ ↑))
  q71 : Ws → Eqn
  q71 c4 = wpE 1350 c4
  q72 : Ws → Eqn
  q72 c4 = wlE 1443 (lit c4)

-- F4-CS1-K1 @0440: 19 steps
lem-F4-CS1-K1-at0440 : Ws → ⟪ (ℓ "与俭与中") ⟫ʷ ≈ ⟪ (ℓ "中与俭与") ⟫ʷ
lem-F4-CS1-K1-at0440 c4 = derive (ℓ "与俭与中") (ℓ "中与俭与")
  (rw⁻ 2 (q65 c4) ∷
   re 1 1 (ℓ "侒些俫些俬") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
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
   re 6 1 (ℓ "俫") ∷
   re 8 1 (ℓ "俬") ∷
   re 4 5 (ℓ "俭") ∷
   rw⁻ 0 (q72 c4) ∷ []) Eq.refl

private
  q73 : Ws → Eqn
  q73 c4 = wpE 1351 c4
  q74 : Ws → Eqn
  q74 c4 = wlE 1516 (lit c4)
  q75 : Ws → Eqn
  q75 c4 = eqn (ℓ "与亳") (ℓ "亳与") (c₁ (X) (Toffᵗ ↑))
  q76 : Ws → Eqn
  q76 c4 = wlE 207 (lit c4)
  q77 : Ws → Eqn
  q77 c4 = wpE 53 c4
  q78 : Ws → Eqn
  q78 c4 = wpE 54 c4
  q79 : Ws → Eqn
  q79 c4 = sE 704 (lem-comm-CSd23-CCZ014 c4)
  q80 : Ws → Eqn
  q80 c4 = sE 703 (lem-comm-CS23-CCZ014 c4)
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
  q89 c4 = sE 6 (lem-comm-CX23-CCZ014 c4)
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
  q97 c4 = eqn (ℓ "乄亳") (ℓ "亳乄") (c₂ (CX₁₀) (Toffᵗ))
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
  q112 c4 = sE 893 (lem-comm-CCZ014-CX23 c4)
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
lem-F4-CS1-CS1-at0440 : Ws → ⟪ (ℓ "与俭与俭") ⟫ʷ ≈ ⟪ (ℓ "俭与俭与") ⟫ʷ
lem-F4-CS1-CS1-at0440 c4 = derive (ℓ "与俭与俭") (ℓ "俭与俭与")
  (re 3 1 (ℓ "侒些俫些俬") ∷
   re 5 1 (ℓ "乎") ∷
   re 7 1 (ℓ "乏") ∷
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
   re 1 1 (ℓ "侒些俫些俬") ∷
   re 5 1 (ℓ "乏") ∷
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
   re 3 1 (ℓ "乎") ∷
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
   re 4 1 (ℓ "俫") ∷
   re 6 1 (ℓ "俬") ∷
   re 2 5 (ℓ "俭") ∷
   rw⁻ 3 (q107 c4) ∷
   re 2 1 (ℓ "侒些俫些俬") ∷
   re 4 1 (ℓ "乎") ∷
   re 6 1 (ℓ "乏") ∷
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
   re 6 1 (ℓ "俫") ∷
   re 8 1 (ℓ "俬") ∷
   re 4 5 (ℓ "俭") ∷
   rw⁻ 1 (q117 c4) ∷
   rw⁻ 4 (q118 c4) ∷
   re 3 1 (ℓ "侒些俫些俬") ∷
   re 5 1 (ℓ "乎") ∷
   re 7 1 (ℓ "乏") ∷
   rw⁻ 4 (q119 c4) ∷
   rw 3 (q67 c4) ∷
   rw⁻ 6 (q102 c4) ∷
   rw 5 (q77 c4) ∷
   rw⁻ 4 (q102 c4) ∷
   rw 3 (q77 c4) ∷
   rw⁻ 4 (q67 c4) ∷
   re 6 1 (ℓ "俫") ∷
   re 8 1 (ℓ "俬") ∷
   re 4 5 (ℓ "俭") ∷
   rw⁻ 2 (q118 c4) ∷
   rw⁻ 5 (q107 c4) ∷
   re 4 1 (ℓ "侒些俫些俬") ∷
   re 6 1 (ℓ "乎") ∷
   re 8 1 (ℓ "乏") ∷
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
   re 8 1 (ℓ "俫") ∷
   re 10 1 (ℓ "俬") ∷
   re 6 5 (ℓ "俭") ∷
   rw⁻ 3 (q117 c4) ∷
   rw⁻ 6 (q120 c4) ∷
   re 5 1 (ℓ "侒些俫些俬") ∷
   re 7 1 (ℓ "乎") ∷
   re 9 1 (ℓ "乏") ∷
   rw⁻ 6 (q121 c4) ∷
   rw 5 (q67 c4) ∷
   rw⁻ 8 (q85 c4) ∷
   rw 7 (q84 c4) ∷
   rw⁻ 6 (q85 c4) ∷
   rw 5 (q84 c4) ∷
   rw⁻ 6 (q67 c4) ∷
   re 8 1 (ℓ "俫") ∷
   re 10 1 (ℓ "俬") ∷
   re 6 5 (ℓ "俭") ∷
   rw⁻ 4 (q120 c4) ∷
   re 2 1 (ℓ "俫") ∷
   re 4 1 (ℓ "俬") ∷
   re 0 5 (ℓ "俭") ∷ []) Eq.refl

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
lem-F4-I-CS1-at0440 : Ws → ⟪ (ℓ "与上与俭") ⟫ʷ ≈ ⟪ (ℓ "俭与上与") ⟫ʷ
lem-F4-I-CS1-at0440 c4 = derive (ℓ "与上与俭") (ℓ "俭与上与")
  (re 3 1 (ℓ "侒些俫些俬") ∷
   re 5 1 (ℓ "乎") ∷
   re 7 1 (ℓ "乏") ∷
   rw 3 (q67 c4) ∷
   rw⁻ 0 (q122 c4) ∷
   rw⁻ 1 (q123 c4) ∷
   rw⁻ 2 (q122 c4) ∷
   rw⁻ 3 (q123 c4) ∷
   rw⁻ 0 (q67 c4) ∷
   rw⁻ 1 (q124 c4) ∷
   re 2 1 (ℓ "俫") ∷
   re 4 1 (ℓ "俬") ∷
   re 0 5 (ℓ "俭") ∷
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
lem-F4-CS1-I-at0440 : Ws → ⟪ (ℓ "与俭与上") ⟫ʷ ≈ ⟪ (ℓ "上与俭与") ⟫ʷ
lem-F4-CS1-I-at0440 c4 = derive (ℓ "与俭与上") (ℓ "上与俭与")
  (rw 2 (q126 c4) ∷
   re 1 1 (ℓ "侒些俫些俬") ∷
   re 3 1 (ℓ "乎") ∷
   re 5 1 (ℓ "乏") ∷
   rw 2 (q127 c4) ∷
   rw 1 (q67 c4) ∷
   rw 4 (q128 c4) ∷
   rw 3 (q129 c4) ∷
   rw 2 (q128 c4) ∷
   rw 1 (q129 c4) ∷
   rw⁻ 3 (q67 c4) ∷
   re 5 1 (ℓ "俫") ∷
   re 7 1 (ℓ "俬") ∷
   re 3 5 (ℓ "俭") ∷
   rw⁻ 0 (q130 c4) ∷ []) Eq.refl

private
  q131 : Ws → Eqn
  q131 c4 = sE 877 (lem-sym-bc-at04203243 c4)

-- box-perm-1324 @04203243: 1 steps
lem-box-perm-1324-at04203243 : Ws → ⟪ (ℓ "侒") ⟫ʷ ≈ ⟪ (ℓ "侓") ⟫ʷ
lem-box-perm-1324-at04203243 c4 = derive (ℓ "侒") (ℓ "侓")
  (rw 0 (q131 c4) ∷ []) Eq.refl

private
  q132 : Ws → Eqn
  q132 c4 = sE 942 (lem-SWbc-box-at041041 c4)
  q133 : Ws → Eqn
  q133 c4 = sE 898 (lem-nat-SWbc-at041041 c4)

-- sym-bc @041041: 2 steps
lem-sym-bc-at041041 : Ws → ⟪ (ℓ "侏") ⟫ʷ ≈ ⟪ (ℓ "侑") ⟫ʷ
lem-sym-bc-at041041 c4 = derive (ℓ "侏") (ℓ "侑")
  (rw⁻ 0 (q132 c4) ∷
   rw 0 (q133 c4) ∷ []) Eq.refl

private
  q134 : Ws → Eqn
  q134 c4 = wpE 516 c4
  q135 : Ws → Eqn
  q135 c4 = sE 928 (lem-QVQ-at0410233241 c4)
  q136 : Ws → Eqn
  q136 c4 = sE 427 (lem-tP-at0410233241 c4)
  q137 : Ws → Eqn
  q137 c4 = wpE 317 c4

-- box-cP @0410233241: 12 steps
lem-box-cP-at0410233241 : Ws → ⟪ (ℓ "侑") ⟫ʷ ≈ ⟪ (ℓ "亠享亠享") ⟫ʷ
lem-box-cP-at0410233241 c4 = derive (ℓ "侑") (ℓ "亠享亠享")
  (re 0 1 (ℓ "亠亣伃亣亠伃") ∷
   re 2 1 (ℓ "亜亝伂亝亜伂") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw 2 (q134 c4) ∷
   re 5 1 (ℓ "亜亝伂亝亜伂") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw 5 (q134 c4) ∷
   rw 2 (q135 c4) ∷
   rw 1 (q136 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q138 : Ws → Eqn
  q138 c4 = wpE 598 c4
  q139 : Ws → Eqn
  q139 c4 = sE 931 (lem-QVQ-at0412213043 c4)
  q140 : Ws → Eqn
  q140 c4 = sE 428 (lem-tP-at0412213043 c4)
  q141 : Ws → Eqn
  q141 c4 = wlE 470 (lit c4)

-- box-cP @0412213043: 12 steps
lem-box-cP-at0412213043 : Ws → ⟪ (ℓ "侘") ⟫ʷ ≈ ⟪ (ℓ "亨亣亨亣") ⟫ʷ
lem-box-cP-at0412213043 c4 = derive (ℓ "侘") (ℓ "亨亣亨亣")
  (re 0 1 (ℓ "亨享佖享亨佖") ∷
   re 2 1 (ℓ "亜亞何亞亜何") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw 2 (q138 c4) ∷
   re 5 1 (ℓ "亜亞何亞亜何") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
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
lem-F4-K1-CS1-at0440 : Ws → ⟪ (ℓ "与中与俭") ⟫ʷ ≈ ⟪ (ℓ "俭与中与") ⟫ʷ
lem-F4-K1-CS1-at0440 c4 = derive (ℓ "与中与俭") (ℓ "俭与中与")
  (re 3 1 (ℓ "侒些俫些俬") ∷
   re 5 1 (ℓ "乎") ∷
   re 7 1 (ℓ "乏") ∷
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
   re 2 1 (ℓ "俫") ∷
   re 4 1 (ℓ "俬") ∷
   re 0 5 (ℓ "俭") ∷ []) Eq.refl

private
  q144 : Ws → Eqn
  q144 c4 = sE 951 (lem-SWbc-box-at04233240 c4)
  q145 : Ws → Eqn
  q145 c4 = sE 901 (lem-nat-SWbc-at04233240 c4)

-- sym-bc @04233240: 2 steps
lem-sym-bc-at04233240 : Ws → ⟪ (ℓ "侖") ⟫ʷ ≈ ⟪ (ℓ "侔") ⟫ʷ
lem-sym-bc-at04233240 c4 = derive (ℓ "侖") (ℓ "侔")
  (rw⁻ 0 (q144 c4) ∷
   rw 0 (q145 c4) ∷ []) Eq.refl

private
  q146 : Ws → Eqn
  q146 c4 = wpE 733 c4
  q147 : Ws → Eqn
  q147 c4 = sE 939 (lem-QVQ-at0440 c4)
  q148 : Ws → Eqn
  q148 c4 = sE 430 (lem-tP-at0440 c4)

-- box-cP @0440: 12 steps
lem-box-cP-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "亨亣亨亣") ⟫ʷ
lem-box-cP-at0440 c4 = derive (ℓ "侔") (ℓ "亨亣亨亣")
  (re 0 1 (ℓ "亨享伬享亨伬") ∷
   re 2 1 (ℓ "京亭伦亭京伦") ∷
   re 4 1 (ℓ "个") ∷
   re 7 1 (ℓ "个") ∷
   rw⁻ 2 (q146 c4) ∷
   re 5 1 (ℓ "京亭伦亭京伦") ∷
   re 7 1 (ℓ "个") ∷
   re 10 1 (ℓ "个") ∷
   rw⁻ 5 (q146 c4) ∷
   rw 2 (q147 c4) ∷
   rw 1 (q148 c4) ∷
   rw 2 (q141 c4) ∷ []) Eq.refl

private
  q149 : Ws → Eqn
  q149 c4 = sE 947 (lem-SWbc-box-at0413203142 c4)
  q150 : Ws → Eqn
  q150 c4 = sE 899 (lem-nat-SWbc-at0413203142 c4)

-- sym-bc @0413203142: 2 steps
lem-sym-bc-at0413203142 : Ws → ⟪ (ℓ "侜") ⟫ʷ ≈ ⟪ (ℓ "侞") ⟫ʷ
lem-sym-bc-at0413203142 c4 = derive (ℓ "侜") (ℓ "侞")
  (rw⁻ 0 (q149 c4) ∷
   rw 0 (q150 c4) ∷ []) Eq.refl

private
  q151 : Ws → Eqn
  q151 c4 = wpE 992 c4
  q152 : Ws → Eqn
  q152 c4 = sE 924 (lem-QVQ-at02142140 c4)
  q153 : Ws → Eqn
  q153 c4 = sE 426 (lem-tP-at02142140 c4)
  q154 : Ws → Eqn
  q154 c4 = wlE 636 (lit c4)

-- box-cP @02142140: 12 steps
lem-box-cP-at02142140 : Ws → ⟪ (ℓ "佟") ⟫ʷ ≈ ⟪ (ℓ "亨亚亨亚") ⟫ʷ
lem-box-cP-at02142140 c4 = derive (ℓ "佟") (ℓ "亨亚亨亚")
  (re 0 1 (ℓ "亨亪佞亪亨佞") ∷
   re 2 1 (ℓ "亰亳住亳亰住") ∷
   re 4 1 (ℓ "丿") ∷
   re 7 1 (ℓ "丿") ∷
   rw⁻ 2 (q151 c4) ∷
   re 5 1 (ℓ "亰亳住亳亰住") ∷
   re 7 1 (ℓ "丿") ∷
   re 10 1 (ℓ "丿") ∷
   rw⁻ 5 (q151 c4) ∷
   rw 2 (q152 c4) ∷
   rw 1 (q153 c4) ∷
   rw 2 (q154 c4) ∷ []) Eq.refl

private
  q155 : Ws → Eqn
  q155 c4 = sE 948 (lem-SWbc-box-at0413213042 c4)
  q156 : Ws → Eqn
  q156 c4 = sE 900 (lem-nat-SWbc-at0413213042 c4)

-- sym-bc @0413213042: 2 steps
lem-sym-bc-at0413213042 : Ws → ⟪ (ℓ "侞") ⟫ʷ ≈ ⟪ (ℓ "侜") ⟫ʷ
lem-sym-bc-at0413213042 c4 = derive (ℓ "侞") (ℓ "侜")
  (rw⁻ 0 (q155 c4) ∷
   rw 0 (q156 c4) ∷ []) Eq.refl

private
  q157 : Ws → Eqn
  q157 c4 = wlE 1596 (lit c4)
  q158 : Ws → Eqn
  q158 c4 = sE 935 (lem-QVQ-at0413203142 c4)
  q159 : Ws → Eqn
  q159 c4 = sE 429 (lem-tP-at0413203142 c4)

-- box-cP @0413203142: 12 steps
lem-box-cP-at0413203142 : Ws → ⟪ (ℓ "侜") ⟫ʷ ≈ ⟪ (ℓ "亠享亠享") ⟫ʷ
lem-box-cP-at0413203142 c4 = derive (ℓ "侜") (ℓ "亠享亠享")
  (re 0 1 (ℓ "亠亣侃亣亠侃") ∷
   re 2 1 (ℓ "京亮佺亮京佺") ∷
   re 4 1 (ℓ "乤") ∷
   re 7 1 (ℓ "乤") ∷
   rw⁻ 2 (q157 c4) ∷
   re 5 1 (ℓ "京亮佺亮京佺") ∷
   re 7 1 (ℓ "乤") ∷
   re 10 1 (ℓ "乤") ∷
   rw⁻ 5 (q157 c4) ∷
   rw 2 (q158 c4) ∷
   rw 1 (q159 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q160 : Ws → Eqn
  q160 c4 = sE 952 (lem-SWbc-box-at0440 c4)
  q161 : Ws → Eqn
  q161 c4 = sE 902 (lem-nat-SWbc-at0440 c4)

-- sym-bc @0440: 2 steps
lem-sym-bc-at0440 : Ws → ⟪ (ℓ "侔") ⟫ʷ ≈ ⟪ (ℓ "侖") ⟫ʷ
lem-sym-bc-at0440 c4 = derive (ℓ "侔") (ℓ "侖")
  (rw⁻ 0 (q160 c4) ∷
   rw 0 (q161 c4) ∷ []) Eq.refl

private
  q162 : Ws → Eqn
  q162 c4 = wpE 766 c4
  q163 : Ws → Eqn
  q163 c4 = sE 937 (lem-QVQ-at0413213240 c4)
  q164 : Ws → Eqn
  q164 c4 = sE 446 (lem-tP-at0413213240 c4)

-- box-cP @0413213240: 12 steps
lem-box-cP-at0413213240 : Ws → ⟪ (ℓ "侟") ⟫ʷ ≈ ⟪ (ℓ "京亟京亟") ⟫ʷ
lem-box-cP-at0413213240 c4 = derive (ℓ "侟") (ℓ "京亟京亟")
  (re 0 1 (ℓ "京亯來亯京來") ∷
   re 2 1 (ℓ "亰亲使亲亰使") ∷
   re 4 1 (ℓ "丸") ∷
   re 7 1 (ℓ "丸") ∷
   rw⁻ 2 (q162 c4) ∷
   re 5 1 (ℓ "亰亲使亲亰使") ∷
   re 7 1 (ℓ "丸") ∷
   re 10 1 (ℓ "丸") ∷
   rw⁻ 5 (q162 c4) ∷
   rw 2 (q163 c4) ∷
   rw 1 (q164 c4) ∷
   rw 2 (q59 c4) ∷ []) Eq.refl

private
  q165 : Ws → Eqn
  q165 c4 = sE 875 (lem-sym-bc-at0310213442 c4)
  q166 : Ws → Eqn
  q166 c4 = sE 894 (lem-sym-ab-at0310243142 c4)

-- box-perm-3124 @0310213442: 2 steps
lem-box-perm-3124-at0310213442 : Ws → ⟪ (ℓ "佥") ⟫ʷ ≈ ⟪ (ℓ "佹") ⟫ʷ
lem-box-perm-3124-at0310213442 c4 = derive (ℓ "佥") (ℓ "佹")
  (rw 0 (q165 c4) ∷
   rw 0 (q166 c4) ∷ []) Eq.refl

private
  q167 : Ws → Eqn
  q167 c4 = sE 310 (lem-box-tQ-at0314203142 c4)
  q168 : Ws → Eqn
  q168 c4 = sE 889 (lem-box-cP-at0213243041 c4)
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
  q174 c4 = eqn (ℓ "丩亰") (ℓ "亰丩") (c₂ (CS • CS • CS) (CCZ))
  q175 : Ws → Eqn
  q175 c4 = eqn (ℓ "丨亰") (ℓ "亰丨") (c₂ (CS) (CCZ))
  q176 : Ws → Eqn
  q176 c4 = wlE 1636 (lit c4)
  q177 : Ws → Eqn
  q177 c4 = wpE 1071 c4
  q178 : Ws → Eqn
  q178 c4 = wpE 1288 c4
  q179 : Ws → Eqn
  q179 c4 = wpE 1185 c4
  q180 : Ws → Eqn
  q180 c4 = eqn (ℓ "亏丟") (ℓ "丟亏") (c₃ (Toffᵗ) (K • iI))
  q181 : Ws → Eqn
  q181 c4 = wlE 1329 (lit c4)
  q182 : Ws → Eqn
  q182 c4 = eqn (ℓ "亏乽") (ℓ "乽亏") (c₃ (Toffᵗ) (CX₀₁))
  q183 : Ws → Eqn
  q183 c4 = wpE 1186 c4
  q184 : Ws → Eqn
  q184 c4 = wpE 1187 c4
  q185 : Ws → Eqn
  q185 c4 = eqn (ℓ "亏丞") (ℓ "丞亏") (c₃ (Toffᵗ) (K))
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
  q193 c4 = sE 20 (lem-comm-CX40-CCZ123 c4)
  q194 : Ws → Eqn
  q194 c4 = wlE 1321 (lit c4)
  q195 : Ws → Eqn
  q195 c4 = wlE 763 (lit c4)
  q196 : Ws → Eqn
  q196 c4 = wpE 687 c4
  q197 : Ws → Eqn
  q197 c4 = wpE 161 c4

-- box-box-4 @0314203142: 103 steps
lem-box-box-4-at0314203142 : Ws → ⟪ (ℓ "佹佋") ⟫ʷ ≈ ⟪ (ℓ "佋佹") ⟫ʷ
lem-box-box-4-at0314203142 c4 = derive (ℓ "佹佋") (ℓ "佋佹")
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
  q198 c4 = sE 891 (lem-box-cP-at0310213442 c4)
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
  q204 c4 = sE 204 (lem-comm-CSd24-CCZ013 c4)
  q205 : Ws → Eqn
  q205 c4 = sE 194 (lem-comm-CS24-CCZ013 c4)
  q206 : Ws → Eqn
  q206 c4 = wlE 1204 (lit c4)
  q207 : Ws → Eqn
  q207 c4 = wlE 1644 (lit c4)
  q208 : Ws → Eqn
  q208 c4 = wlE 1645 (lit c4)

-- CSdu-box-3 @0310213442: 17 steps
lem-CSdu-box-3-at0310213442 : Ws → ⟪ (ℓ "乺佥") ⟫ʷ ≈ ⟪ (ℓ "佥乺") ⟫ʷ
lem-CSdu-box-3-at0310213442 c4 = derive (ℓ "乺佥") (ℓ "佥乺")
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
lem-CSu-box-3-at0310213442 : Ws → ⟪ (ℓ "乹佥") ⟫ʷ ≈ ⟪ (ℓ "佥乹") ⟫ʷ
lem-CSu-box-3-at0310213442 c4 = derive (ℓ "乹佥") (ℓ "佥乹")
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
  q213 c4 = sE 149 (lem-box-tQ-at0310213442 c4)
  q214 : Ws → Eqn
  q214 c4 = sE 917 (lem-t-cP-at0310213442 c4)

-- box2 @0310213442: 11 steps
lem-box2-at0310213442 : Ws → ⟪ (ℓ "佥佥") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at0310213442 c4 = derive (ℓ "佥佥") []
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
  q215 c4 = sE 956 (lem-sym-bc-at0210213443 c4)
  q216 : Ws → Eqn
  q216 c4 = sE 53 (lem-sym-ab-at0210243143 c4)

-- box-perm-3124 @0210213443: 2 steps
lem-box-perm-3124-at0210213443 : Ws → ⟪ (ℓ "伮") ⟫ʷ ≈ ⟪ (ℓ "佔") ⟫ʷ
lem-box-perm-3124-at0210213443 c4 = derive (ℓ "伮") (ℓ "佔")
  (rw 0 (q215 c4) ∷
   rw 0 (q216 c4) ∷ []) Eq.refl

private
  q217 : Ws → Eqn
  q217 c4 = sE 916 (lem-P-box-at04203243 c4)
  q218 : Ws → Eqn
  q218 c4 = sE 438 (lem-box-tQ-at0412233140 c4)

-- pairs @04203243: 4 steps
lem-pairs-at04203243 : Ws → ⟪ (ℓ "侒") ⟫ʷ ≈ ⟪ (ℓ "供") ⟫ʷ
lem-pairs-at04203243 c4 = derive (ℓ "侒") (ℓ "供")
  (rw⁻ 0 (q217 c4) ∷
   rw 1 (q67 c4) ∷
   rw 4 (q48 c4) ∷
   rw⁻ 0 (q218 c4) ∷ []) Eq.refl

private
  q219 : Ws → Eqn
  q219 c4 = sE 946 (lem-SWbc-box-at0412233140 c4)
  q220 : Ws → Eqn
  q220 c4 = sE 909 (lem-nat-SWbc-at0412233140 c4)

-- sym-bc @0412233140: 2 steps
lem-sym-bc-at0412233140 : Ws → ⟪ (ℓ "供") ⟫ʷ ≈ ⟪ (ℓ "侙") ⟫ʷ
lem-sym-bc-at0412233140 c4 = derive (ℓ "供") (ℓ "侙")
  (rw⁻ 0 (q219 c4) ∷
   rw 0 (q220 c4) ∷ []) Eq.refl

private
  q221 : Ws → Eqn
  q221 c4 = wpE 1437 c4
  q222 : Ws → Eqn
  q222 c4 = sE 927 (lem-QVQ-at0410233142 c4)
  q223 : Ws → Eqn
  q223 c4 = sE 442 (lem-tP-at0410233142 c4)

-- box-cP @0410233142: 12 steps
lem-box-cP-at0410233142 : Ws → ⟪ (ℓ "侐") ⟫ʷ ≈ ⟪ (ℓ "亠享亠享") ⟫ʷ
lem-box-cP-at0410233142 c4 = derive (ℓ "侐") (ℓ "亠享亠享")
  (re 0 1 (ℓ "亠亣仹亣亠仹") ∷
   re 2 1 (ℓ "五井仸井五仸") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw 2 (q221 c4) ∷
   re 5 1 (ℓ "五井仸井五仸") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw 5 (q221 c4) ∷
   rw 2 (q222 c4) ∷
   rw 1 (q223 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q224 : Ws → Eqn
  q224 c4 = sE 944 (lem-SWbc-box-at04122140 c4)
  q225 : Ws → Eqn
  q225 c4 = sE 907 (lem-nat-SWbc-at04122140 c4)

-- sym-bc @04122140: 2 steps
lem-sym-bc-at04122140 : Ws → ⟪ (ℓ "侙") ⟫ʷ ≈ ⟪ (ℓ "供") ⟫ʷ
lem-sym-bc-at04122140 c4 = derive (ℓ "侙") (ℓ "供")
  (rw⁻ 0 (q224 c4) ∷
   rw 0 (q225 c4) ∷ []) Eq.refl

private
  q226 : Ws → Eqn
  q226 c4 = wpE 1436 c4
  q227 : Ws → Eqn
  q227 c4 = sE 934 (lem-QVQ-at0412233140 c4)
  q228 : Ws → Eqn
  q228 c4 = sE 444 (lem-tP-at0412233140 c4)

-- box-cP @0412233140: 12 steps
lem-box-cP-at0412233140 : Ws → ⟪ (ℓ "供") ⟫ʷ ≈ ⟪ (ℓ "亰亗亰亗") ⟫ʷ
lem-box-cP-at0412233140 c4 = derive (ℓ "供") (ℓ "亰亗亰亗")
  (re 0 1 (ℓ "亰亳佛亳亰佛") ∷
   re 2 1 (ℓ "亨亪佚亪亨佚") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw⁻ 2 (q226 c4) ∷
   re 5 1 (ℓ "亨亪佚亪亨佚") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
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
lem-CSu-box-3-at04203243 : Ws → ⟪ (ℓ "乩侒") ⟫ʷ ≈ ⟪ (ℓ "侒乩") ⟫ʷ
lem-CSu-box-3-at04203243 c4 = derive (ℓ "乩侒") (ℓ "侒乩")
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
lem-CSdu-box-3-at04203243 : Ws → ⟪ (ℓ "乪侒") ⟫ʷ ≈ ⟪ (ℓ "侒乪") ⟫ʷ
lem-CSdu-box-3-at04203243 c4 = derive (ℓ "乪侒") (ℓ "侒乪")
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
  q241 c4 = sE 84 (lem-box-tQ-at04203243 c4)
  q242 : Ws → Eqn
  q242 c4 = wpE 306 c4
  q243 : Ws → Eqn
  q243 c4 = sE 918 (lem-t-cP-at04203243 c4)

-- box2 @04203243: 11 steps
lem-box2-at04203243 : Ws → ⟪ (ℓ "侒侒") ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-box2-at04203243 c4 = derive (ℓ "侒侒") []
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
  q244 c4 = sE 954 (lem-XCSX-box-2-at04122041 c4)
  q245 : Ws → Eqn
  q245 c4 = wpE 1476 c4
  q246 : Ws → Eqn
  q246 c4 = wpE 1477 c4
  q247 : Ws → Eqn
  q247 c4 = wpE 1478 c4
  q248 : Ws → Eqn
  q248 c4 = wpE 1281 c4

-- F4-S0-CS2 @0440: 13 steps
lem-F4-S0-CS2-at0440 : Ws → ⟪ (ℓ "与丽与俵") ⟫ʷ ≈ ⟪ (ℓ "俵与丽与") ⟫ʷ
lem-F4-S0-CS2-at0440 c4 = derive (ℓ "与丽与俵") (ℓ "俵与丽与")
  (re 3 1 (ℓ "侗互俳互俴") ∷
   re 5 1 (ℓ "乇") ∷
   re 7 1 (ℓ "么") ∷
   rw 0 (q244 c4) ∷
   rw⁻ 1 (q245 c4) ∷
   rw⁻ 2 (q246 c4) ∷
   rw⁻ 3 (q245 c4) ∷
   rw⁻ 4 (q247 c4) ∷
   re 2 1 (ℓ "俳") ∷
   re 4 1 (ℓ "俴") ∷
   re 0 5 (ℓ "俵") ∷
   rw⁻ 1 (q248 c4) ∷
   rw 1 (q248 c4) ∷ []) Eq.refl

private
  q249 : Ws → Eqn
  q249 c4 = wlE 756 (lit c4)
  q250 : Ws → Eqn
  q250 c4 = sE 936 (lem-QVQ-at0413203241 c4)
  q251 : Ws → Eqn
  q251 c4 = sE 445 (lem-tP-at0413203241 c4)

-- box-cP @0413203241: 12 steps
lem-box-cP-at0413203241 : Ws → ⟪ (ℓ "依") ⟫ʷ ≈ ⟪ (ℓ "亠享亠享") ⟫ʷ
lem-box-cP-at0413203241 c4 = derive (ℓ "依") (ℓ "亠享亠享")
  (re 0 1 (ℓ "亠亣侊亣亠侊") ∷
   re 2 1 (ℓ "亰亲侉亲亰侉") ∷
   re 4 1 (ℓ "乐") ∷
   re 7 1 (ℓ "乐") ∷
   rw⁻ 2 (q249 c4) ∷
   re 5 1 (ℓ "亰亲侉亲亰侉") ∷
   re 7 1 (ℓ "乐") ∷
   re 10 1 (ℓ "乐") ∷
   rw⁻ 5 (q249 c4) ∷
   rw 2 (q250 c4) ∷
   rw 1 (q251 c4) ∷
   rw 2 (q137 c4) ∷ []) Eq.refl

private
  q252 : Ws → Eqn
  q252 c4 = wpE 732 c4
  q253 : Ws → Eqn
  q253 c4 = sE 932 (lem-QVQ-at04122140 c4)
  q254 : Ws → Eqn
  q254 c4 = sE 443 (lem-tP-at04122140 c4)

-- box-cP @04122140: 12 steps
lem-box-cP-at04122140 : Ws → ⟪ (ℓ "侙") ⟫ʷ ≈ ⟪ (ℓ "亨亣亨亣") ⟫ʷ
lem-box-cP-at04122140 c4 = derive (ℓ "侙") (ℓ "亨亣亨亣")
  (re 0 1 (ℓ "亨享你享亨你") ∷
   re 2 1 (ℓ "亰亱佚亱亰佚") ∷
   re 4 1 (ℓ "丱") ∷
   re 7 1 (ℓ "丱") ∷
   rw⁻ 2 (q252 c4) ∷
   re 5 1 (ℓ "亰亱佚亱亰佚") ∷
   re 7 1 (ℓ "丱") ∷
   re 10 1 (ℓ "丱") ∷
   rw⁻ 5 (q252 c4) ∷
   rw 2 (q253 c4) ∷
   rw 1 (q254 c4) ∷
   rw 2 (q141 c4) ∷ []) Eq.refl

private
  q255 : Ws → Eqn
  q255 c4 = sE 950 (lem-SWbc-box-at04133140 c4)
  q256 : Ws → Eqn
  q256 c4 = sE 911 (lem-nat-SWbc-at04133140 c4)

-- sym-bc @04133140: 2 steps
lem-sym-bc-at04133140 : Ws → ⟪ (ℓ "侠") ⟫ʷ ≈ ⟪ (ℓ "侟") ⟫ʷ
lem-sym-bc-at04133140 c4 = derive (ℓ "侠") (ℓ "侟")
  (rw⁻ 0 (q255 c4) ∷
   rw 0 (q256 c4) ∷ []) Eq.refl

private
  q257 : Ws → Eqn
  q257 c4 = sE 949 (lem-SWbc-box-at0413213240 c4)
  q258 : Ws → Eqn
  q258 c4 = sE 910 (lem-nat-SWbc-at0413213240 c4)

-- sym-bc @0413213240: 2 steps
lem-sym-bc-at0413213240 : Ws → ⟪ (ℓ "侟") ⟫ʷ ≈ ⟪ (ℓ "侠") ⟫ʷ
lem-sym-bc-at0413213240 c4 = derive (ℓ "侟") (ℓ "侠")
  (rw⁻ 0 (q257 c4) ∷
   rw 0 (q258 c4) ∷ []) Eq.refl
