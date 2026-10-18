{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D014 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0006 ; wl0184 ; wl0190 ; wl0191 ; wl0192 ; wl0193 ; wl0194 ; wl0195 ; wl0196 ; wl0197 ; wl0206 ; wl0207 ; wl0214 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0256 ; wl0263 ; wl0325 ; wl0327 ; wl0432 ; wl0433 ; wl0445 ; wl0446 ; wl0447 ; wl0448 ; wl0449 ; wl0450 ; wl0451 ; wl0452 ; wl0499 ; wl0501 ; wl0519 ; wl0520 ; wl0521 ; wl0524 ; wl0677 ; wl0754 ; wl0778 ; wl0788 ; wl0808 ; wl0836 ; wl0838 ; wl0839 ; wl0840 ; wl0841 ; wl0871 ; wl0905 ; wl0906 ; wl0910 ; wl0930 ; wl0931 ; wl0960 ; wl1000 ; wl1051 ; wl1052 ; wl1053 ; wl1054 ; wl1055 ; wl1056 ; wl1057 ; wl1058 ; wl1059 ; wl1060 ; wl1061 ; wl1062 ; wl1063 ; wl1064 ; wl1065 ; wl1066 ; wl1067 ; wl1068 ; wl1069 ; wl1070 ; wl1071 ; wl1072 ; wl1073 ; wl1074 ; wl1075 ; wl1076 ; wl1077 ; wl1078 ; wl1079 ; wl1080 ; wl1081 ; wl1082 ; wl1083 ; wl1084 ; wl1085 ; wl1086 ; wl1087 ; wl1088 ; wl1089 ; wl1090 ; wl1091 ; wl1092 ; wl1093 ; wl1094 ; wl1095 ; wl1096 ; wl1097 ; wl1098 ; wl1099 ; wl1100 ; wl1101 ; wl1102 ; wl1103 ; wl1104 ; wl1105 ; wl1106 ; wl1107 ; wl1108 ; wl1109 ; wl1110 ; wl1111 ; wl1112 ; wl1113 ; wp0007 ; wp0019 ; wp0021 ; wp0032 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0039 ; wp0041 ; wp0042 ; wp0044 ; wp0053 ; wp0054 ; wp0055 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0068 ; wp0069 ; wp0070 ; wp0071 ; wp0072 ; wp0074 ; wp0090 ; wp0106 ; wp0107 ; wp0108 ; wp0122 ; wp0135 ; wp0161 ; wp0280 ; wp0294 ; wp0296 ; wp0298 ; wp0299 ; wp0300 ; wp0301 ; wp0302 ; wp0305 ; wp0312 ; wp0313 ; wp0314 ; wp0393 ; wp0617 ; wp0647 ; wp0651 ; wp0653 ; wp0655 ; wp0725 ; wp0743 ; wp0756 ; wp0785 ; wp0797 ; wp0850 ; wp0851 ; wp0852 ; wp0853 ; wp0854 ; wp0855 ; wp0856 ; wp0857 ; wp0858 ; wp0859 ; wp0860 ; wp0861 ; wp0862 ; wp0863 ; wp0864 ; wp0865 ; wp0866 ; wp0867 ; wp0868 ; wp0869 ; wp0870 ; wp0871 ; wp0872 ; wp0873 ; wp0874 ; wp0875 ; wp0876 ; wp0877 ; wp0878 ; wp0879 ; wp0880 ; wp0881 ; wp0882 ; wp0883 ; wp0884 ; wp0885 ; wp0886 ; wp0887 ; wp0888 ; wp0889 ; wp0890 ; wp0891 ; wp0892 ; wp0893 ; wp0894 ; wp0895 ; wp0896 ; wp0897 ; wp0898 ; wp0899 ; wp0900 ; wp0901 ; wp0902 ; wp0903 ; wp0904 ; wp0905)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-F5-01 ; lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-perm-1324 ; lem-box-tQ ; lem-box2 ; lem-box2-at0210243143 ; lem-box2-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at2332 ; lem-box-perm-3124 ; lem-box-tQ-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-box-tQ-at12233441)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-tQ-at0330 ; lem-cQ-at03102132)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-perm-2314-at03102132 ; lem-box-perm-3124-at0330 ; lem-sym-ab-at03102132 ; lem-sym-bc-at0330)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-CSu-box-2-at0210243143 ; lem-CSu-box-2-at122441 ; lem-CSu-box-2-at243243 ; lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-CKu-box-2-at0210243143 ; lem-CKu-box-2-at243243 ; lem-box-perm-1324-at0210243143 ; lem-box-perm-1324-at243243 ; lem-cQ-at0210213443)
open import Examples.Groups.Clifford+CS.Five.D.D008 using (lem-CKu-box-2-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-box-box-1-at03102132 ; lem-box-cP-at032032)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-F4-CS0-CS2)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-sym-ab-at132132 ; lem-sym-bc-at2332)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX04-TOFF213 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CX14-TOFF023 ; lem-comm-CX23-CCZ014)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS24-CCZ013 ; lem-comm-CS24-TOFF301 ; lem-comm-CSd24-CCZ013 ; lem-comm-CSd24-TOFF301)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CK41-TOFF023 ; lem-comm-CX04-TOFF312)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ034-CX12 ; lem-comm-SWAP12-BOX⟨3·04⟩)
-- F2-I-CS2: 13 steps
lem-F2-I-CS2 : Ws → ⟪ (S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S4 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ S4 ∷ []) (sym (wp0617 c4)) ▸
       at 1 2 (Toff013 ∷ S4 ∷ []) (wp0647 c4) ▸
       at 2 2 (CCZ024 ∷ S4 ∷ []) (sym (wp0617 c4)) ▸
       at 3 2 (Toff013 ∷ S4 ∷ []) (wp0647 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ S4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ S4 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 5 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ S4 ∷ []) (wl1051 (lit c4)) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-S0-S1: 1 steps
lem-F2-S0-S1 : Ws → ⟪ (CS04 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S1 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS14 ∷ []) (CS14 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS14 ∷ CS04 ∷ []) (wp0850 c4) ▸ done


-- F2-S0-S2: 1 steps
lem-F2-S0-S2 : Ws → ⟪ (CS04 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S2 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS24 ∷ []) (CS24 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS24 ∷ CS04 ∷ []) (wp0851 c4) ▸ done


-- F2-S0-S3: 1 steps
lem-F2-S0-S3 : Ws → ⟪ (CS04 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-S3 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS34 ∷ []) (CS34 ∷ CS04 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS04 ∷ []) (wp0852 c4) ▸ done


-- F2-S0-K1: 1 steps
lem-F2-S0-K1 : Ws → ⟪ (CS04 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K1 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK41 ∷ []) (CK41 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS04 ∷ []) (sym (wp0853 c4)) ▸ done


-- F2-S0-K2: 1 steps
lem-F2-S0-K2 : Ws → ⟪ (CS04 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K2 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK42 ∷ []) (CK42 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS04 ∷ []) (sym (wp0854 c4)) ▸ done


-- F2-S0-K3: 1 steps
lem-F2-S0-K3 : Ws → ⟪ (CS04 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-K3 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK43 ∷ []) (CK43 ∷ CS04 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS04 ∷ []) (sym (wp0855 c4)) ▸ done


-- F2-S0-CS1: 11 steps
lem-F2-S0-CS1 : Ws → ⟪ (CS04 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS04 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ CS04 ∷ []) (lem-CSu-box-2-at243243 c4) ▸
       at 1 2 (Toff324 ∷ CS04 ∷ []) (wp0393 c4) ▸
       at 2 2 (CS13 ∷ CS04 ∷ []) (wp0856 c4) ▸
       at 3 2 (Toff324 ∷ CS04 ∷ []) (wp0393 c4) ▸
       at 4 2 (CS13⁻ ∷ CS04 ∷ []) (wp0857 c4) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS04 ∷ []) (Sb0-1-42-3 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F2-S0-CS2: 11 steps
lem-F2-S0-CS2 : Ws → ⟪ (CS04 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS04 ∷ []) ⟫ʷ
lem-F2-S0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS04 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS04 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ CS04 ∷ []) (lem-CSu-box-2-at122441 c4) ▸
       at 1 2 (Toff134 ∷ CS04 ∷ []) (wp0858 c4) ▸
       at 2 2 (CS12 ∷ CS04 ∷ []) (wp0859 c4) ▸
       at 3 2 (Toff134 ∷ CS04 ∷ []) (wp0858 c4) ▸
       at 4 2 (CS12⁻ ∷ CS04 ∷ []) (wp0860 c4) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS04 ∷ []) (Sb0-2-43-1 ∷ CS04 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-S1-S2: 1 steps
lem-F2-S1-S2 : Ws → ⟪ (CS14 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-S2 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS24 ∷ []) (CS24 ∷ CS14 ∷ [])
  b0 = at 0 2 (CS24 ∷ CS14 ∷ []) (wl1052 (lit c4)) ▸ done


-- F2-S1-S3: 1 steps
lem-F2-S1-S3 : Ws → ⟪ (CS14 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-S3 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS34 ∷ []) (CS34 ∷ CS14 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS14 ∷ []) (wl1053 (lit c4)) ▸ done


-- F2-S1-K0: 1 steps
lem-F2-S1-K0 : Ws → ⟪ (CS14 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K0 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK40 ∷ []) (CK40 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS14 ∷ []) (sym (wp0861 c4)) ▸ done


-- F2-S1-K2: 1 steps
lem-F2-S1-K2 : Ws → ⟪ (CS14 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K2 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK42 ∷ []) (CK42 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS14 ∷ []) (sym (wl1054 (lit c4))) ▸ done


-- F2-S1-K3: 1 steps
lem-F2-S1-K3 : Ws → ⟪ (CS14 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-K3 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK43 ∷ []) (CK43 ∷ CS14 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS14 ∷ []) (sym (wl1055 (lit c4))) ▸ done


-- F2-S1-CS2: 13 steps
lem-F2-S1-CS2 : Ws → ⟪ (CS14 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS14 ∷ []) ⟫ʷ
lem-F2-S1-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS14 ∷ Sb0-2-43-1 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS14 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 1 2 (Toff013 ∷ CS14 ∷ []) (wp0785 c4) ▸
       at 2 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 3 2 (Toff013 ∷ CS14 ∷ []) (wp0785 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS14 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Sb0-2-43-1 ∷ CS14 ∷ [])
  b1 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 5 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS14 ∷ []) (wl1056 (lit c4)) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-S2-S3: 1 steps
lem-F2-S2-S3 : Ws → ⟪ (CS24 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-S3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS34 ∷ []) (CS34 ∷ CS24 ∷ [])
  b0 = at 0 2 (CS34 ∷ CS24 ∷ []) (wl1057 (lit c4)) ▸ done


-- F2-S2-K0: 1 steps
lem-F2-S2-K0 : Ws → ⟪ (CS24 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K0 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK40 ∷ []) (CK40 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS24 ∷ []) (sym (wp0862 c4)) ▸ done


-- F2-S2-K1: 1 steps
lem-F2-S2-K1 : Ws → ⟪ (CS24 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K1 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK41 ∷ []) (CK41 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS24 ∷ []) (sym (wl1058 (lit c4))) ▸ done


-- F2-S2-K3: 1 steps
lem-F2-S2-K3 : Ws → ⟪ (CS24 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-K3 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK43 ∷ []) (CK43 ∷ CS24 ∷ [])
  b0 = at 0 2 (CK43 ∷ CS24 ∷ []) (sym (wl1059 (lit c4))) ▸ done


-- F2-S2-CS0: 11 steps
lem-F2-S2-CS0 : Ws → ⟪ (CS24 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS24 ∷ []) ⟫ʷ
lem-F2-S2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS24 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS24 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CS24 ∷ []) (lem-CSu-box-2-at0210243143 c4) ▸
       at 1 2 (Toff314 ∷ CS24 ∷ []) (wl0754 (lit c4)) ▸
       at 2 2 (CS03 ∷ CS24 ∷ []) (sym (wp0863 c4)) ▸
       at 3 2 (Toff314 ∷ CS24 ∷ []) (wl0754 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ CS24 ∷ []) (sym (wp0864 c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS24 ∷ []) (Sb2-0-41-3 ∷ CS24 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F2-S3-K0: 1 steps
lem-F2-S3-K0 : Ws → ⟪ (CS34 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K0 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK40 ∷ []) (CK40 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK40 ∷ CS34 ∷ []) (sym (wp0865 c4)) ▸ done


-- F2-S3-K1: 1 steps
lem-F2-S3-K1 : Ws → ⟪ (CS34 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K1 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK41 ∷ []) (CK41 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK41 ∷ CS34 ∷ []) (sym (wl1060 (lit c4))) ▸ done


-- F2-S3-K2: 1 steps
lem-F2-S3-K2 : Ws → ⟪ (CS34 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-K2 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK42 ∷ []) (CK42 ∷ CS34 ∷ [])
  b0 = at 0 2 (CK42 ∷ CS34 ∷ []) (sym (wl1061 (lit c4))) ▸ done


-- F2-S3-CS0: 13 steps
lem-F2-S3-CS0 : Ws → ⟪ (CS34 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS34 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 1 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS34 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ CS34 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 5 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS34 ∷ []) (wp0866 c4) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F2-S3-CS1: 13 steps
lem-F2-S3-CS1 : Ws → ⟪ (CS34 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CS34 ∷ []) ⟫ʷ
lem-F2-S3-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CS34 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 1 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸
       at 2 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 3 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ CS34 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 5 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CS34 ∷ []) (wl1062 (lit c4)) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F2-K0-K1: 1 steps
lem-F2-K0-K1 : Ws → ⟪ (CK40 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K1 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK41 ∷ []) (CK41 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK41 ∷ CK40 ∷ []) (wp0867 c4) ▸ done


-- F2-K0-K2: 1 steps
lem-F2-K0-K2 : Ws → ⟪ (CK40 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K2 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK42 ∷ []) (CK42 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK42 ∷ CK40 ∷ []) (wp0868 c4) ▸ done


-- F2-K0-K3: 1 steps
lem-F2-K0-K3 : Ws → ⟪ (CK40 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-K3 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK43 ∷ []) (CK43 ∷ CK40 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK40 ∷ []) (wp0869 c4) ▸ done


-- F2-K0-CS1: 11 steps
lem-F2-K0-CS1 : Ws → ⟪ (CK40 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK40 ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-1423 ∷ CK40 ∷ []) (lem-CKu-box-2-at243243 c4) ▸
       at 1 2 (Toff324 ∷ CK40 ∷ []) (wp0870 c4) ▸
       at 2 2 (CS13 ∷ CK40 ∷ []) (wp0871 c4) ▸
       at 3 2 (Toff324 ∷ CK40 ∷ []) (wp0870 c4) ▸
       at 4 2 (CS13⁻ ∷ CK40 ∷ []) (wp0872 c4) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK40 ∷ []) (Sb0-1-42-3 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F2-K0-CS2: 11 steps
lem-F2-K0-CS2 : Ws → ⟪ (CK40 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK40 ∷ []) ⟫ʷ
lem-F2-K0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK40 ∷ Sb0-2-43-1 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK40 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ CK40 ∷ []) (lem-CKu-box-2-at122441 c4) ▸
       at 1 2 (Toff134 ∷ CK40 ∷ []) (wp0873 c4) ▸
       at 2 2 (CS12 ∷ CK40 ∷ []) (wp0874 c4) ▸
       at 3 2 (Toff134 ∷ CK40 ∷ []) (wp0873 c4) ▸
       at 4 2 (CS12⁻ ∷ CK40 ∷ []) (wp0875 c4) ▸ done

  b1 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK40 ∷ []) (Sb0-2-43-1 ∷ CK40 ∷ [])
  b1 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-K1-K2: 1 steps
lem-F2-K1-K2 : Ws → ⟪ (CK41 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-K2 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK42 ∷ []) (CK42 ∷ CK41 ∷ [])
  b0 = at 0 2 (CK42 ∷ CK41 ∷ []) (wl1063 (lit c4)) ▸ done


-- F2-K1-K3: 1 steps
lem-F2-K1-K3 : Ws → ⟪ (CK41 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-K3 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK43 ∷ []) (CK43 ∷ CK41 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK41 ∷ []) (wl1064 (lit c4)) ▸ done


-- F2-K1-CS2: 35 steps
lem-F2-K1-CS2 : Ws → ⟪ (CK41 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CK41 ∷ []) ⟫ʷ
lem-F2-K1-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK41 ∷ Sb0-2-43-1 ∷ []) (Toff023 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 0 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (sym (wp0876 c4)) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 3 2 (Toff023 ∷ CK41 ∷ []) (lem-comm-CK41-TOFF023 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 11 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 10 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 9 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 7 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 8 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 6 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ []) (sym (wp0876 c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b3 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ [])
  b3 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 6 4 (CZ01 ∷ CK41 ∷ []) (wp0877 c4) ▸
       at 4 3 (CCZ123 ∷ []) (sym (wl1065 (lit c4))) ▸
       at 0 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸
       at 0 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 7 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) (wl1066 (lit c4)) ▸ done

  b4 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK41 ∷ []) (Sb0-2-43-1 ∷ CK41 ∷ [])
  b4 = at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-K2-K3: 1 steps
lem-F2-K2-K3 : Ws → ⟪ (CK42 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2-K3 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK43 ∷ []) (CK43 ∷ CK42 ∷ [])
  b0 = at 0 2 (CK43 ∷ CK42 ∷ []) (wl1067 (lit c4)) ▸ done


-- F2-K2-CS0: 11 steps
lem-F2-K2-CS0 : Ws → ⟪ (CK42 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK42 ∷ []) ⟫ʷ
lem-F2-K2-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CK42 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK42 ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 (Bx2-0413 ∷ CK42 ∷ []) (lem-CKu-box-2-at0210243143 c4) ▸
       at 1 2 (Toff314 ∷ CK42 ∷ []) (wl1068 (lit c4)) ▸
       at 2 2 (CS03 ∷ CK42 ∷ []) (wp0878 c4) ▸
       at 3 2 (Toff314 ∷ CK42 ∷ []) (wl1068 (lit c4)) ▸
       at 4 2 (CS03⁻ ∷ CK42 ∷ []) (wp0879 c4) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK42 ∷ []) (Sb2-0-41-3 ∷ CK42 ∷ [])
  b1 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- box-tQ @0210213443: 13 steps
lem-box-tQ-at0210213443 : Ws → ⟪ (Bx2-0143 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0210213443 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0143 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-243 ∷ Toff201 ∷ CCZ012 ∷ Bx0-243 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 5 1 (CCZ024 ∷ Toff024 ∷ Bx2-03 ∷ Toff024 ∷ CCZ024 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ024 ∷ Toff024 ∷ CZ03 ∷ Toff024 ∷ CCZ024 ∷ CZ03 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0305 c4) ▸
       at 0 2 (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (wl0930 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0210213443 c4) ▸
       at 2 4 (Toff201 ∷ []) (wl0931 (lit c4)) ▸ done


-- F2-K3-CS0: 35 steps
lem-F2-K3-CS0 : Ws → ⟪ (CK43 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK43 ∷ Sb2-0-41-3 ∷ []) (Toff201 ∷ CCZ234 ∷ CZ23 ∷ CK43 ∷ Toff201 ∷ CZ23 ∷ CCZ013 ∷ CCZ234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (Bx2-0143 ∷ []) (lem-box-perm-1324-at0210243143 c4) ▸
       at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0210213443 c4) ▸
       at 0 2 (Toff201 ∷ CK43 ∷ []) (sym (c₃ (Toffᵗ) (CK₁₀))) ▸
       at 1 2 (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) (sym (wl1069 (lit c4))) ▸
       at 4 2 (Toff201 ∷ CZ23 ∷ CCZ013 ∷ []) (wl1070 (lit c4)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CZ23 ∷ CK43 ∷ Toff201 ∷ CZ23 ∷ CCZ013 ∷ CCZ234 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CZ23 ∷ CCZ013 ∷ CK43 ∷ CZ23 ∷ CCZ234 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 3 2 (Toff201 ∷ CK43 ∷ []) (sym (c₃ (Toffᵗ) (CK₁₀))) ▸
       at 2 2 (Toff201 ∷ CZ23 ∷ CCZ013 ∷ []) (wl1070 (lit c4)) ▸
       at 7 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 11 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 10 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 9 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 7 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CZ23 ∷ CCZ013 ∷ CK43 ∷ CZ23 ∷ CCZ234 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CZ23 ∷ CS13 ∷ CCZ234 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ CZ23 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 8 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CZ23 ∷ []) (sym (wl1071 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ []) (sym (wl1069 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 8 2 (CCZ234 ∷ CS03 ∷ []) (sym (wp0294 c4)) ▸
       at 7 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 6 2 (CCZ234 ∷ CS13⁻ ∷ []) (sym (wl0432 (lit c4))) ▸
       at 5 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b3 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CZ23 ∷ CS13 ∷ CCZ234 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CZ23 ∷ CK43 ∷ CZ23 ∷ CZ23 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ [])
  b3 = at 4 2 (CCZ234 ∷ CS13 ∷ []) (sym (wl0433 (lit c4))) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CZ23 ∷ []) (sym (wl1071 (lit c4))) ▸
       at 6 4 (CZ23 ∷ CK43 ∷ []) (wl1072 (lit c4)) ▸
       at 4 3 (CCZ013 ∷ []) (sym (wl1073 (lit c4))) ▸
       at 0 4 (Bx2-0143 ∷ []) (sym (lem-box-tQ-at0210213443 c4)) ▸
       at 0 1 (Bx2-0413 ∷ []) (sym (lem-box-perm-1324-at0210243143 c4)) ▸
       at 1 7 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) (wp0880 c4) ▸ done

  b4 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CK43 ∷ []) (Sb2-0-41-3 ∷ CK43 ∷ [])
  b4 = at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F2-K3-CS1: 35 steps
lem-F2-K3-CS1 : Ws → ⟪ (CK43 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ CK43 ∷ []) ⟫ʷ
lem-F2-K3-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (run b4))))
  where
  b0 : Chain (CK43 ∷ Sb0-1-42-3 ∷ []) (Toff012 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ Toff012 ∷ CZ03 ∷ CCZ123 ∷ CCZ034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ-at3443 c4) ▸
       at 0 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 1 2 (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) (sym (wp0881 c4)) ▸
       at 4 2 (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) (wl1074 (lit c4)) ▸ done

  b1 : Chain (Toff012 ∷ CCZ034 ∷ CZ03 ∷ CK43 ∷ Toff012 ∷ CZ03 ∷ CCZ123 ∷ CCZ034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CZ03 ∷ CCZ123 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 3 2 (Toff012 ∷ CK43 ∷ []) (sym (c₃ (Toff) (CK₁₀))) ▸
       at 2 2 (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) (wl1074 (lit c4)) ▸
       at 7 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 11 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 10 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸ done

  b2 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CZ03 ∷ CCZ123 ∷ CK43 ∷ CZ03 ∷ CCZ034 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CZ03 ∷ CS23 ∷ CCZ034 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 8 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 6 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 5 2 (CCZ034 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ []) (sym (wp0881 c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b3 : Chain (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CZ03 ∷ CS23 ∷ CCZ034 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CZ03 ∷ CK43 ∷ CZ03 ∷ CZ03 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ [])
  b3 = at 4 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 6 4 (CZ03 ∷ CK43 ∷ []) (wp0882 c4) ▸
       at 4 3 (CCZ123 ∷ []) (sym (wl1075 (lit c4))) ▸
       at 0 4 (Bx0-1243 ∷ []) (sym (lem-box-tQ-at3443 c4)) ▸
       at 0 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 1 7 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ []) (wl1076 (lit c4)) ▸ done

  b4 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK43 ∷ []) (Sb0-1-42-3 ∷ CK43 ∷ [])
  b4 = at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- inv-SBOX(2;0;41;3): 30 steps
lem-inv-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-inv-SBOX⟨2·0·41·3⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ [])
  b0 = at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 4 2 [] (wl1077 (lit c4)) ▸
       at 3 2 [] (wl0788 (lit c4)) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 3 1 (CS03⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CS03⁻ ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 2 2 [] (wl1078 (lit c4)) ▸
       at 1 2 [] (wl0788 (lit c4)) ▸
       at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 6 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 5 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 11 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ [])
  b2 = at 11 1 (CZ03 ∷ []) (refl) ▸
       at 14 1 (CZ03 ∷ []) (refl) ▸
       at 5 12 [] (wl1079 (lit c4)) ▸
       at 4 2 [] (wp0135 c4) ▸
       at 3 2 [] (wp0019 c4) ▸
       at 2 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸ done

  b3 : Chain (CCZ024 ∷ Toff204 ∷ CCZ012 ∷ Toff012 ∷ CZ03 ∷ Toff012 ∷ CCZ012 ∷ CZ03 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) []
  b3 = at 8 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 8 1 (CZ03 ∷ []) (refl) ▸
       at 11 1 (CZ03 ∷ []) (refl) ▸
       at 2 12 [] (wl1079 (lit c4)) ▸
       at 1 2 [] (wp0019 c4) ▸
       at 0 2 [] (wp0135 c4) ▸ done


-- invr-SBOX(2;0;41;3): 30 steps
lem-invr-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-invr-SBOX⟨2·0·41·3⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (run b3)))
  where
  b0 : Chain (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b0 = at 0 1 (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-0413 ∷ []) (refl) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ Bx⁻0-213 ∷ Toff204 ∷ CCZ024 ∷ []) (refl) ▸
       at 10 1 (CCZ024 ∷ Toff204 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ []) (refl) ▸
       at 9 2 [] (wp0135 c4) ▸
       at 8 2 [] (wp0019 c4) ▸
       at 7 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻0-213 ∷ CCZ024 ∷ Toff204 ∷ CZ03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff204 ∷ CCZ024 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b1 = at 10 1 (CZ03 ∷ []) (refl) ▸
       at 13 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 18 1 (CZ03 ∷ []) (refl) ▸
       at 7 12 [] (wl1080 (lit c4)) ▸
       at 6 2 [] (wp0019 c4) ▸
       at 5 2 [] (wp0135 c4) ▸
       at 4 1 (Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ []) (refl) ▸ done

  b2 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ Toff314 ∷ Bx⁻2-03 ∷ CCZ012 ∷ Toff012 ∷ Bx⁻2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx0-213 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ [])
  b2 = at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CCZ012 ∷ Toff012 ∷ Bx2-03 ∷ Toff012 ∷ CCZ012 ∷ Bx2-03 ∷ []) (refl) ▸
       at 12 1 (CZ03 ∷ []) (refl) ▸
       at 15 1 (CZ03 ∷ []) (refl) ▸
       at 4 12 [] (wl1080 (lit c4)) ▸
       at 3 2 [] (wl0788 (lit c4)) ▸
       at 2 1 (CS03⁻ ∷ []) (refl) ▸ done

  b3 : Chain (Sb2-0-3-1 ∷ Toff314 ∷ CS03⁻ ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) []
  b3 = at 3 1 (CS03 ∷ []) (refl) ▸
       at 2 2 [] (wl1077 (lit c4)) ▸
       at 1 2 [] (wl0788 (lit c4)) ▸
       at 0 1 (CS03 ∷ []) (refl) ▸
       at 1 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 2 [] (wl1078 (lit c4)) ▸ done


-- CSu-box-4 @122441: 17 steps
lem-CSu-box-4-at122441 : Ws → ⟪ (CS01 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS01 ∷ []) ⟫ʷ
lem-CSu-box-4-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS01 ∷ Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CS01 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 1 2 (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ []) (wl1081 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 7 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CS01 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS01 ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 5 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (wl0906 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CS13 ∷ []) (wl0910 (lit c4)) ▸
       at 3 2 (Toff013 ∷ CS01 ∷ CS13 ∷ CCZ013 ∷ []) (wl1081 (lit c4)) ▸
       at 4 6 (CS01 ∷ []) (wl1082 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS01 ∷ []) (Bx0-2431 ∷ CS01 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- AX-S23: 8 steps
lem-AX-S23 : Ws → ⟪ (CS01 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ CS01 ∷ []) ⟫ʷ
lem-AX-S23 c4 = run b0
  where
  b0 : Chain (CS01 ∷ Sb0-2-43-1 ∷ []) (Sb0-2-43-1 ∷ CS01 ∷ [])
  b0 = at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 2 (Bx0-2431 ∷ CS01 ∷ []) (lem-CSu-box-4-at122441 c4) ▸
       at 1 5 (Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS01 ∷ []) (axAX) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-CS0-CS2: 16 steps
lem-F2-CS0-CS2 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ
lem-F2-CS0-CS2 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CS01 ∷ [])
  b0 = at 0 0 (X4 ∷ X4 ∷ []) (sym (wl1083 (lit c4))) ▸
       at 1 0 (Sb⁻2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (sym (lem-invr-SBOX⟨2·0·41·3⟩ c4)) ▸
       at 2 0 (X4 ∷ X4 ∷ []) (sym (wl1083 (lit c4))) ▸
       at 3 4 (CS01 ∷ []) (lem-F5-01 c4) ▸
       at 3 2 (Sb0-2-43-1 ∷ CS01 ∷ []) (lem-AX-S23 c4) ▸
       at 4 0 (X4 ∷ X4 ∷ []) (sym (wl1083 (lit c4))) ▸
       at 5 0 (Sb2-0-41-3 ∷ Sb⁻2-0-41-3 ∷ []) (sym (lem-inv-SBOX⟨2·0·41·3⟩ c4)) ▸
       at 6 0 (X4 ∷ X4 ∷ []) (sym (wl1083 (lit c4))) ▸ done

  b1 : Chain (X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ X4 ∷ Sb⁻2-0-41-3 ∷ X4 ∷ CS01 ∷ []) (Sb0-2-43-1 ∷ Sb2-0-41-3 ∷ [])
  b1 = at 3 4 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (sym (lem-F4-CS0-CS2 c4)) ▸
       at 2 2 [] (wl1083 (lit c4)) ▸
       at 1 2 [] (lem-invr-SBOX⟨2·0·41·3⟩ c4) ▸
       at 0 2 [] (wl1083 (lit c4)) ▸
       at 4 1 (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (sym (lem-F5-01 c4)) ▸
       at 3 2 [] (wl1083 (lit c4)) ▸
       at 2 2 [] (lem-invr-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 [] (wl1083 (lit c4)) ▸ done


-- box-perm-1324 @0330: 1 steps
lem-box-perm-1324-at0330 : Ws → ⟪ (Bx3-1204 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-1324-at0330 c4 = run b0
  where
  b0 : Chain (Bx3-1204 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-bc-at0330 c4) ▸ done


-- box-perm-2314 @132132: 2 steps
lem-box-perm-2314-at132132 : Ws → ⟪ (Bx0-3124 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-2314-at132132 c4 = run b0
  where
  b0 : Chain (Bx0-3124 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1324 ∷ []) (lem-sym-ab-at132132 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-bc-at2332 c4) ▸ done


-- Tu-box: 83 steps
lem-Tu-box : Ws → ⟪ (Toff301 ∷ Bx0-1234 ∷ Toff301 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ Bx3-1204 ∷ []) ⟫ʷ
lem-Tu-box c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Toff301 ∷ Bx0-1234 ∷ Toff301 ∷ []) (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff012 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ CCZ014 ∷ [])
  b0 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 0 2 (Toff012 ∷ Toff312 ∷ Toff301 ∷ []) (sym (wl1084 (lit c4))) ▸
       at 2 2 (CCZ034 ∷ CCZ014 ∷ Toff301 ∷ []) (sym (wp0883 c4)) ▸
       at 4 2 (Toff012 ∷ Toff312 ∷ Toff301 ∷ []) (sym (wl1084 (lit c4))) ▸
       at 6 3 (CCZ034 ∷ CCZ014 ∷ []) (sym (wp0884 c4)) ▸
       at 3 2 (Toff012 ∷ CCZ014 ∷ CCZ124 ∷ []) (wp0122 c4) ▸
       at 5 2 (Toff312 ∷ CCZ124 ∷ []) (wl0871 (lit c4)) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b1 : Chain (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff012 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ CCZ014 ∷ []) (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff012 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ [])
  b1 = at 8 2 (Toff312 ∷ CS01 ∷ []) (wl0501 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS14⁻ ∷ []) (wl0778 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS14 ∷ []) (wl0499 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 5 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 3 (CCZ034 ∷ []) (wp0885 c4) ▸ done

  b2 : Chain (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff012 ∷ Toff312 ∷ CCZ124 ∷ CCZ034 ∷ []) (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b2 = at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 9 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff312 ∷ Toff012 ∷ []) (wl1085 (lit c4)) ▸ done

  b3 : Chain (Toff012 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b3 = at 4 0 (CCZ034 ∷ CCZ034 ∷ []) (sym (wp0007 c4)) ▸
       at 1 4 (Bx3-1204 ∷ []) (sym (lem-box-tQ-at0330 c4)) ▸
       at 1 1 (Bx3-1024 ∷ []) (lem-box-perm-1324-at0330 c4) ▸
       at 1 1 (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff324 ∷ []) (lem-box-cP-at032032 c4) ▸
       at 0 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸
       at 2 2 (Toff324 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0445 (lit c4)) ▸
       at 1 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 7 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸ done

  b4 : Chain (CCZ013 ∷ K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ K0⁻ ∷ CCZ123 ∷ CCZ124 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b4 = at 6 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 4 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 3 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 2 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 1 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 2 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸ done

  b5 : Chain (CCZ013 ∷ Toff324 ∷ Toff012 ∷ CCZ123 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ013 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff012 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b5 = at 8 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸
       at 5 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CCZ123 ∷ []) (sym (wl0327 (lit c4))) ▸
       at 2 2 (CCZ013 ∷ Toff012 ∷ CCZ123 ∷ []) (sym (wl0325 (lit c4))) ▸ done

  b6 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ Toff012 ∷ CCZ123 ∷ CCZ123 ∷ CCZ124 ∷ Toff324 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ Toff324 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b6 = at 3 3 (Toff012 ∷ []) (wl0449 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CCZ124 ∷ []) (wl0450 (lit c4)) ▸
       at 3 1 (K0 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wl0446 (lit c4))) ▸
       at 9 2 (Toff324 ∷ K0⁻ ∷ []) (c₁ (K • iI) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 8 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 7 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 6 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸ done

  b7 : Chain (CCZ013 ∷ Toff324 ∷ CCZ013 ∷ K0 ∷ CS12 ∷ Toff324 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (Bx3-1204 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ [])
  b7 = at 4 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 3 2 (Toff324 ∷ K0 ∷ []) (c₁ (K) ((K ↑ • CCZ • K ↑ • iI) ↑)) ▸
       at 4 7 (Toff012 ∷ []) (wl0446 (lit c4)) ▸
       at 0 4 (Bx3-1024 ∷ []) (sym (lem-box-cP-at032032 c4)) ▸
       at 0 1 (Bx3-1204 ∷ []) (sym (lem-box-perm-1324-at0330 c4)) ▸
       at 2 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 6 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b8 : Chain (Bx3-1204 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ []) (Bx3-1204 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CCZ124 ∷ [])
  b8 = at 4 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (Toff012 ∷ CCZ124 ∷ []) (wp0300 c4) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS14 ∷ []) (sym (wp0106 c4)) ▸
       at 7 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸ done

  b9 : Chain (Bx3-1204 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ CCZ124 ∷ []) (Bx3-0124 ∷ Bx0-3124 ∷ [])
  b9 = at 6 2 (CCZ034 ∷ CS24⁻ ∷ []) (sym (wp0107 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS24 ∷ []) (sym (wp0108 c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 2 [] (wl0263 (lit c4)) ▸
       at 1 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸
       at 0 1 (Bx3-0124 ∷ []) (lem-box-perm-3124-at0330 c4) ▸
       at 1 1 (Bx0-3124 ∷ []) (lem-box-perm-3124 c4) ▸ done

  b10 : Chain (Bx3-0124 ∷ Bx0-3124 ∷ []) (Bx0-1234 ∷ Bx3-1204 ∷ [])
  b10 = at 0 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-box-perm-2314-at132132 c4) ▸
       at 1 1 (Bx3-1204 ∷ []) (lem-box-perm-2314-at03102132 c4) ▸ done


-- Xb-box @2332: 18 steps
lem-Xb-box-at2332 : Ws → ⟪ (X3 ∷ Bx0-1324 ∷ X3 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1324 ∷ CCZ124 ∷ []) ⟫ʷ
lem-Xb-box-at2332 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X3 ∷ Bx0-1324 ∷ X3 ∷ []) (CCZ013 ∷ Toff024 ∷ X3 ∷ CZ01 ∷ CS24 ∷ CX12 ∷ CCZ013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff024 ∷ X3 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ []) (lem-box-cP-at2332 c4) ▸
       at 0 2 (CCZ013 ∷ X3 ∷ CZ01 ∷ []) (sym (wl1086 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CZ01 ∷ CCZ124 ∷ []) (wp0886 c4) ▸
       at 1 2 (Toff024 ∷ X3 ∷ []) (sym (wp0887 c4)) ▸
       at 4 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CCZ013 ∷ CS14 ∷ []) (sym (wp0299 c4)) ▸
       at 7 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 6 2 (CCZ013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-CCZ013 (lit c4)) ▸ done

  b1 : Chain (CCZ013 ∷ Toff024 ∷ X3 ∷ CZ01 ∷ CS24 ∷ CX12 ∷ CCZ013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff024 ∷ X3 ∷ []) (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ X3 ∷ CCZ124 ∷ X3 ∷ [])
  b1 = at 5 2 (CCZ013 ∷ CX12 ∷ []) (sym (wl0448 (lit c4))) ▸
       at 4 2 (CCZ013 ∷ CS24 ∷ []) (lem-comm-CS24-CCZ013 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (CCZ013 ∷ CZ01 ∷ []) (sym (wl1087 (lit c4))) ▸
       at 2 2 (CCZ013 ∷ X3 ∷ CZ01 ∷ []) (sym (wl1086 (lit c4))) ▸
       at 3 3 (X3 ∷ []) (wl1088 (lit c4)) ▸
       at 4 2 (Toff024 ∷ CCZ124 ∷ []) (wp0743 c4) ▸
       at 3 2 (Toff024 ∷ X3 ∷ []) (sym (wp0887 c4)) ▸ done

  b2 : Chain (CCZ013 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ X3 ∷ CCZ124 ∷ X3 ∷ []) (Bx0-1324 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-1324 ∷ []) (sym (lem-box-cP-at2332 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl1089 (lit c4))) ▸ done


-- box-perm-1324 @2332: 1 steps
lem-box-perm-1324-at2332 : Ws → ⟪ (Bx0-1324 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1324-at2332 c4 = run b0
  where
  b0 : Chain (Bx0-1324 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-sym-bc-at2332 c4) ▸ done


-- CKc-box: 61 steps
lem-CKc-box : Ws → ⟪ (Bx0-1234 ∷ CK34 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK34 ∷ CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-CKc-box c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-1234 ∷ CK34 ∷ []) (X3 ∷ Bx0-1234 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ CCZ124 ∷ [])
  b0 = at 1 0 (CCZ124 ∷ CCZ124 ∷ []) (sym (wl0263 (lit c4))) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-box-perm-1324 c4) ▸
       at 0 2 (X3 ∷ Bx0-1324 ∷ X3 ∷ []) (sym (lem-Xb-box-at2332 c4)) ▸
       at 3 2 (CCZ124 ∷ CK34 ∷ CCZ124 ∷ CCZ124 ∷ []) (sym (wl1090 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ X3 ∷ []) (sym (wl1091 (lit c4))) ▸
       at 3 2 (K4 ∷ CK34 ∷ S3 ∷ X3 ∷ []) (sym (wl1092 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ X3 ∷ []) (sym (wl1091 (lit c4))) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-1324-at2332 c4) ▸ done

  b1 : Chain (X3 ∷ Bx0-1234 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ CCZ124 ∷ [])
  b1 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 4 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

  b2 : Chain (X3 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ X3 ∷ CCZ124 ∷ [])
  b2 = at 5 2 (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0888 c4) ▸
       at 8 2 (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ []) (wp0889 c4) ▸
       at 11 2 (S3 ∷ CCZ034 ∷ []) (wp0890 c4) ▸
       at 13 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b3 : Chain (X3 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ [])
  b3 = at 16 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 12 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 7 (K4 ∷ CK34 ∷ S3 ∷ []) (sym (wp0891 c4)) ▸
       at 3 2 (CCZ124 ∷ Toff012 ∷ []) (sym (wp0300 c4)) ▸
       at 4 2 (K4 ∷ Toff012 ∷ []) (c₃ (Toff) (K ↑)) ▸
       at 5 2 (CK34 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₀₁)) ▸
       at 6 2 (S3 ∷ Toff012 ∷ []) (c₃ (Toff) (S)) ▸
       at 7 2 (CCZ124 ∷ Toff012 ∷ []) (sym (wp0300 c4)) ▸ done

  b4 : Chain (X3 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ [])
  b4 = at 3 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 2 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 3 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 4 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 2 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0888 c4) ▸ done

  b5 : Chain (X3 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ [])
  b5 = at 6 2 (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ []) (wp0889 c4) ▸
       at 9 2 (S3 ∷ CCZ034 ∷ []) (wp0890 c4) ▸
       at 11 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b6 : Chain (X3 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ S3 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ Bx0-1234 ∷ X3 ∷ CCZ124 ∷ [])
  b6 = at 10 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 7 (K4 ∷ CK34 ∷ S3 ∷ []) (sym (wp0891 c4)) ▸
       at 1 2 (CCZ124 ∷ Toff012 ∷ []) (sym (wp0300 c4)) ▸
       at 2 2 (K4 ∷ Toff012 ∷ []) (c₃ (Toff) (K ↑)) ▸
       at 3 2 (CK34 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₀₁)) ▸
       at 4 2 (S3 ∷ Toff012 ∷ []) (c₃ (Toff) (S)) ▸
       at 5 2 (CCZ124 ∷ Toff012 ∷ []) (sym (wp0300 c4)) ▸
       at 6 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

  b7 : Chain (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ Bx0-1234 ∷ X3 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK34 ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b7 = at 6 1 (Bx0-1324 ∷ []) (sym (lem-box-perm-1324-at2332 c4)) ▸
       at 0 6 (CCZ124 ∷ CK34 ∷ CCZ124 ∷ X3 ∷ []) (sym (wl1093 (lit c4))) ▸
       at 3 3 (Bx0-1324 ∷ CCZ124 ∷ []) (lem-Xb-box-at2332 c4) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-box-perm-1324-at2332 c4) ▸ done


-- CKc-boxL: 3 steps
lem-CKc-boxL : Ws → ⟪ (CK34 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ CK34 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CKc-boxL c4 = run b0
  where
  b0 : Chain (CK34 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ CK34 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Bx0-1234 ∷ Bx0-1234 ∷ []) (sym (lem-box2 c4)) ▸
       at 1 2 (CCZ124 ∷ CK34 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (lem-CKc-box c4) ▸
       at 4 2 [] (lem-box2 c4) ▸ done


-- CKdc-box: 63 steps
lem-CKdc-box : Ws → ⟪ (Bx0-1234 ∷ CK34⁻ ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ Bx0-1234 ∷ []) ⟫ʷ
lem-CKdc-box c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-1234 ∷ CK34⁻ ∷ []) (X3 ∷ Bx0-1234 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι ∷ CCZ124 ∷ X3 ∷ CCZ124 ∷ [])
  b0 = at 1 0 (CCZ124 ∷ CCZ124 ∷ []) (sym (wl0263 (lit c4))) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-box-perm-1324 c4) ▸
       at 0 2 (X3 ∷ Bx0-1324 ∷ X3 ∷ []) (sym (lem-Xb-box-at2332 c4)) ▸
       at 3 2 (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ CCZ124 ∷ []) (sym (wl1094 (lit c4))) ▸
       at 2 2 (CCZ124 ∷ X3 ∷ []) (sym (wl1091 (lit c4))) ▸
       at 3 2 (K4 ∷ CK34 ∷ ι ∷ X3 ∷ []) (sym (wl1095 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ X3 ∷ []) (sym (wl1091 (lit c4))) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-1324-at2332 c4) ▸ done

  b1 : Chain (X3 ∷ Bx0-1234 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι ∷ CCZ124 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ K4 ∷ CK34 ∷ ι ∷ CCZ124 ∷ X3 ∷ CCZ124 ∷ [])
  b1 = at 1 1 (Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ []) (lem-box-tQ c4) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 4 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

  b2 : Chain (X3 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ CCZ034 ∷ K4 ∷ CK34 ∷ ι ∷ CCZ124 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ X3 ∷ CCZ124 ∷ [])
  b2 = at 5 2 (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0888 c4) ▸
       at 8 2 (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ []) (wp0889 c4) ▸
       at 11 2 (ι ∷ CCZ034 ∷ []) (zc) ▸
       at 13 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b3 : Chain (X3 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι ∷ CCZ124 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ [])
  b3 = at 16 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 12 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 7 (K4 ∷ CK34 ∷ ι ∷ []) (sym (wp0892 c4)) ▸
       at 3 2 (CCZ124 ∷ Toff012 ∷ []) (sym (wp0300 c4)) ▸
       at 4 2 (K4 ∷ Toff012 ∷ []) (c₃ (Toff) (K ↑)) ▸
       at 5 2 (CK34 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₀₁)) ▸
       at 6 2 (ι ∷ Toff012 ∷ []) (zc) ▸
       at 7 2 (CCZ124 ∷ Toff012 ∷ []) (sym (wp0300 c4)) ▸ done

  b4 : Chain (X3 ∷ Toff012 ∷ CCZ034 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι ∷ CCZ124 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ CK34 ∷ ι ∷ CCZ124 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ [])
  b4 = at 3 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 2 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 3 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 4 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 2 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 2 (K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ []) (wp0888 c4) ▸ done

  b5 : Chain (X3 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CCZ034 ∷ CK34 ∷ ι ∷ CCZ124 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ [])
  b5 = at 6 2 (CZ04 ∷ CK34 ∷ CZ04 ∷ CCZ034 ∷ []) (wp0889 c4) ▸
       at 9 2 (ι ∷ CCZ034 ∷ []) (zc) ▸
       at 11 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b6 : Chain (X3 ∷ Toff012 ∷ CCZ124 ∷ K4 ∷ Toff403 ∷ CCZ034 ∷ CZ04 ∷ CK34 ∷ CZ04 ∷ ι ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ Toff012 ∷ CCZ034 ∷ X3 ∷ CCZ124 ∷ []) (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι ∷ CCZ124 ∷ Bx0-1234 ∷ X3 ∷ CCZ124 ∷ [])
  b6 = at 10 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 3 7 (K4 ∷ CK34 ∷ ι ∷ []) (sym (wp0892 c4)) ▸
       at 1 2 (CCZ124 ∷ Toff012 ∷ []) (sym (wp0300 c4)) ▸
       at 2 2 (K4 ∷ Toff012 ∷ []) (c₃ (Toff) (K ↑)) ▸
       at 3 2 (CK34 ∷ Toff012 ∷ []) (c₃ (Toff) (CK₀₁)) ▸
       at 4 2 (ι ∷ Toff012 ∷ []) (zc) ▸
       at 5 2 (CCZ124 ∷ Toff012 ∷ []) (sym (wp0300 c4)) ▸
       at 6 4 (Bx0-1234 ∷ []) (sym (lem-box-tQ c4)) ▸ done

  b7 : Chain (X3 ∷ CCZ124 ∷ K4 ∷ CK34 ∷ ι ∷ CCZ124 ∷ Bx0-1234 ∷ X3 ∷ CCZ124 ∷ []) (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ Bx0-1234 ∷ [])
  b7 = at 6 1 (Bx0-1324 ∷ []) (sym (lem-box-perm-1324-at2332 c4)) ▸
       at 4 1 (ι1 ∷ []) (uₛ (iI) (iI ↑) Eq.refl) ▸
       at 0 6 (CCZ124 ∷ CK34 ∷ S3 ∷ CCZ124 ∷ X3 ∷ []) (sym (wp0893 c4)) ▸
       at 0 4 (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ []) (wl1096 (lit c4)) ▸
       at 3 3 (Bx0-1324 ∷ CCZ124 ∷ []) (lem-Xb-box-at2332 c4) ▸
       at 4 2 [] (wl0263 (lit c4)) ▸
       at 3 1 (Bx0-1234 ∷ []) (lem-box-perm-1324-at2332 c4) ▸ done


-- CKdc-boxL: 3 steps
lem-CKdc-boxL : Ws → ⟪ (CK34⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ []) ⟫ʷ
lem-CKdc-boxL c4 = run b0
  where
  b0 : Chain (CK34⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Bx0-1234 ∷ Bx0-1234 ∷ []) (sym (lem-box2 c4)) ▸
       at 1 2 (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ Bx0-1234 ∷ []) (lem-CKdc-box c4) ▸
       at 4 2 [] (lem-box2 c4) ▸ done


-- box-perm-2134 @03102132: 1 steps
lem-box-perm-2134-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1024 ∷ []) ⟫ʷ
lem-box-perm-2134-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-1024 ∷ [])
  b0 = at 0 1 (Bx3-1024 ∷ []) (lem-sym-ab-at03102132 c4) ▸ done


-- S-sym-xt: 8 steps
lem-S-sym-xt : Ws → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-1-02-4 ∷ []) ⟫ʷ
lem-S-sym-xt c4 = run b0
  where
  b0 : Chain (Sb3-0-12-4 ∷ []) (Sb3-1-02-4 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 2 1 (CS04 ∷ []) (refl) ▸
       at 4 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 1 (Bx3-1024 ∷ []) (lem-box-perm-2134-at03102132 c4) ▸
       at 1 4 (Toff402 ∷ CS14 ∷ Toff402 ∷ CS14⁻ ∷ []) (sym (wp0894 c4)) ▸
       at 2 1 (Sb3-1-4-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-1-4-2 ∷ []) (refl) ▸
       at 0 5 (Sb3-1-02-4 ∷ []) (refl) ▸ done


-- box-tQ @03102132: 13 steps
lem-box-tQ-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx3-0124 ∷ []) (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ [])
  b0 = at 0 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ013 ∷ Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ013 ∷ CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 0 2 (Toff301 ∷ CCZ013 ∷ CZ01 ∷ []) (wl0519 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ013 ∷ []) (lem-cQ-at03102132 c4) ▸
       at 2 4 (Toff301 ∷ []) (wl0520 (lit c4)) ▸ done


-- CXbc-box @03102132: 17 steps
lem-CXbc-box-at03102132 : Ws → ⟪ (CX12 ∷ Bx3-0124 ∷ CX12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX12 ∷ Bx3-0124 ∷ CX12 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX12 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CCZ234 ∷ CX01 ∷ CS04 ∷ CX12 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ CX12 ∷ []) (wl0524 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (sym (wl1097 (lit c4))) ▸
       at 3 2 (Toff301 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0895 c4) ▸
       at 2 2 (Toff301 ∷ CX12 ∷ []) (wl0524 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 9 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 8 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CX12 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CCZ234 ∷ CX01 ∷ CS04 ∷ CX12 ∷ []) (Bx3-0124 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS14⁻ ∷ []) (sym (wl0451 (lit c4))) ▸
       at 6 2 (CCZ234 ∷ CX01 ∷ []) (c₂ (CX₀₁) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ134 ∷ []) (wl0960 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX12 ∷ CCZ134 ∷ []) (sym (wl1097 (lit c4))) ▸
       at 4 3 (CX12 ∷ []) (wl1098 (lit c4)) ▸
       at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-tQ-at03102132 c4)) ▸ done

  b2 : Chain (Bx3-0124 ∷ CX12 ∷ CCZ014 ∷ CX12 ∷ []) (Bx3-0124 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0655 c4)) ▸ done


-- CXcb-box @03102132: 18 steps
lem-CXcb-box-at03102132 : Ws → ⟪ (CX21 ∷ Bx3-0124 ∷ CX21 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ CCZ024 ∷ []) ⟫ʷ
lem-CXcb-box-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX21 ∷ Bx3-0124 ∷ CX21 ∷ []) (Toff301 ∷ CCZ234 ∷ CX21 ∷ Toff302 ∷ CS24 ∷ CX02 ∷ Toff301 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ234 ∷ CX21 ∷ [])
  b0 = at 1 1 (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ []) (lem-box-tQ-at03102132 c4) ▸
       at 0 2 (Toff301 ∷ CX21 ∷ Toff302 ∷ []) (wl1099 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Toff302 ∷ CCZ024 ∷ []) (sym (wp0896 c4)) ▸
       at 1 2 (CCZ234 ∷ CX21 ∷ []) (sym (wl0836 (lit c4))) ▸
       at 4 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 8 2 (Toff301 ∷ CS04 ∷ []) (wp0897 c4) ▸
       at 7 2 (Toff301 ∷ CX02 ∷ []) (wl0521 (lit c4)) ▸
       at 6 2 (Toff301 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF301 (lit c4)) ▸ done

  b1 : Chain (Toff301 ∷ CCZ234 ∷ CX21 ∷ Toff302 ∷ CS24 ∷ CX02 ∷ Toff301 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ234 ∷ CX21 ∷ []) (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ [])
  b1 = at 5 2 (Toff301 ∷ CX02 ∷ []) (wl0521 (lit c4)) ▸
       at 4 2 (Toff301 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF301 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 3 2 (Toff301 ∷ Toff302 ∷ []) (sym (wl1100 (lit c4))) ▸
       at 2 2 (Toff301 ∷ CX21 ∷ Toff302 ∷ []) (wl1099 (lit c4)) ▸
       at 3 3 (CX21 ∷ []) (wl1101 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 2 (CCZ234 ∷ CX21 ∷ []) (sym (wl0836 (lit c4))) ▸ done

  b2 : Chain (Toff301 ∷ CCZ234 ∷ Toff301 ∷ CCZ234 ∷ CX21 ∷ CCZ024 ∷ CX21 ∷ []) (Bx3-0124 ∷ CCZ024 ∷ [])
  b2 = at 0 4 (Bx3-0124 ∷ []) (sym (lem-box-tQ-at03102132 c4)) ▸
       at 1 3 (CCZ024 ∷ []) (sym (wp0898 c4)) ▸ done


-- SWbc-box @03102132: 11 steps
lem-SWbc-box-at03102132 : Ws → ⟪ (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0124 ∷ []) ⟫ʷ
lem-SWbc-box-at03102132 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (CX12 ∷ Bx3-0124 ∷ CX12 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 4 1 (CX12 ∷ CX21 ∷ CX12 ∷ []) (sym (wl0677 (lit c4))) ▸
       at 2 3 (Bx3-0124 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03102132 c4) ▸
       at 3 2 (CX21 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0899 c4) ▸
       at 1 3 (Bx3-0124 ∷ CCZ024 ∷ []) (lem-CXcb-box-at03102132 c4) ▸
       at 4 2 (CX12 ∷ CCZ014 ∷ []) (wp0054 c4) ▸
       at 3 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸
       at 2 2 (CX12 ∷ CCZ014 ∷ CCZ024 ∷ []) (wp0653 c4) ▸ done

  b1 : Chain (CX12 ∷ Bx3-0124 ∷ CX12 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ CCZ024 ∷ CCZ014 ∷ []) (Bx3-0124 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0900 c4) ▸
       at 0 3 (Bx3-0124 ∷ CCZ014 ∷ []) (lem-CXbc-box-at03102132 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @03102132: 23 steps
lem-nat-SWbc-at03102132 : Ws → ⟪ (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-nat-SWbc-at03102132 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ Sw12 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Sw12 ∷ [])
  b0 = at 1 1 (CCZ013 ∷ Toff301 ∷ Bx0-324 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 1 2 (Toff302 ∷ Sw12 ∷ []) (wl0841 (lit c4)) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 2 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 3 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸
       at 4 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 5 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸ done

  b1 : Chain (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ Sw12 ∷ CCZ023 ∷ Bx3-04 ∷ Toff301 ∷ CCZ013 ∷ Bx0-324 ∷ Sw12 ∷ []) (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Sw12 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Sw12 ∷ [])
  b1 = at 6 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 7 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 8 2 (Toff302 ∷ Sw12 ∷ []) (wl0841 (lit c4)) ▸
       at 9 2 (CCZ023 ∷ Sw12 ∷ []) (sym (wl0840 (lit c4))) ▸
       at 11 1 (CCZ023 ∷ Toff023 ∷ Bx3-04 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ []) (refl) ▸
       at 10 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 11 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸
       at 12 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ023 ∷ Toff302 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Toff013 ∷ CCZ013 ∷ Bx3-04 ∷ Toff302 ∷ CCZ023 ∷ CCZ013 ∷ Toff013 ∷ Bx3-04 ∷ Sw12 ∷ Toff023 ∷ CCZ023 ∷ Bx3-04 ∷ Sw12 ∷ []) (Bx3-0214 ∷ [])
  b2 = at 13 2 (Toff013 ∷ Sw12 ∷ []) (wl0839 (lit c4)) ▸
       at 14 2 (CCZ013 ∷ Sw12 ∷ []) (sym (wl0838 (lit c4))) ▸
       at 15 2 (Bx3-04 ∷ Sw12 ∷ []) (lem-comm-SWAP12-BOX⟨3·04⟩ (lit c4)) ▸
       at 16 2 [] (wl0006 (lit c4)) ▸
       at 2 6 (Bx0-314 ∷ []) (refl) ▸
       at 5 6 (Bx0-314 ∷ []) (refl) ▸
       at 0 6 (Bx3-0214 ∷ []) (refl) ▸ done


-- sym-bc @03102132: 2 steps
lem-sym-bc-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-sym-bc-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 1 (Sw12 ∷ Bx3-0124 ∷ Sw12 ∷ []) (sym (lem-SWbc-box-at03102132 c4)) ▸
       at 0 3 (Bx3-0214 ∷ []) (lem-nat-SWbc-at03102132 c4) ▸ done


-- box-perm-1324 @03102132: 1 steps
lem-box-perm-1324-at03102132 : Ws → ⟪ (Bx3-0124 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0214 ∷ []) ⟫ʷ
lem-box-perm-1324-at03102132 c4 = run b0
  where
  b0 : Chain (Bx3-0124 ∷ []) (Bx3-0214 ∷ [])
  b0 = at 0 1 (Bx3-0214 ∷ []) (lem-sym-bc-at03102132 c4) ▸ done


-- S-sym-ty: 8 steps
lem-S-sym-ty : Ws → ⟪ (Sb3-0-12-4 ∷ []) ⟫ʷ ≈ ⟪ (Sb3-0-21-4 ∷ []) ⟫ʷ
lem-S-sym-ty c4 = run b0
  where
  b0 : Chain (Sb3-0-12-4 ∷ []) (Sb3-0-21-4 ∷ [])
  b0 = at 0 1 (Bx3-0124 ∷ Toff412 ∷ Sb3-0-4-2 ∷ Toff412 ∷ Sb⁻3-0-4-2 ∷ []) (refl) ▸
       at 2 1 (CS04 ∷ []) (refl) ▸
       at 4 1 (CS04⁻ ∷ []) (refl) ▸
       at 0 1 (Bx3-0214 ∷ []) (lem-box-perm-1324-at03102132 c4) ▸
       at 1 4 (Toff412 ∷ CS04 ∷ Toff412 ∷ CS04⁻ ∷ []) (wp0901 c4) ▸
       at 2 1 (Sb3-0-4-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-4-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-21-4 ∷ []) (refl) ▸ done


-- F1-order-I@0: 1 steps
lem-F1-order-Iat0 : Ws → ⟪ (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Iat0 c4 = run b0
  where
  b0 : Chain (S4 ∷ S4 ∷ S4 ∷ S4 ∷ []) []
  b0 = at 0 4 [] (wl1102 (lit c4)) ▸ done


-- F1-order-S@0: 1 steps
lem-F1-order-Sat0 : Ws → ⟪ (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat0 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CS04 ∷ CS04 ∷ CS04 ∷ []) []
  b0 = at 0 4 [] (wp0902 c4) ▸ done


-- F1-order-S@1: 1 steps
lem-F1-order-Sat1 : Ws → ⟪ (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat1 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CS14 ∷ CS14 ∷ CS14 ∷ []) []
  b0 = at 0 4 [] (wl1103 (lit c4)) ▸ done


-- F1-order-S@2: 1 steps
lem-F1-order-Sat2 : Ws → ⟪ (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat2 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CS24 ∷ CS24 ∷ CS24 ∷ []) []
  b0 = at 0 4 [] (wl1104 (lit c4)) ▸ done


-- F1-order-S@3: 1 steps
lem-F1-order-Sat3 : Ws → ⟪ (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-Sat3 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CS34 ∷ CS34 ∷ CS34 ∷ []) []
  b0 = at 0 4 [] (wl1105 (lit c4)) ▸ done


-- F1-order-K@0: 1 steps
lem-F1-order-Kat0 : Ws → ⟪ (CK40 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat0 c4 = run b0
  where
  b0 : Chain (CK40 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wp0903 c4) ▸ done


-- F1-order-K@1: 1 steps
lem-F1-order-Kat1 : Ws → ⟪ (CK41 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat1 c4 = run b0
  where
  b0 : Chain (CK41 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl1106 (lit c4)) ▸ done


-- F1-order-K@2: 1 steps
lem-F1-order-Kat2 : Ws → ⟪ (CK42 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat2 c4 = run b0
  where
  b0 : Chain (CK42 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl1107 (lit c4)) ▸ done


-- F1-order-K@3: 1 steps
lem-F1-order-Kat3 : Ws → ⟪ (CK43 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-Kat3 c4 = run b0
  where
  b0 : Chain (CK43 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 2 (S4 ∷ S4 ∷ S4 ∷ []) (wl1108 (lit c4)) ▸ done


-- F1-order-SK@0: 1 steps
lem-F1-order-SKat0 : Ws → ⟪ (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat0 c4 = run b0
  where
  b0 : Chain (CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ CS04 ∷ CK40 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wp0904 c4) ▸ done


-- F1-order-SK@1: 1 steps
lem-F1-order-SKat1 : Ws → ⟪ (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat1 c4 = run b0
  where
  b0 : Chain (CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ CS14 ∷ CK41 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl1109 (lit c4)) ▸ done


-- F1-order-SK@2: 1 steps
lem-F1-order-SKat2 : Ws → ⟪ (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat2 c4 = run b0
  where
  b0 : Chain (CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ CS24 ∷ CK42 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl1110 (lit c4)) ▸ done


-- F1-order-SK@3: 1 steps
lem-F1-order-SKat3 : Ws → ⟪ (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (S4 ∷ S4 ∷ S4 ∷ []) ⟫ʷ
lem-F1-order-SKat3 c4 = run b0
  where
  b0 : Chain (CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ CS34 ∷ CK43 ∷ []) (S4 ∷ S4 ∷ S4 ∷ [])
  b0 = at 0 6 (S4 ∷ S4 ∷ S4 ∷ []) (wl1111 (lit c4)) ▸ done


-- nf-order-CS@0: 0 steps
lem-nf-order-CSat0 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat0 c4 = refl

-- S2-SBOX(2;0;41;3): 86 steps
lem-S2-SBOX⟨2·0·41·3⟩ : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ014 ∷ []) ⟫ʷ
lem-S2-SBOX⟨2·0·41·3⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 0 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 1 (CS03 ∷ []) (refl) ▸
       at 4 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸ done

  b1 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CCZ024 ∷ CS03⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 5 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 7 2 (Toff213 ∷ CS03⁻ ∷ []) (wl0191 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 9 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 8 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b2 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 4 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b3 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ CCZ024 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 12 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 11 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 7 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b4 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ024 ∷ Toff314 ∷ Toff213 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 5 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 8 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 7 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 11 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸ done

  b5 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ Toff213 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ Toff214 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b5 = at 8 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸
       at 7 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 3 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 3 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸ done

  b6 : Chain (Bx2-0413 ∷ Toff314 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CS03 ∷ Toff213 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ K3 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b6 = at 5 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 1 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 7 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b7 : Chain (Bx2-0413 ∷ K3 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b7 = at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 1 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 2 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 2 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b8 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff213 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b8 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0042 c4)) ▸
       at 6 2 (Toff213 ∷ Toff214 ∷ Toff314 ∷ []) (sym (wl0192 (lit c4))) ▸ done

  b9 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff213 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b9 = at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (Toff213 ∷ CS01 ∷ []) (wl0193 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS14⁻ ∷ []) (wl0194 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 5 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (Toff213 ∷ Toff214 ∷ []) (sym (wl0197 (lit c4))) ▸ done

  b10 : Chain (Bx2-0413 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ Toff314 ∷ CS03 ∷ CCZ014 ∷ Toff314 ∷ CS03⁻ ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ014 ∷ [])
  b10 = at 5 3 (CCZ014 ∷ []) (sym (wp0044 c4)) ▸
       at 1 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 0 2 [] (lem-box2-at0210243143 c4) ▸
       at 0 3 (Toff314 ∷ CS03 ∷ CCZ014 ∷ []) (wp0651 c4) ▸
       at 2 2 [] (wp0161 c4) ▸
       at 0 8 (CCZ014 ∷ []) (sym (wp0905 c4)) ▸ done


-- F1-order-CS@0: 5 steps
lem-F1-order-CSat0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat0 c4 = run b0
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ []) []
  b0 = at 0 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 1 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨2·0·41·3⟩ c4) ▸
       at 0 2 [] (wp0161 c4) ▸
       at 0 0 [] (wl1112 (lit c4)) ▸
       at 0 0 [] (sym (lem-nf-order-CSat0 c4)) ▸ done


-- nf-order-CS@1: 0 steps
lem-nf-order-CSat1 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat1 c4 = refl

-- S2-SBOX(0;1;42;3): 86 steps
lem-S2-SBOX⟨0·1·42·3⟩ : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (CCZ124 ∷ []) ⟫ʷ
lem-S2-SBOX⟨0·1·42·3⟩ c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 5 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13⁻ ∷ []) (sym (wp0060 c4)) ▸
       at 7 2 (Toff023 ∷ CS13⁻ ∷ []) (wl0219 (lit c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 9 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 8 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 5 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 3 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b3 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 12 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 11 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 10 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 6 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 7 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b4 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ014 ∷ Toff324 ∷ Toff023 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 5 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 8 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸ done

  b5 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff024 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 8 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 3 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸ done

  b6 : Chain (Bx0-1423 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CS13 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 5 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 1 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 7 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 6 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 5 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸ done

  b7 : Chain (Bx0-1423 ∷ K3 ∷ CS34 ∷ CX23 ∷ CCZ014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 3 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 1 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 10 2 (CCZ014 ∷ K3⁻ ∷ []) (sym (wp0061 c4)) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸ done

  b8 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 4 2 (CCZ014 ∷ K3 ∷ []) (sym (wp0065 c4)) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ []) (sym (wp0071 c4)) ▸
       at 6 2 (Toff023 ∷ Toff024 ∷ Toff324 ∷ []) (sym (wp0068 c4)) ▸ done

  b9 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CS24⁻ ∷ []) (wp0069 c4) ▸
       at 6 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 5 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 2 (Toff023 ∷ Toff024 ∷ []) (sym (wp0072 c4)) ▸ done

  b10 : Chain (Bx0-1423 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ124 ∷ [])
  b10 = at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 0 2 [] (lem-box2-at243243 c4) ▸
       at 0 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 2 2 [] (wl0263 (lit c4)) ▸
       at 0 8 (CCZ124 ∷ []) (sym (wl1113 (lit c4))) ▸ done


-- F1-order-CS@1: 5 steps
lem-F1-order-CSat1 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat1 c4 = run b0
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) []
  b0 = at 0 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 0 2 [] (wl0263 (lit c4)) ▸
       at 0 0 [] (wl1112 (lit c4)) ▸
       at 0 0 [] (sym (lem-nf-order-CSat1 c4)) ▸ done


-- nf-order-CS@2: 0 steps
lem-nf-order-CSat2 : Ws → ⟪ [] ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-nf-order-CSat2 c4 = refl
