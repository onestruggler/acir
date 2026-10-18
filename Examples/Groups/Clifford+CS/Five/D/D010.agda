{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D010 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0166 ; wl0167 ; wl0171 ; wl0175 ; wl0179 ; wl0180 ; wl0181 ; wl0195 ; wl0196 ; wl0206 ; wl0207 ; wl0208 ; wl0209 ; wl0211 ; wl0230 ; wl0242 ; wl0268 ; wl0288 ; wl0293 ; wl0294 ; wl0297 ; wl0300 ; wl0305 ; wl0306 ; wl0321 ; wl0323 ; wl0341 ; wl0415 ; wl0416 ; wl0417 ; wl0418 ; wl0419 ; wl0420 ; wl0421 ; wl0423 ; wl0518 ; wl0611 ; wl0704 ; wl0852 ; wl0854 ; wl0855 ; wl0856 ; wl0857 ; wl0861 ; wl0864 ; wl0865 ; wl0878 ; wl0879 ; wl0880 ; wl0881 ; wl0882 ; wl0883 ; wl0884 ; wl0885 ; wl0886 ; wl0887 ; wl0888 ; wl0889 ; wl0890 ; wl0891 ; wl0892 ; wl0893 ; wl0894 ; wl0895 ; wl0896 ; wl0897 ; wl0898 ; wl0899 ; wl0900 ; wl0901 ; wl0902 ; wl0903 ; wl0904 ; wl0905 ; wl0906 ; wl0907 ; wl0908 ; wl0909 ; wl0910 ; wl0911 ; wl0912 ; wl0913 ; wl0914 ; wl0915 ; wl0916 ; wl0917 ; wl0918 ; wl0919 ; wl0920 ; wl0921 ; wl0922 ; wl0923 ; wl0924 ; wl0925 ; wl0926 ; wl0927 ; wl0928 ; wl0929 ; wl0930 ; wl0931 ; wl0932 ; wl0933 ; wl0934 ; wl0935 ; wl0936 ; wl0937 ; wl0938 ; wl0939 ; wl0940 ; wl0941 ; wl0942 ; wl0943 ; wl0944 ; wl0945 ; wl0946 ; wl0947 ; wl0948 ; wl0949 ; wl0950 ; wl0951 ; wp0007 ; wp0011 ; wp0012 ; wp0013 ; wp0021 ; wp0032 ; wp0034 ; wp0035 ; wp0036 ; wp0038 ; wp0039 ; wp0052 ; wp0053 ; wp0054 ; wp0055 ; wp0081 ; wp0087 ; wp0090 ; wp0091 ; wp0092 ; wp0104 ; wp0109 ; wp0110 ; wp0115 ; wp0116 ; wp0117 ; wp0127 ; wp0130 ; wp0138 ; wp0140 ; wp0141 ; wp0142 ; wp0143 ; wp0145 ; wp0162 ; wp0165 ; wp0167 ; wp0179 ; wp0189 ; wp0202 ; wp0251 ; wp0252 ; wp0279 ; wp0280 ; wp0282 ; wp0283 ; wp0285 ; wp0290 ; wp0292 ; wp0295 ; wp0312 ; wp0313 ; wp0314 ; wp0341 ; wp0357 ; wp0560 ; wp0565 ; wp0566 ; wp0567 ; wp0568 ; wp0705 ; wp0734 ; wp0737 ; wp0750 ; wp0751 ; wp0752 ; wp0753 ; wp0754 ; wp0755 ; wp0756 ; wp0757 ; wp0758 ; wp0759 ; wp0760 ; wp0761 ; wp0762 ; wp0763 ; wp0764 ; wp0765 ; wp0766 ; wp0767 ; wp0768 ; wp0769)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-tQ-at0210243143 ; lem-tP-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-pairs-at13243241)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-cP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-perm-1324-at243243 ; lem-sym-ab-at122441 ; lem-sym-bc-at1441)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CSdu-box-3-at243243 ; lem-CSu-box-3-at243243 ; lem-F0-at14213243 ; lem-box-box-1-at03102132 ; lem-box-perm-1342-at0310243142 ; lem-box-perm-1423-at03102132 ; lem-box-perm-2431-at132132 ; lem-box-perm-4132-at243243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS04-TOFF213 ; lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034 ; lem-comm-CX12-TOFF034 ; lem-comm-CX31-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ134-CS02 ; lem-comm-CX04-TOFF312 ; lem-comm-CZ13-TOFF204 ; lem-comm-SWAP03-BOX⟨2·14⟩ ; lem-comm-SWAP14-BOX⟨2·30⟩ ; lem-comm-TOFF312-CX04)
-- CXu-box-4 @0310243142: 15 steps
lem-CXu-box-4-at0310243142 : Ws → ⟪ (CX23 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CX23 ∷ []) ⟫ʷ
lem-CXu-box-4-at0310243142 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (CX23 ∷ Bx3-0412 ∷ []) (CCZ034 ∷ CX23 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 2 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 6 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS24⁻ ∷ []) (wl0878 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 2 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ CX23 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ []) (Bx3-0412 ∷ CX23 ∷ [])
  b1 = at 3 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 1 2 (Toff312 ∷ CX23 ∷ []) (wl0880 (lit c4)) ▸
       at 3 2 (CCZ034 ∷ CCZ024 ∷ []) (wp0109 c4) ▸
       at 2 2 (CCZ034 ∷ CX23 ∷ CCZ024 ∷ []) (sym (wp0104 c4)) ▸
       at 3 3 (CX23 ∷ []) (wp0110 c4) ▸
       at 3 2 (Toff312 ∷ CX23 ∷ []) (wl0880 (lit c4)) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done


-- CSu-box-3 @0310243142: 17 steps
lem-CSu-box-3-at0310243142 : Ws → ⟪ (CS13 ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CS13 ∷ []) ⟫ʷ
lem-CSu-box-3-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13 ∷ Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 1 2 (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (wl0881 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ CS13 ∷ CS12 ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ [])
  b1 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 5 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS12 ∷ []) (wl0883 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CS13 ∷ CS12 ∷ CCZ123 ∷ []) (wl0881 (lit c4)) ▸
       at 4 6 (CS13 ∷ []) (wl0884 (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ []) (Bx3-0412 ∷ CS13 ∷ [])
  b2 = at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done


-- CSdu-box-3 @0310243142: 17 steps
lem-CSdu-box-3-at0310243142 : Ws → ⟪ (CS13⁻ ∷ Bx3-0412 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-0412 ∷ CS13⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0310243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS13⁻ ∷ Bx3-0412 ∷ []) (CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 1 2 (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl0885 (lit c4)) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CS12 ∷ CCZ034 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff312 ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ [])
  b1 = at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS13⁻ ∷ []) (sym (wp0734 c4)) ▸
       at 5 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS12⁻ ∷ []) (wl0886 (lit c4)) ▸
       at 3 2 (Toff312 ∷ CS13⁻ ∷ CS12⁻ ∷ CCZ123 ∷ []) (wl0885 (lit c4)) ▸
       at 4 6 (CS13⁻ ∷ []) (wl0887 (lit c4)) ▸ done

  b2 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ []) (Bx3-0412 ∷ CS13⁻ ∷ [])
  b2 = at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done


-- F4-CS0-CS1: 232 steps
lem-F4-CS0-CS1 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (run b28))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb3-0-41-2 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸ done

  b1 : Chain (X4 ∷ Sb3-0-41-2 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Sb3-0-41-2 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ014 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb3-0-41-2 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ014 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Bx0-1423 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 4 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 5 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 5 1 (CS02⁻ ∷ []) (refl) ▸
       at 5 2 (Bx0-1423 ∷ CS02⁻ ∷ []) (lem-CSdu-box-3-at243243 c4) ▸ done

  b3 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Bx0-1423 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 5 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 5 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 4 2 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0750 c4)) ▸
       at 6 2 (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0165 c4) ▸
       at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 11 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 10 2 (Toff034 ∷ CS14 ∷ []) (wp0251 c4) ▸
       at 9 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸ done

  b4 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ Toff214 ∷ CCZ014 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ012 ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 8 2 (Toff034 ∷ CS24⁻ ∷ []) (wp0252 c4) ▸
       at 7 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS24 ∷ []) (wp0202 c4) ▸
       at 5 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 6 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 8 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 12 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 11 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸ done

  b5 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ Toff214 ∷ CCZ014 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ012 ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff214 ∷ Toff034 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 10 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 9 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 7 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 6 2 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0750 c4)) ▸
       at 7 3 (Toff214 ∷ []) (wp0753 c4) ▸
       at 8 2 (Toff034 ∷ CCZ134 ∷ []) (wp0012 c4) ▸ done

  b6 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff214 ∷ Toff034 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 7 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 13 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 12 2 (Toff034 ∷ CS14 ∷ []) (wp0251 c4) ▸
       at 11 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 10 2 (Toff034 ∷ CS24⁻ ∷ []) (wp0252 c4) ▸
       at 9 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS24 ∷ []) (wp0202 c4) ▸
       at 7 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸ done

  b7 : Chain (X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff214 ∷ CCZ014 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 8 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 4 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 3 1 (CS02 ∷ []) (refl) ▸
       at 3 2 (Bx0-1423 ∷ CS02 ∷ []) (lem-CSu-box-3-at243243 c4) ▸
       at 3 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 2 2 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0750 c4)) ▸ done

  b8 : Chain (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff214 ∷ CCZ014 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ K2 ∷ Toff034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (Toff034 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0165 c4) ▸
       at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 9 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 8 2 (Toff034 ∷ CS14 ∷ []) (wp0251 c4) ▸
       at 7 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS24⁻ ∷ []) (wp0252 c4) ▸
       at 5 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CS24 ∷ []) (wp0202 c4) ▸ done

  b9 : Chain (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ K2 ∷ Toff034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff034 ∷ Toff214 ∷ CCZ014 ∷ CCZ012 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 3 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 4 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 6 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 10 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸ done

  b10 : Chain (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff034 ∷ Toff214 ∷ CCZ014 ∷ CCZ012 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff034 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b10 = at 7 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 5 2 (CCZ012 ∷ CCZ014 ∷ []) (sym (wp0167 c4)) ▸
       at 4 2 (CCZ012 ∷ Toff214 ∷ CCZ014 ∷ []) (sym (wp0750 c4)) ▸
       at 5 3 (Toff214 ∷ []) (wp0753 c4) ▸
       at 6 2 (Toff034 ∷ CCZ134 ∷ []) (wp0012 c4) ▸
       at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 11 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 10 2 (Toff034 ∷ CS14 ∷ []) (wp0251 c4) ▸ done

  b11 : Chain (X4 ∷ Bx3-0412 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff034 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Bx0-1423 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b11 = at 9 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS24⁻ ∷ []) (wp0252 c4) ▸
       at 7 2 (Toff034 ∷ CX12 ∷ []) (lem-comm-CX12-TOFF034 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS24 ∷ []) (wp0202 c4) ▸
       at 5 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 6 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 2 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 2 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸ done

  b12 : Chain (X4 ∷ Bx3-0412 ∷ Bx0-1423 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ X4 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b12 = at 1 1 (Bx3-0124 ∷ []) (lem-box-perm-1342-at0310243142 c4) ▸
       at 2 1 (Bx0-3124 ∷ []) (lem-box-perm-4132-at243243 c4) ▸
       at 1 2 (Bx0-3124 ∷ Bx3-0124 ∷ []) (lem-box-box-1-at03102132 c4) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-box-perm-2431-at132132 c4) ▸
       at 2 1 (Bx3-0412 ∷ []) (lem-box-perm-1423-at03102132 c4) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸ done

  b13 : Chain (CCZ014 ∷ X4 ∷ Toff023 ∷ CZ01 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CCZ014 ∷ CCZ123 ∷ Toff023 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b13 = at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸ done

  b14 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CCZ014 ∷ CCZ123 ∷ Toff023 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b14 = at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b15 : Chain (Bx0-1423 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ034 ∷ Toff312 ∷ CZ12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b15 = at 6 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 5 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 4 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 3 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 2 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff312 ∷ CZ12 ∷ CCZ123 ∷ []) (wl0882 (lit c4)) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b16 : Chain (Bx0-1423 ∷ X4 ∷ CCZ034 ∷ Toff312 ∷ CZ12 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b16 = at 9 2 (CCZ034 ∷ CS13 ∷ []) (sym (wp0312 c4)) ▸
       at 8 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CS23⁻ ∷ []) (sym (wp0313 c4)) ▸
       at 6 2 (CCZ034 ∷ CX12 ∷ []) (lem-comm-CX12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ034 ∷ CZ12 ∷ []) (lem-comm-CZ12-CCZ034 (lit c4)) ▸
       at 5 3 (Toff312 ∷ CCZ123 ∷ []) (wl0889 (lit c4)) ▸ done

  b17 : Chain (Bx0-1423 ∷ X4 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ123 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b17 = at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 3 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ CCZ134 ∷ []) (wl0890 (lit c4)) ▸
       at 6 2 (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4)) ▸
       at 5 2 (CS02 ∷ CCZ123 ∷ []) (wl0171 (lit c4)) ▸
       at 6 4 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0891 (lit c4)) ▸
       at 8 2 (CS02⁻ ∷ CCZ123 ∷ []) (wl0611 (lit c4)) ▸
       at 9 2 (X4 ∷ CCZ123 ∷ []) (wl0892 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b18 : Chain (Bx0-1423 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ CCZ134 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS02⁻ ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b18 = at 4 2 (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4)) ▸
       at 5 2 (Toff214 ∷ CCZ134 ∷ []) (wl0893 (lit c4)) ▸
       at 6 2 [] (wl0321 (lit c4)) ▸
       at 4 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 2 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸
       at 2 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸ done

  b19 : Chain (Bx0-1423 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff324 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b19 = at 4 1 (CS02 ∷ []) (refl) ▸
       at 6 1 (CS02⁻ ∷ []) (refl) ▸
       at 6 3 (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) (wp0754 c4) ▸
       at 5 3 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (sym (wl0895 (lit c4))) ▸
       at 4 3 (CX23 ∷ Toff324 ∷ CS02 ∷ []) (wp0755 c4) ▸
       at 3 3 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (sym (wl0895 (lit c4))) ▸
       at 2 2 (CX23 ∷ Bx3-0412 ∷ []) (sym (lem-CXu-box-4-at0310243142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b20 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff324 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ Toff312 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b20 = at 6 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 5 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 4 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 5 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 6 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b21 : Chain (Bx0-1423 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ Toff312 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb3-0-41-2 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b21 = at 9 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 3 3 (Toff324 ∷ CCZ034 ∷ []) (wp0737 c4) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 6 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 4 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 1 3 (Toff324 ∷ X4 ∷ []) (sym (wl0211 (lit c4))) ▸ done

  b22 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb3-0-41-2 ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx3-0412 ∷ CS13 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b22 = at 4 2 (CS13 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸
       at 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 7 2 (CS13 ∷ CS02⁻ ∷ []) (wl0897 (lit c4)) ▸
       at 6 2 (CS13 ∷ Toff214 ∷ []) (sym (wl0898 (lit c4))) ▸
       at 5 2 (CS13 ∷ CS02 ∷ []) (wl0899 (lit c4)) ▸
       at 4 2 (CS13 ∷ Toff214 ∷ []) (sym (wl0898 (lit c4))) ▸ done

  b23 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Bx3-0412 ∷ CS13 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ [])
  b23 = at 3 2 (CS13 ∷ Bx3-0412 ∷ []) (sym (lem-CSu-box-3-at0310243142 c4)) ▸
       at 6 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 4 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸
       at 4 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 1 (CS02 ∷ []) (refl) ▸ done

  b24 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b24 = at 8 1 (CS02⁻ ∷ []) (refl) ▸
       at 8 3 (CX23 ∷ Toff324 ∷ CS02⁻ ∷ []) (wp0754 c4) ▸
       at 7 3 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (sym (wl0895 (lit c4))) ▸
       at 6 3 (CX23 ∷ Toff324 ∷ CS02 ∷ []) (wp0755 c4) ▸
       at 5 3 (CX23 ∷ Toff324 ∷ Toff214 ∷ []) (sym (wl0895 (lit c4))) ▸
       at 4 2 (CX23 ∷ Bx3-0412 ∷ []) (sym (lem-CXu-box-4-at0310243142 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 8 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸ done

  b25 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b25 = at 7 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 6 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 8 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 7 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 9 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 11 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸ done

  b26 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ CCZ034 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Sb3-0-41-2 ∷ CS13⁻ ∷ X4 ∷ [])
  b26 = at 7 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 5 3 (Toff324 ∷ CCZ034 ∷ []) (wp0737 c4) ▸
       at 6 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 8 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 3 3 (Toff324 ∷ X4 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0900 (lit c4))) ▸ done

  b27 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Sb3-0-41-2 ∷ CS13⁻ ∷ X4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ [])
  b27 = at 5 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 7 1 (CS02 ∷ []) (refl) ▸
       at 9 1 (CS02⁻ ∷ []) (refl) ▸
       at 9 2 (CS13⁻ ∷ CS02⁻ ∷ []) (wl0901 (lit c4)) ▸
       at 8 2 (CS13⁻ ∷ Toff214 ∷ []) (sym (wl0902 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CS02 ∷ []) (wl0903 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ Toff214 ∷ []) (sym (wl0902 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ Bx3-0412 ∷ []) (sym (lem-CSdu-box-3-at0310243142 c4)) ▸ done

  b28 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b28 = at 8 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 6 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0900 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0-at14213243 c4)) ▸ done


-- CSdu-box-3 @122441: 17 steps
lem-CSdu-box-3-at122441 : Ws → ⟪ (CS03⁻ ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS03⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03⁻ ∷ Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 1 2 (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) (wl0904 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 7 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03⁻ ∷ []) (sym (wp0032 c4)) ▸
       at 5 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (wl0906 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CS13⁻ ∷ []) (wl0907 (lit c4)) ▸
       at 3 2 (Toff013 ∷ CS03⁻ ∷ CS13⁻ ∷ CCZ013 ∷ []) (wl0904 (lit c4)) ▸
       at 4 6 (CS03⁻ ∷ []) (wl0908 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ []) (Bx0-2431 ∷ CS03⁻ ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- CSu-box-3 @122441: 17 steps
lem-CSu-box-3-at122441 : Ws → ⟪ (CS03 ∷ Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ CS03 ∷ []) ⟫ʷ
lem-CSu-box-3-at122441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS03 ∷ Bx0-2431 ∷ []) (CCZ024 ∷ Toff013 ∷ CS03 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 1 2 (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) (wl0909 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 7 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff013 ∷ CS03 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff013 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03 ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (wl0906 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CS13 ∷ []) (wl0910 (lit c4)) ▸
       at 3 2 (Toff013 ∷ CS03 ∷ CS13 ∷ CCZ013 ∷ []) (wl0909 (lit c4)) ▸
       at 4 6 (CS03 ∷ []) (wl0911 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03 ∷ []) (Bx0-2431 ∷ CS03 ∷ [])
  b2 = at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done


-- P-box @0210243143: 8 steps
lem-P-box-at0210243143 : Ws → ⟪ (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-P-box-at0210243143 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at0210243143 c4) ▸
       at 0 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0210243143 c4)) ▸
       at 1 2 (CCZ123 ∷ CZ13 ∷ Toff213 ∷ []) (sym (wl0912 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (sym (lem-tP-at0210243143 c4)) ▸
       at 4 3 (CCZ123 ∷ CZ13 ∷ []) (sym (wl0913 (lit c4))) ▸
       at 2 2 (Toff204 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF204 (lit c4)) ▸
       at 3 3 (CCZ123 ∷ []) (sym (wl0914 (lit c4))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done


-- cQ @022330: 7 steps
lem-cQ-at022330 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at022330 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done


-- box-tQ @022330: 13 steps
lem-box-tQ-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1304 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 2 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 5 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0915 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at022330 c4) ▸
       at 2 4 (Toff213 ∷ []) (wl0916 (lit c4)) ▸ done


-- pairs @0210243143: 4 steps
lem-pairs-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-pairs-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 1 (Toff213 ∷ Bx2-0413 ∷ Toff213 ∷ []) (sym (lem-P-box-at0210243143 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 4 2 [] (wl0180 (lit c4)) ▸
       at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done


-- CXbc-box @022330: 17 steps
lem-CXbc-box-at022330 : Ws → ⟪ (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXbc-box-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-1304 ∷ CX30 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX30 ∷ CCZ234 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (sym (wp0757 c4)) ▸
       at 3 2 (Toff213 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl0918 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX30 ∷ []) (wl0917 (lit c4)) ▸
       at 5 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX30 ∷ CCZ234 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ CX30 ∷ []) (Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ234 ∷ []) (sym (wp0090 c4)) ▸
       at 3 2 (CCZ024 ∷ CX30 ∷ CCZ234 ∷ []) (sym (wp0757 c4)) ▸
       at 4 3 (CX30 ∷ []) (wp0758 c4) ▸
       at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done

  b2 : Chain (Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-1304 ∷ CCZ134 ∷ [])
  b2 = at 1 3 (CCZ134 ∷ []) (sym (wp0759 c4)) ▸ done


-- CXcb-box @022330: 18 steps
lem-CXcb-box-at022330 : Ws → ⟪ (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-1304 ∷ CX03 ∷ []) (Toff213 ∷ CCZ024 ∷ CX03 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ Toff213 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ024 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ CX03 ∷ Toff201 ∷ []) (wl0919 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff201 ∷ CCZ014 ∷ []) (sym (wp0760 c4)) ▸
       at 1 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 4 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 8 2 (Toff213 ∷ CS14 ∷ []) (wl0195 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX03 ∷ Toff201 ∷ CS04 ∷ CX10 ∷ Toff213 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ CCZ024 ∷ CX03 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX10 ∷ []) (wl0920 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 3 2 (Toff213 ∷ Toff201 ∷ []) (wl0921 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX03 ∷ Toff201 ∷ []) (wl0919 (lit c4)) ▸
       at 3 3 (CX03 ∷ []) (wl0922 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ014 ∷ []) (wp0038 c4) ▸
       at 3 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-1304 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0761 c4)) ▸ done


-- SWbc-box @022330: 11 steps
lem-SWbc-box-at022330 : Ws → ⟪ (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-SWbc-box-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (CX30 ∷ Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ [])
  b0 = at 0 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 4 1 (CX30 ∷ CX03 ∷ CX30 ∷ []) (sym (wl0923 (lit c4))) ▸
       at 2 3 (Bx2-1304 ∷ CCZ134 ∷ []) (lem-CXbc-box-at022330 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸
       at 1 3 (Bx2-1304 ∷ CCZ014 ∷ []) (lem-CXcb-box-at022330 c4) ▸
       at 4 2 (CX30 ∷ CCZ134 ∷ []) (wp0705 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸
       at 2 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸ done

  b1 : Chain (CX30 ∷ Bx2-1304 ∷ CX30 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ []) (Bx2-1304 ∷ [])
  b1 = at 3 5 (CCZ134 ∷ []) (wp0764 c4) ▸
       at 0 3 (Bx2-1304 ∷ CCZ134 ∷ []) (lem-CXbc-box-at022330 c4) ▸
       at 1 2 [] (wl0321 (lit c4)) ▸ done


-- nat-SWbc @022330: 23 steps
lem-nat-SWbc-at022330 : Ws → ⟪ (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-nat-SWbc-at022330 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ Sw03 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx1-204 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 1 2 (Toff201 ∷ Sw03 ∷ []) (wl0925 (lit c4)) ▸
       at 3 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 3 2 (Toff123 ∷ Sw03 ∷ []) (wl0927 (lit c4)) ▸
       at 4 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 5 2 (Toff123 ∷ Sw03 ∷ []) (wl0927 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ Sw03 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ Bx1-204 ∷ Sw03 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Sw03 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 7 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 8 2 (Toff201 ∷ Sw03 ∷ []) (wl0925 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 11 1 (CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 11 2 (Toff123 ∷ Sw03 ∷ []) (wl0927 (lit c4)) ▸
       at 12 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Sw03 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Sw03 ∷ []) (Bx2-1034 ∷ [])
  b2 = at 13 2 (Toff123 ∷ Sw03 ∷ []) (wl0927 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 15 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx1-234 ∷ []) (refl) ▸
       at 5 6 (Bx1-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done


-- sym-bc @022330: 2 steps
lem-sym-bc-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym-bc-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-1304 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at022330 c4)) ▸
       at 0 3 (Bx2-1034 ∷ []) (lem-nat-SWbc-at022330 c4) ▸ done


-- sym-ab @0220: 18 steps
lem-sym-ab-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-sym-ab-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (sym (wp0280 c4)) ▸
       at 4 1 (Bx2-04 ∷ []) (refl) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ [])
  b1 = at 2 6 (Bx0-234 ∷ []) (refl) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ CZ04 ∷ Toff023 ∷ CCZ023 ∷ CZ04 ∷ []) (sym (wp0280 c4)) ▸
       at 7 1 (Bx2-04 ∷ []) (refl) ▸
       at 10 1 (Bx2-04 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (Bx2-0134 ∷ [])
  b2 = at 5 6 (Bx0-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-0134 ∷ []) (refl) ▸ done


-- box-perm-1342 @0210243143: 3 steps
lem-box-perm-1342-at0210243143 : Ws → ⟪ (Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-1342-at0210243143 c4 = run b0
  where
  b0 : Chain (Bx2-0413 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-1304 ∷ []) (lem-pairs-at0210243143 c4) ▸
       at 0 1 (Bx2-1034 ∷ []) (lem-sym-bc-at022330 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4) ▸ done


-- sym-ab @14233241: 18 steps
lem-sym-ab-at14233241 : Ws → ⟪ (Bx0-4321 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3421 ∷ []) ⟫ʷ
lem-sym-ab-at14233241 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4321 ∷ []) (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ [])
  b0 = at 0 1 (CCZ034 ∷ Toff034 ∷ Bx4-021 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (refl) ▸
       at 2 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4)) ▸
       at 4 1 (Bx0-31 ∷ []) (refl) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ034 ∷ Toff034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ Toff034 ∷ CCZ034 ∷ Bx4-021 ∷ []) (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ [])
  b1 = at 2 6 (Bx3-021 ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff402 ∷ Bx0-41 ∷ Toff402 ∷ CCZ024 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ012 ∷ []) (sym (wp0162 c4)) ▸
       at 5 1 (CCZ023 ∷ Toff302 ∷ CZ13 ∷ Toff302 ∷ CCZ023 ∷ CZ13 ∷ []) (wl0288 (lit c4)) ▸
       at 7 1 (Bx0-31 ∷ []) (refl) ▸
       at 10 1 (Bx0-31 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ034 ∷ Toff034 ∷ Bx3-021 ∷ Toff034 ∷ CCZ034 ∷ CCZ023 ∷ Toff302 ∷ Bx0-31 ∷ Toff302 ∷ CCZ023 ∷ Bx0-31 ∷ []) (Bx0-3421 ∷ [])
  b2 = at 5 6 (Bx3-021 ∷ []) (refl) ▸
       at 0 6 (Bx0-3421 ∷ []) (refl) ▸ done


-- box-perm-1432 @122441: 4 steps
lem-box-perm-1432-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-box-perm-1432-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4) ▸
       at 0 1 (Bx0-4321 ∷ []) (lem-sym-bc-at1441 c4) ▸
       at 0 1 (Bx0-3421 ∷ []) (lem-sym-ab-at14233241 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-pairs-at13243241 c4) ▸ done


-- sym-ab @021021: 18 steps
lem-sym-ab-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-sym-ab-at021021 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-0134 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx0-234 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 4 1 (CZ04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (sym (wl0518 (lit c4))) ▸
       at 4 1 (Bx2-14 ∷ []) (refl) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx0-234 ∷ []) (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ [])
  b1 = at 2 6 (Bx1-234 ∷ []) (refl) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-04 ∷ Toff023 ∷ CCZ023 ∷ Bx2-04 ∷ []) (refl) ▸
       at 7 1 (CZ04 ∷ []) (refl) ▸
       at 10 1 (CZ04 ∷ []) (refl) ▸
       at 5 6 (CCZ234 ∷ []) (wp0280 c4) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (sym (wl0518 (lit c4))) ▸
       at 7 1 (Bx2-14 ∷ []) (refl) ▸
       at 10 1 (Bx2-14 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (Bx2-1034 ∷ [])
  b2 = at 5 6 (Bx1-234 ∷ []) (refl) ▸
       at 0 6 (Bx2-1034 ∷ []) (refl) ▸ done


-- cQ @0220: 7 steps
lem-cQ-at0220 : Ws → ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-cQ-at0220 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ CCZ234 ∷ []) (CCZ234 ∷ CCZ012 ∷ [])
  b0 = at 0 1 (CS02 ∷ CX10 ∷ CS02⁻ ∷ CX10 ∷ CS12 ∷ []) (wl0929 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CS12 ∷ []) (sym (wl0415 (lit c4))) ▸
       at 3 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 2 2 (CCZ234 ∷ CS02⁻ ∷ []) (sym (wp0765 c4)) ▸
       at 1 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 0 2 (CCZ234 ∷ CS02 ∷ []) (sym (wp0279 c4)) ▸
       at 1 5 (CCZ012 ∷ []) (sym (wl0929 (lit c4))) ▸ done


-- box-tQ @0220: 13 steps
lem-box-tQ-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) ⟫ʷ
lem-box-tQ-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 0 2 (Toff201 ∷ CCZ012 ∷ CZ01 ∷ []) (wl0930 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ CZ01 ∷ []) (c₂ (CZ) (CCZ)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0220 c4) ▸
       at 2 4 (Toff201 ∷ []) (wl0931 (lit c4)) ▸ done


-- tP @0220: 7 steps
lem-tP-at0220 : Ws → ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ
lem-tP-at0220 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Toff234 ∷ []) (Toff234 ∷ Toff201 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ012 ∷ []) (lem-cQ-at0220 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸
       at 1 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸ done


-- P-box @0220: 8 steps
lem-P-box-at0220 : Ws → ⟪ (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-P-box-at0220 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0220 c4)) ▸
       at 1 2 (CCZ234 ∷ CZ34 ∷ Toff234 ∷ []) (sym (wl0932 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (sym (lem-tP-at0220 c4)) ▸
       at 4 3 (CCZ234 ∷ CZ34 ∷ []) (sym (wl0933 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CZ34 ∷ []) (sym (c₃ (Toffᵗ) (CZ))) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wl0934 (lit c4))) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done


-- VPQ @0220: 14 steps
lem-VPQ-at0220 : Ws → ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ
lem-VPQ-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 4 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 3 2 (CS34⁻ ∷ S2⁻ ∷ []) (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS)) ▸
       at 2 2 (CS34⁻ ∷ Toff201 ∷ []) (c₃ (Toffᵗ) (CS • CS • CS)) ▸
       at 1 2 (CS34⁻ ∷ S2 ∷ []) (c₃ (S ↑ ↑) (CS • CS • CS)) ▸
       at 0 2 (CS34⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) ((CS • CS • CS) ↑)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0220 c4) ▸ done

  b1 : Chain (CS34⁻ ∷ CS01⁻ ∷ S2 ∷ Toff234 ∷ Toff201 ∷ S2⁻ ∷ []) (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S)) ▸
       at 2 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸
       at 3 2 (S2⁻ ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (S • S • S)) ▸
       at 0 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸
       at 2 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸ done


-- QVQ @0220: 3 steps
lem-QVQ-at0220 : Ws → ⟪ (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-QVQ-at0220 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ234 ∷ []) (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ [])
  b0 = at 0 0 (Toff234 ∷ Toff234 ∷ []) (sym (wl0420 (lit c4))) ▸
       at 1 4 (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) (sym (lem-VPQ-at0220 c4)) ▸
       at 4 2 [] (wl0305 (lit c4)) ▸ done


-- box-cP @0220: 12 steps
lem-box-cP-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) ⟫ʷ
lem-box-cP-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1034 ∷ []) (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 5 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ012 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ CCZ123 ∷ Toff123 ∷ CZ14 ∷ Toff123 ∷ CCZ123 ∷ CZ14 ∷ []) (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ [])
  b1 = at 5 6 (CCZ234 ∷ []) (wl0518 (lit c4)) ▸
       at 2 4 (Toff234 ∷ Toff201 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-QVQ-at0220 c4) ▸
       at 1 2 (Toff234 ∷ Toff201 ∷ []) (lem-tP-at0220 c4) ▸
       at 2 2 [] (wl0421 (lit c4)) ▸ done


-- cQ @0213243140: 7 steps
lem-cQ-at0213243140 : Ws → ⟪ (CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (CCZ012 ∷ CCZ234 ∷ []) ⟫ʷ
lem-cQ-at0213243140 c4 = run b0
  where
  b0 : Chain (CCZ234 ∷ CCZ012 ∷ []) (CCZ012 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX34 ∷ CS24⁻ ∷ CX34 ∷ CS23 ∷ []) (wl0293 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CS23 ∷ []) (sym (wl0294 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 2 2 (CCZ012 ∷ CS24⁻ ∷ []) (sym (wp0140 c4)) ▸
       at 1 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 0 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 1 5 (CCZ234 ∷ []) (sym (wl0293 (lit c4))) ▸ done


-- box-tQ @0213243140: 13 steps
lem-box-tQ-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) ⟫ʷ
lem-box-tQ-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3410 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0935 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0935 (lit c4))) ▸
       at 0 2 (Toff234 ∷ CCZ234 ∷ CZ34 ∷ []) (wl0936 (lit c4)) ▸
       at 2 2 (CCZ012 ∷ CZ34 ∷ []) (sym (c₃ (CCZ) (CZ))) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243140 c4) ▸
       at 2 4 (Toff234 ∷ []) (wl0937 (lit c4)) ▸ done


-- pairs @0220: 4 steps
lem-pairs-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-pairs-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 0 1 (Toff234 ∷ Bx2-1034 ∷ Toff234 ∷ []) (sym (lem-P-box-at0220 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ []) (lem-box-cP-at0220 c4) ▸
       at 4 2 [] (wl0420 (lit c4)) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done


-- CXbc-box @0213243140: 17 steps
lem-CXbc-box-at0213243140 : Ws → ⟪ (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXbc-box-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-3410 ∷ CX41 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX41 ∷ CCZ024 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CCZ012 ∷ CX34 ∷ CS03 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ CX41 ∷ []) (wl0938 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (sym (wp0138 c4)) ▸
       at 3 2 (Toff234 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0290 c4) ▸
       at 2 2 (Toff234 ∷ CX41 ∷ []) (wl0938 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0115 c4) ▸
       at 9 2 (CCZ012 ∷ CS03 ∷ []) (sym (wl0268 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CX41 ∷ CCZ024 ∷ CS04 ∷ CX34 ∷ CS04⁻ ∷ CCZ012 ∷ CX34 ∷ CS03 ∷ CX41 ∷ []) (Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 7 2 (CCZ012 ∷ CS04⁻ ∷ []) (sym (wp0116 c4)) ▸
       at 6 2 (CCZ012 ∷ CX34 ∷ []) (sym (c₃ (CCZ) (CX₀₁))) ▸
       at 5 2 (CCZ012 ∷ CS04 ∷ []) (sym (wp0117 c4)) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0115 c4)) ▸
       at 4 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 3 2 (CCZ012 ∷ CX41 ∷ CCZ024 ∷ []) (sym (wp0138 c4)) ▸
       at 4 3 (CX41 ∷ []) (wp0143 c4) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done

  b2 : Chain (Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-3410 ∷ CCZ034 ∷ [])
  b2 = at 1 3 (CCZ034 ∷ []) (sym (wp0560 c4)) ▸ done


-- CXcb-box @0213243140: 18 steps
lem-CXcb-box-at0213243140 : Ws → ⟪ (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-3410 ∷ CX14 ∷ []) (Toff234 ∷ CCZ012 ∷ CX14 ∷ Toff213 ∷ CS01 ∷ CX31 ∷ Toff234 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ012 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ CX14 ∷ Toff213 ∷ []) (wl0939 (lit c4)) ▸
       at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 1 2 (CCZ012 ∷ CX14 ∷ []) (sym (wp0145 c4)) ▸
       at 4 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 8 2 (Toff234 ∷ CS03 ∷ []) (wp0292 c4) ▸
       at 7 2 (Toff234 ∷ CX31 ∷ []) (wl0941 (lit c4)) ▸
       at 6 2 (Toff234 ∷ CS01⁻ ∷ []) (c₂ (CS • CS • CS) (Toff)) ▸ done

  b1 : Chain (Toff234 ∷ CCZ012 ∷ CX14 ∷ Toff213 ∷ CS01 ∷ CX31 ∷ Toff234 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ CCZ012 ∷ CX14 ∷ []) (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 5 2 (Toff234 ∷ CX31 ∷ []) (wl0941 (lit c4)) ▸
       at 4 2 (Toff234 ∷ CS01 ∷ []) (c₂ (CS) (Toff)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Toff213 ∷ []) (wl0942 (lit c4)) ▸
       at 2 2 (Toff234 ∷ CX14 ∷ Toff213 ∷ []) (wl0939 (lit c4)) ▸
       at 3 3 (CX14 ∷ []) (wl0943 (lit c4)) ▸
       at 4 2 (CCZ012 ∷ CCZ013 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CX14 ∷ []) (sym (wp0145 c4)) ▸ done

  b2 : Chain (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-3410 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0565 c4)) ▸ done


-- SWbc-box @0213243140: 11 steps
lem-SWbc-box-at0213243140 : Ws → ⟪ (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-SWbc-box-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (CX41 ∷ Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ [])
  b0 = at 0 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 4 1 (CX41 ∷ CX14 ∷ CX41 ∷ []) (sym (wl0300 (lit c4))) ▸
       at 2 3 (Bx2-3410 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0213243140 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸
       at 1 3 (Bx2-3410 ∷ CCZ013 ∷ []) (lem-CXcb-box-at0213243140 c4) ▸
       at 4 2 (CX41 ∷ CCZ034 ∷ []) (wp0357 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸
       at 2 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸ done

  b1 : Chain (CX41 ∷ Bx2-3410 ∷ CX41 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (Bx2-3410 ∷ [])
  b1 = at 3 5 (CCZ034 ∷ []) (wp0568 c4) ▸
       at 0 3 (Bx2-3410 ∷ CCZ034 ∷ []) (lem-CXbc-box-at0213243140 c4) ▸
       at 1 2 [] (wp0007 c4) ▸ done


-- nat-SWbc @0213243140: 23 steps
lem-nat-SWbc-at0213243140 : Ws → ⟪ (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-nat-SWbc-at0213243140 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ Sw14 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 2 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 3 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 4 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 5 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ Sw14 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ Sw14 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Sw14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 7 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 8 2 (Toff213 ∷ Sw14 ∷ []) (wl0865 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 10 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 11 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 12 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Sw14 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Sw14 ∷ []) (Bx2-3140 ∷ [])
  b2 = at 13 2 (Toff324 ∷ Sw14 ∷ []) (wl0864 (lit c4)) ▸
       at 14 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 15 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx3-240 ∷ []) (refl) ▸
       at 5 6 (Bx3-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- sym-bc @0213243140: 2 steps
lem-sym-bc-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym-bc-at0213243140 c4 = run b0
  where
  b0 : Chain (Bx2-3410 ∷ []) (Bx2-3140 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-3410 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0213243140 c4)) ▸
       at 0 3 (Bx2-3140 ∷ []) (lem-nat-SWbc-at0213243140 c4) ▸ done


-- sym-ab @0213213440: 18 steps
lem-sym-ab-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-sym-ab-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-3140 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4) ▸
       at 4 1 (Bx2-10 ∷ []) (refl) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ [])
  b1 = at 2 6 (Bx1-240 ∷ []) (refl) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (wp0767 c4) ▸
       at 7 1 (Bx2-10 ∷ []) (refl) ▸
       at 10 1 (Bx2-10 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (Bx2-1340 ∷ [])
  b2 = at 5 6 (Bx1-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-1340 ∷ []) (refl) ▸ done


-- box-perm-2341 @021021: 4 steps
lem-box-perm-2341-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1340 ∷ []) ⟫ʷ
lem-box-perm-2341-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-1340 ∷ [])
  b0 = at 0 1 (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4) ▸
       at 0 1 (Bx2-3410 ∷ []) (lem-pairs-at0220 c4) ▸
       at 0 1 (Bx2-3140 ∷ []) (lem-sym-bc-at0213243140 c4) ▸
       at 0 1 (Bx2-1340 ∷ []) (lem-sym-ab-at0213213440 c4) ▸ done


-- cQ @02233440: 7 steps
lem-cQ-at02233440 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at02233440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 1 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done


-- box-tQ @02233440: 13 steps
lem-box-tQ-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at02233440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-1340 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ124 ∷ Toff124 ∷ CZ01 ∷ Toff124 ∷ CCZ124 ∷ CZ01 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0915 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at02233440 c4) ▸
       at 2 4 (Toff213 ∷ []) (wl0916 (lit c4)) ▸ done


-- sym-ab @02233440: 18 steps
lem-sym-ab-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-sym-ab-at02233440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx2-1340 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx1-240 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (refl) ▸
       at 2 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4) ▸
       at 4 1 (Bx2-30 ∷ []) (refl) ▸
       at 7 1 (Bx2-30 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx1-240 ∷ []) (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ [])
  b1 = at 2 6 (Bx3-240 ∷ []) (refl) ▸
       at 5 1 (CCZ124 ∷ Toff124 ∷ Bx2-10 ∷ Toff124 ∷ CCZ124 ∷ Bx2-10 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸
       at 5 6 (CCZ024 ∷ []) (sym (wp0767 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (wp0766 c4) ▸
       at 7 1 (Bx2-30 ∷ []) (refl) ▸
       at 10 1 (Bx2-30 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (Bx2-3140 ∷ [])
  b2 = at 5 6 (Bx3-240 ∷ []) (refl) ▸
       at 0 6 (Bx2-3140 ∷ []) (refl) ▸ done


-- cQ @0213213440: 7 steps
lem-cQ-at0213213440 : Ws → ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ
lem-cQ-at0213213440 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ CCZ024 ∷ []) (CCZ024 ∷ CCZ123 ∷ [])
  b0 = at 0 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 1 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 0 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 1 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸ done


-- box-tQ @0213213440: 13 steps
lem-box-tQ-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) ⟫ʷ
lem-box-tQ-at0213213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3140 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 2 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 5 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ234 ∷ Toff324 ∷ CZ03 ∷ Toff324 ∷ CCZ234 ∷ CZ03 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (sym (wp0766 c4)) ▸
       at 0 2 (Toff213 ∷ CCZ123 ∷ CZ13 ∷ []) (wl0915 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at0213213440 c4) ▸
       at 2 4 (Toff213 ∷ []) (wl0916 (lit c4)) ▸ done


-- CXbc-box @0213213440: 17 steps
lem-CXbc-box-at0213213440 : Ws → ⟪ (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX14 ∷ Bx2-3140 ∷ CX14 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX14 ∷ CCZ012 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ CX14 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at0213213440 c4) ▸
       at 0 2 (Toff213 ∷ CX14 ∷ []) (wl0944 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (sym (wp0282 c4)) ▸
       at 3 2 (Toff213 ∷ CCZ012 ∷ CCZ013 ∷ []) (wl0945 (lit c4)) ▸
       at 2 2 (Toff213 ∷ CX14 ∷ []) (wl0944 (lit c4)) ▸
       at 5 1 (CS01 ∷ CX31 ∷ CS01⁻ ∷ CX31 ∷ CS03 ∷ []) (wl0323 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 8 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CX14 ∷ CCZ012 ∷ CS01 ∷ CX31 ∷ CS01⁻ ∷ CCZ024 ∷ CX31 ∷ CS03 ∷ CX14 ∷ []) (Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ [])
  b1 = at 7 2 (CCZ024 ∷ CS01⁻ ∷ []) (sym (wp0179 c4)) ▸
       at 6 2 (CCZ024 ∷ CX31 ∷ []) (lem-comm-CX31-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0323 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CCZ012 ∷ []) (wp0142 c4) ▸
       at 3 2 (CCZ024 ∷ CX14 ∷ CCZ012 ∷ []) (sym (wp0282 c4)) ▸
       at 4 3 (CX14 ∷ []) (wp0283 c4) ▸
       at 0 4 (Bx2-3140 ∷ []) (sym (lem-box-tQ-at0213213440 c4)) ▸ done

  b2 : Chain (Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CX14 ∷ []) (Bx2-3140 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wp0565 c4)) ▸ done


-- CXcb-box @0213213440: 18 steps
lem-CXcb-box-at0213213440 : Ws → ⟪ (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ CCZ034 ∷ []) ⟫ʷ
lem-CXcb-box-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX41 ∷ Bx2-3140 ∷ CX41 ∷ []) (Toff213 ∷ CCZ024 ∷ CX41 ∷ Toff234 ∷ CS04 ∷ CX34 ∷ Toff213 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ CCZ024 ∷ CX41 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at0213213440 c4) ▸
       at 0 2 (Toff213 ∷ CX41 ∷ Toff234 ∷ []) (wl0946 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (sym (wp0768 c4)) ▸
       at 1 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸
       at 4 1 (CS04 ∷ CX34 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ []) (wp0115 c4) ▸
       at 8 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CX34 ∷ []) (wl0947 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ CX41 ∷ Toff234 ∷ CS04 ∷ CX34 ∷ Toff213 ∷ CS04⁻ ∷ CX34 ∷ CS03 ∷ CCZ024 ∷ CX41 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ [])
  b1 = at 5 2 (Toff213 ∷ CX34 ∷ []) (wl0947 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS04 ∷ []) (lem-comm-CS04-TOFF213 (lit c4)) ▸
       at 5 5 (CCZ034 ∷ []) (sym (wp0115 c4)) ▸
       at 3 2 (Toff213 ∷ Toff234 ∷ []) (sym (wl0942 (lit c4))) ▸
       at 2 2 (Toff213 ∷ CX41 ∷ Toff234 ∷ []) (wl0946 (lit c4)) ▸
       at 3 3 (CX41 ∷ []) (wl0948 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 3 2 (CCZ024 ∷ CX41 ∷ []) (sym (wp0285 c4)) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CX41 ∷ CCZ034 ∷ CX41 ∷ []) (Bx2-3140 ∷ CCZ034 ∷ [])
  b2 = at 0 4 (Bx2-3140 ∷ []) (sym (lem-box-tQ-at0213213440 c4)) ▸
       at 1 3 (CCZ034 ∷ []) (sym (wp0560 c4)) ▸ done


-- SWbc-box @0213213440: 11 steps
lem-SWbc-box-at0213213440 : Ws → ⟪ (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3140 ∷ []) ⟫ʷ
lem-SWbc-box-at0213213440 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (CX14 ∷ Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 4 1 (CX14 ∷ CX41 ∷ CX14 ∷ []) (sym (wl0423 (lit c4))) ▸
       at 2 3 (Bx2-3140 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0213213440 c4) ▸
       at 3 2 (CX41 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0567 c4) ▸
       at 1 3 (Bx2-3140 ∷ CCZ034 ∷ []) (lem-CXcb-box-at0213213440 c4) ▸
       at 4 2 (CX14 ∷ CCZ013 ∷ []) (wp0189 c4) ▸
       at 3 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸
       at 2 2 (CX14 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0566 c4) ▸ done

  b1 : Chain (CX14 ∷ Bx2-3140 ∷ CX14 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ CCZ013 ∷ []) (Bx2-3140 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wp0769 c4) ▸
       at 0 3 (Bx2-3140 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0213213440 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done


-- nat-SWbc @0213213440: 23 steps
lem-nat-SWbc-at0213213440 : Ws → ⟪ (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-nat-SWbc-at0213213440 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ Sw14 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ Sw14 ∷ [])
  b0 = at 1 1 (CCZ123 ∷ Toff213 ∷ Bx3-240 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ []) (refl) ▸
       at 0 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 1 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 3 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 2 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 3 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 4 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 5 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ Sw14 ∷ CCZ234 ∷ Bx2-30 ∷ Toff213 ∷ CCZ123 ∷ Bx3-240 ∷ Sw14 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Sw14 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Sw14 ∷ [])
  b1 = at 6 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 7 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 8 2 (Toff234 ∷ Sw14 ∷ []) (wl0857 (lit c4)) ▸
       at 9 2 (CCZ234 ∷ Sw14 ∷ []) (sym (wl0856 (lit c4))) ▸
       at 11 1 (CCZ234 ∷ Toff324 ∷ Bx2-30 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ []) (refl) ▸
       at 10 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 11 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 12 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ Toff234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Sw14 ∷ Toff324 ∷ CCZ234 ∷ Bx2-30 ∷ Sw14 ∷ []) (Bx2-3410 ∷ [])
  b2 = at 13 2 (Toff312 ∷ Sw14 ∷ []) (wl0855 (lit c4)) ▸
       at 14 2 (CCZ123 ∷ Sw14 ∷ []) (sym (wl0854 (lit c4))) ▸
       at 15 2 (Bx2-30 ∷ Sw14 ∷ []) (lem-comm-SWAP14-BOX⟨2·30⟩ (lit c4)) ▸
       at 16 2 [] (wl0306 (lit c4)) ▸
       at 2 6 (Bx3-210 ∷ []) (refl) ▸
       at 5 6 (Bx3-210 ∷ []) (refl) ▸
       at 0 6 (Bx2-3410 ∷ []) (refl) ▸ done


-- sym-bc @0213213440: 2 steps
lem-sym-bc-at0213213440 : Ws → ⟪ (Bx2-3140 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-sym-bc-at0213213440 c4 = run b0
  where
  b0 : Chain (Bx2-3140 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 0 1 (Sw14 ∷ Bx2-3140 ∷ Sw14 ∷ []) (sym (lem-SWbc-box-at0213213440 c4)) ▸
       at 0 3 (Bx2-3410 ∷ []) (lem-nat-SWbc-at0213213440 c4) ▸ done


-- tP @0213243140: 7 steps
lem-tP-at0213243140 : Ws → ⟪ (Toff234 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ []) ⟫ʷ
lem-tP-at0213243140 c4 = run b0
  where
  b0 : Chain (Toff234 ∷ Toff201 ∷ []) (Toff201 ∷ Toff234 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ234 ∷ K2⁻ ∷ []) (sym (wl0417 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ012 ∷ K2⁻ ∷ []) (sym (wl0416 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ012 ∷ CCZ234 ∷ []) (lem-cQ-at0213243140 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff201 ∷ []) (wl0416 (lit c4)) ▸
       at 1 3 (Toff234 ∷ []) (wl0417 (lit c4)) ▸ done


-- P-box @0213243140: 8 steps
lem-P-box-at0213243140 : Ws → ⟪ (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-3410 ∷ []) ⟫ʷ
lem-P-box-at0213243140 c4 = run b0
  where
  b0 : Chain (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) (Bx2-3410 ∷ [])
  b0 = at 1 1 (Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ012 ∷ []) (lem-box-tQ-at0213243140 c4) ▸
       at 0 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0213243140 c4)) ▸
       at 1 2 (CCZ012 ∷ CZ01 ∷ Toff201 ∷ []) (sym (wl0949 (lit c4))) ▸
       at 3 2 (Toff234 ∷ Toff201 ∷ []) (sym (lem-tP-at0213243140 c4)) ▸
       at 4 3 (CCZ012 ∷ CZ01 ∷ []) (sym (wl0950 (lit c4))) ▸
       at 2 2 (Toff234 ∷ CZ01 ∷ []) (c₂ (CZ) (Toff)) ▸
       at 3 3 (CCZ012 ∷ []) (sym (wl0951 (lit c4))) ▸
       at 0 4 (Bx2-3410 ∷ []) (sym (lem-box-tQ-at0213243140 c4)) ▸ done


-- VPQ @0213243140: 14 steps
lem-VPQ-at0213243140 : Ws → ⟪ (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ []) ⟫ʷ
lem-VPQ-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS34⁻ ∷ S2 ∷ Toff234 ∷ S2⁻ ∷ []) (sym (wl0419 (lit c4))) ▸
       at 4 2 (CS01⁻ ∷ S2 ∷ Toff201 ∷ S2⁻ ∷ []) (sym (wl0418 (lit c4))) ▸
       at 3 2 (CS01⁻ ∷ S2⁻ ∷ []) (sym (c₂ (CS • CS • CS) (S • S • S))) ▸
       at 2 2 (CS01⁻ ∷ Toff234 ∷ []) (sym (c₂ (CS • CS • CS) (Toff))) ▸
       at 1 2 (CS01⁻ ∷ S2 ∷ []) (sym (c₂ (CS • CS • CS) (S))) ▸
       at 0 2 (CS01⁻ ∷ CS34⁻ ∷ []) (sym (c₂ (CS • CS • CS) ((CS • CS • CS) ↑))) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243140 c4) ▸ done

  b1 : Chain (CS01⁻ ∷ CS34⁻ ∷ S2 ∷ Toff201 ∷ Toff234 ∷ S2⁻ ∷ []) (Toff201 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS34⁻ ∷ []) (sym (c₃ (S ↑ ↑) (CS • CS • CS))) ▸
       at 2 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸
       at 3 2 (S2⁻ ∷ CS34⁻ ∷ []) (sym (c₃ ((S • S • S) ↑ ↑) (CS • CS • CS))) ▸
       at 0 4 (Toff201 ∷ CCZ012 ∷ []) (wl0418 (lit c4)) ▸
       at 2 4 (Toff234 ∷ CCZ234 ∷ []) (wl0419 (lit c4)) ▸ done


-- QVQ @0213243140: 3 steps
lem-QVQ-at0213243140 : Ws → ⟪ (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) ⟫ʷ ≈ ⟪ (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-QVQ-at0213243140 c4 = run b0
  where
  b0 : Chain (CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ012 ∷ []) (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ [])
  b0 = at 0 0 (Toff201 ∷ Toff201 ∷ []) (sym (wl0421 (lit c4))) ▸
       at 1 4 (Toff234 ∷ CCZ234 ∷ Toff201 ∷ CCZ012 ∷ []) (sym (lem-VPQ-at0213243140 c4)) ▸
       at 4 2 [] (wl0341 (lit c4)) ▸ done


-- box-cP @0213243140: 12 steps
lem-box-cP-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) ⟫ʷ
lem-box-cP-at0213243140 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-3410 ∷ []) (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ [])
  b0 = at 0 1 (CCZ234 ∷ Toff234 ∷ Bx3-210 ∷ Toff234 ∷ CCZ234 ∷ Bx3-210 ∷ []) (refl) ▸
       at 2 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 4 1 (CZ03 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 2 6 (CCZ012 ∷ []) (sym (wl0935 (lit c4))) ▸
       at 5 1 (CCZ123 ∷ Toff312 ∷ Bx2-30 ∷ Toff312 ∷ CCZ123 ∷ Bx2-30 ∷ []) (refl) ▸
       at 7 1 (CZ03 ∷ []) (refl) ▸
       at 10 1 (CZ03 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ234 ∷ Toff234 ∷ CCZ012 ∷ Toff234 ∷ CCZ234 ∷ CCZ123 ∷ Toff312 ∷ CZ03 ∷ Toff312 ∷ CCZ123 ∷ CZ03 ∷ []) (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ [])
  b1 = at 5 6 (CCZ012 ∷ []) (sym (wl0935 (lit c4))) ▸
       at 2 4 (Toff201 ∷ Toff234 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-QVQ-at0213243140 c4) ▸
       at 1 2 (Toff201 ∷ Toff234 ∷ []) (lem-tP-at0213243140 c4) ▸
       at 2 2 [] (wl0420 (lit c4)) ▸ done


-- pairs @0213243140: 4 steps
lem-pairs-at0213243140 : Ws → ⟪ (Bx2-3410 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-pairs-at0213243140 c4 = run b0
  where
  b0 : Chain (Bx2-3410 ∷ []) (Bx2-1034 ∷ [])
  b0 = at 0 1 (Toff201 ∷ Bx2-3410 ∷ Toff201 ∷ []) (sym (lem-P-box-at0213243140 c4)) ▸
       at 1 1 (CCZ234 ∷ Toff201 ∷ CCZ234 ∷ Toff201 ∷ []) (lem-box-cP-at0213243140 c4) ▸
       at 4 2 [] (wl0421 (lit c4)) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done


-- box-perm-4123 @02233440: 4 steps
lem-box-perm-4123-at02233440 : Ws → ⟪ (Bx2-1340 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0134 ∷ []) ⟫ʷ
lem-box-perm-4123-at02233440 c4 = run b0
  where
  b0 : Chain (Bx2-1340 ∷ []) (Bx2-0134 ∷ [])
  b0 = at 0 1 (Bx2-3140 ∷ []) (lem-sym-ab-at02233440 c4) ▸
       at 0 1 (Bx2-3410 ∷ []) (lem-sym-bc-at0213213440 c4) ▸
       at 0 1 (Bx2-1034 ∷ []) (lem-pairs-at0213243140 c4) ▸
       at 0 1 (Bx2-0134 ∷ []) (lem-sym-ab-at0220 c4) ▸ done

