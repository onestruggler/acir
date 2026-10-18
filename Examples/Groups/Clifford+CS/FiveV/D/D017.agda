{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D017 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0004 ; wl0157 ; wl0159 ; wl0171 ; wl0172 ; wl0173 ; wl0174 ; wl0175 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0180 ; wl0181 ; wl0183 ; wl0185 ; wl0186 ; wl0209 ; wl0210 ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0226 ; wl0227 ; wl0228 ; wl0229 ; wl0230 ; wl0231 ; wl0233 ; wl0234 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0263 ; wl0297 ; wl0305 ; wl0327 ; wl0464 ; wl0547 ; wl0649 ; wl0651 ; wl0682 ; wl0683 ; wl0684 ; wl0720 ; wl0725 ; wl0735 ; wl0743 ; wl0763 ; wl0764 ; wl0765 ; wl0770 ; wl0905 ; wl1000 ; wl1008 ; wl1037 ; wl1074 ; wl1139 ; wl1140 ; wl1141 ; wl1142 ; wl1143 ; wl1144 ; wl1145 ; wl1146 ; wl1147 ; wl1148 ; wl1149 ; wl1150 ; wl1151 ; wl1152 ; wl1153 ; wl1154 ; wl1155 ; wl1156 ; wl1157 ; wl1158 ; wp0013 ; wp0014 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0019 ; wp0020 ; wp0023 ; wp0024 ; wp0025 ; wp0026 ; wp0034 ; wp0035 ; wp0036 ; wp0039 ; wp0041 ; wp0053 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0067 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0078 ; wp0079 ; wp0080 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0092 ; wp0094 ; wp0095 ; wp0097 ; wp0127 ; wp0161 ; wp0214 ; wp0314 ; wp0523 ; wp0527 ; wp0528 ; wp0529 ; wp0530 ; wp0617 ; wp0632 ; wp0633 ; wp0647 ; wp0756 ; wp0796 ; wp0797 ; wp0798 ; wp0805 ; wp0806 ; wp0810 ; wp0812 ; wp0813 ; wp0842 ; wp0843 ; wp0845 ; wp0908 ; wp0909 ; wp0913 ; wp0915 ; wp0916 ; wp0917 ; wp0918 ; wp0919 ; wp0924 ; wp0933 ; wp0934 ; wp0935 ; wp0936 ; wp0937 ; wp0938 ; wp0939 ; wp0940 ; wp0941 ; wp0942 ; wp0943 ; wp0944 ; wp0945 ; wp0946 ; wp0947 ; wp0948 ; wp0949 ; wp0950)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-Xb-box-at122441 ; lem-box-cP-at122441 ; lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D002 using (lem-box-tQ-at13213442 ; lem-box-tQ-at1441 ; lem-cQ-at1441 ; lem-pairs-at13213442 ; lem-sym-bc-at13243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D003 using (lem-box-tQ-at12233441)
open import Examples.Groups.Clifford+CS.FiveV.D.D004 using (lem-box-cP-at13243142 ; lem-sym-bc-at13213442)
open import Examples.Groups.Clifford+CS.FiveV.D.D006 using (lem-box-perm-1324-at122441 ; lem-box-tQ-at0210233441)
open import Examples.Groups.Clifford+CS.FiveV.D.D007 using (lem-sym-ab-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D012 using (lem-pairs-at12233441 ; lem-sym-ab-at14213243)
open import Examples.Groups.Clifford+CS.FiveV.D.D014 using (lem-S2-SBOX⟨0·1·42·3⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D015 using (lem-S2-SBOX⟨0·2·43·1⟩)
open import Examples.Groups.Clifford+CS.FiveV.D.D016 using (lem-box-perm-1324-at12233441 ; lem-box-perm-3421-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd04-TOFF213 ; lem-comm-CSd13-CCZ024 ; lem-comm-CX04-CCZ123 ; lem-comm-CZ04-CCZ123 ; lem-comm-TOFF204-CSd13)
open import Examples.Groups.Clifford+CS.FiveV.D.R002 using (lem-comm-CSd24-TOFF013 ; lem-comm-TOFF024-CSd13)
open import Examples.Groups.Clifford+CS.FiveV.D.R003 using (lem-comm-CS12-CCZ034 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CS13-TOFF204 ; lem-comm-CSd13-TOFF204 ; lem-comm-CSd14-TOFF203 ; lem-comm-CX03-CCZ124 ; lem-comm-CZ13-TOFF024 ; lem-comm-TOFF013-CK42 ; lem-comm-TOFF023-CK41)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ024-CX31 ; lem-comm-CS14-TOFF203 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF023-CS14 ; lem-comm-TOFF023-CX14)
-- CKc-box @12233441: 61 steps
lem-CKc-box-at12233441 : Ws → ⟪ (Bx0-2341 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) ⟫ʷ
lem-CKc-box-at12233441 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-2341 ∷ CK41 ∷ []) (X4 ∷ Bx0-2341 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-box-perm-1324-at12233441 c4) ▸
       at 0 2 (X4 ∷ Bx0-2431 ∷ X4 ∷ []) (sym (lem-Xb-box-at122441 c4)) ▸
       at 3 2 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1139 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K1 ∷ CK41 ∷ S4 ∷ X4 ∷ []) (sym (wl0720 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-2341 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at12233441 c4) ▸
       at 5 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 4 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ CCZ014 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CCZ014 ∷ CS12 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ []) (wp0933 c4) ▸
       at 8 2 (CZ01 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ []) (wp0934 c4) ▸
       at 11 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 13 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 12 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CCZ014 ∷ CS12 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ014 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 5 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wp0935 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 4 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 5 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 7 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff023 ∷ CCZ014 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 2 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 2 (K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ []) (wp0933 c4) ▸ done

  b5 : Chain (X4 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ01 ∷ CK41 ∷ CZ01 ∷ CCZ014 ∷ []) (wp0934 c4) ▸
       at 9 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 11 1 (CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ []) (wl0233 (lit c4)) ▸
       at 10 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸ done

  b6 : Chain (X4 ∷ Toff023 ∷ CCZ123 ∷ K1 ∷ Toff104 ∷ CCZ014 ∷ CZ01 ∷ CK41 ∷ CZ01 ∷ S4 ∷ CS13 ∷ CX23 ∷ CS13⁻ ∷ CX23 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Bx0-2341 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0233 (lit c4))) ▸
       at 3 7 (K1 ∷ CK41 ∷ S4 ∷ []) (sym (wp0935 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 2 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 3 2 (CK41 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CK41 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff023 ∷ []) (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (S)) ▸
       at 5 2 (CCZ123 ∷ Toff023 ∷ []) (sym (wl0209 (lit c4))) ▸
       at 6 4 (Bx0-2341 ∷ []) (sym (lem-box-tQ-at12233441 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K1 ∷ CK41 ∷ S4 ∷ CCZ123 ∷ Bx0-2341 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ [])
  b7 = at 6 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 0 6 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1140 (lit c4))) ▸
       at 3 3 (Bx0-2431 ∷ CCZ123 ∷ []) (lem-Xb-box-at122441 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸ done


-- box-perm-4312 @12233441: 2 steps
lem-box-perm-4312-at12233441 : Ws → ⟪ (Bx0-2341 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1423 ∷ []) ⟫ʷ
lem-box-perm-4312-at12233441 c4 = run b0
  where
  b0 : Chain (Bx0-2341 ∷ []) (Bx0-1423 ∷ [])
  b0 = at 0 1 (Bx0-4123 ∷ []) (lem-pairs-at12233441 c4) ▸
       at 0 1 (Bx0-1423 ∷ []) (lem-sym-ab-at14213243 c4) ▸ done


-- nf-X-CS0@1: 115 steps
lem-nf-X-CS0at1 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-1423 ∷ []) ⟫ʷ
lem-nf-X-CS0at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b0 = at 0 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨0·1·42·3⟩ c4) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b1 : Chain (CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b2 : Chain (CCZ124 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b2 = at 2 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 3 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 4 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b3 : Chain (CCZ124 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b3 = at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 3 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b4 : Chain (CCZ124 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b4 = at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸ done

  b5 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b5 = at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b6 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b7 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b7 = at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b8 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b8 = at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b9 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b9 = at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸ done

  b10 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS14 ∷ CCZ014 ∷ Toff023 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b10 = at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 7 1 (Bx0-2341 ∷ []) (lem-box-perm-3421-at243243 c4) ▸
       at 7 2 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) (lem-CKc-box-at12233441 c4) ▸
       at 10 1 (Bx0-1423 ∷ []) (lem-box-perm-4312-at12233441 c4) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 13 2 (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ014 ∷ []) (wp0908 c4) ▸ done

  b11 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ014 ∷ Toff023 ∷ CS14 ∷ CCZ014 ∷ Toff023 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CS14 ∷ CS14 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b11 = at 11 2 (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ014 ∷ []) (wp0908 c4) ▸
       at 11 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 14 2 (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ014 ∷ []) (wp0908 c4) ▸
       at 12 2 (CS14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CS14 (lit c4)) ▸
       at 11 2 (CS14 ∷ CCZ014 ∷ []) (wp0908 c4) ▸ done

  b12 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CS14 ∷ CS14 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CS14 ∷ CS14 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ014 ∷ S4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS24 ∷ [])
  b12 = at 12 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 12 1 (Bx0-2341 ∷ []) (lem-box-perm-3421-at243243 c4) ▸
       at 12 2 (CCZ123 ∷ CK41 ∷ CCZ123 ∷ Bx0-2341 ∷ []) (lem-CKc-box-at12233441 c4) ▸
       at 15 1 (Bx0-1423 ∷ []) (lem-box-perm-4312-at12233441 c4) ▸
       at 15 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 18 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸
       at 17 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 16 2 (S4 ∷ Toff023 ∷ []) (sym (wp0632 c4)) ▸ done

  b13 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CS14 ∷ CS14 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CCZ014 ∷ S4 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS24 ∷ []) (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CS14 ∷ CS14 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-1423 ∷ [])
  b13 = at 15 2 (S4 ∷ CCZ014 ∷ []) (wp0633 c4) ▸
       at 16 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 16 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 19 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 18 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 17 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 16 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 17 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b14 : Chain (CCZ124 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ CS14 ∷ CS14 ∷ CCZ123 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-1423 ∷ []) (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ Bx0-1423 ∷ [])
  b14 = at 0 2 [] (wl0263 (lit c4)) ▸
       at 7 3 (CS14 ∷ CS14 ∷ CCZ123 ∷ []) (wl1141 (lit c4)) ▸
       at 9 2 [] (wl0181 (lit c4)) ▸ done


-- F1-X-CS0@1: 86 steps
lem-F1-X-CS0at1 : Ws → ⟪ (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) ⟫ʷ
lem-F1-X-CS0at1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ []) (CX41 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 0 5 (CX41 ∷ []) (wl1142 (lit c4)) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 3 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b1 : Chain (CX41 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b2 : Chain (CX41 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 2 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 4 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 3 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 4 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b3 : Chain (CX41 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 4 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 1 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 2 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 3 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 4 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b4 : Chain (CX41 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 2 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸ done

  b5 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ [])
  b5 = at 4 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 3 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 6 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b6 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 10 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 12 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b7 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b7 = at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 7 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 9 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 7 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b8 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ [])
  b8 = at 5 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b9 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ []) (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ [])
  b9 = at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 5 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 8 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸ done

  b10 : Chain (CX41 ∷ CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ [])
  b10 = at 6 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸
       at 0 5 (Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ123 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ CCZ123 ∷ S4 ∷ CS24 ∷ []) (wl1143 (lit c4)) ▸
       at 0 14 (Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ CS14 ∷ CS14 ∷ CK41 ∷ S4 ∷ CS24 ∷ []) (sym (lem-nf-X-CS0at1 c4)) ▸ done


-- tP @1441: 7 steps
lem-tP-at1441 : Ws → ⟪ (Toff024 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ []) ⟫ʷ
lem-tP-at1441 c4 = run b0
  where
  b0 : Chain (Toff024 ∷ Toff013 ∷ []) (Toff013 ∷ Toff024 ∷ [])
  b0 = at 0 1 (K0 ∷ CCZ024 ∷ K0⁻ ∷ []) (sym (wp0078 c4)) ▸
       at 3 1 (K0 ∷ CCZ013 ∷ K0⁻ ∷ []) (sym (wl0226 (lit c4))) ▸
       at 2 2 [] (wl0157 (lit c4)) ▸
       at 1 2 (CCZ013 ∷ CCZ024 ∷ []) (lem-cQ-at1441 c4) ▸
       at 2 0 (K0⁻ ∷ K0 ∷ []) (sym (wl0157 (lit c4))) ▸
       at 0 3 (Toff013 ∷ []) (wl0226 (lit c4)) ▸
       at 1 3 (Toff024 ∷ []) (wp0078 c4) ▸ done


-- P-box @1441: 8 steps
lem-P-box-at1441 : Ws → ⟪ (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-4231 ∷ []) ⟫ʷ
lem-P-box-at1441 c4 = run b0
  where
  b0 : Chain (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) (Bx0-4231 ∷ [])
  b0 = at 1 1 (Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ013 ∷ []) (lem-box-tQ-at1441 c4) ▸
       at 0 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at1441 c4)) ▸
       at 1 2 (CCZ013 ∷ CZ13 ∷ Toff013 ∷ []) (sym (wl0682 (lit c4))) ▸
       at 3 2 (Toff024 ∷ Toff013 ∷ []) (sym (lem-tP-at1441 c4)) ▸
       at 4 3 (CCZ013 ∷ CZ13 ∷ []) (sym (wl0683 (lit c4))) ▸
       at 2 2 (Toff024 ∷ CZ13 ∷ []) (lem-comm-CZ13-TOFF024 (lit c4)) ▸
       at 3 3 (CCZ013 ∷ []) (sym (wl0684 (lit c4))) ▸
       at 0 4 (Bx0-4231 ∷ []) (sym (lem-box-tQ-at1441 c4)) ▸ done


-- VPQ @1441: 14 steps
lem-VPQ-at1441 : Ws → ⟪ (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ [])
  b0 = at 0 2 (CS24⁻ ∷ S0 ∷ Toff024 ∷ S0⁻ ∷ []) (sym (wp0079 c4)) ▸
       at 4 2 (CS13⁻ ∷ S0 ∷ Toff013 ∷ S0⁻ ∷ []) (sym (wl0227 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S0⁻ ∷ []) (c₁ (S • S • S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 2 2 (CS13⁻ ∷ Toff024 ∷ []) (lem-comm-TOFF024-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S0 ∷ []) (c₁ (S) (Swap ↑ • (CS • CS • CS) • Swap ↑)) ▸
       at 0 2 (CS13⁻ ∷ CS24⁻ ∷ []) (sym (wl0228 (lit c4))) ▸
       at 4 2 [] (wl0159 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at1441 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS24⁻ ∷ S0 ∷ Toff013 ∷ Toff024 ∷ S0⁻ ∷ []) (Toff013 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S0⁻ ∷ S0 ∷ []) (sym (wl0159 (lit c4))) ▸
       at 1 2 (S0 ∷ CS24⁻ ∷ []) (sym (c₁ (S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 2 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 3 2 (S0⁻ ∷ CS24⁻ ∷ []) (sym (c₁ (S • S • S) (Swap ↑ ↑ • ((CS • CS • CS) ↑) • Swap ↑ ↑))) ▸
       at 0 4 (Toff013 ∷ CCZ013 ∷ []) (wl0227 (lit c4)) ▸
       at 2 4 (Toff024 ∷ CCZ024 ∷ []) (wp0079 c4) ▸ done


-- QVQ @1441: 3 steps
lem-QVQ-at1441 : Ws → ⟪ (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) ⟫ʷ ≈ ⟪ (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-QVQ-at1441 c4 = run b0
  where
  b0 : Chain (CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ013 ∷ []) (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ [])
  b0 = at 0 0 (Toff013 ∷ Toff013 ∷ []) (sym (wl0229 (lit c4))) ▸
       at 1 4 (Toff024 ∷ CCZ024 ∷ Toff013 ∷ CCZ013 ∷ []) (sym (lem-VPQ-at1441 c4)) ▸
       at 4 2 [] (wl0230 (lit c4)) ▸ done


-- box-cP @1441: 12 steps
lem-box-cP-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) ⟫ʷ
lem-box-cP-at1441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx0-4231 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ013 ∷ Toff024 ∷ CCZ024 ∷ CCZ034 ∷ Toff403 ∷ CZ14 ∷ Toff403 ∷ CCZ034 ∷ CZ14 ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b1 = at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 2 4 (Toff013 ∷ Toff024 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-QVQ-at1441 c4) ▸
       at 1 2 (Toff013 ∷ Toff024 ∷ []) (lem-tP-at1441 c4) ▸
       at 2 2 [] (wp0080 c4) ▸ done


-- pairs @1441: 4 steps
lem-pairs-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-pairs-at1441 c4 = run b0
  where
  b0 : Chain (Bx0-4231 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Toff013 ∷ Bx0-4231 ∷ Toff013 ∷ []) (sym (lem-P-box-at1441 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at1441 c4) ▸
       at 4 2 [] (wl0229 (lit c4)) ▸
       at 0 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸ done


-- box-perm-3421 @122441: 2 steps
lem-box-perm-3421-at122441 : Ws → ⟪ (Bx0-2431 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-3421-at122441 c4 = run b0
  where
  b0 : Chain (Bx0-2431 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-sym-ab-at122441 c4) ▸
       at 0 1 (Bx0-3142 ∷ []) (lem-pairs-at1441 c4) ▸ done


-- box-perm-1324 @13213442: 1 steps
lem-box-perm-1324-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ []) ⟫ʷ
lem-box-perm-1324-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-3412 ∷ [])
  b0 = at 0 1 (Bx0-3412 ∷ []) (lem-sym-bc-at13213442 c4) ▸ done


-- Xb-box @13243142: 18 steps
lem-Xb-box-at13243142 : Ws → ⟪ (X4 ∷ Bx0-3412 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3412 ∷ CCZ123 ∷ []) ⟫ʷ
lem-Xb-box-at13243142 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx0-3412 ∷ X4 ∷ []) (CCZ034 ∷ Toff012 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX31 ∷ CCZ034 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff012 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ []) (lem-box-cP-at13243142 c4) ▸
       at 0 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 2 2 (Toff012 ∷ CZ03 ∷ CCZ123 ∷ []) (wl1074 (lit c4)) ▸
       at 1 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸
       at 4 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS23 ∷ []) (sym (wp0314 c4)) ▸
       at 7 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸ done

  b1 : Chain (CCZ034 ∷ Toff012 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX31 ∷ CCZ034 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ Toff012 ∷ X4 ∷ []) (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ CCZ123 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ034 ∷ CX31 ∷ []) (sym (wp0127 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 3 3 (X4 ∷ []) (wp0798 c4) ▸
       at 4 2 (Toff012 ∷ CCZ123 ∷ []) (wl0464 (lit c4)) ▸
       at 3 2 (Toff012 ∷ X4 ∷ []) (sym (c₃ (Toff) (X ↑))) ▸ done

  b2 : Chain (CCZ034 ∷ Toff012 ∷ CCZ034 ∷ Toff012 ∷ X4 ∷ CCZ123 ∷ X4 ∷ []) (Bx0-3412 ∷ CCZ123 ∷ [])
  b2 = at 0 4 (Bx0-3412 ∷ []) (sym (lem-box-cP-at13243142 c4)) ▸
       at 1 3 (CCZ123 ∷ []) (sym (wl0210 (lit c4))) ▸ done


-- box-perm-1324 @13243142: 1 steps
lem-box-perm-1324-at13243142 : Ws → ⟪ (Bx0-3412 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-3142 ∷ []) ⟫ʷ
lem-box-perm-1324-at13243142 c4 = run b0
  where
  b0 : Chain (Bx0-3412 ∷ []) (Bx0-3142 ∷ [])
  b0 = at 0 1 (Bx0-3142 ∷ []) (lem-sym-bc-at13243142 c4) ▸ done


-- CKc-box @13213442: 61 steps
lem-CKc-box-at13213442 : Ws → ⟪ (Bx0-3142 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) ⟫ʷ
lem-CKc-box-at13213442 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (run b7)))))))
  where
  b0 : Chain (Bx0-3142 ∷ CK42 ∷ []) (X4 ∷ Bx0-3142 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b0 = at 1 0 (CCZ123 ∷ CCZ123 ∷ []) (sym (wl0181 (lit c4))) ▸
       at 0 1 (Bx0-3412 ∷ []) (lem-box-perm-1324-at13213442 c4) ▸
       at 0 2 (X4 ∷ Bx0-3412 ∷ X4 ∷ []) (sym (lem-Xb-box-at13243142 c4)) ▸
       at 3 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ123 ∷ []) (sym (wl1144 (lit c4))) ▸
       at 2 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 3 2 (K2 ∷ CK42 ∷ S4 ∷ X4 ∷ []) (sym (wl0725 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ X4 ∷ []) (sym (c₄ (CCZ ↑) (X))) ▸
       at 1 1 (Bx0-3142 ∷ []) (lem-box-perm-1324-at13243142 c4) ▸ done

  b1 : Chain (X4 ∷ Bx0-3142 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ [])
  b1 = at 1 1 (Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ []) (lem-box-tQ-at13213442 c4) ▸
       at 5 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 5 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 8 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 4 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸ done

  b2 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ CCZ024 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CCZ024 ∷ CS23 ∷ X4 ∷ CCZ123 ∷ [])
  b2 = at 5 2 (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0936 c4) ▸
       at 8 2 (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0937 c4) ▸
       at 11 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 13 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 12 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 13 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 14 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 15 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CCZ024 ∷ CS23 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b3 = at 16 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 12 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 5 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wp0938 c4)) ▸
       at 3 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 4 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 5 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 6 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 7 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b4 = at 3 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 2 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 3 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 4 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 5 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸
       at 2 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 2 (K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ []) (wp0936 c4) ▸ done

  b5 : Chain (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CCZ024 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ [])
  b5 = at 6 2 (CZ02 ∷ CK42 ∷ CZ02 ∷ CCZ024 ∷ []) (wp0937 c4) ▸
       at 9 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 11 1 (CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ []) (wl0297 (lit c4)) ▸
       at 10 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 11 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 12 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 13 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 14 2 (CS23 ∷ CCZ024 ∷ []) (wp0092 c4) ▸ done

  b6 : Chain (X4 ∷ Toff013 ∷ CCZ123 ∷ K2 ∷ Toff204 ∷ CCZ024 ∷ CZ02 ∷ CK42 ∷ CZ02 ∷ S4 ∷ CS12 ∷ CX31 ∷ CS12⁻ ∷ CX31 ∷ CS23 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CCZ123 ∷ []) (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Bx0-3142 ∷ X4 ∷ CCZ123 ∷ [])
  b6 = at 10 5 (CCZ123 ∷ []) (sym (wl0297 (lit c4))) ▸
       at 3 7 (K2 ∷ CK42 ∷ S4 ∷ []) (sym (wp0938 c4)) ▸
       at 1 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 2 2 (K2 ∷ Toff013 ∷ []) (sym (wl0743 (lit c4))) ▸
       at 3 2 (CK42 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CK42 (lit c4)) ▸
       at 4 2 (S4 ∷ Toff013 ∷ []) (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (S)) ▸
       at 5 2 (CCZ123 ∷ Toff013 ∷ []) (sym (wl0234 (lit c4))) ▸
       at 6 4 (Bx0-3142 ∷ []) (sym (lem-box-tQ-at13213442 c4)) ▸ done

  b7 : Chain (X4 ∷ CCZ123 ∷ K2 ∷ CK42 ∷ S4 ∷ CCZ123 ∷ Bx0-3142 ∷ X4 ∷ CCZ123 ∷ []) (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ [])
  b7 = at 6 1 (Bx0-3412 ∷ []) (sym (lem-box-perm-1324-at13243142 c4)) ▸
       at 0 6 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ X4 ∷ []) (sym (wl1145 (lit c4))) ▸
       at 3 3 (Bx0-3412 ∷ CCZ123 ∷ []) (lem-Xb-box-at13243142 c4) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸
       at 3 1 (Bx0-3142 ∷ []) (lem-box-perm-1324-at13243142 c4) ▸ done


-- sym-ab @1441: 18 steps
lem-sym-ab-at1441 : Ws → ⟪ (Bx0-4231 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-sym-ab-at1441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Bx0-4231 ∷ []) (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff024 ∷ Bx4-031 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (refl) ▸
       at 2 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 4 1 (CZ14 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 2 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 2 1 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4)) ▸
       at 4 1 (Bx0-21 ∷ []) (refl) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ Toff024 ∷ CCZ024 ∷ Bx4-031 ∷ []) (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ [])
  b1 = at 2 6 (Bx2-031 ∷ []) (refl) ▸
       at 5 1 (CCZ034 ∷ Toff403 ∷ Bx0-41 ∷ Toff403 ∷ CCZ034 ∷ Bx0-41 ∷ []) (refl) ▸
       at 7 1 (CZ14 ∷ []) (refl) ▸
       at 10 1 (CZ14 ∷ []) (refl) ▸
       at 5 6 (CCZ013 ∷ []) (sym (wp0214 c4)) ▸
       at 5 1 (CCZ023 ∷ Toff203 ∷ CZ12 ∷ Toff203 ∷ CCZ023 ∷ CZ12 ∷ []) (wl0231 (lit c4)) ▸
       at 7 1 (Bx0-21 ∷ []) (refl) ▸
       at 10 1 (Bx0-21 ∷ []) (refl) ▸ done

  b2 : Chain (CCZ024 ∷ Toff024 ∷ Bx2-031 ∷ Toff024 ∷ CCZ024 ∷ CCZ023 ∷ Toff203 ∷ Bx0-21 ∷ Toff203 ∷ CCZ023 ∷ Bx0-21 ∷ []) (Bx0-2431 ∷ [])
  b2 = at 5 6 (Bx2-031 ∷ []) (refl) ▸
       at 0 6 (Bx0-2431 ∷ []) (refl) ▸ done


-- box-perm-4312 @13213442: 2 steps
lem-box-perm-4312-at13213442 : Ws → ⟪ (Bx0-3142 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-4312-at13213442 c4 = run b0
  where
  b0 : Chain (Bx0-3142 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-4231 ∷ []) (lem-pairs-at13213442 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-sym-ab-at1441 c4) ▸ done


-- nf-X-CS0@2: 115 steps
lem-nf-X-CS0at2 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ Bx0-2431 ∷ []) ⟫ʷ
lem-nf-X-CS0at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (run b14))))))))))))))
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b0 = at 0 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b1 : Chain (CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b1 = at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b2 : Chain (CCZ234 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b2 = at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b3 : Chain (CCZ234 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b3 = at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CCZ234 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b5 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b5 = at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b6 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b7 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b7 = at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b8 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b8 = at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b10 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CS24 ∷ CCZ024 ∷ Toff013 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b10 = at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 7 1 (Bx0-3142 ∷ []) (lem-box-perm-3421-at122441 c4) ▸
       at 7 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) (lem-CKc-box-at13213442 c4) ▸
       at 10 1 (Bx0-2431 ∷ []) (lem-box-perm-4312-at13213442 c4) ▸
       at 10 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 13 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ024 ∷ []) (wp0909 c4) ▸ done

  b11 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ Toff013 ∷ CS24 ∷ CCZ024 ∷ Toff013 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b11 = at 11 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ024 ∷ []) (wp0909 c4) ▸
       at 11 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 14 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 13 2 (CS24 ∷ CCZ024 ∷ []) (wp0909 c4) ▸
       at 12 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 11 2 (CS24 ∷ CCZ024 ∷ []) (wp0909 c4) ▸ done

  b12 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ S4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ [])
  b12 = at 12 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 12 1 (Bx0-3142 ∷ []) (lem-box-perm-3421-at122441 c4) ▸
       at 12 2 (CCZ123 ∷ CK42 ∷ CCZ123 ∷ Bx0-3142 ∷ []) (lem-CKc-box-at13213442 c4) ▸
       at 15 1 (Bx0-2431 ∷ []) (lem-box-perm-4312-at13213442 c4) ▸
       at 15 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 18 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸
       at 17 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 2 (S4 ∷ Toff013 ∷ []) (sym (wp0647 c4)) ▸ done

  b13 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CCZ024 ∷ S4 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS34 ∷ []) (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b13 = at 15 2 (S4 ∷ CCZ024 ∷ []) (wp0617 c4) ▸
       at 16 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 16 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 19 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 18 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 17 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 16 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 17 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b14 : Chain (CCZ234 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ CS24 ∷ CS24 ∷ CCZ123 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ Bx0-2431 ∷ []) (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ Bx0-2431 ∷ [])
  b14 = at 0 2 [] (wl0305 (lit c4)) ▸
       at 7 3 (CS24 ∷ CS24 ∷ CCZ123 ∷ []) (wl1146 (lit c4)) ▸
       at 9 2 [] (wl0181 (lit c4)) ▸ done


-- F1-X-CS0@2: 86 steps
lem-F1-X-CS0at2 : Ws → ⟪ (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) ⟫ʷ
lem-F1-X-CS0at2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (run b10))))))))))
  where
  b0 : Chain (CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ Sb0-2-43-1 ∷ []) (CX42 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸
       at 0 5 (CX42 ∷ []) (wl1147 (lit c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b1 : Chain (CX42 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b2 : Chain (CX42 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 2 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 4 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 3 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 4 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 6 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 7 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 3 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b3 : Chain (CX42 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 4 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 2 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 1 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 2 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 3 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 5 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸ done

  b4 : Chain (CX42 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 8 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 2 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸ done

  b5 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b6 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 9 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 12 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 14 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸ done

  b7 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b8 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ [])
  b9 = at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 9 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 8 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b10 : Chain (CX42 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ [])
  b10 = at 6 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 3 2 [] (wl0305 (lit c4)) ▸
       at 0 5 (Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ CCZ123 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ CCZ123 ∷ S4 ∷ CS34 ∷ []) (wl1148 (lit c4)) ▸
       at 0 14 (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ CK42 ∷ CS24 ∷ CS24 ∷ CK42 ∷ S4 ∷ CS34 ∷ []) (sym (lem-nf-X-CS0at2 c4)) ▸ done


-- CXbc-box @0210233441: 17 steps
lem-CXbc-box-at0210233441 : Ws → ⟪ (CX34 ∷ Bx2-0341 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXbc-box-at0210233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx2-0341 ∷ CX34 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX34 ∷ CCZ123 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CCZ124 ∷ CX03 ∷ CS01 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4) ▸
       at 0 2 (Toff203 ∷ CX34 ∷ []) (wp0939 c4) ▸
       at 1 2 (CCZ124 ∷ CX34 ∷ CCZ123 ∷ []) (sym (wl1149 (lit c4))) ▸
       at 3 2 (Toff203 ∷ CCZ123 ∷ CCZ013 ∷ []) (wl1150 (lit c4)) ▸
       at 2 2 (Toff203 ∷ CX34 ∷ []) (wp0939 c4) ▸
       at 5 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 9 2 (CCZ124 ∷ CS01 ∷ []) (sym (wp0919 c4)) ▸
       at 8 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CX34 ∷ CCZ123 ∷ CS13 ∷ CX03 ∷ CS13⁻ ∷ CCZ124 ∷ CX03 ∷ CS01 ∷ CX34 ∷ []) (Bx2-0341 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ [])
  b1 = at 7 2 (CCZ124 ∷ CS13⁻ ∷ []) (sym (wl1151 (lit c4))) ▸
       at 6 2 (CCZ124 ∷ CX03 ∷ []) (lem-comm-CX03-CCZ124 (lit c4)) ▸
       at 5 2 (CCZ124 ∷ CS13 ∷ []) (sym (wl1152 (lit c4))) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 4 2 (CCZ124 ∷ CCZ123 ∷ []) (wl0770 (lit c4)) ▸
       at 3 2 (CCZ124 ∷ CX34 ∷ CCZ123 ∷ []) (sym (wl1149 (lit c4))) ▸
       at 4 3 (CX34 ∷ []) (wl1153 (lit c4)) ▸
       at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸ done

  b2 : Chain (Bx2-0341 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ []) (Bx2-0341 ∷ CCZ013 ∷ [])
  b2 = at 1 3 (CCZ013 ∷ []) (sym (wp0913 c4)) ▸ done


-- CXcb-box @0210233441: 18 steps
lem-CXcb-box-at0210233441 : Ws → ⟪ (CX43 ∷ Bx2-0341 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXcb-box-at0210233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx2-0341 ∷ CX43 ∷ []) (Toff203 ∷ CCZ124 ∷ CX43 ∷ Toff204 ∷ CS14 ∷ CX04 ∷ Toff203 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ124 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ []) (lem-box-tQ-at0210233441 c4) ▸
       at 0 2 (Toff203 ∷ CX43 ∷ Toff204 ∷ []) (wp0940 c4) ▸
       at 2 2 (CCZ124 ∷ Toff204 ∷ CCZ014 ∷ []) (sym (wp0941 c4)) ▸
       at 1 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸
       at 4 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 8 2 (Toff203 ∷ CS01 ∷ []) (wl1154 (lit c4)) ▸
       at 7 2 (Toff203 ∷ CX04 ∷ []) (wp0942 c4) ▸
       at 6 2 (Toff203 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF203 (lit c4)) ▸ done

  b1 : Chain (Toff203 ∷ CCZ124 ∷ CX43 ∷ Toff204 ∷ CS14 ∷ CX04 ∷ Toff203 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ124 ∷ CX43 ∷ []) (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ [])
  b1 = at 5 2 (Toff203 ∷ CX04 ∷ []) (wp0942 c4) ▸
       at 4 2 (Toff203 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF203 (lit c4)) ▸
       at 5 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 3 2 (Toff203 ∷ Toff204 ∷ []) (sym (wp0943 c4)) ▸
       at 2 2 (Toff203 ∷ CX43 ∷ Toff204 ∷ []) (wp0940 c4) ▸
       at 3 3 (CX43 ∷ []) (wp0944 c4) ▸
       at 4 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 3 2 (CCZ124 ∷ CX43 ∷ []) (sym (wl0651 (lit c4))) ▸ done

  b2 : Chain (Toff203 ∷ CCZ124 ∷ Toff203 ∷ CCZ124 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ []) (Bx2-0341 ∷ CCZ014 ∷ [])
  b2 = at 0 4 (Bx2-0341 ∷ []) (sym (lem-box-tQ-at0210233441 c4)) ▸
       at 1 3 (CCZ014 ∷ []) (sym (wp0915 c4)) ▸ done


-- SWbc-box @0210233441: 11 steps
lem-SWbc-box-at0210233441 : Ws → ⟪ (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-SWbc-box-at0210233441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (CX34 ∷ Bx2-0341 ∷ CX34 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ [])
  b0 = at 0 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 4 1 (CX34 ∷ CX43 ∷ CX34 ∷ []) (sym (wl0547 (lit c4))) ▸
       at 2 3 (Bx2-0341 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210233441 c4) ▸
       at 3 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸
       at 1 3 (Bx2-0341 ∷ CCZ014 ∷ []) (lem-CXcb-box-at0210233441 c4) ▸
       at 4 2 (CX34 ∷ CCZ013 ∷ []) (wp0523 c4) ▸
       at 3 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸
       at 2 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸ done

  b1 : Chain (CX34 ∷ Bx2-0341 ∷ CX34 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ []) (Bx2-0341 ∷ [])
  b1 = at 3 5 (CCZ013 ∷ []) (wp0918 c4) ▸
       at 0 3 (Bx2-0341 ∷ CCZ013 ∷ []) (lem-CXbc-box-at0210233441 c4) ▸
       at 1 2 [] (wl0230 (lit c4)) ▸ done


-- nat-SWbc @0210233441: 23 steps
lem-nat-SWbc-at0210233441 : Ws → ⟪ (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-nat-SWbc-at0210233441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ Sw34 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff203 ∷ Bx0-241 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ []) (refl) ▸
       at 0 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 1 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 3 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 3 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 4 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ Sw34 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ Bx0-241 ∷ Sw34 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Sw34 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 7 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 8 2 (Toff204 ∷ Sw34 ∷ []) (wp0530 c4) ▸
       at 9 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 11 1 (CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 11 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 12 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff204 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Sw34 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Sw34 ∷ []) (Bx2-0431 ∷ [])
  b2 = at 13 2 (Toff023 ∷ Sw34 ∷ []) (wp0528 c4) ▸
       at 14 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 15 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx0-231 ∷ []) (refl) ▸
       at 5 6 (Bx0-231 ∷ []) (refl) ▸
       at 0 6 (Bx2-0431 ∷ []) (refl) ▸ done


-- sym-bc @0210233441: 2 steps
lem-sym-bc-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-sym-bc-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx2-0341 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at0210233441 c4)) ▸
       at 0 3 (Bx2-0431 ∷ []) (lem-nat-SWbc-at0210233441 c4) ▸ done


-- box-perm-1324 @0210233441: 1 steps
lem-box-perm-1324-at0210233441 : Ws → ⟪ (Bx2-0341 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-box-perm-1324-at0210233441 c4 = run b0
  where
  b0 : Chain (Bx2-0341 ∷ []) (Bx2-0431 ∷ [])
  b0 = at 0 1 (Bx2-0431 ∷ []) (lem-sym-bc-at0210233441 c4) ▸ done


-- cQ @02102441: 7 steps
lem-cQ-at02102441 : Ws → ⟪ (CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ
lem-cQ-at02102441 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ CCZ123 ∷ []) (CCZ123 ∷ CCZ024 ∷ [])
  b0 = at 0 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 4 2 (CCZ123 ∷ CS02 ∷ []) (sym (wl0171 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 2 2 (CCZ123 ∷ CS24⁻ ∷ []) (sym (wl0172 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 0 2 (CCZ123 ∷ CS24 ∷ []) (sym (wl0173 (lit c4))) ▸
       at 1 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸ done


-- tP @02102441: 7 steps
lem-tP-at02102441 : Ws → ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ
lem-tP-at02102441 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Toff213 ∷ []) (Toff213 ∷ Toff204 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 3 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at02102441 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸
       at 1 3 (Toff204 ∷ []) (wp0014 c4) ▸ done


-- VPQ @02102441: 14 steps
lem-VPQ-at02102441 : Ws → ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ
lem-VPQ-at02102441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 4 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 3 2 (CS13⁻ ∷ S2⁻ ∷ []) (sym (wl0177 (lit c4))) ▸
       at 2 2 (CS13⁻ ∷ Toff204 ∷ []) (lem-comm-TOFF204-CSd13 (lit c4)) ▸
       at 1 2 (CS13⁻ ∷ S2 ∷ []) (sym (wl0178 (lit c4))) ▸
       at 0 2 (CS13⁻ ∷ CS04⁻ ∷ []) (wp0016 c4) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02102441 c4) ▸ done

  b1 : Chain (CS13⁻ ∷ CS04⁻ ∷ S2 ∷ Toff213 ∷ Toff204 ∷ S2⁻ ∷ []) (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS04⁻ ∷ []) (wp0017 c4) ▸
       at 2 2 (Toff213 ∷ CS04⁻ ∷ []) (lem-comm-CSd04-TOFF213 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS04⁻ ∷ []) (wp0018 c4) ▸
       at 0 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸
       at 2 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸ done


-- QVQ @02102441: 3 steps
lem-QVQ-at02102441 : Ws → ⟪ (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) ⟫ʷ ≈ ⟪ (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-QVQ-at02102441 c4 = run b0
  where
  b0 : Chain (CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ123 ∷ []) (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ [])
  b0 = at 0 0 (Toff213 ∷ Toff213 ∷ []) (sym (wl0180 (lit c4))) ▸
       at 1 4 (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) (sym (lem-VPQ-at02102441 c4)) ▸
       at 4 2 [] (wl0181 (lit c4)) ▸ done


-- box-cP @02102441: 12 steps
lem-box-cP-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) ⟫ʷ
lem-box-cP-at02102441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0431 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 2 4 (Toff213 ∷ Toff204 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-QVQ-at02102441 c4) ▸
       at 1 2 (Toff213 ∷ Toff204 ∷ []) (lem-tP-at02102441 c4) ▸
       at 2 2 [] (wp0019 c4) ▸ done


-- Xb-box @02102441: 18 steps
lem-Xb-box-at02102441 : Ws → ⟪ (X4 ∷ Bx2-0431 ∷ X4 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-Xb-box-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (X4 ∷ Bx2-0431 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX03 ∷ CCZ024 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff213 ∷ X4 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at02102441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS01 ∷ []) (sym (wp0039 c4)) ▸
       at 7 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX03 ∷ CCZ024 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ Toff213 ∷ X4 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ [])
  b1 = at 5 2 (CCZ024 ∷ CX03 ∷ []) (sym (wp0756 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CCZ013 ∷ X4 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-cP-at02102441 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0024 c4)) ▸ done


-- box-tQ @02102441: 13 steps
lem-box-tQ-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) ⟫ʷ
lem-box-tQ-at02102441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Bx2-0431 ∷ []) (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ [])
  b0 = at 0 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 2 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 4 1 (CZ01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 2 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 5 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 7 1 (CZ01 ∷ []) (refl) ▸
       at 10 1 (CZ01 ∷ []) (refl) ▸ done

  b1 : Chain (CCZ024 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ CCZ023 ∷ Toff023 ∷ CZ01 ∷ Toff023 ∷ CCZ023 ∷ CZ01 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ [])
  b1 = at 5 6 (CCZ123 ∷ []) (wl1155 (lit c4)) ▸
       at 0 2 (Toff204 ∷ CCZ024 ∷ CZ04 ∷ []) (wp0025 c4) ▸
       at 2 2 (CCZ123 ∷ CZ04 ∷ []) (lem-comm-CZ04-CCZ123 (lit c4)) ▸
       at 1 2 (CCZ123 ∷ CCZ024 ∷ []) (lem-cQ-at02102441 c4) ▸
       at 2 4 (Toff204 ∷ []) (wp0026 c4) ▸ done


-- CXbc-box @02102441: 17 steps
lem-CXbc-box-at02102441 : Ws → ⟪ (CX43 ∷ Bx2-0431 ∷ CX43 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX43 ∷ Bx2-0431 ∷ CX43 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX43 ∷ CCZ124 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ CX43 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4) ▸
       at 0 2 (Toff204 ∷ CX43 ∷ []) (wp0945 c4) ▸
       at 1 2 (CCZ123 ∷ CX43 ∷ CCZ124 ∷ []) (sym (wl1156 (lit c4))) ▸
       at 3 2 (Toff204 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0946 c4) ▸
       at 2 2 (Toff204 ∷ CX43 ∷ []) (wp0945 c4) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (CCZ123 ∷ CS01 ∷ []) (sym (wl0763 (lit c4))) ▸
       at 8 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CX43 ∷ CCZ124 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CCZ123 ∷ CX04 ∷ CS01 ∷ CX43 ∷ []) (Bx2-0431 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ [])
  b1 = at 7 2 (CCZ123 ∷ CS14⁻ ∷ []) (sym (wl0764 (lit c4))) ▸
       at 6 2 (CCZ123 ∷ CX04 ∷ []) (lem-comm-CX04-CCZ123 (lit c4)) ▸
       at 5 2 (CCZ123 ∷ CS14 ∷ []) (sym (wl0765 (lit c4))) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 2 (CCZ123 ∷ CCZ124 ∷ []) (sym (wl0770 (lit c4))) ▸
       at 3 2 (CCZ123 ∷ CX43 ∷ CCZ124 ∷ []) (sym (wl1156 (lit c4))) ▸
       at 4 3 (CX43 ∷ []) (wl1157 (lit c4)) ▸
       at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-tQ-at02102441 c4)) ▸ done

  b2 : Chain (Bx2-0431 ∷ CX43 ∷ CCZ014 ∷ CX43 ∷ []) (Bx2-0431 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0915 c4)) ▸ done


-- CXcb-box @02102441: 18 steps
lem-CXcb-box-at02102441 : Ws → ⟪ (CX34 ∷ Bx2-0431 ∷ CX34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ CCZ013 ∷ []) ⟫ʷ
lem-CXcb-box-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX34 ∷ Bx2-0431 ∷ CX34 ∷ []) (Toff204 ∷ CCZ123 ∷ CX34 ∷ Toff203 ∷ CS13 ∷ CX03 ∷ Toff204 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ123 ∷ CX34 ∷ [])
  b0 = at 1 1 (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ []) (lem-box-tQ-at02102441 c4) ▸
       at 0 2 (Toff204 ∷ CX34 ∷ Toff203 ∷ []) (wp0947 c4) ▸
       at 2 2 (CCZ123 ∷ Toff203 ∷ CCZ013 ∷ []) (sym (wl1158 (lit c4))) ▸
       at 1 2 (CCZ123 ∷ CX34 ∷ []) (sym (wl1008 (lit c4))) ▸
       at 4 1 (CS13 ∷ CX03 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ []) (wl0905 (lit c4)) ▸
       at 8 2 (Toff204 ∷ CS01 ∷ []) (wp0948 c4) ▸
       at 7 2 (Toff204 ∷ CX03 ∷ []) (wp0949 c4) ▸
       at 6 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸ done

  b1 : Chain (Toff204 ∷ CCZ123 ∷ CX34 ∷ Toff203 ∷ CS13 ∷ CX03 ∷ Toff204 ∷ CS13⁻ ∷ CX03 ∷ CS01 ∷ CCZ123 ∷ CX34 ∷ []) (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ [])
  b1 = at 5 2 (Toff204 ∷ CX03 ∷ []) (wp0949 c4) ▸
       at 4 2 (Toff204 ∷ CS13 ∷ []) (lem-comm-CS13-TOFF204 (lit c4)) ▸
       at 5 5 (CCZ013 ∷ []) (sym (wl0905 (lit c4))) ▸
       at 3 2 (Toff204 ∷ Toff203 ∷ []) (wp0943 c4) ▸
       at 2 2 (Toff204 ∷ CX34 ∷ Toff203 ∷ []) (wp0947 c4) ▸
       at 3 3 (CX34 ∷ []) (wp0950 c4) ▸
       at 4 2 (CCZ123 ∷ CCZ013 ∷ []) (wl0327 (lit c4)) ▸
       at 3 2 (CCZ123 ∷ CX34 ∷ []) (sym (wl1008 (lit c4))) ▸ done

  b2 : Chain (Toff204 ∷ CCZ123 ∷ Toff204 ∷ CCZ123 ∷ CX34 ∷ CCZ013 ∷ CX34 ∷ []) (Bx2-0431 ∷ CCZ013 ∷ [])
  b2 = at 0 4 (Bx2-0431 ∷ []) (sym (lem-box-tQ-at02102441 c4)) ▸
       at 1 3 (CCZ013 ∷ []) (sym (wp0913 c4)) ▸ done


-- SWbc-box @02102441: 11 steps
lem-SWbc-box-at02102441 : Ws → ⟪ (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0431 ∷ []) ⟫ʷ
lem-SWbc-box-at02102441 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (CX43 ∷ Bx2-0431 ∷ CX43 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 4 1 (CX43 ∷ CX34 ∷ CX43 ∷ []) (sym (wl0649 (lit c4))) ▸
       at 2 3 (Bx2-0431 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02102441 c4) ▸
       at 3 2 (CX34 ∷ CCZ013 ∷ CCZ014 ∷ []) (wp0917 c4) ▸
       at 1 3 (Bx2-0431 ∷ CCZ013 ∷ []) (lem-CXcb-box-at02102441 c4) ▸
       at 4 2 (CX43 ∷ CCZ014 ∷ []) (wp0810 c4) ▸
       at 3 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸
       at 2 2 (CX43 ∷ CCZ014 ∷ CCZ013 ∷ []) (wp0916 c4) ▸ done

  b1 : Chain (CX43 ∷ Bx2-0431 ∷ CX43 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ CCZ013 ∷ CCZ014 ∷ []) (Bx2-0431 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0924 c4) ▸
       at 0 3 (Bx2-0431 ∷ CCZ014 ∷ []) (lem-CXbc-box-at02102441 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @02102441: 23 steps
lem-nat-SWbc-at02102441 : Ws → ⟪ (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-nat-SWbc-at02102441 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ Sw34 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ Sw34 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff204 ∷ Bx0-231 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ []) (refl) ▸
       at 0 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 1 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 3 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 2 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 3 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 4 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 5 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸ done

  b1 : Chain (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ Sw34 ∷ CCZ023 ∷ Bx2-01 ∷ Toff204 ∷ CCZ024 ∷ Bx0-231 ∷ Sw34 ∷ []) (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Sw34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Sw34 ∷ [])
  b1 = at 6 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 7 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 8 2 (Toff203 ∷ Sw34 ∷ []) (wp0813 c4) ▸
       at 9 2 (CCZ023 ∷ Sw34 ∷ []) (sym (wp0527 c4)) ▸
       at 11 1 (CCZ023 ∷ Toff023 ∷ Bx2-01 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ []) (refl) ▸
       at 10 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 11 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 12 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸ done

  b2 : Chain (CCZ023 ∷ Toff203 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Toff024 ∷ CCZ024 ∷ Bx2-01 ∷ Toff203 ∷ CCZ023 ∷ CCZ024 ∷ Toff024 ∷ Bx2-01 ∷ Sw34 ∷ Toff023 ∷ CCZ023 ∷ Bx2-01 ∷ Sw34 ∷ []) (Bx2-0341 ∷ [])
  b2 = at 13 2 (Toff024 ∷ Sw34 ∷ []) (wp0812 c4) ▸
       at 14 2 (CCZ024 ∷ Sw34 ∷ []) (sym (wp0529 c4)) ▸
       at 15 2 (Bx2-01 ∷ Sw34 ∷ []) (sym (c₂ (CZ) (Swap ↑))) ▸
       at 16 2 [] (wl0004 (lit c4)) ▸
       at 2 6 (Bx0-241 ∷ []) (refl) ▸
       at 5 6 (Bx0-241 ∷ []) (refl) ▸
       at 0 6 (Bx2-0341 ∷ []) (refl) ▸ done


-- sym-bc @02102441: 2 steps
lem-sym-bc-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-sym-bc-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Sw34 ∷ Bx2-0431 ∷ Sw34 ∷ []) (sym (lem-SWbc-box-at02102441 c4)) ▸
       at 0 3 (Bx2-0341 ∷ []) (lem-nat-SWbc-at02102441 c4) ▸ done


-- box-perm-1324 @02102441: 1 steps
lem-box-perm-1324-at02102441 : Ws → ⟪ (Bx2-0431 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0341 ∷ []) ⟫ʷ
lem-box-perm-1324-at02102441 c4 = run b0
  where
  b0 : Chain (Bx2-0431 ∷ []) (Bx2-0341 ∷ [])
  b0 = at 0 1 (Bx2-0341 ∷ []) (lem-sym-bc-at02102441 c4) ▸ done

