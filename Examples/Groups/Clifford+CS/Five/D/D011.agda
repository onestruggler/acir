{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D011 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0166 ; wl0167 ; wl0174 ; wl0175 ; wl0176 ; wl0177 ; wl0178 ; wl0179 ; wl0180 ; wl0181 ; wl0185 ; wl0190 ; wl0196 ; wl0207 ; wl0214 ; wl0232 ; wl0234 ; wl0235 ; wl0241 ; wl0242 ; wl0256 ; wl0263 ; wl0271 ; wl0272 ; wl0274 ; wl0275 ; wl0277 ; wl0279 ; wl0281 ; wl0283 ; wl0285 ; wl0287 ; wl0305 ; wl0311 ; wl0321 ; wl0326 ; wl0335 ; wl0336 ; wl0337 ; wl0341 ; wl0348 ; wl0404 ; wl0411 ; wl0447 ; wl0452 ; wl0469 ; wl0490 ; wl0495 ; wl0503 ; wl0512 ; wl0704 ; wl0807 ; wl0808 ; wl0809 ; wl0828 ; wl0832 ; wl0852 ; wl0861 ; wl0872 ; wl0878 ; wl0879 ; wl0888 ; wl0892 ; wl0897 ; wl0899 ; wl0901 ; wl0903 ; wl0921 ; wl0924 ; wl0926 ; wl0928 ; wl0940 ; wl0942 ; wl0952 ; wl0953 ; wl0954 ; wl0955 ; wl0956 ; wl0957 ; wl0958 ; wl0959 ; wl0960 ; wl0961 ; wl0962 ; wl0963 ; wl0964 ; wl0965 ; wl0966 ; wl0967 ; wl0968 ; wl0969 ; wl0970 ; wl0971 ; wl0972 ; wl0973 ; wl0974 ; wl0975 ; wl0976 ; wl0977 ; wl0978 ; wl0979 ; wl0980 ; wl0981 ; wl0982 ; wl0983 ; wl0984 ; wl0985 ; wl0986 ; wl0987 ; wl0988 ; wl0989 ; wl0990 ; wl0991 ; wl0992 ; wl0993 ; wl0994 ; wl0995 ; wl0996 ; wl0997 ; wl0998 ; wp0003 ; wp0011 ; wp0012 ; wp0013 ; wp0014 ; wp0015 ; wp0016 ; wp0017 ; wp0018 ; wp0019 ; wp0020 ; wp0023 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0053 ; wp0054 ; wp0062 ; wp0063 ; wp0064 ; wp0066 ; wp0070 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0091 ; wp0092 ; wp0124 ; wp0130 ; wp0135 ; wp0139 ; wp0141 ; wp0142 ; wp0146 ; wp0161 ; wp0167 ; wp0171 ; wp0202 ; wp0221 ; wp0251 ; wp0252 ; wp0295 ; wp0298 ; wp0302 ; wp0310 ; wp0341 ; wp0342 ; wp0352 ; wp0737 ; wp0749 ; wp0751 ; wp0752 ; wp0759 ; wp0761 ; wp0762 ; wp0763 ; wp0770 ; wp0771 ; wp0772 ; wp0773 ; wp0774 ; wp0775 ; wp0776 ; wp0777 ; wp0778 ; wp0779 ; wp0780 ; wp0781 ; wp0782 ; wp0783 ; wp0784 ; wp0785 ; wp0786 ; wp0787 ; wp0788 ; wp0789 ; wp0790 ; wp0791 ; wp0792 ; wp0793 ; wp0794 ; wp0795 ; wp0796 ; wp0797 ; wp0798 ; wp0799 ; wp0800 ; wp0801 ; wp0802 ; wp0803 ; wp0804)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box-tQ-at0210243143 ; lem-sym-bc)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-cP-at1221 ; lem-box-perm-1423 ; lem-box-tQ-at122331 ; lem-pairs-at132132 ; lem-sym-ab-at2332)
open import Examples.Groups.Clifford+CS.Five.D.D003 using (lem-sym-ab-at1221)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-box-3 ; lem-box-cP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D007 using (lem-box-perm-1324-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-CSdu-box-3-at243243 ; lem-CSu-box-3-at243243 ; lem-F0-at14213243 ; lem-box-perm-1342-at0310243142 ; lem-box-perm-1423-at03102132 ; lem-pairs-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CSdu-box-3-at0310243142 ; lem-CSdu-box-3-at122441 ; lem-CSu-box-3-at0310243142 ; lem-CSu-box-3-at122441 ; lem-box-perm-1342-at0210243143 ; lem-box-perm-1432-at122441 ; lem-box-perm-2341-at021021 ; lem-box-perm-4123-at02233440 ; lem-box-tQ-at0220 ; lem-box-tQ-at022330 ; lem-box-tQ-at02233440 ; lem-cQ-at022330 ; lem-sym-ab-at021021)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd14-TOFF023 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX13-CCZ024 ; lem-comm-CZ04-TOFF213)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX23-CCZ014 ; lem-comm-CZ13-CCZ024 ; lem-comm-SWAP13-BOX⟨0·24⟩)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CS12-CCZ034 ; lem-comm-CS14-TOFF023 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CSd13-TOFF204 ; lem-comm-CX04-TOFF312 ; lem-comm-SWAP03-BOX⟨2·14⟩ ; lem-comm-TOFF213-CSd04 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ024-CX31 ; lem-comm-CCZ124-CS03 ; lem-comm-CX21-TOFF034 ; lem-comm-TOFF034-CX12)
-- box-box-1 @021021: 105 steps
lem-box-box-1-at021021 : Ws → ⟪ (Bx2-0134 ∷ Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ Bx2-0134 ∷ []) ⟫ʷ
lem-box-box-1-at021021 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (run b13)))))))))))))
  where
  b0 : Chain (Bx2-0134 ∷ Bx0-2134 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ012 ∷ CX23 ∷ CS24 ∷ Toff034 ∷ [])
  b0 = at 0 1 (Bx2-1340 ∷ []) (lem-box-perm-2341-at021021 c4) ▸
       at 0 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at02233440 c4) ▸
       at 4 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 4 2 (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp0139 c4) ▸
       at 6 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 10 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 9 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸ done

  b1 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ012 ∷ CX23 ∷ CS24 ∷ Toff034 ∷ []) (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ [])
  b1 = at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 5 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 6 3 (Toff034 ∷ CCZ024 ∷ []) (wp0770 c4) ▸
       at 3 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 3 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸ done

  b2 : Chain (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ Toff034 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ [])
  b2 = at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 4 2 (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp0771 c4) ▸
       at 3 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 9 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 8 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS13⁻ ∷ []) (wp0772 c4) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸ done

  b3 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ Toff034 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CCZ024 ∷ [])
  b3 = at 4 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 3 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 4 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 6 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 10 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 9 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 8 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸ done

  b4 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CS34 ∷ CCZ012 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ Toff034 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff034 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ [])
  b4 = at 6 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 7 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 5 2 (CCZ012 ∷ CCZ013 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 5 3 (Toff213 ∷ []) (wl0953 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CCZ134 ∷ []) (wp0012 c4) ▸
       at 5 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 11 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸ done

  b5 : Chain (Toff213 ∷ CCZ024 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff034 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ024 ∷ Bx0-2134 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b5 = at 10 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 9 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 8 2 (Toff034 ∷ CS13⁻ ∷ []) (wp0772 c4) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 6 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 5 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 6 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 2 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸ done

  b6 : Chain (Toff213 ∷ CCZ024 ∷ Bx0-2134 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff034 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b6 = at 2 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 1 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 2 2 (Toff034 ∷ CCZ024 ∷ CCZ234 ∷ []) (wp0139 c4) ▸
       at 4 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 8 2 (CCZ012 ∷ CS24 ∷ []) (sym (wp0141 c4)) ▸
       at 7 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX23 ∷ []) (sym (wl0411 (lit c4))) ▸ done

  b7 : Chain (Toff213 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ CS34 ∷ CCZ012 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff034 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff213 ∷ Toff034 ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b7 = at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 3 2 (CCZ012 ∷ CCZ024 ∷ []) (sym (wp0142 c4)) ▸
       at 4 3 (Toff034 ∷ CCZ024 ∷ []) (wp0770 c4) ▸
       at 1 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 1 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at1221 c4) ▸
       at 0 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 2 2 (Toff034 ∷ CCZ013 ∷ CCZ134 ∷ []) (wp0771 c4) ▸ done

  b8 : Chain (CCZ012 ∷ Toff213 ∷ Toff034 ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b8 = at 1 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 7 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 6 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CS13⁻ ∷ []) (wp0772 c4) ▸
       at 3 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 2 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 1 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸ done

  b9 : Chain (CCZ012 ∷ Toff034 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ013 ∷ CCZ134 ∷ CCZ012 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CCZ012 ∷ CCZ134 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b9 = at 2 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 8 2 (CCZ012 ∷ CS14 ∷ []) (sym (wp0011 c4)) ▸
       at 7 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 6 2 (CCZ012 ∷ CS34⁻ ∷ []) (sym (c₃ (CCZ) (CS • CS • CS))) ▸
       at 5 2 (CCZ012 ∷ CX13 ∷ []) (sym (wl0167 (lit c4))) ▸
       at 4 2 (CCZ012 ∷ CS34 ∷ []) (sym (c₃ (CCZ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸ done

  b10 : Chain (CCZ012 ∷ Toff034 ∷ Toff213 ∷ CCZ013 ∷ CCZ012 ∷ CCZ134 ∷ Toff034 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Toff034 ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b10 = at 3 2 (CCZ012 ∷ CCZ013 ∷ []) (sym (wl0704 (lit c4))) ▸
       at 2 2 (CCZ012 ∷ Toff213 ∷ CCZ013 ∷ []) (sym (wl0940 (lit c4))) ▸
       at 3 3 (Toff213 ∷ []) (wl0953 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CCZ134 ∷ []) (wp0012 c4) ▸
       at 3 1 (K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ []) (sym (wl0952 (lit c4))) ▸
       at 9 2 (Toff034 ∷ K2⁻ ∷ []) (wp0751 c4) ▸
       at 8 2 (Toff034 ∷ CS23 ∷ []) (wp0146 c4) ▸
       at 7 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸ done

  b11 : Chain (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ K2 ∷ CS13 ∷ CX21 ∷ CS13⁻ ∷ Toff034 ∷ CX21 ∷ CS23 ∷ K2⁻ ∷ CCZ134 ∷ CCZ024 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx0-2134 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ [])
  b11 = at 6 2 (Toff034 ∷ CS13⁻ ∷ []) (wp0772 c4) ▸
       at 5 2 (Toff034 ∷ CX21 ∷ []) (lem-comm-CX21-TOFF034 (lit c4)) ▸
       at 4 2 (Toff034 ∷ CS13 ∷ []) (wp0171 c4) ▸
       at 3 2 (Toff034 ∷ K2 ∷ []) (wp0752 c4) ▸
       at 4 7 (Toff213 ∷ []) (wl0952 (lit c4)) ▸
       at 0 4 (Bx0-2134 ∷ []) (sym (lem-box-cP-at1221 c4)) ▸
       at 2 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b12 : Chain (Bx0-2134 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ Toff213 ∷ CCZ134 ∷ CCZ024 ∷ []) (Bx0-2134 ∷ Bx2-1340 ∷ [])
  b12 = at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 3 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CCZ134 ∷ []) (wl0954 (lit c4)) ▸
       at 4 2 [] (wl0321 (lit c4)) ▸
       at 1 4 (Bx2-1340 ∷ []) (sym (lem-box-tQ-at02233440 c4)) ▸ done

  b13 : Chain (Bx0-2134 ∷ Bx2-1340 ∷ []) (Bx0-2134 ∷ Bx2-0134 ∷ [])
  b13 = at 1 1 (Bx2-0134 ∷ []) (lem-box-perm-4123-at02233440 c4) ▸ done


-- box-perm-1432 @1221: 4 steps
lem-box-perm-1432-at1221 : Ws → ⟪ (Bx0-2134 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2431 ∷ []) ⟫ʷ
lem-box-perm-1432-at1221 c4 = run b0
  where
  b0 : Chain (Bx0-2134 ∷ []) (Bx0-2431 ∷ [])
  b0 = at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸
       at 0 1 (Bx0-1324 ∷ []) (lem-sym-bc c4) ▸
       at 0 1 (Bx0-3124 ∷ []) (lem-sym-ab-at2332 c4) ▸
       at 0 1 (Bx0-2431 ∷ []) (lem-pairs-at132132 c4) ▸ done


-- CXbc-box @0220: 17 steps
lem-CXbc-box-at0220 : Ws → ⟪ (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ014 ∷ []) ⟫ʷ
lem-CXbc-box-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX03 ∷ Bx2-1034 ∷ CX03 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX03 ∷ CCZ024 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX03 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ CX03 ∷ []) (wl0955 (lit c4)) ▸
       at 1 2 (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (sym (wp0773 c4)) ▸
       at 3 2 (Toff201 ∷ CCZ024 ∷ CCZ014 ∷ []) (wp0774 c4) ▸
       at 2 2 (Toff201 ∷ CX03 ∷ []) (wl0955 (lit c4)) ▸
       at 5 1 (CS04 ∷ CX10 ∷ CS04⁻ ∷ CX10 ∷ CS14 ∷ []) (wp0341 c4) ▸
       at 9 2 (CCZ234 ∷ CS14 ∷ []) (sym (wl0452 (lit c4))) ▸
       at 8 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CX03 ∷ CCZ024 ∷ CS04 ∷ CX10 ∷ CS04⁻ ∷ CCZ234 ∷ CX10 ∷ CS14 ∷ CX03 ∷ []) (Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ [])
  b1 = at 7 2 (CCZ234 ∷ CS04⁻ ∷ []) (sym (wp0342 c4)) ▸
       at 6 2 (CCZ234 ∷ CX10 ∷ []) (c₂ (CX₁₀) (CCZ)) ▸
       at 5 2 (CCZ234 ∷ CS04 ∷ []) (sym (wp0302 c4)) ▸
       at 6 5 (CCZ014 ∷ []) (sym (wp0341 c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 3 2 (CCZ234 ∷ CX03 ∷ CCZ024 ∷ []) (sym (wp0773 c4)) ▸
       at 4 3 (CX03 ∷ []) (wp0775 c4) ▸
       at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸ done

  b2 : Chain (Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CX03 ∷ []) (Bx2-1034 ∷ CCZ014 ∷ [])
  b2 = at 1 3 (CCZ014 ∷ []) (sym (wp0761 c4)) ▸ done


-- CXcb-box @0220: 18 steps
lem-CXcb-box-at0220 : Ws → ⟪ (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ CCZ134 ∷ []) ⟫ʷ
lem-CXcb-box-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX30 ∷ Bx2-1034 ∷ CX30 ∷ []) (Toff201 ∷ CCZ234 ∷ CX30 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ Toff201 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ234 ∷ CX30 ∷ [])
  b0 = at 1 1 (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ []) (lem-box-tQ-at0220 c4) ▸
       at 0 2 (Toff201 ∷ CX30 ∷ Toff213 ∷ []) (wl0956 (lit c4)) ▸
       at 2 2 (CCZ234 ∷ Toff213 ∷ CCZ134 ∷ []) (sym (wl0957 (lit c4))) ▸
       at 1 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸
       at 4 1 (CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ []) (wl0166 (lit c4)) ▸
       at 8 2 (Toff201 ∷ CS14 ∷ []) (wp0777 c4) ▸
       at 7 2 (Toff201 ∷ CX13 ∷ []) (wl0958 (lit c4)) ▸
       at 6 2 (Toff201 ∷ CS34⁻ ∷ []) (sym (c₃ (Toffᵗ) (CS • CS • CS))) ▸ done

  b1 : Chain (Toff201 ∷ CCZ234 ∷ CX30 ∷ Toff213 ∷ CS34 ∷ CX13 ∷ Toff201 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ234 ∷ CX30 ∷ []) (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ [])
  b1 = at 5 2 (Toff201 ∷ CX13 ∷ []) (wl0958 (lit c4)) ▸
       at 4 2 (Toff201 ∷ CS34 ∷ []) (sym (c₃ (Toffᵗ) (CS))) ▸
       at 5 5 (CCZ134 ∷ []) (sym (wl0166 (lit c4))) ▸
       at 3 2 (Toff201 ∷ Toff213 ∷ []) (sym (wl0921 (lit c4))) ▸
       at 2 2 (Toff201 ∷ CX30 ∷ Toff213 ∷ []) (wl0956 (lit c4)) ▸
       at 3 3 (CX30 ∷ []) (wl0959 (lit c4)) ▸
       at 4 2 (CCZ234 ∷ CCZ134 ∷ []) (wl0960 (lit c4)) ▸
       at 3 2 (CCZ234 ∷ CX30 ∷ []) (sym (wp0776 c4)) ▸ done

  b2 : Chain (Toff201 ∷ CCZ234 ∷ Toff201 ∷ CCZ234 ∷ CX30 ∷ CCZ134 ∷ CX30 ∷ []) (Bx2-1034 ∷ CCZ134 ∷ [])
  b2 = at 0 4 (Bx2-1034 ∷ []) (sym (lem-box-tQ-at0220 c4)) ▸
       at 1 3 (CCZ134 ∷ []) (sym (wp0759 c4)) ▸ done


-- SWbc-box @0220: 11 steps
lem-SWbc-box-at0220 : Ws → ⟪ (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1034 ∷ []) ⟫ʷ
lem-SWbc-box-at0220 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (CX03 ∷ Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ [])
  b0 = at 0 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 4 1 (CX03 ∷ CX30 ∷ CX03 ∷ []) (sym (wl0961 (lit c4))) ▸
       at 2 3 (Bx2-1034 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0220 c4) ▸
       at 3 2 (CX30 ∷ CCZ134 ∷ CCZ014 ∷ []) (wp0763 c4) ▸
       at 1 3 (Bx2-1034 ∷ CCZ134 ∷ []) (lem-CXcb-box-at0220 c4) ▸
       at 4 2 (CX03 ∷ CCZ014 ∷ []) (wp0778 c4) ▸
       at 3 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸
       at 2 2 (CX03 ∷ CCZ014 ∷ CCZ134 ∷ []) (wp0762 c4) ▸ done

  b1 : Chain (CX03 ∷ Bx2-1034 ∷ CX03 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ []) (Bx2-1034 ∷ [])
  b1 = at 3 5 (CCZ014 ∷ []) (wp0779 c4) ▸
       at 0 3 (Bx2-1034 ∷ CCZ014 ∷ []) (lem-CXbc-box-at0220 c4) ▸
       at 1 2 [] (wp0161 c4) ▸ done


-- nat-SWbc @0220: 23 steps
lem-nat-SWbc-at0220 : Ws → ⟪ (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-nat-SWbc-at0220 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ Sw03 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ Sw03 ∷ [])
  b0 = at 1 1 (CCZ012 ∷ Toff201 ∷ Bx1-234 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ []) (refl) ▸
       at 0 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 1 2 (Toff213 ∷ Sw03 ∷ []) (wl0962 (lit c4)) ▸
       at 3 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 2 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 3 2 (Toff102 ∷ Sw03 ∷ []) (wl0963 (lit c4)) ▸
       at 4 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 5 2 (Toff102 ∷ Sw03 ∷ []) (wl0963 (lit c4)) ▸ done

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ Sw03 ∷ CCZ123 ∷ Bx2-14 ∷ Toff201 ∷ CCZ012 ∷ Bx1-234 ∷ Sw03 ∷ []) (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Sw03 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Sw03 ∷ [])
  b1 = at 6 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 7 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 8 2 (Toff213 ∷ Sw03 ∷ []) (wl0962 (lit c4)) ▸
       at 9 2 (CCZ123 ∷ Sw03 ∷ []) (sym (wl0926 (lit c4))) ▸
       at 11 1 (CCZ123 ∷ Toff123 ∷ Bx2-14 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ []) (refl) ▸
       at 10 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 11 2 (Toff102 ∷ Sw03 ∷ []) (wl0963 (lit c4)) ▸
       at 12 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ123 ∷ Toff213 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Toff102 ∷ CCZ012 ∷ Bx2-14 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ Bx2-14 ∷ Sw03 ∷ Toff123 ∷ CCZ123 ∷ Bx2-14 ∷ Sw03 ∷ []) (Bx2-1304 ∷ [])
  b2 = at 13 2 (Toff102 ∷ Sw03 ∷ []) (wl0963 (lit c4)) ▸
       at 14 2 (CCZ012 ∷ Sw03 ∷ []) (sym (wl0924 (lit c4))) ▸
       at 15 2 (Bx2-14 ∷ Sw03 ∷ []) (lem-comm-SWAP03-BOX⟨2·14⟩ (lit c4)) ▸
       at 16 2 [] (wl0928 (lit c4)) ▸
       at 2 6 (Bx1-204 ∷ []) (refl) ▸
       at 5 6 (Bx1-204 ∷ []) (refl) ▸
       at 0 6 (Bx2-1304 ∷ []) (refl) ▸ done


-- sym-bc @0220: 2 steps
lem-sym-bc-at0220 : Ws → ⟪ (Bx2-1034 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-sym-bc-at0220 c4 = run b0
  where
  b0 : Chain (Bx2-1034 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 0 1 (Sw03 ∷ Bx2-1034 ∷ Sw03 ∷ []) (sym (lem-SWbc-box-at0220 c4)) ▸
       at 0 3 (Bx2-1304 ∷ []) (lem-nat-SWbc-at0220 c4) ▸ done


-- tP @022330: 7 steps
lem-tP-at022330 : Ws → ⟪ (Toff213 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ []) ⟫ʷ
lem-tP-at022330 c4 = run b0
  where
  b0 : Chain (Toff213 ∷ Toff204 ∷ []) (Toff204 ∷ Toff213 ∷ [])
  b0 = at 0 1 (K2 ∷ CCZ123 ∷ K2⁻ ∷ []) (sym (wl0174 (lit c4))) ▸
       at 3 1 (K2 ∷ CCZ024 ∷ K2⁻ ∷ []) (sym (wp0014 c4)) ▸
       at 2 2 [] (wl0175 (lit c4)) ▸
       at 1 2 (CCZ024 ∷ CCZ123 ∷ []) (lem-cQ-at022330 c4) ▸
       at 2 0 (K2⁻ ∷ K2 ∷ []) (sym (wl0175 (lit c4))) ▸
       at 0 3 (Toff204 ∷ []) (wp0014 c4) ▸
       at 1 3 (Toff213 ∷ []) (wl0174 (lit c4)) ▸ done


-- P-box @022330: 8 steps
lem-P-box-at022330 : Ws → ⟪ (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-1304 ∷ []) ⟫ʷ
lem-P-box-at022330 c4 = run b0
  where
  b0 : Chain (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) (Bx2-1304 ∷ [])
  b0 = at 1 1 (Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ []) (lem-box-tQ-at022330 c4) ▸
       at 0 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at022330 c4)) ▸
       at 1 2 (CCZ024 ∷ CZ04 ∷ Toff204 ∷ []) (sym (wp0780 c4)) ▸
       at 3 2 (Toff213 ∷ Toff204 ∷ []) (sym (lem-tP-at022330 c4)) ▸
       at 4 3 (CCZ024 ∷ CZ04 ∷ []) (sym (wp0781 c4)) ▸
       at 2 2 (Toff213 ∷ CZ04 ∷ []) (lem-comm-CZ04-TOFF213 (lit c4)) ▸
       at 3 3 (CCZ024 ∷ []) (sym (wp0782 c4)) ▸
       at 0 4 (Bx2-1304 ∷ []) (sym (lem-box-tQ-at022330 c4)) ▸ done


-- VPQ @022330: 14 steps
lem-VPQ-at022330 : Ws → ⟪ (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ []) ⟫ʷ
lem-VPQ-at022330 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ [])
  b0 = at 0 2 (CS13⁻ ∷ S2 ∷ Toff213 ∷ S2⁻ ∷ []) (sym (wl0176 (lit c4))) ▸
       at 4 2 (CS04⁻ ∷ S2 ∷ Toff204 ∷ S2⁻ ∷ []) (sym (wp0015 c4)) ▸
       at 3 2 (CS04⁻ ∷ S2⁻ ∷ []) (sym (wp0018 c4)) ▸
       at 2 2 (CS04⁻ ∷ Toff213 ∷ []) (lem-comm-TOFF213-CSd04 (lit c4)) ▸
       at 1 2 (CS04⁻ ∷ S2 ∷ []) (sym (wp0017 c4)) ▸
       at 0 2 (CS04⁻ ∷ CS13⁻ ∷ []) (sym (wp0016 c4)) ▸
       at 4 2 [] (wl0179 (lit c4)) ▸
       at 3 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at022330 c4) ▸ done

  b1 : Chain (CS04⁻ ∷ CS13⁻ ∷ S2 ∷ Toff204 ∷ Toff213 ∷ S2⁻ ∷ []) (Toff204 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ [])
  b1 = at 4 0 (S2⁻ ∷ S2 ∷ []) (sym (wl0179 (lit c4))) ▸
       at 1 2 (S2 ∷ CS13⁻ ∷ []) (wl0178 (lit c4)) ▸
       at 2 2 (Toff204 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-TOFF204 (lit c4)) ▸
       at 3 2 (S2⁻ ∷ CS13⁻ ∷ []) (wl0177 (lit c4)) ▸
       at 0 4 (Toff204 ∷ CCZ024 ∷ []) (wp0015 c4) ▸
       at 2 4 (Toff213 ∷ CCZ123 ∷ []) (wl0176 (lit c4)) ▸ done


-- QVQ @022330: 3 steps
lem-QVQ-at022330 : Ws → ⟪ (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) ⟫ʷ ≈ ⟪ (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-QVQ-at022330 c4 = run b0
  where
  b0 : Chain (CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ024 ∷ []) (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ [])
  b0 = at 0 0 (Toff204 ∷ Toff204 ∷ []) (sym (wp0019 c4)) ▸
       at 1 4 (Toff213 ∷ CCZ123 ∷ Toff204 ∷ CCZ024 ∷ []) (sym (lem-VPQ-at022330 c4)) ▸
       at 4 2 [] (wp0135 c4) ▸ done


-- box-cP @022330: 12 steps
lem-box-cP-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) ⟫ʷ
lem-box-cP-at022330 c4 = trans (run b0) (run b1)
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

  b1 : Chain (CCZ123 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ123 ∷ CCZ012 ∷ Toff102 ∷ CZ14 ∷ Toff102 ∷ CCZ012 ∷ CZ14 ∷ []) (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ [])
  b1 = at 5 6 (CCZ024 ∷ []) (wp0130 c4) ▸
       at 2 4 (Toff204 ∷ Toff213 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-QVQ-at022330 c4) ▸
       at 1 2 (Toff204 ∷ Toff213 ∷ []) (lem-tP-at022330 c4) ▸
       at 2 2 [] (wl0180 (lit c4)) ▸ done


-- pairs @022330: 4 steps
lem-pairs-at022330 : Ws → ⟪ (Bx2-1304 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-pairs-at022330 c4 = run b0
  where
  b0 : Chain (Bx2-1304 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Toff204 ∷ Bx2-1304 ∷ Toff204 ∷ []) (sym (lem-P-box-at022330 c4)) ▸
       at 1 1 (CCZ123 ∷ Toff204 ∷ CCZ123 ∷ Toff204 ∷ []) (lem-box-cP-at022330 c4) ▸
       at 4 2 [] (wp0019 c4) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-tQ-at0210243143 c4)) ▸ done


-- box-perm-1423 @021021: 3 steps
lem-box-perm-1423-at021021 : Ws → ⟪ (Bx2-0134 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ []) ⟫ʷ
lem-box-perm-1423-at021021 c4 = run b0
  where
  b0 : Chain (Bx2-0134 ∷ []) (Bx2-0413 ∷ [])
  b0 = at 0 1 (Bx2-1034 ∷ []) (lem-sym-ab-at021021 c4) ▸
       at 0 1 (Bx2-1304 ∷ []) (lem-sym-bc-at0220 c4) ▸
       at 0 1 (Bx2-0413 ∷ []) (lem-pairs-at022330 c4) ▸ done


-- CSu-box-3 @0210243143: 17 steps
lem-CSu-box-3-at0210243143 : Ws → ⟪ (CS12 ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12 ∷ []) ⟫ʷ
lem-CSu-box-3-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS12 ∷ Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 1 2 (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) (wl0964 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CS12 ∷ CS13 ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl0965 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS13 ∷ []) (wl0966 (lit c4)) ▸
       at 3 2 (Toff213 ∷ CS12 ∷ CS13 ∷ CCZ123 ∷ []) (wl0964 (lit c4)) ▸
       at 4 6 (CS12 ∷ []) (wl0967 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ []) (Bx2-0413 ∷ CS12 ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- CSdu-box-3 @0210243143: 17 steps
lem-CSdu-box-3-at0210243143 : Ws → ⟪ (CS12⁻ ∷ Bx2-0413 ∷ []) ⟫ʷ ≈ ⟪ (Bx2-0413 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-CSdu-box-3-at0210243143 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CS12⁻ ∷ Bx2-0413 ∷ []) (CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ [])
  b0 = at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 1 2 (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) (wl0968 (lit c4)) ▸
       at 4 1 (CS13 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ []) (wl0326 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX21 ∷ []) (sym (wp0749 c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CS13 ∷ CCZ024 ∷ CX21 ∷ CS13⁻ ∷ CX21 ∷ CS23 ∷ Toff213 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ [])
  b1 = at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0326 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 5 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl0965 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CS13⁻ ∷ []) (wl0969 (lit c4)) ▸
       at 3 2 (Toff213 ∷ CS12⁻ ∷ CS13⁻ ∷ CCZ123 ∷ []) (wl0968 (lit c4)) ▸
       at 4 6 (CS12⁻ ∷ []) (wl0970 (lit c4)) ▸ done

  b2 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ []) (Bx2-0413 ∷ CS12⁻ ∷ [])
  b2 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done


-- F4-CS0-CS2: 284 steps
lem-F4-CS0-CS2 : Ws → ⟪ (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS0-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 4 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb2-0-41-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 5 2 (Bx0-2431 ∷ CS03⁻ ∷ []) (lem-CSdu-box-3-at122441 c4) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b3 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸ done

  b4 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff013 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 5 2 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (sym (wp0783 c4)) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 13 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff013 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 8 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (sym (wp0784 c4)) ▸
       at 9 2 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (sym (wp0783 c4)) ▸
       at 8 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 12 2 (Toff013 ∷ CS14 ∷ []) (wp0785 c4) ▸
       at 11 2 (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ Toff014 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Bx0-2431 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b6 = at 10 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 9 2 (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4)) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 7 2 (Toff013 ∷ Toff014 ∷ []) (sym (wp0786 c4)) ▸
       at 8 3 (CCZ124 ∷ []) (sym (wp0787 c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸ done

  b7 : Chain (X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Bx0-2431 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b7 = at 3 2 (Bx0-2431 ∷ CS03 ∷ []) (lem-CSu-box-3-at122441 c4) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Bx2-0413 ∷ K3 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 2 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 3 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (sym (wp0783 c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K3⁻ ∷ []) (sym (wp0033 c4)) ▸
       at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff014 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ K3 ∷ []) (sym (wp0037 c4)) ▸
       at 6 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ Toff014 ∷ CCZ124 ∷ []) (sym (wp0784 c4)) ▸
       at 7 2 (Toff013 ∷ Toff014 ∷ Toff314 ∷ []) (sym (wp0783 c4)) ▸
       at 6 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸ done

  b10 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff014 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b10 = at 10 2 (Toff013 ∷ CS14 ∷ []) (wp0785 c4) ▸
       at 9 2 (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS24⁻ ∷ []) (lem-comm-CSd24-TOFF013 (lit c4)) ▸
       at 7 2 (Toff013 ∷ CX12 ∷ []) (wl0872 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CS24 ∷ []) (lem-comm-CS24-TOFF013 (lit c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 2 (Toff013 ∷ Toff014 ∷ []) (sym (wp0786 c4)) ▸
       at 6 3 (CCZ124 ∷ []) (sym (wp0787 c4)) ▸ done

  b11 : Chain (X4 ∷ Bx2-0413 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b11 = at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx2-0134 ∷ []) (lem-box-perm-1342-at0210243143 c4) ▸
       at 2 1 (Bx0-2134 ∷ []) (lem-box-perm-1432-at122441 c4) ▸
       at 1 2 (Bx0-2134 ∷ Bx2-0134 ∷ []) (lem-box-box-1-at021021 c4) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-box-perm-1432-at1221 c4) ▸
       at 2 1 (Bx2-0413 ∷ []) (lem-box-perm-1423-at021021 c4) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b12 : Chain (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff013 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b12 = at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ Toff013 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b13 = at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸ done

  b14 : Chain (Bx0-2431 ∷ X4 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CZ13 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b14 = at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (Toff213 ∷ CZ13 ∷ CCZ123 ∷ []) (wl0965 (lit c4)) ▸ done

  b15 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CZ13 ∷ CCZ123 ∷ CCZ024 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CZ13 ∷ CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b15 = at 5 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ CZ13 ∷ CCZ123 ∷ Toff213 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b16 = at 5 3 (Toff213 ∷ CCZ123 ∷ []) (wl0971 (lit c4)) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 3 (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ CCZ124 ∷ []) (wl0972 (lit c4)) ▸
       at 6 2 (CS03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CS03 (lit c4)) ▸
       at 5 2 (CS03 ∷ CCZ123 ∷ []) (wl0490 (lit c4)) ▸
       at 6 4 (CCZ124 ∷ Toff314 ∷ CCZ123 ∷ []) (wl0973 (lit c4)) ▸
       at 8 2 (CS03⁻ ∷ CCZ123 ∷ []) (wl0495 (lit c4)) ▸
       at 9 2 (X4 ∷ CCZ123 ∷ []) (wl0892 (lit c4)) ▸ done

  b17 : Chain (Bx0-2431 ∷ X4 ∷ Bx2-0413 ∷ CCZ124 ∷ Toff314 ∷ CS03 ∷ CCZ124 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CCZ123 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Sb2-0-41-3 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b17 = at 10 2 [] (wl0181 (lit c4)) ▸
       at 3 2 (Toff314 ∷ CCZ124 ∷ []) (wl0974 (lit c4)) ▸
       at 4 2 (CS03 ∷ CCZ124 ∷ []) (lem-comm-CCZ124-CS03 (lit c4)) ▸
       at 5 2 [] (wl0263 (lit c4)) ▸
       at 4 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 2 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0975 (lit c4))) ▸ done

  b18 : Chain (Bx0-2431 ∷ X4 ∷ Sb2-0-41-3 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CCZ024 ∷ CX32 ∷ Toff134 ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b18 = at 2 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (CS03 ∷ []) (refl) ▸
       at 6 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0788 c4)) ▸
       at 2 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 5 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 7 2 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (sym (wl0977 (lit c4))) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸ done

  b19 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CCZ024 ∷ CX32 ∷ Toff134 ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b19 = at 5 2 (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0789 c4) ▸
       at 8 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 7 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 8 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b20 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b20 = at 13 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 8 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0790 c4) ▸
       at 3 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 5 2 (CX32 ∷ Toff213 ∷ []) (sym (wl0809 (lit c4))) ▸
       at 7 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 6 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 7 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸ done

  b21 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ Toff234 ∷ CS34 ∷ Toff213 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b21 = at 8 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 6 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 7 2 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (sym (wl0977 (lit c4))) ▸
       at 9 2 (Toff234 ∷ Toff213 ∷ []) (wl0942 (lit c4)) ▸
       at 11 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 10 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸ done

  b22 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ Toff234 ∷ CS34 ∷ Toff213 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ Toff134 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b22 = at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸
       at 13 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 14 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 10 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 3 3 (CX31 ∷ []) (wl0978 (lit c4)) ▸
       at 5 3 (Toff134 ∷ []) (wl0979 (lit c4)) ▸
       at 3 4 (CX31 ∷ Toff134 ∷ []) (wp0791 c4) ▸ done

  b23 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ Toff134 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b23 = at 2 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 3 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b24 : Chain (Bx0-2431 ∷ X4 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Sb2-0-41-3 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b24 = at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 3 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 1 3 (Toff134 ∷ X4 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (sym (wl0980 (lit c4))) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Sb2-0-41-3 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b25 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 7 2 (CS12 ∷ CS03⁻ ∷ []) (wl0981 (lit c4)) ▸
       at 6 2 (CS12 ∷ Toff314 ∷ []) (sym (wl0982 (lit c4))) ▸
       at 5 2 (CS12 ∷ CS03 ∷ []) (wl0983 (lit c4)) ▸
       at 4 2 (CS12 ∷ Toff314 ∷ []) (sym (wl0982 (lit c4))) ▸
       at 3 2 (CS12 ∷ Bx2-0413 ∷ []) (sym (lem-CSu-box-3-at0210243143 c4)) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ [])
  b26 = at 6 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 8 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 4 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (sym (wl0980 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0975 (lit c4))) ▸
       at 4 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 1 (CS03 ∷ []) (refl) ▸
       at 8 1 (CS03⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b27 = at 5 6 (CX31 ∷ Toff134 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (sym (wp0788 c4)) ▸
       at 4 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 7 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 9 2 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (sym (wl0977 (lit c4))) ▸
       at 6 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 7 2 (CX32 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0789 c4) ▸
       at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b28 = at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 9 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 10 2 (Toff234 ∷ CCZ034 ∷ CCZ024 ∷ []) (wp0790 c4) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff213 ∷ CX31 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Toff213 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b29 = at 5 2 (CX31 ∷ CX32 ∷ Toff213 ∷ []) (sym (wl0976 (lit c4))) ▸
       at 7 2 (CX32 ∷ Toff213 ∷ []) (sym (wl0809 (lit c4))) ▸
       at 9 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 8 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸
       at 11 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 12 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ Toff213 ∷ Toff134 ∷ Toff234 ∷ CCZ034 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b30 = at 8 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 9 2 (Toff134 ∷ Toff234 ∷ Toff213 ∷ []) (sym (wl0977 (lit c4))) ▸
       at 11 2 (Toff234 ∷ Toff213 ∷ []) (wl0942 (lit c4)) ▸
       at 13 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 12 2 (CS34 ∷ Toff213 ∷ []) (sym (wl0808 (lit c4))) ▸
       at 13 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ Toff213 ∷ []) (sym (wl0807 (lit c4))) ▸
       at 15 2 (CX04 ∷ Toff213 ∷ []) (lem-comm-TOFF213-CX04 (lit c4)) ▸ done

  b31 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX31 ∷ CX32 ∷ CX32 ∷ CCZ034 ∷ Toff134 ∷ Toff234 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b31 = at 16 2 (CS03 ∷ Toff213 ∷ []) (sym (wl0196 (lit c4))) ▸
       at 12 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 5 3 (CX31 ∷ []) (wl0978 (lit c4)) ▸
       at 7 3 (Toff134 ∷ []) (wl0979 (lit c4)) ▸
       at 5 4 (CX31 ∷ Toff134 ∷ []) (wp0791 c4) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b32 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ Toff134 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸ done

  b33 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ Toff134 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS12⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸
       at 3 3 (Toff134 ∷ X4 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0984 (lit c4))) ▸
       at 5 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 7 1 (CS03 ∷ []) (refl) ▸
       at 9 1 (CS03⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ CS12⁻ ∷ X4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b34 = at 9 2 (CS12⁻ ∷ CS03⁻ ∷ []) (wl0469 (lit c4)) ▸
       at 8 2 (CS12⁻ ∷ Toff314 ∷ []) (sym (wl0985 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CS03 ∷ []) (wl0986 (lit c4)) ▸
       at 6 2 (CS12⁻ ∷ Toff314 ∷ []) (sym (wl0985 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ Bx2-0413 ∷ []) (sym (lem-CSdu-box-3-at0210243143 c4)) ▸
       at 8 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 10 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 6 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ Sb2-0-41-3 ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ X4 ∷ [])
  b35 = at 4 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0984 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- CXbc-box @122331: 17 steps
lem-CXbc-box-at122331 : Ws → ⟪ (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ234 ∷ []) ⟫ʷ
lem-CXbc-box-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX31 ∷ Bx0-2314 ∷ CX31 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX31 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ CX31 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4) ▸
       at 0 2 (Toff023 ∷ CX31 ∷ []) (wl0832 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (sym (wp0792 c4)) ▸
       at 3 2 (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0793 c4) ▸
       at 2 2 (Toff023 ∷ CX31 ∷ []) (wl0832 (lit c4)) ▸
       at 5 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 8 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CX31 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ CX31 ∷ []) (Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ [])
  b1 = at 7 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 6 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 3 2 (CCZ014 ∷ CX31 ∷ CCZ034 ∷ []) (sym (wp0792 c4)) ▸
       at 4 3 (CX31 ∷ []) (wp0794 c4) ▸
       at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸ done

  b2 : Chain (Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CX31 ∷ []) (Bx0-2314 ∷ CCZ234 ∷ [])
  b2 = at 1 3 (CCZ234 ∷ []) (sym (wl0277 (lit c4))) ▸ done


-- CXcb-box @122331: 18 steps
lem-CXcb-box-at122331 : Ws → ⟪ (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CXcb-box-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CX13 ∷ Bx0-2314 ∷ CX13 ∷ []) (Toff023 ∷ CCZ014 ∷ CX13 ∷ Toff012 ∷ CS14 ∷ CX21 ∷ Toff023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ014 ∷ CX13 ∷ [])
  b0 = at 1 1 (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ []) (lem-box-tQ-at122331 c4) ▸
       at 0 2 (Toff023 ∷ CX13 ∷ Toff012 ∷ []) (wl0987 (lit c4)) ▸
       at 2 2 (CCZ014 ∷ Toff012 ∷ CCZ124 ∷ []) (sym (wp0310 c4)) ▸
       at 1 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸
       at 4 1 (CS14 ∷ CX21 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ []) (wl0271 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS24 ∷ []) (wp0070 c4) ▸
       at 7 2 (Toff023 ∷ CX21 ∷ []) (wl0828 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS14⁻ ∷ []) (lem-comm-CSd14-TOFF023 (lit c4)) ▸ done

  b1 : Chain (Toff023 ∷ CCZ014 ∷ CX13 ∷ Toff012 ∷ CS14 ∷ CX21 ∷ Toff023 ∷ CS14⁻ ∷ CX21 ∷ CS24 ∷ CCZ014 ∷ CX13 ∷ []) (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ [])
  b1 = at 5 2 (Toff023 ∷ CX21 ∷ []) (wl0828 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CS14 ∷ []) (lem-comm-CS14-TOFF023 (lit c4)) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0271 (lit c4))) ▸
       at 3 2 (Toff023 ∷ Toff012 ∷ []) (wl0275 (lit c4)) ▸
       at 2 2 (Toff023 ∷ CX13 ∷ Toff012 ∷ []) (wl0987 (lit c4)) ▸
       at 3 3 (CX13 ∷ []) (wl0988 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ124 ∷ []) (sym (wp0066 c4)) ▸
       at 3 2 (CCZ014 ∷ CX13 ∷ []) (sym (wp0795 c4)) ▸ done

  b2 : Chain (Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX13 ∷ CCZ124 ∷ CX13 ∷ []) (Bx0-2314 ∷ CCZ124 ∷ [])
  b2 = at 0 4 (Bx0-2314 ∷ []) (sym (lem-box-tQ-at122331 c4)) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wl0272 (lit c4))) ▸ done


-- SWbc-box @122331: 11 steps
lem-SWbc-box-at122331 : Ws → ⟪ (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2314 ∷ []) ⟫ʷ
lem-SWbc-box-at122331 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (CX31 ∷ Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ [])
  b0 = at 0 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 4 1 (CX31 ∷ CX13 ∷ CX31 ∷ []) (sym (wl0335 (lit c4))) ▸
       at 2 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CXbc-box-at122331 c4) ▸
       at 3 2 (CX13 ∷ CCZ124 ∷ CCZ234 ∷ []) (wl0281 (lit c4)) ▸
       at 1 3 (Bx0-2314 ∷ CCZ124 ∷ []) (lem-CXcb-box-at122331 c4) ▸
       at 4 2 (CX31 ∷ CCZ234 ∷ []) (wl0336 (lit c4)) ▸
       at 3 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸
       at 2 2 (CX31 ∷ CCZ234 ∷ CCZ124 ∷ []) (wl0279 (lit c4)) ▸ done

  b1 : Chain (CX31 ∷ Bx0-2314 ∷ CX31 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ CCZ124 ∷ CCZ234 ∷ []) (Bx0-2314 ∷ [])
  b1 = at 3 5 (CCZ234 ∷ []) (wl0337 (lit c4)) ▸
       at 0 3 (Bx0-2314 ∷ CCZ234 ∷ []) (lem-CXbc-box-at122331 c4) ▸
       at 1 2 [] (wl0305 (lit c4)) ▸ done


-- nat-SWbc @122331: 23 steps
lem-nat-SWbc-at122331 : Ws → ⟪ (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-nat-SWbc-at122331 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ Sw13 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ Sw13 ∷ [])
  b0 = at 1 1 (CCZ023 ∷ Toff023 ∷ Bx2-014 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ []) (refl) ▸
       at 0 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 1 2 (Toff012 ∷ Sw13 ∷ []) (wl0989 (lit c4)) ▸
       at 3 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 2 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 3 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸
       at 4 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 5 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸ done

  b1 : Chain (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ Sw13 ∷ CCZ012 ∷ Bx0-24 ∷ Toff023 ∷ CCZ023 ∷ Bx2-014 ∷ Sw13 ∷ []) (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Sw13 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Sw13 ∷ [])
  b1 = at 6 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 7 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 8 2 (Toff012 ∷ Sw13 ∷ []) (wl0989 (lit c4)) ▸
       at 9 2 (CCZ012 ∷ Sw13 ∷ []) (sym (wl0285 (lit c4))) ▸
       at 11 1 (CCZ012 ∷ Toff201 ∷ Bx0-24 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ []) (refl) ▸
       at 10 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 11 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸
       at 12 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸ done

  b2 : Chain (CCZ012 ∷ Toff012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Toff203 ∷ CCZ023 ∷ Bx0-24 ∷ Toff012 ∷ CCZ012 ∷ CCZ023 ∷ Toff203 ∷ Bx0-24 ∷ Sw13 ∷ Toff201 ∷ CCZ012 ∷ Bx0-24 ∷ Sw13 ∷ []) (Bx0-2134 ∷ [])
  b2 = at 13 2 (Toff203 ∷ Sw13 ∷ []) (wl0990 (lit c4)) ▸
       at 14 2 (CCZ023 ∷ Sw13 ∷ []) (sym (wl0283 (lit c4))) ▸
       at 15 2 (Bx0-24 ∷ Sw13 ∷ []) (lem-comm-SWAP13-BOX⟨0·24⟩ (lit c4)) ▸
       at 16 2 [] (wl0287 (lit c4)) ▸
       at 2 6 (Bx2-034 ∷ []) (refl) ▸
       at 5 6 (Bx2-034 ∷ []) (refl) ▸
       at 0 6 (Bx0-2134 ∷ []) (refl) ▸ done


-- sym-bc @122331: 2 steps
lem-sym-bc-at122331 : Ws → ⟪ (Bx0-2314 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-2134 ∷ []) ⟫ʷ
lem-sym-bc-at122331 c4 = run b0
  where
  b0 : Chain (Bx0-2314 ∷ []) (Bx0-2134 ∷ [])
  b0 = at 0 1 (Sw13 ∷ Bx0-2314 ∷ Sw13 ∷ []) (sym (lem-SWbc-box-at122331 c4)) ▸
       at 0 3 (Bx0-2134 ∷ []) (lem-nat-SWbc-at122331 c4) ▸ done


-- box-perm-1342 @243243: 3 steps
lem-box-perm-1342-at243243 : Ws → ⟪ (Bx0-1423 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ []) ⟫ʷ
lem-box-perm-1342-at243243 c4 = run b0
  where
  b0 : Chain (Bx0-1423 ∷ []) (Bx0-1234 ∷ [])
  b0 = at 0 1 (Bx0-2314 ∷ []) (lem-pairs-at243243 c4) ▸
       at 0 1 (Bx0-2134 ∷ []) (lem-sym-bc-at122331 c4) ▸
       at 0 1 (Bx0-1234 ∷ []) (lem-sym-ab-at1221 c4) ▸ done


-- F4-CS1-CS0: 214 steps
lem-F4-CS1-CS0 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (run b26))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b0 = at 3 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 3 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 5 1 (CS02 ∷ []) (refl) ▸
       at 7 1 (CS02⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 4 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (wl0512 (lit c4)) ▸
       at 3 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CCZ012 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ034 ∷ CZ03 ∷ CCZ012 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b1 = at 6 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 10 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 9 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 8 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 6 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 7 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 5 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ034 ∷ Toff312 ∷ X4 ∷ CCZ034 ∷ CZ03 ∷ CCZ012 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Bx3-0412 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b2 = at 4 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 5 3 (X4 ∷ []) (wp0798 c4) ▸
       at 6 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸
       at 5 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 2 (Bx3-0412 ∷ CS13⁻ ∷ []) (lem-CSdu-box-3-at0310243142 c4) ▸ done

  b3 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Bx3-0412 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b3 = at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 4 2 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0737 c4)) ▸
       at 6 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 10 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸
       at 9 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 8 2 (Toff312 ∷ CS24⁻ ∷ []) (wl0878 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸ done

  b4 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b4 = at 7 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 5 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 6 3 (CCZ034 ∷ Toff324 ∷ []) (sym (wp0295 c4)) ▸
       at 7 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 4 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 3 2 (Bx3-0412 ∷ CS13 ∷ []) (lem-CSu-box-3-at0310243142 c4) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b5 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b5 = at 2 2 (CCZ034 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0737 c4)) ▸
       at 4 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 8 2 (Toff312 ∷ CS02 ∷ []) (wl0861 (lit c4)) ▸
       at 7 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 6 2 (Toff312 ∷ CS24⁻ ∷ []) (wl0878 (lit c4)) ▸
       at 5 2 (Toff312 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF312 (lit c4)) ▸
       at 4 2 (Toff312 ∷ CS24 ∷ []) (wl0879 (lit c4)) ▸
       at 5 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸ done

  b6 : Chain (X4 ∷ Bx0-1423 ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (X4 ∷ Bx3-0412 ∷ Bx0-1234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b6 = at 3 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 4 3 (CCZ034 ∷ Toff324 ∷ []) (sym (wp0295 c4)) ▸
       at 5 2 (Toff312 ∷ Toff324 ∷ []) (sym (wl0852 (lit c4))) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-1342-at243243 c4) ▸
       at 2 1 (Bx3-0124 ∷ []) (lem-box-perm-1342-at0310243142 c4) ▸
       at 1 2 (Bx3-0124 ∷ Bx0-1234 ∷ []) (lem-box-box-3 c4) ▸
       at 1 1 (Bx3-0412 ∷ []) (lem-box-perm-1423-at03102132 c4) ▸ done

  b7 : Chain (X4 ∷ Bx3-0412 ∷ Bx0-1234 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b7 = at 2 1 (Bx0-1423 ∷ []) (lem-box-perm-1423 c4) ▸
       at 1 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 0 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 2 2 (Toff312 ∷ CZ03 ∷ CCZ012 ∷ []) (wl0512 (lit c4)) ▸
       at 1 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 4 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸
       at 8 2 (CCZ034 ∷ CS02 ∷ []) (sym (wp0003 c4)) ▸
       at 7 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸ done

  b8 : Chain (CCZ034 ∷ Toff312 ∷ X4 ∷ CZ03 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CCZ034 ∷ CX01 ∷ CS02 ∷ Toff312 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ Toff312 ∷ CCZ012 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b8 = at 6 2 (CCZ034 ∷ CS12⁻ ∷ []) (lem-comm-CSd12-CCZ034 (lit c4)) ▸
       at 5 2 (CCZ034 ∷ CX01 ∷ []) (sym (wp0221 c4)) ▸
       at 4 2 (CCZ034 ∷ CS12 ∷ []) (lem-comm-CS12-CCZ034 (lit c4)) ▸
       at 5 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 3 2 (CCZ034 ∷ CZ03 ∷ []) (sym (wp0797 c4)) ▸
       at 2 2 (CCZ034 ∷ X4 ∷ CZ03 ∷ []) (sym (wp0796 c4)) ▸
       at 3 3 (X4 ∷ []) (wp0798 c4) ▸
       at 4 2 (Toff312 ∷ CCZ012 ∷ []) (wl0503 (lit c4)) ▸ done

  b9 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ X4 ∷ Toff312 ∷ CCZ012 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b9 = at 3 2 (Toff312 ∷ X4 ∷ []) (sym (c₄ (Toffᵗ ↑) (X))) ▸
       at 0 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4) ▸
       at 3 2 (Toff023 ∷ CCZ012 ∷ CCZ123 ∷ []) (wl0404 (lit c4)) ▸
       at 5 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 8 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b10 : Chain (Bx3-0412 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ012 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b10 = at 7 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 5 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 6 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 4 2 (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4) ▸
       at 5 3 (Toff023 ∷ CCZ012 ∷ []) (wl0991 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸ done

  b11 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b11 = at 7 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 6 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 4 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 3 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 4 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 4 2 (CS13 ∷ CCZ012 ∷ []) (wl0311 (lit c4)) ▸
       at 5 1 (CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ []) (wl0348 (lit c4)) ▸ done

  b12 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CS12 ∷ CX01 ∷ CS12⁻ ∷ CX01 ∷ CS02 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b12 = at 9 2 (Toff324 ∷ CS02 ∷ []) (wp0298 c4) ▸
       at 8 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 7 2 (Toff324 ∷ CS12⁻ ∷ []) (wl0447 (lit c4)) ▸
       at 6 2 (Toff324 ∷ CX01 ∷ []) (c₂ (CX₀₁) (K ↑ • CCZ • K ↑ • iI)) ▸
       at 5 2 (Toff324 ∷ CS12 ∷ []) (wl0214 (lit c4)) ▸
       at 6 5 (CCZ012 ∷ []) (sym (wl0348 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ CCZ012 ∷ []) (wl0992 (lit c4)) ▸
       at 7 2 (X4 ∷ CCZ012 ∷ []) (wl0993 (lit c4)) ▸ done

  b13 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CCZ012 ∷ CCZ012 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b13 = at 8 2 [] (wl0341 (lit c4)) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 (CX12 ∷ Toff214 ∷ X4 ∷ []) (sym (wl0994 (lit c4))) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸
       at 6 1 (CS13⁻ ∷ []) (refl) ▸ done

  b14 : Chain (Bx3-0412 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CX12 ∷ Toff214 ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ K2 ∷ CS24 ∷ CX12 ∷ Toff034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b14 = at 3 6 (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0995 (lit c4))) ▸
       at 2 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 2 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 5 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 7 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 6 2 (K2 ∷ Toff034 ∷ []) (sym (wp0752 c4)) ▸
       at 7 2 (CS24 ∷ Toff034 ∷ []) (sym (wp0202 c4)) ▸
       at 8 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸ done

  b15 : Chain (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ K2 ∷ CS24 ∷ CX12 ∷ Toff034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b15 = at 9 2 (CS24⁻ ∷ Toff034 ∷ []) (sym (wp0252 c4)) ▸
       at 10 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 11 2 (CS14 ∷ Toff034 ∷ []) (sym (wp0251 c4)) ▸
       at 12 2 (K2⁻ ∷ Toff034 ∷ []) (sym (wp0751 c4)) ▸
       at 6 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 4 3 (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp0799 c4) ▸
       at 3 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 5 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b16 : Chain (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ Toff214 ∷ Toff034 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b16 = at 4 2 (K2 ∷ Toff034 ∷ []) (sym (wp0752 c4)) ▸
       at 5 2 (CS24 ∷ Toff034 ∷ []) (sym (wp0202 c4)) ▸
       at 6 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff034 ∷ []) (sym (wp0252 c4)) ▸
       at 8 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 9 2 (CS14 ∷ Toff034 ∷ []) (sym (wp0251 c4)) ▸
       at 10 2 (K2⁻ ∷ Toff034 ∷ []) (sym (wp0751 c4)) ▸
       at 4 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b17 : Chain (Bx3-0412 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ Toff214 ∷ Toff034 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ X4 ∷ CX12 ∷ Toff214 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b17 = at 5 2 (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) (sym (wp0800 c4)) ▸
       at 7 2 (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) (sym (wp0801 c4)) ▸
       at 5 4 (CZ01 ∷ CCZ014 ∷ []) (sym (wp0802 c4)) ▸
       at 2 5 (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) (wp0803 c4) ▸
       at 4 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸
       at 4 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b18 : Chain (Bx3-0412 ∷ X4 ∷ CX12 ∷ Toff214 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CS02 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b18 = at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (Toff214 ∷ X4 ∷ []) (sym (wl0996 (lit c4))) ▸
       at 4 2 (CS02 ∷ X4 ∷ []) (sym (wl0997 (lit c4))) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 7 2 (CS02 ∷ CS13⁻ ∷ []) (sym (wl0903 (lit c4))) ▸
       at 6 2 (CS02 ∷ Toff324 ∷ []) (sym (wp0298 c4)) ▸ done

  b19 : Chain (Bx3-0412 ∷ Toff214 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ CS02 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ Sb0-1-42-3 ∷ CX12 ∷ Toff214 ∷ X4 ∷ CS02⁻ ∷ [])
  b19 = at 5 2 (CS02 ∷ CS13 ∷ []) (sym (wl0899 (lit c4))) ▸
       at 4 2 (CS02 ∷ Toff324 ∷ []) (sym (wp0298 c4)) ▸
       at 3 2 (CS02 ∷ Bx0-1423 ∷ []) (sym (lem-CSu-box-3-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 2 (CS02 ∷ X4 ∷ []) (sym (wl0997 (lit c4))) ▸
       at 5 2 (CX12 ∷ Toff214 ∷ X4 ∷ []) (sym (wl0994 (lit c4))) ▸ done

  b20 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ Sb0-1-42-3 ∷ CX12 ∷ Toff214 ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ [])
  b20 = at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸
       at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX12 ∷ Toff214 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl0995 (lit c4))) ▸
       at 4 1 (Bx0-1243 ∷ []) (lem-box-perm-1324-at243243 c4) ▸
       at 4 1 (CCZ012 ∷ Toff034 ∷ CCZ012 ∷ Toff034 ∷ []) (lem-box-cP-at3443 c4) ▸
       at 7 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 9 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b21 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ Toff034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ Toff214 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ [])
  b21 = at 8 2 (K2 ∷ Toff034 ∷ []) (sym (wp0752 c4)) ▸
       at 9 2 (CS24 ∷ Toff034 ∷ []) (sym (wp0202 c4)) ▸
       at 10 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff034 ∷ []) (sym (wp0252 c4)) ▸
       at 12 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 13 2 (CS14 ∷ Toff034 ∷ []) (sym (wp0251 c4)) ▸
       at 14 2 (K2⁻ ∷ Toff034 ∷ []) (sym (wp0751 c4)) ▸
       at 8 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b22 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ Toff034 ∷ CCZ012 ∷ CX12 ∷ Toff214 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff034 ∷ CS14 ∷ K2⁻ ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ [])
  b22 = at 6 3 (CX12 ∷ Toff214 ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ []) (wp0799 c4) ▸
       at 5 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 7 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 6 2 (K2 ∷ Toff034 ∷ []) (sym (wp0752 c4)) ▸
       at 7 2 (CS24 ∷ Toff034 ∷ []) (sym (wp0202 c4)) ▸
       at 8 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸
       at 9 2 (CS24⁻ ∷ Toff034 ∷ []) (sym (wp0252 c4)) ▸
       at 10 2 (CX12 ∷ Toff034 ∷ []) (lem-comm-TOFF034-CX12 (lit c4)) ▸ done

  b23 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CCZ012 ∷ CX12 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff034 ∷ CS14 ∷ K2⁻ ∷ CZ01 ∷ CCZ014 ∷ CCZ012 ∷ Toff034 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CX12 ∷ Toff214 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ [])
  b23 = at 11 2 (CS14 ∷ Toff034 ∷ []) (sym (wp0251 c4)) ▸
       at 12 2 (K2⁻ ∷ Toff034 ∷ []) (sym (wp0751 c4)) ▸
       at 6 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 7 2 (CZ01 ∷ CCZ134 ∷ Toff034 ∷ []) (sym (wp0800 c4)) ▸
       at 9 2 (CCZ014 ∷ CCZ134 ∷ Toff034 ∷ []) (sym (wp0801 c4)) ▸
       at 7 4 (CZ01 ∷ CCZ014 ∷ []) (sym (wp0802 c4)) ▸
       at 4 5 (CX12 ∷ Toff214 ∷ CCZ012 ∷ []) (wp0803 c4) ▸
       at 6 4 (Bx0-1243 ∷ []) (sym (lem-box-cP-at3443 c4)) ▸ done

  b24 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ X4 ∷ CX12 ∷ Toff214 ∷ Bx0-1243 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS02⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS02⁻ ∷ X4 ∷ [])
  b24 = at 6 1 (Bx0-1423 ∷ []) (sym (lem-box-perm-1324-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 3 (Toff214 ∷ X4 ∷ []) (sym (wl0996 (lit c4))) ▸
       at 6 2 (CS02⁻ ∷ X4 ∷ []) (sym (wl0998 (lit c4))) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 7 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS02⁻ ∷ X4 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ X4 ∷ CS02⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ [])
  b25 = at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 9 2 (CS02⁻ ∷ CS13⁻ ∷ []) (sym (wl0901 (lit c4))) ▸
       at 8 2 (CS02⁻ ∷ Toff324 ∷ []) (sym (wp0804 c4)) ▸
       at 7 2 (CS02⁻ ∷ CS13 ∷ []) (sym (wl0897 (lit c4))) ▸
       at 6 2 (CS02⁻ ∷ Toff324 ∷ []) (sym (wp0804 c4)) ▸
       at 5 2 (CS02⁻ ∷ Bx0-1423 ∷ []) (sym (lem-CSdu-box-3-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b26 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ X4 ∷ CS02⁻ ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b26 = at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 2 (CS02⁻ ∷ X4 ∷ []) (sym (wl0998 (lit c4))) ▸
       at 2 1 (Sb3-0-2-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 0 5 (Sb3-0-41-2 ∷ []) (refl) ▸
       at 0 1 (Sb2-0-41-3 ∷ []) (sym (lem-F0-at14213243 c4)) ▸ done

