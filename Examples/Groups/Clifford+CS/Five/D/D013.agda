{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D013 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0183 ; wl0184 ; wl0185 ; wl0186 ; wl0187 ; wl0190 ; wl0196 ; wl0206 ; wl0207 ; wl0208 ; wl0209 ; wl0211 ; wl0217 ; wl0221 ; wl0222 ; wl0230 ; wl0232 ; wl0234 ; wl0235 ; wl0241 ; wl0242 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0256 ; wl0274 ; wl0305 ; wl0469 ; wl0645 ; wl0703 ; wl0727 ; wl0735 ; wl0745 ; wl0807 ; wl0808 ; wl0872 ; wl0894 ; wl0896 ; wl0900 ; wl0906 ; wl0907 ; wl0910 ; wl0942 ; wl0975 ; wl0979 ; wl0980 ; wl0981 ; wl0983 ; wl0984 ; wl0986 ; wl1013 ; wl1014 ; wl1017 ; wl1025 ; wl1026 ; wl1027 ; wl1028 ; wl1029 ; wl1030 ; wl1031 ; wl1032 ; wl1033 ; wl1034 ; wl1035 ; wl1036 ; wl1037 ; wl1038 ; wl1039 ; wl1040 ; wl1041 ; wl1042 ; wl1043 ; wl1044 ; wl1045 ; wl1046 ; wl1047 ; wl1048 ; wl1049 ; wl1050 ; wp0007 ; wp0020 ; wp0021 ; wp0022 ; wp0023 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0052 ; wp0053 ; wp0054 ; wp0055 ; wp0062 ; wp0063 ; wp0064 ; wp0067 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0091 ; wp0092 ; wp0093 ; wp0094 ; wp0095 ; wp0096 ; wp0097 ; wp0124 ; wp0265 ; wp0277 ; wp0278 ; wp0352 ; wp0546 ; wp0617 ; wp0632 ; wp0633 ; wp0657 ; wp0659 ; wp0663 ; wp0673 ; wp0725 ; wp0768 ; wp0785 ; wp0786 ; wp0787 ; wp0793 ; wp0816 ; wp0817 ; wp0818 ; wp0819 ; wp0823 ; wp0828 ; wp0829 ; wp0830 ; wp0831 ; wp0832 ; wp0833 ; wp0834 ; wp0835 ; wp0836 ; wp0837 ; wp0838 ; wp0839 ; wp0840 ; wp0841 ; wp0842 ; wp0843 ; wp0844 ; wp0845 ; wp0846 ; wp0847 ; wp0848 ; wp0849)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D001 using (lem-box-cP-at0210243143 ; lem-box-cP-at122441 ; lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-box-perm-2431)
open import Examples.Groups.Clifford+CS.Five.D.D004 using (lem-box-box-2)
open import Examples.Groups.Clifford+CS.Five.D.D006 using (lem-box-cP-at12233441 ; lem-box-perm-1324-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D010 using (lem-CSdu-box-3-at122441 ; lem-CSu-box-3-at122441 ; lem-box-perm-1342-at0210243143)
open import Examples.Groups.Clifford+CS.Five.D.D011 using (lem-CSdu-box-3-at0210243143 ; lem-CSu-box-3-at0210243143 ; lem-box-perm-1423-at021021)
open import Examples.Groups.Clifford+CS.Five.D.D012 using (lem-box-perm-3241-at243243 ; lem-box-perm-4132-at122441 ; lem-box-perm-4213-at122441)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX04-TOFF213 ; lem-comm-CX13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CS23-CCZ014 ; lem-comm-CX14-TOFF023 ; lem-comm-CX23-CCZ014 ; lem-comm-CX24-TOFF013 ; lem-comm-CZ13-CCZ024 ; lem-comm-TOFF013-CSd24)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ024-CX13)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-CCZ024-CX31 ; lem-comm-CCZ034-CS12 ; lem-comm-TOFF013-CS24 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF014-CX23)
-- F4-CS2-CS0: 284 steps
lem-F4-CS2-CS0 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb2-0-41-3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 3 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 5 1 (CS03 ∷ []) (refl) ▸
       at 7 1 (CS03⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 4 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 6 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ CCZ024 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 9 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 8 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 7 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ013 ∷ Toff213 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 6 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 5 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 2 (Bx2-0413 ∷ CS12⁻ ∷ []) (lem-CSdu-box-3-at0210243143 c4) ▸
       at 5 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸ done

  b3 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b3 = at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸ done

  b4 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b4 = at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl1025 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (sym (wp0768 c4)) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 12 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 11 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 10 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸ done

  b5 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b5 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 6 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 7 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 9 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 13 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸
       at 12 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 11 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ Toff213 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Bx2-0413 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b6 = at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 10 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 8 2 (Toff213 ∷ Toff234 ∷ []) (sym (wl0942 (lit c4))) ▸
       at 7 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl1025 (lit c4)) ▸
       at 8 3 (Toff134 ∷ []) (wl0979 (lit c4)) ▸
       at 4 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸ done

  b7 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Bx2-0413 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b7 = at 3 2 (Bx2-0413 ∷ CS12 ∷ []) (lem-CSu-box-3-at0210243143 c4) ▸
       at 3 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b8 = at 3 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 2 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 3 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl1025 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ Toff234 ∷ CCZ034 ∷ []) (sym (wp0768 c4)) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b9 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff234 ∷ CCZ034 ∷ Toff213 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b9 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 7 1 (CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ CS03 ∷ []) (wp0352 c4) ▸
       at 11 2 (Toff213 ∷ CS03 ∷ []) (wl0196 (lit c4)) ▸ done

  b10 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff134 ∷ Toff234 ∷ CS34 ∷ CX04 ∷ CS34⁻ ∷ CX04 ∷ Toff213 ∷ CS03 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b10 = at 10 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 9 2 (Toff213 ∷ CS34⁻ ∷ []) (wl0807 (lit c4)) ▸
       at 8 2 (Toff213 ∷ CX04 ∷ []) (lem-comm-CX04-TOFF213 (lit c4)) ▸
       at 7 2 (Toff213 ∷ CS34 ∷ []) (wl0808 (lit c4)) ▸
       at 8 5 (CCZ034 ∷ []) (sym (wp0352 c4)) ▸
       at 6 2 (Toff213 ∷ Toff234 ∷ []) (sym (wl0942 (lit c4))) ▸
       at 5 2 (Toff213 ∷ Toff134 ∷ Toff234 ∷ []) (wl1025 (lit c4)) ▸
       at 6 3 (Toff134 ∷ []) (wl0979 (lit c4)) ▸ done

  b11 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b11 = at 2 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 1 (Bx0-1234 ∷ []) (lem-box-perm-4132-at122441 c4) ▸
       at 2 1 (Bx2-0134 ∷ []) (lem-box-perm-1342-at0210243143 c4) ▸
       at 1 2 (Bx2-0134 ∷ Bx0-1234 ∷ []) (lem-box-box-2 c4) ▸
       at 1 1 (Bx2-0413 ∷ []) (lem-box-perm-1423-at021021 c4) ▸
       at 2 1 (Bx0-2431 ∷ []) (lem-box-perm-2431 c4) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b12 : Chain (CCZ024 ∷ X4 ∷ CZ02 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b12 = at 2 2 (Toff213 ∷ CZ02 ∷ CCZ013 ∷ []) (wl0183 (lit c4)) ▸
       at 1 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 4 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 7 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 6 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff213 ∷ X4 ∷ CZ02 ∷ CCZ024 ∷ CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ Toff213 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b13 = at 5 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff213 ∷ CCZ013 ∷ []) (wl0186 (lit c4)) ▸
       at 3 2 (Toff213 ∷ X4 ∷ []) (sym (c₄ ((K ↑ • CCZ • K ↑ • iI) ↑) (X))) ▸
       at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b14 : Chain (Bx2-0413 ∷ X4 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CZ13 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b14 = at 2 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 5 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 4 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 2 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 3 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 3 2 (Toff013 ∷ CZ13 ∷ CCZ013 ∷ []) (wl0906 (lit c4)) ▸ done

  b15 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CZ13 ∷ CCZ013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b15 = at 5 1 (CS13 ∷ CX01 ∷ CS13⁻ ∷ CX01 ∷ CS03 ∷ []) (wl0184 (lit c4)) ▸
       at 9 2 (CCZ024 ∷ CS03 ∷ []) (sym (wp0021 c4)) ▸
       at 8 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CX01 ∷ []) (sym (wp0022 c4)) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 6 5 (CCZ013 ∷ []) (sym (wl0184 (lit c4))) ▸
       at 4 2 (CCZ024 ∷ CZ13 ∷ []) (lem-comm-CZ13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CZ13 ∷ CCZ013 ∷ Toff013 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b16 = at 5 3 (Toff013 ∷ CCZ013 ∷ []) (wl1026 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 3 (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ CCZ034 ∷ []) (wp0828 c4) ▸
       at 6 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 5 2 (CS12 ∷ CCZ013 ∷ []) (wl0645 (lit c4)) ▸
       at 6 4 (Toff134 ∷ CCZ034 ∷ CCZ013 ∷ []) (wp0829 c4) ▸
       at 8 2 (CS12⁻ ∷ CCZ013 ∷ []) (wl0703 (lit c4)) ▸
       at 9 2 (X4 ∷ CCZ013 ∷ []) (wp0830 c4) ▸ done

  b17 : Chain (Bx2-0413 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ034 ∷ CS12 ∷ Toff134 ∷ CCZ034 ∷ CS12⁻ ∷ X4 ∷ CCZ013 ∷ CCZ013 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ Sb0-2-43-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b17 = at 10 2 [] (wl0230 (lit c4)) ▸
       at 4 2 (CS12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CS12 (lit c4)) ▸
       at 5 2 (Toff134 ∷ CCZ034 ∷ []) (wp0831 c4) ▸
       at 6 2 [] (wp0007 c4) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸ done

  b18 : Chain (Bx2-0413 ∷ X4 ∷ Sb0-2-43-1 ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CX13 ∷ Toff014 ∷ Toff314 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b18 = at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1027 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (sym (wl1028 (lit c4))) ▸
       at 7 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp0832 c4) ▸
       at 4 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸ done

  b19 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CCZ024 ∷ CX13 ∷ Toff014 ∷ Toff314 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b19 = at 6 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 7 2 (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0833 c4) ▸
       at 10 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 9 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b20 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b20 = at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 9 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 3 2 (CX10 ∷ Toff013 ∷ []) (sym (wl1029 (lit c4))) ▸
       at 5 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 5 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 6 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸ done

  b21 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ Toff013 ∷ CX12 ∷ CS14 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b21 = at 7 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 8 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 5 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (sym (wl1028 (lit c4))) ▸
       at 7 2 (Toff014 ∷ Toff013 ∷ []) (wp0786 c4) ▸
       at 9 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸ done

  b22 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ Toff013 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX13 ∷ Toff314 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b22 = at 10 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 12 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 8 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 9 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp0832 c4) ▸
       at 3 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0787 c4)) ▸
       at 3 4 (CX13 ∷ Toff314 ∷ []) (wl1030 (lit c4)) ▸ done

  b23 : Chain (Bx2-0413 ∷ X4 ∷ CCZ024 ∷ CX13 ∷ Toff314 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ X4 ∷ CX13 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b23 = at 2 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 4 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 3 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b24 : Chain (Bx2-0413 ∷ X4 ∷ CX13 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Sb0-2-43-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b24 = at 9 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 3 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (Toff314 ∷ X4 ∷ []) (sym (wl0187 (lit c4))) ▸
       at 4 2 (CS03 ∷ X4 ∷ []) (sym (wp0657 c4)) ▸ done

  b25 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ Sb0-2-43-1 ∷ CS03 ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b25 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 7 2 (CS03 ∷ CS12⁻ ∷ []) (sym (wl0986 (lit c4))) ▸
       at 6 2 (CS03 ∷ Toff134 ∷ []) (sym (wp0277 c4)) ▸
       at 5 2 (CS03 ∷ CS12 ∷ []) (sym (wl0983 (lit c4))) ▸
       at 4 2 (CS03 ∷ Toff134 ∷ []) (sym (wp0277 c4)) ▸
       at 3 2 (CS03 ∷ Bx0-2431 ∷ []) (sym (lem-CSu-box-3-at122441 c4)) ▸ done

  b26 : Chain (Bx2-0413 ∷ Toff314 ∷ X4 ∷ CS03 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff314 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ [])
  b26 = at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 2 (CS03 ∷ X4 ∷ []) (sym (wp0657 c4)) ▸
       at 5 2 (CX13 ∷ Toff314 ∷ X4 ∷ []) (sym (wl0745 (lit c4))) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX13 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b27 = at 5 6 (CX13 ∷ Toff314 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1027 (lit c4))) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (sym (wl1028 (lit c4))) ▸
       at 9 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp0832 c4) ▸
       at 6 2 (CX10 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0673 c4) ▸
       at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (Toff014 ∷ CCZ124 ∷ CCZ024 ∷ []) (wp0833 c4) ▸
       at 12 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸ done

  b28 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ CCZ024 ∷ K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b28 = at 11 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 17 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 11 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸ done

  b29 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX10 ∷ CCZ124 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ Toff013 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b29 = at 5 2 (CX10 ∷ Toff013 ∷ []) (sym (wl1029 (lit c4))) ▸
       at 7 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 6 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 7 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 8 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 9 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 10 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸ done

  b30 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ Toff013 ∷ CX13 ∷ Toff014 ∷ CCZ124 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b30 = at 7 2 (CX10 ∷ CX13 ∷ Toff013 ∷ []) (sym (wl1028 (lit c4))) ▸
       at 9 2 (Toff014 ∷ Toff013 ∷ []) (wp0786 c4) ▸
       at 11 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CS24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CS24 (lit c4)) ▸
       at 11 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 12 2 (CS24⁻ ∷ Toff013 ∷ []) (lem-comm-TOFF013-CSd24 (lit c4)) ▸
       at 13 2 (CX12 ∷ Toff013 ∷ []) (sym (wl0872 (lit c4))) ▸
       at 14 2 (CS14 ∷ Toff013 ∷ []) (sym (wp0785 c4)) ▸ done

  b31 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CCZ024 ∷ CX10 ∷ CCZ124 ∷ CX10 ∷ CX13 ∷ Toff014 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff013 ∷ Toff314 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b31 = at 10 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 11 2 (Toff014 ∷ Toff314 ∷ Toff013 ∷ []) (wp0832 c4) ▸
       at 5 3 (CCZ124 ∷ []) (sym (wp0663 c4)) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wp0787 c4)) ▸
       at 5 4 (CX13 ∷ Toff314 ∷ []) (wl1030 (lit c4)) ▸
       at 4 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 1 (K3 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ []) (sym (wl0190 (lit c4))) ▸
       at 5 2 (K3 ∷ CCZ024 ∷ []) (wp0037 c4) ▸ done

  b32 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ K3 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K3⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K3⁻ ∷ CCZ024 ∷ []) (wp0033 c4) ▸
       at 5 7 (Toff314 ∷ []) (wl0190 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b33 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ X4 ∷ CX13 ∷ Toff314 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS03⁻ ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS03⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 3 (Toff314 ∷ X4 ∷ []) (sym (wl0187 (lit c4))) ▸
       at 6 2 (CS03⁻ ∷ X4 ∷ []) (sym (wp0659 c4)) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS03⁻ ∷ X4 ∷ []) (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b34 = at 9 2 (CS03⁻ ∷ CS12⁻ ∷ []) (sym (wl0469 (lit c4))) ▸
       at 8 2 (CS03⁻ ∷ Toff134 ∷ []) (sym (wp0834 c4)) ▸
       at 7 2 (CS03⁻ ∷ CS12 ∷ []) (sym (wl0981 (lit c4))) ▸
       at 6 2 (CS03⁻ ∷ Toff134 ∷ []) (sym (wp0834 c4)) ▸
       at 5 2 (CS03⁻ ∷ Bx0-2431 ∷ []) (sym (lem-CSdu-box-3-at122441 c4)) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

  b35 : Chain (Bx2-0413 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ X4 ∷ CS03⁻ ∷ Sb0-2-43-1 ∷ X4 ∷ []) (Sb2-0-41-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b35 = at 4 2 (CS03⁻ ∷ X4 ∷ []) (sym (wp0659 c4)) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F4-CS2-CS1: 254 steps
lem-F4-CS2-CS1 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (run b31)))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 4 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b1 = at 10 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 9 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 8 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 4 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ X4 ∷ CZ01 ∷ CZ01 ∷ CCZ123 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ014 ∷ CS12⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 5 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸ done

  b3 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ014 ∷ CS12⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff023 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b3 = at 6 2 (Toff023 ∷ CS12⁻ ∷ []) (wl1017 (lit c4)) ▸
       at 7 2 (CCZ014 ∷ CS12⁻ ∷ []) (sym (wp0265 c4)) ▸
       at 8 2 (Toff023 ∷ CS12⁻ ∷ []) (wl1017 (lit c4)) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 4 2 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (sym (wp0835 c4)) ▸
       at 6 2 (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0793 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸ done

  b4 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff023 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b4 = at 11 2 (Toff023 ∷ K1⁻ ∷ []) (wl1014 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS34⁻ ∷ []) (wp0823 c4) ▸
       at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸
       at 5 2 (Toff023 ∷ K1 ∷ []) (wl0735 (lit c4)) ▸
       at 6 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸ done

  b5 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ014 ∷ CCZ034 ∷ CCZ234 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b5 = at 8 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 12 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 11 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 9 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 7 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸ done

  b6 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ014 ∷ CCZ034 ∷ CCZ234 ∷ Toff023 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b6 = at 6 2 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (sym (wp0835 c4)) ▸
       at 7 3 (Toff134 ∷ []) (wp0836 c4) ▸
       at 8 2 (Toff023 ∷ CCZ234 ∷ []) (wp0278 c4) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸
       at 13 2 (Toff023 ∷ K1⁻ ∷ []) (wl1014 (lit c4)) ▸
       at 12 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 11 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CS34⁻ ∷ []) (wp0823 c4) ▸ done

  b7 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ014 ∷ CS12 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b7 = at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸
       at 7 2 (Toff023 ∷ K1 ∷ []) (wl0735 (lit c4)) ▸
       at 8 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸ done

  b8 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ014 ∷ CS12 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff023 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b8 = at 4 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CS12 ∷ []) (sym (wp0067 c4)) ▸
       at 6 2 (Toff023 ∷ CS12 ∷ []) (wl0221 (lit c4)) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 2 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (sym (wp0835 c4)) ▸
       at 4 2 (Toff023 ∷ CCZ034 ∷ CCZ234 ∷ []) (wp0793 c4) ▸
       at 3 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸ done

  b9 : Chain (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff023 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b9 = at 9 2 (Toff023 ∷ K1⁻ ∷ []) (wl1014 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS34⁻ ∷ []) (wp0823 c4) ▸
       at 5 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸
       at 3 2 (Toff023 ∷ K1 ∷ []) (wl0735 (lit c4)) ▸
       at 4 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸ done

  b10 : Chain (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ034 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ014 ∷ CCZ034 ∷ CCZ234 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b10 = at 6 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 10 2 (CCZ014 ∷ CS24 ∷ []) (sym (wp0062 c4)) ▸
       at 9 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS34⁻ ∷ []) (sym (wp0063 c4)) ▸
       at 7 2 (CCZ014 ∷ CX23 ∷ []) (lem-comm-CX23-CCZ014 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS34 ∷ []) (sym (wp0064 c4)) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 5 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸ done

  b11 : Chain (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CCZ014 ∷ CCZ034 ∷ CCZ234 ∷ Toff023 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b11 = at 4 2 (CCZ014 ∷ Toff134 ∷ CCZ034 ∷ []) (sym (wp0835 c4)) ▸
       at 5 3 (Toff134 ∷ []) (wp0836 c4) ▸
       at 6 2 (Toff023 ∷ CCZ234 ∷ []) (wp0278 c4) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸
       at 11 2 (Toff023 ∷ K1⁻ ∷ []) (wl1014 (lit c4)) ▸
       at 10 2 (Toff023 ∷ CS13 ∷ []) (wl0222 (lit c4)) ▸
       at 9 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 8 2 (Toff023 ∷ CS34⁻ ∷ []) (wp0823 c4) ▸ done

  b12 : Chain (X4 ∷ Bx0-2431 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b12 = at 7 2 (Toff023 ∷ CX14 ∷ []) (lem-comm-CX14-TOFF023 (lit c4)) ▸
       at 6 2 (Toff023 ∷ CS34 ∷ []) (wp0725 c4) ▸
       at 5 2 (Toff023 ∷ K1 ∷ []) (wl0735 (lit c4)) ▸
       at 6 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 1 (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4) ▸
       at 2 1 (Bx0-2431 ∷ []) (lem-box-perm-3241-at243243 c4) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸ done

  b13 : Chain (X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b13 = at 0 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 2 2 (Toff023 ∷ CZ01 ∷ CCZ123 ∷ []) (wl0206 (lit c4)) ▸
       at 1 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b14 : Chain (CCZ014 ∷ Toff023 ∷ X4 ∷ CZ01 ∷ CS23 ∷ CCZ014 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ123 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b14 = at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (CCZ014 ∷ CZ01 ∷ []) (sym (wp0055 c4)) ▸
       at 2 2 (CCZ014 ∷ X4 ∷ CZ01 ∷ []) (sym (wp0052 c4)) ▸
       at 3 3 (X4 ∷ []) (wl0208 (lit c4)) ▸
       at 4 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 3 2 (Toff023 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ • (Swap ↑ ↑ • Toff • Swap ↑ ↑) • Swap ↑) (X))) ▸
       at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸ done

  b15 : Chain (Bx0-1423 ∷ X4 ∷ CCZ123 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ024 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b15 = at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done

  b16 : Chain (Bx0-1423 ∷ X4 ∷ CCZ024 ∷ CCZ123 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b16 = at 3 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸ done

  b17 : Chain (Bx0-1423 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b17 = at 5 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 8 (Toff134 ∷ CCZ234 ∷ CS12 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl1031 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸
       at 4 3 (CS12 ∷ Toff134 ∷ CCZ234 ∷ []) (wl1032 (lit c4)) ▸
       at 6 2 [] (wl0305 (lit c4)) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b18 : Chain (Bx0-1423 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ X4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b18 = at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸
       at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1033 (lit c4))) ▸
       at 2 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 2 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸ done

  b19 : Chain (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b19 = at 5 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 6 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 7 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 8 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 10 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 11 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸ done

  b20 : Chain (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ Toff014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b20 = at 12 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 3 (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp0837 c4) ▸
       at 3 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 4 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 5 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 6 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸ done

  b21 : Chain (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ Toff014 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b21 = at 7 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 8 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 9 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 10 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 2 (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0838 c4)) ▸
       at 7 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 5 4 (CZ02 ∷ CCZ024 ∷ []) (sym (wp0840 c4)) ▸ done

  b22 : Chain (Bx0-1423 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb0-2-43-1 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b22 = at 2 5 (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) (wp0841 c4) ▸
       at 4 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (Toff324 ∷ X4 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 4 2 (CS13 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸ done

  b23 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ Sb0-2-43-1 ∷ CS13 ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CCZ024 ∷ CS13 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b23 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 5 (CS13 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1034 (lit c4))) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS13 ∷ Toff013 ∷ []) (sym (wl0910 (lit c4))) ▸
       at 5 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 4 2 (CS13 ∷ Toff013 ∷ []) (sym (wl0910 (lit c4))) ▸ done

  b24 : Chain (Bx0-1423 ∷ Toff324 ∷ X4 ∷ CCZ024 ∷ CS13 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff324 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ [])
  b24 = at 3 2 (CS13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CS13 (lit c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 2 (CS13 ∷ X4 ∷ []) (sym (wl0896 (lit c4))) ▸
       at 5 2 (CX23 ∷ Toff324 ∷ X4 ∷ []) (sym (wl0894 (lit c4))) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CX23 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ Toff014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b25 = at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 6 (CX23 ∷ Toff324 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1033 (lit c4))) ▸
       at 4 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 4 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 7 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 9 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 8 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸ done

  b26 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ Toff014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b26 = at 9 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 10 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 12 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 13 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸
       at 14 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 3 (CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ []) (wp0837 c4) ▸ done

  b27 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ Toff014 ∷ CX23 ∷ Toff324 ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b27 = at 5 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 6 2 (K3 ∷ Toff014 ∷ []) (sym (wp0819 c4)) ▸
       at 7 2 (CS34 ∷ Toff014 ∷ []) (sym (wp0546 c4)) ▸
       at 8 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff014 ∷ []) (sym (wp0818 c4)) ▸
       at 10 2 (CX23 ∷ Toff014 ∷ []) (lem-comm-TOFF014-CX23 (lit c4)) ▸
       at 11 2 (CS24 ∷ Toff014 ∷ []) (sym (wp0817 c4)) ▸ done

  b28 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CCZ023 ∷ CX23 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CZ02 ∷ CCZ024 ∷ CCZ023 ∷ Toff014 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ [])
  b28 = at 12 2 (K3⁻ ∷ Toff014 ∷ []) (sym (wp0816 c4)) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 7 2 (CZ02 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0838 c4)) ▸
       at 9 2 (CCZ024 ∷ CCZ124 ∷ Toff014 ∷ []) (sym (wp0839 c4)) ▸
       at 7 4 (CZ02 ∷ CCZ024 ∷ []) (sym (wp0840 c4)) ▸
       at 4 5 (CX23 ∷ Toff324 ∷ CCZ023 ∷ []) (wp0841 c4) ▸
       at 6 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 6 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸ done

  b29 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ X4 ∷ CX23 ∷ Toff324 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS13⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ X4 ∷ [])
  b29 = at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 3 (Toff324 ∷ X4 ∷ []) (sym (wl0211 (lit c4))) ▸
       at 6 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0900 (lit c4))) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b30 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS13⁻ ∷ X4 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b30 = at 6 5 (CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1035 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff013 ∷ []) (sym (wl0907 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 6 2 (CS13⁻ ∷ Toff013 ∷ []) (sym (wl0907 (lit c4))) ▸
       at 5 2 (CS13⁻ ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CSd13 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b31 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ X4 ∷ CS13⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b31 = at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 4 2 (CS13⁻ ∷ X4 ∷ []) (sym (wl0900 (lit c4))) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done


-- F4-CS2-CS2: 286 steps
lem-F4-CS2-CS2 : Ws → ⟪ (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS2-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 4 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-2-43-1 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸ done

  b3 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 6 2 (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS12⁻ ∷ []) (sym (wp0087 c4)) ▸
       at 8 2 (Toff013 ∷ CS12⁻ ∷ []) (wl0244 (lit c4)) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 10 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 9 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸ done

  b4 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CCZ024 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 8 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 4 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 5 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b5 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b5 = at 13 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 12 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 11 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 10 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 7 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 8 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b6 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b6 = at 6 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸
       at 9 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 8 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 12 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 11 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 10 2 (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4) ▸
       at 9 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸ done

  b7 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff034 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b7 = at 9 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 7 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸
       at 8 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CS12 ∷ []) (refl) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 4 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸ done

  b8 : Chain (X4 ∷ Bx0-2431 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b8 = at 5 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 6 2 (Toff013 ∷ CS12 ∷ []) (wl0247 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 8 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸
       at 7 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 6 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b9 : Chain (X4 ∷ Bx0-2431 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CCZ024 ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b9 = at 5 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 4 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 3 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 2 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 3 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 11 2 (CCZ024 ∷ K1⁻ ∷ []) (sym (wp0088 c4)) ▸ done

  b10 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b10 = at 10 2 (CCZ024 ∷ CS14 ∷ []) (sym (wp0034 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS34⁻ ∷ []) (sym (wp0035 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS34 ∷ []) (sym (wp0036 c4)) ▸
       at 5 2 (CCZ024 ∷ K1 ∷ []) (sym (wp0089 c4)) ▸
       at 6 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ Toff034 ∷ CCZ234 ∷ []) (sym (wp0096 c4)) ▸ done

  b11 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b11 = at 7 2 (Toff013 ∷ Toff034 ∷ Toff134 ∷ []) (sym (wp0093 c4)) ▸
       at 6 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 10 2 (Toff013 ∷ CS23 ∷ []) (wl0246 (lit c4)) ▸
       at 9 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS34⁻ ∷ []) (wp0094 c4) ▸
       at 7 2 (Toff013 ∷ CX24 ∷ []) (lem-comm-CX24-TOFF013 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CS34 ∷ []) (wp0095 c4) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b12 : Chain (X4 ∷ Bx0-2431 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff013 ∷ CCZ234 ∷ Toff034 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b12 = at 5 2 (Toff013 ∷ Toff034 ∷ []) (sym (wp0097 c4)) ▸
       at 6 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b13 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b13 = at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b14 = at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b15 : Chain (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b15 = at 4 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 3 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸ done

  b16 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CCZ024 ∷ CX13 ∷ CS12 ∷ Toff013 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b16 = at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 8 (CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl1036 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b17 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-2431 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b17 = at 3 3 (Toff134 ∷ CS12 ∷ CCZ234 ∷ []) (wl1037 (lit c4)) ▸
       at 5 2 [] (wl0305 (lit c4)) ▸
       at 4 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 2 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0975 (lit c4))) ▸
       at 2 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (CS12 ∷ []) (refl) ▸ done

  b18 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b18 = at 6 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1038 (lit c4))) ▸
       at 2 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (sym (wl1039 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 4 2 (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0844 c4) ▸
       at 6 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 7 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸ done

  b19 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b19 = at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸ done

  b20 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b20 = at 9 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 3 2 (CX30 ∷ Toff013 ∷ []) (sym (wl1040 (lit c4))) ▸
       at 5 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 4 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 5 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸ done

  b21 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ CX30 ∷ CX31 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b21 = at 4 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 5 2 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (sym (wl1039 (lit c4))) ▸
       at 7 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 9 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 8 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 11 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸ done

  b22 : Chain (Bx0-2431 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ CX30 ∷ CX31 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CX31 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b22 = at 12 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 8 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 9 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 3 3 (CCZ234 ∷ []) (sym (wp0846 c4)) ▸
       at 5 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 3 4 (CX31 ∷ Toff134 ∷ []) (wl1041 (lit c4)) ▸
       at 2 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 4 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b23 : Chain (Bx0-2431 ∷ X4 ∷ CX31 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CX31 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b23 = at 3 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 4 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 5 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 6 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 9 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 3 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b24 : Chain (Bx0-2431 ∷ X4 ∷ CX31 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b24 = at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 1 3 (Toff134 ∷ X4 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (sym (wl0980 (lit c4))) ▸
       at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b25 = at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 4 5 (CS12 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1042 (lit c4))) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 6 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 4 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ [])
  b26 = at 6 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 4 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (sym (wl0980 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0975 (lit c4))) ▸
       at 4 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 1 (CS12 ∷ []) (refl) ▸
       at 8 1 (CS12⁻ ∷ []) (refl) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b27 = at 5 6 (CX31 ∷ Toff134 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1038 (lit c4))) ▸
       at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 7 2 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (sym (wl1039 (lit c4))) ▸
       at 9 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 2 (CX30 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0844 c4) ▸
       at 8 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 9 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 12 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b28 = at 11 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 12 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 15 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 17 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 11 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ Toff013 ∷ CX30 ∷ CCZ234 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ Toff013 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b29 = at 5 2 (CX30 ∷ Toff013 ∷ []) (sym (wl1040 (lit c4))) ▸
       at 7 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 6 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 7 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 9 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 10 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ Toff013 ∷ CX31 ∷ Toff034 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ CX30 ∷ CX31 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b30 = at 7 2 (CX30 ∷ CX31 ∷ Toff013 ∷ []) (sym (wl1039 (lit c4))) ▸
       at 9 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 11 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 10 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 11 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 13 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 14 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸ done

  b31 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ024 ∷ CX30 ∷ CCZ234 ∷ CX30 ∷ CX31 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b31 = at 10 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 11 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 5 3 (CCZ234 ∷ []) (sym (wp0846 c4)) ▸
       at 7 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 5 4 (CX31 ∷ Toff134 ∷ []) (wl1041 (lit c4)) ▸
       at 4 2 (CX31 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX31 (lit c4)) ▸
       at 6 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 5 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸ done

  b32 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ K1 ∷ CCZ024 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b32 = at 6 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 7 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 9 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 11 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 5 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸ done

  b33 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CX31 ∷ Toff134 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12⁻ ∷ X4 ∷ [])
  b33 = at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 3 3 (Toff134 ∷ X4 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0984 (lit c4))) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸ done

  b34 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ CS12⁻ ∷ X4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ [])
  b34 = at 6 5 (CS12⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (sym (wl1043 (lit c4))) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 6 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 8 1 (Sb0-2-1-3 ∷ []) (refl) ▸ done

  b35 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ CS12⁻ ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-2-43-1 ∷ X4 ∷ [])
  b35 = at 10 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 6 5 (Sb0-2-43-1 ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0984 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done


-- F2-I-S0: 1 steps
lem-F2-I-S0 : Ws → ⟪ (S4 ∷ CS04 ∷ []) ⟫ʷ ≈ ⟪ (CS04 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS04 ∷ []) (CS04 ∷ S4 ∷ [])
  b0 = at 0 2 (CS04 ∷ S4 ∷ []) (sym (wp0847 c4)) ▸ done


-- F2-I-S1: 1 steps
lem-F2-I-S1 : Ws → ⟪ (S4 ∷ CS14 ∷ []) ⟫ʷ ≈ ⟪ (CS14 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS14 ∷ []) (CS14 ∷ S4 ∷ [])
  b0 = at 0 2 (CS14 ∷ S4 ∷ []) (sym (wl1044 (lit c4))) ▸ done


-- F2-I-S2: 1 steps
lem-F2-I-S2 : Ws → ⟪ (S4 ∷ CS24 ∷ []) ⟫ʷ ≈ ⟪ (CS24 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS24 ∷ []) (CS24 ∷ S4 ∷ [])
  b0 = at 0 2 (CS24 ∷ S4 ∷ []) (sym (wl1045 (lit c4))) ▸ done


-- F2-I-S3: 1 steps
lem-F2-I-S3 : Ws → ⟪ (S4 ∷ CS34 ∷ []) ⟫ʷ ≈ ⟪ (CS34 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-S3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CS34 ∷ []) (CS34 ∷ S4 ∷ [])
  b0 = at 0 2 (CS34 ∷ S4 ∷ []) (sym (wl1046 (lit c4))) ▸ done


-- F2-I-K0: 1 steps
lem-F2-I-K0 : Ws → ⟪ (S4 ∷ CK40 ∷ []) ⟫ʷ ≈ ⟪ (CK40 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K0 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK40 ∷ []) (CK40 ∷ S4 ∷ [])
  b0 = at 0 2 (CK40 ∷ S4 ∷ []) (sym (wp0848 c4)) ▸ done


-- F2-I-K1: 1 steps
lem-F2-I-K1 : Ws → ⟪ (S4 ∷ CK41 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K1 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK41 ∷ []) (CK41 ∷ S4 ∷ [])
  b0 = at 0 2 (CK41 ∷ S4 ∷ []) (sym (wl1047 (lit c4))) ▸ done


-- F2-I-K2: 1 steps
lem-F2-I-K2 : Ws → ⟪ (S4 ∷ CK42 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K2 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK42 ∷ []) (CK42 ∷ S4 ∷ [])
  b0 = at 0 2 (CK42 ∷ S4 ∷ []) (sym (wl1048 (lit c4))) ▸ done


-- F2-I-K3: 1 steps
lem-F2-I-K3 : Ws → ⟪ (S4 ∷ CK43 ∷ []) ⟫ʷ ≈ ⟪ (CK43 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-K3 c4 = run b0
  where
  b0 : Chain (S4 ∷ CK43 ∷ []) (CK43 ∷ S4 ∷ [])
  b0 = at 0 2 (CK43 ∷ S4 ∷ []) (sym (wl1049 (lit c4))) ▸ done


-- F2-I-CS0: 13 steps
lem-F2-I-CS0 : Ws → ⟪ (S4 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS0 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S4 ∷ Sb2-0-41-3 ∷ []) (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ [])
  b0 = at 1 1 (Bx2-0413 ∷ Toff314 ∷ Sb2-0-3-1 ∷ Toff314 ∷ Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 3 1 (CS03 ∷ []) (refl) ▸
       at 5 1 (CS03⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ []) (lem-box-cP-at0210243143 c4) ▸
       at 0 2 (CCZ024 ∷ S4 ∷ []) (sym (wp0617 c4)) ▸
       at 1 2 (Toff213 ∷ S4 ∷ []) (wl0727 (lit c4)) ▸
       at 2 2 (CCZ024 ∷ S4 ∷ []) (sym (wp0617 c4)) ▸
       at 3 2 (Toff213 ∷ S4 ∷ []) (wl0727 (lit c4)) ▸ done

  b1 : Chain (CCZ024 ∷ Toff213 ∷ CCZ024 ∷ Toff213 ∷ S4 ∷ Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ []) (Sb2-0-41-3 ∷ S4 ∷ [])
  b1 = at 0 4 (Bx2-0413 ∷ []) (sym (lem-box-cP-at0210243143 c4)) ▸
       at 1 5 (Toff314 ∷ CS03 ∷ Toff314 ∷ CS03⁻ ∷ S4 ∷ []) (wp0849 c4) ▸
       at 2 1 (Sb2-0-3-1 ∷ []) (refl) ▸
       at 4 1 (Sb⁻2-0-3-1 ∷ []) (refl) ▸
       at 0 5 (Sb2-0-41-3 ∷ []) (refl) ▸ done


-- F2-I-CS1: 13 steps
lem-F2-I-CS1 : Ws → ⟪ (S4 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-1-42-3 ∷ S4 ∷ []) ⟫ʷ
lem-F2-I-CS1 c4 = trans (run b0) (run b1)
  where
  b0 : Chain (S4 ∷ Sb0-1-42-3 ∷ []) (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ [])
  b0 = at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 1 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 0 2 (CCZ014 ∷ S4 ∷ []) (sym (wp0633 c4)) ▸
       at 1 2 (Toff023 ∷ S4 ∷ []) (wp0632 c4) ▸
       at 2 2 (CCZ014 ∷ S4 ∷ []) (sym (wp0633 c4)) ▸
       at 3 2 (Toff023 ∷ S4 ∷ []) (wp0632 c4) ▸ done

  b1 : Chain (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ S4 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (Sb0-1-42-3 ∷ S4 ∷ [])
  b1 = at 0 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 1 5 (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ S4 ∷ []) (wl1050 (lit c4)) ▸
       at 2 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 0 5 (Sb0-1-42-3 ∷ []) (refl) ▸ done

