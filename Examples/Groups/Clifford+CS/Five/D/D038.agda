{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D038 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0181 ; wl0185 ; wl0190 ; wl0196 ; wl0207 ; wl0232 ; wl0234 ; wl0235 ; wl0241 ; wl0242 ; wl0256 ; wl0263 ; wl0274 ; wl0305 ; wl0469 ; wl0490 ; wl0495 ; wl0807 ; wl0808 ; wl0809 ; wl0832 ; wl0872 ; wl0892 ; wl0942 ; wl0965 ; wl0971 ; wl0972 ; wl0973 ; wl0974 ; wl0975 ; wl0976 ; wl0977 ; wl0978 ; wl0979 ; wl0980 ; wl0981 ; wl0982 ; wl0983 ; wl0984 ; wl0985 ; wl0986 ; wp0020 ; wp0023 ; wp0033 ; wp0034 ; wp0035 ; wp0036 ; wp0037 ; wp0053 ; wp0054 ; wp0062 ; wp0063 ; wp0064 ; wp0081 ; wp0088 ; wp0089 ; wp0091 ; wp0092 ; wp0124 ; wp0161 ; wp0352 ; wp0783 ; wp0784 ; wp0785 ; wp0786 ; wp0787 ; wp0788 ; wp0789 ; wp0790 ; wp0791 ; wp0793 ; wl0206 ; wl0208 ; wl0209 ; wl0211 ; wl0217 ; wl0220 ; wl0221 ; wl0222 ; wl0621 ; wl0735 ; wl0894 ; wl0896 ; wl0900 ; wl0907 ; wl0910 ; wl1010 ; wl1011 ; wl1012 ; wl1013 ; wl1014 ; wl1015 ; wl1016 ; wl1017 ; wp0052 ; wp0055 ; wp0067 ; wp0265 ; wp0513 ; wp0546 ; wp0669 ; wp0725 ; wp0814 ; wp0815 ; wp0816 ; wp0817 ; wp0818 ; wp0819 ; wp0820 ; wp0821 ; wp0822 ; wp0823 ; wp0824 ; wl1031 ; wl1032 ; wl1033 ; wl1034 ; wl1035 ; wp0278 ; wp0835 ; wp0836 ; wp0837 ; wp0838 ; wp0839 ; wp0840 ; wp0841 ; wl1068 ; wl1112 ; wp0870 ; wp0871 ; wp0872 ; wp0873 ; wp0874 ; wp0875 ; wp0878 ; wp0879)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D002 using (lem-nf-order-CSat0 ; lem-nf-order-CSat1 ; lem-nf-order-CSat2)
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0210243143 ; lem-box-cP-at12233441 ; lem-box-cP-at122441 ; lem-box-cP-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box-perm-1324-at122441 ; lem-box2)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-CSdu-box-3-at0210243143 ; lem-CSdu-box-3-at122441 ; lem-CSu-box-3-at0210243143 ; lem-CSu-box-3-at122441 ; lem-box-perm-1432-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-CKu-box-2-at0210243143 ; lem-CKu-box-2-at122441 ; lem-CKu-box-2-at243243 ; lem-box-box-1-at021021 ; lem-box-perm-1342-at0210243143 ; lem-box-perm-1423-at021021 ; lem-box-perm-1432-at1221 ; lem-box-perm-3241-at243243 ; lem-box-perm-4213-at122441)
open import Examples.Groups.Clifford+CS.Five.D.D026 using (lem-CKc-box ; lem-CKdc-box ; lem-S2-SBOX⟨0·1·42·3⟩ ; lem-S2-SBOX⟨0·2·43·1⟩ ; lem-S2-SBOX⟨2·0·41·3⟩)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS13-CCZ024 ; lem-comm-CS23-CCZ014 ; lem-comm-CS24-TOFF013 ; lem-comm-CSd13-CCZ024 ; lem-comm-CSd23-CCZ014 ; lem-comm-CSd24-TOFF013 ; lem-comm-CX13-CCZ024 ; lem-comm-CX14-CCZ023 ; lem-comm-CX14-TOFF023 ; lem-comm-CX23-CCZ014 ; lem-comm-CZ13-CCZ024)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ024-CS13 ; lem-comm-CCZ024-CSd13 ; lem-comm-CCZ024-CX13 ; lem-comm-CCZ024-CX31 ; lem-comm-CCZ124-CS03 ; lem-comm-CX23-TOFF014 ; lem-comm-TOFF014-CX23 ; lem-comm-TOFF213-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF023-CX14)

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

-- F4-CS1-CS2: 248 steps
lem-F4-CS1-CS2 : Ws → ⟪ (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ []) ⟫ʷ
lem-F4-CS1-CS2 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (run b30))))))))))))))))))))))))))))))
  where
  b0 : Chain (X4 ∷ Sb0-1-42-3 ∷ X4 ∷ Sb0-2-43-1 ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 3 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 5 1 (CS12 ∷ []) (refl) ▸
       at 7 1 (CS12⁻ ∷ []) (refl) ▸
       at 3 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 4 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 6 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b1 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 10 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 9 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 8 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 7 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 5 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 4 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b2 : Chain (X4 ∷ Sb0-1-42-3 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ024 ∷ CS13⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 5 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 5 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 2 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 1 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 5 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 5 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸ done

  b3 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ CCZ024 ∷ CS13⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 6 2 (Toff013 ∷ CS13⁻ ∷ []) (wl0907 (lit c4)) ▸
       at 7 2 (CCZ024 ∷ CS13⁻ ∷ []) (lem-comm-CSd13-CCZ024 (lit c4)) ▸
       at 8 2 (Toff013 ∷ CS13⁻ ∷ []) (wl0907 (lit c4)) ▸
       at 5 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 5 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 5 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸
       at 4 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 6 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0815 c4) ▸ done

  b4 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff324 ∷ Toff014 ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 11 2 (Toff014 ∷ K3⁻ ∷ []) (wp0816 c4) ▸
       at 10 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS34⁻ ∷ []) (wp0818 c4) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 6 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 5 2 (Toff014 ∷ K3 ∷ []) (wp0819 c4) ▸ done

  b5 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ CCZ124 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b5 = at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 11 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 10 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 9 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 8 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b6 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CCZ023 ∷ CCZ124 ∷ Toff014 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b6 = at 7 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 6 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 7 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 8 2 (Toff014 ∷ CCZ124 ∷ []) (wp0822 c4) ▸
       at 7 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 13 2 (Toff014 ∷ K3⁻ ∷ []) (wp0816 c4) ▸
       at 12 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 11 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸ done

  b7 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ Toff014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b7 = at 10 2 (Toff014 ∷ CS34⁻ ∷ []) (wp0818 c4) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 7 2 (Toff014 ∷ K3 ∷ []) (wp0819 c4) ▸
       at 8 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸
       at 4 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 3 1 (CS13 ∷ []) (refl) ▸ done

  b8 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Bx0-2431 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b8 = at 4 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 3 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CS13 ∷ []) (wl0910 (lit c4)) ▸
       at 5 2 (CCZ024 ∷ CS13 ∷ []) (lem-comm-CS13-CCZ024 (lit c4)) ▸
       at 6 2 (Toff013 ∷ CS13 ∷ []) (wl0910 (lit c4)) ▸
       at 3 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (Bx0-2341 ∷ []) (lem-box-perm-1324-at122441 c4) ▸
       at 3 1 (CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ []) (lem-box-cP-at12233441 c4) ▸ done

  b9 : Chain (X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ Toff014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b9 = at 2 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 4 2 (Toff014 ∷ CCZ024 ∷ CCZ124 ∷ []) (wp0815 c4) ▸
       at 3 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 9 2 (Toff014 ∷ K3⁻ ∷ []) (wp0816 c4) ▸
       at 8 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 6 2 (Toff014 ∷ CS34⁻ ∷ []) (wp0818 c4) ▸
       at 5 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸ done

  b10 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ Toff014 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ CCZ024 ∷ CCZ124 ∷ CCZ023 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CS24 ∷ CCZ023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b10 = at 4 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 3 2 (Toff014 ∷ K3 ∷ []) (wp0819 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 10 2 (CCZ023 ∷ CS12 ∷ []) (sym (wl0621 (lit c4))) ▸
       at 9 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸
       at 8 2 (CCZ023 ∷ CS24⁻ ∷ []) (sym (wp0820 c4)) ▸
       at 7 2 (CCZ023 ∷ CX14 ∷ []) (lem-comm-CX14-CCZ023 (lit c4)) ▸ done

  b11 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ Toff324 ∷ CCZ024 ∷ CS24 ∷ CCZ023 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff014 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b11 = at 6 2 (CCZ023 ∷ CS24 ∷ []) (sym (wp0513 c4)) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 5 2 (CCZ023 ∷ CCZ024 ∷ []) (sym (wp0669 c4)) ▸
       at 4 2 (CCZ023 ∷ Toff324 ∷ CCZ024 ∷ []) (sym (wp0814 c4)) ▸
       at 5 3 (Toff324 ∷ []) (wp0821 c4) ▸
       at 6 2 (Toff014 ∷ CCZ124 ∷ []) (wp0822 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 11 2 (Toff014 ∷ K3⁻ ∷ []) (wp0816 c4) ▸ done

  b12 : Chain (X4 ∷ Bx0-1423 ∷ CCZ023 ∷ Toff014 ∷ CCZ023 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ Toff014 ∷ K3⁻ ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (X4 ∷ Bx0-1423 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b12 = at 10 2 (Toff014 ∷ CS24 ∷ []) (wp0817 c4) ▸
       at 9 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 8 2 (Toff014 ∷ CS34⁻ ∷ []) (wp0818 c4) ▸
       at 7 2 (Toff014 ∷ CX23 ∷ []) (lem-comm-CX23-TOFF014 (lit c4)) ▸
       at 6 2 (Toff014 ∷ CS34 ∷ []) (wp0546 c4) ▸
       at 5 2 (Toff014 ∷ K3 ∷ []) (wp0819 c4) ▸
       at 6 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 4 (Bx0-2341 ∷ []) (sym (lem-box-cP-at12233441 c4)) ▸ done

  b13 : Chain (X4 ∷ Bx0-1423 ∷ Bx0-2341 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b13 = at 2 1 (Bx0-2431 ∷ []) (sym (lem-box-perm-1324-at122441 c4)) ▸
       at 1 1 (Bx0-2431 ∷ []) (lem-box-perm-3241-at243243 c4) ▸
       at 2 1 (Bx0-1423 ∷ []) (lem-box-perm-4213-at122441 c4) ▸
       at 1 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 0 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸
       at 2 2 (Toff013 ∷ CZ02 ∷ CCZ123 ∷ []) (wl0232 (lit c4)) ▸
       at 1 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 4 1 (CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ []) (wl0242 (lit c4)) ▸ done

  b14 : Chain (CCZ024 ∷ Toff013 ∷ X4 ∷ CZ02 ∷ CS23 ∷ CX13 ∷ CS23⁻ ∷ CX13 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b14 = at 8 2 (CCZ024 ∷ CS12 ∷ []) (sym (wp0081 c4)) ▸
       at 7 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 6 2 (CCZ024 ∷ CS23⁻ ∷ []) (sym (wp0091 c4)) ▸
       at 5 2 (CCZ024 ∷ CX13 ∷ []) (lem-comm-CX13-CCZ024 (lit c4)) ▸
       at 4 2 (CCZ024 ∷ CS23 ∷ []) (sym (wp0092 c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0242 (lit c4))) ▸
       at 3 2 (CCZ024 ∷ CZ02 ∷ []) (sym (wp0023 c4)) ▸
       at 2 2 (CCZ024 ∷ X4 ∷ CZ02 ∷ []) (sym (wp0020 c4)) ▸ done

  b15 : Chain (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ X4 ∷ CZ02 ∷ CZ02 ∷ CCZ123 ∷ Toff013 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b15 = at 3 3 (X4 ∷ []) (wl0185 (lit c4)) ▸
       at 4 2 (Toff013 ∷ CCZ123 ∷ []) (wl0234 (lit c4)) ▸
       at 3 2 (Toff013 ∷ X4 ∷ []) (sym (c₄ (Swap ↑ ↑ • Toff • Swap ↑ ↑) (X))) ▸
       at 0 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 2 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b16 : Chain (Bx0-2431 ∷ X4 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b16 = at 4 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 3 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 2 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 3 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 3 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 4 1 (CS23 ∷ CX12 ∷ CS23⁻ ∷ CX12 ∷ CS13 ∷ []) (wl0207 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CS13 ∷ []) (sym (wp0053 c4)) ▸
       at 7 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸ done

  b17 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CS23 ∷ CX12 ∷ CS23⁻ ∷ CCZ014 ∷ CX12 ∷ CS13 ∷ Toff023 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b17 = at 6 2 (CCZ014 ∷ CS23⁻ ∷ []) (lem-comm-CSd23-CCZ014 (lit c4)) ▸
       at 5 2 (CCZ014 ∷ CX12 ∷ []) (sym (wp0054 c4)) ▸
       at 4 2 (CCZ014 ∷ CS23 ∷ []) (lem-comm-CS23-CCZ014 (lit c4)) ▸
       at 5 5 (CCZ123 ∷ []) (sym (wl0207 (lit c4))) ▸
       at 5 2 (Toff023 ∷ CCZ123 ∷ []) (wl0209 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 8 (Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ CCZ123 ∷ []) (wl1010 (lit c4)) ▸
       at 10 2 [] (wl0181 (lit c4)) ▸ done

  b18 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CCZ124 ∷ CS13 ∷ Toff324 ∷ CCZ124 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b18 = at 4 3 (CS13 ∷ Toff324 ∷ CCZ124 ∷ []) (wl1011 (lit c4)) ▸
       at 6 2 [] (wl0263 (lit c4)) ▸
       at 4 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0975 (lit c4))) ▸
       at 2 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 1 (CS13 ∷ []) (refl) ▸ done

  b19 : Chain (Bx0-2431 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b19 = at 6 1 (CS13⁻ ∷ []) (refl) ▸
       at 3 6 (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1012 (lit c4))) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CX31 ∷ Toff023 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸
       at 6 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 7 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b20 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b20 = at 9 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 6 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸
       at 4 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp0824 c4) ▸
       at 3 2 (CX31 ∷ Toff023 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 5 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸ done

  b21 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b21 = at 4 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 5 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 10 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 4 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸ done

  b22 : Chain (Bx0-2431 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b22 = at 2 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp0824 c4) ▸
       at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 1 3 (Toff134 ∷ X4 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 4 2 (CS12 ∷ X4 ∷ []) (sym (wl0980 (lit c4))) ▸
       at 3 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b23 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12 ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b23 = at 5 1 (CS13 ∷ []) (refl) ▸
       at 7 1 (CS13⁻ ∷ []) (refl) ▸
       at 4 5 (CS12 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1015 (lit c4))) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 5 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 4 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 3 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸ done

  b24 : Chain (Bx0-2431 ∷ Toff134 ∷ X4 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ [])
  b24 = at 4 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 8 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 4 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 2 2 (CS12 ∷ X4 ∷ []) (sym (wl0980 (lit c4))) ▸
       at 5 2 (CX31 ∷ Toff134 ∷ X4 ∷ []) (sym (wl0975 (lit c4))) ▸
       at 4 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 1 (CS13 ∷ []) (refl) ▸ done

  b25 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CX31 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b25 = at 8 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 6 (CX31 ∷ Toff134 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1012 (lit c4))) ▸
       at 4 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 7 2 (CX31 ∷ Toff023 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸
       at 8 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 9 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸ done

  b26 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ CX31 ∷ K1 ∷ CS34 ∷ CX14 ∷ Toff023 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b26 = at 11 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 14 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 8 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸
       at 6 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp0824 c4) ▸
       at 5 2 (CX31 ∷ Toff023 ∷ []) (sym (wl0832 (lit c4))) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸ done

  b27 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ [])
  b27 = at 6 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 7 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 12 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 6 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸ done

  b28 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ X4 ∷ CCZ014 ∷ CX31 ∷ Toff134 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ CS12⁻ ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12⁻ ∷ X4 ∷ [])
  b28 = at 4 3 (CX31 ∷ Toff134 ∷ CCZ014 ∷ []) (wp0824 c4) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 3 3 (Toff134 ∷ X4 ∷ []) (sym (wl0235 (lit c4))) ▸
       at 6 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0984 (lit c4))) ▸
       at 5 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸ done

  b29 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ CS12⁻ ∷ X4 ∷ []) (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ [])
  b29 = at 7 1 (CS13 ∷ []) (refl) ▸
       at 9 1 (CS13⁻ ∷ []) (refl) ▸
       at 6 5 (CS12⁻ ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ []) (sym (wl1016 (lit c4))) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS12⁻ ∷ Toff023 ∷ []) (sym (wl1017 (lit c4))) ▸
       at 7 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸
       at 6 2 (CS12⁻ ∷ Toff023 ∷ []) (sym (wl1017 (lit c4))) ▸
       at 5 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸ done

  b30 : Chain (Bx0-2431 ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ X4 ∷ CS12⁻ ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ X4 ∷ []) (Sb0-2-43-1 ∷ X4 ∷ Sb0-1-42-3 ∷ X4 ∷ [])
  b30 = at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 8 1 (Sb0-1-3-2 ∷ []) (refl) ▸
       at 10 1 (Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 6 5 (Sb0-1-42-3 ∷ []) (refl) ▸
       at 4 2 (CS12⁻ ∷ X4 ∷ []) (sym (wl0984 (lit c4))) ▸
       at 2 1 (Sb0-2-1-3 ∷ []) (refl) ▸
       at 4 1 (Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 0 5 (Sb0-2-43-1 ∷ []) (refl) ▸ done

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

-- CKc-boxL: 3 steps
lem-CKc-boxL : Ws → ⟪ (CK34 ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ CK34 ∷ CCZ124 ∷ []) ⟫ʷ
lem-CKc-boxL c4 = run b0
  where
  b0 : Chain (CK34 ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ CK34 ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Bx0-1234 ∷ Bx0-1234 ∷ []) (sym (lem-box2 c4)) ▸
       at 1 2 (CCZ124 ∷ CK34 ∷ CCZ124 ∷ Bx0-1234 ∷ []) (lem-CKc-box c4) ▸
       at 4 2 [] (lem-box2 c4) ▸ done

-- CKdc-boxL: 3 steps
lem-CKdc-boxL : Ws → ⟪ (CK34⁻ ∷ Bx0-1234 ∷ []) ⟫ʷ ≈ ⟪ (Bx0-1234 ∷ CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ []) ⟫ʷ
lem-CKdc-boxL c4 = run b0
  where
  b0 : Chain (CK34⁻ ∷ Bx0-1234 ∷ []) (Bx0-1234 ∷ CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ [])
  b0 = at 0 0 (Bx0-1234 ∷ Bx0-1234 ∷ []) (sym (lem-box2 c4)) ▸
       at 1 2 (CCZ124 ∷ CK34⁻ ∷ CCZ124 ∷ Bx0-1234 ∷ []) (lem-CKdc-box c4) ▸
       at 4 2 [] (lem-box2 c4) ▸ done

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

-- F1-order-CS@2: 5 steps
lem-F1-order-CSat2 : Ws → ⟪ (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ [] ⟫ʷ
lem-F1-order-CSat2 c4 = run b0
  where
  b0 : Chain (Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ Sb0-2-43-1 ∷ []) []
  b0 = at 0 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 1 2 (CCZ234 ∷ []) (lem-S2-SBOX⟨0·2·43·1⟩ c4) ▸
       at 0 2 [] (wl0305 (lit c4)) ▸
       at 0 0 [] (wl1112 (lit c4)) ▸
       at 0 0 [] (sym (lem-nf-order-CSat2 c4)) ▸ done
