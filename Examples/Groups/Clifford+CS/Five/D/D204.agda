{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D204 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0166 ; wl0167 ; wl0171 ; wl0181 ; wl0206 ; wl0207 ; wl0208 ; wl0209 ; wl0211 ; wl0321 ; wl0341 ; wl0611 ; wl0852 ; wl0861 ; wl0878 ; wl0879 ; wl0882 ; wl0888 ; wl0889 ; wl0890 ; wl0891 ; wl0892 ; wl0893 ; wl0894 ; wl0895 ; wl0896 ; wl0897 ; wl0898 ; wl0899 ; wl0900 ; wl0901 ; wl0902 ; wl0903 ; wp0011 ; wp0012 ; wp0013 ; wp0052 ; wp0053 ; wp0054 ; wp0055 ; wp0165 ; wp0167 ; wp0202 ; wp0251 ; wp0252 ; wp0295 ; wp0312 ; wp0313 ; wp0314 ; wp0737 ; wp0750 ; wp0751 ; wp0752 ; wp0753 ; wp0754 ; wp0755 ; wl0214 ; wl0256 ; wl0263 ; wl0311 ; wl0348 ; wl0404 ; wl0447 ; wl0503 ; wl0512 ; wl0991 ; wl0992 ; wl0993 ; wl0994 ; wl0995 ; wl0996 ; wl0997 ; wl0998 ; wp0003 ; wp0124 ; wp0161 ; wp0221 ; wp0298 ; wp0796 ; wp0797 ; wp0798 ; wp0799 ; wp0800 ; wp0801 ; wp0802 ; wp0803 ; wp0804 ; wl0220 ; wl0497 ; wl0499 ; wl0500 ; wl0501 ; wl0778 ; wl0779 ; wl0780 ; wl0871 ; wl1190 ; wl1206 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1224 ; wl1225 ; wl1226 ; wl1227 ; wp0001 ; wp0002 ; wp0041 ; wp0106 ; wp0107 ; wp0108 ; wp0120 ; wp0129 ; wp0261 ; wp0700 ; wp0701 ; wp0716 ; wp1003 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1025 ; wp1026 ; wp1027 ; wp1028 ; wp1029 ; wp1030)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0310243142 ; lem-box-cP-at03243240 ; lem-box-cP-at243243 ; lem-box-cP-at3443)
open import Examples.Groups.Clifford+CS.Five.D.D018 using (lem-box-perm-1324-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D019 using (lem-CSdu-box-3-at0310243142 ; lem-CSdu-box-3-at243243 ; lem-CSu-box-3-at0310243142 ; lem-CSu-box-3-at243243 ; lem-CXu-box-4-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box2-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D025 using (lem-box-perm-1342-at0310243142 ; lem-box-perm-1342-at243243 ; lem-box-perm-1423 ; lem-box-perm-1423-at03102132 ; lem-box-perm-2431-at132132 ; lem-box-perm-4132-at243243)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-box-perm-3241-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D037 using (lem-box-box-1-at03102132 ; lem-box-box-3)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-F0-at01143043 ; lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.R001 using (lem-comm-CS12-CCZ034 ; lem-comm-CS23-CCZ014 ; lem-comm-CSd12-CCZ034 ; lem-comm-CSd23-CCZ014 ; lem-comm-CX12-CCZ034 ; lem-comm-CX12-TOFF034 ; lem-comm-CZ12-CCZ034)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ034-CX12 ; lem-comm-CCZ134-CS02 ; lem-comm-CCZ134-CX02 ; lem-comm-CX04-TOFF312 ; lem-comm-TOFF034-CX12 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF302-CX14)

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

-- nf-comm-CSu-CS@0: 282 steps
lem-nf-comm-CSu-CSat0 : Ws → ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ ≈ ⟪ (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) ⟫ʷ
lem-nf-comm-CSu-CSat0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b0 = at 0 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 1 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 0 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 2 1 (CS02 ∷ []) (refl) ▸
       at 4 1 (CS02⁻ ∷ []) (refl) ▸
       at 5 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 7 1 (CS01 ∷ []) (refl) ▸
       at 9 1 (CS01⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b1 = at 5 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 8 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 8 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 7 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 8 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 11 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b2 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b2 = at 12 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 13 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 7 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 8 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 8 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 10 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b3 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b3 = at 10 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 12 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 13 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 6 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 5 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸ done

  b4 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b4 = at 6 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 11 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 5 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 6 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸ done

  b5 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b5 = at 7 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 7 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 10 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 9 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 8 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 7 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 8 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 8 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸ done

  b6 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ [])
  b6 = at 11 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 11 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 10 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 11 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 12 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 14 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 15 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸ done

  b7 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ [])
  b7 = at 16 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 10 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 11 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 9 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 11 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 13 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 12 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 13 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸ done

  b8 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ [])
  b8 = at 14 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 15 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 16 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 12 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 9 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 9 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 8 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 9 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸ done

  b9 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ []) (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ [])
  b9 = at 10 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 12 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 13 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 14 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 8 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 9 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 10 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b10 : Chain (Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ []) (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b10 = at 10 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 13 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 12 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 11 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 10 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 11 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 0 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 3 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸ done

  b11 : Chain (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b11 = at 3 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 2 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 3 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 4 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 6 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 7 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 8 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸ done

  b12 : Chain (CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b12 = at 2 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 3 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 1 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 3 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 5 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 4 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 5 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 6 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸ done

  b13 : Chain (CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (K2 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b13 = at 7 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 8 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 4 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 1 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 1 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 0 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 1 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 2 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b14 : Chain (K2 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b14 = at 3 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 4 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 5 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 6 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 0 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 1 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 2 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 2 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b15 : Chain (Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b15 = at 5 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 4 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 3 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 2 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 3 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 3 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 6 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b16 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b16 = at 5 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 6 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 5 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b17 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff312 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b17 = at 6 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 4 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 6 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 8 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 7 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 8 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 9 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b18 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff312 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b18 = at 11 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 7 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 4 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 4 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 3 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 4 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 5 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b19 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02⁻ ∷ Toff312 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b19 = at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 9 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 3 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 4 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 5 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 8 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸ done

  b20 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS02⁻ ∷ Toff312 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS24 ∷ Toff312 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b20 = at 7 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 6 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 5 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 6 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 6 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 10 1 (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wp1028 c4)) ▸
       at 9 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 10 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸ done

  b21 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS24 ∷ Toff312 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b21 = at 11 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 13 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 14 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 15 2 (K0⁻ ∷ Toff312 ∷ []) (sym (c₁ (K • iI) (Toffᵗ))) ▸
       at 9 7 (Toff024 ∷ []) (wp1028 c4) ▸
       at 8 2 (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1029 c4) ▸
       at 8 1 (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wp1028 c4)) ▸ done

  b22 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff024 ∷ Toff312 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b22 = at 7 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 8 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 9 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 11 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 12 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 13 2 (K0⁻ ∷ Toff312 ∷ []) (sym (c₁ (K • iI) (Toffᵗ))) ▸
       at 7 7 (Toff024 ∷ []) (wp1028 c4) ▸ done

  b23 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff024 ∷ Toff312 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ CCZ234 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b23 = at 8 2 (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) (sym (wl0497 (lit c4))) ▸
       at 6 2 (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1029 c4) ▸
       at 9 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b24 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ CCZ234 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b24 = at 8 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 9 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 7 3 (CCZ124 ∷ []) (sym (wl1227 (lit c4))) ▸
       at 8 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 8 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 11 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 11 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b25 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b25 = at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 10 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 9 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 9 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 8 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b26 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS01 ∷ Toff312 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b26 = at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 12 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 8 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 9 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 9 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 12 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸ done

  b27 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS01 ∷ Toff312 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS24 ∷ Toff312 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b27 = at 11 2 (CS01 ∷ CCZ034 ∷ []) (wp0001 c4) ▸
       at 10 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 9 2 (CS01 ∷ CCZ034 ∷ []) (wp0001 c4) ▸
       at 10 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 10 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 14 1 (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wp1028 c4)) ▸
       at 13 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 14 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸ done

  b28 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K0 ∷ CS24 ∷ Toff312 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b28 = at 15 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 17 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 18 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 19 2 (K0⁻ ∷ Toff312 ∷ []) (sym (c₁ (K • iI) (Toffᵗ))) ▸
       at 13 7 (Toff024 ∷ []) (wp1028 c4) ▸
       at 12 2 (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1029 c4) ▸
       at 12 1 (K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ []) (sym (wp1028 c4)) ▸ done

  b29 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ K0 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ K0⁻ ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff024 ∷ Toff312 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b29 = at 11 2 (K0 ∷ Toff312 ∷ []) (sym (c₁ (K) (Toffᵗ))) ▸
       at 12 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 13 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸
       at 15 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 16 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 17 2 (K0⁻ ∷ Toff312 ∷ []) (sym (c₁ (K • iI) (Toffᵗ))) ▸
       at 11 7 (Toff024 ∷ []) (wp1028 c4) ▸ done

  b30 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ CCZ034 ∷ Toff024 ∷ Toff312 ∷ CCZ234 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ CCZ234 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b30 = at 12 2 (CCZ124 ∷ CCZ234 ∷ Toff312 ∷ []) (sym (wl0497 (lit c4))) ▸
       at 10 2 (Toff024 ∷ CCZ234 ∷ CCZ034 ∷ []) (wp1029 c4) ▸
       at 13 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b31 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ234 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ CCZ234 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b31 = at 12 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 13 2 (CCZ234 ∷ CCZ034 ∷ []) (wp0129 c4) ▸
       at 11 3 (CCZ124 ∷ []) (sym (wl1227 (lit c4))) ▸
       at 12 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 12 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 15 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 15 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 14 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b32 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS01⁻ ∷ Bx3-1420 ∷ [])
  b32 = at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 17 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 18 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 14 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 13 2 (CCZ124 ∷ Toff312 ∷ []) (sym (wl0871 (lit c4))) ▸
       at 13 1 (CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ []) (wl0256 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b33 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS01⁻ ∷ Bx3-1420 ∷ []) (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS01⁻ ∷ Toff312 ∷ Bx3-1420 ∷ [])
  b33 = at 13 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 15 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 16 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 12 5 (CCZ124 ∷ []) (sym (wl0256 (lit c4))) ▸
       at 13 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 13 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 16 2 (CS01⁻ ∷ Toff312 ∷ []) (sym (wl0500 (lit c4))) ▸ done

  b34 : Chain (Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ CS01⁻ ∷ Toff312 ∷ Bx3-1420 ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ [])
  b34 = at 15 2 (CS01⁻ ∷ CCZ034 ∷ []) (wp0120 c4) ▸
       at 14 2 (CS01⁻ ∷ Toff312 ∷ []) (sym (wl0500 (lit c4))) ▸
       at 13 2 (CS01⁻ ∷ CCZ034 ∷ []) (wp0120 c4) ▸
       at 14 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 14 1 (Bx3-1420 ∷ []) (lem-box-perm-3241-at0310243142 c4) ▸
       at 14 2 [] (lem-box2-at03243240 c4) ▸
       at 1 3 (CS02 ∷ Toff214 ∷ CCZ014 ∷ []) (wp1030 c4) ▸
       at 3 2 [] (wp0161 c4) ▸ done

  b35 : Chain (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ124 ∷ CS01⁻ ∷ []) (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ [])
  b35 = at 5 2 [] (wl0263 (lit c4)) ▸
       at 7 2 [] (wl0263 (lit c4)) ▸ done
