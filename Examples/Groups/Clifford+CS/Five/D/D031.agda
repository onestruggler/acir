{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D031 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0220 ; wl0499 ; wl0501 ; wl0618 ; wl0758 ; wl0763 ; wl0764 ; wl0765 ; wl0778 ; wl0779 ; wl0780 ; wl0801 ; wl0852 ; wl0861 ; wl0878 ; wl0879 ; wl0888 ; wl0960 ; wl1190 ; wl1206 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1224 ; wl1225 ; wl1226 ; wl1233 ; wl1252 ; wl1309 ; wl1310 ; wl1311 ; wl1312 ; wl1313 ; wl1314 ; wp0002 ; wp0003 ; wp0013 ; wp0041 ; wp0103 ; wp0106 ; wp0107 ; wp0108 ; wp0109 ; wp0124 ; wp0261 ; wp0272 ; wp0295 ; wp0296 ; wp0301 ; wp0691 ; wp0700 ; wp0701 ; wp0716 ; wp1003 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1025 ; wp1026 ; wp1027 ; wp1035 ; wp1036 ; wp1037 ; wp1038 ; wp1039 ; wp1040 ; wp1041 ; wp1130 ; wp1131 ; wp1132 ; wp1133 ; wp1134 ; wp1135 ; wp1136 ; wp1137)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D005 using (lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D009 using (lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D020 using (lem-F0-at01143043 ; lem-box-cP-at03243240 ; lem-box-cP-at033440 ; lem-box-perm-1324-at03243240)
open import Examples.Groups.Clifford+CS.Five.D.D022 using (lem-S2-SBOX⟨3·1·42·0⟩)
open import Examples.Groups.Clifford+CS.Five.D.D030 using (lem-L-CX01-0 ; lem-L-CX01-1 ; lem-L-CX10-1)
open import Examples.Groups.Clifford+CS.Five.D.R004 using (lem-comm-CCZ134-CS02 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R005 using (lem-comm-CCZ034-CX12 ; lem-comm-CCZ123-CX04 ; lem-comm-CCZ134-CX02 ; lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14 ; lem-comm-TOFF304-CX12)
-- L-CCZ-0 part0: 500 steps
lem-L-CCZ-0-part0 : Ws → ⟪ (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) ⟫ʷ
lem-L-CCZ-0-part0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (trans (run b35) (trans (run b36) (trans (run b37) (trans (run b38) (trans (run b39) (trans (run b40) (trans (run b41) (trans (run b42) (trans (run b43) (trans (run b44) (trans (run b45) (trans (run b46) (trans (run b47) (trans (run b48) (trans (run b49) (trans (run b50) (trans (run b51) (trans (run b52) (trans (run b53) (trans (run b54) (trans (run b55) (trans (run b56) (trans (run b57) (trans (run b58) (trans (run b59) (trans (run b60) (trans (run b61) (run b62))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ Sb2-0-41-3 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (Sb0-1-42-3 ∷ Toff104 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b0 = at 1 5 (Toff104 ∷ []) (lem-L-CX01-0 c4) ▸
       at 5 5 (Toff104 ∷ []) (lem-L-CX01-0 c4) ▸
       at 6 5 (Toff214 ∷ []) (lem-L-CX01-1 c4) ▸
       at 7 5 (Toff124 ∷ []) (lem-L-CX10-1 c4) ▸
       at 8 5 (Toff214 ∷ []) (lem-L-CX01-1 c4) ▸
       at 10 5 (Toff214 ∷ []) (lem-L-CX01-1 c4) ▸
       at 11 5 (Toff124 ∷ []) (lem-L-CX10-1 c4) ▸
       at 12 5 (Toff214 ∷ []) (lem-L-CX01-1 c4) ▸ done

  b1 : Chain (Sb0-1-42-3 ∷ Toff104 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb2-0-41-3 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ Toff104 ∷ CCZ124 ∷ Sb3-1-42-0 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb3-0-41-2 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b1 = at 0 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 2 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 3 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 4 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 9 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 2 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸ done

  b2 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ Toff104 ∷ CCZ124 ∷ Sb3-1-42-0 ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Sb3-0-41-2 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b2 = at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 7 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 9 1 (CS01 ∷ []) (refl) ▸
       at 11 1 (CS01⁻ ∷ []) (refl) ▸
       at 16 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 18 1 (CS02 ∷ []) (refl) ▸
       at 20 1 (CS02⁻ ∷ []) (refl) ▸
       at 16 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b3 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b3 = at 19 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 19 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 18 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 19 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 20 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 21 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 22 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 23 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b4 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b4 = at 24 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 18 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 19 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 17 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 19 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 21 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 20 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 21 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b5 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ K2 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b5 = at 22 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 23 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 24 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 20 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 17 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 17 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 16 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 17 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b6 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ K2 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b6 = at 18 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 19 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 20 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 21 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 22 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 16 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 17 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 18 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b7 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b7 = at 18 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 21 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 20 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 19 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 18 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 19 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 19 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 22 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸ done

  b8 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b8 = at 22 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 21 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 22 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 23 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 24 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 25 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 26 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 27 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸ done

  b9 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b9 = at 21 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 22 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 20 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 22 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 24 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 23 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 24 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 25 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸ done

  b10 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ Toff312 ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b10 = at 26 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 27 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 23 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 20 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 20 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 19 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 20 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 21 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b11 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ [])
  b11 = at 22 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 23 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 24 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 25 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 19 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 20 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 21 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 21 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b12 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ Toff124 ∷ Toff214 ∷ [])
  b12 = at 24 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 23 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 22 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 21 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 22 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 22 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 25 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 25 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸ done

  b13 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ Toff124 ∷ Toff214 ∷ [])
  b13 = at 24 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 25 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 26 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 27 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 28 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 29 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 30 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 24 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸ done

  b14 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CCZ034 ∷ Toff314 ∷ Toff312 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff312 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ Toff124 ∷ Toff214 ∷ [])
  b14 = at 25 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 23 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 25 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 27 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 26 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 27 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 28 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 29 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b15 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ Toff312 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff124 ∷ Toff214 ∷ [])
  b15 = at 30 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 26 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 23 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 23 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 22 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 23 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 24 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 25 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸ done

  b16 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CCZ034 ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff124 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff124 ∷ Toff324 ∷ Toff312 ∷ Toff214 ∷ [])
  b16 = at 26 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 27 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 28 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 22 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 23 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 24 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 24 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 27 2 (Toff124 ∷ Toff324 ∷ Toff312 ∷ []) (sym (wl1309 (lit c4))) ▸ done

  b17 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff124 ∷ Toff324 ∷ Toff312 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ Toff214 ∷ [])
  b17 = at 27 1 (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl1310 (lit c4))) ▸
       at 26 2 (K1 ∷ CCZ034 ∷ []) (wp1130 c4) ▸
       at 27 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 28 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 29 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 30 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 31 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 32 2 (K1⁻ ∷ CCZ034 ∷ []) (wp1131 c4) ▸ done

  b18 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ CCZ034 ∷ Toff324 ∷ Toff312 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff124 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Toff312 ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ [])
  b18 = at 26 7 (Toff124 ∷ []) (wl1310 (lit c4)) ▸
       at 27 2 (Toff324 ∷ CCZ024 ∷ CCZ034 ∷ []) (wp0295 c4) ▸
       at 25 2 (Toff124 ∷ Toff324 ∷ Toff312 ∷ []) (sym (wl1309 (lit c4))) ▸
       at 27 2 (Toff324 ∷ Toff312 ∷ []) (wl0852 (lit c4)) ▸
       at 29 1 (CS24 ∷ CX04 ∷ CS24⁻ ∷ CX04 ∷ CS02 ∷ []) (wp0013 c4) ▸
       at 28 2 (CS24 ∷ Toff312 ∷ []) (sym (wl0879 (lit c4))) ▸
       at 29 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 30 2 (CS24⁻ ∷ Toff312 ∷ []) (sym (wl0878 (lit c4))) ▸ done

  b19 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff124 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX04 ∷ CS24⁻ ∷ Toff312 ∷ CX04 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ K1 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ [])
  b19 = at 31 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 32 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 28 5 (CCZ024 ∷ []) (sym (wp0013 c4)) ▸
       at 25 3 (Toff124 ∷ []) (wl1311 (lit c4)) ▸
       at 25 1 (K1 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl1310 (lit c4))) ▸
       at 24 2 (K1 ∷ CCZ034 ∷ []) (wp1130 c4) ▸
       at 25 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 26 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b20 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ K1 ∷ CS24 ∷ CX12 ∷ CCZ034 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ [])
  b20 = at 27 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 28 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 29 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 30 2 (K1⁻ ∷ CCZ034 ∷ []) (wp1131 c4) ▸
       at 24 7 (Toff124 ∷ []) (wl1310 (lit c4)) ▸
       at 25 2 (CCZ024 ∷ CCZ034 ∷ []) (sym (wp0109 c4)) ▸
       at 26 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 26 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b21 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ [])
  b21 = at 29 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 29 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 28 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 29 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 30 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 31 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 32 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 33 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b22 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ [])
  b22 = at 34 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 28 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 29 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 27 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 29 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 31 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 30 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 31 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b23 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ K2 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ [])
  b23 = at 32 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 33 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 34 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 30 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 27 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 27 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 26 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 27 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b24 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ K2 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b24 = at 28 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 29 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 30 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 31 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 32 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 26 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 27 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 28 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b25 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b25 = at 7 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 10 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 10 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 9 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 10 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 11 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 13 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b26 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b26 = at 14 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 15 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 9 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 10 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 8 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 10 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 12 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 11 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b27 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b27 = at 12 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 14 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 15 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 11 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 8 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 8 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 7 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸ done

  b28 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b28 = at 8 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 11 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 12 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 13 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 7 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 8 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸ done

  b29 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b29 = at 9 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 9 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 12 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 11 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 10 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 9 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 10 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 10 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸ done

  b30 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b30 = at 13 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 13 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 12 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 13 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 14 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 15 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 16 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 17 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸ done

  b31 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ134 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b31 = at 18 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 12 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 13 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 11 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 13 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 15 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 14 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 15 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸ done

  b32 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ Toff302 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b32 = at 16 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 17 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 18 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 14 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 11 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 11 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 10 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 11 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸ done

  b33 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b33 = at 12 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 14 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 15 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 16 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 10 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 11 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 12 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b34 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ Bx3-1420 ∷ CS01⁻ ∷ Toff104 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b34 = at 12 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 15 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 14 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 13 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 12 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 13 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 13 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 17 1 (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1⁻ ∷ []) (sym (wp1132 c4)) ▸ done

  b35 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1⁻ ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff104 ∷ Toff302 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b35 = at 16 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 17 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 18 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 19 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 20 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 21 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 22 2 (K1⁻ ∷ Toff302 ∷ []) (sym (wl1312 (lit c4))) ▸
       at 16 7 (Toff104 ∷ []) (wp1132 c4) ▸ done

  b36 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff104 ∷ Toff302 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff302 ∷ K1⁻ ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b36 = at 15 2 (Toff104 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp1133 c4) ▸
       at 15 1 (K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ K1⁻ ∷ []) (sym (wp1132 c4)) ▸
       at 14 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 15 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 16 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 17 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 18 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 19 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸ done

  b37 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ134 ∷ K1 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ Toff302 ∷ K1⁻ ∷ CCZ034 ∷ CCZ134 ∷ Toff302 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ034 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b37 = at 20 2 (K1⁻ ∷ Toff302 ∷ []) (sym (wl1312 (lit c4))) ▸
       at 14 7 (Toff104 ∷ []) (wp1132 c4) ▸
       at 15 2 (CCZ024 ∷ CCZ034 ∷ Toff302 ∷ []) (sym (wp1134 c4)) ▸
       at 13 2 (Toff104 ∷ CCZ034 ∷ CCZ134 ∷ []) (wp1133 c4) ▸
       at 16 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 15 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 16 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 17 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸ done

  b38 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ034 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ CCZ034 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b38 = at 18 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 19 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 15 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 16 2 (CCZ034 ∷ CCZ134 ∷ []) (sym (wp0103 c4)) ▸
       at 14 3 (CCZ024 ∷ []) (sym (wp1135 c4)) ▸
       at 15 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 15 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸
       at 15 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸ done

  b39 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff304 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b39 = at 19 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 18 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 19 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 20 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 21 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 22 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 23 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 24 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸ done

  b40 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff304 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff304 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b40 = at 18 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 17 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 17 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 16 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 17 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 18 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 19 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 20 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸ done

  b41 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff304 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b41 = at 21 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 22 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸
       at 16 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 17 2 (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (sym (wp1039 c4)) ▸
       at 15 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 18 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 17 2 (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4)) ▸
       at 18 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸ done

  b42 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-1420 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b42 = at 19 2 (CS14⁻ ∷ CCZ123 ∷ []) (wl0764 (lit c4)) ▸
       at 20 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸
       at 21 2 (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4)) ▸
       at 17 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 18 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 16 3 (CCZ014 ∷ []) (sym (wp1040 c4)) ▸
       at 17 4 (Bx3-1240 ∷ []) (sym (lem-box-cP-at033440 c4)) ▸
       at 17 1 (Bx3-1420 ∷ []) (sym (lem-box-perm-1324-at03243240 c4)) ▸ done

  b43 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-1420 ∷ Toff124 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ K1⁻ ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b43 = at 17 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 21 1 (K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ []) (sym (wl1313 (lit c4))) ▸
       at 20 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 21 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 22 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 23 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 24 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 25 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸ done

  b44 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ Toff302 ∷ K1⁻ ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff302 ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ CCZ234 ∷ CCZ134 ∷ Toff302 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b44 = at 26 2 (K1⁻ ∷ Toff302 ∷ []) (sym (wl1312 (lit c4))) ▸
       at 20 7 (Toff124 ∷ []) (wl1313 (lit c4)) ▸
       at 19 2 (Toff124 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl1314 (lit c4)) ▸
       at 19 1 (K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ []) (sym (wl1313 (lit c4))) ▸
       at 18 2 (K1 ∷ Toff302 ∷ []) (sym (wl1252 (lit c4))) ▸
       at 19 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 20 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 21 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸ done

  b45 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ K1 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff302 ∷ CX14 ∷ CS12 ∷ K1⁻ ∷ CCZ234 ∷ CCZ134 ∷ Toff302 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ234 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ234 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b45 = at 22 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 23 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 24 2 (K1⁻ ∷ Toff302 ∷ []) (sym (wl1312 (lit c4))) ▸
       at 18 7 (Toff124 ∷ []) (wl1313 (lit c4)) ▸
       at 19 2 (CCZ024 ∷ CCZ234 ∷ Toff302 ∷ []) (sym (wp1136 c4)) ▸
       at 17 2 (Toff124 ∷ CCZ234 ∷ CCZ134 ∷ []) (wl1314 (lit c4)) ▸
       at 20 1 (CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ []) (wp0296 c4) ▸
       at 19 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸ done

  b46 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ234 ∷ CS24 ∷ CCZ134 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ CCZ234 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Bx3-1420 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b46 = at 20 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 21 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 22 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 23 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 19 5 (CCZ024 ∷ []) (sym (wp0296 c4)) ▸
       at 20 2 (CCZ234 ∷ CCZ134 ∷ []) (wl0960 (lit c4)) ▸
       at 18 3 (CCZ024 ∷ []) (sym (wp1137 c4)) ▸
       at 19 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b47 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Bx3-1420 ∷ Toff214 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff304 ∷ CS14 ∷ K2⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b47 = at 19 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸
       at 19 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸
       at 23 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 22 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 23 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 24 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 25 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 26 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸ done

  b48 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff304 ∷ CS14 ∷ K2⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ Toff304 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b48 = at 27 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 28 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸
       at 22 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 21 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 21 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 20 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 21 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 22 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸ done

  b49 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ Toff304 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CCZ123 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b49 = at 23 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 24 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 25 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 26 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸
       at 20 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 21 2 (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (sym (wp1039 c4)) ▸
       at 19 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 22 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸ done

  b50 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ134 ∷ CCZ123 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b50 = at 21 2 (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4)) ▸
       at 22 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸
       at 23 2 (CS14⁻ ∷ CCZ123 ∷ []) (wl0764 (lit c4)) ▸
       at 24 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸
       at 25 2 (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4)) ▸
       at 21 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 22 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 20 3 (CCZ014 ∷ []) (sym (wp1040 c4)) ▸ done

  b51 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ Toff304 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b51 = at 21 4 (Bx3-1240 ∷ []) (sym (lem-box-cP-at033440 c4)) ▸
       at 21 1 (Bx3-1420 ∷ []) (sym (lem-box-perm-1324-at03243240 c4)) ▸
       at 21 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸
       at 21 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸
       at 25 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 24 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 25 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 26 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸ done

  b52 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ Toff304 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ K2 ∷ Toff304 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b52 = at 27 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 28 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 29 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 30 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸
       at 24 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 23 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 23 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 22 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸ done

  b53 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ K2 ∷ Toff304 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b53 = at 23 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 24 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 25 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 26 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 27 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 28 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸
       at 22 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 23 2 (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (sym (wp1039 c4)) ▸ done

  b54 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ134 ∷ CCZ014 ∷ CCZ123 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b54 = at 21 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 24 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 23 2 (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4)) ▸
       at 24 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸
       at 25 2 (CS14⁻ ∷ CCZ123 ∷ []) (wl0764 (lit c4)) ▸
       at 26 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸
       at 27 2 (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4)) ▸
       at 23 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸ done

  b55 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ134 ∷ CCZ014 ∷ CCZ123 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b55 = at 24 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 22 3 (CCZ014 ∷ []) (sym (wp1040 c4)) ▸
       at 23 4 (Bx3-1240 ∷ []) (sym (lem-box-cP-at033440 c4)) ▸
       at 23 1 (Bx3-1420 ∷ []) (sym (lem-box-perm-1324-at03243240 c4)) ▸
       at 23 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 27 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 26 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 27 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸ done

  b56 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b56 = at 28 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 29 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 30 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 26 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 25 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 25 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 24 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 25 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸ done

  b57 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ Toff302 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS02 ∷ Toff302 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b57 = at 26 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 27 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 28 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 24 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 23 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 24 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 24 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 27 2 (CS02 ∷ Toff302 ∷ []) (sym (wl0801 (lit c4))) ▸ done

  b58 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS02 ∷ Toff302 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ Toff304 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b58 = at 26 2 (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4)) ▸
       at 25 2 (CS02 ∷ Toff302 ∷ []) (sym (wl0801 (lit c4))) ▸
       at 24 2 (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4)) ▸
       at 25 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 25 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸
       at 25 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸
       at 29 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 28 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸ done

  b59 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ Toff304 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b59 = at 29 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 30 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 31 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 32 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 33 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 34 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸
       at 28 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 27 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸ done

  b60 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff304 ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b60 = at 27 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 26 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 27 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 28 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 29 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 30 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 31 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 32 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸ done

  b61 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff304 ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CCZ123 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b61 = at 26 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 27 2 (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (sym (wp1039 c4)) ▸
       at 25 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 28 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 27 2 (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4)) ▸
       at 28 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸
       at 29 2 (CS14⁻ ∷ CCZ123 ∷ []) (wl0764 (lit c4)) ▸
       at 30 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸ done

  b62 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CCZ123 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff104 ∷ CCZ124 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff104 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Toff214 ∷ CCZ014 ∷ Toff124 ∷ CCZ024 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ [])
  b62 = at 31 2 (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4)) ▸
       at 27 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 28 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 26 3 (CCZ014 ∷ []) (sym (wp1040 c4)) ▸ done

