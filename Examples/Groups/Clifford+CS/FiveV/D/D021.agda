{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.FiveV.D.D021 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.FiveV.WinSig using (Ws ; lit ; wl0217 ; wl0219 ; wl0220 ; wl0221 ; wl0222 ; wl0241 ; wl0244 ; wl0245 ; wl0246 ; wl0247 ; wl0263 ; wl0274 ; wl0305 ; wl0413 ; wl0499 ; wl0501 ; wl0618 ; wl0735 ; wl0758 ; wl0763 ; wl0764 ; wl0765 ; wl0778 ; wl0779 ; wl0780 ; wl0792 ; wl0801 ; wl0861 ; wl0888 ; wl1000 ; wl1013 ; wl1014 ; wl1017 ; wl1190 ; wl1206 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1224 ; wl1225 ; wl1226 ; wl1233 ; wp0002 ; wp0003 ; wp0034 ; wp0035 ; wp0036 ; wp0041 ; wp0053 ; wp0060 ; wp0061 ; wp0062 ; wp0063 ; wp0064 ; wp0065 ; wp0066 ; wp0067 ; wp0069 ; wp0070 ; wp0072 ; wp0074 ; wp0081 ; wp0087 ; wp0088 ; wp0089 ; wp0090 ; wp0094 ; wp0095 ; wp0097 ; wp0106 ; wp0107 ; wp0108 ; wp0124 ; wp0161 ; wp0261 ; wp0265 ; wp0272 ; wp0278 ; wp0301 ; wp0691 ; wp0700 ; wp0701 ; wp0716 ; wp0725 ; wp0805 ; wp0806 ; wp0823 ; wp0836 ; wp0842 ; wp0843 ; wp0845 ; wp1003 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1025 ; wp1026 ; wp1027 ; wp1035 ; wp1036 ; wp1037 ; wp1038 ; wp1039 ; wp1040 ; wp1041 ; wp1042 ; wp1043 ; wp1044 ; wp1045)
open import Examples.Groups.Clifford+CS.FiveV.Chain
open import Examples.Groups.Clifford+CS.FiveV.D.D001 using (lem-box-cP-at122441 ; lem-box-cP-at243243 ; lem-box2-at122441)
open import Examples.Groups.Clifford+CS.FiveV.D.D005 using (lem-box-cP-at0310243142)
open import Examples.Groups.Clifford+CS.FiveV.D.D009 using (lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.FiveV.D.D012 using (lem-box-perm-3241-at243243)
open import Examples.Groups.Clifford+CS.FiveV.D.D020 using (lem-F0-at01143043 ; lem-box-cP-at03243240 ; lem-box-cP-at033440 ; lem-box-perm-1324-at03243240 ; lem-box-perm-4213-at03243240 ; lem-box2-at0310243142 ; lem-nf-comm-CSu-CSat0)
open import Examples.Groups.Clifford+CS.FiveV.D.R004 using (lem-comm-CCZ024-CX13 ; lem-comm-CCZ134-CS02 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.FiveV.D.R005 using (lem-comm-CCZ014-CX23 ; lem-comm-CCZ034-CX12 ; lem-comm-CCZ123-CX04 ; lem-comm-CCZ134-CSd02 ; lem-comm-CCZ134-CX02 ; lem-comm-TOFF013-CX24 ; lem-comm-TOFF023-CX14 ; lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14 ; lem-comm-TOFF304-CX12)
-- F1-comm-CSu-CS@0: 288 steps
lem-F1-comm-CSu-CSat0 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) ⟫ʷ ≈ ⟪ (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-comm-CSu-CSat0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb2-0-41-3 ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b0 = at 0 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 0 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 2 1 (CS01 ∷ []) (refl) ▸
       at 4 1 (CS01⁻ ∷ []) (refl) ▸
       at 5 1 (Bx3-0412 ∷ Toff214 ∷ Sb3-0-2-1 ∷ Toff214 ∷ Sb⁻3-0-2-1 ∷ []) (refl) ▸
       at 7 1 (CS02 ∷ []) (refl) ▸
       at 9 1 (CS02⁻ ∷ []) (refl) ▸ done

  b1 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Bx3-0412 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b1 = at 5 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 8 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 8 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 7 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 8 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 11 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸ done

  b2 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CCZ034 ∷ CS14 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b2 = at 12 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 13 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 7 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 8 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 6 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 8 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 10 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 9 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸ done

  b3 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ Toff312 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b3 = at 10 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 11 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 12 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 13 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 9 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 6 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 6 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 5 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸ done

  b4 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ K2 ∷ CCZ034 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b4 = at 6 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 7 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 9 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 10 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 11 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 5 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 6 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸ done

  b5 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02⁻ ∷ [])
  b5 = at 7 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 7 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 10 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 9 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 8 2 (CS02 ∷ Toff312 ∷ []) (sym (wl0861 (lit c4))) ▸
       at 7 2 (CS02 ∷ CCZ034 ∷ []) (wp0003 c4) ▸
       at 8 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 8 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸ done

  b6 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ Toff214 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ [])
  b6 = at 11 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 11 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 10 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 11 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸
       at 12 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 13 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 14 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 15 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸ done

  b7 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff312 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ CCZ034 ∷ K2⁻ ∷ Toff314 ∷ Toff312 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ [])
  b7 = at 16 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 10 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 11 2 (Toff314 ∷ CCZ014 ∷ CCZ034 ∷ []) (wp0716 c4) ▸
       at 9 2 (Toff214 ∷ Toff314 ∷ Toff312 ∷ []) (sym (wl1225 (lit c4))) ▸
       at 11 2 (Toff314 ∷ Toff312 ∷ []) (wl0779 (lit c4)) ▸
       at 13 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 12 2 (CS14 ∷ Toff312 ∷ []) (sym (wl0499 (lit c4))) ▸
       at 13 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸ done

  b8 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ CCZ034 ∷ Toff214 ∷ Toff314 ∷ Toff314 ∷ CS14 ∷ CX04 ∷ Toff312 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ [])
  b8 = at 14 2 (CS14⁻ ∷ Toff312 ∷ []) (sym (wl0778 (lit c4))) ▸
       at 15 2 (CX04 ∷ Toff312 ∷ []) (lem-comm-TOFF312-CX04 (lit c4)) ▸
       at 16 2 (CS01 ∷ Toff312 ∷ []) (sym (wl0501 (lit c4))) ▸
       at 12 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 9 3 (Toff214 ∷ []) (wl0780 (lit c4)) ▸
       at 9 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 8 2 (K2 ∷ CCZ034 ∷ []) (wp0701 c4) ▸
       at 9 2 (CS24 ∷ CCZ034 ∷ []) (wp0108 c4) ▸ done

  b9 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ K2 ∷ CS24 ∷ CCZ034 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ CS02⁻ ∷ []) (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ CS02⁻ ∷ [])
  b9 = at 10 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ CCZ034 ∷ []) (wp0107 c4) ▸
       at 12 2 (CX12 ∷ CCZ034 ∷ []) (lem-comm-CCZ034-CX12 (lit c4)) ▸
       at 13 2 (CS14 ∷ CCZ034 ∷ []) (wp0106 c4) ▸
       at 14 2 (K2⁻ ∷ CCZ034 ∷ []) (wp0700 c4) ▸
       at 8 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 9 2 (CCZ014 ∷ CCZ034 ∷ []) (sym (wp0124 c4)) ▸
       at 10 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸ done

  b10 : Chain (Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ Bx3-0412 ∷ CS02⁻ ∷ []) (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b10 = at 10 1 (CCZ034 ∷ Toff312 ∷ CCZ034 ∷ Toff312 ∷ []) (lem-box-cP-at0310243142 c4) ▸
       at 13 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 12 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 11 2 (CS02⁻ ∷ Toff312 ∷ []) (sym (wl1226 (lit c4))) ▸
       at 10 2 (CS02⁻ ∷ CCZ034 ∷ []) (wp0002 c4) ▸
       at 11 4 (Bx3-0412 ∷ []) (sym (lem-box-cP-at0310243142 c4)) ▸
       at 0 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸ done

  b11 : Chain (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ134 ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b11 = at 3 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 2 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 3 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 4 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 6 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 7 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 8 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸ done

  b12 : Chain (CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ134 ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff302 ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b12 = at 2 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 3 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 1 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 3 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 5 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 4 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 5 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸ done

  b13 : Chain (CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ Toff302 ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (K0 ∷ CS24 ∷ CX02 ∷ CCZ134 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b13 = at 7 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 8 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 4 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 1 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 1 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 0 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 1 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 2 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b14 : Chain (K0 ∷ CS24 ∷ CX02 ∷ CCZ134 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b14 = at 3 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 4 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 5 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 6 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 0 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 1 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 2 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 2 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸ done

  b15 : Chain (Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b15 = at 5 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 4 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 3 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 2 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 3 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 3 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 6 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸ done

  b16 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ134 ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b16 = at 5 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 6 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 11 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 5 7 (Toff024 ∷ []) (wp1026 c4) ▸ done

  b17 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ Toff024 ∷ CCZ134 ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff302 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b17 = at 6 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 4 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 6 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 8 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 7 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 8 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 9 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 10 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸ done

  b18 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ Toff302 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b18 = at 11 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 7 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 4 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 4 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 3 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 4 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 5 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 6 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸ done

  b19 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01⁻ ∷ Toff302 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b19 = at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 8 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 9 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 3 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 4 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 5 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 5 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 8 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸ done

  b20 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS01⁻ ∷ Toff302 ∷ Toff214 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ Toff304 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b20 = at 7 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 6 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 5 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 6 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 6 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸
       at 6 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸
       at 10 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 9 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸ done

  b21 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ Toff304 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b21 = at 10 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 11 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 12 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 13 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 14 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 15 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸
       at 9 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 8 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸ done

  b22 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff304 ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b22 = at 8 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 7 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 8 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 9 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 11 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 12 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 13 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸ done

  b23 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff304 ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CCZ123 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b23 = at 7 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (sym (wp1039 c4)) ▸
       at 6 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 9 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 8 2 (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4)) ▸
       at 9 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸
       at 10 2 (CS14⁻ ∷ CCZ123 ∷ []) (wl0764 (lit c4)) ▸
       at 11 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸ done

  b24 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CCZ123 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b24 = at 12 2 (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4)) ▸
       at 8 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 9 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 7 3 (CCZ014 ∷ []) (sym (wp1040 c4)) ▸
       at 8 4 (Bx3-1240 ∷ []) (sym (lem-box-cP-at033440 c4)) ▸
       at 8 1 (Bx3-1420 ∷ []) (sym (lem-box-perm-1324-at03243240 c4)) ▸
       at 8 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 12 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸ done

  b25 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b25 = at 11 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 12 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 13 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 14 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 15 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 11 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 10 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 10 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸ done

  b26 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b26 = at 9 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 10 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 11 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 12 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 13 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 9 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 8 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 9 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b27 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ Bx3-1420 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b27 = at 9 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 12 2 (CS02 ∷ Toff302 ∷ []) (sym (wl0801 (lit c4))) ▸
       at 11 2 (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4)) ▸
       at 10 2 (CS02 ∷ Toff302 ∷ []) (sym (wl0801 (lit c4))) ▸
       at 9 2 (CS02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CS02 (lit c4)) ▸
       at 10 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 10 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸
       at 10 1 (CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ []) (lem-box-cP-at033440 c4) ▸ done

  b28 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ Toff214 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b28 = at 14 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 13 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 14 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 15 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 16 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 17 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 18 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 19 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸ done

  b29 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ Toff304 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff304 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b29 = at 13 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 12 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 12 1 (K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ CS14 ∷ K2⁻ ∷ []) (sym (wl0888 (lit c4))) ▸
       at 11 2 (K2 ∷ Toff304 ∷ []) (sym (wp1035 c4)) ▸
       at 12 2 (CS24 ∷ Toff304 ∷ []) (sym (wp0691 c4)) ▸
       at 13 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸
       at 14 2 (CS24⁻ ∷ Toff304 ∷ []) (sym (wp1036 c4)) ▸
       at 15 2 (CX12 ∷ Toff304 ∷ []) (lem-comm-TOFF304-CX12 (lit c4)) ▸ done

  b30 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ CCZ123 ∷ K2 ∷ CS24 ∷ CX12 ∷ CS24⁻ ∷ CX12 ∷ Toff304 ∷ CS14 ∷ K2⁻ ∷ CCZ134 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b30 = at 16 2 (CS14 ∷ Toff304 ∷ []) (sym (wp1037 c4)) ▸
       at 17 2 (K2⁻ ∷ Toff304 ∷ []) (sym (wp1038 c4)) ▸
       at 11 7 (Toff214 ∷ []) (wl0888 (lit c4)) ▸
       at 12 2 (CCZ014 ∷ CCZ134 ∷ Toff304 ∷ []) (sym (wp1039 c4)) ▸
       at 10 2 (Toff214 ∷ CCZ134 ∷ CCZ123 ∷ []) (wl0758 (lit c4)) ▸
       at 13 1 (CS14 ∷ CX04 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ []) (wp0041 c4) ▸
       at 12 2 (CS14 ∷ CCZ123 ∷ []) (wl0765 (lit c4)) ▸
       at 13 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸ done

  b31 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ134 ∷ CS14 ∷ CX04 ∷ CCZ123 ∷ CS14⁻ ∷ CX04 ∷ CS01 ∷ CCZ134 ∷ Toff304 ∷ CCZ123 ∷ Toff304 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ Bx3-1420 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b31 = at 14 2 (CS14⁻ ∷ CCZ123 ∷ []) (wl0764 (lit c4)) ▸
       at 15 2 (CX04 ∷ CCZ123 ∷ []) (lem-comm-CCZ123-CX04 (lit c4)) ▸
       at 16 2 (CS01 ∷ CCZ123 ∷ []) (wl0763 (lit c4)) ▸
       at 12 5 (CCZ014 ∷ []) (sym (wp0041 c4)) ▸
       at 13 2 (CCZ134 ∷ CCZ123 ∷ []) (wl0618 (lit c4)) ▸
       at 11 3 (CCZ014 ∷ []) (sym (wp1040 c4)) ▸
       at 12 4 (Bx3-1240 ∷ []) (sym (lem-box-cP-at033440 c4)) ▸
       at 12 1 (Bx3-1420 ∷ []) (sym (lem-box-perm-1324-at03243240 c4)) ▸ done

  b32 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ Bx3-1420 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CCZ014 ∷ Toff302 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b32 = at 12 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 16 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 15 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 16 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 17 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 18 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 19 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 15 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

  b33 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CCZ014 ∷ Toff302 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS02⁻ ∷ Bx3-0412 ∷ [])
  b33 = at 14 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 14 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 13 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 14 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 15 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 16 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 17 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 13 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

  b34 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ134 ∷ CCZ014 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS02⁻ ∷ Bx3-0412 ∷ []) (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-1420 ∷ Bx3-0412 ∷ [])
  b34 = at 12 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 13 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 13 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 16 2 (CS02⁻ ∷ Toff302 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 15 2 (CS02⁻ ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CSd02 (lit c4)) ▸
       at 14 2 (CS02⁻ ∷ Toff302 ∷ []) (sym (wl0792 (lit c4))) ▸
       at 13 2 (CS02⁻ ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CSd02 (lit c4)) ▸
       at 14 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b35 : Chain (Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02 ∷ Toff214 ∷ CCZ014 ∷ CCZ014 ∷ CS02⁻ ∷ Bx3-1420 ∷ Bx3-0412 ∷ []) (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ [])
  b35 = at 14 1 (Bx3-0412 ∷ []) (lem-box-perm-4213-at03243240 c4) ▸
       at 14 2 [] (lem-box2-at0310243142 c4) ▸
       at 1 3 (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp1042 c4) ▸
       at 3 2 [] (wl0263 (lit c4)) ▸
       at 5 2 [] (wp0161 c4) ▸
       at 7 2 [] (wp0161 c4) ▸
       at 0 8 (Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ []) (wp1043 c4) ▸
       at 0 8 (Sb2-0-41-3 ∷ Sb0-1-42-3 ∷ []) (sym (lem-nf-comm-CSu-CSat0 c4)) ▸ done


-- nf-comm-CSu-CS@1: 282 steps
lem-nf-comm-CSu-CSat1 : Ws → ⟪ (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) ⟫ʷ ≈ ⟪ (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) ⟫ʷ
lem-nf-comm-CSu-CSat1 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (trans (run b20) (trans (run b21) (trans (run b22) (trans (run b23) (trans (run b24) (trans (run b25) (trans (run b26) (trans (run b27) (trans (run b28) (trans (run b29) (trans (run b30) (trans (run b31) (trans (run b32) (trans (run b33) (trans (run b34) (run b35)))))))))))))))))))))))))))))))))))
  where
  b0 : Chain (Sb0-1-42-3 ∷ Sb0-2-43-1 ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b0 = at 0 1 (Bx0-1423 ∷ Toff324 ∷ Sb0-1-3-2 ∷ Toff324 ∷ Sb⁻0-1-3-2 ∷ []) (refl) ▸
       at 2 1 (CS13 ∷ []) (refl) ▸
       at 4 1 (CS13⁻ ∷ []) (refl) ▸
       at 5 1 (Bx0-2431 ∷ Toff134 ∷ Sb0-2-1-3 ∷ Toff134 ∷ Sb⁻0-2-1-3 ∷ []) (refl) ▸
       at 7 1 (CS12 ∷ []) (refl) ▸
       at 9 1 (CS12⁻ ∷ []) (refl) ▸
       at 5 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 8 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸ done

  b1 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff034 ∷ Toff134 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b1 = at 7 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸
       at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸ done

  b2 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ CCZ024 ∷ K1⁻ ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b2 = at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 9 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 6 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 8 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 7 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 8 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 10 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸ done

  b3 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ Toff013 ∷ CS23 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b3 = at 11 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸
       at 7 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 8 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 6 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 5 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 7 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 6 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 7 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸ done

  b4 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CCZ024 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b4 = at 8 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 9 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 10 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 11 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 12 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 6 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 7 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 7 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸ done

  b5 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b5 = at 10 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 9 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 8 2 (CS12 ∷ Toff013 ∷ []) (sym (wl0247 (lit c4))) ▸
       at 7 2 (CS12 ∷ CCZ024 ∷ []) (wp0081 c4) ▸
       at 8 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 8 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 11 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 10 2 (Toff034 ∷ CCZ234 ∷ CCZ024 ∷ []) (wp0845 c4) ▸ done

  b6 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ CCZ024 ∷ Toff134 ∷ Toff013 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b6 = at 13 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 12 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 13 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 14 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 16 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 17 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 18 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸ done

  b7 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff013 ∷ Toff034 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b7 = at 12 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 9 2 (Toff034 ∷ Toff013 ∷ []) (wp0097 c4) ▸
       at 11 1 (CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ []) (wl0245 (lit c4)) ▸
       at 10 2 (CS34 ∷ Toff013 ∷ []) (sym (wp0095 c4)) ▸
       at 11 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ Toff013 ∷ []) (sym (wp0094 c4)) ▸
       at 13 2 (CX24 ∷ Toff013 ∷ []) (lem-comm-TOFF013-CX24 (lit c4)) ▸
       at 14 2 (CS23 ∷ Toff013 ∷ []) (sym (wl0246 (lit c4))) ▸ done

  b8 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ024 ∷ Toff034 ∷ CS34 ∷ CX24 ∷ CS34⁻ ∷ CX24 ∷ CS23 ∷ Toff013 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ [])
  b8 = at 10 5 (CCZ234 ∷ []) (sym (wl0245 (lit c4))) ▸
       at 11 2 (Toff034 ∷ Toff134 ∷ Toff013 ∷ []) (wp0843 c4) ▸
       at 9 3 (CCZ234 ∷ []) (sym (wp0842 c4)) ▸
       at 8 2 (CCZ234 ∷ CCZ024 ∷ []) (wp0090 c4) ▸
       at 10 1 (K1 ∷ CS34 ∷ CX13 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ []) (sym (wl0241 (lit c4))) ▸
       at 9 2 (K1 ∷ CCZ024 ∷ []) (wp0089 c4) ▸
       at 10 2 (CS34 ∷ CCZ024 ∷ []) (wp0036 c4) ▸
       at 11 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸ done

  b9 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ K1 ∷ CS34 ∷ CX13 ∷ CCZ024 ∷ CS34⁻ ∷ CX13 ∷ CS14 ∷ K1⁻ ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ CS12⁻ ∷ []) (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ [])
  b9 = at 12 2 (CS34⁻ ∷ CCZ024 ∷ []) (wp0035 c4) ▸
       at 13 2 (CX13 ∷ CCZ024 ∷ []) (lem-comm-CCZ024-CX13 (lit c4)) ▸
       at 14 2 (CS14 ∷ CCZ024 ∷ []) (wp0034 c4) ▸
       at 15 2 (K1⁻ ∷ CCZ024 ∷ []) (wp0088 c4) ▸
       at 9 7 (Toff134 ∷ []) (wl0241 (lit c4)) ▸
       at 10 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 10 1 (CCZ024 ∷ Toff013 ∷ CCZ024 ∷ Toff013 ∷ []) (lem-box-cP-at122441 c4) ▸
       at 13 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸ done

  b10 : Chain (Bx0-1423 ∷ Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ024 ∷ Toff013 ∷ CCZ024 ∷ CS12⁻ ∷ Toff013 ∷ []) (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b10 = at 12 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 11 2 (CS12⁻ ∷ Toff013 ∷ []) (sym (wl0244 (lit c4))) ▸
       at 10 2 (CS12⁻ ∷ CCZ024 ∷ []) (wp0087 c4) ▸
       at 11 4 (Bx0-2431 ∷ []) (sym (lem-box-cP-at122441 c4)) ▸
       at 0 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 2 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸ done

  b11 : Chain (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ CCZ014 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b11 = at 4 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 5 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 9 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 10 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸ done

  b12 : Chain (CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b12 = at 1 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸
       at 3 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 2 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 3 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 4 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 5 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 6 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 2 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸ done

  b13 : Chain (CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff023 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b13 = at 3 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 1 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 0 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 2 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 1 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 2 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 3 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 4 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b14 : Chain (CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b14 = at 5 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 6 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 7 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 1 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 2 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 2 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 5 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 4 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸ done

  b15 : Chain (CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b15 = at 3 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 2 2 (CS13 ∷ CCZ014 ∷ []) (wp0053 c4) ▸
       at 3 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 3 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸
       at 5 2 (Toff024 ∷ CCZ124 ∷ CCZ014 ∷ []) (wp0806 c4) ▸
       at 8 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 7 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸ done

  b16 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff023 ∷ Toff024 ∷ CCZ124 ∷ K3 ∷ CCZ014 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b16 = at 8 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 13 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 7 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 4 2 (Toff024 ∷ Toff023 ∷ []) (wp0072 c4) ▸ done

  b17 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ Toff023 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b17 = at 6 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 5 2 (CS24 ∷ Toff023 ∷ []) (sym (wp0070 c4)) ▸
       at 6 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ Toff023 ∷ []) (sym (wp0069 c4)) ▸
       at 8 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 9 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 5 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff023 ∷ []) (wp0805 c4) ▸ done

  b18 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ014 ∷ Toff024 ∷ CCZ124 ∷ Toff024 ∷ Toff324 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b18 = at 4 3 (CCZ124 ∷ []) (sym (wp0074 c4)) ▸
       at 3 2 (CCZ124 ∷ CCZ014 ∷ []) (wp0066 c4) ▸
       at 5 1 (K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ K3⁻ ∷ []) (sym (wl0217 (lit c4))) ▸
       at 4 2 (K3 ∷ CCZ014 ∷ []) (wp0065 c4) ▸
       at 5 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 6 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 7 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 8 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b19 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ K3 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ K3⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b19 = at 9 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 10 2 (K3⁻ ∷ CCZ014 ∷ []) (wp0061 c4) ▸
       at 4 7 (Toff324 ∷ []) (wl0217 (lit c4)) ▸
       at 5 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 5 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 8 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸
       at 7 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 2 (CS13⁻ ∷ Toff023 ∷ []) (sym (wl0219 (lit c4))) ▸ done

  b20 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CCZ014 ∷ CS13⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b20 = at 5 2 (CS13⁻ ∷ CCZ014 ∷ []) (wp0060 c4) ▸
       at 6 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 6 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 9 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 9 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 8 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b21 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b21 = at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 8 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 7 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 7 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 6 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 7 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 8 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b22 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ Toff023 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b22 = at 9 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 10 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 6 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 7 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 7 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 11 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸
       at 10 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 11 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸ done

  b23 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ Toff023 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ034 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b23 = at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 16 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 10 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸
       at 9 2 (Toff134 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1044 c4) ▸
       at 9 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸ done

  b24 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ034 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff134 ∷ Toff023 ∷ CCZ034 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b24 = at 8 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 9 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 10 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 11 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 12 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 13 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 14 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 8 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸ done

  b25 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ CCZ014 ∷ Toff134 ∷ Toff023 ∷ CCZ034 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ034 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b25 = at 9 2 (CCZ034 ∷ CCZ234 ∷ Toff023 ∷ []) (sym (wp1045 c4)) ▸
       at 7 2 (Toff134 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1044 c4) ▸
       at 9 2 (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4) ▸
       at 11 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 10 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b26 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ034 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ014 ∷ CS12 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b26 = at 14 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 10 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 7 3 (Toff134 ∷ []) (wp0836 c4) ▸
       at 9 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 9 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 12 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸
       at 11 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 10 2 (CS12 ∷ Toff023 ∷ []) (sym (wl0221 (lit c4))) ▸ done

  b27 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ014 ∷ CS12 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CCZ234 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b27 = at 9 2 (CS12 ∷ CCZ014 ∷ []) (wp0067 c4) ▸
       at 10 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 10 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 13 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 13 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 12 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b28 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ014 ∷ Toff023 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b28 = at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 16 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 12 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 11 2 (CCZ234 ∷ Toff023 ∷ []) (sym (wp0278 c4)) ▸
       at 11 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 10 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 11 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 12 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸ done

  b29 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CCZ014 ∷ CX23 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Toff134 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ Toff023 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b29 = at 13 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 14 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 10 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 11 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 11 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 15 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸
       at 14 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 15 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸ done

  b30 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ CCZ014 ∷ K1 ∷ CS34 ∷ Toff023 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ034 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b30 = at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 18 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 19 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 20 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 14 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸
       at 13 2 (Toff134 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1044 c4) ▸
       at 13 1 (K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ []) (sym (wl1013 (lit c4))) ▸ done

  b31 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ CCZ014 ∷ Toff023 ∷ K1 ∷ CS34 ∷ CX14 ∷ CS34⁻ ∷ CX14 ∷ CS13 ∷ K1⁻ ∷ CCZ034 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ CCZ014 ∷ Toff134 ∷ Toff023 ∷ CCZ034 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b31 = at 12 2 (K1 ∷ Toff023 ∷ []) (sym (wl0735 (lit c4))) ▸
       at 13 2 (CS34 ∷ Toff023 ∷ []) (sym (wp0725 c4)) ▸
       at 14 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 15 2 (CS34⁻ ∷ Toff023 ∷ []) (sym (wp0823 c4)) ▸
       at 16 2 (CX14 ∷ Toff023 ∷ []) (lem-comm-TOFF023-CX14 (lit c4)) ▸
       at 17 2 (CS13 ∷ Toff023 ∷ []) (sym (wl0222 (lit c4))) ▸
       at 18 2 (K1⁻ ∷ Toff023 ∷ []) (sym (wl1014 (lit c4))) ▸
       at 12 7 (Toff134 ∷ []) (wl1013 (lit c4)) ▸ done

  b32 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ CCZ014 ∷ Toff134 ∷ Toff023 ∷ CCZ034 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ034 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ Bx0-2431 ∷ [])
  b32 = at 13 2 (CCZ034 ∷ CCZ234 ∷ Toff023 ∷ []) (sym (wp1045 c4)) ▸
       at 11 2 (Toff134 ∷ CCZ034 ∷ CCZ014 ∷ []) (wp1044 c4) ▸
       at 13 2 (CCZ034 ∷ CCZ014 ∷ []) (wp0124 c4) ▸
       at 15 1 (CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CS24 ∷ []) (wl0274 (lit c4)) ▸
       at 14 2 (CS34 ∷ CCZ014 ∷ []) (wp0064 c4) ▸
       at 15 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸
       at 16 2 (CS34⁻ ∷ CCZ014 ∷ []) (wp0063 c4) ▸
       at 17 2 (CX23 ∷ CCZ014 ∷ []) (lem-comm-CCZ014-CX23 (lit c4)) ▸ done

  b33 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ034 ∷ CCZ034 ∷ CS34 ∷ CX23 ∷ CS34⁻ ∷ CX23 ∷ CCZ014 ∷ CS24 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ CS12⁻ ∷ Bx0-2431 ∷ []) (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ014 ∷ CS12⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx0-2431 ∷ [])
  b33 = at 18 2 (CS24 ∷ CCZ014 ∷ []) (wp0062 c4) ▸
       at 14 5 (CCZ234 ∷ []) (sym (wl0274 (lit c4))) ▸
       at 11 3 (Toff134 ∷ []) (wp0836 c4) ▸
       at 13 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 13 1 (CCZ014 ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ []) (lem-box-cP-at243243 c4) ▸
       at 16 2 (CS12⁻ ∷ Toff023 ∷ []) (sym (wl1017 (lit c4))) ▸
       at 15 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸
       at 14 2 (CS12⁻ ∷ Toff023 ∷ []) (sym (wl1017 (lit c4))) ▸ done

  b34 : Chain (CCZ124 ∷ Toff324 ∷ CS13 ∷ CCZ124 ∷ Toff324 ∷ CS13⁻ ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CCZ014 ∷ CS12⁻ ∷ Toff023 ∷ CCZ014 ∷ Toff023 ∷ Bx0-2431 ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ [])
  b34 = at 13 2 (CS12⁻ ∷ CCZ014 ∷ []) (wp0265 c4) ▸
       at 14 4 (Bx0-1423 ∷ []) (sym (lem-box-cP-at243243 c4)) ▸
       at 14 1 (Bx0-2431 ∷ []) (lem-box-perm-3241-at243243 c4) ▸
       at 14 2 [] (lem-box2-at122441 c4) ▸
       at 0 3 (Toff324 ∷ CS13 ∷ CCZ124 ∷ []) (wl1000 (lit c4)) ▸
       at 2 2 [] (wl0263 (lit c4)) ▸
       at 4 2 (Toff134 ∷ CCZ234 ∷ []) (wl0413 (lit c4)) ▸
       at 5 2 [] (wl0305 (lit c4)) ▸ done

  b35 : Chain (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ CCZ234 ∷ Toff134 ∷ CCZ234 ∷ CS12⁻ ∷ []) (Toff324 ∷ CS13 ∷ Toff324 ∷ CS13⁻ ∷ Toff134 ∷ CS12 ∷ Toff134 ∷ CS12⁻ ∷ [])
  b35 = at 6 2 (Toff134 ∷ CCZ234 ∷ []) (wl0413 (lit c4)) ▸
       at 7 2 [] (wl0305 (lit c4)) ▸ done

