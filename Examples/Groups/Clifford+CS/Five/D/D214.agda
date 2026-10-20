{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.D.D214 where

open import Data.List using (List ; [] ; _∷_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality as Eq using ()
open import Word.Base using (ε ; _•_)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.MultiControlled using (CZ ; CK₀₁ ; CK₁₀ ; Toffᵗ)
open import Examples.Groups.Clifford+CS.Five.WinSig using (Ws ; lit ; wl0220 ; wl0263 ; wl0499 ; wl0501 ; wl0618 ; wl0758 ; wl0763 ; wl0764 ; wl0765 ; wl0778 ; wl0779 ; wl0780 ; wl0792 ; wl0801 ; wl0861 ; wl0888 ; wl1190 ; wl1206 ; wl1220 ; wl1221 ; wl1222 ; wl1223 ; wl1224 ; wl1225 ; wl1226 ; wl1233 ; wp0002 ; wp0003 ; wp0041 ; wp0106 ; wp0107 ; wp0108 ; wp0124 ; wp0161 ; wp0261 ; wp0272 ; wp0301 ; wp0691 ; wp0700 ; wp0701 ; wp0716 ; wp1003 ; wp1005 ; wp1006 ; wp1007 ; wp1008 ; wp1025 ; wp1026 ; wp1027 ; wp1035 ; wp1036 ; wp1037 ; wp1038 ; wp1039 ; wp1040 ; wp1041 ; wp1042 ; wp1043 ; wl0341 ; wl1249 ; wl1269 ; wp0167 ; wp1110 ; wp1111 ; wp1112 ; wp1119 ; wp1120)
open import Examples.Groups.Clifford+CS.Five.Chain
open import Examples.Groups.Clifford+CS.Five.D.D016 using (lem-box-cP-at0310243142 ; lem-box-cP-at03243240 ; lem-box-cP-at033440)
open import Examples.Groups.Clifford+CS.Five.D.D021 using (lem-box-perm-1324-at03243240 ; lem-box-perm-1324-at033440 ; lem-box2-at0310243142)
open import Examples.Groups.Clifford+CS.Five.D.D027 using (lem-CKc-box-at0312203441 ; lem-CKc-box-at033440 ; lem-S2-SBOX⟨3·0·41·2⟩ ; lem-S2-SBOX⟨3·1·42·0⟩ ; lem-box-perm-3421-at03243240 ; lem-box-perm-4213-at03243240 ; lem-box-perm-4312-at0312203441)
open import Examples.Groups.Clifford+CS.Five.D.D189 using (lem-F0-at01143043 ; lem-F0-at14213243)
open import Examples.Groups.Clifford+CS.Five.D.D204 using (lem-nf-comm-CSu-CSat0)
open import Examples.Groups.Clifford+CS.Five.D.D205 using (lem-nf-rel-266at0 ; lem-nf-rel-267at0)
open import Examples.Groups.Clifford+CS.Five.D.R002 using (lem-comm-CCZ034-CX12 ; lem-comm-CCZ134-CS02 ; lem-comm-CCZ134-CX02 ; lem-comm-TOFF304-CX12 ; lem-comm-TOFF312-CX04)
open import Examples.Groups.Clifford+CS.Five.D.R003 using (lem-comm-CCZ123-CX04 ; lem-comm-CCZ134-CSd02)
open import Examples.Groups.Clifford+CS.Five.D.R009 using (lem-comm-TOFF302-CS14 ; lem-comm-TOFF302-CSd14 ; lem-comm-TOFF302-CX14)

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

-- F1-rel-266@0: 166 steps
lem-F1-rel-266at0 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) ⟫ʷ
lem-F1-rel-266at0 c4 = trans (run b0) (trans (run b1) (trans (run b2) (trans (run b3) (trans (run b4) (trans (run b5) (trans (run b6) (trans (run b7) (trans (run b8) (trans (run b9) (trans (run b10) (trans (run b11) (trans (run b12) (trans (run b13) (trans (run b14) (trans (run b15) (trans (run b16) (trans (run b17) (trans (run b18) (trans (run b19) (run b20))))))))))))))))))))
  where
  b0 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 2 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 6 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 7 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 10 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 12 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 13 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 17 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸ done

  b1 : Chain (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb3-0-41-2 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b1 = at 18 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 1 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 5 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 10 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 14 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 8 1 (Bx3-1420 ∷ Toff024 ∷ Sb3-1-0-2 ∷ Toff024 ∷ Sb⁻3-1-0-2 ∷ []) (refl) ▸
       at 10 1 (CS01 ∷ []) (refl) ▸
       at 12 1 (CS01⁻ ∷ []) (refl) ▸ done

  b2 : Chain (CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ Bx3-1420 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b2 = at 0 8 (Toff014 ∷ Toff104 ∷ []) (wp1110 c4) ▸
       at 2 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 5 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 5 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 4 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 5 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 6 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 7 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸ done

  b3 : Chain (Toff014 ∷ Toff104 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CCZ134 ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ Toff302 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b3 = at 8 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 9 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 10 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 4 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 5 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 3 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 5 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 7 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸ done

  b4 : Chain (Toff014 ∷ Toff104 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ Toff302 ∷ CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b4 = at 6 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸
       at 7 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 9 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 10 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 6 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 3 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 3 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸ done

  b5 : Chain (Toff014 ∷ Toff104 ∷ CCZ134 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ134 ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b5 = at 2 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 3 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 4 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 5 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 6 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 7 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 8 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 2 7 (Toff024 ∷ []) (wp1026 c4) ▸ done

  b6 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ134 ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Bx3-1420 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b6 = at 3 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸
       at 4 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 4 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 7 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 6 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 5 2 (CS01 ∷ Toff302 ∷ []) (sym (wl1223 (lit c4))) ▸
       at 4 2 (CS01 ∷ CCZ134 ∷ []) (wp0261 c4) ▸
       at 5 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸ done

  b7 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Bx3-1420 ∷ Toff024 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b7 = at 5 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 8 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 8 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 7 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 8 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 11 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸ done

  b8 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff302 ∷ K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CCZ134 ∷ CS04 ∷ K0⁻ ∷ Toff324 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b8 = at 12 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 13 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 7 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 8 2 (Toff324 ∷ CCZ124 ∷ CCZ134 ∷ []) (wl1206 (lit c4)) ▸
       at 6 2 (Toff024 ∷ Toff324 ∷ Toff302 ∷ []) (sym (wp1025 c4)) ▸
       at 8 2 (Toff324 ∷ Toff302 ∷ []) (wp1007 c4) ▸
       at 10 1 (CS24 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ []) (wl0220 (lit c4)) ▸
       at 9 2 (CS24 ∷ Toff302 ∷ []) (sym (wp1006 c4)) ▸ done

  b9 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ CCZ134 ∷ Toff024 ∷ Toff324 ∷ Toff324 ∷ CS24 ∷ Toff302 ∷ CX14 ∷ CS24⁻ ∷ CX14 ∷ CS12 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b9 = at 10 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 11 2 (CS24⁻ ∷ Toff302 ∷ []) (sym (wp1005 c4)) ▸
       at 12 2 (CX14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CX14 (lit c4)) ▸
       at 13 2 (CS12 ∷ Toff302 ∷ []) (sym (wl1190 (lit c4))) ▸
       at 9 5 (CCZ124 ∷ []) (sym (wl0220 (lit c4))) ▸
       at 6 3 (Toff024 ∷ []) (wp1008 c4) ▸
       at 6 1 (K0 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ []) (sym (wp1026 c4)) ▸
       at 5 2 (K0 ∷ CCZ134 ∷ []) (sym (c₁ (K) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸ done

  b10 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ K0 ∷ CCZ134 ∷ CS24 ∷ CX02 ∷ CS24⁻ ∷ CX02 ∷ CS04 ∷ K0⁻ ∷ CCZ124 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b10 = at 6 2 (CS24 ∷ CCZ134 ∷ []) (wl1220 (lit c4)) ▸
       at 7 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 8 2 (CS24⁻ ∷ CCZ134 ∷ []) (wl1221 (lit c4)) ▸
       at 9 2 (CX02 ∷ CCZ134 ∷ []) (lem-comm-CCZ134-CX02 (lit c4)) ▸
       at 10 2 (CS04 ∷ CCZ134 ∷ []) (wp1003 c4) ▸
       at 11 2 (K0⁻ ∷ CCZ134 ∷ []) (sym (c₁ (K • iI) (Swap ↑ • (Swap ↑ ↑ • CCZ • Swap ↑ ↑) • Swap ↑))) ▸
       at 5 7 (Toff024 ∷ []) (wp1026 c4) ▸
       at 6 2 (CCZ124 ∷ CCZ134 ∷ []) (sym (wl1222 (lit c4))) ▸ done

  b11 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CS01⁻ ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-2041 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b11 = at 7 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 7 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 10 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 9 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 8 2 (CS01⁻ ∷ Toff302 ∷ []) (sym (wl1224 (lit c4))) ▸
       at 7 2 (CS01⁻ ∷ CCZ134 ∷ []) (wp1027 c4) ▸
       at 8 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 8 1 (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4) ▸ done

  b12 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ Bx3-2041 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b12 = at 8 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4) ▸
       at 11 1 (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4) ▸
       at 11 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 15 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 14 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 15 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 16 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 17 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸ done

  b13 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b13 = at 18 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 14 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 13 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 13 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 12 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 13 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 14 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 15 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸ done

  b14 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ Toff302 ∷ CS04 ∷ CCZ134 ∷ Toff302 ∷ CK41 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b14 = at 16 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 12 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸
       at 11 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 12 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 12 1 (Bx3-2041 ∷ []) (lem-box-perm-3421-at03243240 c4) ▸
       at 12 2 (CCZ012 ∷ CK41 ∷ CCZ012 ∷ Bx3-2041 ∷ []) (lem-CKc-box-at0312203441 c4) ▸
       at 15 1 (Bx3-1420 ∷ []) (lem-box-perm-4312-at0312203441 c4) ▸
       at 15 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸ done

  b15 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ CK40 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1420 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ [])
  b15 = at 18 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 17 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 16 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 15 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 16 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 16 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸
       at 16 2 (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ []) (lem-CKc-box-at033440 c4) ▸
       at 19 1 (Bx3-1420 ∷ []) (lem-box-perm-1324-at033440 c4) ▸ done

  b16 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1420 ∷ CCZ014 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CCZ014 ∷ Toff302 ∷ CK40 ∷ S4 ∷ [])
  b16 = at 19 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 23 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 22 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 23 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 24 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 25 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 26 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 22 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

  b17 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ CCZ134 ∷ CCZ014 ∷ Toff302 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ134 ∷ CCZ014 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CK40 ∷ S4 ∷ [])
  b17 = at 21 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 21 1 (CS14 ∷ CX01 ∷ CS14⁻ ∷ CX01 ∷ CS04 ∷ []) (wp0301 c4) ▸
       at 20 2 (CS14 ∷ Toff302 ∷ []) (lem-comm-TOFF302-CS14 (lit c4)) ▸
       at 21 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 22 2 (CS14⁻ ∷ Toff302 ∷ []) (lem-comm-TOFF302-CSd14 (lit c4)) ▸
       at 23 2 (CX01 ∷ Toff302 ∷ []) (sym (wl1233 (lit c4))) ▸
       at 24 2 (CS04 ∷ Toff302 ∷ []) (sym (wp1041 c4)) ▸
       at 20 5 (CCZ014 ∷ []) (sym (wp0301 c4)) ▸ done

  b18 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ134 ∷ CCZ014 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ CK40 ∷ S4 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ CCZ134 ∷ Toff302 ∷ [])
  b18 = at 19 2 (CCZ014 ∷ CCZ134 ∷ []) (sym (wp0272 c4)) ▸
       at 20 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 20 1 (Bx3-1240 ∷ []) (lem-box-perm-1324-at03243240 c4) ▸
       at 20 2 (CCZ012 ∷ CK40 ∷ CCZ012 ∷ Bx3-1240 ∷ []) (lem-CKc-box-at033440 c4) ▸
       at 23 1 (Bx3-1420 ∷ []) (lem-box-perm-1324-at033440 c4) ▸
       at 23 1 (CCZ134 ∷ Toff302 ∷ CCZ134 ∷ Toff302 ∷ []) (lem-box-cP-at03243240 c4) ▸
       at 26 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 25 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸ done

  b19 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CCZ124 ∷ CS01 ∷ Toff024 ∷ CCZ124 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK41 ∷ CCZ012 ∷ S4 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ134 ∷ Toff302 ∷ S4 ∷ CCZ134 ∷ Toff302 ∷ []) (Toff014 ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ [])
  b19 = at 24 2 (S4 ∷ Toff302 ∷ []) (sym (wp1111 c4)) ▸
       at 23 2 (S4 ∷ CCZ134 ∷ []) (wl1249 (lit c4)) ▸
       at 24 4 (Bx3-1420 ∷ []) (sym (lem-box-cP-at03243240 c4)) ▸
       at 3 3 (CS01 ∷ Toff024 ∷ CCZ124 ∷ []) (wp1042 c4) ▸
       at 5 2 [] (wl0263 (lit c4)) ▸
       at 8 2 (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4) ▸
       at 9 2 [] (wl0341 (lit c4)) ▸
       at 10 2 (S4 ∷ CCZ012 ∷ []) (wl1269 (lit c4)) ▸ done

  b20 : Chain (Toff014 ∷ Toff104 ∷ Toff024 ∷ CS01 ∷ Toff024 ∷ CS01⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ014 ∷ CK41 ∷ S4 ∷ CCZ012 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ CCZ014 ∷ CCZ012 ∷ CK40 ∷ CCZ012 ∷ S4 ∷ Bx3-1420 ∷ []) (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ [])
  b20 = at 11 2 [] (wl0341 (lit c4)) ▸
       at 12 2 (CCZ014 ∷ CCZ012 ∷ []) (wp0167 c4) ▸
       at 13 2 [] (wl0341 (lit c4)) ▸
       at 16 1 (Bx3-0412 ∷ []) (lem-box-perm-4213-at03243240 c4) ▸
       at 0 16 (Toff214 ∷ Toff124 ∷ Toff214 ∷ CS02 ∷ Toff214 ∷ CS02⁻ ∷ CCZ012 ∷ CK41 ∷ CCZ124 ∷ CK41 ∷ S4 ∷ CK42 ∷ CCZ124 ∷ CK42 ∷ CCZ012 ∷ S4 ∷ []) (wp1112 c4) ▸
       at 0 17 (CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ Sb2-0-41-3 ∷ CK41 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ S4 ∷ CK42 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK42 ∷ S4 ∷ []) (sym (lem-nf-rel-266at0 c4)) ▸ done

-- F1-rel-267@0: 18 steps
lem-F1-rel-267at0 : Ws → ⟪ (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) ⟫ʷ ≈ ⟪ (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) ⟫ʷ
lem-F1-rel-267at0 c4 = trans (run b0) (trans (run b1) (run b2))
  where
  b0 : Chain (CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ [])
  b0 = at 1 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 2 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 6 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 7 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 10 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 11 1 (Sb3-1-42-0 ∷ []) (lem-F0-at01143043 c4) ▸
       at 13 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 14 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸ done

  b1 : Chain (CK40 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK40 ∷ S4 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ Sb3-1-42-0 ∷ Sb3-1-42-0 ∷ CK41 ∷ Sb3-0-41-2 ∷ Sb3-0-41-2 ∷ CK41 ∷ S4 ∷ CK40 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK40 ∷ S4 ∷ []) (CCZ024 ∷ [])
  b1 = at 18 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 19 1 (Sb3-0-41-2 ∷ []) (lem-F0-at14213243 c4) ▸
       at 1 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 5 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 8 2 (CCZ124 ∷ []) (lem-S2-SBOX⟨3·1·42·0⟩ c4) ▸
       at 10 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 14 2 (CCZ014 ∷ []) (lem-S2-SBOX⟨3·0·41·2⟩ c4) ▸
       at 0 17 (CCZ024 ∷ []) (sym (wp1119 c4)) ▸ done

  b2 : Chain (CCZ024 ∷ []) (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ [])
  b2 = at 0 1 (CCZ024 ∷ []) (wp1120 c4) ▸
       at 0 1 (CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ CK41 ∷ Sb2-0-41-3 ∷ Sb2-0-41-3 ∷ CK41 ∷ S4 ∷ Sb0-1-42-3 ∷ Sb0-1-42-3 ∷ []) (sym (lem-nf-rel-267at0 c4)) ▸ done
